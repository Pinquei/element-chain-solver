/**
 * 高效能 5x5 元素連鎖求解器（v2）
 *
 * 相較 v1 的主要優化：
 * 1. 確定性分支只算一次：點擊後若補入的那張牌沒有引發連鎖，結果完全由補牌顏色決定，
 *    不再重複蒙地卡羅取樣（v1 對同一結果重算 4～16 次）。只有發生連鎖（之後補牌隨機）才取樣。
 * 2. 多步數共用同一棵搜尋樹：一次遞迴同時算出 1～N 步的期望值向量，
 *    不再為 1、2、3、4 步各重跑一次搜尋。
 * 3. 零配置模擬：每層遞迴使用預先配置的緩衝區，單格點擊直接位移欄位（免完整重力計算），
 *    使用 xorshift 亂數取代 Math.random。
 * 4. 置換表（Transposition Table）以數值雙鍵編碼盤面，每次計算前清空，避免記憶體越用越多。
 * 5. 深層 Top-K 剪枝保留，葉節點（最後一步）完整評估 25 個點擊點。
 */

const SIZE = 5;
const CELLS = 25;

// 預計算 30 組三連線（橫 15 + 直 15），攤平成三個型別陣列加速存取
const LA = new Uint8Array(30), LB = new Uint8Array(30), LC = new Uint8Array(30);
{
  let n = 0;
  for (let r = 0; r < SIZE; r++) for (let c = 0; c <= SIZE - 3; c++) {
    LA[n] = r * 5 + c; LB[n] = r * 5 + c + 1; LC[n] = r * 5 + c + 2; n++;
  }
  for (let c = 0; c < SIZE; c++) for (let r = 0; r <= SIZE - 3; r++) {
    LA[n] = r * 5 + c; LB[n] = (r + 1) * 5 + c; LC[n] = (r + 2) * 5 + c; n++;
  }
}
const NLINES = 30;

// 每個點擊位置會「動到」的格子 = 同欄、該列以上（含）；只有經過這些格子的線可能新形成三消
const AFFECTED = [];
for (let idx = 0; idx < CELLS; idx++) {
  const c = idx % 5, r = (idx / 5) | 0;
  const list = [];
  for (let i = 0; i < 30; i++) {
    for (const cell of [LA[i], LB[i], LC[i]]) {
      if (cell % 5 === c && ((cell / 5) | 0) <= r) { list.push(i); break; }
    }
  }
  AFFECTED.push(Uint8Array.from(list));
}
const ALL_MOVES = Array.from({ length: CELLS }, (_, i) => i);

// 搜尋參數（依「剩餘步數」決定）
const TOPK_BY_REMAINING = [0, 25, 10, 8, 6, 5];       // 剩 1 步（葉節點）全評估
const CHAIN_SAMPLES_BY_REMAINING = [0, 1, 1, 1, 1, 1]; // 發生連鎖時的取樣數
const ROOT_CHAIN_SAMPLES = 6;
const MAX_STEPS = 5;

export class ChainSolver {
  constructor(numColors = 5) {
    this.numColors = numColors;
    this.memo = new Map();
    this.clearFlags = new Uint8Array(CELLS);
    this.isNew = new Uint8Array(CELLS);
    this.chained = false;
    this.seed = (Date.now() ^ 0x9e3779b9) >>> 0 || 1;
    // 每層遞迴各自的盤面緩衝區與 Q 值緩衝區
    this.bufs = Array.from({ length: MAX_STEPS + 2 }, () => new Uint8Array(CELLS));
    this.qs = Array.from({ length: MAX_STEPS + 2 }, () => new Float64Array(MAX_STEPS + 2));
    this.shiftBufs = Array.from({ length: MAX_STEPS + 2 }, () => new Uint8Array(CELLS));
    this.scoreBuf = new Float32Array(CELLS);
    this.tmpBoard = new Uint8Array(CELLS);
  }

  rand() {
    let x = this.seed;
    x ^= x << 13; x >>>= 0;
    x ^= x >>> 17;
    x ^= x << 5; x >>>= 0;
    this.seed = x;
    return x;
  }

  randColor() {
    return (this.rand() % this.numColors) + 1;
  }

  // 盤面 → 置換表鍵（每格 3 bits，分兩段數值，避免逐字串接）
  key(board, k) {
    let a = 0, b = 0;
    for (let i = 0; i < 13; i++) a = a * 8 + board[i];
    for (let i = 13; i < CELLS; i++) b = b * 8 + board[i];
    return a + ':' + b + ':' + k;
  }

  applyGravity(board) {
    for (let c = 0; c < SIZE; c++) {
      let w = 20 + c;
      for (let i = 20 + c; i >= 0; i -= 5) {
        const v = board[i];
        if (v !== 0) {
          if (w !== i) { board[w] = v; board[i] = 0; }
          w -= 5;
        }
      }
    }
  }

  /** 找出所有三消並清除，回傳消除張數（保守規則：三張全為新補入者不算） */
  resolveOnce(board) {
    const flags = this.clearFlags, isNew = this.isNew;
    let any = false;
    for (let i = 0; i < NLINES; i++) {
      const a = LA[i], b = LB[i], c = LC[i];
      const col = board[a];
      if (col !== 0 && col === board[b] && col === board[c]) {
        if (isNew[a] && isNew[b] && isNew[c]) continue;
        if (!any) { flags.fill(0); any = true; }
        flags[a] = 1; flags[b] = 1; flags[c] = 1;
      }
    }
    if (!any) return 0;
    let n = 0;
    for (let i = 0; i < CELLS; i++) {
      if (flags[i]) { board[i] = 0; n++; }
    }
    return n;
  }

  /**
   * 模擬點擊 idx、首張補牌為 color 的完整連鎖。結果寫入 dst，回傳總消除張數。
   * this.chained 表示是否發生連鎖（發生則結果含隨機性）。
   */
  simulate(src, idx, color, dst) {
    dst.set(src);
    const c = idx % 5;
    // 單格消除：上方同欄整段下移一格，頂端補入 color
    for (let i = idx; i >= 5; i -= 5) dst[i] = dst[i - 5];
    dst[c] = color;
    const isNew = this.isNew;
    isNew.fill(0);
    isNew[c] = 1;

    let total = 1;
    this.chained = false;
    while (true) {
      const n = this.resolveOnce(dst);
      if (n === 0) break;
      this.chained = true;
      total += n;
      this.applyGravity(dst);
      isNew.fill(0);
      for (let i = 0; i < CELLS; i++) {
        if (dst[i] === 0) { dst[i] = this.randColor(); isNew[i] = 1; }
      }
    }
    return total;
  }

  /** 啟發式排序：點擊後（下落後）盤面的三連 / 二連潛力 */
  rankMoves(board, topK) {
    if (topK >= CELLS) return ALL_MOVES;
    const scores = this.scoreBuf, t = this.tmpBoard;
    for (let idx = 0; idx < CELLS; idx++) {
      t.set(board);
      for (let i = idx; i >= 5; i -= 5) t[i] = t[i - 5];
      t[idx % 5] = 0;
      let p = 0;
      for (let i = 0; i < NLINES; i++) {
        const ca = t[LA[i]], cb = t[LB[i]], cc = t[LC[i]];
        if (ca !== 0 && ca === cb && cb === cc) p += 10;
        else if ((ca !== 0 && ca === cb) || (cb !== 0 && cb === cc) || (ca !== 0 && ca === cc)) p += 2;
      }
      scores[idx] = p;
    }
    const idxs = ALL_MOVES.slice();
    idxs.sort((a, b) => scores[b] - scores[a]);
    return idxs.slice(0, topK);
  }

  /**
   * 對「點擊 idx」這個動作，計算 Q 向量：q[k] = 點擊後再最佳走 k-1 步的期望總消除數（k = 1..K）
   * 結果累加進 q（呼叫前需清零）。
   */
  actionQ(board, idx, K, q, buf, chainSamples, level, hasLatent) {
    const nc = this.numColors;
    const c = idx % 5;
    // 快速路徑：先做一次「欄位下移」，各顏色只需檢查受影響的線即可判斷是否連鎖
    const base = this.shiftBufs[level];
    base.set(board);
    for (let i = idx; i >= 5; i -= 5) base[i] = base[i - 5];
    const aff = AFFECTED[idx];

    for (let color = 1; color <= nc; color++) {
      let match = hasLatent;
      if (!match) {
        base[c] = color;
        for (let j = 0; j < aff.length; j++) {
          const l = aff[j];
          const x = base[LA[l]];
          if (x === base[LB[l]] && x === base[LC[l]]) { match = true; break; }
        }
      }
      if (!match) {
        // 無連鎖：結果確定，只算一次
        if (K > 1) {
          const child = this.values(base, K - 1);
          for (let k = 1; k <= K; k++) q[k] += (1 + child[k - 1]) / nc;
        } else {
          q[1] += 1 / nc;
        }
        continue;
      }
      // 有連鎖：之後補牌隨機，取樣平均
      const w = 1 / (nc * chainSamples);
      for (let s = 0; s < chainSamples; s++) {
        const r = this.simulate(board, idx, color, buf);
        if (K > 1) {
          const child = this.values(buf, K - 1);
          for (let k = 1; k <= K; k++) q[k] += (r + child[k - 1]) * w;
        } else {
          q[1] += r * w;
        }
      }
    }
  }

  /** 盤面是否殘留「全為新補入、被保守規則略過」的三連（下一次點擊時會被消除） */
  hasLatentTriple(board) {
    for (let i = 0; i < NLINES; i++) {
      const x = board[LA[i]];
      if (x === board[LB[i]] && x === board[LC[i]]) return true;
    }
    return false;
  }

  /**
   * 回傳向量 v，v[k] = 從 board 出發最佳走 k 步的期望總消除數（k = 0..K）
   */
  values(board, K) {
    // 葉節點（剩 1 步）不進置換表：重算很便宜，存起來反而佔掉大量記憶體
    const useMemo = K >= 2;
    let mk = '';
    if (useMemo) {
      mk = this.key(board, K);
      const cached = this.memo.get(mk);
      if (cached !== undefined) return cached;
    }

    const v = new Float64Array(K + 1);
    const q = this.qs[K];
    const buf = this.bufs[K];
    const cands = this.rankMoves(board, TOPK_BY_REMAINING[K]);
    const samples = CHAIN_SAMPLES_BY_REMAINING[K];
    const latent = this.hasLatentTriple(board);

    for (let m = 0; m < cands.length; m++) {
      q.fill(0);
      this.actionQ(board, cands[m], K, q, buf, samples, K, latent);
      for (let k = 1; k <= K; k++) if (q[k] > v[k]) v[k] = q[k];
    }
    if (useMemo) this.memo.set(mk, v);
    return v;
  }

  /**
   * 針對指定起手點列表，計算 1 ~ maxSteps 中「期望消除 / 步數」最佳者
   */
  evaluateStartMoves(boardArray, startIndices, maxSteps) {
    maxSteps = Math.min(maxSteps, MAX_STEPS);
    const board = new Uint8Array(boardArray);
    // 換了盤面或步數才清空置換表（同一次計算的多個起手點可共用），避免越積越大
    const sig = this.key(board, maxSteps);
    if (sig !== this.lastSig) { this.memo.clear(); this.lastSig = sig; }
    const results = [];
    const q = this.qs[MAX_STEPS + 1];
    const buf = this.bufs[MAX_STEPS + 1];

    const latent = this.hasLatentTriple(board);
    for (const startIdx of startIndices) {
      q.fill(0);
      this.actionQ(board, startIdx, maxSteps, q, buf, ROOT_CHAIN_SAMPLES, MAX_STEPS + 1, latent);
      let bestRatio = 0, bestStep = 1, bestTotal = 0;
      for (let k = 1; k <= maxSteps; k++) {
        const ratio = q[k] / k;
        if (ratio > bestRatio) { bestRatio = ratio; bestStep = k; bestTotal = q[k]; }
      }
      results.push({
        index: startIdx,
        row: Math.floor(startIdx / 5) + 1,
        col: (startIdx % 5) + 1,
        scorePerStep: bestRatio,
        bestStep,
        expectedTotal: bestTotal
      });
    }
    return results;
  }
}
