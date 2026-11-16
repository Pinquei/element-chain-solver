/**
 * 高效能 5x5 元素連鎖求解器
 * 優化技術：
 * 1. 一維 Uint8Array(25) 零配置記憶體複用
 * 2. 預計算 30 組橫/直向三連線查表
 * 3. Transposition Table (置換表) 狀態去重
 * 4. 深層節點啟發式 Top-K 動作剪枝 (Beam Pruning)
 */

const SIZE = 5;
const CELLS = 25;

// 預計算所有 30 組「連續 3 格」的索引組合（橫向 15 組 + 直向 15 組）
const LINES_3 = [];
for (let r = 0; r < SIZE; r++) {
  for (let c = 0; c <= SIZE - 3; c++) {
    LINES_3.push([r * 5 + c, r * 5 + c + 1, r * 5 + c + 2]);
  }
}
for (let c = 0; c < SIZE; c++) {
  for (let r = 0; r <= SIZE - 3; r++) {
    LINES_3.push([r * 5 + c, (r + 1) * 5 + c, (r + 2) * 5 + c]);
  }
}

export class ChainSolver {
  constructor(numColors = 5) {
    this.numColors = numColors;
    this.memo = new Map();
    // 預先配置緩衝區，避免遞迴中反覆 new Array 觸發 GC
    this.clearFlags = new Uint8Array(CELLS);
  }

  /**
   * 將盤面編碼為緊湊字串作為 Transposition Table Key
   */
  encodeBoard(board) {
    let key = '';
    for (let i = 0; i < CELLS; i++) {
      key += board[i];
    }
    return key;
  }

  /**
   * 重力下落（In-place 原地修改，零記憶體分配）
   */
  applyGravity(board) {
    for (let c = 0; c < SIZE; c++) {
      let writeRow = SIZE - 1;
      for (let r = SIZE - 1; r >= 0; r--) {
        const val = board[r * 5 + c];
        if (val !== 0) {
          board[writeRow * 5 + c] = val;
          if (writeRow !== r) board[r * 5 + c] = 0;
          writeRow--;
        }
      }
      while (writeRow >= 0) {
        board[writeRow * 5 + c] = 0;
        writeRow--;
      }
    }
  }

  /**
   * 執行一次三消判定並清除，回傳本次消除張數
   * @param {Uint8Array} board 當前盤面
   * @param {Uint8Array|null} isNewMask 標記哪些格子是本輪新補入的（1=新補入, 0=原本留存）
   */
  resolveMatchesOnce(board, isNewMask) {
    this.clearFlags.fill(0);
    let matchedAny = false;

    for (let i = 0; i < LINES_3.length; i++) {
      const [a, b, c] = LINES_3[i];
      const color = board[a];
      if (color !== 0 && color === board[b] && color === board[c]) {
        // 保守估計規則：若啟用 isNewMask，至少要有一張是原本留在盤面上的卡片
        if (isNewMask && isNewMask[a] && isNewMask[b] && isNewMask[c]) {
          continue;
        }
        this.clearFlags[a] = 1;
        this.clearFlags[b] = 1;
        this.clearFlags[c] = 1;
        matchedAny = true;
      }
    }

    if (!matchedAny) return 0;

    let clearedCount = 0;
    for (let i = 0; i < CELLS; i++) {
      if (this.clearFlags[i]) {
        board[i] = 0;
        if (isNewMask) isNewMask[i] = 0;
        clearedCount++;
      }
    }
    return clearedCount;
  }

  /**
   * 隨機填滿空位，並回傳新填補位置的遮罩
   */
  fillEmptyRandom(board, isNewMask) {
    isNewMask.fill(0);
    for (let i = 0; i < CELLS; i++) {
      if (board[i] === 0) {
        board[i] = ((Math.random() * this.numColors) | 0) + 1;
        isNewMask[i] = 1;
      }
    }
  }

  /**
   * 模擬點擊某格後的完整連鎖過程（單次模擬）
   * 回傳：{ totalCleared, nextBoard }
   */
  simulateClickOnce(srcBoard, clickIdx, forcedFirstColor = 0) {
    const board = new Uint8Array(srcBoard);
    const isNewMask = new Uint8Array(CELLS);

    // 1. 點擊消除該格
    board[clickIdx] = 0;
    let totalCleared = 1;

    // 2. 下落並補入第一張牌（此時空位必為 1 格）
    this.applyGravity(board);
    isNewMask.fill(0);
    for (let i = 0; i < CELLS; i++) {
      if (board[i] === 0) {
        board[i] = forcedFirstColor || (((Math.random() * this.numColors) | 0) + 1);
        isNewMask[i] = 1;
        break;
      }
    }

    // 3. 連鎖循環直到沒有三消
    while (true) {
      const cleared = this.resolveMatchesOnce(board, isNewMask);
      if (cleared === 0) break;
      totalCleared += cleared;
      this.applyGravity(board);
      this.fillEmptyRandom(board, isNewMask);
    }

    return { totalCleared, nextBoard: board };
  }

  /**
   * 啟發式快速評分：用來在深層搜尋時篩選出 Top-K 潛力點擊位置
   */
  rankCandidateMoves(board, topK) {
    if (topK >= CELLS) {
      return Array.from({ length: CELLS }, (_, i) => i);
    }

    const scores = new Float32Array(CELLS);
    const tempBoard = new Uint8Array(CELLS);

    for (let idx = 0; idx < CELLS; idx++) {
      tempBoard.set(board);
      tempBoard[idx] = 0;
      this.applyGravity(tempBoard);

      // 評估下落後盤面上形成「二連」或「三連」的潛力
      let potential = 0;
      for (let i = 0; i < LINES_3.length; i++) {
        const [a, b, c] = LINES_3[i];
        const ca = tempBoard[a], cb = tempBoard[b], cc = tempBoard[c];
        if (ca !== 0 && ca === cb && cb === cc) potential += 10; // 直接三消
        else if ((ca !== 0 && ca === cb) || (cb !== 0 && cb === cc) || (ca !== 0 && ca === cc)) {
          potential += 2; // 聽牌二連
        }
      }
      scores[idx] = potential;
    }

    const indices = Array.from({ length: CELLS }, (_, i) => i);
    indices.sort((a, b) => scores[b] - scores[a]);
    return indices.slice(0, topK);
  }

  /**
   * Expectimax 核心遞迴：計算在 board 狀態下，再走 remainingSteps 步的最大期望總消除數
   */
  expectimax(board, remainingSteps, maxDepth) {
    if (remainingSteps === 0) return 0;

    const memoKey = `${this.encodeBoard(board)}_${remainingSteps}`;
    const cached = this.memo.get(memoKey);
    if (cached !== undefined) return cached;

    // 依深度動態調整取樣數與剪枝寬度（兼顧速度與準確度）
    const depthIndex = maxDepth - remainingSteps; // 0 = 第一步, 1 = 第二步...
    const topK = depthIndex === 0 ? 25 : depthIndex === 1 ? 12 : 7;
    const mcSamples = remainingSteps === 1 ? 16 : remainingSteps === 2 ? 8 : 4;

    const candidates = this.rankCandidateMoves(board, topK);
    let bestExpected = 0;

    for (let m = 0; m < candidates.length; m++) {
      const clickIdx = candidates[m];
      let moveExpected = 0;

      // 第一步補牌精確枚舉所有顏色 (1 ~ numColors)
      for (let color = 1; color <= this.numColors; color++) {
        if (remainingSteps === 1) {
          // 葉節點：只需做輕量取樣計算期望消除張數
          let subTotal = 0;
          for (let s = 0; s < mcSamples; s++) {
            subTotal += this.simulateClickOnce(board, clickIdx, color).totalCleared;
          }
          moveExpected += subTotal / mcSamples;
        } else {
          // 非葉節點：模擬連鎖後遞迴進入下一步
          let branchTotal = 0;
          const branchSamples = Math.max(2, Math.floor(mcSamples / 2));
          for (let s = 0; s < branchSamples; s++) {
            const { totalCleared, nextBoard } = this.simulateClickOnce(board, clickIdx, color);
            branchTotal += totalCleared + this.expectimax(nextBoard, remainingSteps - 1, maxDepth);
          }
          moveExpected += branchTotal / branchSamples;
        }
      }

      moveExpected /= this.numColors;
      if (moveExpected > bestExpected) {
        bestExpected = moveExpected;
      }
    }

    this.memo.set(memoKey, bestExpected);
    return bestExpected;
  }

  /**
   * 針對指定的起手點列表計算 1 ~ maxSteps 的最佳「期望消除數 / 步數」
   */
  evaluateStartMoves(boardArray, startIndices, maxSteps) {
    const board = new Uint8Array(boardArray);
    const results = [];

    // 每次重新計算時清理過大的快取避免記憶體膨脹
    if (this.memo.size > 150000) this.memo.clear();

    for (const startIdx of startIndices) {
      let bestRatio = 0;
      let bestStep = 1;
      let bestTotal = 0;

      // 評估規劃 1 ~ maxSteps 步，取「期望/步數」最大值（涵蓋先佈局後爆發策略）
      for (let steps = 1; steps <= maxSteps; steps++) {
        let stepExpected = 0;
        const outerSamples = steps >= 3 ? 6 : 16;

        for (let color = 1; color <= this.numColors; color++) {
          let colorSum = 0;
          for (let s = 0; s < outerSamples; s++) {
            const { totalCleared, nextBoard } = this.simulateClickOnce(board, startIdx, color);
            const future = steps > 1 ? this.expectimax(nextBoard, steps - 1, steps) : 0;
            colorSum += totalCleared + future;
          }
          stepExpected += colorSum / outerSamples;
        }

        stepExpected /= this.numColors;
        const ratio = stepExpected / steps;

        if (ratio > bestRatio) {
          bestRatio = ratio;
          bestStep = steps;
          bestTotal = stepExpected;
        }
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
