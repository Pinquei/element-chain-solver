import { ChainSolver } from './solver.js';

let solver = null;

self.onmessage = function (e) {
  const { board, numColors, startIndices, maxSteps, taskId } = e.data;

  if (!solver || solver.numColors !== numColors) {
    solver = new ChainSolver(numColors);
  }

  const results = solver.evaluateStartMoves(board, startIndices, maxSteps);
  self.postMessage({ taskId, results });
};
