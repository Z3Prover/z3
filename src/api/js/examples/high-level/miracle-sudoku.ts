import { init } from '../../build/node.js';

import type { Solver, Arith } from '../../build/node';

// solve the "miracle sudoku"
// https://www.youtube.com/watch?v=yKf9aUIxdb4
// most of the interesting stuff is in `solve`
// the process is:
// - parse the board
// - create a Solver
// - create a Z3.Int variable for each square
// - for known cells, add a constraint which says the variable for that cell equals that value
// - add the usual uniqueness constraints
// - add the special "miracle sudoku" constraints
// - call `await solver.check()`
// - if the result is "sat", the board is solvable
//   - call `solver.model()` to get a model, i.e. a concrete assignment of variables which satisfies the model
//   - for each variable, call `model.evaluate(v)` to recover its value

function parseSudoku(str: string) {
  // derive a list of { row, col, val } records, one for each specified position
  // from a string like
  // ....1..3.
  // ..9..5..8
  // 8.4..6.25
  // ......6..
  // ..8..4...
  // 12..87...
  // 3..9..2..
  // .65..8...
  // 9........

  let cells = [];

  let lines = str.trim().split('\n');
  if (lines.length !== 9) {
    throw new Error(`expected 9 lines, got ${lines.length}`);
  }
  for (let row = 0; row < 9; ++row) {
    let line = lines[row].trim();
    if (line.length !== 9) {
      throw new Error(`expected line of length 9, got length ${line.length}`);
    }
    for (let col = 0; col < 9; ++col) {
      let char = line[col];
      if (char === '.') {
        continue;
      }
      if (char < '1' || char > '9') {
        throw new Error(`expected digit or '.', got ${char}`);
      }
      cells.push({ row, col, value: char.codePointAt(0)! - 48 /* '0' */ });
    }
  }
  return cells;
}

(async () => {
  let { Context, em } = await init();

  // if you use 'main' as your context name, you won't need to name it in types like Solver
  // if you're creating multiple contexts, give them different names
  // then the type system will prevent you from mixing them
  let Z3 = Context('main');

  function addSudokuConstraints(solver: Solver, cells: Arith[][]) {
    // the usual constraints:

    // every square is between 1 and 9
    for (let row of cells) {
      for (let cell of row) {
        solver.add(cell.ge(1));
        solver.add(cell.le(9));
      }
    }

    // values in each row are unique
    for (let row of cells) {
      solver.add(Z3.Distinct(...row));
    }

    // values in each column are unique
    for (let col = 0; col < 9; ++col) {
      solver.add(Z3.Distinct(...cells.map(row => row[col])));
    }

    // values in each 3x3 subdivision are unique
    for (let suprow = 0; suprow < 3; ++suprow) {
      for (let supcol = 0; supcol < 3; ++supcol) {
        let square = [];
        for (let row = 0; row < 3; ++row) {
          for (let col = 0; col < 3; ++col) {
            square.push(cells[suprow * 3 + row][supcol * 3 + col]);
          }
        }
        solver.add(Z3.Distinct(...square));
      }
    }
  }

  function applyOffsets(x: number, y: number, offsets: [number, number][]) {
    let out = [];
    for (let offset of offsets) {
      let rx = x + offset[0];
      let ry = y + offset[1];
      if (rx >= 0 && rx < 9 && ry >= 0 && ry < 8) {
        out.push({ x: rx, y: ry });
      }
    }
    return out;
  }

  function addMiracleConstraints(s: Solver, cells: Arith[][]) {
    // the special "miracle sudoku" constraints

    // any two cells separated by a knight's move or a kings move cannot contain the same digit
    let knightOffets: [number, number][] = [
      [1, -2],
      [2, -1],
      [2, 1],
      [1, 2],
      [-1, 2],
      [-2, 1],
      [-2, -1],
      [-1, -2],
    ];
    let kingOffsets: [number, number][] = [
      [1, 1],
      [1, -1],
      [-1, 1],
      [-1, -1],
    ]; // skipping immediately adjacent because those are covered by normal sudoku rules
    let allOffets = [...knightOffets, ...kingOffsets];
    for (let row = 0; row < 9; ++row) {
      for (let col = 0; col < 9; ++col) {
        for (let { x, y } of applyOffsets(row, col, allOffets)) {
          s.add(cells[row][col].neq(cells[x][y]));
        }
      }
    }

    // any two orthogonally adjacent cells cannot contain consecutive digits
    let orthoOffsets: [number, number][] = [
      [0, 1],
      [0, -1],
      [1, 0],
      [-1, 0],
    ];
    for (let row = 0; row < 9; ++row) {
      for (let col = 0; col < 9; ++col) {
        for (let { x, y } of applyOffsets(row, col, orthoOffsets)) {
          s.add(cells[row][col].sub(cells[x][y]).neq(1));
        }
      }
    }
  }

  async function solve(str: string) {
    let solver = new Z3.Solver();
    let cells = Array.from({ length: 9 }, (_, col) =>
      Array.from({ length: 9 }, (_, row) => Z3.Int.const(`c_${row}_${col}`)),
    );
    for (let { row, col, value } of parseSudoku(str)) {
      solver.add(cells[row][col].eq(value));
    }
    addSudokuConstraints(solver, cells);
    addMiracleConstraints(solver, cells); // remove this line to solve normal sudokus

    let start = Date.now();
    console.log('starting... this may take a minute or two');
    let check = await solver.check();
    console.log(`problem was determined to be ${check} in ${Date.now() - start} ms`);
    if (check === 'sat') {
      let model = solver.model();
      let str = '';
      for (let row = 0; row < 9; ++row) {
        for (let col = 0; col < 9; ++col) {
          str += model.eval(cells[row][col]).toString() + (col === 8 ? '' : ' ');
          if (col === 2 || col === 5) {
            str += ' ';
          }
        }
        str += '\n';
        if (row === 2 || row === 5) {
          str += '\n';
        }
      }
      console.log(str);
    }
  }

  await solve(`
.........
.........
.........
.........
..1......
......2..
.........
.........
.........
`);
})().catch(e => {
  console.error('error', e);
  process.exit(1);
});
