import assert from 'assert';
import asyncToArray from 'iter-tools/methods/async-to-array';
import { init, killThreads } from '../jest';
import { ArithRef, BoolRef, Model, sat, unsat, Z3AssertionError, Z3HighLevel } from './types';

/**
 * Generate all possible solutions from given assumptions.
 *
 * **NOTE**: The set of solutions might be infinite.
 * Always ensure to limit amount generated, either by knowing that the
 * solution space is constrainted, or by taking only a specified
 * amount of solutions
 * ```typescript
 * import { sliceAsync } from 'iter-tools';
 * // ...
 * for await (const model of sliceAsync(10, solver.solutions())) {
 *   console.log(model.sexpr());
 * }
 * ```
 * @see http://theory.stanford.edu/~nikolaj/programmingz3.html#sec-blocking-evaluations
 * @returns Models with solutions. Nothing if no constants provided
 */
// TODO(ritave): Use faster solution https://stackoverflow.com/a/70656700
// TODO(ritave): Move to high-level.ts
async function* allSolutions<Name extends string>(...assertions: BoolRef<Name>[]): AsyncIterable<Model<Name>> {
  if (assertions.length === 0) {
    return;
  }

  const { Or } = assertions[0].ctx;
  const solver = new assertions[0].ctx.Solver();
  solver.add(...assertions);

  while ((await solver.check()) === sat) {
    const model = solver.model();
    const decls = model.decls();
    if (decls.length === 0) {
      return;
    }
    yield model;

    solver.add(
      Or(
        ...decls
          // TODO(ritave): Assert on arity > 0
          .filter(decl => decl.arity() === 0)
          .map(decl => {
            const term = decl.call();
            // TODO(ritave): Assert not an array / uinterpeted sort
            const value = model.eval(term, true);
            return term.neq(value);
          }),
      ),
    );
  }
}

async function prove(conjecture: BoolRef): Promise<void> {
  const solver = new conjecture.ctx.Solver();
  const { Not } = solver.ctx;
  solver.add(Not(conjecture));
  expect(await solver.check()).toStrictEqual(unsat);
}

describe('high-level', () => {
  let api: { em: any } & Z3HighLevel;

  beforeAll(async () => {
    api = await init();
  });

  afterAll(async () => {
    await killThreads(api.em);
  });

  it('can set params', () => {
    const { setParam, getParam, resetParams } = api;

    expect(getParam('pp.decimal')).toStrictEqual('false');
    setParam('pp.decimal', 'true');
    expect(getParam('pp.decimal')).toStrictEqual('true');
    setParam({ 'pp.decimal': 'false', timeout: 4 });
    expect(getParam('pp.decimal')).toStrictEqual('false');
    expect(getParam('timeout')).toStrictEqual('4');

    resetParams();
    expect(getParam('pp.decimal')).toStrictEqual('false');
    expect(getParam('timeout')).toStrictEqual('4294967295');
  });

  it('proves x = y implies g(x) = g(y)', async () => {
    const { Solver, Int, IntSort, Function, Implies, Not } = new api.Context('main');
    const solver = new Solver();

    const sort = IntSort();
    const x = Int('x');
    const y = Int('y');
    const g = Function('g', sort, sort);

    const conjecture = Implies(x.eq(y), g.call(x).eq(g.call(y)));
    solver.add(Not(conjecture));
    expect(await solver.check()).toStrictEqual(unsat);
  });

  it('disproves x = y implies g(g(x)) = g(y)', async () => {
    const { Solver, Int, IntSort, Function, Implies, Not } = new api.Context('main');
    const solver = new Solver();

    const sort = IntSort();
    const x = Int('x');
    const y = Int('y');
    const g = Function('g', sort, sort);
    const conjecture = Implies(x.eq(y), g.call(g.call(x)).eq(g.call(y)));
    solver.add(Not(conjecture));
    expect(await solver.check()).toStrictEqual(sat);
  });

  it('checks that Context matches', () => {
    const c1 = new api.Context('context');
    const c2 = new api.Context('context');
    const c3 = new api.Context('foo');
    const c4 = new api.Context('bar');

    // Contexts with the same name don't do type checking during compile time.
    // We need to check for different context dynamically
    expect(() => c1.Or(c2.IntVal(5).eq(2))).toThrowError(Z3AssertionError);

    // On the other hand, this won't compile due to automatic generics
    // @ts-expect-error
    expect(() => c3.Or(c4.IntVal(5).eq(2))).toThrowError(Z3AssertionError);

    const allUniqueContexes = new Set([c1, c2, c3, c4]).size === 4;
    expect(allUniqueContexes).toStrictEqual(true);

    expect(() => c1.Or(c1.IntVal(5).eq(2))).not.toThrowError();
  });

  describe('booleans', () => {
    it("proves De Morgan's Law", async () => {
      const { Bool, Not, And, Eq, Or } = new api.Context('main');
      const [x, y] = [Bool('x'), Bool('y')];

      const conjecture = Eq(Not(And(x, y)), Or(Not(x), Not(y)));

      await prove(conjecture);
    });
  });

  describe('ints', () => {
    it('finds a model', async () => {
      const { Solver, Int, getValue } = new api.Context('main');
      const solver = new Solver();
      const x = Int('x');
      const y = Int('y');

      solver.add(x.ge(1)); // x >= 1
      solver.add(y.lt(x.add(3))); // y < x + 3

      expect(await solver.check()).toStrictEqual(sat);

      const model = solver.model();
      expect(model.length).toStrictEqual(2);

      for (const decl of model) {
        expect(decl.arity()).toStrictEqual(0);
      }
      const xValue = getValue(model.get(x));
      const yValue = getValue(model.get(y));
      assert(typeof xValue === 'bigint');
      assert(typeof yValue === 'bigint');
      expect(xValue).toBeGreaterThanOrEqual(1n);
      expect(yValue).toBeLessThanOrEqual(xValue + 3n);
    });

    it('solves sudoku', async () => {
      function toSudoku(data: string): (number | null)[][] {
        const cells: (number | null)[][] = Array.from({ length: 9 }, () => Array.from({ length: 9 }, () => null));

        const lines = data.trim().split('\n');
        for (let row = 0; row < 9; row++) {
          const line = lines[row].trim();
          for (let col = 0; col < 9; col++) {
            const char = line[col];
            if (char !== '.') {
              cells[row][col] = Number.parseInt(char);
            }
          }
        }
        return cells;
      }
      const INSTANCE = toSudoku(`
        ....94.3.
        ...51...7
        .89....4.
        ......2.8
        .6.2.1.5.
        1.2......
        .7....52.
        9...65...
        .4.97....
      `);

      const EXPECTED = toSudoku(`
        715894632
        234516897
        689723145
        493657218
        867231954
        152489763
        376148529
        928365471
        541972386
      `);

      const { Solver, Int, Distinct, getValue, isInt } = new api.Context('main');

      const cells: ArithRef[][] = [];
      // 9x9 matrix of integer variables
      for (let i = 0; i < 9; i++) {
        const row = [];
        for (let j = 0; j < 9; j++) {
          row.push(Int(`x_${i}_${j}`));
        }
        cells.push(row);
      }

      const solver = new Solver();

      // each cell contains a value 1<=x<=9
      for (let i = 0; i < 9; i++) {
        for (let j = 0; j < 9; j++) {
          solver.add(cells[i][j].ge(1), cells[i][j].le(9));
        }
      }

      // each row contains a digit only once
      for (let i = 0; i < 9; i++) {
        solver.add(Distinct(...cells[i]));
      }

      // each column contains a digit only once
      for (let j = 0; j < 9; j++) {
        const column = [];
        for (let i = 0; i < 9; i++) {
          column.push(cells[i][j]);
        }
        solver.add(Distinct(...column));
      }

      // each 3x3 contains a digit at most once
      for (let iSquare = 0; iSquare < 3; iSquare++) {
        for (let jSquare = 0; jSquare < 3; jSquare++) {
          const square = [];

          for (let i = iSquare * 3; i < iSquare * 3 + 3; i++) {
            for (let j = jSquare * 3; j < jSquare * 3 + 3; j++) {
              square.push(cells[i][j]);
            }
          }

          solver.add(Distinct(...square));
        }
      }

      for (let i = 0; i < 9; i++) {
        for (let j = 0; j < 9; j++) {
          const digit = INSTANCE[i][j];
          if (digit !== null) {
            solver.add(cells[i][j].eq(digit));
          }
        }
      }

      expect(await solver.check()).toStrictEqual(sat);

      const model = solver.model();
      const result = [];
      for (let i = 0; i < 9; i++) {
        let row = [];
        for (let j = 0; j < 9; j++) {
          const cell = model.eval(cells[i][j]);
          expect(isInt(cell)).toStrictEqual(true);
          const value = getValue(cell);
          assert(typeof value === 'bigint');
          expect(value).toBeGreaterThanOrEqual(0n);
          expect(value).toBeLessThanOrEqual(9n);
          // JSON.stringify doesn't handle bigints
          row.push(Number(value));
        }
        result.push(row);
      }
      expect(JSON.stringify(result)).toStrictEqual(JSON.stringify(EXPECTED));
    });
  });

  describe('reals', () => {
    it('can work with numerals', async () => {
      const { RealVal, And } = new api.Context('main');
      const n1 = RealVal('1/2');
      const n2 = RealVal('0.5');
      const n3 = RealVal(0.5);
      await prove(And(n1.eq(n2), n1.eq(n3)));

      const n4 = RealVal('-1/3');
      const n5 = RealVal('-0.3333333333333333333333333333333333');
      await prove(n4.neq(n5));
    });
  });

  describe('Solver', () => {
    it('can use push and pop', async () => {
      const { Solver, Int } = new api.Context('main');
      const solver = new Solver();
      const x = Int('x');

      solver.add(x.gt(0));

      expect(await solver.check()).toStrictEqual(sat);

      solver.push();
      solver.add(x.lt(0));

      expect(solver.numScopes()).toStrictEqual(1);
      expect(await solver.check()).toStrictEqual(unsat);

      solver.pop();

      expect(solver.numScopes()).toStrictEqual(0);
      expect(await solver.check()).toStrictEqual(sat);
    });

    it('can find multiple solutions', async () => {
      const { Int, getValue } = new api.Context('main');

      const x = Int('x');

      const solutions = await asyncToArray(allSolutions(x.ge(1), x.le(5)));
      expect(solutions.length).toStrictEqual(5);
      const results = solutions
        .map(solution => getValue(solution.eval(x)))
        .sort((a, b) => {
          assert(a !== null && b !== null && typeof a === 'bigint' && typeof b === 'bigint');
          if (a < b) {
            return -1;
          } else if (a == b) {
            return 0;
          } else {
            return 1;
          }
        });
      expect(results).toStrictEqual([1n, 2n, 3n, 4n, 5n]);
    });
  });

  describe('AstVector', () => {
    it('can use basic methods', async () => {
      const { Solver, AstVector, Int } = new api.Context('main');
      const solver = new Solver();

      const vector = new AstVector<ArithRef>();
      for (let i = 0; i < 5; i++) {
        vector.push(Int(i));
      }

      const length = vector.length;
      for (let i = 0; i < length; i++) {
        solver.add(vector.get(i).gt(1));
      }

      expect(await solver.check()).toStrictEqual(sat);
    });
  });
});
