import assert from 'assert';
import asyncToArray from 'iter-tools/methods/async-to-array';
import { init, killThreads } from '../jest';
import { Arith, Bool, Model, Quantifier, Z3AssertionError, Z3HighLevel, AstVector } from './types';
import { expectType } from 'ts-expect';

// this should not be necessary but there may be a Jest bug
// https://github.com/jestjs/jest/issues/7874
afterEach(() => {
  global.gc && global.gc();
});

/**
 * Generate all possible solutions from given assumptions.
 *
 * **NOTE**: The set of solutions might be infinite.
 * Always ensure to limit amount generated, either by knowing that the
 * solution space is constrained, or by taking only a specified
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
async function* allSolutions<Name extends string>(...assertions: Bool<Name>[]): AsyncIterable<Model<Name>> {
  if (assertions.length === 0) {
    return;
  }

  const { Or } = assertions[0].ctx;
  const solver = new assertions[0].ctx.Solver();
  solver.add(...assertions);

  while ((await solver.check()) === 'sat') {
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
            // TODO(ritave): Assert not an array / uninterpreted sort
            const value = model.eval(term, true);
            return term.neq(value);
          }),
      ),
    );
  }
}

async function prove(conjecture: Bool): Promise<void> {
  const solver = new conjecture.ctx.Solver();
  solver.set('timeout', 1000);
  const { Not } = solver.ctx;
  solver.add(Not(conjecture));
  expect(await solver.check()).toStrictEqual('unsat');
}

async function solve(conjecture: Bool): Promise<Model> {
  const solver = new conjecture.ctx.Solver();
  solver.add(conjecture);
  expect(await solver.check()).toStrictEqual('sat');
  return solver.model();
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
    const { Solver, Int, Function, Implies, Not } = api.Context('main');
    const solver = new Solver();

    const sort = Int.sort();
    const x = Int.const('x');
    const y = Int.const('y');
    const g = Function.declare('g', sort, sort);

    const conjecture = Implies(x.eq(y), g.call(x).eq(g.call(y)));
    solver.add(Not(conjecture));
    expect(await solver.check()).toStrictEqual('unsat');
  });

  it('test loading a solver state from a string', async () => {
    const { Solver, Not, Int } = api.Context('main');
    const solver = new Solver();
    solver.fromString('(declare-const x Int) (assert (and (< x 2) (> x 0)))');
    expect(await solver.check()).toStrictEqual('sat');
    const x = Int.const('x');
    solver.add(Not(x.eq(1)));
    expect(await solver.check()).toStrictEqual('unsat');
  });

  it('disproves x = y implies g(g(x)) = g(y)', async () => {
    const { Solver, Int, Function, Implies, Not } = api.Context('main');
    const solver = new Solver();

    const sort = Int.sort();
    const x = Int.const('x');
    const y = Int.const('y');
    const g = Function.declare('g', sort, sort);
    const conjecture = Implies(x.eq(y), g.call(g.call(x)).eq(g.call(y)));
    solver.add(Not(conjecture));
    expect(await solver.check()).toStrictEqual('sat');
  });

  it('checks that Context matches', () => {
    const c1 = api.Context('context');
    const c2 = api.Context('context');
    const c3 = api.Context('foo');
    const c4 = api.Context('bar');

    // Contexts with the same name don't do type checking during compile time.
    // We need to check for different context dynamically
    expect(() => c1.Or(c2.Int.val(5).eq(2))).toThrowError(Z3AssertionError);

    // On the other hand, this won't compile due to automatic generics
    // @ts-expect-error
    expect(() => c3.Or(c4.Int.val(5).eq(2))).toThrowError(Z3AssertionError);

    const allUniqueContexes = new Set([c1, c2, c3, c4]).size === 4;
    expect(allUniqueContexes).toStrictEqual(true);

    expect(() => c1.Or(c1.Int.val(5).eq(2))).not.toThrowError();
  });

  describe('booleans', () => {
    it('can use pseudo-boolean constraints', async () => {
      const { Bool, PbEq, Solver } = api.Context('main');
      const x = Bool.const('x');
      const y = Bool.const('y');

      const solver = new Solver();
      solver.add(PbEq([x, y], [1, 1], 1));
      expect(await solver.check()).toStrictEqual('sat');

      solver.add(x.eq(y));
      expect(await solver.check()).toStrictEqual('unsat');
    });

    it("proves De Morgan's Law", async () => {
      const { Bool, Not, And, Eq, Or } = api.Context('main');
      const [x, y] = [Bool.const('x'), Bool.const('y')];

      const conjecture = Eq(Not(And(x, y)), Or(Not(x), Not(y)));

      await prove(conjecture);
    });
  });

  describe('ints', () => {
    it('finds a model', async () => {
      const { Solver, Int, isIntVal } = api.Context('main');
      const solver = new Solver();
      const x = Int.const('x');
      const y = Int.const('y');

      solver.add(x.ge(1)); // x >= 1
      solver.add(y.lt(x.add(3))); // y < x + 3

      expect(await solver.check()).toStrictEqual('sat');

      const model = solver.model();
      expect(model.length()).toStrictEqual(2);

      for (const decl of model) {
        expect(decl.arity()).toStrictEqual(0);
      }
      const xValueExpr = model.get(x);
      const yValueExpr = model.get(y);
      assert(isIntVal(xValueExpr));
      assert(isIntVal(yValueExpr));
      const xValue = xValueExpr.value();
      const yValue = yValueExpr.value();
      assert(typeof xValue === 'bigint');
      assert(typeof yValue === 'bigint');
      expect(xValue).toBeGreaterThanOrEqual(1n);
      expect(yValue).toBeLessThanOrEqual(xValue + 3n);
    });

    // TODO(ritave): After changes made since last commit (a332187c746c23450860deb210d94e6e042dd424),
    //               this test takes twice as long (from 5s to 10s). Figure out why
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

      const { Solver, Int, Distinct, isIntVal } = api.Context('main');

      const cells: Arith[][] = [];
      // 9x9 matrix of integer variables
      for (let i = 0; i < 9; i++) {
        const row = [];
        for (let j = 0; j < 9; j++) {
          row.push(Int.const(`x_${i}_${j}`));
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

      expect(await solver.check()).toStrictEqual('sat');

      const model = solver.model();
      const result = [];
      for (let i = 0; i < 9; i++) {
        let row = [];
        for (let j = 0; j < 9; j++) {
          const cell = model.eval(cells[i][j]);
          assert(isIntVal(cell));
          const value = cell.value();
          assert(typeof value === 'bigint');
          expect(value).toBeGreaterThanOrEqual(0n);
          expect(value).toBeLessThanOrEqual(9n);
          // JSON.stringify doesn't handle bigints
          row.push(Number(value));
        }
        result.push(row);
      }
      expect(JSON.stringify(result)).toStrictEqual(JSON.stringify(EXPECTED));
    }, 120_000);
  });

  describe('reals', () => {
    it('can work with numerals', async () => {
      const { Real, And } = api.Context('main');
      const n1 = Real.val('1/2');
      const n2 = Real.val('0.5');
      const n3 = Real.val(0.5);
      await prove(And(n1.eq(n2), n1.eq(n3)));

      const n4 = Real.val('-1/3');
      const n5 = Real.val('-0.3333333333333333333333333333333333');
      await prove(n4.neq(n5));
    });

    it('can do non-linear arithmetic', async () => {
      api.setParam('pp.decimal', true);
      api.setParam('pp.decimal_precision', 20);
      const { Real, Solver, isReal, isRealVal } = api.Context('main');
      const x = Real.const('x');
      const y = Real.const('y');
      const z = Real.const('z');

      const solver = new Solver();
      solver.add(x.mul(x).add(y.mul(y)).eq(1)); // x^2 + y^2 == 1
      solver.add(x.mul(x).mul(x).add(z.mul(z).mul(z)).lt('1/2')); // x^3 + z^3 < 1/2

      expect(await solver.check()).toStrictEqual('sat');
      const model = solver.model();

      expect(isRealVal(model.get(x))).toStrictEqual(true);
      // solution of y is a polynomial
      // https://stackoverflow.com/a/69740906
      expect(isReal(model.get(y))).toStrictEqual(true);
      expect(isRealVal(model.get(z))).toStrictEqual(true);
    });
  });

  describe('bitvectors', () => {
    it('can do simple proofs', async () => {
      const { BitVec, Concat, Implies, isBitVecVal } = api.Context('main');

      const x = BitVec.const('x', 32);

      const sSol = (await solve(x.sub(10).sle(0).eq(x.sle(10)))).get(x); // signed:   (x - 10 <= 0) == (x <= 10)
      const uSol = (await solve(x.sub(10).ule(0).eq(x.ule(10)))).get(x); // unsigned: (x - 10 <= 0) == (x <= 10)

      assert(isBitVecVal(sSol) && isBitVecVal(uSol));
      let v = sSol.asSignedValue();
      expect(v - 10n <= 0n === v <= 10n).toStrictEqual(true);
      v = uSol.value();
      expect(v - 10n <= 0n === v <= 10n).toStrictEqual(true);

      const y = BitVec.const('y', 32);

      await prove(Implies(Concat(x, y).eq(Concat(y, x)), x.eq(y)));
    }, 10_000 /* timeout ms */);

    it('finds x and y such that: x ^ y - 103 == x * y', async () => {
      const { BitVec, isBitVecVal } = api.Context('main');

      const x = BitVec.const('x', 32);
      const y = BitVec.const('y', 32);

      const model = await solve(x.xor(y).sub(103).eq(x.mul(y)));
      const xSol = model.get(x);
      const ySol = model.get(y);
      assert(isBitVecVal(xSol) && isBitVecVal(ySol));
      const xv = xSol.asSignedValue();
      const yv = ySol.asSignedValue();

      // this solutions wraps around so we need to check using modulo
      expect((xv ^ yv) - 103n === (xv * yv) % 2n ** 32n).toStrictEqual(true);
    });
  });

  describe('arrays', () => {
    it('Example 1', async () => {
      const Z3 = api.Context('main');

      const arr = Z3.Array.const('arr', Z3.Int.sort(), Z3.Int.sort());
      const [idx, val] = Z3.Int.consts('idx val');

      const conjecture = arr.store(idx, val).select(idx).eq(val);
      await prove(conjecture);
    });

    it('domain and range type inference', async () => {
      const { BitVec, Array, isArray, isArraySort } = api.Context('main');

      const arr = Array.const('arr', BitVec.sort(160), BitVec.sort(256));

      const domain = arr.domain();
      expect(domain.size()).toStrictEqual(160);
      expect(arr.domain_n(0).size()).toStrictEqual(160);
      const range = arr.range();
      expect(range.size()).toStrictEqual(256);

      assert(isArray(arr) && isArraySort(arr.sort));

      const arr2 = Array.const('arr2', BitVec.sort(1), BitVec.sort(2), BitVec.sort(3));
      const dom2 = arr2.domain_n(1);

      // We can call size() on dom2 and see that it is two bits
      // purely from type inference
      expectType<2>(dom2.size());

      // Won't let us create an array constant with only one of domain/range
      // and is detected at compile time
      // @ts-expect-error
      const arr3 = Array.const('arr3', BitVec.sort(1));
    });

    it('can do simple proofs', async () => {
      const { BitVec, Array, isArray, isArraySort, isConstArray, Eq, Not } = api.Context('main');

      const idx = BitVec.const('idx', 160);
      const val = BitVec.const('val', 256);

      const FIVE_VAL = BitVec.val(5, 256);

      const arr = Array.const('arr', BitVec.sort(160), BitVec.sort(256));

      const constArr = Array.K(BitVec.sort(160), FIVE_VAL);
      assert(isArray(arr) && isArraySort(arr.sort) && isConstArray(constArr));

      const arr2 = arr.store(0, 5);
      await prove(Eq(arr2.select(0), FIVE_VAL));
      await prove(Not(Eq(arr2.select(0), BitVec.val(6, 256))));
      await prove(Eq(arr2.store(idx, val).select(idx), constArr.store(idx, val).select(idx)));
    }, 10_000 /* timeout ms */);

    it('Finds arrays that differ but that sum to the same', async () => {
      const Z3 = api.Context('main');
      const { Array, BitVec } = Z3;

      const mod = 1n << 32n;

      const arr1 = Array.const('arr', BitVec.sort(2), BitVec.sort(32));
      const arr2 = Array.const('arr2', BitVec.sort(2), BitVec.sort(32));

      const same_sum = arr1
        .select(0)
        .add(arr1.select(1))
        .add(arr1.select(2))
        .add(arr1.select(3))
        .eq(arr2.select(0).add(arr2.select(1)).add(arr2.select(2)).add(arr2.select(3)));

      const different = arr1
        .select(0)
        .neq(arr2.select(0))
        .or(arr1.select(1).neq(arr2.select(1)))
        .or(arr1.select(2).neq(arr2.select(2)))
        .or(arr1.select(3).neq(arr2.select(3)));

      const model = await solve(same_sum.and(different));

      const arr1Vals = [0, 1, 2, 3].map(i => model.eval(arr1.select(i)).value());
      const arr2Vals = [0, 1, 2, 3].map(i => model.eval(arr2.select(i)).value());
      expect(arr1Vals.reduce((a, b) => a + b, 0n) % mod === arr2Vals.reduce((a, b) => a + b, 0n) % mod);
      for (let i = 0; i < 4; i++) {
        expect(arr1Vals[i] !== arr2Vals[i]);
      }
    });

    it('Array type inference', async () => {
      const z3 = api.Context('main');

      const Z3_ADDR = z3.BitVec.const('Vault_addr', 160);
      const Z3_GLOBAL_STORAGE = z3.Array.const(
        'global_storage',
        z3.BitVec.sort(160),
        z3.Array.sort(z3.BitVec.sort(160), z3.BitVec.sort(256)),
      );
      const Z3_STORAGE = Z3_GLOBAL_STORAGE.select(Z3_ADDR);

      // We are so far unable to properly infer the type of Z3_STORAGE
      // expectType<
      //   SMTArray<'main', [BitVecSort<160>], BitVecSort<256>>
      // >(Z3_STORAGE);
    });
  });

  describe('sets', () => {
    it('Example 1', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');

      const conjecture = set.contains(a).and(set.contains(b)).implies(Z3.EmptySet(Z3.Int.sort()).neq(set));
      await prove(conjecture);
    });

    it('Example 2', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');

      const conjecture = set.contains(a).and(set.contains(b)).implies(Z3.Set.val([a, b], Z3.Int.sort()).subsetOf(set));
      await prove(conjecture);
    });

    it('Example 3', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');

      const conjecture = set.contains(a).and(set.contains(b)).and(Z3.Set.val([a, b], Z3.Int.sort()).eq(set));
      await solve(conjecture);
    });

    it('Intersection 1', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');
      const abset = Z3.Set.val([a, b], Z3.Int.sort());

      const conjecture = set.intersect(abset).subsetOf(abset);
      await prove(conjecture);
    });
    
    it('Intersection 2', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');
      const abset = Z3.Set.val([a, b], Z3.Int.sort());

      const conjecture = set.subsetOf(set.intersect(abset));
      await solve(conjecture);
    });

    it('Union 1', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');
      const abset = Z3.Set.val([a, b], Z3.Int.sort());

      const conjecture = set.subsetOf(set.union(abset));
      await prove(conjecture);
    });
    
    it('Union 2', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');
      const abset = Z3.Set.val([a, b], Z3.Int.sort());

      const conjecture = set.union(abset).subsetOf(abset);
      await solve(conjecture);
    });
    
    it('Complement 1', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const a = Z3.Int.const('a');

      const conjecture = set.complement().complement().eq(set)
      await prove(conjecture);
    });
    it('Complement 2', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());
      const a = Z3.Int.const('a');

      const conjecture = set.contains(a).implies(Z3.Not(set.complement().contains(a)))
      await prove(conjecture);
    });
    
    it('Difference', async () => {
      const Z3 = api.Context('main');

      const [set1, set2] = Z3.Set.consts('set1 set2', Z3.Int.sort());
      const a = Z3.Int.const('a');

      const conjecture = set1.contains(a).implies(Z3.Not(set2.diff(set1).contains(a)))
      
      await prove(conjecture);
    });
    
    it('FullSet', async () => {
      const Z3 = api.Context('main');

      const set = Z3.Set.const('set', Z3.Int.sort());

      const conjecture = set.complement().eq(Z3.FullSet(Z3.Int.sort()).diff(set));
      
      await prove(conjecture);
    });

    it('SetDel', async () => {
      const Z3 = api.Context('main');

      const empty = Z3.Set.empty(Z3.Int.sort());
      const [a, b] = Z3.Int.consts('a b');

      const conjecture = empty.add(a).add(b).del(a).del(b).eq(empty);
      
      await prove(conjecture);
    });
  });

  describe('quantifiers', () => {
    it('Basic Universal', async () => {
      const Z3 = api.Context('main');

      const [x, y] = Z3.Int.consts('x y');

      const conjecture = Z3.ForAll([x, y], x.neq(y).implies(x.lt(y).or(x.gt(y))));
      expect(Z3.isBool(conjecture)).toBeTruthy();
      expect(conjecture.var_name(0)).toBe('x');
      expect(conjecture.var_sort(0).eqIdentity(Z3.Int.sort())).toBeTruthy();
      expect(conjecture.var_name(1)).toBe('y');
      expect(conjecture.var_sort(1).eqIdentity(Z3.Int.sort())).toBeTruthy();
      await prove(conjecture);
    });

    it('Basic Existential', async () => {
      const Z3 = api.Context('main');

      const [x, y, z] = Z3.Int.consts('x y z');

      const quantifier = Z3.Exists([z], Z3.Not(z.lt(x)).and(Z3.Not(z.gt(y))));
      expect(Z3.isBool(quantifier)).toBeTruthy();
      expect(quantifier.var_name(0)).toBe('z');
      expect(quantifier.var_sort(0).eqIdentity(Z3.Int.sort())).toBeTruthy();

      const conjecture = Z3.Not(x.gt(y)).implies(quantifier); // Can be trivially discovered with z = x or x = y
      await prove(conjecture);
    });

    it('Basic Lambda', async () => {
      const Z3 = api.Context('main');

      const [x, y] = Z3.Int.consts('x y z');
      const L = Z3.Lambda([x, y], x.add(y));
      expect(Z3.isArraySort(L.sort)).toBeTruthy();
      expect(Z3.isArray(L)).toBeFalsy();
      expect(L.var_name(0)).toBe('x');
      expect(L.var_sort(0).eqIdentity(Z3.Int.sort())).toBeTruthy();
      expect(L.var_name(1)).toBe('y');
      expect(L.var_sort(1).eqIdentity(Z3.Int.sort())).toBeTruthy();

      const conjecture = L.select(Z3.Int.val(2), Z3.Int.val(5)).eq(Z3.Int.val(7));
      await prove(conjecture);
    });

    it('Loading Quantifier Preserves Type', async () => {
      const Z3 = api.Context('main');

      const [x, y, z] = Z3.Int.consts('x y z');
      const quantifier = Z3.Exists([z], Z3.Not(z.lt(x)).and(Z3.Not(z.gt(y))));
      expect(Z3.isBool(quantifier)).toBeTruthy();

      const solver = new Z3.Solver();
      solver.add(quantifier);

      const dumped_str = solver.toString();

      const solver2 = new Z3.Solver();
      solver2.fromString(dumped_str);
      const quantifier2 = solver2.assertions().get(0) as unknown as Quantifier;
      expect(Z3.isBool(quantifier2)).toBeTruthy();
      expect(quantifier2.var_name(0)).toBe('z');
    });
  });

  describe('uninterpreted functions', () => {
    it('Type Inference', async () => {
      const Z3 = api.Context('main');

      const f = Z3.Function.declare('f', Z3.Int.sort(), Z3.Bool.sort());
      const input = Z3.Int.val(6);
      const output = f.call(input);
      expectType<Bool>(output);
      expect(output.sort.eqIdentity(Z3.Bool.sort())).toBeTruthy();
    });
  });

  describe('Solver', () => {
    it('can use push and pop', async () => {
      const { Solver, Int } = api.Context('main');
      const solver = new Solver();
      const x = Int.const('x');

      solver.add(x.gt(0));

      expect(await solver.check()).toStrictEqual('sat');

      solver.push();
      solver.add(x.lt(0));

      expect(solver.numScopes()).toStrictEqual(1);
      expect(await solver.check()).toStrictEqual('unsat');

      solver.pop();

      expect(solver.numScopes()).toStrictEqual(0);
      expect(await solver.check()).toStrictEqual('sat');
    });

    it('can find multiple solutions', async () => {
      const { Int, isIntVal } = api.Context('main');

      const x = Int.const('x');

      const solutions = await asyncToArray(allSolutions(x.ge(1), x.le(5)));
      expect(solutions.length).toStrictEqual(5);
      const results = solutions
        .map(solution => {
          const expr = solution.eval(x);
          assert(isIntVal(expr));
          return expr.value();
        })
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
      const Z3 = api.Context('main');
      const { Solver, Int } = Z3;
      const solver = new Solver();

      const vector = new Z3.AstVector<Arith>();
      for (let i = 0; i < 5; i++) {
        vector.push(Int.const(`int__${i}`));
      }

      const length = vector.length();
      for (let i = 0; i < length; i++) {
        solver.add(vector.get(i).gt(1));
      }

      expect(await solver.check()).toStrictEqual('sat');
    });
  });

  describe('Substitution', () => {
    it('basic variable substitution', async () => {
      const { Int, substitute } = api.Context('main');
      const x = Int.const('x');
      const y = Int.const('y');
      const z = Int.const('z');

      const expr = x.add(y);
      const subst = substitute(expr, [x, z]);
      expect(subst.eqIdentity(z.add(y))).toBeTruthy();
    });

    it('term substitution', async () => {
      const { Int, substitute } = api.Context('main');
      const x = Int.const('x');
      const y = Int.const('y');
      const z = Int.const('z');

      const expr = x.add(y).mul(Int.val(1).sub(x.add(y)));
      const subst = substitute(expr, [x.add(y), z]);
      expect(subst.eqIdentity(z.mul(Int.val(1).sub(z)))).toBeTruthy();
    });
  });

  describe('Model', () => {
    it('Assigning constants', async () => {
      const { Int, Model } = api.Context('main');
      const m = new Model();

      const [x, y] = Int.consts('x y');

      m.updateValue(x, Int.val(6));
      m.updateValue(y, Int.val(12));

      expect(m.eval(x.add(y)).eqIdentity(Int.val(18))).toBeTruthy();
    });

    it('Creating Func Interpretations', async () => {
      const { Int, Function, Model } = api.Context('main');
      const m = new Model();

      const f = Function.declare('f', Int.sort(), Int.sort(), Int.sort());

      const f_interp = m.addFuncInterp(f, 0);
      f_interp.addEntry([Int.val(1), Int.val(2)], Int.val(3));
      f_interp.addEntry([Int.val(4), Int.val(5)], Int.val(6));

      expect(m.eval(f.call(1, 2)).eqIdentity(Int.val(3))).toBeTruthy();
      expect(m.eval(f.call(4, 5)).eqIdentity(Int.val(6))).toBeTruthy();
      expect(m.eval(f.call(0, 0)).eqIdentity(Int.val(0))).toBeTruthy();
    });
  });

  describe('optimize', () => {
    it('maximization problem over reals', async () => {
      const { Real, Optimize } = api.Context('main');

      const opt = new Optimize();
      const x = Real.const('x');
      const y = Real.const('y');
      const z = Real.const('z');

      opt.add(x.ge(0), y.ge(0), z.ge(0));
      opt.add(x.le(1), y.le(1), z.le(1));
      opt.maximize(x.mul(7).add(y.mul(9)).sub(z.mul(3)));

      const result = await opt.check();
      expect(result).toStrictEqual('sat');
      const model = opt.model();
      expect(model.eval(x).eqIdentity(Real.val(1))).toBeTruthy();
      expect(model.eval(y).eqIdentity(Real.val(1))).toBeTruthy();
      expect(model.eval(z).eqIdentity(Real.val(0))).toBeTruthy();
    });

    it('minimization problem over integers using addSoft', async () => {
      const { Int, Optimize } = api.Context('main');

      const opt = new Optimize();
      const x = Int.const('x');
      const y = Int.const('y');
      const z = Int.const('z');

      opt.add(x.ge(0), y.ge(0));
      opt.add(x.le(1), y.le(1));
      opt.addSoft(x.eq(1), 2);
      opt.addSoft(y.eq(1), 1);
      opt.add(z.eq(x.mul(5).add(y.mul(5))));
      opt.add(z.le(5));
      opt.minimize(z);

      const result = await opt.check();
      expect(result).toStrictEqual('sat');
      const model = opt.model();
      expect(model.eval(x).eqIdentity(Int.val(1))).toBeTruthy();
      expect(model.eval(y).eqIdentity(Int.val(0))).toBeTruthy();
      expect(model.eval(z).eqIdentity(Int.val(5))).toBeTruthy();
    });
  });
});
