// TODO(ritave): Add typing for Context Options
//               https://github.com/Z3Prover/z3/pull/6048#discussion_r883391669
// TODO(ritave): Add an error handler
// TODO(ritave): Add support for building faster floats without support for Safari
// TODO(ritave): Use Z3_DECLARE_CLOSURE macro to generate code https://github.com/Z3Prover/z3/pull/6048#discussion_r884155462
// TODO(ritave): Add pretty printing
// TODO(ritave): Make Z3 multi-threaded
// TODO(ritave): If a test times out, jest kills it, and the global state of Z3 is left in an unexpected state.
//               This occurs specifically during longer check(). Afterwards, all next tests will fail to run
//               thinking the previous call was not finished. Find a way to stop execution and clean up the global state
import { Mutex } from 'async-mutex';
import {
  Z3Core,
  Z3_ast,
  Z3_ast_kind,
  Z3_ast_map,
  Z3_ast_print_mode,
  Z3_ast_vector,
  Z3_context,
  Z3_decl_kind,
  Z3_func_decl,
  Z3_func_interp,
  Z3_lbool,
  Z3_model,
  Z3_parameter_kind,
  Z3_probe,
  Z3_solver,
  Z3_sort,
  Z3_sort_kind,
  Z3_symbol,
  Z3_symbol_kind,
  Z3_tactic,
} from '../low-level';
import {
  AnyAst,
  AnyExpr,
  AnySort,
  Arith,
  ArithSort,
  Ast,
  AstMap,
  AstMapCtor,
  AstVector,
  AstVectorCtor,
  BitVec,
  BitVecNum,
  BitVecSort,
  Bool,
  BoolSort,
  CheckSatResult,
  CoercibleRational,
  CoercibleToBitVec,
  CoercibleToExpr,
  CoercibleToExprMap,
  Context,
  ContextCtor,
  Expr,
  FuncDecl,
  FuncDeclSignature,
  FuncInterp,
  IntNum,
  Model,
  Probe,
  RatNum,
  sat,
  Solver,
  Sort,
  SortToExprMap,
  Tactic,
  unknown,
  unsat,
  Z3Error,
  Z3HighLevel,
} from './types';
import { allSatisfy, assert, assertExhaustive, autoBind } from './utils';

const FALLBACK_PRECISION = 17;

const asyncMutex = new Mutex();

function isCoercibleRational(obj: any): obj is CoercibleRational {
  // prettier-ignore
  const r = (
    (obj !== null &&
      (typeof obj === 'object' || typeof obj === 'function')) &&
    (obj.numerator !== null &&
      (typeof obj.numerator === 'number' || typeof obj.numerator === 'bigint')) &&
    (obj.denominator !== null &&
      (typeof obj.denominator === 'number' || typeof obj.denominator === 'bigint'))
  );
  r &&
    assert(
      (typeof obj.numerator !== 'number' || Number.isSafeInteger(obj.numerator)) &&
        (typeof obj.denominator !== 'number' || Number.isSafeInteger(obj.denominator)),
      'Fraction numerator and denominator must be integers',
    );
  return r;
}

export function createApi(Z3: Z3Core): Z3HighLevel {
  // TODO(ritave): Create a custom linting rule that checks if the provided callbacks to cleanup
  //               Don't capture `this`
  const cleanup = new FinalizationRegistry<() => void>(callback => callback());

  function enableTrace(tag: string) {
    Z3.enable_trace(tag);
  }

  function disableTrace(tag: string) {
    Z3.disable_trace(tag);
  }

  function getVersion() {
    return Z3.get_version();
  }

  function getVersionString() {
    const { major, minor, build_number } = Z3.get_version();
    return `${major}.${minor}.${build_number}`;
  }

  function getFullVersion() {
    return Z3.get_full_version();
  }

  function openLog(filename: string) {
    return Z3.open_log(filename);
  }

  function appendLog(s: string) {
    Z3.append_log(s);
  }

  function setParam(key: string, value: any): void;
  function setParam(params: Record<string, any>): void;
  function setParam(key: string | Record<string, any>, value?: any) {
    if (typeof key === 'string') {
      Z3.global_param_set(key, value.toString());
    } else {
      assert(value === undefined, "Can't provide a Record and second parameter to set_param at the same time");
      Object.entries(key).forEach(([key, value]) => setParam(key, value));
    }
  }

  function resetParams() {
    Z3.global_param_reset_all();
  }

  function getParam(name: string) {
    return Z3.global_param_get(name);
  }

  function isContext(obj: unknown): obj is Context {
    return obj instanceof ContextImpl;
  }

  class ContextImpl implements Context {
    declare readonly __typename: Context['__typename'];

    readonly ptr: Z3_context;
    readonly name: string;

    constructor(name: string, params: Record<string, any> = {}) {
      const cfg = Z3.mk_config();
      Object.entries(params).forEach(([key, value]) => Z3.set_param_value(cfg, key, value.toString()));
      const context = Z3.mk_context_rc(cfg);

      this.ptr = context;
      this.name = name;

      Z3.set_ast_print_mode(this.ptr, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
      Z3.del_config(cfg);

      // We want to bind functions and operations to `this` inside Context
      // So that the user can write things like this and have it work:
      // ```
      // const { And, Or } = new Context('main');
      // ```
      //
      // Typescript doesn't handle overloading of method fields, only
      // methods. We can't use closures to bind this, so we use auto-bind library
      // ```
      // class {
      //   // This works
      //   test(a: boolean): boolean;
      //   test(a: number): number;
      //   test(a: boolean | number): boolean | number {
      //     return 0;
      //   }
      //
      //   // This fails to compile
      //   test2: (a: boolean) => boolean;
      //   test2: (a: number) => number;
      //   test2 = (a: boolean | number): boolean | number => {
      //     return 0;
      //   }
      // }
      // ```
      autoBind(this);

      cleanup.register(this, () => Z3.del_context(context));
    }

    ///////////////
    // Functions //
    ///////////////
    interrupt(): void {
      Z3.interrupt(this.ptr);
    }

    isModel(obj: unknown): obj is Model {
      const r = obj instanceof ModelImpl;
      r && this._assertContext(obj);
      return r;
    }

    isAst(obj: unknown): obj is Ast {
      const r = obj instanceof AstImpl;
      r && this._assertContext(obj);
      return r;
    }

    isSort(obj: unknown): obj is Sort {
      const r = obj instanceof SortImpl;
      r && this._assertContext(obj);
      return r;
    }

    isFuncDecl(obj: unknown): obj is FuncDecl {
      const r = obj instanceof FuncDeclImpl;
      r && this._assertContext(obj);
      return r;
    }

    isApp(obj: unknown): boolean {
      if (!this.isExpr(obj)) {
        return false;
      }
      const kind = Z3.get_ast_kind(this.ptr, obj.ast);
      return kind === Z3_ast_kind.Z3_NUMERAL_AST || kind === Z3_ast_kind.Z3_APP_AST;
    }

    isConst(obj: unknown): boolean {
      return this.isExpr(obj) && this.isApp(obj) && obj.numArgs() === 0;
    }

    isExpr(obj: unknown): obj is Expr {
      const r = obj instanceof ExprImpl;
      r && this._assertContext(obj);
      return r;
    }

    isVar(obj: unknown): boolean {
      return this.isExpr(obj) && Z3.get_ast_kind(this.ptr, obj.ast) === Z3_ast_kind.Z3_VAR_AST;
    }

    isAppOf(obj: unknown, kind: Z3_decl_kind): boolean {
      return this.isExpr(obj) && this.isApp(obj) && obj.decl().kind() === kind;
    }

    isBool(obj: unknown): obj is Bool {
      const r = obj instanceof BoolImpl;
      r && this._assertContext(obj);
      return r;
    }

    isTrue(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_TRUE);
    }

    isFalse(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_FALSE);
    }

    isAnd(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_AND);
    }

    isOr(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_OR);
    }

    isImplies(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_IMPLIES);
    }

    isNot(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_NOT);
    }

    isEq(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_EQ);
    }

    isDistinct(obj: unknown): boolean {
      return this.isAppOf(obj, Z3_decl_kind.Z3_OP_DISTINCT);
    }

    isArith(obj: unknown): obj is Arith {
      const r = obj instanceof ArithImpl;
      r && this._assertContext(obj);
      return r;
    }

    isArithSort(obj: unknown): obj is ArithSort {
      const r = obj instanceof ArithSortImpl;
      r && this._assertContext(obj);
      return r;
    }

    isInt(obj: unknown): boolean {
      return this.isArith(obj) && this.isIntSort(obj.sort);
    }

    isIntVal(obj: unknown): obj is IntNum {
      const r = obj instanceof IntNumImpl;
      r && this._assertContext(obj);
      return r;
    }

    isIntSort(obj: unknown): boolean {
      return this.isSort(obj) && obj.kind() === Z3_sort_kind.Z3_INT_SORT;
    }

    isReal(obj: unknown): boolean {
      return this.isArith(obj) && this.isRealSort(obj.sort);
    }

    isRealVal(obj: unknown): obj is RatNum {
      const r = obj instanceof RatNumImpl;
      r && this._assertContext(obj);
      return r;
    }

    isRealSort(obj: unknown): boolean {
      return this.isSort(obj) && obj.kind() === Z3_sort_kind.Z3_REAL_SORT;
    }

    isBitVecSort(obj: unknown): obj is BitVecSort {
      const r = obj instanceof BitVecSortImpl;
      r && this._assertContext(obj);
      return r;
    }

    isBitVec(obj: unknown): obj is BitVec {
      const r = obj instanceof BitVecImpl;
      r && this._assertContext(obj);
      return r;
    }

    isBitVecVal(obj: unknown): obj is BitVecNum {
      const r = obj instanceof BitVecNumImpl;
      r && this._assertContext(obj);
      return r;
    }

    isProbe(obj: unknown): obj is Probe {
      const r = obj instanceof ProbeImpl;
      r && this._assertContext(obj);
      return r;
    }

    isTactic(obj: unknown): obj is Tactic {
      const r = obj instanceof TacticImpl;
      r && this._assertContext(obj);
      return r;
    }

    isAstVector(obj: unknown): obj is AstVector {
      const r = obj instanceof AstVectorImpl;
      r && this._assertContext(obj);
      return r;
    }

    eqIdentity(a: Ast, b: Ast): boolean {
      return a.eqIdentity(b);
    }

    getVarIndex(obj: Expr): number {
      assert(this.isVar(obj), 'Z3 bound variable expected');
      return Z3.get_index_value(this.ptr, obj.ast);
    }

    from(primitive: boolean): Bool;
    from(primitive: number | CoercibleRational): RatNum;
    from(primitive: bigint): IntNum;
    from<T extends Expr>(expr: T): T;
    from(expr: CoercibleToExpr): AnyExpr;
    from(value: CoercibleToExpr): AnyExpr {
      if (typeof value === 'boolean') {
        return this.Bool.val(value);
      } else if (typeof value === 'number' || isCoercibleRational(value)) {
        return this.Real.val(value);
      } else if (typeof value === 'bigint') {
        return this.Int.val(value);
      } else if (this.isExpr(value)) {
        return value;
      }
      assert(false);
    }

    async solve(...assertions: Bool[]): Promise<Model | typeof unsat | typeof unknown> {
      const solver = new this.Solver();
      solver.add(...assertions);
      const result = await solver.check();
      if (result === sat) {
        return solver.model();
      }
      return result;
    }

    /////////////
    // Classes //
    /////////////
    readonly Solver = SolverImpl.bind(SolverImpl, this);
    readonly Model = ModelImpl.bind(ModelImpl, this);
    readonly Tactic = TacticImpl.bind(TacticImpl, this);
    readonly AstVector = AstVectorImpl.bind(AstVectorImpl, this) as AstVectorCtor<any>;
    readonly AstMap = AstMapImpl.bind(AstMapImpl, this) as AstMapCtor<any>;

    /////////////
    // Objects //
    /////////////
    readonly Sort = {
      declare: (name: string) => new SortImpl(this, Z3.mk_uninterpreted_sort(this.ptr, this._toSymbol(name))),
    };
    readonly Function = {
      declare: (name: string, ...signature: FuncDeclSignature<any>) => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        this._assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          this._assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl(this, Z3.mk_func_decl(this.ptr, this._toSymbol(name), dom, rng.ptr));
      },
      fresh: (...signature: FuncDeclSignature<any>) => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        this._assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          this._assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl(this, Z3.mk_fresh_func_decl(this.ptr, 'f', dom, rng.ptr));
      },
    };
    readonly RecFunc = {
      declare: (name: string, ...signature: FuncDeclSignature<any>) => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        this._assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          this._assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl(this, Z3.mk_rec_func_decl(this.ptr, this._toSymbol(name), dom, rng.ptr));
      },

      addDefinition: (f: FuncDecl, args: Expr[], body: Expr) => {
        this._assertContext(f, ...args, body);
        Z3.add_rec_def(
          this.ptr,
          f.ptr,
          args.map(arg => arg.ast),
          body.ast,
        );
      },
    };
    readonly Bool = {
      sort: () => new BoolSortImpl(this, Z3.mk_bool_sort(this.ptr)),

      const: (name: string) => new BoolImpl(this, Z3.mk_const(this.ptr, this._toSymbol(name), this.Bool.sort().ptr)),
      consts: (names: string | string[]) => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => this.Bool.const(name));
      },
      vector: (prefix: string, count: number) => {
        const result = [];
        for (let i = 0; i < count; i++) {
          result.push(this.Bool.const(`${prefix}__${i}`));
        }
        return result;
      },
      fresh: (prefix = 'b') => new BoolImpl(this, Z3.mk_fresh_const(this.ptr, prefix, this.Bool.sort().ptr)),

      val: (value: boolean) => {
        if (value) {
          return new BoolImpl(this, Z3.mk_true(this.ptr));
        }
        return new BoolImpl(this, Z3.mk_false(this.ptr));
      },
    };
    readonly Int = {
      sort: () => new ArithSortImpl(this, Z3.mk_int_sort(this.ptr)),

      const: (name: string) => new ArithImpl(this, Z3.mk_const(this.ptr, this._toSymbol(name), this.Int.sort().ptr)),
      consts: (names: string | string[]) => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => this.Int.const(name));
      },
      vector: (prefix: string, count: number) => {
        const result = [];
        for (let i = 0; i < count; i++) {
          result.push(this.Int.const(`${prefix}__${i}`));
        }
        return result;
      },
      fresh: (prefix = 'x') => new ArithImpl(this, Z3.mk_fresh_const(this.ptr, prefix, this.Int.sort().ptr)),

      val: (value: number | bigint | string) => {
        assert(typeof value === 'bigint' || typeof value === 'string' || Number.isSafeInteger(value));
        return new IntNumImpl(this, Z3.mk_numeral(this.ptr, value.toString(), this.Int.sort().ptr));
      },
    };
    readonly Real = {
      sort: () => new ArithSortImpl(this, Z3.mk_real_sort(this.ptr)),

      const: (name: string) => new ArithImpl(this, Z3.mk_const(this.ptr, this._toSymbol(name), this.Real.sort().ptr)),
      consts: (names: string | string[]) => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => this.Real.const(name));
      },
      vector: (prefix: string, count: number) => {
        const result = [];
        for (let i = 0; i < count; i++) {
          result.push(this.Real.const(`${prefix}__${i}`));
        }
        return result;
      },
      fresh: (prefix = 'b') => new ArithImpl(this, Z3.mk_fresh_const(this.ptr, prefix, this.Real.sort().ptr)),

      val: (value: number | bigint | string | CoercibleRational) => {
        if (isCoercibleRational(value)) {
          value = `${value.numerator}/${value.denominator}`;
        }
        return new RatNumImpl(this, Z3.mk_numeral(this.ptr, value.toString(), this.Real.sort().ptr));
      },
    };
    readonly BitVec = {
      sort: (bits: number): BitVecSort<any> => {
        assert(Number.isSafeInteger(bits), 'number of bits must be an integer');
        return new BitVecSortImpl(this, Z3.mk_bv_sort(this.ptr, bits));
      },

      const: (name: string, bits: number | BitVecSort): BitVec<any> =>
        new BitVecImpl(
          this,
          Z3.mk_const(this.ptr, this._toSymbol(name), this.isBitVecSort(bits) ? bits.ptr : this.BitVec.sort(bits).ptr),
        ),

      consts: (names: string | string[], bits: number | BitVecSort): BitVec<any>[] => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => this.BitVec.const(name, bits));
      },

      val: (value: bigint | number | boolean, bits: number | BitVecSort): BitVecNum<any> => {
        if (value === true) {
          return this.BitVec.val(1, bits);
        } else if (value === false) {
          return this.BitVec.val(0, bits);
        }
        return new BitVecNumImpl(
          this,
          Z3.mk_numeral(this.ptr, value.toString(), this.isBitVecSort(bits) ? bits.ptr : this.BitVec.sort(bits).ptr),
        );
      },
    };

    ////////////////
    // Operations //
    ////////////////
    If(condition: Probe, onTrue: Tactic, onFalse: Tactic): Tactic;
    If<OnTrueRef extends CoercibleToExpr, OnFalseRef extends CoercibleToExpr>(
      condition: Bool | boolean,
      onTrue: OnTrueRef,
      onFalse: OnFalseRef,
    ): CoercibleToExprMap<OnTrueRef | OnFalseRef>;
    If(
      condition: Bool | Probe | boolean,
      onTrue: CoercibleToExpr | Tactic,
      onFalse: CoercibleToExpr | Tactic,
    ): Expr | Tactic {
      if (this.isProbe(condition) && this.isTactic(onTrue) && this.isTactic(onFalse)) {
        return this.Cond(condition, onTrue, onFalse);
      }
      assert(
        !this.isProbe(condition) && !this.isTactic(onTrue) && !this.isTactic(onFalse),
        'Mixed expressions and goals',
      );
      if (typeof condition === 'boolean') {
        condition = this.Bool.val(condition);
      }
      onTrue = this.from(onTrue);
      onFalse = this.from(onFalse);
      return this._toExpr(Z3.mk_ite(this.ptr, condition.ptr, onTrue.ast, onFalse.ast));
    }

    Distinct(...exprs: CoercibleToExpr[]): Bool {
      assert(exprs.length > 0, "Can't make Distinct ouf of nothing");

      return new BoolImpl(
        this,
        Z3.mk_distinct(
          this.ptr,
          exprs.map(expr => {
            expr = this.from(expr);
            this._assertContext(expr);
            return expr.ast;
          }),
        ),
      );
    }

    Const<S extends Sort>(name: string, sort: S): SortToExprMap<S> {
      this._assertContext(sort);
      return this._toExpr(Z3.mk_const(this.ptr, this._toSymbol(name), sort.ptr)) as SortToExprMap<S>;
    }

    Consts<S extends Sort>(names: string | string[], sort: S): SortToExprMap<S>[] {
      this._assertContext(sort);
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => this.Const(name, sort));
    }

    FreshConst<S extends Sort>(sort: S, prefix: string = 'c'): SortToExprMap<S> {
      this._assertContext(sort);
      return this._toExpr(Z3.mk_fresh_const(sort.ctx.ptr, prefix, sort.ptr)) as SortToExprMap<S>;
    }

    Var<S extends Sort>(idx: number, sort: S): SortToExprMap<S> {
      this._assertContext(sort);
      return this._toExpr(Z3.mk_bound(sort.ctx.ptr, idx, sort.ptr)) as SortToExprMap<S>;
    }

    Implies(a: Bool | boolean, b: Bool | boolean): Bool {
      a = this.from(a) as Bool;
      b = this.from(b) as Bool;
      this._assertContext(a, b);
      return new BoolImpl(this, Z3.mk_implies(this.ptr, a.ptr, b.ptr));
    }

    Eq(a: CoercibleToExpr, b: CoercibleToExpr): Bool {
      a = this.from(a);
      b = this.from(b);
      this._assertContext(a, b);
      return a.eq(b);
    }

    Xor(a: Bool | boolean, b: Bool | boolean): Bool {
      a = this.from(a) as Bool;
      b = this.from(b) as Bool;
      this._assertContext(a, b);
      return new BoolImpl(this, Z3.mk_xor(this.ptr, a.ptr, b.ptr));
    }

    Not(a: Probe): Probe;
    Not(a: Bool | boolean): Bool;
    Not(a: Bool | boolean | Probe): Bool | Probe {
      if (typeof a === 'boolean') {
        a = this.from(a);
      }
      this._assertContext(a);
      if (this.isProbe(a)) {
        return new ProbeImpl(this, Z3.probe_not(this.ptr, a.ptr));
      }
      return new BoolImpl(this, Z3.mk_not(this.ptr, a.ptr));
    }

    And(): Bool;
    And(vector: AstVector<Bool>): Bool;
    And(...args: (Bool | boolean)[]): Bool;
    And(...args: Probe[]): Probe;
    And(...args: (AstVector<Bool> | Probe | Bool | boolean)[]): Bool | Probe {
      if (args.length == 1 && args[0] instanceof this.AstVector) {
        args = [...args[0].values()];
        assert(allSatisfy(args, this.isBool.bind(this)) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, this.isProbe.bind(this)) ?? false;
      if (allProbes) {
        return this._probeNary(Z3.probe_and, args as [Probe, ...Probe[]]);
      } else {
        args = args.map(this.from.bind(this)) as Bool[];
        this._assertContext(...(args as Bool[]));
        return new BoolImpl(
          this,
          Z3.mk_and(
            this.ptr,
            args.map(arg => (arg as Bool).ptr),
          ),
        );
      }
    }

    Or(): Bool;
    Or(vector: AstVector<Bool>): Bool;
    Or(...args: (Bool | boolean)[]): Bool;
    Or(...args: Probe[]): Probe;
    Or(...args: (AstVector<Bool> | Probe | Bool | boolean)[]): Bool | Probe {
      if (args.length == 1 && args[0] instanceof this.AstVector) {
        args = [...args[0].values()];
        assert(allSatisfy(args, this.isBool.bind(this)) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, this.isProbe.bind(this)) ?? false;
      if (allProbes) {
        return this._probeNary(Z3.probe_or, args as [Probe, ...Probe[]]);
      } else {
        args = args.map(this.from.bind(this)) as Bool[];
        this._assertContext(...(args as Bool[]));
        return new BoolImpl(
          this,
          Z3.mk_or(
            this.ptr,
            args.map(arg => (arg as Bool).ptr),
          ),
        );
      }
    }

    ToReal(expr: Arith | bigint): Arith {
      expr = this.from(expr) as Arith;
      this._assertContext(expr);
      assert(this.isInt(expr), 'Int expression expected');
      return new ArithImpl(this, Z3.mk_int2real(this.ptr, expr.ast));
    }

    ToInt(expr: Arith | number | CoercibleRational | string): Arith {
      if (!this.isExpr(expr)) {
        expr = this.Real.val(expr);
      }
      this._assertContext(expr);
      assert(this.isReal(expr), 'Real expression expected');
      return new ArithImpl(this, Z3.mk_real2int(this.ptr, expr.ast));
    }

    IsInt(expr: Arith | number | CoercibleRational | string): Bool {
      if (!this.isExpr(expr)) {
        expr = this.Real.val(expr);
      }
      this._assertContext(expr);
      assert(this.isReal(expr), 'Real expression expected');
      return new BoolImpl(this, Z3.mk_is_int(this.ptr, expr.ast));
    }

    Sqrt(a: Arith | number | bigint | string | CoercibleRational): Arith {
      if (!this.isExpr(a)) {
        a = this.Real.val(a);
      }
      return a.pow('1/2');
    }

    Cbrt(a: Arith | number | bigint | string | CoercibleRational): Arith {
      if (!this.isExpr(a)) {
        a = this.Real.val(a);
      }
      return a.pow('1/3');
    }

    BV2Int(a: BitVec, isSigned: boolean): Arith {
      this._assertContext(a);
      return new ArithImpl(this, Z3.mk_bv2int(this.ptr, a.ast, isSigned));
    }

    Int2BV(a: Arith | bigint | number, bits: number): BitVec<any> {
      if (this.isArith(a)) {
        assert(this.isInt(a), 'parameter must be an integer');
      } else {
        assert(typeof a !== 'number' || Number.isSafeInteger(a), 'parameter must not have decimal places');
        a = this.Int.val(a);
      }
      return new BitVecImpl(this, Z3.mk_int2bv(this.ptr, bits, a.ast));
    }

    Concat(...bitvecs: BitVec[]): BitVec {
      this._assertContext(...bitvecs);
      return bitvecs.reduce((prev, curr) => new BitVecImpl(this, Z3.mk_concat(this.ptr, prev.ast, curr.ast)));
    }

    Cond(probe: Probe, onTrue: Tactic, onFalse: Tactic): Tactic {
      this._assertContext(probe, onTrue, onFalse);
      return new this.Tactic(Z3.tactic_cond(this.ptr, probe.ptr, onTrue.ptr, onFalse.ptr));
    }

    /////////////
    // Private //
    /////////////
    _assertContext(...ctxs: (Context | { ctx: Context })[]) {
      ctxs.forEach(other => assert('ctx' in other ? this === other.ctx : this === other, 'Context mismatch'));
    }

    _toSymbol(s: string | number) {
      if (typeof s === 'number') {
        return Z3.mk_int_symbol(this.ptr, s);
      } else {
        return Z3.mk_string_symbol(this.ptr, s);
      }
    }

    _fromSymbol(sym: Z3_symbol) {
      const kind = Z3.get_symbol_kind(this.ptr, sym);
      switch (kind) {
        case Z3_symbol_kind.Z3_INT_SYMBOL:
          return Z3.get_symbol_int(this.ptr, sym);
        case Z3_symbol_kind.Z3_STRING_SYMBOL:
          return Z3.get_symbol_string(this.ptr, sym);
        default:
          assertExhaustive(kind);
      }
    }

    _toAst(ast: Z3_ast): AnyAst {
      switch (Z3.get_ast_kind(this.ptr, ast)) {
        case Z3_ast_kind.Z3_SORT_AST:
          return this._toSort(ast as Z3_sort);
        case Z3_ast_kind.Z3_FUNC_DECL_AST:
          return new FuncDeclImpl(this, ast as Z3_func_decl);
        default:
          return this._toExpr(ast);
      }
    }

    _toSort(ast: Z3_sort): AnySort {
      switch (Z3.get_sort_kind(this.ptr, ast)) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new BoolSortImpl(this, ast);
        case Z3_sort_kind.Z3_INT_SORT:
        case Z3_sort_kind.Z3_REAL_SORT:
          return new ArithSortImpl(this, ast);
        case Z3_sort_kind.Z3_BV_SORT:
          return new BitVecSortImpl(this, ast);
        default:
          return new SortImpl(this, ast);
      }
    }

    _toExpr(ast: Z3_ast): Bool | IntNum | RatNum | Arith | Expr {
      const kind = Z3.get_ast_kind(this.ptr, ast);
      if (kind === Z3_ast_kind.Z3_QUANTIFIER_AST) {
        assert(false);
      }
      const sortKind = Z3.get_sort_kind(this.ptr, Z3.get_sort(this.ptr, ast));
      switch (sortKind) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new BoolImpl(this, ast);
        case Z3_sort_kind.Z3_INT_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new IntNumImpl(this, ast);
          }
          return new ArithImpl(this, ast);
        case Z3_sort_kind.Z3_REAL_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new RatNumImpl(this, ast);
          }
          return new ArithImpl(this, ast);
        case Z3_sort_kind.Z3_BV_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new BitVecNumImpl(this, ast);
          }
          return new BitVecImpl(this, ast);
        default:
          return new ExprImpl(this, ast);
      }
    }

    _flattenArgs<T extends AnyAst = AnyAst>(args: (T | AstVector<T>)[]): T[] {
      const result: T[] = [];
      for (const arg of args) {
        if (this.isAstVector(arg)) {
          result.push(...arg.values());
        } else {
          result.push(arg);
        }
      }
      return result;
    }

    _toProbe(p: Probe | Z3_probe): Probe {
      if (this.isProbe(p)) {
        return p;
      }
      return new ProbeImpl(this, p);
    }

    _probeNary(
      f: (ctx: Z3_context, left: Z3_probe, right: Z3_probe) => Z3_probe,
      args: [Probe | Z3_probe, ...(Probe | Z3_probe)[]],
    ) {
      assert(args.length > 0, 'At least one argument expected');
      let r = this._toProbe(args[0]);
      for (let i = 1; i < args.length; i++) {
        r = new ProbeImpl(this, f(this.ptr, r.ptr, this._toProbe(args[i]).ptr));
      }
      return r;
    }
  }

  class AstImpl<Ptr> implements Ast {
    declare readonly __typename: Ast['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Ptr) {
      const myAst = this.ast;

      Z3.inc_ref(ctx.ptr, myAst);
      cleanup.register(this, () => Z3.dec_ref(ctx.ptr, myAst));
    }

    get ast(): Z3_ast {
      return this.ptr as any as Z3_ast;
    }

    get id() {
      return Z3.get_ast_id(this.ctx.ptr, this.ast);
    }

    eqIdentity(other: Ast) {
      this.ctx._assertContext(other);
      return Z3.is_eq_ast(this.ctx.ptr, this.ast, other.ast);
    }

    neqIdentity(other: Ast) {
      this.ctx._assertContext(other);
      return !this.eqIdentity(other);
    }

    sexpr() {
      return Z3.ast_to_string(this.ctx.ptr, this.ast);
    }

    hash() {
      return Z3.get_ast_hash(this.ctx.ptr, this.ast);
    }
  }

  class SolverImpl implements Solver {
    declare readonly __typename: Solver['__typename'];

    readonly ptr: Z3_solver;

    constructor(readonly ctx: ContextImpl, ptr: Z3_solver | string = Z3.mk_solver(ctx.ptr)) {
      let myPtr: Z3_solver;
      if (typeof ptr === 'string') {
        myPtr = Z3.mk_solver_for_logic(ctx.ptr, ctx._toSymbol(ptr));
      } else {
        myPtr = ptr;
      }
      this.ptr = myPtr;
      Z3.solver_inc_ref(ctx.ptr, myPtr);
      cleanup.register(this, () => Z3.solver_dec_ref(ctx.ptr, myPtr));
    }

    push() {
      Z3.solver_push(this.ctx.ptr, this.ptr);
    }
    pop(num: number = 1) {
      Z3.solver_pop(this.ctx.ptr, this.ptr, num);
    }
    numScopes() {
      return Z3.solver_get_num_scopes(this.ctx.ptr, this.ptr);
    }
    reset() {
      Z3.solver_reset(this.ctx.ptr, this.ptr);
    }
    add(...exprs: (Bool | AstVector<Bool>)[]) {
      this.ctx._flattenArgs(exprs).forEach(expr => {
        this.ctx._assertContext(expr);
        Z3.solver_assert(this.ctx.ptr, this.ptr, expr.ast);
      });
    }
    addAndTrack(expr: Bool, constant: Bool | string) {
      if (typeof constant === 'string') {
        constant = this.ctx.Bool.const(constant);
      }
      assert(this.ctx.isConst(constant), 'Provided expression that is not a constant to addAndTrack');
      Z3.solver_assert_and_track(this.ctx.ptr, this.ptr, expr.ast, constant.ast);
    }

    assertions(): AstVector<Bool> {
      return new AstVectorImpl(this.ctx, Z3.solver_get_assertions(this.ctx.ptr, this.ptr));
    }

    async check(...exprs: (Bool | AstVector<Bool>)[]): Promise<CheckSatResult> {
      const assumptions = this.ctx._flattenArgs(exprs).map(expr => {
        this.ctx._assertContext(expr);
        return expr.ast;
      });
      const result = await asyncMutex.runExclusive(() =>
        Z3.solver_check_assumptions(this.ctx.ptr, this.ptr, assumptions),
      );
      switch (result) {
        case Z3_lbool.Z3_L_FALSE:
          return unsat;
        case Z3_lbool.Z3_L_TRUE:
          return sat;
        case Z3_lbool.Z3_L_UNDEF:
          return unknown;
        default:
          assertExhaustive(result);
      }
    }

    model() {
      return new this.ctx.Model(Z3.solver_get_model(this.ctx.ptr, this.ptr));
    }
  }

  class ModelImpl implements Model {
    declare readonly __typename: Model['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_model = Z3.mk_model(ctx.ptr)) {
      Z3.model_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.model_dec_ref(ctx.ptr, ptr));
    }

    get length() {
      return Z3.model_get_num_consts(this.ctx.ptr, this.ptr) + Z3.model_get_num_funcs(this.ctx.ptr, this.ptr);
    }

    [Symbol.iterator](): Iterator<FuncDecl> {
      return this.values();
    }

    *entries(): IterableIterator<[number, FuncDecl]> {
      const length = this.length;
      for (let i = 0; i < length; i++) {
        yield [i, this.get(i)];
      }
    }

    *keys(): IterableIterator<number> {
      for (const [key] of this.entries()) {
        yield key;
      }
    }

    *values(): IterableIterator<FuncDecl> {
      for (const [, value] of this.entries()) {
        yield value;
      }
    }

    decls() {
      return [...this.values()];
    }

    sexpr() {
      return Z3.model_to_string(this.ctx.ptr, this.ptr);
    }

    eval(expr: Bool, modelCompletion?: boolean): Bool;
    eval(expr: Arith, modelCompletion?: boolean): Arith;
    eval(expr: Expr, modelCompletion: boolean = false) {
      this.ctx._assertContext(expr);
      const r = Z3.model_eval(this.ctx.ptr, this.ptr, expr.ast, modelCompletion);
      if (r === null) {
        throw new Z3Error('Failed to evaluatio expression in the model');
      }
      return this.ctx._toExpr(r);
    }

    get(i: number): FuncDecl;
    get(from: number, to: number): FuncDecl[];
    get(declaration: FuncDecl): FuncInterp | Expr;
    get(constant: Expr): Expr;
    get(sort: Sort): AstVector<AnyExpr>;
    get(
      i: number | FuncDecl | Expr | Sort,
      to?: number,
    ): FuncDecl | FuncInterp | Expr | AstVector<AnyAst> | FuncDecl[] {
      assert(to === undefined || typeof i === 'number');
      if (typeof i === 'number') {
        const length = this.length;

        if (i >= length) {
          throw new RangeError();
        }

        if (to === undefined) {
          const numConsts = Z3.model_get_num_consts(this.ctx.ptr, this.ptr);
          if (i < numConsts) {
            return new FuncDeclImpl(this.ctx, Z3.model_get_const_decl(this.ctx.ptr, this.ptr, i));
          } else {
            return new FuncDeclImpl(this.ctx, Z3.model_get_func_decl(this.ctx.ptr, this.ptr, i - numConsts));
          }
        }

        if (to < 0) {
          to += length;
        }
        if (to >= length) {
          throw new RangeError();
        }
        const result = [];
        for (let j = i; j < to; j++) {
          result.push(this.get(j));
        }
        return result;
      } else if (this.ctx.isFuncDecl(i) || (this.ctx.isExpr(i) && this.ctx.isConst(i))) {
        const result = this.getInterp(i);
        assert(result !== null);
        return result;
      } else if (this.ctx.isSort(i)) {
        return this.getUniverse(i);
      }
      assert(false, 'Number, declaration or constant expected');
    }

    private getInterp(expr: FuncDecl | Expr): Expr | FuncInterp | null {
      assert(this.ctx.isFuncDecl(expr) || this.ctx.isConst(expr), 'Declaration expected');
      if (this.ctx.isConst(expr)) {
        assert(this.ctx.isExpr(expr));
        expr = expr.decl();
      }
      assert(this.ctx.isFuncDecl(expr));
      if (expr.arity() === 0) {
        const result = Z3.model_get_const_interp(this.ctx.ptr, this.ptr, expr.ptr);
        if (result === null) {
          return null;
        }
        return this.ctx._toExpr(result);
      } else {
        const interp = Z3.model_get_func_interp(this.ctx.ptr, this.ptr, expr.ptr);
        if (interp === null) {
          return null;
        }
        return new FuncInterpImpl(this.ctx, interp);
      }
    }

    private getUniverse(sort: Sort): AstVector<AnyAst> {
      this.ctx._assertContext(sort);
      return new AstVectorImpl(this.ctx, Z3.model_get_sort_universe(this.ctx.ptr, this.ptr, sort.ptr));
    }
  }

  class FuncInterpImpl implements FuncInterp {
    declare readonly __typename: FuncInterp['__typename'];

    constructor(readonly ctx: Context, readonly ptr: Z3_func_interp) {
      Z3.func_interp_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.func_interp_dec_ref(ctx.ptr, ptr));
    }
  }

  class SortImpl extends AstImpl<Z3_sort> implements Sort {
    declare readonly __typename: Sort['__typename'];

    get ast(): Z3_ast {
      return Z3.sort_to_ast(this.ctx.ptr, this.ptr);
    }

    kind() {
      return Z3.get_sort_kind(this.ctx.ptr, this.ptr);
    }

    subsort(other: Sort) {
      this.ctx._assertContext(other);
      return false;
    }

    cast(expr: Expr): Expr {
      this.ctx._assertContext(expr);
      assert(expr.sort.eqIdentity(expr.sort), 'Sort mismatch');
      return expr;
    }

    name() {
      return this.ctx._fromSymbol(Z3.get_sort_name(this.ctx.ptr, this.ptr));
    }

    eqIdentity(other: Sort) {
      this.ctx._assertContext(other);
      return Z3.is_eq_sort(this.ctx.ptr, this.ptr, other.ptr);
    }

    neqIdentity(other: Sort) {
      return !this.eqIdentity(other);
    }
  }

  class FuncDeclImpl extends AstImpl<Z3_func_decl> implements FuncDecl {
    declare readonly __typename: FuncDecl['__typename'];

    get ast() {
      return Z3.func_decl_to_ast(this.ctx.ptr, this.ptr);
    }

    name() {
      return this.ctx._fromSymbol(Z3.get_decl_name(this.ctx.ptr, this.ptr));
    }

    arity() {
      return Z3.get_arity(this.ctx.ptr, this.ptr);
    }

    domain(i: number) {
      assert(i < this.arity(), 'Index out of bounds');
      return this.ctx._toSort(Z3.get_domain(this.ctx.ptr, this.ptr, i));
    }

    range() {
      return this.ctx._toSort(Z3.get_range(this.ctx.ptr, this.ptr));
    }

    kind() {
      return Z3.get_decl_kind(this.ctx.ptr, this.ptr);
    }

    params(): (number | string | Z3_symbol | Sort | Expr | FuncDecl)[] {
      const n = Z3.get_decl_num_parameters(this.ctx.ptr, this.ptr);
      const result = [];
      for (let i = 0; i < n; i++) {
        const kind = Z3.get_decl_parameter_kind(this.ctx.ptr, this.ptr, i);
        switch (kind) {
          case Z3_parameter_kind.Z3_PARAMETER_INT:
            result.push(Z3.get_decl_int_parameter(this.ctx.ptr, this.ptr, i));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_DOUBLE:
            result.push(Z3.get_decl_double_parameter(this.ctx.ptr, this.ptr, i));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_RATIONAL:
            result.push(Z3.get_decl_rational_parameter(this.ctx.ptr, this.ptr, i));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_SYMBOL:
            result.push(Z3.get_decl_symbol_parameter(this.ctx.ptr, this.ptr, i));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_SORT:
            result.push(new SortImpl(this.ctx, Z3.get_decl_sort_parameter(this.ctx.ptr, this.ptr, i)));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_AST:
            result.push(new ExprImpl(this.ctx, Z3.get_decl_ast_parameter(this.ctx.ptr, this.ptr, i)));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
            result.push(new FuncDeclImpl(this.ctx, Z3.get_decl_func_decl_parameter(this.ctx.ptr, this.ptr, i)));
            break;
          default:
            assertExhaustive(kind);
        }
      }
      return result;
    }

    call(...args: CoercibleToExpr[]) {
      assert(args.length === this.arity(), `Incorrect number of arguments to ${this}`);
      return this.ctx._toExpr(
        Z3.mk_app(
          this.ctx.ptr,
          this.ptr,
          args.map((arg, i) => {
            return this.domain(i).cast(arg).ast;
          }),
        ),
      );
    }
  }

  class ExprImpl<Ptr, S extends Sort = AnySort> extends AstImpl<Ptr> implements Expr {
    declare readonly __typename: Expr['__typename'];

    get sort(): S {
      return this.ctx._toSort(Z3.get_sort(this.ctx.ptr, this.ast)) as S;
    }

    eq(other: CoercibleToExpr): Bool {
      return new BoolImpl(this.ctx, Z3.mk_eq(this.ctx.ptr, this.ast, this.ctx.from(other).ast));
    }

    neq(other: CoercibleToExpr): Bool {
      return new BoolImpl(
        this.ctx,
        Z3.mk_distinct(
          this.ctx.ptr,
          [this, other].map(expr => this.ctx.from(expr).ast),
        ),
      );
    }

    params() {
      return this.decl().params();
    }

    decl(): FuncDecl {
      assert(this.ctx.isApp(this), 'Z3 application expected');
      return new FuncDeclImpl(this.ctx, Z3.get_app_decl(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast)));
    }

    numArgs(): number {
      assert(this.ctx.isApp(this), 'Z3 applicaiton expected');
      return Z3.get_app_num_args(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast));
    }

    arg(i: number): ReturnType<typeof this.ctx._toExpr> {
      assert(this.ctx.isApp(this), 'Z3 applicaiton expected');
      assert(i < this.numArgs(), 'Invalid argument index');
      return this.ctx._toExpr(Z3.get_app_arg(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast), i));
    }

    children(): ReturnType<typeof this.ctx._toExpr>[] {
      const num_args = this.numArgs();
      if (this.ctx.isApp(this)) {
        const result = [];
        for (let i = 0; i < num_args; i++) {
          result.push(this.arg(i));
        }
        return result;
      }
      return [];
    }
  }

  class BoolSortImpl extends SortImpl implements BoolSort {
    declare readonly __typename: BoolSort['__typename'];

    cast(other: Bool | boolean): Bool;
    cast(other: CoercibleToExpr): never;
    cast(other: CoercibleToExpr | Bool) {
      if (typeof other === 'boolean') {
        other = this.ctx.Bool.val(other);
      }
      assert(this.ctx.isExpr(other), 'true, false or Z3 Boolean expression expected.');
      assert(this.eqIdentity(other.sort), 'Value cannot be converted into a Z3 Boolean value');
      return other;
    }

    subsort(other: Sort) {
      this.ctx._assertContext(other.ctx);
      return other instanceof ArithSortImpl;
    }
  }

  class BoolImpl extends ExprImpl<Z3_ast, BoolSort> implements Bool {
    declare readonly __typename: Bool['__typename'];

    not(): Bool {
      return this.ctx.Not(this);
    }
    and(other: Bool | boolean): Bool {
      return this.ctx.And(this, other);
    }
    or(other: Bool | boolean): Bool {
      return this.ctx.Or(this, other);
    }
    xor(other: Bool | boolean): Bool {
      return this.ctx.Xor(this, other);
    }
  }

  class ProbeImpl implements Probe {
    declare readonly __typename: Probe['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_probe) {}
  }

  class TacticImpl implements Tactic {
    declare readonly __typename: Tactic['__typename'];

    readonly ptr: Z3_tactic;

    constructor(readonly ctx: ContextImpl, tactic: string | Z3_tactic) {
      let myPtr: Z3_tactic;
      if (typeof tactic === 'string') {
        myPtr = Z3.mk_tactic(ctx.ptr, tactic);
      } else {
        myPtr = tactic;
      }

      this.ptr = myPtr;

      Z3.tactic_inc_ref(ctx.ptr, myPtr);
      cleanup.register(this, () => Z3.tactic_dec_ref(ctx.ptr, myPtr));
    }
  }

  class ArithSortImpl extends SortImpl implements ArithSort {
    declare readonly __typename: ArithSort['__typename'];

    cast(other: bigint | number): IntNum | RatNum;
    cast(other: CoercibleRational | RatNum): RatNum;
    cast(other: IntNum): IntNum;
    cast(other: Bool | Arith): Arith;
    cast(other: CoercibleToExpr): never;
    cast(other: CoercibleToExpr): Arith | RatNum | IntNum {
      const { If, isExpr, isArith, isBool, isIntSort, isRealSort, ToReal, Int, Real } = this.ctx;
      const sortTypeStr = isIntSort(this) ? 'IntSort' : 'RealSort';
      if (isExpr(other)) {
        const otherS = other.sort;
        if (isArith(other)) {
          if (this.eqIdentity(otherS)) {
            return other;
          } else if (isIntSort(otherS) && isRealSort(this)) {
            return this.ctx.ToReal(other);
          }
          assert(false, "Can't cast Real to IntSort without loss");
        } else if (isBool(other)) {
          if (isIntSort(this)) {
            return If(other, 1, 0);
          } else {
            return ToReal(If(other, 1, 0));
          }
        }
        assert(false, `Can't cast expression to ${sortTypeStr}`);
      } else {
        if (typeof other !== 'boolean') {
          if (isIntSort(this)) {
            assert(!isCoercibleRational(other), "Can't cast fraction to IntSort");
            return Int.val(other);
          }
          return Real.val(other);
        }
        assert(false, `Can't cast primitive to ${sortTypeStr}`);
      }
    }
  }

  class ArithImpl extends ExprImpl<Z3_ast, ArithSort> implements Arith {
    declare readonly __typename: Arith['__typename'];

    add(other: Arith | number | bigint | string | CoercibleRational) {
      return new ArithImpl(this.ctx, Z3.mk_add(this.ctx.ptr, [this.ast, this.sort.cast(other).ast]));
    }

    mul(other: Arith | number | bigint | string | CoercibleRational) {
      return new ArithImpl(this.ctx, Z3.mk_mul(this.ctx.ptr, [this.ast, this.sort.cast(other).ast]));
    }

    sub(other: Arith | number | bigint | string | CoercibleRational) {
      return new ArithImpl(this.ctx, Z3.mk_sub(this.ctx.ptr, [this.ast, this.sort.cast(other).ast]));
    }

    pow(exponent: Arith | number | bigint | string | CoercibleRational) {
      return new ArithImpl(this.ctx, Z3.mk_power(this.ctx.ptr, this.ast, this.sort.cast(exponent).ast));
    }

    div(other: Arith | number | bigint | string | CoercibleRational) {
      return new ArithImpl(this.ctx, Z3.mk_div(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }

    mod(other: Arith | number | bigint | string | CoercibleRational) {
      return new ArithImpl(this.ctx, Z3.mk_mod(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }

    neg() {
      return new ArithImpl(this.ctx, Z3.mk_unary_minus(this.ctx.ptr, this.ast));
    }

    le(other: Arith | number | bigint | string | CoercibleRational) {
      return new BoolImpl(this.ctx, Z3.mk_le(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }

    lt(other: Arith | number | bigint | string | CoercibleRational) {
      return new BoolImpl(this.ctx, Z3.mk_lt(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }

    gt(other: Arith | number | bigint | string | CoercibleRational) {
      return new BoolImpl(this.ctx, Z3.mk_gt(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }

    ge(other: Arith | number | bigint | string | CoercibleRational) {
      return new BoolImpl(this.ctx, Z3.mk_ge(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
  }

  class IntNumImpl extends ArithImpl implements IntNum {
    declare readonly __typename: IntNum['__typename'];

    get value() {
      return BigInt(this.asString());
    }

    asString() {
      return Z3.get_numeral_string(this.ctx.ptr, this.ast);
    }

    asBinary() {
      return Z3.get_numeral_binary_string(this.ctx.ptr, this.ast);
    }
  }

  class RatNumImpl extends ArithImpl implements RatNum {
    declare readonly __typename: RatNum['__typename'];

    get value() {
      return { numerator: this.numerator().value, denominator: this.denominator().value };
    }

    numerator() {
      return new IntNumImpl(this.ctx, Z3.get_numerator(this.ctx.ptr, this.ast));
    }

    denominator() {
      return new IntNumImpl(this.ctx, Z3.get_denominator(this.ctx.ptr, this.ast));
    }

    asNumber() {
      const { numerator, denominator } = this.value;
      const div = numerator / denominator;
      return Number(div) + Number(numerator - div * denominator) / Number(denominator);
    }

    asDecimal(prec: number = Number.parseInt(getParam('precision') ?? FALLBACK_PRECISION.toString())) {
      return Z3.get_numeral_decimal_string(this.ctx.ptr, this.ast, prec);
    }

    asString() {
      return Z3.get_numeral_string(this.ctx.ptr, this.ast);
    }
  }

  class BitVecSortImpl extends SortImpl implements BitVecSort {
    declare readonly __typename: BitVecSort['__typename'];

    get size() {
      return Z3.get_bv_sort_size(this.ctx.ptr, this.ptr);
    }

    subsort(other: Sort<any>): boolean {
      return this.ctx.isBitVecSort(other) && this.size < other.size;
    }

    cast(other: CoercibleToBitVec): BitVec;
    cast(other: CoercibleToExpr): Expr;
    cast(other: CoercibleToExpr): Expr {
      if (this.ctx.isExpr(other)) {
        this.ctx._assertContext(other);
        return other;
      }
      assert(!isCoercibleRational(other), "Can't convert rational to BitVec");
      return this.ctx.BitVec.val(other, this.size);
    }
  }

  class BitVecImpl extends ExprImpl<Z3_ast, BitVecSortImpl> implements BitVec {
    declare readonly __typename: BitVec['__typename'];

    get size() {
      return this.sort.size;
    }

    add(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvadd(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    mul(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvmul(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    sub(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvsub(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    sdiv(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvsdiv(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    udiv(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvudiv(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    smod(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvsmod(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    urem(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvurem(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    srem(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvsrem(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    neg(): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvneg(this.ctx.ptr, this.ast));
    }

    or(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvor(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    and(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvand(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    nand(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvnand(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    xor(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvxor(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    xnor(other: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvxnor(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    shr(count: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvashr(this.ctx.ptr, this.ast, this.sort.cast(count).ast));
    }
    lshr(count: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvlshr(this.ctx.ptr, this.ast, this.sort.cast(count).ast));
    }
    shl(count: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvshl(this.ctx.ptr, this.ast, this.sort.cast(count).ast));
    }
    rotateRight(count: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_ext_rotate_right(this.ctx.ptr, this.ast, this.sort.cast(count).ast));
    }
    rotateLeft(count: CoercibleToBitVec): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_ext_rotate_left(this.ctx.ptr, this.ast, this.sort.cast(count).ast));
    }
    not(): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvnot(this.ctx.ptr, this.ast));
    }

    extract(high: number, low: number): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_extract(this.ctx.ptr, high, low, this.ast));
    }
    signExt(count: number): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_sign_ext(this.ctx.ptr, count, this.ast));
    }
    zeroExt(count: number): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_zero_ext(this.ctx.ptr, count, this.ast));
    }
    repeat(count: number): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_repeat(this.ctx.ptr, count, this.ast));
    }

    sle(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvsle(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    ule(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvule(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    slt(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvslt(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    ult(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvult(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    sge(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvsge(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    uge(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvuge(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    sgt(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvsgt(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    ugt(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvugt(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }

    redAnd(): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvredand(this.ctx.ptr, this.ast));
    }
    redOr(): BitVec {
      return new BitVecImpl(this.ctx, Z3.mk_bvredor(this.ctx.ptr, this.ast));
    }

    addNoOverflow(other: CoercibleToBitVec, isSigned: boolean): Bool {
      return new BoolImpl(
        this.ctx,
        Z3.mk_bvadd_no_overflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast, isSigned),
      );
    }
    addNoUnderflow(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvadd_no_underflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    subNoOverflow(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvsub_no_overflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    subNoUndeflow(other: CoercibleToBitVec, isSigned: boolean): Bool {
      return new BoolImpl(
        this.ctx,
        Z3.mk_bvsub_no_underflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast, isSigned),
      );
    }
    sdivNoOverflow(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvsdiv_no_overflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    mulNoOverflow(other: CoercibleToBitVec, isSigned: boolean): Bool {
      return new BoolImpl(
        this.ctx,
        Z3.mk_bvmul_no_overflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast, isSigned),
      );
    }
    mulNoUndeflow(other: CoercibleToBitVec): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvmul_no_underflow(this.ctx.ptr, this.ast, this.sort.cast(other).ast));
    }
    negNoOverflow(): Bool {
      return new BoolImpl(this.ctx, Z3.mk_bvneg_no_overflow(this.ctx.ptr, this.ast));
    }
  }

  class BitVecNumImpl extends BitVecImpl implements BitVecNum {
    declare readonly __typename: BitVecNum['__typename'];
    get value() {
      return BigInt(this.asString());
    }

    asSignedValue() {
      let val = this.value;
      const size = BigInt(this.size);
      if (val >= 2n ** (size - 1n)) {
        val = val - 2n ** size;
      }
      if (val < (-2n) ** (size - 1n)) {
        val = val + 2n ** size;
      }
      return val;
    }
    asString() {
      return Z3.get_numeral_string(this.ctx.ptr, this.ast);
    }
    asBinaryString() {
      return Z3.get_numeral_binary_string(this.ctx.ptr, this.ast);
    }
  }

  class AstVectorImpl<Item extends AnyAst = AnyAst> {
    declare readonly __typename: AstVector['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_ast_vector = Z3.mk_ast_vector(ctx.ptr)) {
      Z3.ast_vector_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.ast_vector_dec_ref(ctx.ptr, ptr));
    }

    get length(): number {
      return Z3.ast_vector_size(this.ctx.ptr, this.ptr);
    }

    [Symbol.iterator](): IterableIterator<Item> {
      return this.values();
    }

    *entries(): IterableIterator<[number, Item]> {
      const length = this.length;
      for (let i = 0; i < length; i++) {
        yield [i, this.get(i)];
      }
    }

    *keys(): IterableIterator<number> {
      for (let [key] of this.entries()) {
        yield key;
      }
    }

    *values(): IterableIterator<Item> {
      for (let [, value] of this.entries()) {
        yield value;
      }
    }

    get(i: number): Item;
    get(from: number, to: number): Item[];
    get(from: number, to?: number): Item | Item[] {
      const length = this.length;
      if (from < 0) {
        from += length;
      }
      if (from >= length) {
        throw new RangeError();
      }

      if (to === undefined) {
        return this.ctx._toAst(Z3.ast_vector_get(this.ctx.ptr, this.ptr, from)) as Item;
      }

      if (to < 0) {
        to += length;
      }
      if (to >= length) {
        throw new RangeError();
      }

      const result: Item[] = [];
      for (let i = from; i < to; i++) {
        result.push(this.ctx._toAst(Z3.ast_vector_get(this.ctx.ptr, this.ptr, i)) as Item);
      }
      return result;
    }

    set(i: number, v: Item): void {
      this.ctx._assertContext(v);
      if (i >= this.length) {
        throw new RangeError();
      }
      Z3.ast_vector_set(this.ctx.ptr, this.ptr, i, v.ast);
    }

    push(v: Item): void {
      this.ctx._assertContext(v);
      Z3.ast_vector_push(this.ctx.ptr, this.ptr, v.ast);
    }

    resize(size: number): void {
      Z3.ast_vector_resize(this.ctx.ptr, this.ptr, size);
    }

    has(v: Item): boolean {
      this.ctx._assertContext(v);
      for (const item of this.values()) {
        if (item.eqIdentity(v)) {
          return true;
        }
      }
      return false;
    }

    sexpr(): string {
      return Z3.ast_vector_to_string(this.ctx.ptr, this.ptr);
    }
  }

  class AstMapImpl<Key extends AnyAst = AnyAst, Value extends AnyAst = AnyAst> implements AstMap<Key, Value> {
    declare readonly __typename: AstMap['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_ast_map = Z3.mk_ast_map(ctx.ptr)) {
      Z3.ast_map_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.ast_map_dec_ref(ctx.ptr, ptr));
    }

    [Symbol.iterator](): Iterator<[Key, Value]> {
      return this.entries();
    }

    get size(): number {
      return Z3.ast_map_size(this.ctx.ptr, this.ptr);
    }

    *entries(): IterableIterator<[Key, Value]> {
      for (const key of this.keys()) {
        yield [key, this.get(key)];
      }
    }

    keys(): AstVector<Key> {
      return new AstVectorImpl(this.ctx, Z3.ast_map_keys(this.ctx.ptr, this.ptr));
    }

    *values(): IterableIterator<Value> {
      for (const [_, value] of this.entries()) {
        yield value;
      }
    }
    get(key: Key): Value {
      return this.ctx._toAst(Z3.ast_map_find(this.ctx.ptr, this.ptr, key.ast)) as Value;
    }

    set(key: Key, value: Value): void {
      Z3.ast_map_insert(this.ctx.ptr, this.ptr, key.ast, value.ast);
    }

    delete(key: Key): void {
      Z3.ast_map_erase(this.ctx.ptr, this.ptr, key.ast);
    }

    clear(): void {
      Z3.ast_map_reset(this.ctx.ptr, this.ptr);
    }

    has(key: Key): boolean {
      return Z3.ast_map_contains(this.ctx.ptr, this.ptr, key.ast);
    }

    sexpr(): string {
      return Z3.ast_map_to_string(this.ctx.ptr, this.ptr);
    }
  }

  return {
    enableTrace,
    disableTrace,
    getVersion,
    getVersionString,
    getFullVersion,
    openLog,
    appendLog,
    getParam,
    setParam,
    resetParams,
    isContext,

    Context: ContextImpl as ContextCtor,
  };
}
