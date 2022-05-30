// TODO(ritave): Research whether we can use type system to discern between classes
//               from other contexts.
//               We could use templated string literals Solver<'contextName'> but that would
//               be cumbersome for the end user
// TODO(ritave): Coerce primitives to expressions
// TODO(ritave): Add typing for Context Options
//               https://github.com/Z3Prover/z3/pull/6048#discussion_r883391669
// TODO(ritave): Add an error handler
// TODO(ritave): Add support for building faster floats without support for Safari
// TODO(ritave): Update PUBLISHED_README.md
// TODO(ritave): Use Z3_DECLARE_CLOSURE macro to generate code https://github.com/Z3Prover/z3/pull/6048#discussion_r884155462
// TODO(ritave): Add pretty printing
// TODO(ritave): Make Z3 multi-threaded
// TODO(ritave): Use a mutex (see async-mutex package) to guard async calls instead of throwing
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
  Z3_pattern,
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
  ArithRef,
  ArithSortRef,
  AstMap,
  AstRef,
  AstVector,
  BoolRef,
  BoolSortRef,
  CheckSatResult,
  CoercibleRational,
  CoercibleToExpr,
  CoercibleToExprMap,
  Context,
  ContextCtor,
  ExprRef,
  FuncDeclRef,
  FuncInterp,
  IntNumRef,
  Model,
  PatternRef,
  Probe,
  RatNumRef,
  sat,
  Solver,
  SortRef,
  SortToExprMap,
  Tactic,
  unknown,
  unsat,
  Z3Error,
  Z3HighLevel,
} from './types';
import { allSatisfy, assert, assertExhaustive, autoBind } from './utils';

const FALLBACK_PRECISION = 17;

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

  class ContextImpl {
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

      this.AstRef = AstRefImpl.bind(AstRefImpl, this) as any;
      this.Solver = SolverImpl.bind(SolverImpl, this);
      this.Model = ModelImpl.bind(ModelImpl, this);
      this.FuncInterp = FuncInterpImpl.bind(FuncInterpImpl, this);
      this.SortRef = SortRefImpl.bind(SortRefImpl, this);
      this.FuncDeclRef = FuncDeclRefImpl.bind(FuncDeclRefImpl, this);
      this.ExprRef = ExprRefImpl.bind(ExprRefImpl, this) as any;
      this.BoolSortRef = BoolSortRefImpl.bind(BoolSortRefImpl, this);
      this.BoolRef = BoolRefImpl.bind(BoolSortRefImpl, this);
      this.PatternRef = PatternRefImpl.bind(PatternRefImpl, this);
      this.Probe = ProbeImpl.bind(ProbeImpl, this);
      this.Tactic = TacticImpl.bind(TacticImpl, this);
      this.ArithSortRef = ArithSortRefImpl.bind(ArithSortRefImpl, this);
      this.ArithRef = ArithRefImpl.bind(ArithRefImpl, this);
      this.IntNumRef = IntNumRefImpl.bind(IntNumRefImpl, this);
      this.RatNumRef = RatNumRefImpl.bind(RatNumRefImpl, this);
      this.AstVector = AstVectorImpl.bind(AstVectorImpl, this) as any;
      this.AstMap = AstMapImpl.bind(AstMapImpl, this) as any;

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

    isAst(obj: unknown): obj is AstRef {
      const r = obj instanceof this.AstRef;
      r && this._assertContext(obj);
      return r;
    }

    isSort(obj: unknown): obj is SortRef {
      const r = obj instanceof this.SortRef;
      r && this._assertContext(obj);
      return r;
    }

    isFuncDecl(obj: unknown): obj is FuncDeclRef {
      const r = obj instanceof this.FuncDeclRef;
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

    isExpr(obj: unknown): obj is ExprRef {
      const r = obj instanceof this.ExprRef;
      r && this._assertContext(obj);
      return r;
    }

    isVar(obj: unknown): boolean {
      return this.isExpr(obj) && Z3.get_ast_kind(this.ptr, obj.ast) === Z3_ast_kind.Z3_VAR_AST;
    }

    isAppOf(obj: unknown, kind: Z3_decl_kind): boolean {
      return this.isExpr(obj) && this.isApp(obj) && obj.decl().kind() === kind;
    }

    isBool(obj: unknown): obj is BoolRef {
      const r = obj instanceof this.BoolRef;
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

    isArith(obj: unknown): obj is ArithRef {
      const r = obj instanceof this.ArithRef;
      r && this._assertContext(obj);
      return r;
    }

    isArithSort(obj: unknown): obj is ArithSortRef {
      const r = obj instanceof this.ArithSortRef;
      r && this._assertContext(obj);
      return r;
    }

    isInt(obj: unknown): boolean {
      return this.isArith(obj) && this.isIntSort(obj.sort());
    }

    isIntVal(obj: unknown): obj is IntNumRef {
      const r = obj instanceof IntNumRefImpl;
      r && this._assertContext(obj);
      return r;
    }

    isIntSort(obj: unknown): boolean {
      return this.isSort(obj) && obj.kind() === Z3_sort_kind.Z3_INT_SORT;
    }

    isReal(obj: unknown): boolean {
      return this.isArith(obj) && this.isRealSort(obj.sort());
    }

    isRealVal(obj: unknown): obj is RatNumRef {
      const r = obj instanceof RatNumRefImpl;
      r && this._assertContext(obj);
      return r;
    }

    isRealSort(obj: unknown): boolean {
      return this.isSort(obj) && obj.kind() === Z3_sort_kind.Z3_REAL_SORT;
    }

    isProbe(obj: unknown): obj is Probe {
      const r = obj instanceof this.Probe;
      r && this._assertContext(obj);
      return r;
    }

    isTactic(obj: unknown): obj is Tactic {
      const r = obj instanceof this.Tactic;
      r && this._assertContext(obj);
      return r;
    }

    isPattern(obj: unknown): obj is PatternRef {
      const r = obj instanceof this.PatternRef;
      r && this._assertContext(obj);
      return r;
    }

    isAstVector(obj: unknown): obj is AstVector {
      const r = obj instanceof this.AstVector;
      r && this._assertContext(obj);
      return r;
    }

    /*
      function isQuantifier(obj: unknown): obj is QuantifierRef {
        return obj instanceof QuantifierRefImpl;
      }

      function isForAll(obj: unknown): obj is QuantifierRef<BoolSortRef> {
        return isQuantifier(obj) && Z3.is_quantifier_forall(ctx.ptr, obj.ast);
      }

      function isExists(obj: unknown): obj is QuantifierRef<BoolSortRef> {
        return isQuantifier(obj) && Z3.is_quantifier_exists(ctx.ptr, obj.ast);
      }

      function isLambda(obj: unknown): obj is LambdaRef<AnySort> {
        return obj instanceof LambdaRefImpl;
      }
      */

    eqIdentity(a: AstRef, b: AstRef): boolean {
      return a.eqIdentity(b);
    }

    getVarIndex(obj: ExprRef): number {
      assert(this.isVar(obj), 'Z3 bound variable expected');
      return Z3.get_index_value(this.ptr, obj.ast);
    }

    from(primitive: boolean): BoolRef;
    from(primitive: number | CoercibleRational): RatNumRef;
    from(primitive: bigint): IntNumRef;
    from<T extends ExprRef>(expr: T): T;
    from(expr: CoercibleToExpr): AnyExpr;
    from(value: CoercibleToExpr): AnyExpr {
      if (typeof value === 'boolean') {
        return this.BoolVal(value);
      } else if (typeof value === 'number' || isCoercibleRational(value)) {
        return this.RealVal(value);
      } else if (typeof value === 'bigint') {
        return this.IntVal(value);
      } else if (this.isExpr(value)) {
        return value;
      }
      assert(false);
    }

    /////////////
    // Classes //
    /////////////
    readonly AstRef: new <Ptr>(ptr: Ptr) => AstRef<any, Ptr>;
    readonly Solver: new () => Solver;
    readonly Model: new (ptr?: Z3_model) => Model;
    readonly FuncInterp: new (ptr: Z3_func_interp) => FuncInterp;
    readonly SortRef: new (ptr: Z3_sort) => SortRef;
    readonly FuncDeclRef: new (ptr: Z3_func_decl) => FuncDeclRef;
    readonly ExprRef: new <Ptr>(ptr: Ptr) => ExprRef<any, AnySort, Ptr>;
    readonly BoolSortRef: new (ptr: Z3_sort) => BoolSortRef;
    readonly BoolRef: new (ptr: Z3_ast) => BoolRef;
    readonly PatternRef: new (ptr: Z3_pattern) => PatternRef;
    readonly Probe: new (ptr: Z3_probe) => Probe;
    readonly Tactic: new (name: string | Z3_tactic) => Tactic;
    readonly ArithSortRef: new (ptr: Z3_sort) => ArithSortRef;
    readonly ArithRef: new (ptr: Z3_ast) => ArithRef;
    readonly IntNumRef: new (ptr: Z3_ast) => IntNumRef;
    readonly RatNumRef: new (ptr: Z3_ast) => RatNumRef;
    readonly AstVector: new <Item extends AstRef<any, unknown> = AnyAst<any>>(ptr?: Z3_ast_vector) => AstVector<Item>;
    readonly AstMap: new <Key extends AstRef = AnyAst, Value extends AstRef = AnyAst>(ptr?: Z3_ast_map) => AstMap<
      Key,
      Value
    >;

    ////////////////
    // Operations //
    ////////////////
    DeclareSort(name: string | number): SortRef {
      return new this.SortRef(Z3.mk_uninterpreted_sort(this.ptr, this._toSymbol(name)));
    }

    Function(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      this._assertContext(rng);
      const dom = [];
      for (let i = 0; i < arity; i++) {
        this._assertContext(signature[i]);
        dom.push(signature[i].ptr);
      }
      return new this.FuncDeclRef(Z3.mk_func_decl(this.ptr, this._toSymbol(name), dom, rng.ptr));
    }

    FreshFunction(...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      this._assertContext(rng);
      const dom = [];
      for (let i = 0; i < arity; i++) {
        this._assertContext(signature[i]);
        dom.push(signature[i].ptr);
      }
      return new this.FuncDeclRef(Z3.mk_fresh_func_decl(this.ptr, 'f', dom, rng.ptr));
    }

    RecFunction(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      this._assertContext(rng);
      const dom = [];
      for (let i = 0; i < arity; i++) {
        this._assertContext(signature[i]);
        dom.push(signature[i].ptr);
      }
      return new this.FuncDeclRef(Z3.mk_rec_func_decl(this.ptr, this._toSymbol(name), dom, rng.ptr));
    }

    RecAddDefinition(f: FuncDeclRef, args: ExprRef[], body: ExprRef) {
      this._assertContext(f, ...args, body);
      Z3.add_rec_def(
        this.ptr,
        f.ptr,
        args.map(arg => arg.ast),
        body.ast,
      );
    }

    If(condition: Probe, onTrue: Tactic, onFalse: Tactic): Tactic;
    If<OnTrueRef extends CoercibleToExpr, OnFalseRef extends CoercibleToExpr>(
      condition: BoolRef,
      onTrue: OnTrueRef,
      onFalse: OnFalseRef,
    ): CoercibleToExprMap<OnTrueRef | OnFalseRef>;
    If(
      condition: BoolRef | Probe,
      onTrue: CoercibleToExpr | Tactic,
      onFalse: CoercibleToExpr | Tactic,
    ): ExprRef | Tactic {
      if (this.isProbe(condition) && this.isTactic(onTrue) && this.isTactic(onFalse)) {
        return this.Cond(condition, onTrue, onFalse);
      }
      assert(
        !this.isProbe(condition) && !this.isTactic(onTrue) && !this.isTactic(onFalse),
        'Mixed expressions and goals',
      );
      onTrue = this.from(onTrue);
      onFalse = this.from(onFalse);
      return this._toExpr(Z3.mk_ite(this.ptr, condition.ptr, onTrue.ast, onFalse.ast));
    }

    Distinct(...exprs: ExprRef[]): BoolRef {
      assert(exprs.length > 0, "Can't make Distinct ouf of nothing");

      return new this.BoolRef(
        Z3.mk_distinct(
          this.ptr,
          exprs.map(expr => {
            this._assertContext(expr);
            return expr.ast;
          }),
        ),
      );
    }

    Const<S extends SortRef>(name: string, sort: S): SortToExprMap<S> {
      this._assertContext(sort);
      return this._toExpr(Z3.mk_const(this.ptr, this._toSymbol(name), sort.ptr)) as SortToExprMap<S>;
    }

    Consts<S extends SortRef>(names: string | string[], sort: S): SortToExprMap<S>[] {
      this._assertContext(sort);
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => this.Const(name, sort));
    }

    FreshConst<S extends SortRef>(sort: S, prefix: string = 'c'): SortToExprMap<S> {
      this._assertContext(sort);
      return this._toExpr(Z3.mk_fresh_const(sort.ctx.ptr, prefix, sort.ptr)) as SortToExprMap<S>;
    }

    Var<S extends SortRef>(idx: number, sort: S): SortToExprMap<S> {
      this._assertContext(sort);
      return this._toExpr(Z3.mk_bound(sort.ctx.ptr, idx, sort.ptr)) as SortToExprMap<S>;
    }

    BoolSort(): BoolSortRef {
      return new this.BoolSortRef(Z3.mk_bool_sort(this.ptr));
    }

    BoolVal(value: boolean): BoolRef {
      if (value) {
        return new this.BoolRef(Z3.mk_true(this.ptr));
      }
      return new this.BoolRef(Z3.mk_false(this.ptr));
    }

    Bool(name: string): BoolRef {
      return new this.BoolRef(Z3.mk_const(this.ptr, this._toSymbol(name), this.BoolSort().ptr));
    }

    Bools(names: string | string[]): BoolRef[] {
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => this.Bool(name));
    }

    BoolVector(prefix: string, count: number): BoolRef[] {
      const result = [];
      for (let i = 0; i < count; i++) {
        result.push(this.Bool(`${prefix}__${i}`));
      }
      return result;
    }

    FreshBool(prefix = 'b'): BoolRef {
      return new this.BoolRef(Z3.mk_fresh_const(this.ptr, prefix, this.BoolSort().ptr));
    }

    Implies(a: BoolRef, b: BoolRef): BoolRef {
      this._assertContext(a, b);
      return new this.BoolRef(Z3.mk_implies(this.ptr, a.ptr, b.ptr));
    }

    Eq(a: ExprRef, b: ExprRef): BoolRef {
      this._assertContext(a, b);
      return a.eq(b);
    }

    Xor(a: BoolRef, b: BoolRef): BoolRef {
      this._assertContext(a, b);
      return new this.BoolRef(Z3.mk_xor(this.ptr, a.ptr, b.ptr));
    }

    Not(a: Probe): Probe;
    Not(a: BoolRef): BoolRef;
    Not(a: BoolRef | Probe): BoolRef | Probe {
      this._assertContext(a);
      if (this.isProbe(a)) {
        return new this.Probe(Z3.probe_not(this.ptr, a.ptr));
      }
      return new this.BoolRef(Z3.mk_not(this.ptr, a.ptr));
    }

    And(): BoolRef;
    And(vector: AstVector<BoolRef>): BoolRef;
    And(...args: BoolRef[]): BoolRef;
    And(...args: Probe[]): Probe;
    And(...args: (AstVector<BoolRef> | Probe | BoolRef)[]): BoolRef | Probe {
      if (args.length == 1 && args[0] instanceof this.AstVector) {
        args = [...args[0].values()];
        assert(allSatisfy(args, this.isBool.bind(this)) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, this.isProbe.bind(this)) ?? false;
      if (allProbes) {
        return this._probeNary(Z3.probe_and, args as [Probe, ...Probe[]]);
      } else {
        this._assertContext(...args);
        return new this.BoolRef(
          Z3.mk_and(
            this.ptr,
            args.map(arg => (arg as BoolRef).ptr),
          ),
        );
      }
    }

    Or(): BoolRef;
    Or(vector: AstVector<BoolRef>): BoolRef;
    Or(...args: BoolRef[]): BoolRef;
    Or(...args: Probe[]): Probe;
    Or(...args: (AstVector<BoolRef> | Probe | BoolRef)[]): BoolRef | Probe {
      if (args.length == 1 && args[0] instanceof this.AstVector) {
        args = [...args[0].values()];
        assert(allSatisfy(args, this.isBool.bind(this)) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, this.isProbe.bind(this)) ?? false;
      if (allProbes) {
        return this._probeNary(Z3.probe_or, args as [Probe, ...Probe[]]);
      } else {
        this._assertContext(...args);
        return new this.BoolRef(
          Z3.mk_or(
            this.ptr,
            args.map(arg => (arg as BoolRef).ptr),
          ),
        );
      }
    }

    IntSort(): ArithSortRef {
      return new this.ArithSortRef(Z3.mk_int_sort(this.ptr));
    }

    IntVal(value: number | bigint | string): IntNumRef {
      assert(typeof value === 'bigint' || typeof value === 'string' || Number.isSafeInteger(value));
      return new this.IntNumRef(Z3.mk_numeral(this.ptr, value.toString(), this.IntSort().ptr));
    }

    Int(name: string | number): ArithRef {
      return new this.ArithRef(Z3.mk_const(this.ptr, this._toSymbol(name), this.IntSort().ptr));
    }

    Ints(names: string | string[]): ArithRef[] {
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => this.Int(name));
    }

    IntVector(prefix: string, count: number): ArithRef[] {
      const result = [];
      for (let i = 0; i < count; i++) {
        result.push(this.Int(`${prefix}__${i}`));
      }
      return result;
    }

    FreshInt(prefix: string = 'x'): ArithRef {
      return new this.ArithRef(Z3.mk_fresh_const(this.ptr, prefix, this.IntSort().ptr));
    }

    RealSort(): ArithSortRef {
      return new this.ArithSortRef(Z3.mk_real_sort(this.ptr));
    }

    RealVal(value: number | bigint | string | CoercibleRational): RatNumRef {
      if (isCoercibleRational(value)) {
        value = `${value.numerator}/${value.denominator}`;
      }
      return new this.RatNumRef(Z3.mk_numeral(this.ptr, value.toString(), this.RealSort().ptr));
    }

    Real(name: string | number): ArithRef {
      return new this.ArithRef(Z3.mk_const(this.ptr, this._toSymbol(name), this.RealSort().ptr));
    }

    Reals(names: string | string[]): ArithRef[] {
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => this.Real(name));
    }

    RealVector(prefix: string, count: number): ArithRef[] {
      const result = [];
      for (let i = 0; i < count; i++) {
        result.push(this.Real(`${prefix}__${i}`));
      }
      return result;
    }

    FreshReal(prefix: string = 'b'): ArithRef {
      return new this.ArithRef(Z3.mk_fresh_const(this.ptr, prefix, this.RealSort().ptr));
    }

    ToReal(expr: ArithRef): ArithRef {
      this._assertContext(expr);
      assert(this.isInt(expr), 'Int expression expected');
      return new this.ArithRef(Z3.mk_int2real(this.ptr, expr.ast));
    }

    ToInt(expr: ArithRef): ArithRef {
      this._assertContext(expr);
      assert(this.isReal(expr), 'Real expression expected');
      return new this.ArithRef(Z3.mk_real2int(this.ptr, expr.ast));
    }

    IsInt(expr: ArithRef): BoolRef {
      this._assertContext(expr);
      assert(this.isReal(expr), 'Real expression expected');
      return new this.BoolRef(Z3.mk_is_int(this.ptr, expr.ast));
    }

    Sqrt(a: ArithRef | number | bigint | string): ArithRef {
      if (!this.isExpr(a)) {
        a = this.RealVal(a);
      }
      return a.pow('1/2');
    }

    Cbrt(a: ArithRef | number | bigint | string): ArithRef {
      if (!this.isExpr(a)) {
        a = this.RealVal(a);
      }
      return a.pow('1/3');
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
          return new this.FuncDeclRef(ast as Z3_func_decl);
        default:
          return this._toExpr(ast);
      }
    }

    _toSort(ast: Z3_sort): AnySort {
      switch (Z3.get_sort_kind(this.ptr, ast)) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new this.BoolSortRef(ast);
        case Z3_sort_kind.Z3_INT_SORT || Z3_sort_kind.Z3_REAL_SORT:
          return new this.ArithSortRef(ast);
        default:
          return new this.SortRef(ast);
      }
    }

    _toExpr(ast: Z3_ast): BoolRef | IntNumRef | RatNumRef | ArithRef | ExprRef {
      const kind = Z3.get_ast_kind(this.ptr, ast);
      if (kind === Z3_ast_kind.Z3_QUANTIFIER_AST) {
        assert(false);
      }
      const sortKind = Z3.get_sort_kind(this.ptr, Z3.get_sort(this.ptr, ast));
      switch (sortKind) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new this.BoolRef(ast);
        case Z3_sort_kind.Z3_INT_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new this.IntNumRef(ast);
          }
          return new this.ArithRef(ast);
        case Z3_sort_kind.Z3_REAL_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new this.RatNumRef(ast);
          }
          return new this.ArithRef(ast);
        default:
          return new this.ExprRef(ast);
      }
    }

    _flattenArgs<T extends AstRef = AnyAst>(args: (T | AstVector<T>)[]): T[] {
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
      return new this.Probe(p);
    }

    _probeNary(
      f: (ctx: Z3_context, left: Z3_probe, right: Z3_probe) => Z3_probe,
      args: [Probe | Z3_probe, ...(Probe | Z3_probe)[]],
    ) {
      assert(args.length > 0, 'At least one argument expected');
      let r = this._toProbe(args[0]);
      for (let i = 1; i < args.length; i++) {
        r = new this.Probe(f(this.ptr, r.ptr, this._toProbe(args[i]).ptr));
      }
      return r;
    }
  }

  class AstRefImpl<Ptr> {
    declare readonly __typename: AstRef['__typename'];

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

    eqIdentity(other: AstRef) {
      this.ctx._assertContext(other);
      return Z3.is_eq_ast(this.ctx.ptr, this.ast, other.ast);
    }

    neqIdentity(other: AstRef) {
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

  /*
  class ParamsRef {
    readonly ptr: Z3_params;

    constructor() {
      const myPtr = Z3.mk_params(ctx.ptr);

      this.ptr = myPtr;

      Z3.params_inc_ref(ctx.ptr, myPtr);
      cleanup.register(this, () => Z3.params_dec_ref(ctx.ptr, myPtr));
    }

    set(key: string, value: boolean | string) {
      const keySymbol = _toSymbol(key);
      if (typeof value === 'boolean') {
        Z3.params_set_bool(ctx.ptr, this.ptr, keySymbol, value);
      } else if (typeof value === 'string') {
        const valueSymbol = _toSymbol(key);
        Z3.params_set_symbol(ctx.ptr, this.ptr, keySymbol, valueSymbol);
      }
    }

    setUInt(key: string, value: number) {
      assert(value >= 0);
      const keySymbol = _toSymbol(key);
      Z3.params_set_uint(ctx.ptr, this.ptr, keySymbol, value);
    }
    setFloat(key: string, value: number) {
      const keySymbol = _toSymbol(key);
      Z3.params_set_double(ctx.ptr, this.ptr, keySymbol, value);
    }
  }
  */

  class SolverImpl {
    declare readonly __typename: Solver['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_solver = Z3.mk_solver(ctx.ptr)) {
      Z3.solver_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.solver_dec_ref(ctx.ptr, ptr));
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
    add(...exprs: (BoolRef | AstVector<BoolRef>)[]) {
      this.ctx._flattenArgs(exprs).forEach(expr => {
        this.ctx._assertContext(expr);
        Z3.solver_assert(this.ctx.ptr, this.ptr, expr.ast);
      });
    }
    addAndTrack(expr: BoolRef, constant: BoolRef | string) {
      if (typeof constant === 'string') {
        constant = this.ctx.Bool(constant);
      }
      assert(this.ctx.isConst(constant), 'Provided expression that is not a constant to addAndTrack');
      Z3.solver_assert_and_track(this.ctx.ptr, this.ptr, expr.ast, constant.ast);
    }

    assertions(): AstVector<BoolRef> {
      return new AstVectorImpl(this.ctx, Z3.solver_get_assertions(this.ctx.ptr, this.ptr));
    }

    async check(...exprs: (BoolRef | AstVector<BoolRef>)[]): Promise<CheckSatResult> {
      const assumptions = this.ctx._flattenArgs(exprs).map(expr => {
        this.ctx._assertContext(expr);
        return expr.ast;
      });
      const result = await Z3.solver_check_assumptions(this.ctx.ptr, this.ptr, assumptions);
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

  class ModelImpl {
    declare readonly __typename: Model['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_model = Z3.mk_model(ctx.ptr)) {
      Z3.model_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.model_dec_ref(ctx.ptr, ptr));
    }

    get length() {
      return Z3.model_get_num_consts(this.ctx.ptr, this.ptr) + Z3.model_get_num_funcs(this.ctx.ptr, this.ptr);
    }

    [Symbol.iterator](): Iterator<FuncDeclRef> {
      return this.values();
    }

    *entries(): IterableIterator<[number, FuncDeclRef]> {
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

    *values(): IterableIterator<FuncDeclRef> {
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

    eval(expr: BoolRef, modelCompletion?: boolean): BoolRef;
    eval(expr: ArithRef, modelCompletion?: boolean): ArithRef;
    eval(expr: ExprRef, modelCompletion: boolean = false) {
      this.ctx._assertContext(expr);
      const r = Z3.model_eval(this.ctx.ptr, this.ptr, expr.ast, modelCompletion);
      if (r === null) {
        throw new Z3Error('Failed to evaluatio expression in the model');
      }
      return this.ctx._toExpr(r);
    }

    get(i: number): FuncDeclRef;
    get(from: number, to: number): FuncDeclRef[];
    get(declaration: FuncDeclRef): FuncInterp | ExprRef;
    get(constant: ExprRef): ExprRef;
    get(sort: SortRef): AstVector<AnyExpr>;
    get(
      i: number | FuncDeclRef | ExprRef | SortRef,
      to?: number,
    ): FuncDeclRef | FuncInterp | ExprRef | AstVector<AnyAst> | FuncDeclRef[] {
      assert(to === undefined || typeof i === 'number');
      if (typeof i === 'number') {
        const length = this.length;

        if (i >= length) {
          throw new RangeError();
        }

        if (to === undefined) {
          const numConsts = Z3.model_get_num_consts(this.ctx.ptr, this.ptr);
          if (i < numConsts) {
            return new this.ctx.FuncDeclRef(Z3.model_get_const_decl(this.ctx.ptr, this.ptr, i));
          } else {
            return new this.ctx.FuncDeclRef(Z3.model_get_func_decl(this.ctx.ptr, this.ptr, i - numConsts));
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

    private getInterp(expr: FuncDeclRef | ExprRef): ExprRef | FuncInterp | null {
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
        return new this.ctx.FuncInterp(interp);
      }
    }

    private getUniverse(sort: SortRef): AstVector<AnyAst> {
      this.ctx._assertContext(sort);
      return new this.ctx.AstVector(Z3.model_get_sort_universe(this.ctx.ptr, this.ptr, sort.ptr));
    }
  }

  class FuncInterpImpl {
    declare readonly __typename: FuncInterp['__typename'];

    constructor(readonly ctx: Context, readonly ptr: Z3_func_interp) {
      Z3.func_interp_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.func_interp_dec_ref(ctx.ptr, ptr));
    }
  }

  class SortRefImpl extends AstRefImpl<Z3_sort> {
    declare readonly __typename: SortRef['__typename'];

    get ast(): Z3_ast {
      return Z3.sort_to_ast(this.ctx.ptr, this.ptr);
    }

    kind() {
      return Z3.get_sort_kind(this.ctx.ptr, this.ptr);
    }

    subsort(other: SortRef) {
      this.ctx._assertContext(other);
      return false;
    }

    cast(expr: ExprRef): ExprRef {
      this.ctx._assertContext(expr);
      assert(expr.sort().eqIdentity(expr.sort()), 'Sort mismatch');
      return expr;
    }

    name() {
      return this.ctx._fromSymbol(Z3.get_sort_name(this.ctx.ptr, this.ptr));
    }

    eqIdentity(other: SortRef) {
      this.ctx._assertContext(other);
      return Z3.is_eq_sort(this.ctx.ptr, this.ptr, other.ptr);
    }

    neqIdentity(other: SortRef) {
      return !this.eqIdentity(other);
    }
  }

  class FuncDeclRefImpl extends AstRefImpl<Z3_func_decl> {
    declare readonly __typename: FuncDeclRef['__typename'];

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

    params(): (number | string | Z3_symbol | SortRef | ExprRef | FuncDeclRef)[] {
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
            result.push(new this.ctx.SortRef(Z3.get_decl_sort_parameter(this.ctx.ptr, this.ptr, i)));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_AST:
            result.push(new this.ctx.ExprRef(Z3.get_decl_ast_parameter(this.ctx.ptr, this.ptr, i)));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
            result.push(new this.ctx.FuncDeclRef(Z3.get_decl_func_decl_parameter(this.ctx.ptr, this.ptr, i)));
            break;
          default:
            assertExhaustive(kind);
        }
      }
      return result;
    }

    call(...args: ExprRef[]) {
      assert(args.length === this.arity(), `Incorrect number of arguments to ${this}`);
      return this.ctx._toExpr(
        Z3.mk_app(
          this.ctx.ptr,
          this.ptr,
          args.map((arg, i) => {
            this.ctx._assertContext(arg);
            return this.domain(i).cast(arg).ast;
          }),
        ),
      );
    }
  }

  class ExprRefImpl<Ptr, Sort extends SortRef = AnySort> extends AstRefImpl<Ptr> {
    declare readonly __typename: ExprRef['__typename'];

    sort(): Sort {
      return this.ctx._toSort(Z3.get_sort(this.ctx.ptr, this.ast)) as Sort;
    }

    eq(other: CoercibleToExpr): BoolRef {
      return new this.ctx.BoolRef(Z3.mk_eq(this.ctx.ptr, this.ast, this.ctx.from(other).ast));
    }

    neq(other: CoercibleToExpr): BoolRef {
      return new this.ctx.BoolRef(
        Z3.mk_distinct(
          this.ctx.ptr,
          [this, other].map(expr => this.ctx.from(expr).ast),
        ),
      );
    }

    params() {
      return this.decl().params();
    }

    decl(): FuncDeclRef {
      assert(this.ctx.isApp(this), 'Z3 application expected');
      return new this.ctx.FuncDeclRef(Z3.get_app_decl(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast)));
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

  class BoolSortRefImpl extends SortRefImpl {
    declare readonly __typename: BoolSortRef['__typename'];

    cast(other: BoolRef | boolean): BoolRef;
    cast(other: CoercibleToExpr): never;
    cast(other: CoercibleToExpr | BoolRef) {
      if (typeof other === 'boolean') {
        other = this.ctx.BoolVal(other);
      }
      assert(this.ctx.isExpr(other), 'true, false or Z3 Boolean expression expected.');
      assert(this.eqIdentity(other.sort()), 'Value cannot be converted into a Z3 Boolean value');
      return other;
    }

    subsort(other: SortRef) {
      this.ctx._assertContext(other.ctx);
      return other instanceof this.ctx.ArithSortRef;
    }
  }

  class BoolRefImpl extends ExprRefImpl<Z3_ast, BoolSortRef> implements BoolRef {
    declare readonly __typename: BoolRef['__typename'];

    mul(other: BoolRef) {
      this.ctx._assertContext(other.ctx);
      return this.ctx.If(this as BoolRef, other, this.ctx.BoolVal(false));
    }
  }

  class PatternRefImpl extends ExprRefImpl<Z3_pattern> {
    declare readonly __typename: PatternRef['__typename'];

    get ast() {
      return Z3.pattern_to_ast(this.ctx.ptr, this.ptr);
    }
  }

  class ProbeImpl {
    declare readonly __typename: Probe['__typename'];

    constructor(readonly ctx: ContextImpl, readonly ptr: Z3_probe) {}
  }

  class TacticImpl {
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

  class ArithSortRefImpl extends SortRefImpl {
    declare readonly __typename: ArithSortRef['__typename'];

    cast(other: bigint | number): IntNumRef | RatNumRef;
    cast(other: CoercibleRational | RatNumRef): RatNumRef;
    cast(other: IntNumRef): IntNumRef;
    cast(other: BoolRef | ArithRef): ArithRef;
    cast(other: CoercibleToExpr): never;
    cast(other: CoercibleToExpr): ArithRef | RatNumRef | IntNumRef {
      const { If, isExpr, isArith, isBool, isIntSort, isRealSort, ToReal, IntVal, RealVal } = this.ctx;
      const sortTypeStr = isIntSort(this) ? 'IntSort' : 'RealSort';
      if (isExpr(other)) {
        const otherS = other.sort();
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
            return IntVal(other);
          }
          return RealVal(other);
        }
        assert(false, `Can't cast primitive to ${sortTypeStr}`);
      }
    }
  }

  class ArithRefImpl extends ExprRefImpl<Z3_ast, ArithSortRef> {
    declare readonly __typename: ArithRef['__typename'];

    add(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.ArithRef(Z3.mk_add(this.ctx.ptr, [this.ast, this.sort().cast(other).ast]));
    }

    mul(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.ArithRef(Z3.mk_mul(this.ctx.ptr, [this.ast, this.sort().cast(other).ast]));
    }

    sub(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.ArithRef(Z3.mk_sub(this.ctx.ptr, [this.ast, this.sort().cast(other).ast]));
    }

    pow(exponent: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.ArithRef(Z3.mk_power(this.ctx.ptr, this.ast, this.sort().cast(exponent).ast));
    }

    div(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.ArithRef(Z3.mk_div(this.ctx.ptr, this.ast, this.sort().cast(other).ast));
    }

    mod(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.ArithRef(Z3.mk_mod(this.ctx.ptr, this.ast, this.sort().cast(other).ast));
    }

    neg() {
      return new this.ctx.ArithRef(Z3.mk_unary_minus(this.ctx.ptr, this.ast));
    }

    le(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.BoolRef(Z3.mk_le(this.ctx.ptr, this.ast, this.sort().cast(other).ast));
    }

    lt(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.BoolRef(Z3.mk_lt(this.ctx.ptr, this.ast, this.sort().cast(other).ast));
    }

    gt(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.BoolRef(Z3.mk_gt(this.ctx.ptr, this.ast, this.sort().cast(other).ast));
    }

    ge(other: ArithRef | number | bigint | string | CoercibleRational) {
      return new this.ctx.BoolRef(Z3.mk_ge(this.ctx.ptr, this.ast, this.sort().cast(other).ast));
    }
  }

  class IntNumRefImpl extends ArithRefImpl {
    declare readonly __typename: IntNumRef['__typename'];

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

  class RatNumRefImpl extends ArithRefImpl {
    declare readonly __typename: RatNumRef['__typename'];

    get value() {
      return { numerator: this.numerator().value, denominator: this.denominator().value };
    }

    numerator() {
      return new this.ctx.IntNumRef(Z3.get_numerator(this.ctx.ptr, this.ast));
    }

    denominator() {
      return new this.ctx.IntNumRef(Z3.get_denominator(this.ctx.ptr, this.ast));
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

  class AstVectorImpl<Item extends AstRef = AnyAst> {
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

  class AstMapImpl<Key extends AstRef = AnyAst, Value extends AstRef = AnyAst> {
    declare readonly __typename: AstMap['__typename'];

    constructor(readonly ctx: Context, readonly ptr: Z3_ast_map = Z3.mk_ast_map(ctx.ptr)) {
      Z3.ast_map_inc_ref(ctx.ptr, ptr);
      cleanup.register(this, () => Z3.ast_map_dec_ref(ctx.ptr, ptr));
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
