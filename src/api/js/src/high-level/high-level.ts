// TODO(ritave): Research whether we can use type system to discern between classes
//               from other contexts.
//               We could use templated string literals Solver<'contextName'> but that would
//               be cumbersome for the end user
// TODO(ritave): Coerce primitives to expressions
// TODO(ritave): Add typing for Context Options
//               https://github.com/Z3Prover/z3/pull/6048#discussion_r883391669
// TODO(ritave): Add an error handler
// TODO(ritave): Add support for building faster floats without support for Safari
// TODO(ritave): Update readme
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
  ArithRef,
  ArithSortRef,
  AstRef,
  AstVector,
  BoolRef,
  BoolSortRef,
  CheckSatResult,
  CoercibleToExpr,
  CoercibleToExprMap,
  Context,
  ExprRef,
  FuncDeclRef,
  FuncInterp,
  PatternRef,
  Probe,
  sat,
  SortRef,
  SortToExprMap,
  Tactic,
  unknown,
  unsat,
  Z3AssertionError,
  Z3Error,
  Z3HighLevel,
} from './types';

export function createApi(Z3: Z3Core): Z3HighLevel {
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

  function createContext(name: string, options: Record<string, any> = {}) {
    // TODO(ritave): Create a custom linting rule that checks if the provided callbacks to cleanup
    //               Don't capture `this`
    const cleanup = new FinalizationRegistry<() => void>(callback => callback());

    function assertContext(...ctxs: Context[]) {
      ctxs.forEach(other => assert(ctx === other, 'Context mismatch'));
    }

    class ContextImpl {
      declare readonly __typename: 'Context';

      readonly ptr: Z3_context;
      readonly name = name;

      constructor(params: Record<string, any>) {
        params = params ?? {};
        const cfg = Z3.mk_config();
        Object.entries(params).forEach(([key, value]) => Z3.set_param_value(cfg, key, value.toString()));
        const context = Z3.mk_context_rc(cfg);
        this.ptr = context;
        Z3.set_ast_print_mode(this.ptr, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
        Z3.del_config(cfg);

        cleanup.register(this, () => Z3.del_context(context));
      }

      interrupt(): void {
        Z3.interrupt(this.ptr);
      }
    }

    const ctx = new ContextImpl(options);

    function _toSymbol(s: string | number) {
      if (typeof s === 'number') {
        return Z3.mk_int_symbol(ctx.ptr, s);
      } else {
        return Z3.mk_string_symbol(ctx.ptr, s);
      }
    }
    function _fromSymbol(sym: Z3_symbol) {
      const kind = Z3.get_symbol_kind(ctx.ptr, sym);
      switch (kind) {
        case Z3_symbol_kind.Z3_INT_SYMBOL:
          return Z3.get_symbol_int(ctx.ptr, sym);
        case Z3_symbol_kind.Z3_STRING_SYMBOL:
          return Z3.get_symbol_string(ctx.ptr, sym);
        default:
          assertExhaustive(kind);
      }
    }

    function _toAst(ast: Z3_ast): AnyAst {
      switch (Z3.get_ast_kind(ctx.ptr, ast)) {
        case Z3_ast_kind.Z3_SORT_AST:
          return _toSort(ast as Z3_sort);
        case Z3_ast_kind.Z3_FUNC_DECL_AST:
          return new FuncDeclRefImpl(ast as Z3_func_decl);
        default:
          return _toExpr(ast);
      }
    }

    function _toSort(ast: Z3_sort) {
      switch (Z3.get_sort_kind(ctx.ptr, ast)) {
        default:
          return new SortRefImpl(ast);
      }
    }

    function _toExpr(ast: Z3_ast): BoolRef | ArithRef | ExprRef {
      const kind = Z3.get_ast_kind(ctx.ptr, ast);
      if (kind === Z3_ast_kind.Z3_QUANTIFIER_AST) {
        assert(false);
      }
      const sortKind = Z3.get_sort_kind(ctx.ptr, Z3.get_sort(ctx.ptr, ast));
      switch (sortKind) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new BoolRefImpl(ast);
        case Z3_sort_kind.Z3_INT_SORT:
          return new ArithRefImpl(ast);
        default:
          return new ExprRefImpl(ast);
      }
    }

    function _flattenArgs<T extends AstRef = AnyAst>(args: (T | AstVector<T>)[]): T[] {
      const result: T[] = [];
      for (const arg of args) {
        if (isAstVector(arg)) {
          result.push(...arg.values());
        } else {
          result.push(arg);
        }
      }
      return result;
    }

    function _toProbe(p: Probe | Z3_probe): Probe {
      if (isProbe(p)) {
        return p;
      }
      return new ProbeImpl(p);
    }

    function _probeNary(
      f: (ctx: Z3_context, left: Z3_probe, right: Z3_probe) => Z3_probe,
      args: [Probe | Z3_probe, ...(Probe | Z3_probe)[]],
    ) {
      assert(args.length > 0, 'At least one argument expected');
      let r = _toProbe(args[0]);
      for (let i = 1; i < args.length; i++) {
        r = new ProbeImpl(f(ctx.ptr, r.probe, _toProbe(args[i]).probe));
      }
      return r;
    }

    function isContext(obj: unknown): obj is ContextImpl {
      const r = obj instanceof ContextImpl;
      r && assertContext(obj);
      return r;
    }

    function isAst(obj: unknown): obj is AstRef {
      const r = obj instanceof AstRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isSort(obj: unknown): obj is SortRef {
      const r = obj instanceof SortRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isFuncDecl(obj: unknown): obj is FuncDeclRef {
      const r = obj instanceof FuncDeclRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isApp(obj: unknown): obj is ExprRef {
      if (!isExpr(obj)) {
        return false;
      }
      const kind = Z3.get_ast_kind(obj.ctx.ptr, obj.ast);
      return kind === Z3_ast_kind.Z3_NUMERAL_AST || kind === Z3_ast_kind.Z3_APP_AST;
    }

    function isConst(obj: unknown): obj is ExprRef {
      return isApp(obj) && obj.numArgs() === 0;
    }

    function isExpr(obj: unknown): obj is ExprRef {
      const r = obj instanceof ExprRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isVar(obj: unknown): obj is ExprRef {
      return isExpr(obj) && Z3.get_ast_kind(obj.ctx.ptr, obj.ast) === Z3_ast_kind.Z3_VAR_AST;
    }

    function isAppOf(obj: unknown, kind: Z3_decl_kind): boolean {
      return isApp(obj) && obj.decl().kind() === kind;
    }

    function isBool(obj: unknown): obj is BoolRef {
      const r = obj instanceof BoolRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isTrue(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_TRUE);
    }

    function isFalse(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_FALSE);
    }

    function isAnd(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_AND);
    }

    function isOr(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_OR);
    }

    function isImplies(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_IMPLIES);
    }

    function isNot(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_NOT);
    }

    function isEq(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_EQ);
    }

    function isDistinct(obj: unknown): obj is BoolRef {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_DISTINCT);
    }

    function isArith(obj: unknown): obj is ArithRef {
      const r = obj instanceof ArithRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isInt(obj: unknown): obj is ArithRef {
      return isArith(obj) && isIntSort(obj.sort());
    }

    function isIntSort(obj: unknown): obj is ArithSortRef {
      return isSort(obj) && obj.kind() === Z3_sort_kind.Z3_INT_SORT;
    }

    function isProbe(obj: unknown): obj is Probe {
      const r = obj instanceof ProbeImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isTactic(obj: unknown): obj is Tactic {
      const r = obj instanceof TacticImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isPattern(obj: unknown): obj is PatternRef {
      const r = obj instanceof PatternRefImpl;
      r && assertContext(obj.ctx);
      return r;
    }

    function isAstVector(obj: unknown): obj is AstVector<AnyAst> {
      const r = obj instanceof AstVectorImpl;
      r && assertContext(obj.ctx);
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

    function eqIdentity(a: AstRef, b: AstRef) {
      return a.eqIdentity(b);
    }

    function getVarIndex(obj: ExprRef): number {
      assert(isVar(obj), 'Z3 bound variable expected');
      return Z3.get_index_value(obj.ctx.ptr, obj.ast);
    }

    function getValue(obj: BoolRef): boolean | null;
    function getValue(obj: ArithRef): number | bigint | null;
    function getValue(obj: ExprRef): boolean | number | bigint | null;
    function getValue(obj: ExprRef): boolean | number | bigint | null {
      if (isBool(obj)) {
        if (isTrue(obj)) {
          return true;
        } else if (isFalse(obj)) {
          return false;
        }
        return null;
      } else if (isInt(obj)) {
        if (Z3.get_ast_kind(ctx.ptr, obj.ast) == Z3_ast_kind.Z3_NUMERAL_AST) {
          return BigInt(Z3.get_numeral_string(ctx.ptr, obj.ast));
        }
        return null;
      }
      assert(false);
    }

    function from(primitive: boolean): BoolRef;
    function from(primitive: number | bigint): ArithRef;
    function from(expr: ExprRef): ExprRef;
    function from(value: CoercibleToExpr): BoolRef | ArithRef | ExprRef;
    function from(value: CoercibleToExpr): BoolRef | ArithRef | ExprRef {
      if ((typeof value === 'number' && Number.isSafeInteger(value)) || typeof value === 'bigint') {
        return IntVal(value);
      } else if (typeof value === 'boolean') {
        return BoolVal(value);
      } else if (isExpr(value)) {
        return value;
      }
      assert(false);
    }

    class AstRefImpl<Ptr> {
      declare readonly __typename: 'AstRef' | 'FuncDeclRef' | SortRef['__typename'] | ExprRef['__typename'];

      readonly ctx: Context;
      readonly ptr: Ptr;

      constructor(ptr: Ptr) {
        this.ctx = ctx;
        this.ptr = ptr;

        const myAst = this.ast;

        Z3.inc_ref(ctx.ptr, myAst);
        cleanup.register(this, () => Z3.dec_ref(ctx.ptr, myAst));
      }

      get ast(): Z3_ast {
        //assert((this.ptr as any).__typename === 'Z3_ast', String(this.ptr));
        return this.ptr as any as Z3_ast;
      }

      get id() {
        return Z3.get_ast_id(this.ctx.ptr, this.ast);
      }

      eqIdentity(other: AstRef) {
        assertContext(other.ctx);
        return Z3.is_eq_ast(this.ctx.ptr, this.ast, other.ast);
      }

      neqIdentity(other: AstRef) {
        assertContext(other.ctx);
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
      declare readonly __typename: 'Solver';

      readonly ptr: Z3_solver;
      readonly ctx = ctx;

      constructor(ptr?: Z3_solver) {
        const myPtr = ptr ?? Z3.mk_solver(ctx.ptr);

        this.ptr = myPtr;

        Z3.solver_inc_ref(ctx.ptr, myPtr);
        cleanup.register(this, () => Z3.solver_dec_ref(ctx.ptr, myPtr));
      }

      push() {
        Z3.solver_push(ctx.ptr, this.ptr);
      }
      pop(num: number = 1) {
        Z3.solver_pop(ctx.ptr, this.ptr, num);
      }
      numScopes() {
        return Z3.solver_get_num_scopes(ctx.ptr, this.ptr);
      }
      reset() {
        Z3.solver_reset(ctx.ptr, this.ptr);
      }
      add(...exprs: (BoolRef | AstVector<BoolRef>)[]) {
        _flattenArgs(exprs).forEach(expr => {
          assertContext(expr.ctx);
          Z3.solver_assert(ctx.ptr, this.ptr, expr.ast);
        });
      }
      addAndTrack(expr: BoolRef, constant: BoolRef | string) {
        if (typeof constant === 'string') {
          constant = Bool(constant);
        }
        assert(isConst(constant), 'Provided expression that is not a constant to addAndTrack');
        Z3.solver_assert_and_track(ctx.ptr, this.ptr, expr.ast, constant.ast);
      }

      async check(...exprs: (BoolRef | AstVector<BoolRef>)[]): Promise<CheckSatResult> {
        const assumptions = _flattenArgs(exprs).map(expr => {
          assertContext(expr.ctx);
          return expr.ast;
        });
        const result = await Z3.solver_check_assumptions(ctx.ptr, this.ptr, assumptions);
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
        return new ModelImpl(Z3.solver_get_model(ctx.ptr, this.ptr));
      }
    }

    class ModelImpl {
      declare readonly __typename: 'Model';

      readonly ctx = ctx;
      readonly ptr: Z3_model;

      constructor(ptr?: Z3_model) {
        const myPtr = ptr ?? Z3.mk_model(ctx.ptr);
        this.ptr = myPtr;

        Z3.model_inc_ref(ctx.ptr, myPtr);
        cleanup.register(this, () => Z3.model_dec_ref(ctx.ptr, myPtr));
      }

      get length() {
        return Z3.model_get_num_consts(ctx.ptr, this.ptr) + Z3.model_get_num_funcs(ctx.ptr, this.ptr);
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
        return Z3.model_to_string(ctx.ptr, this.ptr);
      }

      eval(expr: BoolRef, modelCompletion?: boolean): BoolRef;
      eval(expr: ArithRef, modelCompletion?: boolean): ArithRef;
      eval(expr: ExprRef, modelCompletion: boolean = false) {
        assertContext(expr.ctx);
        const r = Z3.model_eval(ctx.ptr, this.ptr, expr.ast, modelCompletion);
        if (r === null) {
          throw new Z3Error('Failed to evaluatio expression in the model');
        }
        return _toExpr(r);
      }

      get(i: number): FuncDeclRef;
      get(from: number, to: number): FuncDeclRef[];
      get(declaration: FuncDeclRef): FuncInterp;
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
            const numConsts = Z3.model_get_num_consts(ctx.ptr, this.ptr);
            if (i < numConsts) {
              return new FuncDeclRefImpl(Z3.model_get_const_decl(ctx.ptr, this.ptr, i));
            } else {
              return new FuncDeclRefImpl(Z3.model_get_func_decl(ctx.ptr, this.ptr, i - numConsts));
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
        } else if (isFuncDecl(i) || isConst(i)) {
          const result = this.getInterp(i);
          assert(result !== null);
          return result;
        } else if (isSort(i)) {
          return this.getUniverse(i);
        }
        assert(false, 'Number, declaration or constant expected');
      }

      private getInterp(expr: FuncDeclRef | ExprRef): ExprRef | FuncInterp | null {
        assert(isFuncDecl(expr) || isConst(expr), 'Declaration expected');
        if (isConst(expr)) {
          expr = expr.decl();
        }
        if (expr.arity() === 0) {
          const result = Z3.model_get_const_interp(ctx.ptr, this.ptr, expr.ptr);
          if (result === null) {
            return null;
          }
          return _toExpr(result);
        } else {
          const interp = Z3.model_get_func_interp(ctx.ptr, this.ptr, expr.ptr);
          if (interp === null) {
            return null;
          }
          return new FuncInterpImpl(interp);
        }
      }

      private getUniverse(sort: SortRef): AstVector<AnyAst> {
        assertContext(sort.ctx);
        return new AstVectorImpl(Z3.model_get_sort_universe(ctx.ptr, this.ptr, sort.ptr));
      }
    }

    class FuncInterpImpl {
      declare readonly __typename: 'FuncInterp';

      readonly ctx = ctx;
      readonly ptr: Z3_func_interp;

      constructor(ptr: Z3_func_interp) {
        this.ptr = ptr;

        Z3.func_interp_inc_ref(ctx.ptr, ptr);
        cleanup.register(this, () => Z3.func_interp_dec_ref(ctx.ptr, ptr));
      }
    }

    class SortRefImpl extends AstRefImpl<Z3_sort> {
      declare readonly __typename: 'SortRef' | BoolSortRef['__typename'] | ArithSortRef['__typename'];

      get ast(): Z3_ast {
        return Z3.sort_to_ast(ctx.ptr, this.ptr);
      }

      kind() {
        return Z3.get_sort_kind(this.ctx.ptr, this.ptr);
      }

      subsort(other: SortRef) {
        assertContext(other.ctx);
        return false;
      }

      cast(expr: ExprRef): ExprRef {
        assertContext(expr.ctx);
        assert(expr.sort().eqIdentity(expr.sort()), 'Sort mismatch');
        return expr;
      }

      name() {
        return _fromSymbol(Z3.get_sort_name(this.ctx.ptr, this.ptr));
      }

      eqIdentity(other: SortRef) {
        assertContext(other.ctx);
        return Z3.is_eq_sort(this.ctx.ptr, this.ptr, other.ptr);
      }

      neqIdentity(other: SortRef) {
        return !this.eqIdentity(other);
      }
    }

    class FuncDeclRefImpl extends AstRefImpl<Z3_func_decl> {
      declare readonly __typename: 'FuncDeclRef';

      get ast() {
        return Z3.func_decl_to_ast(ctx.ptr, this.ptr);
      }

      name() {
        return _fromSymbol(Z3.get_decl_name(this.ctx.ptr, this.ptr));
      }

      arity() {
        return Z3.get_arity(this.ctx.ptr, this.ptr);
      }

      domain(i: number) {
        assert(i < this.arity(), 'Index out of bounds');
        return _toSort(Z3.get_domain(this.ctx.ptr, this.ptr, i));
      }

      range() {
        return _toSort(Z3.get_range(this.ctx.ptr, this.ptr));
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
              result.push(new SortRefImpl(Z3.get_decl_sort_parameter(this.ctx.ptr, this.ptr, i)));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_AST:
              result.push(new ExprRefImpl(Z3.get_decl_ast_parameter(this.ctx.ptr, this.ptr, i)));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
              result.push(new FuncDeclRefImpl(Z3.get_decl_func_decl_parameter(this.ctx.ptr, this.ptr, i)));
              break;
            default:
              assertExhaustive(kind);
          }
        }
        return result;
      }

      call(...args: ExprRef[]) {
        assert(args.length === this.arity(), `Incorrect number of arguments to ${this}`);
        return _toExpr(
          Z3.mk_app(
            this.ctx.ptr,
            this.ptr,
            args.map((arg, i) => {
              assertContext(arg.ctx);
              return this.domain(i).cast(arg).ast;
            }),
          ),
        );
      }
    }

    class ExprRefImpl<Ptr> extends AstRefImpl<Ptr> {
      declare readonly __typename:
        | 'ExprRef'
        | BoolRef['__typename']
        | PatternRef['__typename']
        | ArithRef['__typename'];

      sort() {
        return _toSort(Z3.get_sort(this.ctx.ptr, this.ast));
      }

      eq(other: CoercibleToExpr): BoolRef {
        return new BoolRefImpl(Z3.mk_eq(this.ctx.ptr, this.ast, from(other).ast));
      }

      neq(other: CoercibleToExpr): BoolRef {
        return new BoolRefImpl(
          Z3.mk_distinct(
            this.ctx.ptr,
            [this, other].map(expr => from(expr).ast),
          ),
        );
      }

      params() {
        return this.decl().params();
      }

      decl(): FuncDeclRef {
        assert(isApp(this), 'Z3 application expected');
        return new FuncDeclRefImpl(Z3.get_app_decl(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast)));
      }

      numArgs(): number {
        assert(isApp(this), 'Z3 applicaiton expected');
        return Z3.get_app_num_args(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast));
      }

      arg(i: number): ReturnType<typeof _toExpr> {
        assert(isApp(this), 'Z3 applicaiton expected');
        assert(i < this.numArgs(), 'Invalid argument index');
        return _toExpr(Z3.get_app_arg(this.ctx.ptr, Z3.to_app(this.ctx.ptr, this.ast), i));
      }

      children(): ReturnType<typeof _toExpr>[] {
        const num_args = this.numArgs();
        if (isApp(this)) {
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
      declare readonly __typename: 'BoolSortRef';

      cast(other: BoolRef | boolean): BoolRef;
      cast(other: CoercibleToExpr): never;
      cast(other: CoercibleToExpr | BoolRef) {
        if (typeof other === 'boolean') {
          other = BoolVal(other);
        }
        assert(isExpr(other), 'true, false or Z3 Boolean expression expected.');
        assert(this.eqIdentity(other.sort()), 'Value cannot be converted into a Z3 Boolean value');
        return other;
      }

      subsort(other: SortRef) {
        assertContext(other.ctx);
        return other instanceof ArithSortRefImpl;
      }
    }

    class BoolRefImpl extends ExprRefImpl<Z3_ast> {
      declare readonly __typename: 'BoolRef';

      sort() {
        return new BoolSortRefImpl(Z3.get_sort(this.ctx.ptr, this.ast));
      }
      mul(other: BoolRef) {
        assertContext(other.ctx);
        return If(this, other, BoolVal(false));
      }
    }

    class PatternRefImpl extends ExprRefImpl<Z3_pattern> {
      declare readonly __typename: 'PatternRef';

      constructor(pattern: Z3_pattern) {
        super(pattern);
      }

      get ast() {
        return Z3.pattern_to_ast(ctx.ptr, this.ptr);
      }
    }

    class ProbeImpl {
      declare readonly __typename: 'Probe';

      public readonly ctx = ctx;

      constructor(public readonly probe: Z3_probe) {}
    }

    class TacticImpl {
      declare readonly __typename: 'Tactic';

      public readonly ctx = ctx;
      public readonly ptr: Z3_tactic;

      constructor(tactic: string | Z3_tactic) {
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
      declare readonly __typename: 'ArithSortRef';

      cast(other: number | bigint | ArithRef | BoolRef): ArithRef;
      cast(other: CoercibleToExpr): never;
      cast(other: CoercibleToExpr): ArithRef {
        if (typeof other === 'number' || typeof other === 'bigint') {
          assert(isInt(this));
          return IntVal(other);
        } else if (isArith(other)) {
          return other;
        } else if (isBool(other)) {
          return If(other, 1, 0);
        }
        assert(false, 'number, bigint, boolean, or Z3 Bool / Arith expect');
      }
    }

    class ArithRefImpl extends ExprRefImpl<Z3_ast> {
      declare readonly __typename: 'ArithRef';

      add(other: ArithRef | number | bigint) {
        return new ArithRefImpl(Z3.mk_add(ctx.ptr, [this.ast, this.coerce(other).ast]));
      }

      mul(other: ArithRef | number | bigint) {
        return new ArithRefImpl(Z3.mk_mul(ctx.ptr, [this.ast, this.coerce(other).ast]));
      }

      sub(other: ArithRef | number | bigint) {
        return new ArithRefImpl(Z3.mk_sub(ctx.ptr, [this.ast, this.coerce(other).ast]));
      }

      pow(exponent: ArithRef | number | bigint) {
        return new ArithRefImpl(Z3.mk_power(ctx.ptr, this.ast, this.coerce(exponent).ast));
      }

      div(other: ArithRef | number | bigint) {
        return new ArithRefImpl(Z3.mk_div(ctx.ptr, this.ast, this.coerce(other).ast));
      }

      mod(other: ArithRef | number | bigint) {
        return new ArithRefImpl(Z3.mk_mod(ctx.ptr, this.ast, this.coerce(other).ast));
      }

      neg() {
        return new ArithRefImpl(Z3.mk_unary_minus(ctx.ptr, this.ast));
      }

      le(other: ArithRef | number | bigint) {
        return new BoolRefImpl(Z3.mk_le(ctx.ptr, this.ast, this.coerce(other).ast));
      }

      lt(other: ArithRef | number | bigint) {
        return new BoolRefImpl(Z3.mk_lt(ctx.ptr, this.ast, this.coerce(other).ast));
      }

      gt(other: ArithRef | number | bigint) {
        return new BoolRefImpl(Z3.mk_gt(ctx.ptr, this.ast, this.coerce(other).ast));
      }

      ge(other: ArithRef | number | bigint) {
        return new BoolRefImpl(Z3.mk_ge(ctx.ptr, this.ast, this.coerce(other).ast));
      }

      private coerce(value: number | bigint | ArithRef): ArithRef {
        assert(isInt(this), 'Reals not implemented yet');
        if (isArith(value)) {
          assert(isInt(this) === isInt(value));
          return value;
        }
        assert(typeof value === 'bigint' || Number.isSafeInteger(value), 'Provided number is not integer');
        return IntVal(value);
      }
    }

    class AstVectorImpl<Item extends AstRef = AnyAst> {
      declare readonly __typename: 'AstVector';

      readonly ctx: Context = ctx;
      readonly ptr: Z3_ast_vector;

      constructor(vector?: Z3_ast_vector) {
        const myVector = vector ?? Z3.mk_ast_vector(ctx.ptr);

        this.ptr = myVector;

        Z3.ast_vector_inc_ref(ctx.ptr, myVector);

        cleanup.register(this, () => Z3.ast_vector_dec_ref(ctx.ptr, myVector));
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
          return _toAst(Z3.ast_vector_get(this.ctx.ptr, this.ptr, from)) as Item;
        }

        if (to < 0) {
          to += length;
        }
        if (to >= length) {
          throw new RangeError();
        }

        const result: Item[] = [];
        for (let i = from; i < to; i++) {
          result.push(_toAst(Z3.ast_vector_get(this.ctx.ptr, this.ptr, i)) as Item);
        }
        return result;
      }

      set(i: number, v: Item): void {
        assertContext(v.ctx);
        if (i >= this.length) {
          throw new RangeError();
        }
        Z3.ast_vector_set(this.ctx.ptr, this.ptr, i, v.ast);
      }

      push(v: Item): void {
        assertContext(v.ctx);
        Z3.ast_vector_push(this.ctx.ptr, this.ptr, v.ast);
      }

      resize(size: number): void {
        Z3.ast_vector_resize(this.ctx.ptr, this.ptr, size);
      }

      has(v: Item): boolean {
        assertContext(v.ctx);
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
      declare readonly __typename: 'AstMap';

      readonly ctx: Context = ctx;
      readonly ptr: Z3_ast_map;

      constructor(ptr?: Z3_ast_map) {
        const myPtr = ptr ?? Z3.mk_ast_map(ctx.ptr);

        this.ptr = myPtr;

        Z3.ast_map_inc_ref(ctx.ptr, myPtr);

        cleanup.register(this, () => Z3.ast_map_dec_ref(ctx.ptr, myPtr));
      }
    }

    function DeclareSort(name: string | number): SortRef {
      return new SortRefImpl(Z3.mk_uninterpreted_sort(ctx.ptr, _toSymbol(name)));
    }

    function Function(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      assertContext(rng.ctx);
      const dom = [];
      for (let i = 0; i < arity; i++) {
        assertContext(signature[i].ctx);
        dom.push(signature[i].ptr);
      }
      const ctx = rng.ctx;
      return new FuncDeclRefImpl(Z3.mk_func_decl(ctx.ptr, _toSymbol(name), dom, rng.ptr));
    }

    function FreshFunction(...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      assertContext(rng.ctx);
      const dom = [];
      for (let i = 0; i < arity; i++) {
        assertContext(signature[i].ctx);
        dom.push(signature[i].ptr);
      }
      const ctx = rng.ctx;
      return new FuncDeclRefImpl(Z3.mk_fresh_func_decl(ctx.ptr, 'f', dom, rng.ptr));
    }

    function RecFunction(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      assertContext(rng.ctx);
      const dom = [];
      for (let i = 0; i < arity; i++) {
        assertContext(signature[i].ctx);
        dom.push(signature[i].ptr);
      }
      const ctx = rng.ctx;
      return new FuncDeclRefImpl(Z3.mk_rec_func_decl(ctx.ptr, _toSymbol(name), dom, rng.ptr));
    }

    function RecAddDefinition(f: FuncDeclRef, args: ExprRef[], body: ExprRef) {
      assertContext(f.ctx, ...args.map(arg => arg.ctx), body.ctx);
      Z3.add_rec_def(
        body.ctx.ptr,
        f.ptr,
        args.map(arg => arg.ast),
        body.ast,
      );
    }

    function If(condition: Probe, onTrue: Tactic, onFalse: Tactic): Tactic;
    function If<OnTrueRef extends CoercibleToExpr, OnFalseRef extends CoercibleToExpr>(
      condition: BoolRef,
      onTrue: OnTrueRef,
      onFalse: OnFalseRef,
    ): CoercibleToExprMap<OnTrueRef | OnFalseRef>;
    function If(
      condition: BoolRef | Probe,
      onTrue: CoercibleToExpr | Tactic,
      onFalse: CoercibleToExpr | Tactic,
    ): ExprRef | Tactic {
      if (isProbe(condition) && isTactic(onTrue) && isTactic(onFalse)) {
        return Cond(condition, onTrue, onFalse);
      }
      assert(!isProbe(condition) && !isTactic(onTrue) && !isTactic(onFalse), 'Mixed expressions and goals');
      onTrue = from(onTrue);
      onFalse = from(onFalse);
      return _toExpr(Z3.mk_ite(ctx.ptr, condition.ptr, onTrue.ast, onFalse.ast));
    }

    function Distinct(...exprs: ExprRef[]): BoolRef {
      assert(exprs.length > 0, "Can't make Distinct ouf of nothing");

      return new BoolRefImpl(
        Z3.mk_distinct(
          ctx.ptr,
          exprs.map(expr => {
            assertContext(expr.ctx);
            return expr.ast;
          }),
        ),
      );
    }

    function Const<S extends SortRef>(name: string, sort: S): SortToExprMap<S> {
      assertContext(sort.ctx);
      return _toExpr(Z3.mk_const(ctx.ptr, _toSymbol(name), sort.ptr)) as SortToExprMap<S>;
    }

    function Consts<S extends SortRef>(names: string | string[], sort: S): SortToExprMap<S>[] {
      assertContext(sort.ctx);
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => Const(name, sort));
    }

    function FreshConst<S extends SortRef>(sort: S, prefix: string = 'c'): SortToExprMap<S> {
      assertContext(sort.ctx);
      return _toExpr(Z3.mk_fresh_const(sort.ctx.ptr, prefix, sort.ptr)) as SortToExprMap<S>;
    }

    function Var<S extends SortRef>(idx: number, sort: S): SortToExprMap<S> {
      assertContext(sort.ctx);
      return _toExpr(Z3.mk_bound(sort.ctx.ptr, idx, sort.ptr)) as SortToExprMap<S>;
    }

    function BoolSort() {
      return new BoolSortRefImpl(Z3.mk_bool_sort(ctx.ptr));
    }

    function BoolVal(value: boolean): BoolRefImpl {
      if (value) {
        return new BoolRefImpl(Z3.mk_true(ctx.ptr));
      }
      return new BoolRefImpl(Z3.mk_false(ctx.ptr));
    }

    function Bool(name: string) {
      return new BoolRefImpl(Z3.mk_const(ctx.ptr, _toSymbol(name), BoolSort().ptr));
    }

    function Bools(names: string | string[]) {
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => Bool(name));
    }

    function BoolVector(prefix: string, count: number) {
      const result = [];
      for (let i = 0; i < count; i++) {
        result.push(Bool(`${prefix}__${i}`));
      }
      return result;
    }

    function FreshBool(prefix = 'b') {
      return new BoolRefImpl(Z3.mk_fresh_const(ctx.ptr, prefix, BoolSort().ptr));
    }

    function Implies(a: BoolRef, b: BoolRef) {
      assertContext(a.ctx, b.ctx);
      return new BoolRefImpl(Z3.mk_implies(ctx.ptr, a.ptr, b.ptr));
    }

    function Eq(a: ExprRef, b: ExprRef) {
      assertContext(a.ctx, b.ctx);
      return a.eq(b);
    }

    function Xor(a: BoolRef, b: BoolRef) {
      assertContext(a.ctx, b.ctx);
      return new BoolRefImpl(Z3.mk_xor(ctx.ptr, a.ptr, b.ptr));
    }

    function Not(a: Probe): Probe;
    function Not(a: BoolRef): BoolRef;
    function Not(a: BoolRef | Probe): BoolRef | Probe {
      assertContext(a.ctx);
      if (isProbe(a)) {
        return new ProbeImpl(Z3.probe_not(ctx.ptr, a.probe));
      }
      return new BoolRefImpl(Z3.mk_not(ctx.ptr, a.ptr));
    }

    function And(): BoolRef;
    function And(vector: AstVector<BoolRef>): BoolRef;
    function And(...args: BoolRef[]): BoolRef;
    function And(...args: Probe[]): Probe;
    function And(...args: (AstVector<BoolRef> | Probe | BoolRef)[]): BoolRef | Probe {
      if (args.length == 1 && args[0] instanceof AstVectorImpl) {
        args = [...args[0].values()];
        assert(allSatisfy(args, isBool) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, isProbe) ?? false;
      if (allProbes) {
        return _probeNary(Z3.probe_and, args as [Probe, ...Probe[]]);
      } else {
        assertContext(...args.map(arg => arg.ctx));
        return new BoolRefImpl(
          Z3.mk_and(
            ctx.ptr,
            args.map(arg => (arg as BoolRef).ptr),
          ),
        );
      }
    }

    function Or(): BoolRef;
    function Or(vector: AstVector<BoolRef>): BoolRef;
    function Or(...args: BoolRef[]): BoolRef;
    function Or(...args: Probe[]): Probe;
    function Or(...args: (AstVector<BoolRef> | Probe | BoolRef)[]): BoolRef | Probe {
      if (args.length == 1 && args[0] instanceof AstVectorImpl) {
        args = [...args[0].values()];
        assert(allSatisfy(args, isBool) ?? true, 'AstVector containing not bools');
      }

      const all_probes = allSatisfy(args, isProbe) ?? false;
      if (all_probes) {
        return _probeNary(Z3.probe_or, args as [Probe, ...Probe[]]);
      } else {
        assertContext(...args.map(arg => arg.ctx));
        return new BoolRefImpl(
          Z3.mk_or(
            ctx.ptr,
            args.map(arg => (arg as BoolRef).ptr),
          ),
        );
      }
    }

    function IntSort() {
      return new ArithSortRefImpl(Z3.mk_int_sort(ctx.ptr));
    }

    function Int(name: string | number) {
      return new ArithRefImpl(Z3.mk_const(ctx.ptr, _toSymbol(name), IntSort().ptr));
    }

    function IntVal(value: number | bigint) {
      assert(typeof value === 'bigint' || Number.isSafeInteger(value));
      return new ArithRefImpl(Z3.mk_numeral(ctx.ptr, value.toString(), IntSort().ptr));
    }

    function Cond(probe: Probe, onTrue: Tactic, onFalse: Tactic): Tactic {
      assertContext(probe.ctx, onTrue.ctx, onFalse.ctx);
      return new TacticImpl(Z3.tactic_cond(ctx.ptr, probe.probe, onTrue.ptr, onFalse.ptr));
    }

    return {
      // Constants
      context: ctx,

      // Functions
      isContext,
      isAst,
      isSort,
      isFuncDecl,
      isApp,
      isConst,
      isExpr,
      isVar,
      isAppOf,
      isBool,
      isTrue,
      isFalse,
      isAnd,
      isOr,
      isImplies,
      isNot,
      isEq,
      isDistinct,
      isArith,
      isInt,
      isIntSort,
      isProbe,
      isTactic,
      isPattern,
      isAstVector,
      /*
      isQuantifier,
      isForAll,
      isExists,
      isLambda,
      */
      eqIdentity,
      getVarIndex,
      getValue,
      from,

      // Classes
      Solver: SolverImpl,
      Model: ModelImpl,
      AstVector: AstVectorImpl,
      AstMap: AstMapImpl,
      Tactic: TacticImpl,

      // Operations
      DeclareSort,
      Function,
      FreshFunction,
      RecFunction,
      RecAddDefinition,
      If,
      Distinct,
      Const,
      Consts,
      FreshConst,
      Var,
      BoolSort,
      BoolVal,
      Bool,
      Bools,
      BoolVector,
      FreshBool,
      Implies,
      Eq,
      Xor,
      Not,
      And,
      Or,
      IntSort,
      Int,
      IntVal,
    };
  }

  return {
    enableTrace,
    disableTrace,
    getVersion,
    getVersionString,
    getFullVersion,
    openLog,
    appendLog,
    setParam,
    resetParams,
    getParam,

    createContext: createContext as Z3HighLevel['createContext'],
  };
}

/**
 * Use to ensure that switches are checked to be exhaustive at compile time
 *
 * ```typescript
 * enum Something {
 *  left,
 *  right,
 * };
 * const something = getSomething();
 * switch (something) {
 *  case Something.left:
 *    ...
 *  case Something.right:
 *    ...
 *  default:
 *    assertExhaustive(something);
 * }
 * ```
 *
 * @param x The param on which the switch operates
 */
function assertExhaustive(x: never): never {
  throw new Error('Unexpected code execution detected, should be caught at compile time');
}

function assert(condition: boolean, reason?: string): asserts condition {
  if (!condition) {
    throw new Z3AssertionError(reason ?? 'Assertion failed');
  }
}

function allSatisfy<T>(collection: Iterable<T>, premise: (arg: T) => boolean): boolean | undefined {
  let result = undefined;
  for (const arg of collection) {
    if (result === undefined) {
      result = premise(arg);
    } else {
      result = result && premise(arg);
    }
  }
  return result;
}

let _lastId = -1;
function nextId() {
  _lastId += 1;
  return _lastId;
}
