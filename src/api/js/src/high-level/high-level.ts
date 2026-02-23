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
  Z3_constructor,
  Z3_constructor_list,
  Z3_decl_kind,
  Z3_error_code,
  Z3_func_decl,
  Z3_func_interp,
  Z3_lbool,
  Z3_model,
  Z3_parameter_kind,
  Z3_probe,
  Z3_solver,
  Z3_sort,
  Z3_sort_kind,
  Z3_stats,
  Z3_symbol,
  Z3_symbol_kind,
  Z3_tactic,
  Z3_pattern,
  Z3_app,
  Z3_params,
  Z3_func_entry,
  Z3_optimize,
  Z3_fixedpoint,
  Z3_goal,
  Z3_apply_result,
  Z3_goal_prec,
  Z3_param_descrs,
  Z3_simplifier,
  Z3_rcf_num,
} from '../low-level';
import {
  AnyAst,
  AnyExpr,
  AnySort,
  Arith,
  ArithSort,
  ArrayIndexType,
  CoercibleToArrayIndexType,
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
  CoercibleToMap,
  CoercibleRational,
  CoercibleToBitVec,
  CoercibleToExpr,
  CoercibleFromMap,
  CoercibleToFP,
  Context,
  ContextCtor,
  Expr,
  FP,
  FPNum,
  FPSort,
  FPRM,
  FPRMSort,
  Fixedpoint,
  FuncDecl,
  FuncDeclSignature,
  FuncInterp,
  IntNum,
  Model,
  Optimize,
  Params,
  ParamDescrs,
  Pattern,
  Probe,
  Quantifier,
  BodyT,
  RatNum,
  RCFNum,
  RCFNumCreation,
  Re,
  ReSort,
  ReCreation,
  Seq,
  SeqSort,
  Simplifier,
  SMTArray,
  SMTArraySort,
  Solver,
  Sort,
  SortToExprMap,
  Statistics,
  StatisticsEntry,
  Tactic,
  Goal,
  ApplyResult,
  Z3Error,
  Z3HighLevel,
  CoercibleToArith,
  NonEmptySortArray,
  FuncEntry,
  SMTSetSort,
  SMTSet,
  Datatype,
  DatatypeSort,
  DatatypeExpr,
  DatatypeCreation,
  FiniteSet,
  FiniteSetSort,
  FiniteSetCreation,
} from './types';
import { allSatisfy, assert, assertExhaustive } from './utils';

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
      (typeof obj!.numerator !== 'number' || Number.isSafeInteger(obj!.numerator)) &&
        (typeof obj!.denominator !== 'number' || Number.isSafeInteger(obj!.denominator)),
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

  function createContext<Name extends string>(name: Name, options?: Record<string, any>): Context<Name> {
    const cfg = Z3.mk_config();
    if (options != null) {
      Object.entries(options).forEach(([key, value]) => check(Z3.set_param_value(cfg, key, value.toString())));
    }
    const contextPtr = Z3.mk_context_rc(cfg);
    Z3.set_ast_print_mode(contextPtr, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
    Z3.del_config(cfg);

    function _assertContext(...ctxs: (Context<Name> | { ctx: Context<Name> })[]) {
      ctxs.forEach(other => assert('ctx' in other ? ctx === other.ctx : ctx === other, 'Context mismatch'));
    }

    function _assertPtr<T extends Number>(ptr: T | null): asserts ptr is T {
      if (ptr == null) throw new TypeError('Expected non-null pointer');
    }

    // call this after every nontrivial call to the underlying API
    function throwIfError() {
      if (Z3.get_error_code(contextPtr) !== Z3_error_code.Z3_OK) {
        throw new Error(Z3.get_error_msg(ctx.ptr, Z3.get_error_code(ctx.ptr)));
      }
    }

    function check<T>(val: T): T {
      throwIfError();
      return val;
    }

    /////////////
    // Private //
    /////////////
    function _toSymbol(s: string | number) {
      if (typeof s === 'number') {
        return check(Z3.mk_int_symbol(contextPtr, s));
      } else {
        return check(Z3.mk_string_symbol(contextPtr, s));
      }
    }

    function _fromSymbol(sym: Z3_symbol) {
      const kind = check(Z3.get_symbol_kind(contextPtr, sym));
      switch (kind) {
        case Z3_symbol_kind.Z3_INT_SYMBOL:
          return Z3.get_symbol_int(contextPtr, sym);
        case Z3_symbol_kind.Z3_STRING_SYMBOL:
          return Z3.get_symbol_string(contextPtr, sym);
        default:
          assertExhaustive(kind);
      }
    }

    function _toParams(key: string, value: any): Z3_params {
      const params = Z3.mk_params(contextPtr);
      Z3.params_inc_ref(contextPtr, params);
      // If value is a boolean
      if (typeof value === 'boolean') {
        Z3.params_set_bool(contextPtr, params, _toSymbol(key), value);
      } else if (typeof value === 'number') {
        // If value is a uint
        if (Number.isInteger(value)) {
          check(Z3.params_set_uint(contextPtr, params, _toSymbol(key), value));
        } else {
          // If value is a double
          check(Z3.params_set_double(contextPtr, params, _toSymbol(key), value));
        }
      } else if (typeof value === 'string') {
        check(Z3.params_set_symbol(contextPtr, params, _toSymbol(key), _toSymbol(value)));
      }
      return params;
    }

    function _toAst(ast: Z3_ast): AnyAst<Name> {
      switch (check(Z3.get_ast_kind(contextPtr, ast))) {
        case Z3_ast_kind.Z3_SORT_AST:
          return _toSort(ast as Z3_sort);
        case Z3_ast_kind.Z3_FUNC_DECL_AST:
          return new FuncDeclImpl(ast as Z3_func_decl);
        default:
          return _toExpr(ast);
      }
    }

    function _toSort(ast: Z3_sort): AnySort<Name> {
      switch (check(Z3.get_sort_kind(contextPtr, ast))) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new BoolSortImpl(ast);
        case Z3_sort_kind.Z3_INT_SORT:
        case Z3_sort_kind.Z3_REAL_SORT:
          return new ArithSortImpl(ast);
        case Z3_sort_kind.Z3_BV_SORT:
          return new BitVecSortImpl(ast);
        case Z3_sort_kind.Z3_FLOATING_POINT_SORT:
          return new FPSortImpl(ast);
        case Z3_sort_kind.Z3_ROUNDING_MODE_SORT:
          return new FPRMSortImpl(ast);
        case Z3_sort_kind.Z3_SEQ_SORT:
          return new SeqSortImpl(ast);
        case Z3_sort_kind.Z3_RE_SORT:
          return new ReSortImpl(ast);
        case Z3_sort_kind.Z3_ARRAY_SORT:
          return new ArraySortImpl(ast);
        default:
          if (Z3.is_finite_set_sort(contextPtr, ast)) {
            return new FiniteSetSortImpl(ast);
          }
          return new SortImpl(ast);
      }
    }

    function _toExpr(ast: Z3_ast): AnyExpr<Name> {
      const kind = check(Z3.get_ast_kind(contextPtr, ast));
      if (kind === Z3_ast_kind.Z3_QUANTIFIER_AST) {
        if (Z3.is_lambda(contextPtr, ast)) {
          return new LambdaImpl(ast);
        }
        return new NonLambdaQuantifierImpl(ast);
      }
      const sortKind = check(Z3.get_sort_kind(contextPtr, Z3.get_sort(contextPtr, ast)));
      switch (sortKind) {
        case Z3_sort_kind.Z3_BOOL_SORT:
          return new BoolImpl(ast);
        case Z3_sort_kind.Z3_INT_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new IntNumImpl(ast);
          }
          return new ArithImpl(ast);
        case Z3_sort_kind.Z3_REAL_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new RatNumImpl(ast);
          }
          return new ArithImpl(ast);
        case Z3_sort_kind.Z3_BV_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST) {
            return new BitVecNumImpl(ast);
          }
          return new BitVecImpl(ast);
        case Z3_sort_kind.Z3_FLOATING_POINT_SORT:
          if (kind === Z3_ast_kind.Z3_NUMERAL_AST || kind === Z3_ast_kind.Z3_APP_AST) {
            return new FPNumImpl(ast);
          }
          return new FPImpl(ast);
        case Z3_sort_kind.Z3_ROUNDING_MODE_SORT:
          return new FPRMImpl(ast);
        case Z3_sort_kind.Z3_SEQ_SORT:
          return new SeqImpl(ast);
        case Z3_sort_kind.Z3_RE_SORT:
          return new ReImpl(ast);
        case Z3_sort_kind.Z3_ARRAY_SORT:
          return new ArrayImpl(ast);
        default:
          if (Z3.is_finite_set_sort(contextPtr, Z3.get_sort(contextPtr, ast))) {
            return new FiniteSetImpl(ast);
          }
          return new ExprImpl(ast);
      }
    }

    function _flattenArgs<T extends AnyAst<Name> = AnyAst<Name>>(args: (T | AstVector<Name, T>)[]): T[] {
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

    function _toProbe(p: Probe<Name> | Z3_probe): Probe<Name> {
      if (isProbe(p)) {
        return p;
      }
      return new ProbeImpl(p);
    }

    function _probeNary(
      f: (ctx: Z3_context, left: Z3_probe, right: Z3_probe) => Z3_probe,
      args: [Probe<Name> | Z3_probe, ...(Probe<Name> | Z3_probe)[]],
    ) {
      assert(args.length > 0, 'At least one argument expected');
      let r = _toProbe(args[0]);
      for (let i = 1; i < args.length; i++) {
        r = new ProbeImpl(check(f(contextPtr, r.ptr, _toProbe(args[i]).ptr)));
      }
      return r;
    }

    ///////////////
    // Functions //
    ///////////////
    function interrupt(): void {
      check(Z3.interrupt(contextPtr));
    }

    function setPrintMode(mode: Z3_ast_print_mode): void {
      Z3.set_ast_print_mode(contextPtr, mode);
    }

    function isModel(obj: unknown): obj is Model<Name> {
      const r = obj instanceof ModelImpl;
      r && _assertContext(obj);
      return r;
    }

    function isAst(obj: unknown): obj is Ast<Name> {
      const r = obj instanceof AstImpl;
      r && _assertContext(obj);
      return r;
    }

    function isSort(obj: unknown): obj is Sort<Name> {
      const r = obj instanceof SortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFuncDecl(obj: unknown): obj is FuncDecl<Name> {
      const r = obj instanceof FuncDeclImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFuncInterp(obj: unknown): obj is FuncInterp<Name> {
      const r = obj instanceof FuncInterpImpl;
      r && _assertContext(obj);
      return r;
    }

    function isApp(obj: unknown): boolean {
      if (!isExpr(obj)) {
        return false;
      }
      const kind = check(Z3.get_ast_kind(contextPtr, obj.ast));
      return kind === Z3_ast_kind.Z3_NUMERAL_AST || kind === Z3_ast_kind.Z3_APP_AST;
    }

    function isConst(obj: unknown): boolean {
      return isExpr(obj) && isApp(obj) && obj.numArgs() === 0;
    }

    function isExpr(obj: unknown): obj is Expr<Name> {
      const r = obj instanceof ExprImpl;
      r && _assertContext(obj);
      return r;
    }

    function isVar(obj: unknown): boolean {
      return isExpr(obj) && check(Z3.get_ast_kind(contextPtr, obj.ast)) === Z3_ast_kind.Z3_VAR_AST;
    }

    function isAppOf(obj: unknown, kind: Z3_decl_kind): boolean {
      return isExpr(obj) && isApp(obj) && obj.decl().kind() === kind;
    }

    function isBool(obj: unknown): obj is Bool<Name> {
      const r = obj instanceof ExprImpl && obj.sort.kind() === Z3_sort_kind.Z3_BOOL_SORT;
      r && _assertContext(obj);
      return r;
    }

    function isTrue(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_TRUE);
    }

    function isFalse(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_FALSE);
    }

    function isAnd(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_AND);
    }

    function isOr(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_OR);
    }

    function isImplies(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_IMPLIES);
    }

    function isNot(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_NOT);
    }

    function isEq(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_EQ);
    }

    function isDistinct(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_DISTINCT);
    }

    function isQuantifier(obj: unknown): obj is Quantifier<Name> {
      const r = obj instanceof QuantifierImpl;
      r && _assertContext(obj);
      return r;
    }

    function isArith(obj: unknown): obj is Arith<Name> {
      const r = obj instanceof ArithImpl;
      r && _assertContext(obj);
      return r;
    }

    function isArithSort(obj: unknown): obj is ArithSort<Name> {
      const r = obj instanceof ArithSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isInt(obj: unknown): boolean {
      return isArith(obj) && isIntSort(obj.sort);
    }

    function isIntVal(obj: unknown): obj is IntNum<Name> {
      const r = obj instanceof IntNumImpl;
      r && _assertContext(obj);
      return r;
    }

    function isIntSort(obj: unknown): boolean {
      return isSort(obj) && obj.kind() === Z3_sort_kind.Z3_INT_SORT;
    }

    function isReal(obj: unknown): boolean {
      return isArith(obj) && isRealSort(obj.sort);
    }

    function isRealVal(obj: unknown): obj is RatNum<Name> {
      const r = obj instanceof RatNumImpl;
      r && _assertContext(obj);
      return r;
    }

    function isRealSort(obj: unknown): boolean {
      return isSort(obj) && obj.kind() === Z3_sort_kind.Z3_REAL_SORT;
    }

    function isRCFNum(obj: unknown): obj is RCFNum<Name> {
      const r = obj instanceof RCFNumImpl;
      r && _assertContext(obj);
      return r;
    }

    function isBitVecSort(obj: unknown): obj is BitVecSort<number, Name> {
      const r = obj instanceof BitVecSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isBitVec(obj: unknown): obj is BitVec<number, Name> {
      const r = obj instanceof BitVecImpl;
      r && _assertContext(obj);
      return r;
    }

    function isBitVecVal(obj: unknown): obj is BitVecNum<number, Name> {
      const r = obj instanceof BitVecNumImpl;
      r && _assertContext(obj);
      return r;
    }

    function isArraySort(obj: unknown): obj is SMTArraySort<Name> {
      const r = obj instanceof ArraySortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isArray(obj: unknown): obj is SMTArray<Name> {
      const r = obj instanceof ArrayImpl;
      r && _assertContext(obj);
      return r;
    }

    function isConstArray(obj: unknown): boolean {
      return isAppOf(obj, Z3_decl_kind.Z3_OP_CONST_ARRAY);
    }

    function isFPRMSort(obj: unknown): obj is FPRMSort<Name> {
      const r = obj instanceof FPRMSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFPRM(obj: unknown): obj is FPRM<Name> {
      const r = obj instanceof FPRMImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFPSort(obj: unknown): obj is FPSort<Name> {
      const r = obj instanceof FPSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFP(obj: unknown): obj is FP<Name> {
      const r = obj instanceof FPImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFPVal(obj: unknown): obj is FPNum<Name> {
      const r = obj instanceof FPNumImpl;
      r && _assertContext(obj);
      return r;
    }

    function isSeqSort(obj: unknown): obj is SeqSort<Name> {
      const r = obj instanceof SeqSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isSeq(obj: unknown): obj is Seq<Name> {
      const r = obj instanceof SeqImpl;
      r && _assertContext(obj);
      return r;
    }

    function isReSort(obj: unknown): obj is ReSort<Name> {
      const r = obj instanceof ReSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isRe(obj: unknown): obj is Re<Name> {
      const r = obj instanceof ReImpl;
      r && _assertContext(obj);
      return r;
    }

    function isStringSort(obj: unknown): obj is SeqSort<Name> {
      return isSeqSort(obj) && obj.isString();
    }

    function isString(obj: unknown): obj is Seq<Name> {
      return isSeq(obj) && obj.isString();
    }

    function isFiniteSetSort(obj: unknown): obj is FiniteSetSort<Name> {
      const r = obj instanceof FiniteSetSortImpl;
      r && _assertContext(obj);
      return r;
    }

    function isFiniteSet(obj: unknown): obj is FiniteSet<Name> {
      const r = obj instanceof FiniteSetImpl;
      r && _assertContext(obj);
      return r;
    }

    function isProbe(obj: unknown): obj is Probe<Name> {
      const r = obj instanceof ProbeImpl;
      r && _assertContext(obj);
      return r;
    }

    function isTactic(obj: unknown): obj is Tactic<Name> {
      const r = obj instanceof TacticImpl;
      r && _assertContext(obj);
      return r;
    }

    function isGoal(obj: unknown): obj is Goal<Name> {
      const r = obj instanceof GoalImpl;
      r && _assertContext(obj);
      return r;
    }

    function isAstVector(obj: unknown): obj is AstVector<Name> {
      const r = obj instanceof AstVectorImpl;
      r && _assertContext(obj);
      return r;
    }

    function eqIdentity(a: Ast<Name>, b: Ast<Name>): boolean {
      return a.eqIdentity(b);
    }

    function getVarIndex(obj: Expr<Name>): number {
      assert(isVar(obj), 'Z3 bound variable expected');
      return Z3.get_index_value(contextPtr, obj.ast);
    }

    function from(primitive: boolean): Bool<Name>;
    function from(primitive: number): IntNum<Name> | RatNum<Name>;
    function from(primitive: CoercibleRational): RatNum<Name>;
    function from(primitive: bigint): IntNum<Name>;
    function from<T extends Expr<Name>>(expr: T): T;
    function from(expr: CoercibleToExpr<Name>): AnyExpr<Name>;
    function from(value: CoercibleToExpr<Name>): AnyExpr<Name> {
      if (typeof value === 'boolean') {
        return Bool.val(value);
      } else if (typeof value === 'number') {
        if (!Number.isFinite(value)) {
          throw new Error(`cannot represent infinity/NaN (got ${value})`);
        }
        if (Math.floor(value) === value) {
          return Int.val(value);
        }
        return Real.val(value);
      } else if (isCoercibleRational(value)) {
        return Real.val(value);
      } else if (typeof value === 'bigint') {
        return Int.val(value);
      } else if (isExpr(value)) {
        return value;
      }
      assert(false);
    }

    async function solve(...assertions: Bool<Name>[]): Promise<Model<Name> | 'unsat' | 'unknown'> {
      const solver = new ctx.Solver();
      solver.add(...assertions);
      const result = await solver.check();
      if (result === 'sat') {
        return solver.model();
      }
      return result;
    }

    ///////////////////////////////
    // expression simplification //
    ///////////////////////////////

    async function simplify(e: Expr<Name>): Promise<Expr<Name>> {
      const result = await Z3.simplify(contextPtr, e.ast);
      return _toExpr(check(result));
    }

    /////////////
    // Objects //
    /////////////
    const Sort = {
      declare: (name: string) => new SortImpl(Z3.mk_uninterpreted_sort(contextPtr, _toSymbol(name))),
    };
    const Function = {
      declare: <DomainSort extends Sort<Name>[], RangeSort extends Sort<Name>>(
        name: string,
        ...signature: [...DomainSort, RangeSort]
      ): FuncDecl<Name, DomainSort, RangeSort> => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        _assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          _assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl<DomainSort, RangeSort>(Z3.mk_func_decl(contextPtr, _toSymbol(name), dom, rng.ptr));
      },
      fresh: <DomainSort extends Sort<Name>[], RangeSort extends Sort<Name>>(
        ...signature: [...DomainSort, RangeSort]
      ): FuncDecl<Name, DomainSort, RangeSort> => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        _assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          _assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl<DomainSort, RangeSort>(Z3.mk_fresh_func_decl(contextPtr, 'f', dom, rng.ptr));
      },
    };
    const RecFunc = {
      declare: (name: string, ...signature: FuncDeclSignature<Name>) => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        _assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          _assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl(Z3.mk_rec_func_decl(contextPtr, _toSymbol(name), dom, rng.ptr));
      },

      addDefinition: (f: FuncDecl<Name>, args: Expr<Name>[], body: Expr<Name>) => {
        _assertContext(f, ...args, body);
        check(
          Z3.add_rec_def(
            contextPtr,
            f.ptr,
            args.map(arg => arg.ast),
            body.ast,
          ),
        );
      },
    };
    const Bool = {
      sort: () => new BoolSortImpl(Z3.mk_bool_sort(contextPtr)),

      const: (name: string) => new BoolImpl(Z3.mk_const(contextPtr, _toSymbol(name), Bool.sort().ptr)),
      consts: (names: string | string[]) => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Bool.const(name));
      },
      vector: (prefix: string, count: number) => {
        const result = [];
        for (let i = 0; i < count; i++) {
          result.push(Bool.const(`${prefix}__${i}`));
        }
        return result;
      },
      fresh: (prefix = 'b') => new BoolImpl(Z3.mk_fresh_const(contextPtr, prefix, Bool.sort().ptr)),

      val: (value: boolean) => {
        if (value) {
          return new BoolImpl(Z3.mk_true(contextPtr));
        }
        return new BoolImpl(Z3.mk_false(contextPtr));
      },
    };
    const Int = {
      sort: () => new ArithSortImpl(Z3.mk_int_sort(contextPtr)),

      const: (name: string) => new ArithImpl(Z3.mk_const(contextPtr, _toSymbol(name), Int.sort().ptr)),
      consts: (names: string | string[]) => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Int.const(name));
      },
      vector: (prefix: string, count: number) => {
        const result = [];
        for (let i = 0; i < count; i++) {
          result.push(Int.const(`${prefix}__${i}`));
        }
        return result;
      },
      fresh: (prefix = 'x') => new ArithImpl(Z3.mk_fresh_const(contextPtr, prefix, Int.sort().ptr)),

      val: (value: number | bigint | string) => {
        assert(typeof value === 'bigint' || typeof value === 'string' || Number.isSafeInteger(value));
        return new IntNumImpl(check(Z3.mk_numeral(contextPtr, value.toString(), Int.sort().ptr)));
      },
    };
    const Real = {
      sort: () => new ArithSortImpl(Z3.mk_real_sort(contextPtr)),

      const: (name: string) => new ArithImpl(check(Z3.mk_const(contextPtr, _toSymbol(name), Real.sort().ptr))),
      consts: (names: string | string[]) => {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Real.const(name));
      },
      vector: (prefix: string, count: number) => {
        const result = [];
        for (let i = 0; i < count; i++) {
          result.push(Real.const(`${prefix}__${i}`));
        }
        return result;
      },
      fresh: (prefix = 'b') => new ArithImpl(Z3.mk_fresh_const(contextPtr, prefix, Real.sort().ptr)),

      val: (value: number | bigint | string | CoercibleRational) => {
        if (isCoercibleRational(value)) {
          value = `${value.numerator}/${value.denominator}`;
        }
        return new RatNumImpl(Z3.mk_numeral(contextPtr, value.toString(), Real.sort().ptr));
      },
    };

    const RCFNum = Object.assign((value: string | number) => new RCFNumImpl(value), {
      pi: () => new RCFNumImpl(check(Z3.rcf_mk_pi(contextPtr))),

      e: () => new RCFNumImpl(check(Z3.rcf_mk_e(contextPtr))),

      infinitesimal: () => new RCFNumImpl(check(Z3.rcf_mk_infinitesimal(contextPtr))),

      roots: (coefficients: RCFNum<Name>[]) => {
        assert(coefficients.length > 0, 'Polynomial coefficients cannot be empty');
        const coeffPtrs = coefficients.map(c => (c as RCFNumImpl).ptr);
        const { rv: numRoots, roots: rootPtrs } = Z3.rcf_mk_roots(contextPtr, coeffPtrs);
        const result: RCFNum<Name>[] = [];
        for (let i = 0; i < numRoots; i++) {
          result.push(new RCFNumImpl(rootPtrs[i]));
        }
        return result;
      },
    }) as RCFNumCreation<Name>;

    const BitVec = {
      sort<Bits extends number>(bits: Bits): BitVecSort<Bits, Name> {
        assert(Number.isSafeInteger(bits), 'number of bits must be an integer');
        return new BitVecSortImpl(Z3.mk_bv_sort(contextPtr, bits));
      },

      const<Bits extends number>(name: string, bits: Bits | BitVecSort<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(
          check(Z3.mk_const(contextPtr, _toSymbol(name), isBitVecSort(bits) ? bits.ptr : BitVec.sort(bits).ptr)),
        );
      },

      consts<Bits extends number>(names: string | string[], bits: Bits | BitVecSort<Bits, Name>): BitVec<Bits, Name>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => BitVec.const(name, bits));
      },

      val<Bits extends number>(
        value: bigint | number | boolean | string,
        bits: Bits | BitVecSort<Bits, Name>,
      ): BitVecNum<Bits, Name> {
        if (value === true) {
          return BitVec.val(1, bits);
        } else if (value === false) {
          return BitVec.val(0, bits);
        }
        return new BitVecNumImpl<Bits>(
          check(Z3.mk_numeral(contextPtr, value.toString(), isBitVecSort(bits) ? bits.ptr : BitVec.sort(bits).ptr)),
        );
      },
    };

    const Float = {
      sort(ebits: number, sbits: number): FPSort<Name> {
        assert(Number.isSafeInteger(ebits) && ebits > 0, 'ebits must be a positive integer');
        assert(Number.isSafeInteger(sbits) && sbits > 0, 'sbits must be a positive integer');
        return new FPSortImpl(Z3.mk_fpa_sort(contextPtr, ebits, sbits));
      },

      sort16(): FPSort<Name> {
        return new FPSortImpl(Z3.mk_fpa_sort_16(contextPtr));
      },

      sort32(): FPSort<Name> {
        return new FPSortImpl(Z3.mk_fpa_sort_32(contextPtr));
      },

      sort64(): FPSort<Name> {
        return new FPSortImpl(Z3.mk_fpa_sort_64(contextPtr));
      },

      sort128(): FPSort<Name> {
        return new FPSortImpl(Z3.mk_fpa_sort_128(contextPtr));
      },

      const(name: string, sort: FPSort<Name>): FP<Name> {
        return new FPImpl(check(Z3.mk_const(contextPtr, _toSymbol(name), sort.ptr)));
      },

      consts(names: string | string[], sort: FPSort<Name>): FP<Name>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Float.const(name, sort));
      },

      val(value: number, sort: FPSort<Name>): FPNum<Name> {
        return new FPNumImpl(check(Z3.mk_fpa_numeral_double(contextPtr, value, sort.ptr)));
      },

      NaN(sort: FPSort<Name>): FPNum<Name> {
        return new FPNumImpl(check(Z3.mk_fpa_nan(contextPtr, sort.ptr)));
      },

      inf(sort: FPSort<Name>, negative: boolean = false): FPNum<Name> {
        return new FPNumImpl(check(Z3.mk_fpa_inf(contextPtr, sort.ptr, negative)));
      },

      zero(sort: FPSort<Name>, negative: boolean = false): FPNum<Name> {
        return new FPNumImpl(check(Z3.mk_fpa_zero(contextPtr, sort.ptr, negative)));
      },
    };

    const FloatRM = {
      sort(): FPRMSort<Name> {
        return new FPRMSortImpl(Z3.mk_fpa_rounding_mode_sort(contextPtr));
      },

      RNE(): FPRM<Name> {
        return new FPRMImpl(check(Z3.mk_fpa_rne(contextPtr)));
      },

      RNA(): FPRM<Name> {
        return new FPRMImpl(check(Z3.mk_fpa_rna(contextPtr)));
      },

      RTP(): FPRM<Name> {
        return new FPRMImpl(check(Z3.mk_fpa_rtp(contextPtr)));
      },

      RTN(): FPRM<Name> {
        return new FPRMImpl(check(Z3.mk_fpa_rtn(contextPtr)));
      },

      RTZ(): FPRM<Name> {
        return new FPRMImpl(check(Z3.mk_fpa_rtz(contextPtr)));
      },
    };

    const String = {
      sort(): SeqSort<Name> {
        return new SeqSortImpl(Z3.mk_string_sort(contextPtr));
      },

      const(name: string): Seq<Name> {
        return new SeqImpl(check(Z3.mk_const(contextPtr, _toSymbol(name), String.sort().ptr)));
      },

      consts(names: string | string[]): Seq<Name>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => String.const(name));
      },

      val(value: string): Seq<Name> {
        return new SeqImpl(check(Z3.mk_string(contextPtr, value)));
      },
    };

    const Seq = {
      sort<ElemSort extends Sort<Name>>(elemSort: ElemSort): SeqSort<Name, ElemSort> {
        return new SeqSortImpl<ElemSort>(Z3.mk_seq_sort(contextPtr, elemSort.ptr));
      },

      empty<ElemSort extends Sort<Name>>(elemSort: ElemSort): Seq<Name, ElemSort> {
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_empty(contextPtr, Seq.sort(elemSort).ptr)));
      },

      unit<ElemSort extends Sort<Name>>(elem: Expr<Name>): Seq<Name, ElemSort> {
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_unit(contextPtr, elem.ast)));
      },
    };

    const Re = {
      sort<SeqSortRef extends SeqSort<Name>>(seqSort: SeqSortRef): ReSort<Name, SeqSortRef> {
        return new ReSortImpl<SeqSortRef>(Z3.mk_re_sort(contextPtr, seqSort.ptr));
      },

      toRe(seq: Seq<Name> | string): Re<Name> {
        const seqExpr = isSeq(seq) ? seq : String.val(seq);
        return new ReImpl(check(Z3.mk_seq_to_re(contextPtr, seqExpr.ast)));
      },
    };

    const Array = {
      sort<DomainSort extends NonEmptySortArray<Name>, RangeSort extends AnySort<Name>>(
        ...sig: [...DomainSort, RangeSort]
      ): SMTArraySort<Name, DomainSort, RangeSort> {
        const arity = sig.length - 1;
        const r = sig[arity];
        const d = sig[0];
        if (arity === 1) {
          return new ArraySortImpl(Z3.mk_array_sort(contextPtr, d.ptr, r.ptr));
        }
        const dom = sig.slice(0, arity);
        return new ArraySortImpl(
          Z3.mk_array_sort_n(
            contextPtr,
            dom.map(s => s.ptr),
            r.ptr,
          ),
        );
      },
      const<DomainSort extends NonEmptySortArray<Name>, RangeSort extends AnySort<Name>>(
        name: string,
        ...sig: [...DomainSort, RangeSort]
      ): SMTArray<Name, DomainSort, RangeSort> {
        return new ArrayImpl<DomainSort, RangeSort>(
          check(Z3.mk_const(contextPtr, _toSymbol(name), Array.sort(...sig).ptr)),
        );
      },
      consts<DomainSort extends NonEmptySortArray<Name>, RangeSort extends AnySort<Name>>(
        names: string | string[],
        ...sig: [...DomainSort, RangeSort]
      ): SMTArray<Name, DomainSort, RangeSort>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Array.const(name, ...sig));
      },
      K<DomainSort extends AnySort<Name>, RangeSort extends AnySort<Name>>(
        domain: DomainSort,
        value: SortToExprMap<RangeSort, Name>,
      ): SMTArray<Name, [DomainSort], RangeSort> {
        return new ArrayImpl<[DomainSort], RangeSort>(check(Z3.mk_const_array(contextPtr, domain.ptr, value.ptr)));
      },
    };
    const Set = {
      // reference: https://z3prover.github.io/api/html/namespacez3py.html#a545f894afeb24caa1b88b7f2a324ee7e
      sort<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSetSort<Name, ElemSort> {
        return Array.sort(sort, Bool.sort());
      },
      const<ElemSort extends AnySort<Name>>(name: string, sort: ElemSort): SMTSet<Name, ElemSort> {
        return new SetImpl<ElemSort>(
          check(Z3.mk_const(contextPtr, _toSymbol(name), Array.sort(sort, Bool.sort()).ptr)),
        );
      },
      consts<ElemSort extends AnySort<Name>>(names: string | string[], sort: ElemSort): SMTSet<Name, ElemSort>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Set.const(name, sort));
      },
      empty<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort> {
        return EmptySet(sort);
      },
      val<ElemSort extends AnySort<Name>>(
        values: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>[],
        sort: ElemSort,
      ): SMTSet<Name, ElemSort> {
        var result = EmptySet(sort);
        for (const value of values) {
          result = SetAdd(result, value);
        }
        return result;
      },
    };

    const FiniteSet = {
      sort<ElemSort extends Sort<Name>>(elemSort: ElemSort): FiniteSetSort<Name, ElemSort> {
        return new FiniteSetSortImpl<ElemSort>(check(Z3.mk_finite_set_sort(contextPtr, elemSort.ptr)));
      },
      const<ElemSort extends Sort<Name>>(name: string, elemSort: ElemSort): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(
          check(Z3.mk_const(contextPtr, _toSymbol(name), FiniteSet.sort(elemSort).ptr)),
        );
      },
      consts<ElemSort extends Sort<Name>>(names: string | string[], elemSort: ElemSort): FiniteSet<Name, ElemSort>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => FiniteSet.const(name, elemSort));
      },
      empty<ElemSort extends Sort<Name>>(sort: ElemSort): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(check(Z3.mk_finite_set_empty(contextPtr, FiniteSet.sort(sort).ptr)));
      },
      singleton<ElemSort extends Sort<Name>>(elem: Expr<Name>): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(check(Z3.mk_finite_set_singleton(contextPtr, elem.ast)));
      },
      range(low: Expr<Name>, high: Expr<Name>): FiniteSet<Name, Sort<Name>> {
        return new FiniteSetImpl(check(Z3.mk_finite_set_range(contextPtr, low.ast, high.ast)));
      },
    };

    const Datatype = Object.assign(
      (name: string): DatatypeImpl => {
        return new DatatypeImpl(ctx, name);
      },
      {
        createDatatypes(...datatypes: DatatypeImpl[]): DatatypeSortImpl[] {
          return createDatatypes(...datatypes);
        },
      },
    );

    ////////////////
    // Operations //
    ////////////////
    function If(condition: Probe<Name>, onTrue: Tactic<Name>, onFalse: Tactic<Name>): Tactic<Name>;
    function If<OnTrueRef extends CoercibleToExpr<Name>, OnFalseRef extends CoercibleToExpr<Name>>(
      condition: Bool<Name> | boolean,
      onTrue: OnTrueRef,
      onFalse: OnFalseRef,
    ): CoercibleFromMap<OnTrueRef | OnFalseRef, Name>;
    function If(
      condition: Bool<Name> | Probe<Name> | boolean,
      onTrue: CoercibleToExpr<Name> | Tactic<Name>,
      onFalse: CoercibleToExpr<Name> | Tactic<Name>,
    ): Expr<Name> | Tactic<Name> {
      if (isProbe(condition) && isTactic(onTrue) && isTactic(onFalse)) {
        return Cond(condition, onTrue, onFalse);
      }
      assert(!isProbe(condition) && !isTactic(onTrue) && !isTactic(onFalse), 'Mixed expressions and goals');
      if (typeof condition === 'boolean') {
        condition = Bool.val(condition);
      }
      onTrue = from(onTrue);
      onFalse = from(onFalse);
      return _toExpr(check(Z3.mk_ite(contextPtr, condition.ptr, onTrue.ast, onFalse.ast)));
    }

    function Distinct(...exprs: CoercibleToExpr<Name>[]): Bool<Name> {
      assert(exprs.length > 0, "Can't make Distinct ouf of nothing");

      return new BoolImpl(
        check(
          Z3.mk_distinct(
            contextPtr,
            exprs.map(expr => {
              expr = from(expr);
              _assertContext(expr);
              return expr.ast;
            }),
          ),
        ),
      );
    }

    function Const<S extends Sort<Name>>(name: string, sort: S): SortToExprMap<S, Name> {
      _assertContext(sort);
      return _toExpr(check(Z3.mk_const(contextPtr, _toSymbol(name), sort.ptr))) as SortToExprMap<S, Name>;
    }

    function Consts<S extends Sort<Name>>(names: string | string[], sort: S): SortToExprMap<S, Name>[] {
      _assertContext(sort);
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => Const(name, sort));
    }

    function FreshConst<S extends Sort<Name>>(sort: S, prefix: string = 'c'): SortToExprMap<S, Name> {
      _assertContext(sort);
      return _toExpr(Z3.mk_fresh_const(sort.ctx.ptr, prefix, sort.ptr)) as SortToExprMap<S, Name>;
    }

    function Var<S extends Sort<Name>>(idx: number, sort: S): SortToExprMap<S, Name> {
      _assertContext(sort);
      return _toExpr(Z3.mk_bound(sort.ctx.ptr, idx, sort.ptr)) as SortToExprMap<S, Name>;
    }

    function Implies(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name> {
      a = from(a) as Bool<Name>;
      b = from(b) as Bool<Name>;
      _assertContext(a, b);
      return new BoolImpl(check(Z3.mk_implies(contextPtr, a.ptr, b.ptr)));
    }

    function Iff(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name> {
      a = from(a) as Bool<Name>;
      b = from(b) as Bool<Name>;
      _assertContext(a, b);
      return new BoolImpl(check(Z3.mk_iff(contextPtr, a.ptr, b.ptr)));
    }

    function Eq(a: CoercibleToExpr<Name>, b: CoercibleToExpr<Name>): Bool<Name> {
      a = from(a);
      b = from(b);
      _assertContext(a, b);
      return a.eq(b);
    }

    function Xor(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name> {
      a = from(a) as Bool<Name>;
      b = from(b) as Bool<Name>;
      _assertContext(a, b);
      return new BoolImpl(check(Z3.mk_xor(contextPtr, a.ptr, b.ptr)));
    }

    function Not(a: Probe<Name>): Probe<Name>;
    function Not(a: Bool<Name> | boolean): Bool<Name>;
    function Not(a: Bool<Name> | boolean | Probe<Name>): Bool<Name> | Probe<Name> {
      if (typeof a === 'boolean') {
        a = from(a);
      }
      _assertContext(a);
      if (isProbe(a)) {
        return new ProbeImpl(check(Z3.probe_not(contextPtr, a.ptr)));
      }
      return new BoolImpl(check(Z3.mk_not(contextPtr, a.ptr)));
    }

    function And(): Bool<Name>;
    function And(vector: AstVector<Name, Bool<Name>>): Bool<Name>;
    function And(...args: (Bool<Name> | boolean)[]): Bool<Name>;
    function And(...args: Probe<Name>[]): Probe<Name>;
    function And(
      ...args: (AstVector<Name, Bool<Name>> | Probe<Name> | Bool<Name> | boolean)[]
    ): Bool<Name> | Probe<Name> {
      if (args.length == 1 && args[0] instanceof ctx.AstVector) {
        args = [...args[0].values()];
        assert(allSatisfy(args, isBool) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, isProbe) ?? false;
      if (allProbes) {
        return _probeNary(Z3.probe_and, args as [Probe<Name>, ...Probe<Name>[]]);
      } else {
        const castArgs = args.map(from) as Bool<Name>[];
        _assertContext(...castArgs);
        return new BoolImpl(
          check(
            Z3.mk_and(
              contextPtr,
              castArgs.map(arg => arg.ptr),
            ),
          ),
        );
      }
    }

    function Or(): Bool<Name>;
    function Or(vector: AstVector<Name, Bool<Name>>): Bool<Name>;
    function Or(...args: (Bool<Name> | boolean)[]): Bool<Name>;
    function Or(...args: Probe<Name>[]): Probe<Name>;
    function Or(
      ...args: (AstVector<Name, Bool<Name>> | Probe<Name> | Bool<Name> | boolean)[]
    ): Bool<Name> | Probe<Name> {
      if (args.length == 1 && args[0] instanceof ctx.AstVector) {
        args = [...args[0].values()];
        assert(allSatisfy(args, isBool) ?? true, 'AstVector containing not bools');
      }

      const allProbes = allSatisfy(args, isProbe) ?? false;
      if (allProbes) {
        return _probeNary(Z3.probe_or, args as [Probe<Name>, ...Probe<Name>[]]);
      } else {
        const castArgs = args.map(from) as Bool<Name>[];
        _assertContext(...castArgs);
        return new BoolImpl(
          check(
            Z3.mk_or(
              contextPtr,
              castArgs.map(arg => arg.ptr),
            ),
          ),
        );
      }
    }

    function PbEq(args: [Bool<Name>, ...Bool<Name>[]], coeffs: [number, ...number[]], k: number): Bool<Name> {
      _assertContext(...args);
      if (args.length !== coeffs.length) {
        throw new Error('Number of arguments and coefficients must match');
      }
      return new BoolImpl(
        check(
          Z3.mk_pbeq(
            contextPtr,
            args.map(arg => arg.ast),
            coeffs,
            k,
          ),
        ),
      );
    }

    function PbGe(args: [Bool<Name>, ...Bool<Name>[]], coeffs: [number, ...number[]], k: number): Bool<Name> {
      _assertContext(...args);
      if (args.length !== coeffs.length) {
        throw new Error('Number of arguments and coefficients must match');
      }
      return new BoolImpl(
        check(
          Z3.mk_pbge(
            contextPtr,
            args.map(arg => arg.ast),
            coeffs,
            k,
          ),
        ),
      );
    }

    function PbLe(args: [Bool<Name>, ...Bool<Name>[]], coeffs: [number, ...number[]], k: number): Bool<Name> {
      _assertContext(...args);
      if (args.length !== coeffs.length) {
        throw new Error('Number of arguments and coefficients must match');
      }
      return new BoolImpl(
        check(
          Z3.mk_pble(
            contextPtr,
            args.map(arg => arg.ast),
            coeffs,
            k,
          ),
        ),
      );
    }

    function AtMost(args: [Bool<Name>, ...Bool<Name>[]], k: number): Bool<Name> {
      _assertContext(...args);
      return new BoolImpl(
        check(
          Z3.mk_atmost(
            contextPtr,
            args.map(arg => arg.ast),
            k,
          ),
        ),
      );
    }

    function AtLeast(args: [Bool<Name>, ...Bool<Name>[]], k: number): Bool<Name> {
      _assertContext(...args);
      return new BoolImpl(
        check(
          Z3.mk_atleast(
            contextPtr,
            args.map(arg => arg.ast),
            k,
          ),
        ),
      );
    }

    function ForAll<QVarSorts extends NonEmptySortArray<Name>>(
      quantifiers: ArrayIndexType<Name, QVarSorts>,
      body: Bool<Name>,
      weight: number = 1,
    ): NonLambdaQuantifierImpl<QVarSorts> {
      // Verify all quantifiers are constants
      if (!allSatisfy(quantifiers, isConst)) {
        throw new Error('Quantifier variables must be constants');
      }

      return new NonLambdaQuantifierImpl<QVarSorts>(
        check(
          Z3.mk_quantifier_const_ex(
            contextPtr,
            true,
            weight,
            _toSymbol(''),
            _toSymbol(''),
            quantifiers.map(q => q.ptr as unknown as Z3_app), // The earlier check verifies these are all apps
            [],
            [],
            body.ptr,
          ),
        ),
      );
    }

    function Exists<QVarSorts extends NonEmptySortArray<Name>>(
      quantifiers: ArrayIndexType<Name, QVarSorts>,
      body: Bool<Name>,
      weight: number = 1,
    ): NonLambdaQuantifierImpl<QVarSorts> {
      // Verify all quantifiers are constants
      if (!allSatisfy(quantifiers, isConst)) {
        throw new Error('Quantifier variables must be constants');
      }

      return new NonLambdaQuantifierImpl<QVarSorts>(
        check(
          Z3.mk_quantifier_const_ex(
            contextPtr,
            false,
            weight,
            _toSymbol(''),
            _toSymbol(''),
            quantifiers.map(q => q.ptr as unknown as Z3_app), // The earlier check verifies these are all apps
            [],
            [],
            body.ptr,
          ),
        ),
      );
    }

    function Lambda<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
      quantifiers: ArrayIndexType<Name, DomainSort>,
      expr: SortToExprMap<RangeSort, Name>,
    ): LambdaImpl<any, RangeSort> {
      // TODO(walden): For some reason LambdaImpl<DomainSort, RangeSort> leads to type issues
      //    and Typescript won't build. I'm not sure why since the types seem to all match
      //    up. For now, we just use any for the domain sort

      // Verify all quantifiers are constants
      if (!allSatisfy(quantifiers, isConst)) {
        throw new Error('Quantifier variables must be constants');
      }

      return new LambdaImpl<DomainSort, RangeSort>(
        check(
          Z3.mk_lambda_const(
            contextPtr,
            quantifiers.map(q => q.ptr as unknown as Z3_app),
            expr.ptr,
          ),
        ),
      );
    }

    function ToReal(expr: Arith<Name> | bigint): Arith<Name> {
      expr = from(expr) as Arith<Name>;
      _assertContext(expr);
      assert(isInt(expr), 'Int expression expected');
      return new ArithImpl(check(Z3.mk_int2real(contextPtr, expr.ast)));
    }

    function ToInt(expr: Arith<Name> | number | CoercibleRational | string): Arith<Name> {
      if (!isExpr(expr)) {
        expr = Real.val(expr);
      }
      _assertContext(expr);
      assert(isReal(expr), 'Real expression expected');
      return new ArithImpl(check(Z3.mk_real2int(contextPtr, expr.ast)));
    }

    function IsInt(expr: Arith<Name> | number | CoercibleRational | string): Bool<Name> {
      if (!isExpr(expr)) {
        expr = Real.val(expr);
      }
      _assertContext(expr);
      assert(isReal(expr), 'Real expression expected');
      return new BoolImpl(check(Z3.mk_is_int(contextPtr, expr.ast)));
    }

    function Sqrt(a: Arith<Name> | number | bigint | string | CoercibleRational): Arith<Name> {
      if (!isExpr(a)) {
        a = Real.val(a);
      }
      return a.pow('1/2');
    }

    function Cbrt(a: Arith<Name> | number | bigint | string | CoercibleRational): Arith<Name> {
      if (!isExpr(a)) {
        a = Real.val(a);
      }
      return a.pow('1/3');
    }

    function BV2Int<Bits extends number>(a: BitVec<Bits, Name>, isSigned: boolean): Arith<Name> {
      _assertContext(a);
      return new ArithImpl(check(Z3.mk_bv2int(contextPtr, a.ast, isSigned)));
    }

    function Int2BV<Bits extends number>(a: Arith<Name> | bigint | number, bits: Bits): BitVec<Bits, Name> {
      if (isArith(a)) {
        assert(isInt(a), 'parameter must be an integer');
      } else {
        assert(typeof a !== 'number' || Number.isSafeInteger(a), 'parameter must not have decimal places');
        a = Int.val(a);
      }
      return new BitVecImpl<Bits>(check(Z3.mk_int2bv(contextPtr, bits, a.ast)));
    }

    function Concat<Bits extends number>(...bitvecs: BitVec<Bits, Name>[]): BitVec<Bits, Name> {
      _assertContext(...bitvecs);
      return bitvecs.reduce((prev, curr) => new BitVecImpl<Bits>(check(Z3.mk_concat(contextPtr, prev.ast, curr.ast))));
    }

    function Cond(probe: Probe<Name>, onTrue: Tactic<Name>, onFalse: Tactic<Name>): Tactic<Name> {
      _assertContext(probe, onTrue, onFalse);
      return new TacticImpl(check(Z3.tactic_cond(contextPtr, probe.ptr, onTrue.ptr, onFalse.ptr)));
    }

    function _toTactic(t: Tactic<Name> | string): Tactic<Name> {
      return typeof t === 'string' ? new TacticImpl(t) : t;
    }

    function AndThen(
      t1: Tactic<Name> | string,
      t2: Tactic<Name> | string,
      ...ts: (Tactic<Name> | string)[]
    ): Tactic<Name> {
      let result = _toTactic(t1);
      let current = _toTactic(t2);
      _assertContext(result, current);
      result = new TacticImpl(check(Z3.tactic_and_then(contextPtr, result.ptr, current.ptr)));

      for (const t of ts) {
        current = _toTactic(t);
        _assertContext(result, current);
        result = new TacticImpl(check(Z3.tactic_and_then(contextPtr, result.ptr, current.ptr)));
      }

      return result;
    }

    function OrElse(
      t1: Tactic<Name> | string,
      t2: Tactic<Name> | string,
      ...ts: (Tactic<Name> | string)[]
    ): Tactic<Name> {
      let result = _toTactic(t1);
      let current = _toTactic(t2);
      _assertContext(result, current);
      result = new TacticImpl(check(Z3.tactic_or_else(contextPtr, result.ptr, current.ptr)));

      for (const t of ts) {
        current = _toTactic(t);
        _assertContext(result, current);
        result = new TacticImpl(check(Z3.tactic_or_else(contextPtr, result.ptr, current.ptr)));
      }

      return result;
    }

    const UINT_MAX = 4294967295;

    function Repeat(t: Tactic<Name> | string, max?: number): Tactic<Name> {
      const tactic = _toTactic(t);
      _assertContext(tactic);
      const maxVal = max !== undefined ? max : UINT_MAX;
      return new TacticImpl(check(Z3.tactic_repeat(contextPtr, tactic.ptr, maxVal)));
    }

    function TryFor(t: Tactic<Name> | string, ms: number): Tactic<Name> {
      const tactic = _toTactic(t);
      _assertContext(tactic);
      return new TacticImpl(check(Z3.tactic_try_for(contextPtr, tactic.ptr, ms)));
    }

    function When(p: Probe<Name>, t: Tactic<Name> | string): Tactic<Name> {
      const tactic = _toTactic(t);
      _assertContext(p, tactic);
      return new TacticImpl(check(Z3.tactic_when(contextPtr, p.ptr, tactic.ptr)));
    }

    function Skip(): Tactic<Name> {
      return new TacticImpl(check(Z3.tactic_skip(contextPtr)));
    }

    function Fail(): Tactic<Name> {
      return new TacticImpl(check(Z3.tactic_fail(contextPtr)));
    }

    function FailIf(p: Probe<Name>): Tactic<Name> {
      _assertContext(p);
      return new TacticImpl(check(Z3.tactic_fail_if(contextPtr, p.ptr)));
    }

    function ParOr(...tactics: (Tactic<Name> | string)[]): Tactic<Name> {
      assert(tactics.length > 0, 'ParOr requires at least one tactic');
      const tacticImpls = tactics.map(t => _toTactic(t));
      _assertContext(...tacticImpls);
      const tacticPtrs = tacticImpls.map(t => t.ptr);
      return new TacticImpl(check(Z3.tactic_par_or(contextPtr, tacticPtrs)));
    }

    function ParAndThen(t1: Tactic<Name> | string, t2: Tactic<Name> | string): Tactic<Name> {
      const tactic1 = _toTactic(t1);
      const tactic2 = _toTactic(t2);
      _assertContext(tactic1, tactic2);
      return new TacticImpl(check(Z3.tactic_par_and_then(contextPtr, tactic1.ptr, tactic2.ptr)));
    }

    function With(t: Tactic<Name> | string, params: Record<string, any>): Tactic<Name> {
      const tactic = _toTactic(t);
      _assertContext(tactic);
      // Convert params to Z3_params
      const z3params = check(Z3.mk_params(contextPtr));
      Z3.params_inc_ref(contextPtr, z3params);
      try {
        for (const [key, value] of Object.entries(params)) {
          const sym = _toSymbol(key);
          if (typeof value === 'boolean') {
            Z3.params_set_bool(contextPtr, z3params, sym, value);
          } else if (typeof value === 'number') {
            if (Number.isInteger(value)) {
              Z3.params_set_uint(contextPtr, z3params, sym, value);
            } else {
              Z3.params_set_double(contextPtr, z3params, sym, value);
            }
          } else if (typeof value === 'string') {
            Z3.params_set_symbol(contextPtr, z3params, sym, _toSymbol(value));
          } else {
            throw new Error(`Unsupported parameter type for ${key}`);
          }
        }
        const result = new TacticImpl(check(Z3.tactic_using_params(contextPtr, tactic.ptr, z3params)));
        return result;
      } finally {
        Z3.params_dec_ref(contextPtr, z3params);
      }
    }

    function LT(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_lt(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function GT(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_gt(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function LE(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_le(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function GE(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_ge(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function ULT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvult(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function UGT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvugt(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function ULE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvule(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function UGE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvuge(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function SLT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvslt(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function SGT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvsgt(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function SLE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvsle(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function SGE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_bvsge(contextPtr, a.ast, a.sort.cast(b).ast)));
    }

    function Extract<Bits extends number>(hi: number, lo: number, val: BitVec<Bits, Name>): BitVec<number, Name> {
      return new BitVecImpl<number>(check(Z3.mk_extract(contextPtr, hi, lo, val.ast)));
    }

    function Select<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
      array: SMTArray<Name, DomainSort, RangeSort>,
      ...indices: CoercibleToArrayIndexType<Name, DomainSort>
    ): SortToExprMap<RangeSort, Name> {
      const args = indices.map((arg, i) => array.domain_n(i).cast(arg as any));
      if (args.length === 1) {
        return _toExpr(check(Z3.mk_select(contextPtr, array.ast, args[0].ast))) as SortToExprMap<RangeSort, Name>;
      }
      const _args = args.map(arg => arg.ast);
      return _toExpr(check(Z3.mk_select_n(contextPtr, array.ast, _args))) as SortToExprMap<RangeSort, Name>;
    }

    function Store<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
      array: SMTArray<Name, DomainSort, RangeSort>,
      ...indicesAndValue: [
        ...CoercibleToArrayIndexType<Name, DomainSort>,
        CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
      ]
    ): SMTArray<Name, DomainSort, RangeSort> {
      const args = indicesAndValue.map((arg, i) => {
        if (i === indicesAndValue.length - 1) {
          return array.range().cast(arg as any) as SortToExprMap<RangeSort, Name>;
        }
        return array.domain_n(i).cast(arg as any);
      });
      if (args.length <= 1) {
        throw new Error('Array store requires both index and value arguments');
      }
      if (args.length === 2) {
        return _toExpr(check(Z3.mk_store(contextPtr, array.ast, args[0].ast, args[1].ast))) as SMTArray<
          Name,
          DomainSort,
          RangeSort
        >;
      }
      const _idxs = args.slice(0, args.length - 1).map(arg => arg.ast);
      return _toExpr(check(Z3.mk_store_n(contextPtr, array.ast, _idxs, args[args.length - 1].ast))) as SMTArray<
        Name,
        DomainSort,
        RangeSort
      >;
    }

    /**
     * Create array extensionality index given two arrays with the same sort.
     * The meaning is given by the axiom:
     * (=> (= (select A (array-ext A B)) (select B (array-ext A B))) (= A B))
     * Two arrays are equal if and only if they are equal on the index returned by this function.
     */
    function Ext<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
      a: SMTArray<Name, DomainSort, RangeSort>,
      b: SMTArray<Name, DomainSort, RangeSort>,
    ): SortToExprMap<DomainSort[0], Name> {
      return _toExpr(check(Z3.mk_array_ext(contextPtr, a.ast, b.ast))) as SortToExprMap<DomainSort[0], Name>;
    }

    function SetUnion<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(
        check(
          Z3.mk_set_union(
            contextPtr,
            args.map(arg => arg.ast),
          ),
        ),
      );
    }

    function SetIntersect<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(
        check(
          Z3.mk_set_intersect(
            contextPtr,
            args.map(arg => arg.ast),
          ),
        ),
      );
    }

    function SetDifference<ElemSort extends AnySort<Name>>(
      a: SMTSet<Name, ElemSort>,
      b: SMTSet<Name, ElemSort>,
    ): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_set_difference(contextPtr, a.ast, b.ast)));
    }

    function SetAdd<ElemSort extends AnySort<Name>>(
      set: SMTSet<Name, ElemSort>,
      elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>,
    ): SMTSet<Name, ElemSort> {
      const arg = set.elemSort().cast(elem as any);
      return new SetImpl<ElemSort>(check(Z3.mk_set_add(contextPtr, set.ast, arg.ast)));
    }
    function SetDel<ElemSort extends AnySort<Name>>(
      set: SMTSet<Name, ElemSort>,
      elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>,
    ): SMTSet<Name, ElemSort> {
      const arg = set.elemSort().cast(elem as any);
      return new SetImpl<ElemSort>(check(Z3.mk_set_del(contextPtr, set.ast, arg.ast)));
    }
    function SetComplement<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_set_complement(contextPtr, set.ast)));
    }

    function EmptySet<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_empty_set(contextPtr, sort.ptr)));
    }
    function FullSet<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_full_set(contextPtr, sort.ptr)));
    }
    function isMember<ElemSort extends AnySort<Name>>(
      elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>,
      set: SMTSet<Name, ElemSort>,
    ): Bool<Name> {
      const arg = set.elemSort().cast(elem as any);
      return new BoolImpl(check(Z3.mk_set_member(contextPtr, arg.ast, set.ast)));
    }
    function isSubset<ElemSort extends AnySort<Name>>(
      a: SMTSet<Name, ElemSort>,
      b: SMTSet<Name, ElemSort>,
    ): Bool<Name> {
      return new BoolImpl(check(Z3.mk_set_subset(contextPtr, a.ast, b.ast)));
    }

    //////////////////////
    // Regular Expressions
    //////////////////////

    function InRe(seq: Seq<Name> | string, re: Re<Name>): Bool<Name> {
      const seqExpr = isSeq(seq) ? seq : String.val(seq);
      return new BoolImpl(check(Z3.mk_seq_in_re(contextPtr, seqExpr.ast, re.ast)));
    }

    function Union<SeqSortRef extends SeqSort<Name>>(...res: Re<Name, SeqSortRef>[]): Re<Name, SeqSortRef> {
      if (res.length === 0) {
        throw new Error('Union requires at least one argument');
      }
      if (res.length === 1) {
        return res[0];
      }
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_union(contextPtr, res.map(r => r.ast))));
    }

    function Intersect<SeqSortRef extends SeqSort<Name>>(...res: Re<Name, SeqSortRef>[]): Re<Name, SeqSortRef> {
      if (res.length === 0) {
        throw new Error('Intersect requires at least one argument');
      }
      if (res.length === 1) {
        return res[0];
      }
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_intersect(contextPtr, res.map(r => r.ast))));
    }

    function ReConcat<SeqSortRef extends SeqSort<Name>>(...res: Re<Name, SeqSortRef>[]): Re<Name, SeqSortRef> {
      if (res.length === 0) {
        throw new Error('ReConcat requires at least one argument');
      }
      if (res.length === 1) {
        return res[0];
      }
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_concat(contextPtr, res.map(r => r.ast))));
    }

    function Plus<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_plus(contextPtr, re.ast)));
    }

    function Star<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_star(contextPtr, re.ast)));
    }

    function Option<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_option(contextPtr, re.ast)));
    }

    function Complement<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_complement(contextPtr, re.ast)));
    }

    function Diff<SeqSortRef extends SeqSort<Name>>(a: Re<Name, SeqSortRef>, b: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_diff(contextPtr, a.ast, b.ast)));
    }

    function Range<SeqSortRef extends SeqSort<Name>>(lo: Seq<Name, SeqSortRef> | string, hi: Seq<Name, SeqSortRef> | string): Re<Name, SeqSortRef> {
      const loSeq = isSeq(lo) ? lo : String.val(lo);
      const hiSeq = isSeq(hi) ? hi : String.val(hi);
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_range(contextPtr, loSeq.ast, hiSeq.ast)));
    }

    /**
     * Create a bounded repetition regex.
     * @param re The regex to repeat
     * @param lo Minimum number of repetitions
     * @param hi Maximum number of repetitions (0 means unbounded, i.e., at least lo)
     */
    function Loop<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>, lo: number, hi: number = 0): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_loop(contextPtr, re.ast, lo, hi)));
    }

    function Power<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>, n: number): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_power(contextPtr, re.ast, n)));
    }

    function AllChar<SeqSortRef extends SeqSort<Name>>(reSort: ReSort<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_allchar(contextPtr, reSort.ptr)));
    }

    function Empty<SeqSortRef extends SeqSort<Name>>(reSort: ReSort<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_empty(contextPtr, reSort.ptr)));
    }

    function Full<SeqSortRef extends SeqSort<Name>>(reSort: ReSort<Name, SeqSortRef>): Re<Name, SeqSortRef> {
      return new ReImpl<SeqSortRef>(check(Z3.mk_re_full(contextPtr, reSort.ptr)));
    }

    function mkPartialOrder(sort: Sort<Name>, index: number): FuncDecl<Name> {
      return new FuncDeclImpl(check(Z3.mk_partial_order(contextPtr, sort.ptr, index)));
    }

    function mkTransitiveClosure(f: FuncDecl<Name>): FuncDecl<Name> {
      return new FuncDeclImpl(check(Z3.mk_transitive_closure(contextPtr, f.ptr)));
    }

    async function polynomialSubresultants(
      p: Arith<Name>,
      q: Arith<Name>,
      x: Arith<Name>,
    ): Promise<AstVector<Name, Arith<Name>>> {
      const result = await Z3.polynomial_subresultants(contextPtr, p.ast, q.ast, x.ast);
      return new AstVectorImpl<ArithImpl>(check(result));
    }

    class AstImpl<Ptr extends Z3_ast> implements Ast<Name, Ptr> {
      declare readonly __typename: Ast['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Ptr) {
        this.ctx = ctx;
        const myAst = this.ast;

        Z3.inc_ref(contextPtr, myAst);
        cleanup.register(this, () => Z3.dec_ref(contextPtr, myAst), this);
      }

      get ast(): Z3_ast {
        return this.ptr;
      }

      id() {
        return Z3.get_ast_id(contextPtr, this.ast);
      }

      eqIdentity(other: Ast<Name>) {
        _assertContext(other);
        return check(Z3.is_eq_ast(contextPtr, this.ast, other.ast));
      }

      neqIdentity(other: Ast<Name>) {
        _assertContext(other);
        return !this.eqIdentity(other);
      }

      sexpr() {
        return Z3.ast_to_string(contextPtr, this.ast);
      }

      hash() {
        return Z3.get_ast_hash(contextPtr, this.ast);
      }

      toString() {
        return this.sexpr();
      }
    }

    class SolverImpl implements Solver<Name> {
      declare readonly __typename: Solver['__typename'];

      readonly ctx: Context<Name>;
      private _ptr: Z3_solver | null;
      get ptr(): Z3_solver {
        _assertPtr(this._ptr);
        return this._ptr;
      }

      constructor(ptr: Z3_solver | string = Z3.mk_solver(contextPtr)) {
        this.ctx = ctx;
        let myPtr: Z3_solver;
        if (typeof ptr === 'string') {
          myPtr = check(Z3.mk_solver_for_logic(contextPtr, _toSymbol(ptr)));
        } else {
          myPtr = ptr;
        }
        this._ptr = myPtr;
        Z3.solver_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.solver_dec_ref(contextPtr, myPtr), this);
      }

      set(key: string, value: any): void {
        Z3.solver_set_params(contextPtr, this.ptr, _toParams(key, value));
      }

      push() {
        Z3.solver_push(contextPtr, this.ptr);
      }

      pop(num: number = 1) {
        Z3.solver_pop(contextPtr, this.ptr, num);
      }

      numScopes() {
        return Z3.solver_get_num_scopes(contextPtr, this.ptr);
      }

      reset() {
        Z3.solver_reset(contextPtr, this.ptr);
      }

      add(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]) {
        _flattenArgs(exprs).forEach(expr => {
          _assertContext(expr);
          check(Z3.solver_assert(contextPtr, this.ptr, expr.ast));
        });
      }

      addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string) {
        if (typeof constant === 'string') {
          constant = Bool.const(constant);
        }
        assert(isConst(constant), 'Provided expression that is not a constant to addAndTrack');
        check(Z3.solver_assert_and_track(contextPtr, this.ptr, expr.ast, constant.ast));
      }

      addSimplifier(simplifier: Simplifier<Name>): void {
        _assertContext(simplifier);
        check(Z3.solver_add_simplifier(contextPtr, this.ptr, simplifier.ptr));
      }

      assertions(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.solver_get_assertions(contextPtr, this.ptr)));
      }

      async check(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): Promise<CheckSatResult> {
        const assumptions = _flattenArgs(exprs).map(expr => {
          _assertContext(expr);
          return expr.ast;
        });
        const result = await asyncMutex.runExclusive(() =>
          check(Z3.solver_check_assumptions(contextPtr, this.ptr, assumptions)),
        );
        switch (result) {
          case Z3_lbool.Z3_L_FALSE:
            return 'unsat';
          case Z3_lbool.Z3_L_TRUE:
            return 'sat';
          case Z3_lbool.Z3_L_UNDEF:
            return 'unknown';
          default:
            assertExhaustive(result);
        }
      }

      unsatCore(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.solver_get_unsat_core(contextPtr, this.ptr)));
      }

      model() {
        return new ModelImpl(check(Z3.solver_get_model(contextPtr, this.ptr)));
      }

      statistics(): Statistics<Name> {
        return new StatisticsImpl(check(Z3.solver_get_statistics(contextPtr, this.ptr)));
      }

      reasonUnknown(): string {
        return check(Z3.solver_get_reason_unknown(contextPtr, this.ptr));
      }

      toString() {
        return check(Z3.solver_to_string(contextPtr, this.ptr));
      }

      toSmtlib2(status: string = 'unknown'): string {
        const assertionsVec = this.assertions();
        const numAssertions = assertionsVec.length();
        let formula: Z3_ast;
        let assumptions: Z3_ast[];

        if (numAssertions > 0) {
          // Use last assertion as formula and rest as assumptions
          assumptions = [];
          for (let i = 0; i < numAssertions - 1; i++) {
            assumptions.push(assertionsVec.get(i).ast);
          }
          formula = assertionsVec.get(numAssertions - 1).ast;
        } else {
          // No assertions, use true
          assumptions = [];
          formula = ctx.Bool.val(true).ast;
        }

        return check(Z3.benchmark_to_smtlib_string(
          contextPtr,
          '',
          '',
          status,
          '',
          assumptions,
          formula
        ));
      }

      fromString(s: string) {
        Z3.solver_from_string(contextPtr, this.ptr, s);
        throwIfError();
      }

      units(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.solver_get_units(contextPtr, this.ptr)));
      }

      nonUnits(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.solver_get_non_units(contextPtr, this.ptr)));
      }

      trail(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.solver_get_trail(contextPtr, this.ptr)));
      }

      trailLevels(): number[] {
        const trailVec = check(Z3.solver_get_trail(contextPtr, this.ptr));
        const n = Z3.ast_vector_size(contextPtr, trailVec);
        return check(Z3.solver_get_levels(contextPtr, this.ptr, trailVec, n));
      }

      async cube(vars?: AstVector<Name, Bool<Name>>, cutoff: number = 0xFFFFFFFF): Promise<AstVector<Name, Bool<Name>>> {
        const tempVars = vars ?? new AstVectorImpl();
        const result = await asyncMutex.runExclusive(() =>
          check(Z3.solver_cube(contextPtr, this.ptr, tempVars.ptr, cutoff)),
        );
        return new AstVectorImpl(result);
      }

      async getConsequences(
        assumptions: (Bool<Name> | AstVector<Name, Bool<Name>>)[],
        variables: Expr<Name>[],
      ): Promise<[CheckSatResult, AstVector<Name, Bool<Name>>]> {
        const asmsVec = new AstVectorImpl();
        const varsVec = new AstVectorImpl();
        const consVec = new AstVectorImpl<Bool<Name>>();
        _flattenArgs(assumptions).forEach(expr => {
          _assertContext(expr);
          Z3.ast_vector_push(contextPtr, asmsVec.ptr, expr.ast);
        });
        variables.forEach(v => {
          _assertContext(v);
          Z3.ast_vector_push(contextPtr, varsVec.ptr, v.ast);
        });
        const r = await asyncMutex.runExclusive(() =>
          check(Z3.solver_get_consequences(contextPtr, this.ptr, asmsVec.ptr, varsVec.ptr, consVec.ptr)),
        );
        let status: CheckSatResult;
        switch (r) {
          case Z3_lbool.Z3_L_FALSE:
            status = 'unsat';
            break;
          case Z3_lbool.Z3_L_TRUE:
            status = 'sat';
            break;
          default:
            status = 'unknown';
        }
        return [status, consVec];
      }

      solveFor(variables: Expr<Name>[], terms: Expr<Name>[], guards: Bool<Name>[]): void {
        const varsVec = new AstVectorImpl();
        const termsVec = new AstVectorImpl();
        const guardsVec = new AstVectorImpl();
        variables.forEach(v => {
          _assertContext(v);
          Z3.ast_vector_push(contextPtr, varsVec.ptr, v.ast);
        });
        terms.forEach(t => {
          _assertContext(t);
          Z3.ast_vector_push(contextPtr, termsVec.ptr, t.ast);
        });
        guards.forEach(g => {
          _assertContext(g);
          Z3.ast_vector_push(contextPtr, guardsVec.ptr, g.ast);
        });
        Z3.solver_solve_for(contextPtr, this.ptr, varsVec.ptr, termsVec.ptr, guardsVec.ptr);
        throwIfError();
      }

      setInitialValue(variable: Expr<Name>, value: Expr<Name>): void {
        _assertContext(variable);
        _assertContext(value);
        Z3.solver_set_initial_value(contextPtr, this.ptr, variable.ast, value.ast);
        throwIfError();
      }

      congruenceRoot(expr: Expr<Name>): Expr<Name> {
        _assertContext(expr);
        return _toExpr(check(Z3.solver_congruence_root(contextPtr, this.ptr, expr.ast)));
      }

      congruenceNext(expr: Expr<Name>): Expr<Name> {
        _assertContext(expr);
        return _toExpr(check(Z3.solver_congruence_next(contextPtr, this.ptr, expr.ast)));
      }

      congruenceExplain(a: Expr<Name>, b: Expr<Name>): Expr<Name> {
        _assertContext(a);
        _assertContext(b);
        return _toExpr(check(Z3.solver_congruence_explain(contextPtr, this.ptr, a.ast, b.ast)));
      }

      fromFile(filename: string) {
        Z3.solver_from_file(contextPtr, this.ptr, filename);
        throwIfError();
      }

      release() {
        Z3.solver_dec_ref(contextPtr, this.ptr);
        // Mark the ptr as null to prevent double free
        this._ptr = null;
        cleanup.unregister(this);
      }
    }

    class OptimizeImpl implements Optimize<Name> {
      declare readonly __typename: Optimize['__typename'];

      readonly ctx: Context<Name>;
      private _ptr: Z3_optimize | null;
      get ptr(): Z3_optimize {
        _assertPtr(this._ptr);
        return this._ptr;
      }

      constructor(ptr: Z3_optimize = Z3.mk_optimize(contextPtr)) {
        this.ctx = ctx;
        let myPtr: Z3_optimize;
        myPtr = ptr;
        this._ptr = myPtr;
        Z3.optimize_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.optimize_dec_ref(contextPtr, myPtr), this);
      }

      set(key: string, value: any): void {
        Z3.optimize_set_params(contextPtr, this.ptr, _toParams(key, value));
      }

      push() {
        Z3.optimize_push(contextPtr, this.ptr);
      }

      pop() {
        Z3.optimize_pop(contextPtr, this.ptr);
      }

      add(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]) {
        _flattenArgs(exprs).forEach(expr => {
          _assertContext(expr);
          check(Z3.optimize_assert(contextPtr, this.ptr, expr.ast));
        });
      }

      addSoft(expr: Bool<Name>, weight: number | bigint | string | CoercibleRational, id: number | string = '') {
        if (isCoercibleRational(weight)) {
          weight = `${weight.numerator}/${weight.denominator}`;
        }
        check(Z3.optimize_assert_soft(contextPtr, this.ptr, expr.ast, weight.toString(), _toSymbol(id)));
      }

      addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string) {
        if (typeof constant === 'string') {
          constant = Bool.const(constant);
        }
        assert(isConst(constant), 'Provided expression that is not a constant to addAndTrack');
        check(Z3.optimize_assert_and_track(contextPtr, this.ptr, expr.ast, constant.ast));
      }

      assertions(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.optimize_get_assertions(contextPtr, this.ptr)));
      }

      maximize(expr: Arith<Name> | BitVec<number, Name>) {
        check(Z3.optimize_maximize(contextPtr, this.ptr, expr.ast));
      }

      minimize(expr: Arith<Name> | BitVec<number, Name>) {
        check(Z3.optimize_minimize(contextPtr, this.ptr, expr.ast));
      }

      async check(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): Promise<CheckSatResult> {
        const assumptions = _flattenArgs(exprs).map(expr => {
          _assertContext(expr);
          return expr.ast;
        });
        const result = await asyncMutex.runExclusive(() => check(Z3.optimize_check(contextPtr, this.ptr, assumptions)));
        switch (result) {
          case Z3_lbool.Z3_L_FALSE:
            return 'unsat';
          case Z3_lbool.Z3_L_TRUE:
            return 'sat';
          case Z3_lbool.Z3_L_UNDEF:
            return 'unknown';
          default:
            assertExhaustive(result);
        }
      }

      model() {
        return new ModelImpl(check(Z3.optimize_get_model(contextPtr, this.ptr)));
      }

      statistics(): Statistics<Name> {
        return new StatisticsImpl(check(Z3.optimize_get_statistics(contextPtr, this.ptr)));
      }

      setInitialValue(variable: Expr<Name>, value: Expr<Name>): void {
        _assertContext(variable);
        _assertContext(value);
        Z3.optimize_set_initial_value(contextPtr, this.ptr, variable.ast, value.ast);
        throwIfError();
      }

      toString() {
        return check(Z3.optimize_to_string(contextPtr, this.ptr));
      }

      fromString(s: string) {
        Z3.optimize_from_string(contextPtr, this.ptr, s);
        throwIfError();
      }

      release() {
        Z3.optimize_dec_ref(contextPtr, this.ptr);
        this._ptr = null;
        cleanup.unregister(this);
      }
    }

    class FixedpointImpl implements Fixedpoint<Name> {
      declare readonly __typename: Fixedpoint['__typename'];

      readonly ctx: Context<Name>;
      private _ptr: Z3_fixedpoint | null;
      get ptr(): Z3_fixedpoint {
        _assertPtr(this._ptr);
        return this._ptr;
      }

      constructor(ptr: Z3_fixedpoint = Z3.mk_fixedpoint(contextPtr)) {
        this.ctx = ctx;
        let myPtr: Z3_fixedpoint;
        myPtr = ptr;
        this._ptr = myPtr;
        Z3.fixedpoint_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.fixedpoint_dec_ref(contextPtr, myPtr), this);
      }

      set(key: string, value: any): void {
        Z3.fixedpoint_set_params(contextPtr, this.ptr, _toParams(key, value));
      }

      help(): string {
        return check(Z3.fixedpoint_get_help(contextPtr, this.ptr));
      }

      add(...constraints: Bool<Name>[]) {
        constraints.forEach(constraint => {
          _assertContext(constraint);
          check(Z3.fixedpoint_assert(contextPtr, this.ptr, constraint.ast));
        });
      }

      registerRelation(pred: FuncDecl<Name>): void {
        _assertContext(pred);
        check(Z3.fixedpoint_register_relation(contextPtr, this.ptr, pred.ptr));
      }

      addRule(rule: Bool<Name>, name?: string): void {
        _assertContext(rule);
        const symbol = _toSymbol(name ?? '');
        check(Z3.fixedpoint_add_rule(contextPtr, this.ptr, rule.ast, symbol));
      }

      addFact(pred: FuncDecl<Name>, ...args: number[]): void {
        _assertContext(pred);
        check(Z3.fixedpoint_add_fact(contextPtr, this.ptr, pred.ptr, args));
      }

      updateRule(rule: Bool<Name>, name: string): void {
        _assertContext(rule);
        const symbol = _toSymbol(name);
        check(Z3.fixedpoint_update_rule(contextPtr, this.ptr, rule.ast, symbol));
      }

      async query(query: Bool<Name>): Promise<CheckSatResult> {
        _assertContext(query);
        const result = await asyncMutex.runExclusive(() => check(Z3.fixedpoint_query(contextPtr, this.ptr, query.ast)));
        switch (result) {
          case Z3_lbool.Z3_L_FALSE:
            return 'unsat';
          case Z3_lbool.Z3_L_TRUE:
            return 'sat';
          case Z3_lbool.Z3_L_UNDEF:
            return 'unknown';
          default:
            assertExhaustive(result);
        }
      }

      async queryRelations(...relations: FuncDecl<Name>[]): Promise<CheckSatResult> {
        relations.forEach(rel => _assertContext(rel));
        const decls = relations.map(rel => rel.ptr);
        const result = await asyncMutex.runExclusive(() =>
          check(Z3.fixedpoint_query_relations(contextPtr, this.ptr, decls)),
        );
        switch (result) {
          case Z3_lbool.Z3_L_FALSE:
            return 'unsat';
          case Z3_lbool.Z3_L_TRUE:
            return 'sat';
          case Z3_lbool.Z3_L_UNDEF:
            return 'unknown';
          default:
            assertExhaustive(result);
        }
      }

      getAnswer(): Expr<Name> | null {
        const ans = check(Z3.fixedpoint_get_answer(contextPtr, this.ptr));
        return ans ? _toExpr(ans) : null;
      }

      getReasonUnknown(): string {
        return check(Z3.fixedpoint_get_reason_unknown(contextPtr, this.ptr));
      }

      getNumLevels(pred: FuncDecl<Name>): number {
        _assertContext(pred);
        return check(Z3.fixedpoint_get_num_levels(contextPtr, this.ptr, pred.ptr));
      }

      getCoverDelta(level: number, pred: FuncDecl<Name>): Expr<Name> | null {
        _assertContext(pred);
        const res = check(Z3.fixedpoint_get_cover_delta(contextPtr, this.ptr, level, pred.ptr));
        return res ? _toExpr(res) : null;
      }

      addCover(level: number, pred: FuncDecl<Name>, property: Expr<Name>): void {
        _assertContext(pred);
        _assertContext(property);
        check(Z3.fixedpoint_add_cover(contextPtr, this.ptr, level, pred.ptr, property.ast));
      }

      getRules(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.fixedpoint_get_rules(contextPtr, this.ptr)));
      }

      getAssertions(): AstVector<Name, Bool<Name>> {
        return new AstVectorImpl(check(Z3.fixedpoint_get_assertions(contextPtr, this.ptr)));
      }

      setPredicateRepresentation(pred: FuncDecl<Name>, kinds: string[]): void {
        _assertContext(pred);
        const symbols = kinds.map(kind => _toSymbol(kind));
        check(Z3.fixedpoint_set_predicate_representation(contextPtr, this.ptr, pred.ptr, symbols));
      }

      toString(): string {
        return check(Z3.fixedpoint_to_string(contextPtr, this.ptr, []));
      }

      fromString(s: string): AstVector<Name, Bool<Name>> {
        const av = check(Z3.fixedpoint_from_string(contextPtr, this.ptr, s));
        return new AstVectorImpl(av);
      }

      fromFile(file: string): AstVector<Name, Bool<Name>> {
        const av = check(Z3.fixedpoint_from_file(contextPtr, this.ptr, file));
        return new AstVectorImpl(av);
      }

      statistics(): Statistics<Name> {
        return new StatisticsImpl(check(Z3.fixedpoint_get_statistics(contextPtr, this.ptr)));
      }

      release() {
        Z3.fixedpoint_dec_ref(contextPtr, this.ptr);
        this._ptr = null;
        cleanup.unregister(this);
      }
    }

    class ModelImpl implements Model<Name> {
      declare readonly __typename: Model['__typename'];
      readonly ctx: Context<Name>;
      private _ptr: Z3_model | null;
      get ptr(): Z3_model {
        _assertPtr(this._ptr);
        return this._ptr;
      }

      constructor(ptr: Z3_model = Z3.mk_model(contextPtr)) {
        this.ctx = ctx;
        this._ptr = ptr;
        Z3.model_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.model_dec_ref(contextPtr, ptr), this);
      }

      length() {
        return Z3.model_get_num_consts(contextPtr, this.ptr) + Z3.model_get_num_funcs(contextPtr, this.ptr);
      }

      [Symbol.iterator](): Iterator<FuncDecl<Name>> {
        return this.values();
      }

      *entries(): IterableIterator<[number, FuncDecl<Name>]> {
        const length = this.length();
        for (let i = 0; i < length; i++) {
          yield [i, this.get(i)];
        }
      }

      *keys(): IterableIterator<number> {
        for (const [key] of this.entries()) {
          yield key;
        }
      }

      *values(): IterableIterator<FuncDecl<Name>> {
        for (const [, value] of this.entries()) {
          yield value;
        }
      }

      decls() {
        return [...this.values()];
      }

      sexpr() {
        return check(Z3.model_to_string(contextPtr, this.ptr));
      }

      toString() {
        return this.sexpr();
      }

      eval(expr: Bool<Name>, modelCompletion?: boolean): Bool<Name>;
      eval(expr: Arith<Name>, modelCompletion?: boolean): Arith<Name>;
      eval<Bits extends number = number>(expr: BitVec<Bits, Name>, modelCompletion?: boolean): BitVecNum<Bits, Name>;
      eval(expr: Expr<Name>, modelCompletion: boolean = false) {
        _assertContext(expr);
        const r = check(Z3.model_eval(contextPtr, this.ptr, expr.ast, modelCompletion));
        if (r === null) {
          throw new Z3Error('Failed to evaluate expression in the model');
        }
        return _toExpr(r);
      }

      get(i: number): FuncDecl<Name>;
      get(from: number, to: number): FuncDecl<Name>[];
      get(declaration: FuncDecl<Name>): FuncInterp<Name> | Expr<Name>;
      get(constant: Expr<Name>): Expr<Name>;
      get(sort: Sort<Name>): AstVector<Name, AnyExpr<Name>>;
      get(
        i: number | FuncDecl<Name> | Expr<Name> | Sort<Name>,
        to?: number,
      ): FuncDecl<Name> | FuncInterp<Name> | Expr<Name> | AstVector<Name, AnyAst<Name>> | FuncDecl<Name>[] {
        assert(to === undefined || typeof i === 'number');
        if (typeof i === 'number') {
          const length = this.length();

          if (i >= length) {
            throw new RangeError(`expected index ${i} to be less than length ${length}`);
          }

          if (to === undefined) {
            const numConsts = check(Z3.model_get_num_consts(contextPtr, this.ptr));
            if (i < numConsts) {
              return new FuncDeclImpl(check(Z3.model_get_const_decl(contextPtr, this.ptr, i)));
            } else {
              return new FuncDeclImpl(check(Z3.model_get_func_decl(contextPtr, this.ptr, i - numConsts)));
            }
          }

          if (to < 0) {
            to += length;
          }
          if (to >= length) {
            throw new RangeError(`expected index ${to} to be less than length ${length}`);
          }
          const result = [];
          for (let j = i; j < to; j++) {
            result.push(this.get(j));
          }
          return result;
        } else if (isFuncDecl(i) || (isExpr(i) && isConst(i))) {
          const result = this.getInterp(i);
          assert(result !== null);
          return result;
        } else if (isSort(i)) {
          return this.getUniverse(i);
        }
        assert(false, 'Number, declaration or constant expected');
      }

      updateValue(decl: FuncDecl<Name> | Expr<Name>, a: Ast<Name> | FuncInterp<Name>): void {
        _assertContext(decl);
        _assertContext(a);
        if (isExpr(decl)) {
          decl = decl.decl();
        }
        if (isFuncDecl(decl) && decl.arity() !== 0 && isFuncInterp(a)) {
          const funcInterp = this.addFuncInterp(decl, a.elseValue() as Expr<Name>);
          for (let i = 0; i < a.numEntries(); i++) {
            const e = a.entry(i);
            const n = e.numArgs();
            const args = global.Array(n).map((_, i) => e.argValue(i));
            funcInterp.addEntry(args, e.value());
          }
          return;
        }
        if (!isFuncDecl(decl) || decl.arity() !== 0) {
          throw new Z3Error('Expecting 0-ary function or constant expression');
        }
        if (!isAst(a)) {
          throw new Z3Error('Only func declarations can be assigned to func interpretations');
        }
        check(Z3.add_const_interp(contextPtr, this.ptr, decl.ptr, a.ast));
      }

      addFuncInterp<DomainSort extends Sort<Name>[] = Sort<Name>[], RangeSort extends Sort<Name> = Sort<Name>>(
        decl: FuncDecl<Name, DomainSort, RangeSort>,
        defaultValue: CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
      ): FuncInterp<Name> {
        const fi = check(
          Z3.add_func_interp(contextPtr, this.ptr, decl.ptr, decl.range().cast(defaultValue).ptr as Z3_ast),
        );
        return new FuncInterpImpl(fi);
      }

      private getInterp(expr: FuncDecl<Name> | Expr<Name>): Expr<Name> | FuncInterp<Name> | null {
        assert(isFuncDecl(expr) || isConst(expr), 'Declaration expected');
        if (isConst(expr)) {
          assert(isExpr(expr));
          expr = expr.decl();
        }
        assert(isFuncDecl(expr));
        if (expr.arity() === 0) {
          const result = check(Z3.model_get_const_interp(contextPtr, this.ptr, expr.ptr));
          if (result === null) {
            return null;
          }
          return _toExpr(result);
        } else {
          const interp = check(Z3.model_get_func_interp(contextPtr, this.ptr, expr.ptr));
          if (interp === null) {
            return null;
          }
          return new FuncInterpImpl(interp);
        }
      }

      private getUniverse(sort: Sort<Name>): AstVector<Name, AnyAst<Name>> {
        _assertContext(sort);
        return new AstVectorImpl(check(Z3.model_get_sort_universe(contextPtr, this.ptr, sort.ptr)));
      }

      numSorts(): number {
        return check(Z3.model_get_num_sorts(contextPtr, this.ptr));
      }

      getSort(i: number): Sort<Name> {
        return _toSort(check(Z3.model_get_sort(contextPtr, this.ptr, i)));
      }

      getSorts(): Sort<Name>[] {
        const n = this.numSorts();
        const result: Sort<Name>[] = [];
        for (let i = 0; i < n; i++) {
          result.push(this.getSort(i));
        }
        return result;
      }

      sortUniverse(sort: Sort<Name>): AstVector<Name, AnyExpr<Name>> {
        return this.getUniverse(sort) as AstVector<Name, AnyExpr<Name>>;
      }

      release() {
        Z3.model_dec_ref(contextPtr, this.ptr);
        this._ptr = null;
        cleanup.unregister(this);
      }
    }

    class StatisticsImpl implements Statistics<Name> {
      declare readonly __typename: Statistics['__typename'];
      readonly ctx: Context<Name>;
      private _ptr: Z3_stats | null;
      get ptr(): Z3_stats {
        _assertPtr(this._ptr);
        return this._ptr;
      }

      constructor(ptr: Z3_stats) {
        this.ctx = ctx;
        this._ptr = ptr;
        Z3.stats_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.stats_dec_ref(contextPtr, ptr), this);
      }

      size(): number {
        return Z3.stats_size(contextPtr, this.ptr);
      }

      keys(): string[] {
        const result: string[] = [];
        const sz = this.size();
        for (let i = 0; i < sz; i++) {
          result.push(Z3.stats_get_key(contextPtr, this.ptr, i));
        }
        return result;
      }

      get(key: string): number {
        const sz = this.size();
        for (let i = 0; i < sz; i++) {
          if (Z3.stats_get_key(contextPtr, this.ptr, i) === key) {
            if (Z3.stats_is_uint(contextPtr, this.ptr, i)) {
              return Z3.stats_get_uint_value(contextPtr, this.ptr, i);
            } else {
              return Z3.stats_get_double_value(contextPtr, this.ptr, i);
            }
          }
        }
        throw new Error(`Statistics key not found: ${key}`);
      }

      entries(): StatisticsEntry<Name>[] {
        const result: StatisticsEntry<Name>[] = [];
        const sz = this.size();
        for (let i = 0; i < sz; i++) {
          const key = Z3.stats_get_key(contextPtr, this.ptr, i);
          const isUint = Z3.stats_is_uint(contextPtr, this.ptr, i);
          const isDouble = Z3.stats_is_double(contextPtr, this.ptr, i);
          const value = isUint
            ? Z3.stats_get_uint_value(contextPtr, this.ptr, i)
            : Z3.stats_get_double_value(contextPtr, this.ptr, i);
          result.push({
            __typename: 'StatisticsEntry' as const,
            key,
            value,
            isUint,
            isDouble,
          });
        }
        return result;
      }

      [Symbol.iterator](): Iterator<StatisticsEntry<Name>> {
        return this.entries()[Symbol.iterator]();
      }

      release() {
        Z3.stats_dec_ref(contextPtr, this.ptr);
        this._ptr = null;
        cleanup.unregister(this);
      }
    }

    class FuncEntryImpl implements FuncEntry<Name> {
      declare readonly __typename: FuncEntry['__typename'];

      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_func_entry) {
        this.ctx = ctx;
        Z3.func_entry_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.func_entry_dec_ref(contextPtr, ptr), this);
      }

      numArgs() {
        return check(Z3.func_entry_get_num_args(contextPtr, this.ptr));
      }

      argValue(i: number): Expr<Name> {
        return _toExpr(check(Z3.func_entry_get_arg(contextPtr, this.ptr, i)));
      }

      value(): Expr<Name> {
        return _toExpr(check(Z3.func_entry_get_value(contextPtr, this.ptr)));
      }
    }

    class FuncInterpImpl implements FuncInterp<Name> {
      declare readonly __typename: FuncInterp['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_func_interp) {
        this.ctx = ctx;
        Z3.func_interp_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.func_interp_dec_ref(contextPtr, ptr), this);
      }

      elseValue(): Expr<Name> {
        return _toExpr(check(Z3.func_interp_get_else(contextPtr, this.ptr)));
      }

      numEntries(): number {
        return check(Z3.func_interp_get_num_entries(contextPtr, this.ptr));
      }

      arity(): number {
        return check(Z3.func_interp_get_arity(contextPtr, this.ptr));
      }

      entry(i: number): FuncEntry<Name> {
        return new FuncEntryImpl(check(Z3.func_interp_get_entry(contextPtr, this.ptr, i)));
      }

      addEntry(args: Expr<Name>[], value: Expr<Name>): void {
        const argsVec = new AstVectorImpl();
        for (const arg of args) {
          argsVec.push(arg);
        }
        _assertContext(argsVec);
        _assertContext(value);
        assert(this.arity() === argsVec.length(), "Number of arguments in entry doesn't match function arity");
        check(Z3.func_interp_add_entry(contextPtr, this.ptr, argsVec.ptr, value.ptr as Z3_ast));
      }
    }

    class SortImpl extends AstImpl<Z3_sort> implements Sort<Name> {
      declare readonly __typename: Sort['__typename'];

      get ast(): Z3_ast {
        return Z3.sort_to_ast(contextPtr, this.ptr);
      }

      kind() {
        return Z3.get_sort_kind(contextPtr, this.ptr);
      }

      subsort(other: Sort<Name>) {
        _assertContext(other);
        return false;
      }

      cast(expr: Expr<Name>): Expr<Name> {
        _assertContext(expr);
        assert(expr.sort.eqIdentity(expr.sort), 'Sort mismatch');
        return expr;
      }

      name() {
        return _fromSymbol(Z3.get_sort_name(contextPtr, this.ptr));
      }

      eqIdentity(other: Sort<Name>) {
        _assertContext(other);
        return check(Z3.is_eq_sort(contextPtr, this.ptr, other.ptr));
      }

      neqIdentity(other: Sort<Name>) {
        return !this.eqIdentity(other);
      }
    }

    class FuncDeclImpl<DomainSort extends Sort<Name>[], RangeSort extends Sort<Name>>
      extends AstImpl<Z3_func_decl>
      implements FuncDecl<Name>
    {
      declare readonly __typename: FuncDecl['__typename'];

      get ast(): Z3_ast {
        return Z3.func_decl_to_ast(contextPtr, this.ptr);
      }

      name() {
        return _fromSymbol(Z3.get_decl_name(contextPtr, this.ptr));
      }

      arity() {
        return Z3.get_arity(contextPtr, this.ptr);
      }

      domain<T extends number>(i: T): DomainSort[T] {
        assert(i < this.arity(), 'Index out of bounds');
        return _toSort(Z3.get_domain(contextPtr, this.ptr, i));
      }

      range(): RangeSort {
        return _toSort(Z3.get_range(contextPtr, this.ptr)) as RangeSort;
      }

      kind() {
        return Z3.get_decl_kind(contextPtr, this.ptr);
      }

      params(): (number | string | Sort<Name> | Expr<Name> | FuncDecl<Name>)[] {
        const n = Z3.get_decl_num_parameters(contextPtr, this.ptr);
        const result = [];
        for (let i = 0; i < n; i++) {
          const kind = check(Z3.get_decl_parameter_kind(contextPtr, this.ptr, i));
          switch (kind) {
            case Z3_parameter_kind.Z3_PARAMETER_INT:
              result.push(check(Z3.get_decl_int_parameter(contextPtr, this.ptr, i)));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_DOUBLE:
              result.push(check(Z3.get_decl_double_parameter(contextPtr, this.ptr, i)));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_RATIONAL:
              result.push(check(Z3.get_decl_rational_parameter(contextPtr, this.ptr, i)));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_SYMBOL:
              result.push(_fromSymbol(check(Z3.get_decl_symbol_parameter(contextPtr, this.ptr, i))));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_SORT:
              result.push(new SortImpl(check(Z3.get_decl_sort_parameter(contextPtr, this.ptr, i))));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_AST:
              result.push(new ExprImpl(check(Z3.get_decl_ast_parameter(contextPtr, this.ptr, i))));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
              result.push(new FuncDeclImpl(check(Z3.get_decl_func_decl_parameter(contextPtr, this.ptr, i))));
              break;
            case Z3_parameter_kind.Z3_PARAMETER_INTERNAL:
              break;
            case Z3_parameter_kind.Z3_PARAMETER_ZSTRING:
              break;
            default:
              assertExhaustive(kind);
          }
        }
        return result;
      }

      call(...args: CoercibleToArrayIndexType<Name, DomainSort>): SortToExprMap<RangeSort, Name> {
        assert(args.length === this.arity(), `Incorrect number of arguments to ${this}`);
        return _toExpr(
          check(
            Z3.mk_app(
              contextPtr,
              this.ptr,
              args.map((arg, i) => {
                return this.domain(i).cast(arg as any).ast;
              }),
            ),
          ),
        ) as SortToExprMap<RangeSort, Name>;
      }
    }

    class ExprImpl<Ptr extends Z3_ast, S extends Sort<Name> = AnySort<Name>>
      extends AstImpl<Ptr>
      implements Expr<Name>
    {
      declare readonly __typename: Expr['__typename'];

      get sort(): S {
        return _toSort(Z3.get_sort(contextPtr, this.ast)) as S;
      }

      eq(other: CoercibleToExpr<Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_eq(contextPtr, this.ast, from(other).ast)));
      }

      neq(other: CoercibleToExpr<Name>): Bool<Name> {
        return new BoolImpl(
          check(
            Z3.mk_distinct(
              contextPtr,
              [this, other].map(expr => from(expr).ast),
            ),
          ),
        );
      }

      name() {
        return this.decl().name();
      }

      params() {
        return this.decl().params();
      }

      decl(): FuncDecl<Name> {
        assert(isApp(this), 'Z3 application expected');
        return new FuncDeclImpl(check(Z3.get_app_decl(contextPtr, check(Z3.to_app(contextPtr, this.ast)))));
      }

      numArgs(): number {
        assert(isApp(this), 'Z3 applicaiton expected');
        return check(Z3.get_app_num_args(contextPtr, check(Z3.to_app(contextPtr, this.ast))));
      }

      arg(i: number): ReturnType<typeof _toExpr> {
        assert(isApp(this), 'Z3 applicaiton expected');
        assert(i < this.numArgs(), `Invalid argument index - expected ${i} to be less than ${this.numArgs()}`);
        return _toExpr(check(Z3.get_app_arg(contextPtr, check(Z3.to_app(contextPtr, this.ast)), i)));
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

    class PatternImpl implements Pattern<Name> {
      declare readonly __typename: Pattern['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_pattern) {
        this.ctx = ctx;
        // TODO: implement rest of Pattern
      }
    }

    class BoolSortImpl extends SortImpl implements BoolSort<Name> {
      declare readonly __typename: BoolSort['__typename'];

      cast(other: Bool<Name> | boolean): Bool<Name>;
      cast(other: CoercibleToExpr<Name>): never;
      cast(other: CoercibleToExpr<Name> | Bool<Name>) {
        if (typeof other === 'boolean') {
          other = Bool.val(other);
        }
        assert(isExpr(other), 'true, false or Z3 Boolean expression expected.');
        assert(this.eqIdentity(other.sort), 'Value cannot be converted into a Z3 Boolean value');
        return other;
      }

      subsort(other: Sort<Name>) {
        _assertContext(other.ctx);
        return other instanceof ArithSortImpl;
      }
    }

    class BoolImpl extends ExprImpl<Z3_ast, BoolSort<Name>> implements Bool<Name> {
      declare readonly __typename: 'Bool' | 'NonLambdaQuantifier';

      not(): Bool<Name> {
        return Not(this);
      }

      and(other: Bool<Name> | boolean): Bool<Name> {
        return And(this, other);
      }

      or(other: Bool<Name> | boolean): Bool<Name> {
        return Or(this, other);
      }

      xor(other: Bool<Name> | boolean): Bool<Name> {
        return Xor(this, other);
      }

      implies(other: Bool<Name> | boolean): Bool<Name> {
        return Implies(this, other);
      }

      iff(other: Bool<Name> | boolean): Bool<Name> {
        return Iff(this, other);
      }
    }

    class ProbeImpl implements Probe<Name> {
      declare readonly __typename: Probe['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_probe) {
        this.ctx = ctx;
      }

      apply(goal: Goal<Name>): number {
        _assertContext(goal);
        return Z3.probe_apply(contextPtr, this.ptr, goal.ptr);
      }
    }

    class GoalImpl implements Goal<Name> {
      declare readonly __typename: Goal['__typename'];
      readonly ctx: Context<Name>;
      readonly ptr: Z3_goal;

      constructor(models: boolean = true, unsat_cores: boolean = false, proofs: boolean = false) {
        this.ctx = ctx;
        const myPtr = check(Z3.mk_goal(contextPtr, models, unsat_cores, proofs));
        this.ptr = myPtr;
        Z3.goal_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.goal_dec_ref(contextPtr, myPtr), this);
      }

      // Factory method for creating from existing Z3_goal pointer
      static fromPtr(goalPtr: Z3_goal): GoalImpl {
        const goal = Object.create(GoalImpl.prototype) as GoalImpl;
        (goal as any).ctx = ctx;
        (goal as any).ptr = goalPtr;
        Z3.goal_inc_ref(contextPtr, goalPtr);
        cleanup.register(goal, () => Z3.goal_dec_ref(contextPtr, goalPtr), goal);
        return goal;
      }

      add(...constraints: (Bool<Name> | boolean)[]): void {
        for (const constraint of constraints) {
          const boolConstraint = isBool(constraint) ? constraint : Bool.val(constraint);
          _assertContext(boolConstraint);
          Z3.goal_assert(contextPtr, this.ptr, boolConstraint.ast);
        }
      }

      size(): number {
        return Z3.goal_size(contextPtr, this.ptr);
      }

      get(i: number): Bool<Name> {
        assert(i >= 0 && i < this.size(), 'Index out of bounds');
        const ast = check(Z3.goal_formula(contextPtr, this.ptr, i));
        return new BoolImpl(ast);
      }

      depth(): number {
        return Z3.goal_depth(contextPtr, this.ptr);
      }

      inconsistent(): boolean {
        return Z3.goal_inconsistent(contextPtr, this.ptr);
      }

      precision(): Z3_goal_prec {
        return Z3.goal_precision(contextPtr, this.ptr);
      }

      reset(): void {
        Z3.goal_reset(contextPtr, this.ptr);
      }

      numExprs(): number {
        return Z3.goal_num_exprs(contextPtr, this.ptr);
      }

      isDecidedSat(): boolean {
        return Z3.goal_is_decided_sat(contextPtr, this.ptr);
      }

      isDecidedUnsat(): boolean {
        return Z3.goal_is_decided_unsat(contextPtr, this.ptr);
      }

      convertModel(model: Model<Name>): Model<Name> {
        _assertContext(model);
        const convertedModel = check(Z3.goal_convert_model(contextPtr, this.ptr, model.ptr));
        return new ModelImpl(convertedModel);
      }

      asExpr(): Bool<Name> {
        const sz = this.size();
        if (sz === 0) {
          return Bool.val(true);
        } else if (sz === 1) {
          return this.get(0);
        } else {
          const constraints: Bool<Name>[] = [];
          for (let i = 0; i < sz; i++) {
            constraints.push(this.get(i));
          }
          return And(...constraints);
        }
      }

      toString(): string {
        return Z3.goal_to_string(contextPtr, this.ptr);
      }

      dimacs(includeNames: boolean = true): string {
        return Z3.goal_to_dimacs_string(contextPtr, this.ptr, includeNames);
      }
    }

    class ApplyResultImpl implements ApplyResult<Name> {
      declare readonly __typename: ApplyResult['__typename'];
      readonly ctx: Context<Name>;
      readonly ptr: Z3_apply_result;

      constructor(ptr: Z3_apply_result) {
        this.ctx = ctx;
        this.ptr = ptr;
        Z3.apply_result_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.apply_result_dec_ref(contextPtr, ptr), this);
      }

      length(): number {
        return Z3.apply_result_get_num_subgoals(contextPtr, this.ptr);
      }

      getSubgoal(i: number): Goal<Name> {
        assert(i >= 0 && i < this.length(), 'Index out of bounds');
        const goalPtr = check(Z3.apply_result_get_subgoal(contextPtr, this.ptr, i));
        return GoalImpl.fromPtr(goalPtr);
      }

      toString(): string {
        return Z3.apply_result_to_string(contextPtr, this.ptr);
      }

      [index: number]: Goal<Name>;
    }

    // Add indexer support to ApplyResultImpl
    const applyResultHandler = {
      get(target: ApplyResultImpl, prop: string | symbol): any {
        if (typeof prop === 'string') {
          const index = parseInt(prop, 10);
          if (!isNaN(index) && index >= 0 && index < target.length()) {
            return target.getSubgoal(index);
          }
        }
        return (target as any)[prop];
      },
    };

    class TacticImpl implements Tactic<Name> {
      declare readonly __typename: Tactic['__typename'];

      readonly ptr: Z3_tactic;
      readonly ctx: Context<Name>;

      constructor(tactic: string | Z3_tactic) {
        this.ctx = ctx;
        let myPtr: Z3_tactic;
        if (typeof tactic === 'string') {
          myPtr = check(Z3.mk_tactic(contextPtr, tactic));
        } else {
          myPtr = tactic;
        }

        this.ptr = myPtr;

        Z3.tactic_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.tactic_dec_ref(contextPtr, myPtr), this);
      }

      async apply(goal: Goal<Name> | Bool<Name>): Promise<ApplyResult<Name>> {
        let goalToUse: Goal<Name>;

        if (isBool(goal)) {
          // Convert Bool expression to Goal
          goalToUse = new GoalImpl();
          goalToUse.add(goal);
        } else {
          goalToUse = goal;
        }

        _assertContext(goalToUse);
        const result = await Z3.tactic_apply(contextPtr, this.ptr, goalToUse.ptr);
        const applyResult = new ApplyResultImpl(check(result));
        // Wrap with Proxy to enable indexer access
        return new Proxy(applyResult, applyResultHandler) as ApplyResult<Name>;
      }

      solver(): Solver<Name> {
        const solverPtr = check(Z3.mk_solver_from_tactic(contextPtr, this.ptr));
        return new SolverImpl(solverPtr);
      }

      help(): string {
        return Z3.tactic_get_help(contextPtr, this.ptr);
      }

      paramDescrs(): ParamDescrs<Name> {
        const descrs = check(Z3.tactic_get_param_descrs(contextPtr, this.ptr));
        return new ParamDescrsImpl(descrs);
      }

      usingParams(params: Params<Name>): Tactic<Name> {
        _assertContext(params);
        const newTactic = check(Z3.tactic_using_params(contextPtr, this.ptr, params.ptr));
        return new TacticImpl(newTactic);
      }
    }

    class ParamsImpl implements Params<Name> {
      declare readonly __typename: Params['__typename'];

      readonly ptr: Z3_params;
      readonly ctx: Context<Name>;

      constructor(params?: Z3_params) {
        this.ctx = ctx;
        if (params) {
          this.ptr = params;
        } else {
          this.ptr = Z3.mk_params(contextPtr);
        }
        Z3.params_inc_ref(contextPtr, this.ptr);
        cleanup.register(this, () => Z3.params_dec_ref(contextPtr, this.ptr), this);
      }

      set(name: string, value: boolean | number | string): void {
        const sym = _toSymbol(name);
        if (typeof value === 'boolean') {
          Z3.params_set_bool(contextPtr, this.ptr, sym, value);
        } else if (typeof value === 'number') {
          if (Number.isInteger(value)) {
            check(Z3.params_set_uint(contextPtr, this.ptr, sym, value));
          } else {
            check(Z3.params_set_double(contextPtr, this.ptr, sym, value));
          }
        } else if (typeof value === 'string') {
          check(Z3.params_set_symbol(contextPtr, this.ptr, sym, _toSymbol(value)));
        }
      }

      validate(descrs: ParamDescrs<Name>): void {
        _assertContext(descrs);
        Z3.params_validate(contextPtr, this.ptr, descrs.ptr);
      }

      toString(): string {
        return Z3.params_to_string(contextPtr, this.ptr);
      }
    }

    class ParamDescrsImpl implements ParamDescrs<Name> {
      declare readonly __typename: ParamDescrs['__typename'];

      readonly ptr: Z3_param_descrs;
      readonly ctx: Context<Name>;

      constructor(paramDescrs: Z3_param_descrs) {
        this.ctx = ctx;
        this.ptr = paramDescrs;
        Z3.param_descrs_inc_ref(contextPtr, this.ptr);
        cleanup.register(this, () => Z3.param_descrs_dec_ref(contextPtr, this.ptr), this);
      }

      size(): number {
        return Z3.param_descrs_size(contextPtr, this.ptr);
      }

      getName(i: number): string {
        const sym = Z3.param_descrs_get_name(contextPtr, this.ptr, i);
        const name = _fromSymbol(sym);
        return typeof name === 'string' ? name : `${name}`;
      }

      getKind(name: string): number {
        return Z3.param_descrs_get_kind(contextPtr, this.ptr, _toSymbol(name));
      }

      getDocumentation(name: string): string {
        return Z3.param_descrs_get_documentation(contextPtr, this.ptr, _toSymbol(name));
      }

      toString(): string {
        return Z3.param_descrs_to_string(contextPtr, this.ptr);
      }
    }

    class SimplifierImpl implements Simplifier<Name> {
      declare readonly __typename: Simplifier['__typename'];

      readonly ptr: Z3_simplifier;
      readonly ctx: Context<Name>;

      constructor(simplifier: string | Z3_simplifier) {
        this.ctx = ctx;
        let myPtr: Z3_simplifier;
        if (typeof simplifier === 'string') {
          myPtr = check(Z3.mk_simplifier(contextPtr, simplifier));
        } else {
          myPtr = simplifier;
        }

        this.ptr = myPtr;

        Z3.simplifier_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.simplifier_dec_ref(contextPtr, myPtr), this);
      }

      help(): string {
        return Z3.simplifier_get_help(contextPtr, this.ptr);
      }

      paramDescrs(): ParamDescrs<Name> {
        const descrs = check(Z3.simplifier_get_param_descrs(contextPtr, this.ptr));
        return new ParamDescrsImpl(descrs);
      }

      usingParams(params: Params<Name>): Simplifier<Name> {
        _assertContext(params);
        const newSimplifier = check(Z3.simplifier_using_params(contextPtr, this.ptr, params.ptr));
        return new SimplifierImpl(newSimplifier);
      }

      andThen(other: Simplifier<Name>): Simplifier<Name> {
        _assertContext(other);
        const newSimplifier = check(Z3.simplifier_and_then(contextPtr, this.ptr, other.ptr));
        return new SimplifierImpl(newSimplifier);
      }
    }

    class ArithSortImpl extends SortImpl implements ArithSort<Name> {
      declare readonly __typename: ArithSort['__typename'];

      cast(other: bigint | number | string): IntNum<Name> | RatNum<Name>;
      cast(other: CoercibleRational | RatNum<Name>): RatNum<Name>;
      cast(other: IntNum<Name>): IntNum<Name>;
      cast(other: Bool<Name> | Arith<Name>): Arith<Name>;
      cast(other: CoercibleToExpr<Name>): never;
      cast(other: CoercibleToExpr<Name> | string): Arith<Name> | RatNum<Name> | IntNum<Name> {
        const sortTypeStr = isIntSort(this) ? 'IntSort' : 'RealSort';
        if (isExpr(other)) {
          const otherS = other.sort;
          if (isArith(other)) {
            if (this.eqIdentity(otherS)) {
              return other;
            } else if (isIntSort(otherS) && isRealSort(this)) {
              return ToReal(other);
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

    function Sum(arg0: Arith<Name>, ...args: CoercibleToArith<Name>[]): Arith<Name>;
    function Sum<Bits extends number>(
      arg0: BitVec<Bits, Name>,
      ...args: CoercibleToBitVec<Bits, Name>[]
    ): BitVec<Bits, Name>;
    function Sum<T extends Expr<Name>>(arg0: T, ...args: CoercibleToMap<T, Name>[]): T {
      if (arg0 instanceof BitVecImpl) {
        // Assert only 2
        if (args.length !== 1) {
          throw new Error('BitVec add only supports 2 arguments');
        }
        return new BitVecImpl<number>(
          check(Z3.mk_bvadd(contextPtr, arg0.ast, arg0.sort.cast(args[0]).ast)),
        ) as unknown as T;
      } else {
        assert(arg0 instanceof ArithImpl);
        return new ArithImpl(
          check(Z3.mk_add(contextPtr, [arg0.ast].concat(args.map(arg => arg0.sort.cast(arg).ast)))),
        ) as unknown as T;
      }
    }

    function Sub(arg0: Arith<Name>, ...args: CoercibleToArith<Name>[]): Arith<Name>;
    function Sub<Bits extends number>(
      arg0: BitVec<Bits, Name>,
      ...args: CoercibleToBitVec<Bits, Name>[]
    ): BitVec<Bits, Name>;
    function Sub<T extends Expr<Name>>(arg0: T, ...args: CoercibleToMap<T, Name>[]): T {
      if (arg0 instanceof BitVecImpl) {
        // Assert only 2
        if (args.length !== 1) {
          throw new Error('BitVec sub only supports 2 arguments');
        }
        return new BitVecImpl<number>(
          check(Z3.mk_bvsub(contextPtr, arg0.ast, arg0.sort.cast(args[0]).ast)),
        ) as unknown as T;
      } else {
        assert(arg0 instanceof ArithImpl);
        return new ArithImpl(
          check(Z3.mk_sub(contextPtr, [arg0.ast].concat(args.map(arg => arg0.sort.cast(arg).ast)))),
        ) as unknown as T;
      }
    }

    function Product(arg0: Arith<Name>, ...args: CoercibleToArith<Name>[]): Arith<Name>;
    function Product<Bits extends number>(
      arg0: BitVec<Bits, Name>,
      ...args: CoercibleToBitVec<Bits, Name>[]
    ): BitVec<Bits, Name>;
    function Product<T extends Expr<Name>>(arg0: T, ...args: CoercibleToMap<T, Name>[]): T {
      if (arg0 instanceof BitVecImpl) {
        // Assert only 2
        if (args.length !== 1) {
          throw new Error('BitVec mul only supports 2 arguments');
        }
        return new BitVecImpl<number>(
          check(Z3.mk_bvmul(contextPtr, arg0.ast, arg0.sort.cast(args[0]).ast)),
        ) as unknown as T;
      } else {
        assert(arg0 instanceof ArithImpl);
        return new ArithImpl(
          check(Z3.mk_mul(contextPtr, [arg0.ast].concat(args.map(arg => arg0.sort.cast(arg).ast)))),
        ) as unknown as T;
      }
    }

    function Div(arg0: Arith<Name>, arg1: CoercibleToArith<Name>): Arith<Name>;
    function Div<Bits extends number>(
      arg0: BitVec<Bits, Name>,
      arg1: CoercibleToBitVec<Bits, Name>,
    ): BitVec<Bits, Name>;
    function Div<T extends Expr<Name>>(arg0: T, arg1: CoercibleToMap<T, Name>): T {
      if (arg0 instanceof BitVecImpl) {
        return new BitVecImpl<number>(
          check(Z3.mk_bvsdiv(contextPtr, arg0.ast, arg0.sort.cast(arg1).ast)),
        ) as unknown as T;
      } else {
        assert(arg0 instanceof ArithImpl);
        return new ArithImpl(check(Z3.mk_div(contextPtr, arg0.ast, arg0.sort.cast(arg1).ast))) as unknown as T;
      }
    }

    function BUDiv<Bits extends number>(
      arg0: BitVec<Bits, Name>,
      arg1: CoercibleToBitVec<Bits, Name>,
    ): BitVec<Bits, Name> {
      return new BitVecImpl<number>(
        check(Z3.mk_bvudiv(contextPtr, arg0.ast, arg0.sort.cast(arg1).ast)),
      ) as unknown as BitVec<Bits, Name>;
    }

    function Neg(a: Arith<Name>): Arith<Name>;
    function Neg<Bits extends number>(a: BitVec<Bits, Name>): BitVec<Bits, Name>;
    function Neg<T extends Expr<Name>>(a: T): T {
      if (a instanceof BitVecImpl) {
        return new BitVecImpl<number>(check(Z3.mk_bvneg(contextPtr, a.ast))) as unknown as T;
      } else {
        assert(a instanceof ArithImpl);
        return new ArithImpl(check(Z3.mk_unary_minus(contextPtr, a.ast))) as unknown as T;
      }
    }

    function Mod(a: Arith<Name>, b: CoercibleToArith<Name>): Arith<Name>;
    function Mod<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;
    function Mod<T extends Expr<Name>>(a: T, b: CoercibleToMap<T, Name>): T {
      if (a instanceof BitVecImpl) {
        return new BitVecImpl<number>(check(Z3.mk_bvsrem(contextPtr, a.ast, a.sort.cast(b).ast))) as unknown as T;
      } else {
        assert(a instanceof ArithImpl);
        return new ArithImpl(check(Z3.mk_mod(contextPtr, a.ast, a.sort.cast(b).ast))) as unknown as T;
      }
    }

    class ArithImpl extends ExprImpl<Z3_ast, ArithSort<Name>> implements Arith<Name> {
      declare readonly __typename: Arith['__typename'];

      add(other: CoercibleToArith<Name>) {
        return Sum(this, other);
      }

      mul(other: CoercibleToArith<Name>) {
        return Product(this, other);
      }

      sub(other: CoercibleToArith<Name>) {
        return Sub(this, other);
      }

      pow(exponent: CoercibleToArith<Name>) {
        return new ArithImpl(check(Z3.mk_power(contextPtr, this.ast, this.sort.cast(exponent).ast)));
      }

      div(other: CoercibleToArith<Name>) {
        return Div(this, other);
      }

      mod(other: CoercibleToArith<Name>) {
        return Mod(this, other);
      }

      neg() {
        return Neg(this);
      }

      le(other: CoercibleToArith<Name>) {
        return LE(this, other);
      }

      lt(other: CoercibleToArith<Name>) {
        return LT(this, other);
      }

      gt(other: CoercibleToArith<Name>) {
        return GT(this, other);
      }

      ge(other: CoercibleToArith<Name>) {
        return GE(this, other);
      }
    }

    class IntNumImpl extends ArithImpl implements IntNum<Name> {
      declare readonly __typename: IntNum['__typename'];

      value() {
        return BigInt(this.asString());
      }

      asString() {
        return Z3.get_numeral_string(contextPtr, this.ast);
      }

      asBinary() {
        return Z3.get_numeral_binary_string(contextPtr, this.ast);
      }
    }

    class RatNumImpl extends ArithImpl implements RatNum<Name> {
      declare readonly __typename: RatNum['__typename'];

      value() {
        return { numerator: this.numerator().value(), denominator: this.denominator().value() };
      }

      numerator() {
        return new IntNumImpl(Z3.get_numerator(contextPtr, this.ast));
      }

      denominator() {
        return new IntNumImpl(Z3.get_denominator(contextPtr, this.ast));
      }

      asNumber() {
        const { numerator, denominator } = this.value();
        const div = numerator / denominator;
        return Number(div) + Number(numerator - div * denominator) / Number(denominator);
      }

      asDecimal(prec: number = Number.parseInt(getParam('precision') ?? FALLBACK_PRECISION.toString())) {
        return Z3.get_numeral_decimal_string(contextPtr, this.ast, prec);
      }

      asString() {
        return Z3.get_numeral_string(contextPtr, this.ast);
      }
    }

    class RCFNumImpl implements RCFNum<Name> {
      declare readonly __typename: RCFNum['__typename'];
      readonly ctx: Context<Name>;
      readonly ptr: Z3_rcf_num;

      constructor(value: string | number);
      constructor(ptr: Z3_rcf_num);
      constructor(valueOrPtr: string | number | Z3_rcf_num) {
        this.ctx = ctx;
        let myPtr: Z3_rcf_num;
        if (typeof valueOrPtr === 'string') {
          myPtr = check(Z3.rcf_mk_rational(contextPtr, valueOrPtr));
        } else if (typeof valueOrPtr === 'number') {
          myPtr = check(Z3.rcf_mk_small_int(contextPtr, valueOrPtr));
        } else {
          myPtr = valueOrPtr;
        }
        this.ptr = myPtr;
        cleanup.register(this, () => Z3.rcf_del(contextPtr, myPtr), this);
      }

      add(other: RCFNum<Name>): RCFNum<Name> {
        _assertContext(other);
        return new RCFNumImpl(check(Z3.rcf_add(contextPtr, this.ptr, (other as RCFNumImpl).ptr)));
      }

      sub(other: RCFNum<Name>): RCFNum<Name> {
        _assertContext(other);
        return new RCFNumImpl(check(Z3.rcf_sub(contextPtr, this.ptr, (other as RCFNumImpl).ptr)));
      }

      mul(other: RCFNum<Name>): RCFNum<Name> {
        _assertContext(other);
        return new RCFNumImpl(check(Z3.rcf_mul(contextPtr, this.ptr, (other as RCFNumImpl).ptr)));
      }

      div(other: RCFNum<Name>): RCFNum<Name> {
        _assertContext(other);
        return new RCFNumImpl(check(Z3.rcf_div(contextPtr, this.ptr, (other as RCFNumImpl).ptr)));
      }

      neg(): RCFNum<Name> {
        return new RCFNumImpl(check(Z3.rcf_neg(contextPtr, this.ptr)));
      }

      inv(): RCFNum<Name> {
        return new RCFNumImpl(check(Z3.rcf_inv(contextPtr, this.ptr)));
      }

      power(k: number): RCFNum<Name> {
        return new RCFNumImpl(check(Z3.rcf_power(contextPtr, this.ptr, k)));
      }

      lt(other: RCFNum<Name>): boolean {
        _assertContext(other);
        return check(Z3.rcf_lt(contextPtr, this.ptr, (other as RCFNumImpl).ptr));
      }

      gt(other: RCFNum<Name>): boolean {
        _assertContext(other);
        return check(Z3.rcf_gt(contextPtr, this.ptr, (other as RCFNumImpl).ptr));
      }

      le(other: RCFNum<Name>): boolean {
        _assertContext(other);
        return check(Z3.rcf_le(contextPtr, this.ptr, (other as RCFNumImpl).ptr));
      }

      ge(other: RCFNum<Name>): boolean {
        _assertContext(other);
        return check(Z3.rcf_ge(contextPtr, this.ptr, (other as RCFNumImpl).ptr));
      }

      eq(other: RCFNum<Name>): boolean {
        _assertContext(other);
        return check(Z3.rcf_eq(contextPtr, this.ptr, (other as RCFNumImpl).ptr));
      }

      neq(other: RCFNum<Name>): boolean {
        _assertContext(other);
        return check(Z3.rcf_neq(contextPtr, this.ptr, (other as RCFNumImpl).ptr));
      }

      isRational(): boolean {
        return check(Z3.rcf_is_rational(contextPtr, this.ptr));
      }

      isAlgebraic(): boolean {
        return check(Z3.rcf_is_algebraic(contextPtr, this.ptr));
      }

      isInfinitesimal(): boolean {
        return check(Z3.rcf_is_infinitesimal(contextPtr, this.ptr));
      }

      isTranscendental(): boolean {
        return check(Z3.rcf_is_transcendental(contextPtr, this.ptr));
      }

      toString(compact: boolean = false): string {
        return check(Z3.rcf_num_to_string(contextPtr, this.ptr, compact, false));
      }

      toDecimal(precision: number): string {
        return check(Z3.rcf_num_to_decimal_string(contextPtr, this.ptr, precision));
      }
    }

    class BitVecSortImpl<Bits extends number> extends SortImpl implements BitVecSort<Bits, Name> {
      declare readonly __typename: BitVecSort['__typename'];

      size() {
        return Z3.get_bv_sort_size(contextPtr, this.ptr) as Bits;
      }

      subsort(other: Sort<Name>): boolean {
        return isBitVecSort(other) && this.size() < other.size();
      }

      cast(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;
      cast(other: CoercibleToExpr<Name>): Expr<Name>;
      cast(other: CoercibleToExpr<Name>): Expr<Name> {
        if (isExpr(other)) {
          _assertContext(other);
          return other;
        }
        assert(!isCoercibleRational(other), "Can't convert rational to BitVec");
        return BitVec.val(other, this.size());
      }
    }

    class BitVecImpl<Bits extends number> extends ExprImpl<Z3_ast, BitVecSortImpl<Bits>> implements BitVec<Bits, Name> {
      declare readonly __typename: BitVec['__typename'];

      size() {
        return this.sort.size();
      }

      add(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return Sum(this, other);
      }

      mul(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return Product(this, other);
      }

      sub(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return Sub(this, other);
      }

      sdiv(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return Div(this, other);
      }

      udiv(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return BUDiv(this, other);
      }

      smod(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return Mod(this, other);
      }

      urem(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvurem(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      srem(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvsrem(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      neg(): BitVec<Bits, Name> {
        return Neg(this);
      }

      or(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvor(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      and(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvand(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      nand(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvnand(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      xor(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvxor(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      xnor(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvxnor(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      shr(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvashr(contextPtr, this.ast, this.sort.cast(count).ast)));
      }

      lshr(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvlshr(contextPtr, this.ast, this.sort.cast(count).ast)));
      }

      shl(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvshl(contextPtr, this.ast, this.sort.cast(count).ast)));
      }

      rotateRight(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_ext_rotate_right(contextPtr, this.ast, this.sort.cast(count).ast)));
      }

      rotateLeft(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_ext_rotate_left(contextPtr, this.ast, this.sort.cast(count).ast)));
      }

      not(): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvnot(contextPtr, this.ast)));
      }

      extract(high: number, low: number): BitVec<number, Name> {
        return Extract(high, low, this);
      }

      signExt(count: number): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_sign_ext(contextPtr, count, this.ast)));
      }

      zeroExt(count: number): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_zero_ext(contextPtr, count, this.ast)));
      }

      repeat(count: number): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_repeat(contextPtr, count, this.ast)));
      }

      sle(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return SLE(this, other);
      }

      ule(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return ULE(this, other);
      }

      slt(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return SLT(this, other);
      }

      ult(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return ULT(this, other);
      }

      sge(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return SGE(this, other);
      }

      uge(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return UGE(this, other);
      }

      sgt(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return SGT(this, other);
      }

      ugt(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return UGT(this, other);
      }

      redAnd(): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvredand(contextPtr, this.ast)));
      }

      redOr(): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvredor(contextPtr, this.ast)));
      }

      addNoOverflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvadd_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
      }

      addNoUnderflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvadd_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      subNoOverflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsub_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      subNoUnderflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsub_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
      }

      sdivNoOverflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsdiv_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      mulNoOverflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvmul_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
      }

      mulNoUnderflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvmul_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      negNoOverflow(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvneg_no_overflow(contextPtr, this.ast)));
      }
    }

    class BitVecNumImpl<Bits extends number> extends BitVecImpl<Bits> implements BitVecNum<Bits, Name> {
      declare readonly __typename: BitVecNum['__typename'];

      value() {
        return BigInt(this.asString());
      }

      asSignedValue() {
        let val = this.value();
        const size = BigInt(this.size());
        if (val >= 2n ** (size - 1n)) {
          val = val - 2n ** size;
        }
        if (val < (-2n) ** (size - 1n)) {
          val = val + 2n ** size;
        }
        return val;
      }

      asString() {
        return Z3.get_numeral_string(contextPtr, this.ast);
      }

      asBinaryString() {
        return Z3.get_numeral_binary_string(contextPtr, this.ast);
      }
    }

    class FPRMSortImpl extends SortImpl implements FPRMSort<Name> {
      declare readonly __typename: FPRMSort['__typename'];

      cast(other: FPRM<Name>): FPRM<Name>;
      cast(other: CoercibleToExpr<Name>): never;
      cast(other: any): any {
        if (isFPRM(other)) {
          _assertContext(other);
          return other;
        }
        throw new Error("Can't cast to FPRMSort");
      }
    }

    class FPRMImpl extends ExprImpl<Z3_ast, FPRMSortImpl> implements FPRM<Name> {
      declare readonly __typename: FPRM['__typename'];
    }

    class FPSortImpl extends SortImpl implements FPSort<Name> {
      declare readonly __typename: FPSort['__typename'];

      ebits() {
        return Z3.fpa_get_ebits(contextPtr, this.ptr);
      }

      sbits() {
        return Z3.fpa_get_sbits(contextPtr, this.ptr);
      }

      cast(other: CoercibleToFP<Name>): FP<Name>;
      cast(other: CoercibleToExpr<Name>): Expr<Name>;
      cast(other: CoercibleToExpr<Name>): Expr<Name> {
        if (isExpr(other)) {
          _assertContext(other);
          return other;
        }
        if (typeof other === 'number') {
          return Float.val(other, this);
        }
        throw new Error("Can't cast to FPSort");
      }
    }

    class FPImpl extends ExprImpl<Z3_ast, FPSortImpl> implements FP<Name> {
      declare readonly __typename: FP['__typename'];

      add(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new FPImpl(check(Z3.mk_fpa_add(contextPtr, rm.ast, this.ast, otherFP.ast)));
      }

      sub(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new FPImpl(check(Z3.mk_fpa_sub(contextPtr, rm.ast, this.ast, otherFP.ast)));
      }

      mul(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new FPImpl(check(Z3.mk_fpa_mul(contextPtr, rm.ast, this.ast, otherFP.ast)));
      }

      div(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new FPImpl(check(Z3.mk_fpa_div(contextPtr, rm.ast, this.ast, otherFP.ast)));
      }

      neg(): FP<Name> {
        return new FPImpl(check(Z3.mk_fpa_neg(contextPtr, this.ast)));
      }

      abs(): FP<Name> {
        return new FPImpl(check(Z3.mk_fpa_abs(contextPtr, this.ast)));
      }

      sqrt(rm: FPRM<Name>): FP<Name> {
        return new FPImpl(check(Z3.mk_fpa_sqrt(contextPtr, rm.ast, this.ast)));
      }

      rem(other: CoercibleToFP<Name>): FP<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new FPImpl(check(Z3.mk_fpa_rem(contextPtr, this.ast, otherFP.ast)));
      }

      fma(rm: FPRM<Name>, y: CoercibleToFP<Name>, z: CoercibleToFP<Name>): FP<Name> {
        const yFP = isFP(y) ? y : Float.val(y, this.sort);
        const zFP = isFP(z) ? z : Float.val(z, this.sort);
        return new FPImpl(check(Z3.mk_fpa_fma(contextPtr, rm.ast, this.ast, yFP.ast, zFP.ast)));
      }

      lt(other: CoercibleToFP<Name>): Bool<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new BoolImpl(check(Z3.mk_fpa_lt(contextPtr, this.ast, otherFP.ast)));
      }

      gt(other: CoercibleToFP<Name>): Bool<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new BoolImpl(check(Z3.mk_fpa_gt(contextPtr, this.ast, otherFP.ast)));
      }

      le(other: CoercibleToFP<Name>): Bool<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new BoolImpl(check(Z3.mk_fpa_leq(contextPtr, this.ast, otherFP.ast)));
      }

      ge(other: CoercibleToFP<Name>): Bool<Name> {
        const otherFP = isFP(other) ? other : Float.val(other, this.sort);
        return new BoolImpl(check(Z3.mk_fpa_geq(contextPtr, this.ast, otherFP.ast)));
      }

      isNaN(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_nan(contextPtr, this.ast)));
      }

      isInf(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_infinite(contextPtr, this.ast)));
      }

      isZero(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_zero(contextPtr, this.ast)));
      }

      isNormal(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_normal(contextPtr, this.ast)));
      }

      isSubnormal(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_subnormal(contextPtr, this.ast)));
      }

      isNegative(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_negative(contextPtr, this.ast)));
      }

      isPositive(): Bool<Name> {
        return new BoolImpl(check(Z3.mk_fpa_is_positive(contextPtr, this.ast)));
      }
    }

    class FPNumImpl extends FPImpl implements FPNum<Name> {
      declare readonly __typename: FPNum['__typename'];

      value(): number {
        // Get the floating-point numeral as a JavaScript number
        // Note: This may lose precision for values outside JavaScript number range
        return Z3.get_numeral_double(contextPtr, this.ast);
      }
    }

    class SeqSortImpl<ElemSort extends Sort<Name> = Sort<Name>> extends SortImpl implements SeqSort<Name, ElemSort> {
      declare readonly __typename: SeqSort['__typename'];

      isString(): boolean {
        return Z3.is_string_sort(contextPtr, this.ptr);
      }

      basis(): Sort<Name> {
        return _toSort(check(Z3.get_seq_sort_basis(contextPtr, this.ptr)));
      }

      cast(other: Seq<Name>): Seq<Name>;
      cast(other: string): Seq<Name>;
      cast(other: CoercibleToExpr<Name>): Expr<Name>;
      cast(other: any): any {
        if (isSeq(other)) {
          _assertContext(other);
          return other;
        }
        if (typeof other === 'string') {
          return String.val(other);
        }
        throw new Error("Can't cast to SeqSort");
      }
    }

    class SeqImpl<ElemSort extends Sort<Name> = Sort<Name>>
      extends ExprImpl<Z3_ast, SeqSortImpl<ElemSort>>
      implements Seq<Name, ElemSort>
    {
      declare readonly __typename: Seq['__typename'];

      isString(): boolean {
        return Z3.is_string_sort(contextPtr, Z3.get_sort(contextPtr, this.ast));
      }

      asString(): string {
        if (!Z3.is_string(contextPtr, this.ast)) {
          throw new Error('Not a string value');
        }
        return Z3.get_string(contextPtr, this.ast);
      }

      concat(other: Seq<Name, ElemSort> | string): Seq<Name, ElemSort> {
        const otherSeq = isSeq(other) ? other : String.val(other);
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_concat(contextPtr, [this.ast, otherSeq.ast])));
      }

      length(): Arith<Name> {
        return new ArithImpl(check(Z3.mk_seq_length(contextPtr, this.ast)));
      }

      at(index: Arith<Name> | number | bigint): Seq<Name, ElemSort> {
        const indexExpr = isArith(index) ? index : Int.val(index);
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_at(contextPtr, this.ast, indexExpr.ast)));
      }

      nth(index: Arith<Name> | number | bigint): Expr<Name> {
        const indexExpr = isArith(index) ? index : Int.val(index);
        return _toExpr(check(Z3.mk_seq_nth(contextPtr, this.ast, indexExpr.ast)));
      }

      extract(offset: Arith<Name> | number | bigint, length: Arith<Name> | number | bigint): Seq<Name, ElemSort> {
        const offsetExpr = isArith(offset) ? offset : Int.val(offset);
        const lengthExpr = isArith(length) ? length : Int.val(length);
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_extract(contextPtr, this.ast, offsetExpr.ast, lengthExpr.ast)));
      }

      indexOf(substr: Seq<Name, ElemSort> | string, offset?: Arith<Name> | number | bigint): Arith<Name> {
        const substrSeq = isSeq(substr) ? substr : String.val(substr);
        const offsetExpr = offset !== undefined ? (isArith(offset) ? offset : Int.val(offset)) : Int.val(0);
        return new ArithImpl(check(Z3.mk_seq_index(contextPtr, this.ast, substrSeq.ast, offsetExpr.ast)));
      }

      lastIndexOf(substr: Seq<Name, ElemSort> | string): Arith<Name> {
        const substrSeq = isSeq(substr) ? substr : String.val(substr);
        return new ArithImpl(check(Z3.mk_seq_last_index(contextPtr, this.ast, substrSeq.ast)));
      }

      contains(substr: Seq<Name, ElemSort> | string): Bool<Name> {
        const substrSeq = isSeq(substr) ? substr : String.val(substr);
        return new BoolImpl(check(Z3.mk_seq_contains(contextPtr, this.ast, substrSeq.ast)));
      }

      prefixOf(s: Seq<Name, ElemSort> | string): Bool<Name> {
        const sSeq = isSeq(s) ? s : String.val(s);
        return new BoolImpl(check(Z3.mk_seq_prefix(contextPtr, this.ast, sSeq.ast)));
      }

      suffixOf(s: Seq<Name, ElemSort> | string): Bool<Name> {
        const sSeq = isSeq(s) ? s : String.val(s);
        return new BoolImpl(check(Z3.mk_seq_suffix(contextPtr, this.ast, sSeq.ast)));
      }

      replace(src: Seq<Name, ElemSort> | string, dst: Seq<Name, ElemSort> | string): Seq<Name, ElemSort> {
        const srcSeq = isSeq(src) ? src : String.val(src);
        const dstSeq = isSeq(dst) ? dst : String.val(dst);
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_replace(contextPtr, this.ast, srcSeq.ast, dstSeq.ast)));
      }

      replaceAll(src: Seq<Name, ElemSort> | string, dst: Seq<Name, ElemSort> | string): Seq<Name, ElemSort> {
        const srcSeq = isSeq(src) ? src : String.val(src);
        const dstSeq = isSeq(dst) ? dst : String.val(dst);
        return new SeqImpl<ElemSort>(check(Z3.mk_seq_replace_all(contextPtr, this.ast, srcSeq.ast, dstSeq.ast)));
      }
    }

    class ReSortImpl<SeqSortRef extends SeqSort<Name> = SeqSort<Name>> extends SortImpl implements ReSort<Name, SeqSortRef> {
      declare readonly __typename: ReSort['__typename'];

      basis(): SeqSortRef {
        return _toSort(check(Z3.get_re_sort_basis(contextPtr, this.ptr))) as SeqSortRef;
      }

      cast(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;
      cast(other: CoercibleToExpr<Name>): Expr<Name>;
      cast(other: any): any {
        if (isRe(other)) {
          _assertContext(other);
          return other;
        }
        throw new Error("Can't cast to ReSort");
      }
    }

    class ReImpl<SeqSortRef extends SeqSort<Name> = SeqSort<Name>>
      extends ExprImpl<Z3_ast, ReSortImpl<SeqSortRef>>
      implements Re<Name, SeqSortRef>
    {
      declare readonly __typename: Re['__typename'];

      plus(): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_plus(contextPtr, this.ast)));
      }

      star(): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_star(contextPtr, this.ast)));
      }

      option(): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_option(contextPtr, this.ast)));
      }

      complement(): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_complement(contextPtr, this.ast)));
      }

      union(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_union(contextPtr, [this.ast, other.ast])));
      }

      intersect(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_intersect(contextPtr, [this.ast, other.ast])));
      }

      diff(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_diff(contextPtr, this.ast, other.ast)));
      }

      concat(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_concat(contextPtr, [this.ast, other.ast])));
      }

      /**
       * Create a bounded repetition of this regex
       * @param lo Minimum number of repetitions
       * @param hi Maximum number of repetitions (0 means unbounded, i.e., at least lo)
       */
      loop(lo: number, hi: number = 0): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_loop(contextPtr, this.ast, lo, hi)));
      }

      power(n: number): Re<Name, SeqSortRef> {
        return new ReImpl<SeqSortRef>(check(Z3.mk_re_power(contextPtr, this.ast, n)));
      }
    }

    class ArraySortImpl<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>
      extends SortImpl
      implements SMTArraySort<Name, DomainSort, RangeSort>
    {
      declare readonly __typename: SMTArraySort['__typename'];

      domain(): DomainSort[0] {
        return _toSort(check(Z3.get_array_sort_domain(contextPtr, this.ptr)));
      }

      domain_n<T extends number>(i: T): DomainSort[T] {
        return _toSort(check(Z3.get_array_sort_domain_n(contextPtr, this.ptr, i)));
      }

      range(): RangeSort {
        return _toSort(check(Z3.get_array_sort_range(contextPtr, this.ptr))) as RangeSort;
      }
    }

    class ArrayImpl<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>
      extends ExprImpl<Z3_ast, ArraySortImpl<DomainSort, RangeSort>>
      implements SMTArray<Name, DomainSort, RangeSort>
    {
      declare readonly __typename: 'Array' | 'Lambda';

      domain(): DomainSort[0] {
        return this.sort.domain();
      }

      domain_n<T extends number>(i: T): DomainSort[T] {
        return this.sort.domain_n(i);
      }

      range(): RangeSort {
        return this.sort.range();
      }

      select(...indices: CoercibleToArrayIndexType<Name, DomainSort>): SortToExprMap<RangeSort, Name> {
        return Select<DomainSort, RangeSort>(this, ...indices) as SortToExprMap<RangeSort, Name>;
      }

      store(
        ...indicesAndValue: [
          ...CoercibleToArrayIndexType<Name, DomainSort>,
          CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
        ]
      ): SMTArray<Name, DomainSort, RangeSort> {
        return Store(this, ...indicesAndValue);
      }

      /**
       * Access the array default value.
       * Produces the default range value, for arrays that can be represented as
       * finite maps with a default range value.
       */
      default(): SortToExprMap<RangeSort, Name> {
        return _toExpr(check(Z3.mk_array_default(contextPtr, this.ast))) as SortToExprMap<RangeSort, Name>;
      }
    }

    class SetImpl<ElemSort extends Sort<Name>>
      extends ExprImpl<Z3_ast, ArraySortImpl<[ElemSort], BoolSort<Name>>>
      implements SMTSet<Name, ElemSort>
    {
      declare readonly __typename: 'Array';

      elemSort(): ElemSort {
        return this.sort.domain();
      }
      union(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort> {
        return SetUnion(this, ...args);
      }
      intersect(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort> {
        return SetIntersect(this, ...args);
      }
      diff(b: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort> {
        return SetDifference(this, b);
      }
      add(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort> {
        return SetAdd(this, elem);
      }
      del(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort> {
        return SetDel(this, elem);
      }
      complement(): SMTSet<Name, ElemSort> {
        return SetComplement(this);
      }
      contains(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): Bool<Name> {
        return isMember(elem, this);
      }
      subsetOf(b: SMTSet<Name, ElemSort>): Bool<Name> {
        return isSubset(this, b);
      }
    }

    ////////////////////////////
    // Finite Sets
    ////////////////////////////

    class FiniteSetSortImpl<ElemSort extends Sort<Name> = Sort<Name>>
      extends SortImpl
      implements FiniteSetSort<Name, ElemSort>
    {
      declare readonly __typename: 'FiniteSetSort';

      elemSort(): ElemSort {
        return _toSort(check(Z3.get_finite_set_sort_basis(contextPtr, this.ptr))) as ElemSort;
      }

      cast(other: Expr<Name>): Expr<Name> {
        _assertContext(other);
        return other;
      }
    }

    class FiniteSetImpl<ElemSort extends Sort<Name> = Sort<Name>>
      extends ExprImpl<Z3_ast, FiniteSetSortImpl<ElemSort>>
      implements FiniteSet<Name, ElemSort>
    {
      declare readonly __typename: 'FiniteSet';

      union(other: FiniteSet<Name, ElemSort>): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(check(Z3.mk_finite_set_union(contextPtr, this.ast, other.ast)));
      }

      intersect(other: FiniteSet<Name, ElemSort>): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(check(Z3.mk_finite_set_intersect(contextPtr, this.ast, other.ast)));
      }

      diff(other: FiniteSet<Name, ElemSort>): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(check(Z3.mk_finite_set_difference(contextPtr, this.ast, other.ast)));
      }

      contains(elem: Expr<Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_finite_set_member(contextPtr, elem.ast, this.ast)));
      }

      size(): Expr<Name> {
        return new ExprImpl(check(Z3.mk_finite_set_size(contextPtr, this.ast)));
      }

      subsetOf(other: FiniteSet<Name, ElemSort>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_finite_set_subset(contextPtr, this.ast, other.ast)));
      }

      map(f: Expr<Name>): FiniteSet<Name, Sort<Name>> {
        return new FiniteSetImpl(check(Z3.mk_finite_set_map(contextPtr, f.ast, this.ast)));
      }

      filter(f: Expr<Name>): FiniteSet<Name, ElemSort> {
        return new FiniteSetImpl<ElemSort>(check(Z3.mk_finite_set_filter(contextPtr, f.ast, this.ast)));
      }
    }

    ////////////////////////////
    // Datatypes
    ////////////////////////////

    class DatatypeImpl implements Datatype<Name> {
      readonly ctx: Context<Name>;
      readonly name: string;
      public constructors: Array<[string, Array<[string, Sort<Name> | Datatype<Name>]>]> = [];

      constructor(ctx: Context<Name>, name: string) {
        this.ctx = ctx;
        this.name = name;
      }

      declare(name: string, ...fields: Array<[string, Sort<Name> | Datatype<Name>]>): this {
        this.constructors.push([name, fields]);
        return this;
      }

      create(): DatatypeSort<Name> {
        const datatypes = createDatatypes(this);
        return datatypes[0];
      }
    }

    class DatatypeSortImpl extends SortImpl implements DatatypeSort<Name> {
      declare readonly __typename: DatatypeSort['__typename'];

      numConstructors(): number {
        return Z3.get_datatype_sort_num_constructors(contextPtr, this.ptr);
      }

      constructorDecl(idx: number): FuncDecl<Name> {
        const ptr = Z3.get_datatype_sort_constructor(contextPtr, this.ptr, idx);
        return new FuncDeclImpl(ptr);
      }

      recognizer(idx: number): FuncDecl<Name> {
        const ptr = Z3.get_datatype_sort_recognizer(contextPtr, this.ptr, idx);
        return new FuncDeclImpl(ptr);
      }

      accessor(constructorIdx: number, accessorIdx: number): FuncDecl<Name> {
        const ptr = Z3.get_datatype_sort_constructor_accessor(contextPtr, this.ptr, constructorIdx, accessorIdx);
        return new FuncDeclImpl(ptr);
      }

      cast(other: CoercibleToExpr<Name>): DatatypeExpr<Name>;
      cast(other: DatatypeExpr<Name>): DatatypeExpr<Name>;
      cast(other: CoercibleToExpr<Name> | DatatypeExpr<Name>): DatatypeExpr<Name> {
        if (isExpr(other)) {
          assert(this.eqIdentity(other.sort), 'Value cannot be converted to this datatype');
          return other as DatatypeExpr<Name>;
        }
        throw new Error('Cannot coerce value to datatype expression');
      }

      subsort(other: Sort<Name>) {
        _assertContext(other.ctx);
        return this.eqIdentity(other);
      }
    }

    class DatatypeExprImpl extends ExprImpl<Z3_ast, DatatypeSortImpl> implements DatatypeExpr<Name> {
      declare readonly __typename: DatatypeExpr['__typename'];
    }

    function createDatatypes(...datatypes: DatatypeImpl[]): DatatypeSortImpl[] {
      if (datatypes.length === 0) {
        throw new Error('At least one datatype must be provided');
      }

      // All datatypes must be from the same context
      const dtCtx = datatypes[0].ctx;
      for (const dt of datatypes) {
        if (dt.ctx !== dtCtx) {
          throw new Error('All datatypes must be from the same context');
        }
      }

      const sortNames = datatypes.map(dt => dt.name);
      const constructorLists: Z3_constructor_list[] = [];
      const scopedConstructors: Z3_constructor[] = [];

      try {
        // Create constructor lists for each datatype
        for (const dt of datatypes) {
          const constructors: Z3_constructor[] = [];

          for (const [constructorName, fields] of dt.constructors) {
            const fieldNames: string[] = [];
            const fieldSorts: Z3_sort[] = [];
            const fieldRefs: number[] = [];

            for (const [fieldName, fieldSort] of fields) {
              fieldNames.push(fieldName);

              if (fieldSort instanceof DatatypeImpl) {
                // Reference to another datatype being defined
                const refIndex = datatypes.indexOf(fieldSort);
                if (refIndex === -1) {
                  throw new Error(`Referenced datatype "${fieldSort.name}" not found in datatypes being created`);
                }
                // For recursive references, we pass null and the ref index
                fieldSorts.push(null as any); // null will be handled by the Z3 API
                fieldRefs.push(refIndex);
              } else {
                // Regular sort
                fieldSorts.push((fieldSort as Sort<Name>).ptr);
                fieldRefs.push(0);
              }
            }

            const constructor = Z3.mk_constructor(
              contextPtr,
              Z3.mk_string_symbol(contextPtr, constructorName),
              Z3.mk_string_symbol(contextPtr, `is_${constructorName}`),
              fieldNames.map(name => Z3.mk_string_symbol(contextPtr, name)),
              fieldSorts,
              fieldRefs,
            );
            constructors.push(constructor);
            scopedConstructors.push(constructor);
          }

          const constructorList = Z3.mk_constructor_list(contextPtr, constructors);
          constructorLists.push(constructorList);
        }

        // Create the datatypes
        const sortSymbols = sortNames.map(name => Z3.mk_string_symbol(contextPtr, name));
        const resultSorts = Z3.mk_datatypes(contextPtr, sortSymbols, constructorLists);

        // Create DatatypeSortImpl instances
        const results: DatatypeSortImpl[] = [];
        for (let i = 0; i < resultSorts.length; i++) {
          const sortImpl = new DatatypeSortImpl(resultSorts[i]);

          // Attach constructor, recognizer, and accessor functions dynamically
          const numConstructors = sortImpl.numConstructors();
          for (let j = 0; j < numConstructors; j++) {
            const constructor = sortImpl.constructorDecl(j);
            const recognizer = sortImpl.recognizer(j);
            const constructorName = constructor.name().toString();

            // Attach constructor function
            if (constructor.arity() === 0) {
              // Nullary constructor (constant)
              (sortImpl as any)[constructorName] = constructor.call();
            } else {
              (sortImpl as any)[constructorName] = constructor;
            }

            // Attach recognizer function
            (sortImpl as any)[`is_${constructorName}`] = recognizer;

            // Attach accessor functions
            for (let k = 0; k < constructor.arity(); k++) {
              const accessor = sortImpl.accessor(j, k);
              const accessorName = accessor.name().toString();
              (sortImpl as any)[accessorName] = accessor;
            }
          }

          results.push(sortImpl);
        }

        return results;
      } finally {
        // Clean up resources
        for (const constructor of scopedConstructors) {
          Z3.del_constructor(contextPtr, constructor);
        }
        for (const constructorList of constructorLists) {
          Z3.del_constructor_list(contextPtr, constructorList);
        }
      }
    }

    class QuantifierImpl<
        QVarSorts extends NonEmptySortArray<Name>,
        QSort extends BoolSort<Name> | SMTArraySort<Name, QVarSorts>,
      >
      extends ExprImpl<Z3_ast, QSort>
      implements Quantifier<Name, QVarSorts, QSort>
    {
      declare readonly __typename: Quantifier['__typename'];

      is_forall(): boolean {
        return Z3.is_quantifier_forall(contextPtr, this.ast);
      }

      is_exists(): boolean {
        return Z3.is_quantifier_exists(contextPtr, this.ast);
      }

      is_lambda(): boolean {
        return Z3.is_lambda(contextPtr, this.ast);
      }

      weight(): number {
        return Z3.get_quantifier_weight(contextPtr, this.ast);
      }

      num_patterns(): number {
        return Z3.get_quantifier_num_patterns(contextPtr, this.ast);
      }

      pattern(i: number): Pattern<Name> {
        return new PatternImpl(check(Z3.get_quantifier_pattern_ast(contextPtr, this.ast, i)));
      }

      num_no_patterns(): number {
        return Z3.get_quantifier_num_no_patterns(contextPtr, this.ast);
      }

      no_pattern(i: number): Expr<Name> {
        return _toExpr(check(Z3.get_quantifier_no_pattern_ast(contextPtr, this.ast, i)));
      }

      body(): BodyT<Name, QVarSorts, QSort> {
        return _toExpr(check(Z3.get_quantifier_body(contextPtr, this.ast))) as any;
      }

      num_vars(): number {
        return Z3.get_quantifier_num_bound(contextPtr, this.ast);
      }

      var_name(i: number): string | number {
        return _fromSymbol(Z3.get_quantifier_bound_name(contextPtr, this.ast, i));
      }

      var_sort<T extends number>(i: T): QVarSorts[T] {
        return _toSort(check(Z3.get_quantifier_bound_sort(contextPtr, this.ast, i)));
      }

      children(): [BodyT<Name, QVarSorts, QSort>] {
        return [this.body()];
      }
    }

    class NonLambdaQuantifierImpl<QVarSorts extends NonEmptySortArray<Name>>
      extends QuantifierImpl<QVarSorts, BoolSort<Name>>
      implements Quantifier<Name, QVarSorts, BoolSort<Name>>, Bool<Name>
    {
      declare readonly __typename: 'NonLambdaQuantifier';

      not(): Bool<Name> {
        return Not(this);
      }

      and(other: Bool<Name> | boolean): Bool<Name> {
        return And(this, other);
      }

      or(other: Bool<Name> | boolean): Bool<Name> {
        return Or(this, other);
      }

      xor(other: Bool<Name> | boolean): Bool<Name> {
        return Xor(this, other);
      }

      implies(other: Bool<Name> | boolean): Bool<Name> {
        return Implies(this, other);
      }

      iff(other: Bool<Name> | boolean): Bool<Name> {
        return Iff(this, other);
      }
    }

    // isBool will return false which is unlike the python API (but like the C API)
    class LambdaImpl<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>
      extends QuantifierImpl<DomainSort, SMTArraySort<Name, DomainSort, RangeSort>>
      implements
        Quantifier<Name, DomainSort, SMTArraySort<Name, DomainSort, RangeSort>>,
        SMTArray<Name, DomainSort, RangeSort>
    {
      declare readonly __typename: 'Lambda';

      domain(): DomainSort[0] {
        return this.sort.domain();
      }

      domain_n<T extends number>(i: T): DomainSort[T] {
        return this.sort.domain_n(i);
      }

      range(): RangeSort {
        return this.sort.range();
      }

      select(...indices: CoercibleToArrayIndexType<Name, DomainSort>): SortToExprMap<RangeSort, Name> {
        return Select<DomainSort, RangeSort>(this, ...indices);
      }

      store(
        ...indicesAndValue: [
          ...CoercibleToArrayIndexType<Name, DomainSort>,
          CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
        ]
      ): SMTArray<Name, DomainSort, RangeSort> {
        return Store(this, ...indicesAndValue);
      }

      /**
       * Access the array default value.
       * Produces the default range value, for arrays that can be represented as
       * finite maps with a default range value.
       */
      default(): SortToExprMap<RangeSort, Name> {
        return _toExpr(check(Z3.mk_array_default(contextPtr, this.ast))) as SortToExprMap<RangeSort, Name>;
      }
    }

    class AstVectorImpl<Item extends AnyAst<Name>> {
      declare readonly __typename: AstVector['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_ast_vector = Z3.mk_ast_vector(contextPtr)) {
        this.ctx = ctx;
        Z3.ast_vector_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.ast_vector_dec_ref(contextPtr, ptr), this);
      }

      length(): number {
        return Z3.ast_vector_size(contextPtr, this.ptr);
      }

      [Symbol.iterator](): IterableIterator<Item> {
        return this.values();
      }

      *entries(): IterableIterator<[number, Item]> {
        const length = this.length();
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
        const length = this.length();
        if (from < 0) {
          from += length;
        }
        if (from >= length) {
          throw new RangeError(`expected from index ${from} to be less than length ${length}`);
        }

        if (to === undefined) {
          return _toAst(check(Z3.ast_vector_get(contextPtr, this.ptr, from))) as Item;
        }

        if (to < 0) {
          to += length;
        }
        if (to >= length) {
          throw new RangeError(`expected to index ${to} to be less than length ${length}`);
        }

        const result: Item[] = [];
        for (let i = from; i < to; i++) {
          result.push(_toAst(check(Z3.ast_vector_get(contextPtr, this.ptr, i))) as Item);
        }
        return result;
      }

      set(i: number, v: Item): void {
        _assertContext(v);
        if (i >= this.length()) {
          throw new RangeError(`expected index ${i} to be less than length ${this.length()}`);
        }
        check(Z3.ast_vector_set(contextPtr, this.ptr, i, v.ast));
      }

      push(v: Item): void {
        _assertContext(v);
        check(Z3.ast_vector_push(contextPtr, this.ptr, v.ast));
      }

      resize(size: number): void {
        check(Z3.ast_vector_resize(contextPtr, this.ptr, size));
      }

      has(v: Item): boolean {
        _assertContext(v);
        for (const item of this.values()) {
          if (item.eqIdentity(v)) {
            return true;
          }
        }
        return false;
      }

      sexpr(): string {
        return check(Z3.ast_vector_to_string(contextPtr, this.ptr));
      }
    }

    class AstMapImpl<Key extends AnyAst<Name>, Value extends AnyAst<Name>> implements AstMap<Name, Key, Value> {
      declare readonly __typename: AstMap['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_ast_map = Z3.mk_ast_map(contextPtr)) {
        this.ctx = ctx;
        Z3.ast_map_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.ast_map_dec_ref(contextPtr, ptr), this);
      }

      [Symbol.iterator](): Iterator<[Key, Value]> {
        return this.entries();
      }

      get size(): number {
        return Z3.ast_map_size(contextPtr, this.ptr);
      }

      *entries(): IterableIterator<[Key, Value]> {
        for (const key of this.keys()) {
          yield [key, this.get(key)];
        }
      }

      keys(): AstVector<Name, Key> {
        return new AstVectorImpl(Z3.ast_map_keys(contextPtr, this.ptr));
      }

      *values(): IterableIterator<Value> {
        for (const [_, value] of this.entries()) {
          yield value;
        }
      }

      get(key: Key): Value {
        return _toAst(check(Z3.ast_map_find(contextPtr, this.ptr, key.ast))) as Value;
      }

      set(key: Key, value: Value): void {
        check(Z3.ast_map_insert(contextPtr, this.ptr, key.ast, value.ast));
      }

      delete(key: Key): void {
        check(Z3.ast_map_erase(contextPtr, this.ptr, key.ast));
      }

      clear(): void {
        check(Z3.ast_map_reset(contextPtr, this.ptr));
      }

      has(key: Key): boolean {
        return check(Z3.ast_map_contains(contextPtr, this.ptr, key.ast));
      }

      sexpr(): string {
        return check(Z3.ast_map_to_string(contextPtr, this.ptr));
      }
    }

    function substitute(t: Expr<Name>, ...substitutions: [Expr<Name>, Expr<Name>][]): Expr<Name> {
      _assertContext(t);
      const from: Z3_ast[] = [];
      const to: Z3_ast[] = [];
      for (const [f, t] of substitutions) {
        _assertContext(f);
        _assertContext(t);
        from.push(f.ast);
        to.push(t.ast);
      }
      return _toExpr(check(Z3.substitute(contextPtr, t.ast, from, to)));
    }

    function substituteVars(t: Expr<Name>, ...to: Expr<Name>[]): Expr<Name> {
      _assertContext(t);
      const toAsts: Z3_ast[] = [];
      for (const expr of to) {
        _assertContext(expr);
        toAsts.push(expr.ast);
      }
      return _toExpr(check(Z3.substitute_vars(contextPtr, t.ast, toAsts)));
    }

    function substituteFuns(t: Expr<Name>, ...substitutions: [FuncDecl<Name>, Expr<Name>][]): Expr<Name> {
      _assertContext(t);
      const from: Z3_func_decl[] = [];
      const to: Z3_ast[] = [];
      for (const [f, body] of substitutions) {
        _assertContext(f);
        _assertContext(body);
        from.push(f.ptr);
        to.push(body.ast);
      }
      return _toExpr(check(Z3.substitute_funs(contextPtr, t.ast, from, to)));
    }

    function updateField(t: DatatypeExpr<Name>, fieldAccessor: FuncDecl<Name>, newValue: Expr<Name>): DatatypeExpr<Name> {
      _assertContext(t);
      _assertContext(fieldAccessor);
      _assertContext(newValue);
      return _toExpr(check(Z3.datatype_update_field(contextPtr, fieldAccessor.ptr, t.ast, newValue.ast))) as DatatypeExpr<Name>;
    }

    function ast_from_string(s: string): Ast<Name> {
      const sort_names: Z3_symbol[] = [];
      const sorts: Z3_sort[] = [];
      const decl_names: Z3_symbol[] = [];
      const decls: Z3_func_decl[] = [];
      const v = new AstVectorImpl(check(Z3.parse_smtlib2_string(contextPtr, s, sort_names, sorts, decl_names, decls)));
      if (v.length() !== 1) {
        throw new Error('Expected exactly one AST. Instead got ' + v.length() + ': ' + v.sexpr());
      }
      return v.get(0);
    }

    const ctx: Context<Name> = {
      ptr: contextPtr,
      name,

      /////////////
      // Classes //
      /////////////
      Solver: SolverImpl,
      Optimize: OptimizeImpl,
      Fixedpoint: FixedpointImpl,
      Model: ModelImpl,
      Tactic: TacticImpl,
      Goal: GoalImpl,
      Params: ParamsImpl,
      Simplifier: SimplifierImpl,
      AstVector: AstVectorImpl as AstVectorCtor<Name>,
      AstMap: AstMapImpl as AstMapCtor<Name>,

      ///////////////
      // Functions //
      ///////////////
      interrupt,
      setPrintMode,
      isModel,
      isAst,
      isSort,
      isFuncDecl,
      isFuncInterp,
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
      isQuantifier,
      isArith,
      isArithSort,
      isInt,
      isIntVal,
      isIntSort,
      isReal,
      isRealVal,
      isRealSort,
      isRCFNum,
      isBitVecSort,
      isBitVec,
      isBitVecVal, // TODO fix ordering
      isFPRMSort,
      isFPRM,
      isFPSort,
      isFP,
      isFPVal,
      isSeqSort,
      isSeq,
      isStringSort,
      isString,
      isFiniteSetSort,
      isFiniteSet,
      isArraySort,
      isArray,
      isConstArray,
      isProbe,
      isTactic,
      isGoal,
      isAstVector,
      eqIdentity,
      getVarIndex,
      from,
      solve,

      /////////////
      // Objects //
      /////////////
      Sort,
      Function,
      RecFunc,
      Bool,
      Int,
      Real,
      RCFNum,
      BitVec,
      Float,
      FloatRM,
      String,
      Seq,
      Re,
      Array,
      Set,
      FiniteSet,
      Datatype,

      ////////////////
      // Operations //
      ////////////////
      If,
      Distinct,
      Const,
      Consts,
      FreshConst,
      Var,
      Implies,
      Iff,
      Eq,
      Xor,
      Not,
      And,
      Or,
      PbEq,
      PbGe,
      PbLe,
      AtMost,
      AtLeast,
      ForAll,
      Exists,
      Lambda,
      ToReal,
      ToInt,
      IsInt,
      Sqrt,
      Cbrt,
      BV2Int,
      Int2BV,
      Concat,
      Cond,
      AndThen,
      OrElse,
      Repeat,
      TryFor,
      When,
      Skip,
      Fail,
      FailIf,
      ParOr,
      ParAndThen,
      With,
      LT,
      GT,
      LE,
      GE,
      ULT,
      UGT,
      ULE,
      UGE,
      SLT,
      SGT,
      SLE,
      SGE,
      Sum,
      Sub,
      Product,
      Div,
      BUDiv,
      Neg,
      Mod,
      Select,
      Store,
      Ext,
      Extract,

      substitute,
      substituteVars,
      substituteFuns,
      updateField,
      simplify,

      /////////////
      // Loading //
      /////////////
      ast_from_string,

      SetUnion,
      SetIntersect,
      SetDifference,
      SetAdd,
      SetDel,
      SetComplement,
      EmptySet,
      FullSet,
      isMember,
      isSubset,

      InRe,
      Union,
      Intersect,
      ReConcat,
      Plus,
      Star,
      Option,
      Complement,
      Diff,
      Range,
      Loop,
      Power,
      AllChar,
      Empty,
      Full,

      mkPartialOrder,
      mkTransitiveClosure,
      polynomialSubresultants,
    };
    cleanup.register(ctx, () => Z3.del_context(contextPtr));
    return ctx;
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

    Context: createContext as ContextCtor,
  };
}
