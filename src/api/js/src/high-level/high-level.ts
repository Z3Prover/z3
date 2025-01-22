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
  Z3_symbol,
  Z3_symbol_kind,
  Z3_tactic,
  Z3_pattern,
  Z3_app,
  Z3_params,
  Z3_func_entry,
  Z3_optimize,
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
  Context,
  ContextCtor,
  Expr,
  FuncDecl,
  FuncDeclSignature,
  FuncInterp,
  IntNum,
  Model,
  Optimize,
  Pattern,
  Probe,
  Quantifier,
  BodyT,
  RatNum,
  SMTArray,
  SMTArraySort,
  Solver,
  Sort,
  SortToExprMap,
  Tactic,
  Z3Error,
  Z3HighLevel,
  CoercibleToArith,
  NonEmptySortArray,
  FuncEntry,
  SMTSetSort,
  SMTSet,
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
        case Z3_sort_kind.Z3_ARRAY_SORT:
          return new ArraySortImpl(ast);
        default:
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
        case Z3_sort_kind.Z3_ARRAY_SORT:
          return new ArrayImpl(ast);
        default:
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
      const<ElemSort extends AnySort<Name>>(name: string, sort: ElemSort) : SMTSet<Name, ElemSort> {
        return new SetImpl<ElemSort>(
          check(Z3.mk_const(contextPtr, _toSymbol(name), Array.sort(sort, Bool.sort()).ptr)),
        );
      },
      consts<ElemSort extends AnySort<Name>>(names: string | string[], sort: ElemSort) : SMTSet<Name, ElemSort>[] {
        if (typeof names === 'string') {
          names = names.split(' ');
        }
        return names.map(name => Set.const(name, sort));
      },
      empty<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort> {
        return EmptySet(sort);
      },
      val<ElemSort extends AnySort<Name>>(values: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>[], sort: ElemSort): SMTSet<Name, ElemSort> {
        var result = EmptySet(sort);
        for (const value of values) {
          result = SetAdd(result, value);
        }
        return result;
      }
    }

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

    function SetUnion<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_set_union(contextPtr, args.map(arg => arg.ast))));
    }
    
    function SetIntersect<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_set_intersect(contextPtr, args.map(arg => arg.ast))));
    }
    
    function SetDifference<ElemSort extends AnySort<Name>>(a: SMTSet<Name, ElemSort>, b: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort> {
      return new SetImpl<ElemSort>(check(Z3.mk_set_difference(contextPtr, a.ast, b.ast)));
    }
    
    function SetHasSize<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>, size: bigint | number | string | IntNum<Name>): Bool<Name> {
      const a = typeof size === 'object'? Int.sort().cast(size) : Int.sort().cast(size);
      return new BoolImpl(check(Z3.mk_set_has_size(contextPtr, set.ast, a.ast)));
    }

    function SetAdd<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>, elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort> {
      const arg = set.elemSort().cast(elem as any);
      return new SetImpl<ElemSort>(check(Z3.mk_set_add(contextPtr, set.ast, arg.ast)));
    }
    function SetDel<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>, elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort> {
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
    function isMember<ElemSort extends AnySort<Name>>(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>, set: SMTSet<Name, ElemSort>): Bool<Name> {
      const arg = set.elemSort().cast(elem as any);
      return new BoolImpl(check(Z3.mk_set_member(contextPtr, arg.ast, set.ast)));
    }
    function isSubset<ElemSort extends AnySort<Name>>(a: SMTSet<Name, ElemSort>, b: SMTSet<Name, ElemSort>): Bool<Name> {
      return new BoolImpl(check(Z3.mk_set_subset(contextPtr, a.ast, b.ast)));
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

      model() {
        return new ModelImpl(check(Z3.solver_get_model(contextPtr, this.ptr)));
      }

      toString() {
        return check(Z3.solver_to_string(contextPtr, this.ptr));
      }

      fromString(s: string) {
        Z3.solver_from_string(contextPtr, this.ptr, s);
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

      release() {
        Z3.model_dec_ref(contextPtr, this.ptr);
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
    }

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

      subNoUndeflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsub_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
      }

      sdivNoOverflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsdiv_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      mulNoOverflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvmul_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
      }

      mulNoUndeflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
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
    }

    class SetImpl<ElemSort extends Sort<Name>> extends ExprImpl<Z3_ast, ArraySortImpl<[ElemSort], BoolSort<Name>>> implements SMTSet<Name, ElemSort> {
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
      hasSize(size: string | number | bigint | IntNum<Name>): Bool<Name> {
        return SetHasSize(this, size);
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
      Model: ModelImpl,
      Tactic: TacticImpl,
      AstVector: AstVectorImpl as AstVectorCtor<Name>,
      AstMap: AstMapImpl as AstMapCtor<Name>,

      ///////////////
      // Functions //
      ///////////////
      interrupt,
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
      isBitVecSort,
      isBitVec,
      isBitVecVal, // TODO fix ordering
      isArraySort,
      isArray,
      isConstArray,
      isProbe,
      isTactic,
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
      BitVec,
      Array,
      Set,

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
      Extract,

      substitute,
      simplify,

      /////////////
      // Loading //
      /////////////
      ast_from_string,

      SetUnion,
      SetIntersect,
      SetDifference,
      SetHasSize,
      SetAdd,
      SetDel,
      SetComplement,
      EmptySet,
      FullSet,
      isMember,
      isSubset,
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

    Context: createContext,
  };
}
