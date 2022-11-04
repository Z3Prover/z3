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
} from '../low-level';
import {
  AnyAst,
  AnyExpr,
  AnySort,
  Arith,
  ArithSort, ArrayIndexType,
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
  CheckSatResult, CoercibleFromMap,
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
  SMTArray,
  SMTArraySort,
  Solver,
  Sort,
  SortToExprMap,
  Tactic,
  Z3Error,
  Z3HighLevel,
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
  r && assert(
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
      Object.entries(options).forEach(
        ([key, value]) => check(Z3.set_param_value(cfg, key, value.toString()))
      );
    }
    const contextPtr = Z3.mk_context_rc(cfg);
    Z3.set_ast_print_mode(contextPtr, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
    Z3.del_config(cfg);

    function _assertContext(...ctxs: (Context<Name> | { ctx: Context<Name> })[]) {
      ctxs.forEach(other => assert('ctx' in other ? ctx === other.ctx : ctx === other, 'Context mismatch'));
    }

    // call this after every nontrivial call to the underlying API
    function throwIfError() {
      if (Z3.get_error_code(contextPtr) !== Z3_error_code.Z3_OK) {
        throw new Error(Z3.get_error_msg(ctx.ptr, Z3.get_error_code(ctx.ptr)));
      }
    }

    function check<T>(val: T) {
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
        if (Z3.is_quantifier_forall(contextPtr, ast))
          return new BoolImpl(ast);
        if (Z3.is_quantifier_exists(contextPtr, ast))
          return new BoolImpl(ast);
        if (Z3.is_lambda(contextPtr, ast))
          return new ExprImpl(ast);
        assert(false);
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
      const r = obj instanceof BoolImpl;
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

    async function simplify(e: Expr<Name>) {
      const result = await Z3.simplify(contextPtr, e.ast)
      return _toExpr(check(result));
    }

    /////////////
    // Objects //
    /////////////
    const Sort = {
      declare: (name: string) => new SortImpl(Z3.mk_uninterpreted_sort(contextPtr, _toSymbol(name))),
    };
    const Function = {
      declare: (name: string, ...signature: FuncDeclSignature<Name>) => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        _assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          _assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl(Z3.mk_func_decl(contextPtr, _toSymbol(name), dom, rng.ptr));
      },
      fresh: (...signature: FuncDeclSignature<Name>) => {
        const arity = signature.length - 1;
        const rng = signature[arity];
        _assertContext(rng);
        const dom = [];
        for (let i = 0; i < arity; i++) {
          _assertContext(signature[i]);
          dom.push(signature[i].ptr);
        }
        return new FuncDeclImpl(Z3.mk_fresh_func_decl(contextPtr, 'f', dom, rng.ptr));
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
        value: bigint | number | boolean,
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
      sort<DomainSort extends [AnySort<Name>, ...AnySort<Name>[]], RangeSort extends AnySort<Name>>(
        ...sig: [...DomainSort, RangeSort]
      ): SMTArraySort<Name, DomainSort, RangeSort> {
        const arity = sig.length - 1;
        const r = sig[arity];
        const d = sig[0];
        if (arity === 1) {
          return new ArraySortImpl(Z3.mk_array_sort(contextPtr, d.ptr, r.ptr));
        }
        const dom = sig.slice(0, arity);
        return new ArraySortImpl(Z3.mk_array_sort_n(contextPtr, dom.map(s => s.ptr), r.ptr));
      },
      const<DomainSort extends [AnySort<Name>, ...AnySort<Name>[]], RangeSort extends AnySort<Name>>(
        name: string, ...sig: [...DomainSort, RangeSort]
      ): SMTArray<Name, DomainSort, RangeSort> {
        return new ArrayImpl<DomainSort, RangeSort>(
          check(Z3.mk_const(contextPtr, _toSymbol(name), Array.sort(...sig).ptr))
        );
      },
      consts<DomainSort extends [AnySort<Name>, ...AnySort<Name>[]], RangeSort extends AnySort<Name>>(
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
        value: SortToExprMap<RangeSort, Name>
      ): SMTArray<Name, [DomainSort], RangeSort> {
        return new ArrayImpl<[DomainSort], RangeSort>(
          check(Z3.mk_const_array(contextPtr, domain.ptr, value.ptr))
        );
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
    ): CoercibleToExprMap<OnTrueRef | OnFalseRef, Name>;
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

    class AstImpl<Ptr extends Z3_ast> implements Ast<Name, Ptr> {
      declare readonly __typename: Ast['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Ptr) {
        this.ctx = ctx;
        const myAst = this.ast;

        Z3.inc_ref(contextPtr, myAst);
        cleanup.register(this, () => Z3.dec_ref(contextPtr, myAst));
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

      readonly ptr: Z3_solver;
      readonly ctx: Context<Name>;

      constructor(ptr: Z3_solver | string = Z3.mk_solver(contextPtr)) {
        this.ctx = ctx;
        let myPtr: Z3_solver;
        if (typeof ptr === 'string') {
          myPtr = check(Z3.mk_solver_for_logic(contextPtr, _toSymbol(ptr)));
        } else {
          myPtr = ptr;
        }
        this.ptr = myPtr;
        Z3.solver_inc_ref(contextPtr, myPtr);
        cleanup.register(this, () => Z3.solver_dec_ref(contextPtr, myPtr));
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
    }

    class ModelImpl implements Model<Name> {
      declare readonly __typename: Model['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_model = Z3.mk_model(contextPtr)) {
        this.ctx = ctx;
        Z3.model_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.model_dec_ref(contextPtr, ptr));
      }

      length() {
        return Z3.model_get_num_consts(contextPtr, this.ptr) + Z3.model_get_num_funcs(contextPtr, this.ptr);
      }

      [Symbol.iterator](): Iterator<FuncDecl<Name>> {
        return this.values();
      }

      * entries(): IterableIterator<[number, FuncDecl<Name>]> {
        const length = this.length();
        for (let i = 0; i < length; i++) {
          yield [i, this.get(i)];
        }
      }

      * keys(): IterableIterator<number> {
        for (const [key] of this.entries()) {
          yield key;
        }
      }

      * values(): IterableIterator<FuncDecl<Name>> {
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
        to?: number
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
    }

    class FuncInterpImpl implements FuncInterp<Name> {
      declare readonly __typename: FuncInterp['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_func_interp) {
        this.ctx = ctx;
        Z3.func_interp_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.func_interp_dec_ref(contextPtr, ptr));
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

    class FuncDeclImpl extends AstImpl<Z3_func_decl> implements FuncDecl<Name> {
      declare readonly __typename: FuncDecl['__typename'];

      get ast() {
        return Z3.func_decl_to_ast(contextPtr, this.ptr);
      }

      name() {
        return _fromSymbol(Z3.get_decl_name(contextPtr, this.ptr));
      }

      arity() {
        return Z3.get_arity(contextPtr, this.ptr);
      }

      domain(i: number) {
        assert(i < this.arity(), 'Index out of bounds');
        return _toSort(Z3.get_domain(contextPtr, this.ptr, i));
      }

      range() {
        return _toSort(Z3.get_range(contextPtr, this.ptr));
      }

      kind() {
        return Z3.get_decl_kind(contextPtr, this.ptr);
      }

      params(): (number | string | Z3_symbol | Sort<Name> | Expr<Name> | FuncDecl<Name>)[] {
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
              result.push(check(Z3.get_decl_symbol_parameter(contextPtr, this.ptr, i)));
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
            default:
              assertExhaustive(kind);
          }
        }
        return result;
      }

      call(...args: CoercibleToExpr<Name>[]) {
        assert(args.length === this.arity(), `Incorrect number of arguments to ${this}`);
        return _toExpr(
          check(Z3.mk_app(
            contextPtr,
            this.ptr,
            args.map((arg, i) => {
              return this.domain(i).cast(arg).ast;
            }),
          )),
        );
      }
    }

    class ExprImpl<Ptr extends Z3_ast, S extends Sort<Name> = AnySort<Name>> extends AstImpl<Ptr> implements Expr<Name> {
      declare readonly __typename: Expr['__typename'];

      get sort(): S {
        return _toSort(Z3.get_sort(contextPtr, this.ast)) as S;
      }

      eq(other: CoercibleToExpr<Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_eq(contextPtr, this.ast, from(other).ast)));
      }

      neq(other: CoercibleToExpr<Name>): Bool<Name> {
        return new BoolImpl(
          check(Z3.mk_distinct(
            contextPtr,
            [this, other].map(expr => from(expr).ast),
          )),
        );
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
      declare readonly __typename: Bool['__typename'];

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
        cleanup.register(this, () => Z3.tactic_dec_ref(contextPtr, myPtr));
      }
    }

    class ArithSortImpl extends SortImpl implements ArithSort<Name> {
      declare readonly __typename: ArithSort['__typename'];

      cast(other: bigint | number): IntNum<Name> | RatNum<Name>;
      cast(other: CoercibleRational | RatNum<Name>): RatNum<Name>;
      cast(other: IntNum<Name>): IntNum<Name>;
      cast(other: Bool<Name> | Arith<Name>): Arith<Name>;
      cast(other: CoercibleToExpr<Name>): never;
      cast(other: CoercibleToExpr<Name>): Arith<Name> | RatNum<Name> | IntNum<Name> {
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

    class ArithImpl extends ExprImpl<Z3_ast, ArithSort<Name>> implements Arith<Name> {
      declare readonly __typename: Arith['__typename'];

      add(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new ArithImpl(check(Z3.mk_add(contextPtr, [this.ast, this.sort.cast(other).ast])));
      }

      mul(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new ArithImpl(check(Z3.mk_mul(contextPtr, [this.ast, this.sort.cast(other).ast])));
      }

      sub(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new ArithImpl(check(Z3.mk_sub(contextPtr, [this.ast, this.sort.cast(other).ast])));
      }

      pow(exponent: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new ArithImpl(check(Z3.mk_power(contextPtr, this.ast, this.sort.cast(exponent).ast)));
      }

      div(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new ArithImpl(check(Z3.mk_div(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      mod(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new ArithImpl(check(Z3.mk_mod(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      neg() {
        return new ArithImpl(check(Z3.mk_unary_minus(contextPtr, this.ast)));
      }

      le(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new BoolImpl(check(Z3.mk_le(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      lt(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new BoolImpl(check(Z3.mk_lt(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      gt(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new BoolImpl(check(Z3.mk_gt(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      ge(other: Arith<Name> | number | bigint | string | CoercibleRational) {
        return new BoolImpl(check(Z3.mk_ge(contextPtr, this.ast, this.sort.cast(other).ast)));
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
        return new BitVecImpl<Bits>(check(Z3.mk_bvadd(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      mul(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvmul(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      sub(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvsub(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      sdiv(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvsdiv(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      udiv(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvudiv(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      smod(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvsmod(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      urem(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvurem(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      srem(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvsrem(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      neg(): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_bvneg(contextPtr, this.ast)));
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

      extract(high: number, low: number): BitVec<Bits, Name> {
        return new BitVecImpl<Bits>(check(Z3.mk_extract(contextPtr, high, low, this.ast)));
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
        return new BoolImpl(check(Z3.mk_bvsle(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      ule(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvule(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      slt(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvslt(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      ult(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvult(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      sge(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsge(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      uge(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvuge(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      sgt(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvsgt(contextPtr, this.ast, this.sort.cast(other).ast)));
      }

      ugt(other: CoercibleToBitVec<Bits, Name>): Bool<Name> {
        return new BoolImpl(check(Z3.mk_bvugt(contextPtr, this.ast, this.sort.cast(other).ast)));
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

    class ArraySortImpl<DomainSort extends [AnySort<Name>, ...AnySort<Name>[]] = [Sort<Name>, ...Sort<Name>[]],
      RangeSort extends AnySort<Name> = Sort<Name>>
      extends SortImpl
      implements SMTArraySort<Name, DomainSort, RangeSort> {
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

    class ArrayImpl<
      DomainSort extends [AnySort<Name>, ...AnySort<Name>[]] = [Sort<Name>, ...Sort<Name>[]],
      RangeSort extends AnySort<Name> = Sort<Name>
    > extends ExprImpl<Z3_ast, ArraySortImpl<DomainSort, RangeSort>>
      implements SMTArray<Name, DomainSort, RangeSort> {
      declare readonly __typename: SMTArray['__typename'];

      domain(): DomainSort[0] {
        return this.sort.domain();
      }

      domain_n<T extends number>(i: T): DomainSort[T] {
        return this.sort.domain_n(i);
      }

      range(): RangeSort {
        return this.sort.range();
      }

      select(...indices: ArrayIndexType<Name, DomainSort>): SortToExprMap<RangeSort, Name> {
        const args = indices.map((arg, i) => this.domain_n(i).cast(arg as any));
        if (args.length === 1) {
          return _toExpr(check(Z3.mk_select(contextPtr, this.ast, args[0].ast))) as SortToExprMap<RangeSort, Name>;
        }
        const _args = args.map(arg => arg.ast);
        return _toExpr(check(Z3.mk_select_n(contextPtr, this.ast, _args))) as SortToExprMap<RangeSort, Name>;
      }

      store(
        ...indicesAndValue: [
          ...ArrayIndexType<Name, DomainSort>,
          CoercibleFromMap<SortToExprMap<RangeSort, Name>, Name>
        ]
      ): SMTArray<Name, DomainSort, RangeSort> {
        const args = indicesAndValue.map((arg, i) => {
          if (i === indicesAndValue.length - 1) {
            return this.range().cast(arg as CoercibleFromMap<SortToExprMap<RangeSort, Name>, Name>);
          }
          return this.domain_n(i).cast(arg as any);
        });
        if (args.length <= 1) {
          throw new Z3Error("Array store requires both index and value arguments");
        }
        if (args.length === 2) {
          return _toExpr(check(Z3.mk_store(contextPtr, this.ast, args[0].ast, args[1].ast))) as SMTArray<Name, DomainSort, RangeSort>;
        }
        const _idxs = args.slice(0, args.length - 1).map(arg => arg.ast);
        return _toExpr(check(Z3.mk_store_n(contextPtr, this.ast, _idxs, args[args.length - 1].ast))) as SMTArray<Name, DomainSort, RangeSort>;
      }
    }

    class AstVectorImpl<Item extends AnyAst<Name>> {
      declare readonly __typename: AstVector['__typename'];
      readonly ctx: Context<Name>;

      constructor(readonly ptr: Z3_ast_vector = Z3.mk_ast_vector(contextPtr)) {
        this.ctx = ctx;
        Z3.ast_vector_inc_ref(contextPtr, ptr);
        cleanup.register(this, () => Z3.ast_vector_dec_ref(contextPtr, ptr));
      }

      length(): number {
        return Z3.ast_vector_size(contextPtr, this.ptr);
      }

      [Symbol.iterator](): IterableIterator<Item> {
        return this.values();
      }

      * entries(): IterableIterator<[number, Item]> {
        const length = this.length();
        for (let i = 0; i < length; i++) {
          yield [i, this.get(i)];
        }
      }

      * keys(): IterableIterator<number> {
        for (let [key] of this.entries()) {
          yield key;
        }
      }

      * values(): IterableIterator<Item> {
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
        cleanup.register(this, () => Z3.ast_map_dec_ref(contextPtr, ptr));
      }

      [Symbol.iterator](): Iterator<[Key, Value]> {
        return this.entries();
      }

      get size(): number {
        return Z3.ast_map_size(contextPtr, this.ptr);
      }

      * entries(): IterableIterator<[Key, Value]> {
        for (const key of this.keys()) {
          yield [key, this.get(key)];
        }
      }

      keys(): AstVector<Name, Key> {
        return new AstVectorImpl(Z3.ast_map_keys(contextPtr, this.ptr));
      }

      * values(): IterableIterator<Value> {
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

    const ctx: Context<Name> = {
      ptr: contextPtr,
      name,

      /////////////
      // Classes //
      /////////////
      Solver: SolverImpl,
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
      Eq,
      Xor,
      Not,
      And,
      Or,
      ToReal,
      ToInt,
      IsInt,
      Sqrt,
      Cbrt,
      BV2Int,
      Int2BV,
      Concat,
      Cond,
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
