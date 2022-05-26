// TODO(ritave): Research whether we can use type system to discern between classes
//               from other contexts.
//               We could use templated string literals Solver<'contextName'> but that would
//               be cumbersome for the end user
// TODO(ritave): Coerce primitives to expressions
// TODO(ritave): Verify that the contexts match
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
  Z3_parameter_kind,
  Z3_pattern,
  Z3_probe,
  Z3_sort,
  Z3_symbol,
  Z3_symbol_kind,
  Z3_tactic,
} from '../low-level';
import {
  AnyAst,
  AstRef,
  AstVector,
  BoolRef,
  BoolSortRef,
  Context,
  ContextOptions,
  ExprRef,
  FuncDeclRef,
  PatternRef,
  Probe,
  SortRef,
  SortToExpr,
  Tactic,
  Z3AssertionError,
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
      Z3.global_param_set(key, value.to_string());
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

  function createContext(contextOptions: Partial<ContextOptions> = {}) {
    // TODO(ritave): Create a custom linting rule that checks if the provided callbacks to cleanup
    //               Don't capture `this`
    const cleanup = new FinalizationRegistry<() => void>(callback => callback());

    class ContextImpl {
      declare readonly __typename: 'Context';

      readonly ptr: Z3_context;

      constructor(params: Partial<ContextOptions>) {
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

    const ctx = new ContextImpl(contextOptions);

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
        default:
          throw new Error('Not implemented');
      }
    }

    function _toSort(ast: Z3_sort) {
      switch (Z3.get_sort_kind(ctx.ptr, ast)) {
        default:
          return new SortRefImpl(ast);
      }
    }

    function _toExpr(ast: Z3_ast) {
      const kind = Z3.get_ast_kind(ctx.ptr, ast);
      switch (kind) {
        default:
          return new ExprRefImpl(ast);
      }
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
      return obj instanceof ContextImpl;
    }

    function isAst(obj: unknown): obj is AstRef {
      return obj instanceof AstRefImpl;
    }

    function isSort(obj: unknown): obj is SortRef {
      return obj instanceof SortRefImpl;
    }

    function isFuncDecl(obj: unknown): obj is FuncDeclRef {
      return obj instanceof FuncDeclRefImpl;
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
      return obj instanceof ExprRefImpl;
    }

    function isVar(obj: unknown): obj is ExprRef {
      return isExpr(obj) && Z3.get_ast_kind(obj.ctx.ptr, obj.ast) === Z3_ast_kind.Z3_VAR_AST;
    }

    function isAppOf(obj: unknown, kind: Z3_decl_kind): boolean {
      return isApp(obj) && obj.decl().kind() === kind;
    }

    function isBool(obj: unknown): obj is BoolRef {
      return obj instanceof BoolRefImpl;
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

    function isProbe(obj: unknown): obj is Probe {
      return obj instanceof ProbeImpl;
    }

    function isTactic(obj: unknown): obj is Tactic {
      return obj instanceof TacticImpl;
    }

    function isPattern(obj: unknown): obj is PatternRef {
      return obj instanceof PatternRefImpl;
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
        assert((this.ptr as any).__typename === 'Z3_ast');
        return this.ptr as any as Z3_ast;
      }

      get id() {
        return Z3.get_ast_id(this.ctx.ptr, this.ast);
      }

      eqIdentity(other: AstRef) {
        return Z3.is_eq_ast(this.ctx.ptr, this.ast, other.ast);
      }

      neqIdentity(other: AstRef) {
        return !this.eqIdentity(other);
      }

      sexpr() {
        return Z3.ast_to_string(this.ctx.ptr, this.ast);
      }

      hash() {
        return Z3.get_ast_hash(this.ctx.ptr, this.ast);
      }
    }

    class SortRefImpl extends AstRefImpl<Z3_sort> {
      declare readonly __typename: 'SortRef' | BoolSortRef['__typename'];

      get ast(): Z3_ast {
        return Z3.sort_to_ast(ctx.ptr, this.ptr);
      }

      kind() {
        return Z3.get_sort_kind(this.ctx.ptr, this.ptr);
      }

      subsort(other: SortRef) {
        return false;
      }

      cast(expr: ExprRef): ExprRef {
        assert(expr.eqIdentity(expr.sort()), 'Sort mismatch');
        return expr;
      }

      name() {
        return _fromSymbol(Z3.get_sort_name(this.ctx.ptr, this.ptr));
      }

      eqIdentity(other: SortRef) {
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
            args.map((arg, i) => this.domain(i).cast(arg).ast),
          ),
        );
      }
    }

    class ExprRefImpl<Ptr> extends AstRefImpl<Ptr> {
      declare readonly __typename: 'ExprRef' | BoolRef['__typename'] | PatternRef['__typename'];

      sort() {
        return _toSort(Z3.get_sort(this.ctx.ptr, this.ast));
      }

      eq(other: ExprRef) {
        return new BoolRefImpl(Z3.mk_eq(this.ctx.ptr, this.ast, other.ast));
      }

      neq(other: ExprRef) {
        return new BoolRefImpl(
          Z3.mk_distinct(
            this.ctx.ptr,
            [this, other].map(expr => expr.ast),
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

      cast(other: ExprRef) {
        assert(this.eqIdentity(other.sort()), 'Value cannot be converted into a Z3 Boolean value');
        assert(other instanceof BoolRefImpl);
        return other;
      }

      subsort(other: SortRef) {
        return other instanceof ArithSortRefImpl;
      }

      isInt(): true {
        return true;
      }

      isBool(): true {
        return true;
      }
    }

    class BoolRefImpl extends ExprRefImpl<Z3_ast> {
      declare readonly __typename: 'BoolRef';

      sort() {
        return new BoolSortRefImpl(Z3.get_sort(this.ctx.ptr, this.ast));
      }
      mul(other: BoolRef) {
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

    class ArithSortRefImpl extends SortRefImpl {}

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
        if (i >= this.length) {
          throw new RangeError();
        }
        Z3.ast_vector_set(this.ctx.ptr, this.ptr, i, v.ast);
      }

      push(v: Item): void {
        Z3.ast_vector_push(this.ctx.ptr, this.ptr, v.ast);
      }

      resize(size: number): void {
        Z3.ast_vector_resize(this.ctx.ptr, this.ptr, size);
      }

      has(v: Item): boolean {
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
      const dom = [];
      for (let i = 0; i < arity; i++) {
        dom.push(signature[i].ptr);
      }
      const ctx = rng.ctx;
      return new FuncDeclRefImpl(Z3.mk_func_decl(ctx.ptr, _toSymbol(name), dom, rng.ptr));
    }

    function FreshFunction(...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      const dom = [];
      for (let i = 0; i < arity; i++) {
        dom.push(signature[i].ptr);
      }
      const ctx = rng.ctx;
      return new FuncDeclRefImpl(Z3.mk_fresh_func_decl(ctx.ptr, 'f', dom, rng.ptr));
    }

    function RecFunction(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef {
      const arity = signature.length - 1;
      const rng = signature[arity];
      const dom = [];
      for (let i = 0; i < arity; i++) {
        dom.push(signature[i].ptr);
      }
      const ctx = rng.ctx;
      return new FuncDeclRefImpl(Z3.mk_rec_func_decl(ctx.ptr, _toSymbol(name), dom, rng.ptr));
    }

    function RecAddDefinition(f: FuncDeclRef, args: ExprRef[], body: ExprRef) {
      Z3.add_rec_def(
        body.ctx.ptr,
        f.ptr,
        args.map(arg => arg.ast),
        body.ast,
      );
    }

    function If(condition: Probe, onTrue: Tactic, onFalse: Tactic): Tactic;
    function If<OnTrueRef extends ExprRef = ExprRef, OnFalseRef extends ExprRef = ExprRef>(
      condition: BoolRef,
      onTrue: OnTrueRef,
      onFalse: OnFalseRef,
    ): OnTrueRef | OnFalseRef;
    function If(condition: BoolRef | Probe, onTrue: ExprRef | Tactic, onFalse: ExprRef | Tactic): ExprRef | Tactic {
      if (isProbe(condition) && isTactic(onTrue) && isTactic(onFalse)) {
        return Cond(condition, onTrue, onFalse);
      }
      assert(isExpr(condition) && isExpr(onTrue) && isExpr(onFalse), 'Mixed expressions and goals');
      return _toExpr(Z3.mk_ite(ctx.ptr, condition.ptr, onTrue.ast, onFalse.ast));
    }

    function Distinct(...exprs: BoolRef[]): BoolRef {
      assert(exprs.length > 0, "Can't make Distinct ouf of nothing");

      const ctx = exprs[0].ctx;
      return new BoolRefImpl(
        Z3.mk_distinct(
          ctx.ptr,
          exprs.map(expr => expr.ptr),
        ),
      );
    }

    function Const<S extends SortRef>(name: string, sort: S): SortToExpr<S> {
      return _toExpr(Z3.mk_const(ctx.ptr, _toSymbol(name), sort.ptr)) as SortToExpr<S>;
    }

    function Consts<S extends SortRef>(names: string | string[], sort: S): SortToExpr<S>[] {
      if (typeof names === 'string') {
        names = names.split(' ');
      }
      return names.map(name => Const(name, sort));
    }

    function FreshConst<S extends SortRef>(sort: S, prefix: string = 'c'): SortToExpr<S> {
      return _toExpr(Z3.mk_fresh_const(sort.ctx.ptr, prefix, sort.ptr)) as SortToExpr<S>;
    }

    function Var<S extends SortRef>(idx: number, sort: S): SortToExpr<S> {
      return _toExpr(Z3.mk_bound(sort.ctx.ptr, idx, sort.ptr)) as SortToExpr<S>;
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
      return new BoolRefImpl(Z3.mk_implies(ctx.ptr, a.ptr, b.ptr));
    }

    function Xor(a: BoolRef, b: BoolRef) {
      return new BoolRefImpl(Z3.mk_xor(ctx.ptr, a.ptr, b.ptr));
    }

    function Not(a: Probe): Probe;
    function Not(a: BoolRef): BoolRef;
    function Not(a: BoolRef | Probe): BoolRef | Probe {
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
        return new BoolRefImpl(
          Z3.mk_or(
            ctx.ptr,
            args.map(arg => (arg as BoolRef).ptr),
          ),
        );
      }
    }

    function Cond(probe: Probe, onTrue: Tactic, onFalse: Tactic): Tactic {
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
      isProbe,
      isTactic,
      isPattern,
      /*
      isQuantifier,
      isForAll,
      isExists,
      isLambda,
      */
      eqIdentity,
      getVarIndex,

      // Classes
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
      Xor,
      Not,
      And,
      Or,
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

    createContext,
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
      result &&= premise(arg);
    }
  }
  return result;
}
