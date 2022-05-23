import {
  Z3_ast,
  Z3_ast_kind,
  Z3_ast_map,
  Z3_ast_print_mode,
  Z3_ast_vector,
  Z3_context,
  Z3_decl_kind,
  Z3_error_code,
  Z3_func_decl,
  Z3_parameter_kind,
  Z3_probe,
  Z3_sort,
  Z3_sort_kind,
  Z3_symbol,
  Z3_symbol_kind,
  Z3_tactic
} from "../build/wrapper";

type ConfigParams = {
  proof: boolean;
  debug_ref_count: boolean;
  trace: boolean;
  trace_file_name: string;
  timeout: number;
  well_sorted_check: boolean;
  auto_config: boolean;
  model: boolean;
  model_validate: boolean;
  unsat_core: boolean;
  encoding: "unicode" | "bmp" | "ascii";
};

export type Z3Core = Awaited<
  ReturnType<typeof import("../build/wrapper")["init"]>
>["Z3"];

export type {
  Context,
  Ast,
  Sort,
  FuncDecl,
  Expr,
  BoolSort,
  BoolExpr,
  Probe,
  Tactic,
  AstVector,
  AstMap,
};

declare class Context {
  readonly __typename: "Context";

  readonly ref: Z3_context;

  constructor(params?: Partial<ConfigParams>);

  interrupt(): void;
}

declare class Ast<Ref extends Z3_ast = Z3_ast> {
  readonly __typename:
    | "Ast"
    | Sort["__typename"]
    | FuncDecl["__typename"]
    | Expr["__typename"]
    | BoolSort["__typename"]
    | BoolExpr["__typename"];

  readonly ast: Ref;
  readonly ctx: Context;
  get id(): number;

  constructor(ast: Ref, ctx?: Context);
  eqIdentity(other: Ast): boolean;
  neqIdentity(other: Ast): boolean;
  sexpr(): string;
  hash(): number;
  translate(target: Context): Ast;
}

declare class Sort extends Ast<Z3_sort> {
  readonly __typename: "Sort" | BoolSort["__typename"];

  kind(): Z3_sort_kind;
  subsort(other: Sort): boolean;
  cast(expr: Expr): Expr;
  name(): string | number;
  eqIdentity(other: Sort): boolean;
  neqIdentity(other: Sort): boolean;
}

declare class FuncDecl extends Ast<Z3_func_decl> {
  readonly __typename: "FuncDecl";

  name(): string | number;
  arity(): number;
  domain(i: number): Sort;
  range(): Sort;
  kind(): Z3_decl_kind;
  params(): (number | string | Z3_symbol | Sort | Expr | FuncDecl)[];
  call(...args: Expr[]): AnyExpr;
}

declare class Expr extends Ast<Z3_ast> {
  readonly __typename: "Expr" | BoolExpr["__typename"];

  sort(): Sort;
  eq(other: Expr): BoolExpr;
  neq(other: Expr): BoolExpr;
  params(): ReturnType<FuncDecl["params"]>;
  decl(): FuncDecl;
  numArgs(): number;
  arg(i: number): AnyExpr;
  children(): AnyExpr[];
}

declare class BoolSort extends Sort {
  readonly __typename: "BoolSort";

  cast(expr: Expr): BoolExpr;
  isInt(): true;
  isBool(): true;
}

declare class BoolExpr extends Expr {
  readonly __typename: "Bool";

  mul(other: BoolExpr): BoolExpr;
}

declare class Probe {
  readonly __typename: "Probe";

  readonly ctx: Context;
  readonly probe: Z3_probe;

  constructor(probe: Z3_probe, ctx?: Context);
}

declare class Tactic {
  readonly __typename: "Tactic";

  readonly ctx: Context;
  readonly tactic: Z3_tactic;

  constructor(tactic: Z3_tactic, ctx?: Context);
}

declare class AstVector<Item extends Ast = AnyAst> implements Iterable<Item> {
  readonly __typename: "AstVector";

  [Symbol.iterator](): Iterator<Item, any, undefined>;

  readonly ctx: Context;
  readonly vector: Z3_ast_vector;
  get length(): number;

  constructor();
  constructor(ctx: Context);
  constructor(vector: Z3_ast_vector);
  constructor(vector: Z3_ast_vector, ctx: Context);

  entries(): IterableIterator<[number, Item]>;
  keys(): IterableIterator<number>;
  values(): IterableIterator<Item>;
  get(i: number): Item;
  get(from: number, to: number): Item[];
  set(i: number, v: Item): void;
  push(v: Item): void;
  resize(size: number): void;
  has(v: Item): boolean;
  translate(otherCtx: Context): AstVector<Item>;
  sexpr(): string;
}

export class AssertionError extends Error {}

declare class AstMap<Key extends Ast = AnyAst, Value extends Ast = AnyAst> {
  readonly __typename: "AstMap";

  readonly ctx: Context;
  readonly map: Z3_ast_map;

  constructor();
  constructor(ctx: Context);
  constructor(map: Z3_ast_map);
  constructor(map: Z3_ast_map, ctx: Context);
}

type AnySort = Sort | BoolSort;
type AnyExpr = Expr | BoolExpr;
type AnyAst = AnyExpr | AnySort | Ast | FuncDecl;

type SortToExpr<Sort> = Sort extends BoolSort
  ? BoolExpr
  : Sort extends Sort
  ? Expr
  : never;

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
  throw new Error(
    "Unexpected code execution detected, should be caught at compile time"
  );
}

function assert(condition: boolean, reason?: string): asserts condition {
  if (!condition) {
    throw new AssertionError(reason ?? "Assertion failed");
  }
}

export function init(Z3: Z3Core) {
  const cleanup = new FinalizationRegistry<() => void>((callback) =>
    callback()
  );

  function _assertNoError(ctx: Context) {
    const code = Z3.get_error_code(ctx.ref);
    if (code !== Z3_error_code.Z3_OK) {
      throw new AssertionError(`Z3 Error: ${Z3.get_error_msg(ctx.ref, code)}`);
    }
  }

  function _getCtx(ctx?: Context): Context {
    if (ctx === undefined) {
      return mainCtx();
    }
    return ctx;
  }

  function _toSymbol(s: string | number, ctx?: Context) {
    if (typeof s === "number") {
      return Z3.mk_int_symbol(_getCtx(ctx).ref, s);
    } else {
      return Z3.mk_string_symbol(_getCtx(ctx).ref, s);
    }
  }
  function _symbolToPrimitive(ctx: Context, sym: Z3_symbol) {
    const kind = Z3.get_symbol_kind(ctx.ref, sym);
    switch (kind) {
      case Z3_symbol_kind.Z3_INT_SYMBOL:
        return Z3.get_symbol_int(ctx.ref, sym);
      case Z3_symbol_kind.Z3_STRING_SYMBOL:
        return Z3.get_symbol_string(ctx.ref, sym);
      default:
        assertExhaustive(kind);
    }
  }

  let _mainCtx: Context | undefined = undefined;
  function mainCtx(): Context {
    if (_mainCtx === undefined) {
      _mainCtx = new Context();
    }
    return _mainCtx;
  }

  function _toAstRef(ast: Z3_ast, ctx?: Context): AnyAst {
    ctx = _getCtx(ctx);
    switch (Z3.get_ast_kind(ctx.ref, ast)) {
      case Z3_ast_kind.Z3_SORT_AST:
        return _toSortRef(ast as Z3_sort, ctx);
      default:
        throw new Error("Not implemented");
    }
  }

  function _toSortRef(ast: Z3_sort, ctx?: Context): AnySort {
    ctx = _getCtx(ctx);
    switch (Z3.get_sort_kind(ctx.ref, ast)) {
      default:
        return new Sort(ast, ctx);
    }
  }

  function _toExprRef(ast: Z3_ast, ctx?: Context): AnyExpr {
    ctx = _getCtx(ctx);
    const kind = Z3.get_ast_kind(ctx.ref, ast);
    switch (kind) {
      default:
        return new Expr(ast, ctx);
    }
  }

  function _ctxFromArgList(
    args: unknown[],
    default_ctx?: Context
  ): Context | undefined {
    const ctx = args.reduce<Context | undefined>((ctx, arg) => {
      if (isAst(arg) || isProbe(arg)) {
        if (ctx === undefined) {
          return arg.ctx;
        } else {
          assert(ctx === arg.ctx, "Context mismatch");
        }
      }
      return ctx;
    }, undefined);
    if (ctx !== undefined && default_ctx !== undefined) {
      assert(ctx === default_ctx, "Context mismatch");
    }
    return ctx ?? default_ctx;
  }

  function _toProbe(p: Probe | Z3_probe, ctx?: Context): Probe {
    if (isProbe(p)) {
      return p;
    }
    return new Probe(p, ctx);
  }

  function _probeNary(
    f: (ctx: Z3_context, left: Z3_probe, right: Z3_probe) => Z3_probe,
    args: [Probe | Z3_probe, ...(Probe | Z3_probe)[]],
    ctx: Context
  ) {
    assert(args.length > 0, "At least one argument expected");
    let r = _toProbe(args[0]);
    for (let i = 1; i < args.length; i++) {
      r = new Probe(f(ctx.ref, r.probe, _toProbe(args[i], ctx).probe), ctx);
    }
    return r;
  }

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

  function setParam(key: string | Record<string, any>, value?: any) {
    if (typeof key === "string") {
      Z3.global_param_set(key, value.to_string());
    } else {
      assert(
        value === undefined,
        "Can't provide a Record and second parameter to set_param at the same time"
      );
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
    return obj instanceof Context;
  }

  function isAst(obj: unknown): obj is Ast {
    return obj instanceof Ast;
  }

  function isSort(obj: unknown): obj is Sort {
    return obj instanceof Sort;
  }

  function isFuncDecl(obj: unknown): obj is FuncDecl {
    return obj instanceof FuncDecl;
  }

  function isApp(obj: unknown): obj is Expr {
    if (!isExpr(obj)) {
      return false;
    }
    const kind = Z3.get_ast_kind(obj.ctx.ref, obj.ast);
    return (
      kind === Z3_ast_kind.Z3_NUMERAL_AST || kind === Z3_ast_kind.Z3_APP_AST
    );
  }

  function isConst(obj: unknown): obj is Expr {
    return isApp(obj) && obj.numArgs() === 0;
  }

  function isExpr(obj: unknown): obj is Expr {
    return obj instanceof ExprRefImpl;
  }

  function isVar(obj: unknown): obj is Expr {
    return (
      isExpr(obj) &&
      Z3.get_ast_kind(obj.ctx.ref, obj.ast) === Z3_ast_kind.Z3_VAR_AST
    );
  }

  function eqIdentity(a: Ast, b: Ast) {
    return a.eqIdentity(b);
  }

  function getVarIndex(obj: Expr): number {
    assert(isVar(obj), "Z3 bound variable expected");
    return Z3.get_index_value(obj.ctx.ref, obj.ast);
  }

  function isAppOf(obj: unknown, kind: Z3_decl_kind): boolean {
    return isApp(obj) && obj.decl().kind() === kind;
  }

  function isBool(obj: unknown): obj is BoolExpr {
    return obj instanceof BoolExpr;
  }

  function isTrue(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_TRUE);
  }

  function isFalse(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_FALSE);
  }

  function isAnd(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_AND);
  }

  function isOr(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_OR);
  }

  function isImplies(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_IMPLIES);
  }

  function isNot(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_NOT);
  }

  function isEq(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_EQ);
  }

  function isDistinct(obj: unknown): obj is BoolExpr {
    return isAppOf(obj, Z3_decl_kind.Z3_OP_DISTINCT);
  }

  function isProbe(obj: unknown): obj is Probe {
    return obj instanceof Probe;
  }

  function isTactic(obj: unknown): obj is Tactic {
    return obj instanceof Tactic;
  }

  class Context {
    declare readonly __typename: "Context";

    readonly ref: Z3_context;

    constructor(params?: Partial<ConfigParams>) {
      params = params ?? {};
      const cfg = Z3.mk_config();
      Object.entries(params).forEach(([key, value]) =>
        Z3.set_param_value(cfg, key, value.toString())
      );
      const ref = Z3.mk_context_rc(cfg);
      this.ref = ref;
      Z3.set_ast_print_mode(
        this.ref,
        Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT
      );
      Z3.del_config(cfg);

      cleanup.register(this, () => Z3.del_context(ref));
    }

    interrupt(): void {
      Z3.interrupt(this.ref);
    }
  }

  class Ast<Ref extends Z3_ast = Z3_ast> {
    declare readonly __typename: "Ast" | Sort["__typename"];

    public readonly ast: Ref;
    public readonly ctx: Context;

    constructor(ast: Ref, ctx?: Context) {
      const myCtx = _getCtx(ctx);
      this.ast = ast;
      this.ctx = myCtx;

      Z3.inc_ref(myCtx.ref, ast);
      cleanup.register(this, () => Z3.dec_ref(myCtx?.ref, ast));
    }

    get id() {
      return Z3.get_ast_id(this.ctx.ref, this.ast);
    }

    eqIdentity(other: Ast) {
      return Z3.is_eq_ast(this.ctx.ref, this.ast, other.ast);
    }

    neqIdentity(other: Ast) {
      return !this.eqIdentity(other);
    }

    sexpr() {
      return Z3.ast_to_string(this.ctx.ref, this.ast);
    }

    hash() {
      return Z3.get_ast_hash(this.ctx.ref, this.ast);
    }

    translate(target: Context) {
      return _toAstRef(
        Z3.translate(this.ctx.ref, this.ast, target.ref),
        this.ctx
      );
    }
  }

  class Sort extends Ast<Z3_sort> {
    declare readonly __typename: "Sort";

    kind() {
      return Z3.get_sort_kind(this.ctx.ref, this.ast);
    }

    subsort(other: Sort) {
      return false;
    }

    cast(expr: Expr): Expr {
      assert(expr.eqIdentity(expr.sort()), "Sort mismatch");
      return expr;
    }

    name() {
      return _symbolToPrimitive(
        this.ctx,
        Z3.get_sort_name(this.ctx.ref, this.ast)
      );
    }

    eqIdentity(other: Sort) {
      return Z3.is_eq_sort(this.ctx.ref, this.ast, other.ast);
    }

    neqIdentity(other: Sort) {
      return !this.eqIdentity(other);
    }
  }

  function DeclareSort(name: string | number, ctx?: Context): SortRef {
    const myCtx = _getCtx(ctx);
    return new SortRefImpl(
      Z3.mk_uninterpreted_sort(myCtx.ref, _toSymbol(name, myCtx))
    );
  }

  class FuncDeclRefImpl
    extends AstRefImpl<Z3_func_decl>
    implements FuncDeclRef
  {
    name() {
      return _symbolToPrimitive(
        this.ctx,
        Z3.get_decl_name(this.ctx.ref, this.ast)
      );
    }

    arity() {
      return Z3.get_arity(this.ctx.ref, this.ast);
    }

    domain(i: number) {
      assert(i < this.arity(), "Index out of bounds");
      return _toSortRef(Z3.get_domain(this.ctx.ref, this.ast, i), this.ctx);
    }

    range() {
      return _toSortRef(Z3.get_range(this.ctx.ref, this.ast));
    }

    kind() {
      return Z3.get_decl_kind(this.ctx.ref, this.ast);
    }

    params(): (
      | number
      | string
      | Z3_symbol
      | SortRefImpl
      | ExprRef
      | FuncDeclRef
    )[] {
      const n = Z3.get_decl_num_parameters(this.ctx.ref, this.ast);
      const result = [];
      for (let i = 0; i < n; i++) {
        const kind = Z3.get_decl_parameter_kind(this.ctx.ref, this.ast, i);
        switch (kind) {
          case Z3_parameter_kind.Z3_PARAMETER_INT:
            result.push(Z3.get_decl_int_parameter(this.ctx.ref, this.ast, i));
            break;
          case Z3_parameter_kind.Z3_PARAMETER_DOUBLE:
            result.push(
              Z3.get_decl_double_parameter(this.ctx.ref, this.ast, i)
            );
            break;
          case Z3_parameter_kind.Z3_PARAMETER_RATIONAL:
            result.push(
              Z3.get_decl_rational_parameter(this.ctx.ref, this.ast, i)
            );
            break;
          case Z3_parameter_kind.Z3_PARAMETER_SYMBOL:
            result.push(
              Z3.get_decl_symbol_parameter(this.ctx.ref, this.ast, i)
            );
            break;
          case Z3_parameter_kind.Z3_PARAMETER_SORT:
            result.push(
              new SortRefImpl(
                Z3.get_decl_sort_parameter(this.ctx.ref, this.ast, i)
              )
            );
            break;
          case Z3_parameter_kind.Z3_PARAMETER_AST:
            result.push(
              new ExprRefImpl(
                Z3.get_decl_ast_parameter(this.ctx.ref, this.ast, i),
                this.ctx
              )
            );
            break;
          case Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
            result.push(
              new FuncDeclRefImpl(
                Z3.get_decl_func_decl_parameter(this.ctx.ref, this.ast, i),
                this.ctx
              )
            );
            break;
          default:
            assertExhaustive(kind);
        }
      }
      return result;
    }

    call(...args: ExprRef[]) {
      assert(
        args.length === this.arity(),
        `Incorrect number of arguments to ${this}`
      );
      return _toExprRef(
        Z3.mk_app(
          this.ctx.ref,
          this.ast,
          args.map((arg, i) => this.domain(i).cast(arg).ast)
        )
      );
    }
  }

  function Function(
    name: string,
    ...signature: [SortRef, SortRef, ...SortRef[]]
  ): FuncDeclRef {
    const arity = signature.length - 1;
    const rng = signature[arity];
    const dom = [];
    for (let i = 0; i < arity; i++) {
      dom.push(signature[i].ast);
    }
    const ctx = rng.ctx;
    return new FuncDeclRefImpl(
      Z3.mk_func_decl(ctx.ref, _toSymbol(name, ctx), dom, rng.ast)
    );
  }

  function FreshFunction(
    ...signature: [SortRef, SortRef, ...SortRef[]]
  ): FuncDeclRef {
    const arity = signature.length - 1;
    const rng = signature[arity];
    const dom = [];
    for (let i = 0; i < arity; i++) {
      dom.push(signature[i].ast);
    }
    const ctx = rng.ctx;
    return new FuncDeclRefImpl(
      Z3.mk_fresh_func_decl(ctx.ref, "f", dom, rng.ast),
      ctx
    );
  }

  function RecFunction(
    name: string,
    ...signature: [SortRef, SortRef, ...SortRef[]]
  ): FuncDeclRef {
    const arity = signature.length - 1;
    const rng = signature[arity];
    const dom = [];
    for (let i = 0; i < arity; i++) {
      dom.push(signature[i].ast);
    }
    const ctx = rng.ctx;
    return new FuncDeclRefImpl(
      Z3.mk_rec_func_decl(ctx.ref, _toSymbol(name, ctx), dom, rng.ast),
      ctx
    );
  }

  function RecAddDefinition(f: FuncDeclRef, args: ExprRef[], body: ExprRef) {
    Z3.add_rec_def(
      body.ctx.ref,
      f.ast,
      args.map((arg) => arg.ast),
      body.ast
    );
  }

  class ExprRefImpl extends AstRefImpl<Z3_ast> implements ExprRef {
    sort() {
      return _toSortRef(Z3.get_sort(this.ctx.ref, this.ast));
    }

    eq(other: ExprRef) {
      return new BoolRefImpl(
        Z3.mk_eq(this.ctx.ref, this.ast, other.ast),
        this.ctx
      );
    }

    neq(other: ExprRef) {
      return new BoolRefImpl(
        Z3.mk_distinct(
          this.ctx.ref,
          [this, other].map((expr) => expr.ast)
        ),
        this.ctx
      );
    }

    params() {
      return this.decl().params();
    }

    decl(): FuncDeclRefImpl {
      assert(isApp(this), "Z3 application expected");
      return new FuncDeclRefImpl(
        Z3.get_app_decl(this.ctx.ref, Z3.to_app(this.ctx.ref, this.ast)),
        this.ctx
      );
    }

    numArgs(): number {
      assert(isApp(this), "Z3 applicaiton expected");
      return Z3.get_app_num_args(
        this.ctx.ref,
        Z3.to_app(this.ctx.ref, this.ast)
      );
    }

    arg(i: number): ReturnType<typeof _toExprRef> {
      assert(isApp(this), "Z3 applicaiton expected");
      assert(i < this.numArgs(), "Invalid argument index");
      return _toExprRef(
        Z3.get_app_arg(this.ctx.ref, Z3.to_app(this.ctx.ref, this.ast), i),
        this.ctx
      );
    }

    children(): ReturnType<typeof _toExprRef>[] {
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

  function If(condition: Probe, onTrue: Tactic, onFalse: Tactic): Tactic;
  function If<
    OnTrueRef extends ExprRef = ExprRef,
    OnFalseRef extends ExprRef = ExprRef
  >(
    condition: BoolExpr,
    onTrue: OnTrueRef,
    onFalse: OnFalseRef
  ): OnTrueRef | OnFalseRef;
  function If(
    condition: BoolExpr | Probe,
    onTrue: ExprRef | Tactic,
    onFalse: ExprRef | Tactic,
    ctx?: Context
  ): ExprRef | Tactic {
    if (isProbe(condition) && isTactic(onTrue) && isTactic(onFalse)) {
      return Cond(condition, onTrue, onFalse, ctx);
    }
    assert(
      isExpr(condition) && isExpr(onTrue) && isExpr(onFalse),
      "Mixed expressions and goals"
    );

    ctx = _getCtx(_ctxFromArgList([condition, onTrue, onFalse], ctx));
    assert(
      condition.ctx === onTrue.ctx && onTrue.ctx === onFalse.ctx,
      "Context mismatch"
    );
    return _toExprRef(
      Z3.mk_ite(ctx.ref, condition.ast, onTrue.ast, onFalse.ast),
      ctx
    );
  }

  function Distinct(...exprs: ExprRef[]): BoolExpr {
    assert(exprs.length > 0, "Can't make Distinct ouf of nothing");

    const ctx = exprs[0].ctx;
    return new BoolRefImpl(
      Z3.mk_distinct(
        ctx.ref,
        exprs.map((expr) => expr.ast)
      ),
      ctx
    );
  }

  function Const<Sort extends SortRef>(
    name: string,
    sort: Sort
  ): SortToExpr<Sort> {
    return _toExprRef(
      Z3.mk_const(sort.ctx.ref, _toSymbol(name, sort.ctx), sort.ast),
      sort.ctx
    ) as SortToExpr<Sort>;
  }

  function Consts<Sort extends SortRef>(
    names: string | string[],
    sort: Sort
  ): SortToExpr<Sort>[] {
    if (typeof names === "string") {
      names = names.split(" ");
    }
    return names.map((name) => Const(name, sort));
  }

  function FreshConst<Sort extends SortRef>(
    sort: Sort,
    prefix: string = "c"
  ): SortToExpr<Sort> {
    return _toExprRef(
      Z3.mk_fresh_const(sort.ctx.ref, prefix, sort.ast),
      sort.ctx
    ) as SortToExpr<Sort>;
  }

  function Var<Sort extends SortRef>(
    idx: number,
    sort: Sort
  ): SortToExpr<Sort> {
    return _toExprRef(
      Z3.mk_bound(sort.ctx.ref, idx, sort.ast),
      sort.ctx
    ) as SortToExpr<Sort>;
  }

  function RealVar(idx: number, ctx?: Context) {
    return Var(idx, RealSort(ctx));
  }

  function RealVarVector(
    count: number,
    ctx?: Context
  ): ReturnType<typeof RealVar>[] {
    const result = [];
    for (let i = 0; i < count; i++) {
      result.push(RealVar(i, ctx));
    }
    return result;
  }

  class BoolSortRefImpl extends SortRefImpl implements BoolSort {
    cast(other: ExprRef) {
      assert(
        this.eqIdentity(other.sort()),
        "Value cannot be converted into a Z3 Boolean value"
      );
      assert(other instanceof BoolRefImpl);
      return other;
    }

    subsort(other: SortRef) {
      return other instanceof ArithSortRef;
    }

    isInt(): true {
      return true;
    }

    isBool(): true {
      return true;
    }
  }

  class BoolRefImpl extends ExprRefImpl implements BoolExpr {
    sort() {
      return new BoolSortRefImpl(Z3.get_sort(this.ctx.ref, this.ast), this.ctx);
    }
    mul(other: BoolExpr) {
      return If(this, other, BoolVal(false));
    }
  }

  function BoolSort(ctx?: Context): BoolSort {
    ctx = _getCtx(ctx);
    return new BoolSortRefImpl(Z3.mk_bool_sort(ctx.ref), ctx);
  }

  function BoolVal(value: boolean, ctx?: Context): BoolExpr {
    ctx = _getCtx(ctx);
    if (value) {
      return new BoolRefImpl(Z3.mk_true(ctx.ref), ctx);
    }
    return new BoolRefImpl(Z3.mk_false(ctx.ref), ctx);
  }

  function Bool(name: string, ctx?: Context): BoolExpr {
    ctx = _getCtx(ctx);
    return new BoolRefImpl(
      Z3.mk_const(ctx.ref, _toSymbol(name), BoolSort(ctx).ast),
      ctx
    );
  }

  function Bools(names: string | string[], ctx?: Context): BoolExpr[] {
    ctx = _getCtx(ctx);
    if (typeof names === "string") {
      names = names.split(" ");
    }
    return names.map((name) => Bool(name, ctx));
  }

  function BoolVector(
    prefix: string,
    count: number,
    ctx?: Context
  ): BoolExpr[] {
    const result = [];
    for (let i = 0; i < count; i++) {
      result.push(Bool(`${prefix}__${i}`, ctx));
    }
    return result;
  }

  function FreshBool(prefix = "b", ctx?: Context): BoolExpr {
    ctx = _getCtx(ctx);
    return new BoolRefImpl(
      Z3.mk_fresh_const(ctx.ref, prefix, BoolSort(ctx).ast),
      ctx
    );
  }

  function Implies(a: BoolExpr, b: BoolExpr, ctx?: Context): BoolExpr {
    ctx = _getCtx(_ctxFromArgList([a, b], ctx));
    return new BoolRefImpl(Z3.mk_implies(ctx.ref, a.ast, b.ast), ctx);
  }

  function Xor(a: BoolExpr, b: BoolExpr, ctx?: Context): BoolExpr {
    ctx = _getCtx(_ctxFromArgList([a, b], ctx));
    return new BoolRefImpl(Z3.mk_xor(ctx.ref, a.ast, b.ast), ctx);
  }

  function Not(a: Probe, ctx?: Context): Probe;
  function Not(a: BoolExpr, ctx?: Context): BoolExpr;
  function Not(a: BoolExpr | Probe, ctx?: Context): BoolExpr | Probe {
    ctx = _getCtx(_ctxFromArgList([a], ctx));
    if (isProbe(a)) {
      return new ProbeImpl(Z3.probe_not(ctx.ref, a.probe), ctx);
    }
    return new BoolRefImpl(Z3.mk_not(ctx.ref, a.ast), ctx);
  }

  function And(): BoolExpr;
  function And(vector: AstVector<BoolExpr>): BoolExpr;
  function And(...args: BoolExpr[]): BoolExpr;
  function And(...args: [...BoolExpr[], Context]): BoolExpr;
  function And(...args: Probe[]): Probe;
  function And(...args: [...Probe[], Context]): Probe;
  function And(
    ...args: (AstVector | Probe | BoolExpr | Context)[]
  ): BoolExpr | Probe {
    let ctx: Context | undefined;
    const last_arg = args.length > 0 ? args[args.length - 1] : undefined;
    if (isContext(last_arg)) {
      ctx = last_arg;
      args = args.slice(0, -1);
    } else if (args.length === 1 && args[0] instanceof AstVectorImpl) {
      assert(ctx === undefined, "Provided AstVector and a context");
      ctx = args[0].ctx;
      args = [...args[0]];
    }
    ctx = _getCtx(_ctxFromArgList(args, ctx));

    // false if empty array
    const all_probes =
      args.reduce<boolean | undefined>((acc, arg) => {
        const arg_is_probe = isProbe(arg);
        if (acc !== undefined) {
          assert(arg_is_probe === acc, "Mixed expressions and probes");
        }
        return arg_is_probe;
      }, undefined) ?? false;

    if (all_probes) {
      return _probeNary(Z3.probe_and, args as [Probe, ...Probe[]], ctx);
    } else {
      // We need to check due to dynamic nature of AstVector
      args.forEach((arg) =>
        assert(isBool(arg), "Provided arguments aren't bools")
      );
      return new BoolRefImpl(
        Z3.mk_and(
          ctx.ref,
          args.map((arg) => (arg as BoolExpr).ast)
        ),
        ctx
      );
    }
  }

  function Or(): BoolExpr;
  function Or(vector: AstVector<BoolExpr>): BoolExpr;
  function Or(...args: BoolExpr[]): BoolExpr;
  function Or(...args: [...BoolExpr[], Context]): BoolExpr;
  function Or(...args: Probe[]): Probe;
  function Or(...args: [...Probe[], Context]): Probe;
  function Or(
    ...args: (AstVector | Probe | BoolExpr | Context)[]
  ): BoolExpr | Probe {
    let ctx: Context | undefined;
    const last_arg = args.length > 0 ? args[args.length - 1] : undefined;
    if (isContext(last_arg)) {
      ctx = last_arg;
      args = args.slice(0, -1);
    } else if (args.length === 1 && args[0] instanceof AstVectorImpl) {
      assert(ctx === undefined, "Provided AstVector and a context");
      ctx = args[0].ctx;
      args = [...args[0]];
    }
    ctx = _getCtx(_ctxFromArgList(args, ctx));

    // false if empty array
    const all_probes =
      args.reduce<boolean | undefined>((acc, arg) => {
        const arg_is_probe = isProbe(arg);
        if (acc !== undefined) {
          assert(arg_is_probe === acc, "Mixed expressions and probes");
        }
        return arg_is_probe;
      }, undefined) ?? false;

    if (all_probes) {
      return _probeNary(Z3.probe_or, args as [Probe, ...Probe[]], ctx);
    } else {
      // We need to check due to dynamic nature of AstVector
      args.forEach((arg) =>
        assert(isBool(arg), "Provided arguments aren't bools")
      );
      return new BoolRefImpl(
        Z3.mk_or(
          ctx.ref,
          args.map((arg) => (arg as BoolExpr).ast)
        ),
        ctx
      );
    }
  }

  function Cond(
    probe: Probe,
    onTrue: Tactic,
    onFalse: Tactic,
    ctx?: Context
  ): Tactic {}

  class ProbeImpl implements Probe {
    public readonly ctx: Context;

    constructor(public readonly probe: Z3_probe, ctx?: Context) {
      this.ctx = _getCtx(ctx);
    }
  }

  class ArithSortRef extends SortRefImpl {}

  class AstVectorImpl<Item extends AstRef = AnyAst> implements AstVector<Item> {
    readonly ctx: Context;
    readonly vector: Z3_ast_vector;

    constructor();
    constructor(ctx: Context);
    constructor(vector: Z3_ast_vector);
    constructor(vector: Z3_ast_vector, ctx: Context);
    constructor(vector?: Z3_ast_vector | Context, ctx?: Context) {
      let myCtx: Context;
      if (isContext(vector)) {
        assert(ctx === undefined, "Two Contexes provided");
        myCtx = vector;
        vector = undefined;
      } else {
        myCtx = _getCtx(ctx);
      }
      const myVector = vector ?? Z3.mk_ast_vector(myCtx.ref);

      this.ctx = myCtx;
      this.vector = myVector;

      Z3.ast_vector_inc_ref(myCtx.ref, myVector);

      cleanup.register(this, () => Z3.ast_vector_dec_ref(myCtx.ref, myVector));
    }

    get length(): number {
      return Z3.ast_vector_size(this.ctx.ref, this.vector);
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
        return _toAstRef(
          Z3.ast_vector_get(this.ctx.ref, this.vector, from),
          this.ctx
        ) as Item;
      }

      if (to < 0) {
        to += length;
      }
      if (to >= length) {
        throw new RangeError();
      }

      const result: Item[] = [];
      for (let i = from; i < to; i++) {
        result.push(
          _toAstRef(
            Z3.ast_vector_get(this.ctx.ref, this.vector, i),
            this.ctx
          ) as Item
        );
      }
      return result;
    }

    set(i: number, v: Item): void {
      if (i >= this.length) {
        throw new RangeError();
      }
      Z3.ast_vector_set(this.ctx.ref, this.vector, i, v.ast);
    }

    push(v: Item): void {
      Z3.ast_vector_push(this.ctx.ref, this.vector, v.ast);
    }

    resize(size: number): void {
      Z3.ast_vector_resize(this.ctx.ref, this.vector, size);
    }

    has(v: Item): boolean {
      for (const item of this.values()) {
        if (item.eqIdentity(v)) {
          return true;
        }
      }
      return false;
    }

    translate(otherCtx: Context): AstVector<Item> {
      return new AstVectorImpl(
        Z3.ast_vector_translate(otherCtx.ref, this.vector, this.ctx.ref),
        otherCtx
      );
    }

    sexpr(): string {
      return Z3.ast_vector_to_string(this.ctx.ref, this.vector);
    }
  }

  class AstMapImpl<Key extends AstRef = AnyAst, Value extends AstRef = AnyAst> {
    readonly ctx: Context;
    readonly map: Z3_ast_map;

    constructor();
    constructor(ctx: Context);
    constructor(map: Z3_ast_map);
    constructor(map: Z3_ast_map, ctx: Context);
    constructor(map?: Z3_ast_map | Context, ctx?: Context) {
      let myCtx: Context;
      if (isContext(map)) {
        assert(ctx === undefined, "Two Contexes provided");
        myCtx = map;
        map = undefined;
      } else {
        myCtx = _getCtx(ctx);
      }
      const myMap = map ?? Z3.mk_ast_map(myCtx.ref);

      this.ctx = myCtx;
      this.map = myMap;

      Z3.ast_map_inc_ref(myCtx.ref, myMap);

      cleanup.register(this, () => Z3.ast_map_dec_ref(myCtx.ref, myMap));
    }
  }

  return {
    mainCtx,
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
    eqIdentity,
    getVarIndex,
    Context,
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
    RealVar,
    RealVarVector,
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
    AstVector,
    AstMap,
  };
}
