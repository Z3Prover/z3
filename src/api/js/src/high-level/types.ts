import {
  Z3_ast,
  Z3_ast_map,
  Z3_ast_vector,
  Z3_context,
  Z3_decl_kind,
  Z3_func_decl,
  Z3_func_interp,
  Z3_model,
  Z3_pattern,
  Z3_probe,
  Z3_solver,
  Z3_sort,
  Z3_sort_kind,
  Z3_symbol,
  Z3_tactic,
} from '../low-level';

export type AnySort<Name extends string = any> = Sort<Name> | BoolSort<Name> | ArithSort<Name> | BitVecSort<Name>;
export type AnyExpr<Name extends string = any> =
  | Expr<Name>
  | Bool<Name>
  | Pattern<Name>
  | Quantifier<Name>
  | Arith<Name>
  | IntNum<Name>
  | RatNum<Name>
  | BitVec<number, Name>;
export type AnyAst<Name extends string = any> = AnyExpr<Name> | AnySort<Name> | FuncDecl<Name>;

export type SortToExprMap<S extends AnySort<Name>, Name extends string = any> = S extends BoolSort
  ? Bool<Name>
  : S extends ArithSort<Name>
  ? Arith<Name>
  : S extends BitVecSort<infer Size, Name>
  ? BitVec<Size, Name>
  : S extends Sort<Name>
  ? Expr<Name>
  : never;

export type CoercibleToExprMap<S extends CoercibleToExpr<Name>, Name extends string = any> = S extends bigint
  ? IntNum<Name>
  : S extends number | CoercibleRational
  ? RatNum<Name>
  : S extends boolean
  ? Bool<Name>
  : S extends Expr<Name>
  ? S
  : never;

export type CoercibleRational = { numerator: bigint | number; denominator: bigint | number };

export type CoercibleToExpr<Name extends string = any> = number | bigint | boolean | CoercibleRational | Expr<Name>;

export class Z3Error extends Error {}
export class Z3AssertionError extends Z3Error {}

export const sat = Symbol('Solver found a solution');
export const unsat = Symbol("Solver didn't find a solution");
export const unknown = Symbol("Solver couldn't reason about the assumptions");
export type CheckSatResult = typeof sat | typeof unsat | typeof unknown;

export interface ContextCtor {
  new <Name extends string>(name: Name, options?: Record<string, any>): Context<Name>;
}
export interface Context<Name extends string = any> {
  readonly __typename: 'Context';

  readonly ptr: Z3_context;
  readonly name: Name;

  ///////////////
  // Functions //
  ///////////////
  interrupt(): void;
  isAst(obj: unknown): obj is Ast<Name>;
  isSort(obj: unknown): obj is Sort<Name>;
  isFuncDecl(obj: unknown): obj is FuncDecl<Name>;
  isApp(obj: unknown): boolean;
  isConst(obj: unknown): boolean;
  isExpr(obj: unknown): obj is Expr<Name>;
  isVar(obj: unknown): boolean;
  isAppOf(obj: unknown, kind: Z3_decl_kind): boolean;
  isBool(obj: unknown): obj is Bool<Name>;
  isTrue(obj: unknown): boolean;
  isFalse(obj: unknown): boolean;
  isAnd(obj: unknown): boolean;
  isOr(obj: unknown): boolean;
  isImplies(obj: unknown): boolean;
  isNot(obj: unknown): boolean;
  isEq(obj: unknown): boolean;
  isDistinct(obj: unknown): boolean;
  isArith(obj: unknown): obj is Arith<Name>;
  isArithSort(obj: unknown): obj is ArithSort<Name>;
  isInt(obj: unknown): boolean;
  isIntVal(obj: unknown): obj is IntNum<Name>;
  isIntSort(obj: unknown): boolean;
  isReal(obj: unknown): boolean;
  isRealVal(obj: unknown): obj is RatNum<Name>;
  isRealSort(obj: unknown): boolean;
  isProbe(obj: unknown): obj is Probe<Name>;
  isTactic(obj: unknown): obj is Tactic<Name>;
  isPattern(obj: unknown): obj is Pattern<Name>;
  isAstVector(obj: unknown): obj is AstVector<AnyAst<Name>, Name>;
  /*
  isQuantifier(obj: unknown): obj is QuantifierRef;
  isForAll(obj: unknown): obj is QuantifierRef;
  isExists(obj: unknown): obj is QuantifierRef;
  isLambda(obj: unknown): obj is LambdaRef<AnySort>;
  */
  eqIdentity(a: Ast<Name>, b: Ast<Name>): boolean;
  getVarIndex(obj: Expr<Name>): number;
  from(primitive: boolean): Bool<Name>;
  from(primitive: number | CoercibleRational): RatNum<Name>;
  from(primitive: bigint): IntNum<Name>;
  from<E extends Expr<Name>>(expr: E): E;
  from(value: CoercibleToExpr<Name>): AnyExpr<Name>;

  /////////////
  // Classes //
  /////////////
  readonly Solver: new (logic?: string) => Solver<Name>;
  readonly Model: new () => Model<Name>;
  readonly AstVector: new <Item extends Ast<Name> = AnyAst<Name>>() => AstVector<Item, Name>;
  readonly AstMap: new <Key extends Ast = AnyAst, Value extends Ast = AnyAst>() => AstMap<Key, Value, Name>;
  readonly Tactic: new (name: string) => Tactic<Name>;

  /////////////
  // Objects //
  /////////////
  readonly Sort: SortStatics<Name>;
  readonly Function: FuncDeclStatics<Name>;
  readonly RecFunc: RecFuncStatics<Name>;
  readonly Bool: BoolStatics<Name>;
  readonly Int: IntStatics<Name>;
  readonly Real: RealStatics<Name>;

  ////////////////
  // Operations //
  ////////////////
  Const<S extends Sort<Name>>(name: string, sort: S): SortToExprMap<S, Name>;
  Consts<S extends Sort<Name>>(name: string | string[], sort: S): SortToExprMap<S, Name>[];
  FreshConst<S extends Sort<Name>>(sort: S, prefix?: string): SortToExprMap<S, Name>;
  Var<S extends Sort<Name>>(idx: number, sort: S): SortToExprMap<S, Name>;
  // Booleans
  If(condition: Probe<Name>, onTrue: Tactic<Name>, onFalse: Tactic<Name>): Tactic<Name>;
  If<OnTrueRef extends CoercibleToExpr<Name>, OnFalseRef extends CoercibleToExpr<Name>>(
    condition: Bool<Name>,
    onTrue: OnTrueRef,
    onFalse: OnFalseRef,
  ): CoercibleToExprMap<OnTrueRef | OnFalseRef, Name>;
  Distinct(...args: Expr<Name>[]): Bool<Name>;
  Implies(a: Bool<Name>, b: Bool<Name>): Bool<Name>;
  Eq(a: Expr<Name>, b: Expr<Name>): Bool<Name>;
  Xor(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name>;
  Not(a: Probe<Name>): Probe<Name>;
  Not(a: Bool<Name> | boolean): Bool<Name>;
  And(): Bool<Name>;
  And(vector: AstVector<Bool<Name>, Name>): Bool<Name>;
  And(...args: (Bool<Name> | boolean)[]): Bool<Name>;
  And(...args: Probe<Name>[]): Probe<Name>;
  Or(): Bool<Name>;
  Or(vector: AstVector<Bool<Name>, Name>): Bool<Name>;
  Or(...args: (Bool<Name> | boolean)[]): Bool<Name>;
  Or(...args: Probe<Name>[]): Probe<Name>;
  // Arithmetic
  ToReal(expr: Arith<Name>): Arith<Name>;
  ToInt(expr: Arith<Name>): Arith<Name>;
  IsInt(expr: Arith<Name>): Bool<Name>;
  Sqrt(a: Arith<Name> | number | bigint | string | CoercibleRational): Arith<Name>;
  Cbrt(a: Arith<Name> | number | bigint | string | CoercibleRational): Arith<Name>;
  /*
  MultiPattern(...args: [ExprRef, ...ExprRef[]]): PatternRef;
  ForAll(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Exists(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Lambda<Sort extends SortRef>(vars: ExprRef | ExprRef[], body: ExprRef<Sort>): LambdaRef<Sort>;
  */
}

export interface Ast<Name extends string = any, Ptr = unknown> {
  readonly __typename: 'AstRef' | Sort['__typename'] | FuncDecl['__typename'] | Expr['__typename'];

  readonly ctx: Context<Name>;
  readonly ptr: Ptr;
  /** @virtual */
  get ast(): Z3_ast;
  /** @virtual */
  get id(): number;

  eqIdentity(other: Ast<Name>): boolean;
  neqIdentity(other: Ast<Name>): boolean;
  sexpr(): string;
  hash(): number;
}

export interface SolverCtor<Name extends string> {
  new (): Solver<Name>;
}
export interface Solver<Name extends string = any> {
  readonly __typename: 'Solver';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_solver;

  /* TODO(ritave): Decide on how to discern between integer and float paramaters
  set(key: string, value: any): void;
  set(params: Record<string, any>): void;
  */
  push(): void;
  pop(num?: number): void;
  numScopes(): number;
  reset(): void;
  add(...exprs: (Bool<Name> | AstVector<Bool<Name>, Name>)[]): void;
  addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string): void;
  assertions(): AstVector<Bool<Name>, Name>;
  check(...exprs: (Bool<Name> | AstVector<Bool<Name>, Name>)[]): Promise<CheckSatResult>;
  model(): Model<Name>;
}

export interface ModelCtor<Name extends string> {
  new (): Model<Name>;
}
export interface Model<Name extends string = any> extends Iterable<FuncDecl<Name>> {
  readonly __typename: 'Model';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_model;

  get length(): number;

  entries(): IterableIterator<[number, FuncDecl<Name>]>;
  keys(): IterableIterator<number>;
  values(): IterableIterator<FuncDecl<Name>>;
  decls(): FuncDecl<Name>[];
  sexpr(): string;
  eval(expr: Bool<Name>, modelCompletion?: boolean): Bool<Name>;
  eval(expr: Arith<Name>, modelCompletion?: boolean): Arith<Name>;
  eval(expr: Expr<Name>, modelCompletion?: boolean): Expr<Name>;
  get(i: number): FuncDecl<Name>;
  get(from: number, to: number): FuncDecl[];
  get(declaration: FuncDecl<Name>): FuncInterp<Name> | Expr<Name>;
  get(constant: Expr<Name>): Expr<Name>;
  get(sort: Sort<Name>): AstVector<AnyExpr<Name>, Name>;
}

export interface SortStatics<Name extends string> {
  declare(name: string): Sort<Name>;
}
export interface Sort<Name extends string = any> extends Ast<Name, Z3_sort> {
  readonly __typename: 'SortRef' | BoolSort['__typename'] | ArithSort['__typename'] | BitVecSort['__typename'];

  kind(): Z3_sort_kind;
  subsort(other: Sort<Name>): boolean;
  cast(expr: CoercibleToExpr<Name>): Expr<Name>;
  name(): string | number;
}

export interface FuncInterp<Name extends string = any> {
  readonly __typename: 'FuncInterp';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_func_interp;
}

export type FuncDeclSignature<Name extends string> = [Sort<Name>, Sort<Name>, ...Sort<Name>[]];
export interface FuncDeclStatics<Name extends string> {
  declare(name: string, ...signature: FuncDeclSignature<Name>): FuncDecl<Name>;
  fresh(...signature: FuncDeclSignature<Name>): FuncDecl<Name>;
}
export interface RecFuncStatics<Name extends string> {
  declare(name: string, ...signature: FuncDeclSignature<Name>): FuncDecl<Name>;
  addDefinition(f: FuncDecl<Name>, args: Expr<Name>[], body: Expr<Name>): void;
}
export interface FuncDecl<Name extends string = any> extends Ast<Name, Z3_func_decl> {
  readonly __typename: 'FuncDeclRef';

  name(): string | number;
  arity(): number;
  domain(i: number): Sort<Name>;
  range(): Sort<Name>;
  kind(): Z3_decl_kind;
  params(): (number | string | Z3_symbol | Sort<Name> | Expr<Name> | FuncDecl<Name>)[];
  call(...args: Expr<Name>[]): AnyExpr<Name>;
}

export interface Expr<Name extends string = any, S extends Sort<Name> = AnySort<Name>, Ptr = unknown>
  extends Ast<Name, Ptr> {
  readonly __typename:
    | 'ExprRef'
    | Bool['__typename']
    | Pattern['__typename']
    | Quantifier['__typename']
    | Lambda['__typename']
    | Arith['__typename']
    | BitVec['__typename'];

  sort(): S;
  eq(other: CoercibleToExpr<Name>): Bool<Name>;
  neq(other: CoercibleToExpr<Name>): Bool<Name>;
  params(): ReturnType<FuncDecl<Name>['params']>;
  decl(): FuncDecl<Name>;
  numArgs(): number;
  arg(i: number): AnyExpr<Name>;
  children(): AnyExpr<Name>[];
}

export interface BoolSort<Name extends string = any> extends Sort<Name> {
  readonly __typename: 'BoolSortRef';

  cast(expr: Bool<Name> | boolean): Bool<Name>;
  cast(expr: CoercibleToExpr<Name>): never;
}

export interface BoolStatics<Name extends string = any> {
  sort(): BoolSort<Name>;

  const(name: string): Bool<Name>;
  consts(names: string | string[]): Bool<Name>[];
  vector(prefix: string, count: number): Bool<Name>[];
  fresh(prefix?: string): Bool<Name>;

  val(value: boolean): Bool<Name>;
}
export interface Bool<Name extends string = any> extends Expr<Name, BoolSort<Name>, Z3_ast> {
  readonly __typename: 'BoolRef';

  not(): Bool<Name>;
  and(other: Bool<Name> | boolean): Bool<Name>;
  or(other: Bool<Name> | boolean): Bool<Name>;
  xor(other: Bool<Name> | boolean): Bool<Name>;
}

export interface Pattern<Name extends string = any> extends Expr<Name, Sort<Name>, Z3_pattern> {
  readonly __typename: 'PatternRef';
}

export interface Quantifier<Name extends string = any> extends Expr<Name, BoolSort<Name>, Z3_ast> {
  readonly __typename: 'QuantifierRef';

  weight(): number;
  numPatterns(): number;
  pattern(i: number): Pattern<Name>;
  numNoPatterns(): number;
  noPattern(i: number): AnyExpr<Name>;
  body(): AnyExpr<Name>;
  varName(i: number): string | number;
  varSort(i: number): AnySort<Name>;
  children(): [AnyExpr<Name>];
}

export interface Lambda<Name extends string = any, S extends Sort<Name> = AnySort<Name>> extends Expr<Name, S, Z3_ast> {
  readonly __typename: 'LambdaRef';

  get(expr: Expr<Name>): Expr<Name>;
  body(): AnyExpr<Name>;
}

export interface ArithSort<Name extends string = any> extends Sort<Name> {
  readonly __typename: 'ArithSortRef';

  cast(other: bigint | number | string): IntNum<Name> | RatNum<Name>;
  cast(other: CoercibleRational | RatNum<Name>): RatNum<Name>;
  cast(other: IntNum<Name>): IntNum<Name>;
  cast(other: bigint | number | string | Bool<Name> | Arith<Name> | CoercibleRational): Arith<Name>;
  cast(other: CoercibleToExpr<Name> | string): never;
}

export interface IntStatics<Name extends string> {
  sort(): ArithSort<Name>;

  const(name: string): Arith<Name>;
  consts(names: string | string[]): Arith<Name>[];
  vector(prefix: string, count: number): Arith<Name>[];
  fresh(prefix?: string): Arith<Name>;

  val(value: bigint | number | string): IntNum<Name>;
}
export interface RealStatics<Name extends string> {
  sort(): ArithSort<Name>;

  const(name: string): Arith<Name>;
  consts(names: string | string[]): Arith<Name>[];
  vector(prefix: string, count: number): Arith<Name>[];
  fresh(prefix?: string): Arith<Name>;

  val(value: number | string | bigint | CoercibleRational): RatNum<Name>;
}
export interface Arith<Name extends string = any> extends Expr<Name, ArithSort<Name>, Z3_ast> {
  readonly __typename: 'ArithRef' | IntNum['__typename'] | RatNum['__typename'];

  add(other: Arith<Name> | number | bigint | string): Arith<Name>;
  mul(other: Arith<Name> | number | bigint | string): Arith<Name>;
  sub(other: Arith<Name> | number | bigint | string): Arith<Name>;
  pow(exponent: Arith<Name> | number | bigint | string): Arith<Name>;
  div(other: Arith<Name> | number | bigint | string): Arith<Name>;
  mod(other: Arith<Name> | number | bigint | string): Arith<Name>;
  neg(): Arith<Name>;
  le(other: Arith<Name> | number | bigint | string): Bool<Name>;
  lt(other: Arith<Name> | number | bigint | string): Bool<Name>;
  gt(other: Arith<Name> | number | bigint | string): Bool<Name>;
  ge(other: Arith<Name> | number | bigint | string): Bool<Name>;
}

export interface IntNum<Name extends string = any> extends Arith<Name> {
  readonly __typename: 'IntNumRef';

  get value(): bigint;
  asString(): string;
  asBinary(): string;
}

export interface RatNum<Name extends string = any> extends Arith<Name> {
  readonly __typename: 'RatNumRef';

  get value(): { numerator: bigint; denominator: bigint };
  numerator(): IntNum<Name>;
  denominator(): IntNum<Name>;
  asNumber(): number;
  asDecimal(prec?: number): string;
  asString(): string;
}

export interface BitVecSort<Size extends number = number, Name extends string = any> extends Sort<Name> {
  readonly __typename: 'BitVecSortRef';

  get size(): Size;

  cast(other: number | bigint): BitVec<Size, Name>;
  cast(other: CoercibleToExpr<Name>): Expr<Name>;
}

type CoercibleToBitVec<Size extends number = number, Name extends string = any> = bigint | number | BitVec<Size, Name>;
export interface BitVec<Size extends number = number, Name extends string = any>
  extends Expr<Name, BitVecSort<Size, Name>, Z3_ast> {
  readonly __typename: 'BitVecRef';

  get size(): Size;

  add(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  mul(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  sub(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  sdiv(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  udiv(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  smod(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  urem(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  srem(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  neg(): BitVec<Size, Name>;

  or(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  and(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  xor(other: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  shr(count: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  lshr(count: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  shl(count: CoercibleToBitVec<Size, Name>): BitVec<Size, Name>;
  not(): BitVec<Size, Name>;

  sle(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  ule(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  slt(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  ult(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  sge(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  uge(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  sgt(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
  ugt(other: CoercibleToBitVec<Size, Name>): Bool<Name>;
}

export interface Probe<Name extends string = any> {
  readonly __typename: 'Probe';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_probe;
}

export interface TacticCtor<Name extends string> {
  new (name: string): Tactic<Name>;
}
export interface Tactic<Name extends string = any> {
  readonly __typename: 'Tactic';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_tactic;
}

export interface AstVectorCtor<Name extends string> {
  new <Item extends Ast<Name> = AnyAst<Name>>(): AstVector<Item, Name>;
}
export interface AstVector<Item extends Ast<Name> = AnyAst, Name extends string = any> extends Iterable<Item> {
  readonly __typename: 'AstVector';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_ast_vector;
  get length(): number;

  entries(): IterableIterator<[number, Item]>;
  keys(): IterableIterator<number>;
  values(): IterableIterator<Item>;
  get(i: number): Item;
  get(from: number, to: number): Item[];
  set(i: number, v: Item): void;
  push(v: Item): void;
  resize(size: number): void;
  has(v: Item): boolean;
  sexpr(): string;
}

export interface AstMapCtor<Name extends string> {
  new <Key extends Ast = AnyAst, Value extends Ast = AnyAst>(): AstMap<Key, Value, Name>;
}
export interface AstMap<Key extends Ast<Name> = AnyAst, Value extends Ast = AnyAst, Name extends string = any> {
  readonly __typename: 'AstMap';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_ast_map;
}

type QuantifierOptions = {
  qid: string;
  skid: string;
  patterns: Pattern[];
  noPatterns: Expr[];
};

export type Z3HighLevel = {
  // Global functions
  enableTrace(tag: string): void;
  disableTrace(tag: string): void;
  getVersion(): {
    major: number;
    minor: number;
    build_number: number;
    revision_number: number;
  };
  getVersionString(): string;
  getFullVersion(): string;
  openLog(filename: string): boolean;
  appendLog(s: string): void;
  setParam(key: string, value: any): void;
  setParam(key: Record<string, any>): void;
  resetParams(): void;
  getParam(name: string): string | null;
  isContext(obj: unknown): obj is Context;

  Context: ContextCtor;
};
