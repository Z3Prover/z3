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

export type AnySort<Name extends string = any> = SortRef<Name> | BoolSortRef<Name>;
export type AnyExpr<Name extends string = any> = ExprRef<Name> | BoolRef<Name> | PatternRef<Name> | QuantifierRef<Name>;
export type AnyAst<Name extends string = any> = AnyExpr<Name> | AnySort<Name> | AstRef<Name> | FuncDeclRef<Name>;

export type SortToExprMap<S, Name extends string = any> = S extends BoolSortRef
  ? BoolRef<Name>
  : S extends SortRef
  ? ExprRef<Name>
  : S extends ArithSortRef
  ? ArithRef<Name>
  : never;

export type CoercibleToExprMap<S, Name extends string = any> = S extends bigint | number
  ? ArithRef<Name>
  : S extends boolean
  ? BoolRef<Name>
  : S extends ExprRef
  ? S
  : never;

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
  isAst(obj: unknown): obj is AstRef<Name>;
  isSort(obj: unknown): obj is SortRef<Name>;
  isFuncDecl(obj: unknown): obj is FuncDeclRef<Name>;
  isApp(obj: unknown): obj is ExprRef<Name>;
  isConst(obj: unknown): obj is ExprRef<Name>;
  isExpr(obj: unknown): obj is ExprRef<Name>;
  isVar(obj: unknown): obj is ExprRef<Name>;
  isAppOf(obj: unknown, kind: Z3_decl_kind): boolean;
  isBool(obj: unknown): obj is BoolRef<Name>;
  isTrue(obj: unknown): obj is BoolRef<Name>;
  isFalse(obj: unknown): obj is BoolRef<Name>;
  isAnd(obj: unknown): obj is BoolRef<Name>;
  isOr(obj: unknown): obj is BoolRef<Name>;
  isImplies(obj: unknown): obj is BoolRef<Name>;
  isNot(obj: unknown): obj is BoolRef<Name>;
  isEq(obj: unknown): obj is BoolRef<Name>;
  isDistinct(obj: unknown): obj is BoolRef<Name>;
  isArith(obj: unknown): obj is ArithRef<Name>;
  isInt(obj: unknown): obj is ArithRef<Name>;
  isIntSort(obj: unknown): obj is ArithSortRef<Name>;
  isProbe(obj: unknown): obj is Probe<Name>;
  isTactic(obj: unknown): obj is Tactic<Name>;
  isPattern(obj: unknown): obj is PatternRef<Name>;
  isAstVector(obj: unknown): obj is AstVector<AnyAst<Name>, Name>;
  /*
  isQuantifier(obj: unknown): obj is QuantifierRef;
  isForAll(obj: unknown): obj is QuantifierRef;
  isExists(obj: unknown): obj is QuantifierRef;
  isLambda(obj: unknown): obj is LambdaRef<AnySort>;
  */
  eqIdentity(a: AstRef<Name>, b: AstRef<Name>): boolean;
  getVarIndex(obj: ExprRef<Name>): number;
  getValue(obj: BoolRef<Name>): boolean | null;
  getValue(obj: ArithRef<Name>): number | bigint | null;
  getValue(obj: ExprRef<Name>): boolean | number | bigint | null;
  from(primitive: boolean): BoolRef<Name>;
  from(primitive: number | bigint): ArithRef<Name>;
  from(expr: ExprRef<Name>): ExprRef<Name>;
  from(expr: CoercibleToExpr<Name>): AnyExpr<Name>;

  /////////////
  // Classes //
  /////////////
  readonly Solver: new () => Solver<Name>;
  readonly Model: new () => Model<Name>;
  readonly AstVector: new <Item extends AstRef<Name> = AnyAst<Name>>() => AstVector<Item, Name>;
  readonly AstMap: new <Key extends AstRef = AnyAst, Value extends AstRef = AnyAst>() => AstMap<Key, Value, Name>;
  readonly Tactic: new (name: string) => Tactic<Name>;

  ////////////////
  // Operations //
  ////////////////
  DeclareSort(name: string | number): SortRef<Name>;
  Function(name: string, ...signature: [SortRef<Name>, SortRef<Name>, ...SortRef<Name>[]]): FuncDeclRef<Name>;
  FreshFunction(...signature: [SortRef<Name>, SortRef<Name>, ...SortRef<Name>[]]): FuncDeclRef<Name>;
  RecFunction(name: string, ...signature: [SortRef<Name>, SortRef<Name>, ...SortRef<Name>[]]): FuncDeclRef<Name>;
  RecAddDefinition(f: FuncDeclRef<Name>, args: ExprRef<Name>[], body: ExprRef<Name>): void;
  If(condition: Probe<Name>, onTrue: Tactic<Name>, onFalse: Tactic<Name>): Tactic<Name>;
  If<OnTrueRef extends CoercibleToExpr<Name>, OnFalseRef extends CoercibleToExpr<Name>>(
    condition: BoolRef<Name>,
    onTrue: OnTrueRef,
    onFalse: OnFalseRef,
  ): CoercibleToExprMap<OnTrueRef | OnFalseRef, Name>;
  Distinct(...args: ExprRef<Name>[]): BoolRef<Name>;
  Const<S extends SortRef<Name>>(name: string, sort: S): SortToExprMap<S, Name>;
  Consts<S extends SortRef<Name>>(name: string | string[], sort: S): SortToExprMap<S, Name>[];
  FreshConst<S extends SortRef<Name>>(sort: S, prefix?: string): SortToExprMap<S, Name>;
  Var<S extends SortRef<Name>>(idx: number, sort: S): SortToExprMap<S, Name>;
  BoolSort(): BoolSortRef<Name>;
  BoolVal(value: boolean): BoolRef<Name>;
  Bool(name: string): BoolRef<Name>;
  Bools(names: string | string[]): BoolRef<Name>[];
  BoolVector(prefix: string, count: number): BoolRef<Name>[];
  FreshBool(prefix?: string): BoolRef<Name>;
  Implies(a: BoolRef<Name>, b: BoolRef<Name>): BoolRef<Name>;
  Eq(a: ExprRef<Name>, b: ExprRef<Name>): BoolRef<Name>;
  Xor(a: BoolRef<Name>, b: BoolRef<Name>): BoolRef<Name>;
  Not(a: Probe<Name>): Probe<Name>;
  Not(a: BoolRef<Name>): BoolRef<Name>;
  And(): BoolRef<Name>;
  And(vector: AstVector<BoolRef<Name>, Name>): BoolRef<Name>;
  And(...args: BoolRef<Name>[]): BoolRef<Name>;
  And(...args: Probe<Name>[]): Probe<Name>;
  Or(): BoolRef<Name>;
  Or(vector: AstVector<BoolRef<Name>, Name>): BoolRef<Name>;
  Or(...args: BoolRef<Name>[]): BoolRef<Name>;
  Or(...args: Probe<Name>[]): Probe<Name>;
  IntSort(): ArithSortRef<Name>;
  IntVal(value: bigint | number): ArithRef<Name>;
  Int(name: string | number): ArithRef<Name>;
  //Ints(names: string | string[]): ArithRef<Name>[];
  //IntVector(prefix: string, count: number): ArithRef<Name>[];
  //FreshInt(prefix?: string): ArithRef<Name>;
  //RealSort(): ArithSortRef<Name>;
  //RealVal(value: number | string): ArithRef<Name>;
  //Real(name: string | number): ArithRef<Name>;
  //Reals(names: string | string[]): ArithRef<Name>;
  //RealVector(prefix: string, count: number): ArithRef<Name>[];
  //FreshReal(prefix?: string): ArithRef<Name>;
  //ToReal(expr: ArithRef<Name>): ArithRef<Name>;
  //ToInt(expr: ArithRef<Name>): ArithRef<Name>;
  //IsInt(expr: ArithRef<Name>): ArithRef<Name>;
  /*
  MultiPattern(...args: [ExprRef, ...ExprRef[]]): PatternRef;
  ForAll(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Exists(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Lambda<Sort extends SortRef>(vars: ExprRef | ExprRef[], body: ExprRef<Sort>): LambdaRef<Sort>;
  */
}

export interface AstRef<Name extends string = any, Ptr = unknown> {
  readonly __typename: 'AstRef' | SortRef['__typename'] | FuncDeclRef['__typename'] | ExprRef['__typename'];

  readonly ctx: Context<Name>;
  readonly ptr: Ptr;
  get ast(): Z3_ast;
  get id(): number;

  eqIdentity(other: AstRef<Name>): boolean;
  neqIdentity(other: AstRef<Name>): boolean;
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
  add(...exprs: (BoolRef<Name> | AstVector<BoolRef<Name>, Name>)[]): void;
  addAndTrack(expr: BoolRef<Name>, constant: BoolRef<Name> | string): void;
  check(...exprs: (BoolRef<Name> | AstVector<BoolRef<Name>, Name>)[]): Promise<CheckSatResult>;
  model(): Model<Name>;
}

export interface ModelCtor<Name extends string> {
  new (): Model<Name>;
}
export interface Model<Name extends string = any> extends Iterable<FuncDeclRef<Name>> {
  readonly __typename: 'Model';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_model;

  get length(): number;

  entries(): IterableIterator<[number, FuncDeclRef<Name>]>;
  keys(): IterableIterator<number>;
  values(): IterableIterator<FuncDeclRef<Name>>;
  decls(): FuncDeclRef<Name>[];
  sexpr(): string;
  eval(expr: BoolRef<Name>, modelCompletion?: boolean): BoolRef<Name>;
  eval(expr: ArithRef<Name>, modelCompletion?: boolean): ArithRef<Name>;
  eval(expr: ExprRef<Name>, modelCompletion?: boolean): ExprRef<Name>;
  get(i: number): FuncDeclRef<Name>;
  get(declaration: FuncDeclRef<Name>): FuncInterp<Name>;
  get(constant: ExprRef<Name>): ExprRef<Name>;
  get(sort: SortRef<Name>): AstVector<AnyExpr<Name>, Name>;
}

export interface SortRef<Name extends string = any> extends AstRef<Name, Z3_sort> {
  readonly __typename: 'SortRef' | BoolSortRef['__typename'] | ArithSortRef['__typename'];

  kind(): Z3_sort_kind;
  subsort(other: SortRef<Name>): boolean;
  cast(expr: CoercibleToExpr<Name>): ExprRef<Name>;
  name(): string | number;
  eqIdentity(other: SortRef<Name>): boolean;
  neqIdentity(other: SortRef<Name>): boolean;
}

export interface FuncInterp<Name extends string = any> {
  readonly __typename: 'FuncInterp';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_func_interp;
}

export interface FuncDeclRef<Name extends string = any> extends AstRef<Name, Z3_func_decl> {
  readonly __typename: 'FuncDeclRef';

  name(): string | number;
  arity(): number;
  domain(i: number): SortRef<Name>;
  range(): SortRef<Name>;
  kind(): Z3_decl_kind;
  params(): (number | string | Z3_symbol | SortRef<Name> | ExprRef<Name> | FuncDeclRef<Name>)[];
  call(...args: ExprRef<Name>[]): AnyExpr<Name>;
}

export interface ExprRef<Name extends string = any, Sort extends SortRef<Name> = AnySort<Name>, Ptr = unknown>
  extends AstRef<Name, Ptr> {
  readonly __typename:
    | 'ExprRef'
    | BoolRef['__typename']
    | PatternRef['__typename']
    | QuantifierRef['__typename']
    | LambdaRef['__typename']
    | ArithRef['__typename'];

  sort(): Sort;
  eq(other: CoercibleToExpr): BoolRef<Name>;
  neq(other: CoercibleToExpr): BoolRef<Name>;
  params(): ReturnType<FuncDeclRef<Name>['params']>;
  decl(): FuncDeclRef<Name>;
  numArgs(): number;
  arg(i: number): AnyExpr<Name>;
  children(): AnyExpr<Name>[];
}

export interface BoolSortRef<Name extends string = any> extends SortRef<Name> {
  readonly __typename: 'BoolSortRef';

  cast(expr: BoolRef<Name> | boolean): BoolRef<Name>;
  cast(expr: CoercibleToExpr<Name>): never;
}

export interface BoolRef<Name extends string = any> extends ExprRef<Name, BoolSortRef<Name>, Z3_ast> {
  readonly __typename: 'BoolRef';

  sort(): BoolSortRef<Name>;
  mul(other: BoolRef | boolean): BoolRef<Name>;
}

export interface PatternRef<Name extends string = any> extends ExprRef<Name, SortRef<Name>, Z3_pattern> {
  readonly __typename: 'PatternRef';
}

export interface QuantifierRef<Name extends string = any> extends ExprRef<Name, BoolSortRef<Name>, Z3_ast> {
  readonly __typename: 'QuantifierRef';

  weight(): number;
  numPatterns(): number;
  pattern(i: number): PatternRef<Name>;
  numNoPatterns(): number;
  noPattern(i: number): AnyExpr<Name>;
  body(): AnyExpr<Name>;
  varName(i: number): string | number;
  varSort(i: number): AnySort<Name>;
  children(): [AnyExpr<Name>];
}

export interface LambdaRef<Name extends string = any, Sort extends SortRef<Name> = AnySort<Name>>
  extends ExprRef<Name, Sort, Z3_ast> {
  readonly __typename: 'LambdaRef';

  get(expr: ExprRef<Name>): ExprRef<Name>;
  body(): AnyExpr<Name>;
}

export interface ArithSortRef<Name extends string = any> extends SortRef<Name> {
  readonly __typename: 'ArithSortRef';

  cast(other: number | bigint | ArithRef<Name> | BoolRef<Name>): ArithRef<Name>;
  cast(other: CoercibleToExpr<Name>): never;
}

export interface ArithRef<Name extends string = any> extends ExprRef<Name> {
  readonly __typename: 'ArithRef';

  add(other: ArithRef<Name> | number | bigint): ArithRef<Name>;
  mul(other: ArithRef<Name> | number | bigint): ArithRef<Name>;
  sub(other: ArithRef<Name> | number | bigint): ArithRef<Name>;
  pow(exponent: ArithRef<Name> | number | bigint): ArithRef<Name>;
  div(other: ArithRef<Name> | number | bigint): ArithRef<Name>;
  mod(other: ArithRef<Name> | number | bigint): ArithRef<Name>;
  neg(): ArithRef<Name>;
  le(other: ArithRef<Name> | number | bigint): BoolRef<Name>;
  lt(other: ArithRef<Name> | number | bigint): BoolRef<Name>;
  gt(other: ArithRef<Name> | number | bigint): BoolRef<Name>;
  ge(other: ArithRef<Name> | number | bigint): BoolRef<Name>;
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
  new <Item extends AstRef<Name> = AnyAst<Name>>(): AstVector<Item, Name>;
}
export interface AstVector<Item extends AstRef<Name> = AnyAst, Name extends string = any> extends Iterable<Item> {
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
  new <Key extends AstRef = AnyAst, Value extends AstRef = AnyAst>(): AstMap<Key, Value, Name>;
}
export interface AstMap<Key extends AstRef<Name> = AnyAst, Value extends AstRef = AnyAst, Name extends string = any> {
  readonly __typename: 'AstMap';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_ast_map;
}

export type CoercibleToExpr<Name extends string = any> = number | bigint | boolean | ExprRef<Name>;

type QuantifierOptions = {
  qid: string;
  skid: string;
  patterns: PatternRef[];
  noPatterns: ExprRef[];
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
