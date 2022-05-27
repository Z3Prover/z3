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

export type AnySort = SortRef | BoolSortRef;
export type AnyExpr = ExprRef | BoolRef | PatternRef | QuantifierRef | LambdaRef<AnySort>;
export type AnyAst = AnyExpr | AnySort | AstRef | FuncDeclRef;

export type SortToExprMap<S> = S extends BoolSortRef
  ? BoolRef
  : S extends SortRef
  ? ExprRef
  : S extends ArithSortRef
  ? ArithRef
  : never;

export type CoercibleToExprMap<S> = S extends bigint | number
  ? ArithRef
  : S extends boolean
  ? BoolRef
  : S extends ExprRef
  ? S
  : never;

export class Z3Error extends Error {}
export class Z3AssertionError extends Z3Error {}

export const sat = Symbol('Solver found a solution');
export const unsat = Symbol("Solver didn't find a solution");
export const unknown = Symbol("Solver couldn't reason about the assumptions");
export type CheckSatResult = typeof sat | typeof unsat | typeof unknown;

export interface Context {
  readonly __typename: 'Context';

  readonly ptr: Z3_context;

  interrupt(): void;
}

export interface AstRef<Ptr = unknown> {
  readonly __typename: 'AstRef' | SortRef['__typename'] | FuncDeclRef['__typename'] | ExprRef['__typename'];

  readonly ctx: Context;
  readonly ptr: Ptr;
  get ast(): Z3_ast;
  get id(): number;

  eqIdentity(other: AstRef): boolean;
  neqIdentity(other: AstRef): boolean;
  sexpr(): string;
  hash(): number;
}

export interface SolverCtor {
  new (): Solver;
}
export interface Solver {
  readonly __typename: 'Solver';

  readonly ctx: Context;
  readonly ptr: Z3_solver;

  /* TODO(ritave): Decide on how to discern between integer and float paramaters
  set(key: string, value: any): void;
  set(params: Record<string, any>): void;
  */
  push(): void;
  pop(num?: number): void;
  numScopes(): number;
  reset(): void;
  add(...exprs: (BoolRef | AstVector<BoolRef>)[]): void;
  addAndTrack(expr: BoolRef, constant: BoolRef | string): void;
  check(...exprs: (BoolRef | AstVector<BoolRef>)[]): Promise<CheckSatResult>;
  model(): Model;
}

export interface ModelCtor {
  new (): Model;
}
export interface Model extends Iterable<FuncDeclRef> {
  readonly __typename: 'Model';

  readonly ctx: Context;
  readonly ptr: Z3_model;

  get length(): number;

  entries(): IterableIterator<[number, FuncDeclRef]>;
  keys(): IterableIterator<number>;
  values(): IterableIterator<FuncDeclRef>;
  sexpr(): string;
  eval(expr: BoolRef, modelCompletion?: boolean): BoolRef;
  eval(expr: ArithRef, modelCompletion?: boolean): ArithRef;
  eval(expr: ExprRef, modelCompletion?: boolean): ExprRef;
  get(i: number): FuncDeclRef;
  get(declaration: FuncDeclRef): FuncInterp;
  get(constant: ExprRef): ExprRef;
  get(sort: SortRef): AstVector<AnyExpr>;
}

export interface SortRef extends AstRef<Z3_sort> {
  readonly __typename: 'SortRef' | BoolSortRef['__typename'] | ArithSortRef['__typename'];

  kind(): Z3_sort_kind;
  subsort(other: SortRef): boolean;
  cast(expr: CoercibleToExpr): ExprRef;
  name(): string | number;
  eqIdentity(other: SortRef): boolean;
  neqIdentity(other: SortRef): boolean;
}

export interface FuncInterp {
  readonly __typename: 'FuncInterp';

  readonly ctx: Context;
  readonly ptr: Z3_func_interp;
}

export interface FuncDeclRef extends AstRef<Z3_func_decl> {
  readonly __typename: 'FuncDeclRef';

  name(): string | number;
  arity(): number;
  domain(i: number): SortRef;
  range(): SortRef;
  kind(): Z3_decl_kind;
  params(): (number | string | Z3_symbol | SortRef | ExprRef | FuncDeclRef)[];
  call(...args: ExprRef[]): AnyExpr;
}

export interface ExprRef<Sort extends SortRef = AnySort, Ptr = unknown> extends AstRef<Ptr> {
  readonly __typename:
    | 'ExprRef'
    | BoolRef['__typename']
    | PatternRef['__typename']
    | QuantifierRef['__typename']
    | LambdaRef['__typename']
    | ArithRef['__typename'];

  sort(): Sort;
  eq(other: CoercibleToExpr): BoolRef;
  neq(other: CoercibleToExpr): BoolRef;
  params(): ReturnType<FuncDeclRef['params']>;
  decl(): FuncDeclRef;
  numArgs(): number;
  arg(i: number): AnyExpr;
  children(): AnyExpr[];
}

export interface BoolSortRef extends SortRef {
  readonly __typename: 'BoolSortRef';

  cast(expr: BoolRef | boolean): BoolRef;
  cast(expr: CoercibleToExpr): never;
}

export interface BoolRef extends ExprRef<BoolSortRef, Z3_ast> {
  readonly __typename: 'BoolRef';

  sort(): BoolSortRef;
  mul(other: BoolRef | boolean): BoolRef;
}

export interface PatternRef extends ExprRef<SortRef, Z3_pattern> {
  readonly __typename: 'PatternRef';
}

export interface QuantifierRef extends ExprRef<BoolSortRef, Z3_ast> {
  readonly __typename: 'QuantifierRef';

  weight(): number;
  numPatterns(): number;
  pattern(i: number): PatternRef;
  numNoPatterns(): number;
  noPattern(i: number): AnyExpr;
  body(): AnyExpr;
  varName(i: number): string | number;
  varSort(i: number): AnySort;
  children(): [AnyExpr];
}

export interface LambdaRef<Sort extends SortRef = AnySort> extends ExprRef<Sort, Z3_ast> {
  readonly __typename: 'LambdaRef';

  get(expr: ExprRef): ExprRef;
  body(): AnyExpr;
}

export interface ArithSortRef extends SortRef {
  readonly __typename: 'ArithSortRef';

  cast(other: number | bigint | ArithRef | BoolRef): ArithRef;
  cast(other: CoercibleToExpr): never;
}

export interface ArithRef extends ExprRef {
  readonly __typename: 'ArithRef';

  add(other: ArithRef | number | bigint): ArithRef;
  mul(other: ArithRef | number | bigint): ArithRef;
  sub(other: ArithRef | number | bigint): ArithRef;
  pow(exponent: ArithRef | number | bigint): ArithRef;
  div(other: ArithRef | number | bigint): ArithRef;
  mod(other: ArithRef | number | bigint): ArithRef;
  neg(): ArithRef;
  le(other: ArithRef | number | bigint): BoolRef;
  lt(other: ArithRef | number | bigint): BoolRef;
  gt(other: ArithRef | number | bigint): BoolRef;
  ge(other: ArithRef | number | bigint): BoolRef;
}

export interface Probe {
  readonly __typename: 'Probe';

  readonly ctx: Context;
  readonly probe: Z3_probe;
}

export interface TacticCtor {
  new (name: string): Tactic;
}
export interface Tactic {
  readonly __typename: 'Tactic';

  readonly ctx: Context;
  readonly ptr: Z3_tactic;
}

export interface AstVectorCtor {
  new <Item extends AstRef = AnyAst>(): AstVector<Item>;
}
export interface AstVector<Item extends AstRef = AnyAst> extends Iterable<Item> {
  readonly __typename: 'AstVector';

  readonly ctx: Context;
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

export interface AstMapCtor {
  new <Key extends AstRef = AnyAst, Value extends AstRef = AnyAst>(): AstMap<Key, Value>;
}
export interface AstMap<Key extends AstRef = AnyAst, Value extends AstRef = AnyAst> {
  readonly __typename: 'AstMap';

  readonly ctx: Context;
  readonly ptr: Z3_ast_map;
}

export type CoercibleToExpr = number | bigint | boolean | ExprRef;

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

  // Operations that require context
  createContext(contextOptions?: Record<string, any>): Z3WithContext;
};

type Z3WithContext = {
  // Constants
  context: Context;

  // Functions
  isContext(obj: unknown): obj is Context;
  isAst(obj: unknown): obj is AstRef;
  isSort(obj: unknown): obj is SortRef;
  isFuncDecl(obj: unknown): obj is FuncDeclRef;
  isApp(obj: unknown): obj is ExprRef;
  isConst(obj: unknown): obj is ExprRef;
  isExpr(obj: unknown): obj is ExprRef;
  isVar(obj: unknown): obj is ExprRef;
  isAppOf(obj: unknown, kind: Z3_decl_kind): boolean;
  isBool(obj: unknown): obj is BoolRef;
  isTrue(obj: unknown): obj is BoolRef;
  isFalse(obj: unknown): obj is BoolRef;
  isAnd(obj: unknown): obj is BoolRef;
  isOr(obj: unknown): obj is BoolRef;
  isImplies(obj: unknown): obj is BoolRef;
  isNot(obj: unknown): obj is BoolRef;
  isEq(obj: unknown): obj is BoolRef;
  isDistinct(obj: unknown): obj is BoolRef;
  isArith(obj: unknown): obj is ArithRef;
  isInt(obj: unknown): obj is ArithRef;
  isIntSort(obj: unknown): obj is ArithSortRef;
  isProbe(obj: unknown): obj is Probe;
  isTactic(obj: unknown): obj is Tactic;
  isPattern(obj: unknown): obj is PatternRef;
  isAstVector(obj: unknown): obj is AstVector<AnyAst>;
  /*
  isQuantifier(obj: unknown): obj is QuantifierRef;
  isForAll(obj: unknown): obj is QuantifierRef;
  isExists(obj: unknown): obj is QuantifierRef;
  isLambda(obj: unknown): obj is LambdaRef<AnySort>;
  */
  eqIdentity(a: AstRef, b: AstRef): boolean;
  getVarIndex(obj: ExprRef): number;
  getValue(obj: BoolRef): boolean | null;
  getValue(obj: ArithRef): number | bigint | null;
  getValue(obj: ExprRef): boolean | number | bigint | null;
  from(primitive: boolean): BoolRef;
  from(primitive: number | bigint): ArithRef;
  from(expr: ExprRef): ExprRef;

  // Classes
  Solver: SolverCtor;
  Model: ModelCtor;
  AstVector: AstVectorCtor;
  AstMap: AstMapCtor;
  Tactic: TacticCtor;

  // Operations
  DeclareSort(name: string | number): SortRef;
  Function(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef;
  FreshFunction(...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef;
  RecFunction(name: string, ...signature: [SortRef, SortRef, ...SortRef[]]): FuncDeclRef;
  RecAddDefinition(f: FuncDeclRef, args: ExprRef[], body: ExprRef): void;
  If(condition: Probe, onTrue: Tactic, onFalse: Tactic): Tactic;
  If<OnTrueRef extends CoercibleToExpr = ExprRef, OnFalseRef extends CoercibleToExpr = ExprRef>(
    condition: BoolRef,
    onTrue: OnTrueRef,
    onFalse: OnFalseRef,
  ): CoercibleToExprMap<OnTrueRef | OnFalseRef>;
  Distinct(...args: ExprRef[]): BoolRef;
  Const<S extends SortRef>(name: string, sort: S): SortToExprMap<S>;
  Consts<S extends SortRef>(name: string | string[], sort: S): SortToExprMap<S>[];
  FreshConst<S extends SortRef>(sort: S, prefix?: string): SortToExprMap<S>;
  Var<S extends SortRef>(idx: number, sort: S): SortToExprMap<S>;
  BoolSort(): BoolSortRef;
  BoolVal(value: boolean): BoolRef;
  Bool(name: string): BoolRef;
  Bools(names: string | string[]): BoolRef[];
  BoolVector(prefix: string, count: number): BoolRef[];
  FreshBool(prefix?: string): BoolRef;
  Implies(a: BoolRef, b: BoolRef): BoolRef;
  Eq(a: ExprRef, b: ExprRef): BoolRef;
  Xor(a: BoolRef, b: BoolRef): BoolRef;
  Not(a: Probe): Probe;
  Not(a: BoolRef): BoolRef;
  And(): BoolRef;
  And(vector: AstVector<BoolRef>): BoolRef;
  And(...args: BoolRef[]): BoolRef;
  And(...args: Probe[]): Probe;
  Or(): BoolRef;
  Or(vector: AstVector<BoolRef>): BoolRef;
  Or(...args: BoolRef[]): BoolRef;
  Or(...args: Probe[]): Probe;
  IntSort(): ArithSortRef;
  Int(name: string | number): ArithRef;
  IntVal(value: bigint | number): ArithRef;
  /*
  MultiPattern(...args: [ExprRef, ...ExprRef[]]): PatternRef;
  ForAll(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Exists(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Lambda<Sort extends SortRef>(vars: ExprRef | ExprRef[], body: ExprRef<Sort>): LambdaRef<Sort>;
  */
};
