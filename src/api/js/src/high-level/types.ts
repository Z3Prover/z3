import {
  Z3_ast,
  Z3_ast_map,
  Z3_ast_vector,
  Z3_context,
  Z3_decl_kind,
  Z3_func_decl,
  Z3_pattern,
  Z3_probe,
  Z3_sort,
  Z3_sort_kind,
  Z3_symbol,
  Z3_tactic,
} from '../low-level';

export type AnySort = SortRef | BoolSortRef;
export type AnyExpr = ExprRef | BoolRef | PatternRef | QuantifierRef | LambdaRef<AnySort>;
export type AnyAst = AnyExpr | AnySort | AstRef | FuncDeclRef;

export type SortToExpr<S> = S extends BoolSortRef ? BoolRef : S extends SortRef ? ExprRef : never;

export class Z3AssertionError extends Error {}

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

export interface SortRef extends AstRef<Z3_sort> {
  readonly __typename: 'SortRef' | BoolSortRef['__typename'];

  kind(): Z3_sort_kind;
  subsort(other: SortRef): boolean;
  cast(expr: ExprRef): ExprRef;
  name(): string | number;
  eqIdentity(other: SortRef): boolean;
  neqIdentity(other: SortRef): boolean;
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
    | LambdaRef['__typename'];

  sort(): Sort;
  eq(other: ExprRef): BoolRef;
  neq(other: ExprRef): BoolRef;
  params(): ReturnType<FuncDeclRef['params']>;
  decl(): FuncDeclRef;
  numArgs(): number;
  arg(i: number): AnyExpr;
  children(): AnyExpr[];
}

export interface BoolSortRef extends SortRef {
  readonly __typename: 'BoolSortRef';

  cast(expr: ExprRef): BoolRef;
  isInt(): true;
  isBool(): true;
}

export interface BoolRef extends ExprRef<BoolSortRef, Z3_ast> {
  readonly __typename: 'BoolRef';

  sort(): BoolSortRef;
  mul(other: BoolRef): BoolRef;
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

export interface AstVectorCtor<Item extends AstRef = AnyAst> {
  new (): AstVector<Item>;
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

export interface AstMapCtor<Key extends AstRef = AnyAst, Value extends AstRef = AnyAst> {
  new (): AstMap<Key, Value>;
}
export interface AstMap<Key extends AstRef = AnyAst, Value extends AstRef = AnyAst> {
  readonly __typename: 'AstMap';

  readonly ctx: Context;
  readonly ptr: Z3_ast_map;
}

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
  isProbe(obj: unknown): obj is Probe;
  isTactic(obj: unknown): obj is Tactic;
  isPattern(obj: unknown): obj is PatternRef;
  /*
  isQuantifier(obj: unknown): obj is QuantifierRef;
  isForAll(obj: unknown): obj is QuantifierRef;
  isExists(obj: unknown): obj is QuantifierRef;
  isLambda(obj: unknown): obj is LambdaRef<AnySort>;
  */
  eqIdentity(a: AstRef, b: AstRef): boolean;
  getVarIndex(obj: ExprRef): number;

  // Classes
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
  If<OnTrueRef extends ExprRef = ExprRef, OnFalseRef extends ExprRef = ExprRef>(
    condition: BoolRef,
    onTrue: OnTrueRef,
    onFalse: OnFalseRef,
  ): OnTrueRef | OnFalseRef;
  Distinct(...args: ExprRef[]): BoolRef;
  Const<S extends SortRef>(name: string, sort: S): SortToExpr<S>;
  Consts<S extends SortRef>(name: string | string[], sort: S): SortToExpr<S>[];
  FreshConst<S extends SortRef>(sort: S, prefix?: string): SortToExpr<S>;
  Var<S extends SortRef>(idx: number, sort: S): SortToExpr<S>;
  BoolSort(): BoolSortRef;
  BoolVal(value: boolean): BoolRef;
  Bool(name: string): BoolRef;
  Bools(names: string | string[]): BoolRef[];
  BoolVector(prefix: string, count: number): BoolRef[];
  FreshBool(prefix?: string): BoolRef;
  Implies(a: BoolRef, b: BoolRef): BoolRef;
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
  /*
  MultiPattern(...args: [ExprRef, ...ExprRef[]]): PatternRef;
  ForAll(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Exists(vars: ExprRef | ExprRef[], body: ExprRef, options?: QuantifierOptions): QuantifierRef;
  Lambda<Sort extends SortRef>(vars: ExprRef | ExprRef[], body: ExprRef<Sort>): LambdaRef<Sort>;
  */
};
