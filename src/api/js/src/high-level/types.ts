import {
  Z3_ast,
  Z3_ast_map,
  Z3_ast_vector,
  Z3_context,
  Z3_decl_kind,
  Z3_func_decl,
  Z3_func_entry,
  Z3_func_interp,
  Z3_model,
  Z3_probe,
  Z3_solver,
  Z3_optimize,
  Z3_sort,
  Z3_sort_kind,
  Z3_tactic,
} from '../low-level';

/** @hidden */
export type AnySort<Name extends string = 'main'> =
  | Sort<Name>
  | BoolSort<Name>
  | ArithSort<Name>
  | BitVecSort<number, Name>
  | SMTArraySort<Name>;
/** @hidden */
export type AnyExpr<Name extends string = 'main'> =
  | Expr<Name>
  | Bool<Name>
  | Arith<Name>
  | IntNum<Name>
  | RatNum<Name>
  | BitVec<number, Name>
  | BitVecNum<number, Name>
  | SMTArray<Name>;
/** @hidden */
export type AnyAst<Name extends string = 'main'> = AnyExpr<Name> | AnySort<Name> | FuncDecl<Name>;

/** @hidden */
// prettier-ignore
export type SortToExprMap<S extends AnySort<Name>, Name extends string = 'main'> = S extends BoolSort
  ? Bool<Name>
  : S extends ArithSort<Name>
  ? Arith<Name>
  : S extends BitVecSort<infer Size, Name>
  ? BitVec<Size, Name>
  : S extends SMTArraySort<Name, infer DomainSort, infer RangeSort>
  ? SMTArray<Name, DomainSort, RangeSort>
  : S extends Sort<Name>
  ? Expr<Name, S, Z3_ast>
  : never;

/** @hidden */
// prettier-ignore
export type CoercibleFromMap<S extends CoercibleToExpr<Name>, Name extends string = 'main'> = S extends bigint
  ? Arith<Name>
  : S extends number | CoercibleRational
  ? RatNum<Name>
  : S extends boolean
  ? Bool<Name>
  : S extends Expr<Name>
  ? S
  : never;

/** @hidden */
export type CoercibleToBitVec<Bits extends number = number, Name extends string = 'main'> =
  | bigint
  | number
  | BitVec<Bits, Name>;

export type CoercibleRational = { numerator: bigint | number; denominator: bigint | number };

/** @hidden */
export type CoercibleToExpr<Name extends string = 'main'> = number | string | bigint | boolean | CoercibleRational | Expr<Name>;

/** @hidden */
export type CoercibleToArith<Name extends string = 'main'> = number | string | bigint | CoercibleRational | Arith<Name>;

/** @hidden */
// prettier-ignore
export type CoercibleToMap<T extends AnyExpr<Name>, Name extends string = 'main'> = T extends Bool<Name>
  ? boolean | Bool<Name>
  : T extends IntNum<Name>
  ? bigint | number | IntNum<Name>
  : T extends RatNum<Name>
  ? bigint | number | CoercibleRational | RatNum<Name>
  : T extends Arith<Name>
  ? CoercibleToArith<Name>
  : T extends BitVec<infer Size, Name>
  ? CoercibleToBitVec<Size, Name>
  : T extends SMTArray<Name, infer DomainSort, infer RangeSort>
  ? SMTArray<Name, DomainSort, RangeSort>
  : T extends Expr<Name>
  ? Expr<Name>
  : never;

/**
 * Used to create a Real constant
 *
 * ```typescript
 * const x = from({ numerator: 1, denominator: 3 })
 *
 * x
 * // 1/3
 * isReal(x)
 * // true
 * isRealVal(x)
 * // true
 * x.asNumber()
 * // 0.3333333333333333
 * ```
 * @see {@link Context.from}
 * @category Global
 */

export class Z3Error extends Error {}

export class Z3AssertionError extends Z3Error {}

/** @category Global */
export type CheckSatResult = 'sat' | 'unsat' | 'unknown';

/** @hidden */
export interface ContextCtor {
  <Name extends string>(name: Name, options?: Record<string, any>): Context<Name>;
}

export interface Context<Name extends string = 'main'> {
  /** @hidden */
  readonly ptr: Z3_context;
  /**
   * Name of the current Context
   *
   * ```typescript
   * const c = new Context('main')
   *
   * c.name
   * // 'main'
   * ```
   */
  readonly name: Name;

  ///////////////
  // Functions //
  ///////////////
  /** @category Functions */
  interrupt(): void;

  /** @category Functions */
  isModel(obj: unknown): obj is Model<Name>;

  /** @category Functions */
  isAst(obj: unknown): obj is Ast<Name>;

  /** @category Functions */
  isSort(obj: unknown): obj is Sort<Name>;

  /** @category Functions */
  isFuncDecl(obj: unknown): obj is FuncDecl<Name>;

  /** @category Functions */
  isFuncInterp(obj: unknown): obj is FuncInterp<Name>;

  /** @category Functions */
  isApp(obj: unknown): boolean;

  /** @category Functions */
  isConst(obj: unknown): boolean;

  /** @category Functions */
  isExpr(obj: unknown): obj is Expr<Name>;

  /** @category Functions */
  isVar(obj: unknown): boolean;

  /** @category Functions */
  isAppOf(obj: unknown, kind: Z3_decl_kind): boolean;

  /** @category Functions */
  isBool(obj: unknown): obj is Bool<Name>;

  /** @category Functions */
  isTrue(obj: unknown): boolean;

  /** @category Functions */
  isFalse(obj: unknown): boolean;

  /** @category Functions */
  isAnd(obj: unknown): boolean;

  /** @category Functions */
  isOr(obj: unknown): boolean;

  /** @category Functions */
  isImplies(obj: unknown): boolean;

  /** @category Functions */
  isNot(obj: unknown): boolean;

  /** @category Functions */
  isEq(obj: unknown): boolean;

  /** @category Functions */
  isDistinct(obj: unknown): boolean;

  /** @category Functions */
  isQuantifier(obj: unknown): obj is Quantifier<Name>;

  /** @category Functions */
  isArith(obj: unknown): obj is Arith<Name>;

  /** @category Functions */
  isArithSort(obj: unknown): obj is ArithSort<Name>;

  /** @category Functions */
  isInt(obj: unknown): boolean;

  /** @category Functions */
  isIntVal(obj: unknown): obj is IntNum<Name>;

  /** @category Functions */
  isIntSort(obj: unknown): boolean;

  /** @category Functions */
  isReal(obj: unknown): boolean;

  /** @category Functions */
  isRealVal(obj: unknown): obj is RatNum<Name>;

  /** @category Functions */
  isRealSort(obj: unknown): boolean;

  /** @category Functions */
  isBitVecSort(obj: unknown): obj is BitVecSort<number, Name>;

  /** @category Functions */
  isBitVec(obj: unknown): obj is BitVec<number, Name>;

  /** @category Functions */
  isBitVecVal(obj: unknown): obj is BitVecNum<number, Name>;

  /** @category Functions */
  isArraySort(obj: unknown): obj is SMTArraySort<Name>;

  /** @category Functions */
  isArray(obj: unknown): obj is SMTArray<Name>;

  /** @category Functions */
  isConstArray(obj: unknown): boolean;

  /** @category Functions */
  isProbe(obj: unknown): obj is Probe<Name>;

  /** @category Functions */
  isTactic(obj: unknown): obj is Tactic<Name>;

  /** @category Functions */
  isAstVector(obj: unknown): obj is AstVector<Name, AnyAst<Name>>;

  /**
   * Returns whether two Asts are the same thing
   * @category Functions */
  eqIdentity(a: Ast<Name>, b: Ast<Name>): boolean;

  /** @category Functions */
  getVarIndex(obj: Expr<Name>): number;

  /**
   * Coerce a boolean into a Bool expression
   * @category Functions */
  from(primitive: boolean): Bool<Name>;

  /**
   * Coerce a number to an Int or Real expression (integral numbers become Ints)
   * @category Functions */
  from(primitive: number): IntNum<Name> | RatNum<Name>;

  /**
   * Coerce a rational into a Real expression
   * @category Functions */
  from(primitive: CoercibleRational): RatNum<Name>;

  /**
   * Coerce a big number into a Integer expression
   * @category Functions */
  from(primitive: bigint): IntNum<Name>;

  /**
   * Returns whatever expression was given
   * @category Functions */
  from<E extends Expr<Name>>(expr: E): E;

  /** @hidden */
  from(value: CoercibleToExpr<Name>): AnyExpr<Name>;

  /**
   * Sugar function for getting a model for given assertions
   *
   * ```typescript
   * const x = Int.const('x');
   * const y = Int.const('y');
   * const result = await solve(x.le(y));
   * if (isModel(result)) {
   *   console.log('Z3 found a solution');
   *   console.log(`x=${result.get(x)}, y=${result.get(y)}`);
   * } else {
   *   console.error('No solution found');
   * }
   * ```
   *
   * @see {@link Solver}
   * @category Functions */
  solve(...assertions: Bool<Name>[]): Promise<Model<Name> | 'unsat' | 'unknown'>;

  /////////////
  // Classes //
  /////////////
  /**
   * Creates a Solver
   * @param logic - Optional logic which the solver will use. Creates a general Solver otherwise
   * @category Classes
   */
  readonly Solver: new (logic?: string) => Solver<Name>;

  readonly Optimize: new () => Optimize<Name>;

  /**
   * Creates an empty Model
   * @see {@link Solver.model} for common usage of Model
   * @category Classes
   */
  readonly Model: new () => Model<Name>;
  /** @category Classes */
  readonly AstVector: new <Item extends Ast<Name> = AnyAst<Name>>() => AstVector<Name, Item>;
  /** @category Classes */
  readonly AstMap: new <Key extends Ast<Name> = AnyAst<Name>, Value extends Ast<Name> = AnyAst<Name>>() => AstMap<
    Name,
    Key,
    Value
  >;
  /** @category Classes */
  readonly Tactic: new (name: string) => Tactic<Name>;

  /////////////
  // Objects //
  /////////////
  /** @category Expressions */
  readonly Sort: SortCreation<Name>;
  /** @category Expressions */
  readonly Function: FuncDeclCreation<Name>;
  /** @category Expressions */
  readonly RecFunc: RecFuncCreation<Name>;
  /** @category Expressions */
  readonly Bool: BoolCreation<Name>;
  /** @category Expressions */
  readonly Int: IntCreation<Name>;
  /** @category Expressions */
  readonly Real: RealCreation<Name>;
  /** @category Expressions */
  readonly BitVec: BitVecCreation<Name>;
  /** @category Expressions */
  readonly Array: SMTArrayCreation<Name>;
  /** @category Expressions */
  readonly Set: SMTSetCreation<Name>;

  ////////////////
  // Operations //
  ////////////////
  /** @category Operations */
  Const<S extends Sort<Name>>(name: string, sort: S): SortToExprMap<S, Name>;

  /** @category Operations */
  Consts<S extends Sort<Name>>(name: string | string[], sort: S): SortToExprMap<S, Name>[];

  /** @category Operations */
  FreshConst<S extends Sort<Name>>(sort: S, prefix?: string): SortToExprMap<S, Name>;

  /** @category Operations */
  Var<S extends Sort<Name>>(idx: number, sort: S): SortToExprMap<S, Name>;

  // Booleans
  /** @category Operations */
  If(condition: Probe<Name>, onTrue: Tactic<Name>, onFalse: Tactic<Name>): Tactic<Name>;

  /** @category Operations */
  If<OnTrueRef extends CoercibleToExpr<Name>, OnFalseRef extends CoercibleToExpr<Name>>(
    condition: Bool<Name> | boolean,
    onTrue: OnTrueRef,
    onFalse: OnFalseRef,
  ): CoercibleFromMap<OnTrueRef | OnFalseRef, Name>;

  /** @category Operations */
  Distinct(...args: CoercibleToExpr<Name>[]): Bool<Name>;

  /** @category Operations */
  Implies(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name>;

  /** @category Operations */
  Iff(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name>;

  /** @category Operations */
  Eq(a: CoercibleToExpr<Name>, b: CoercibleToExpr<Name>): Bool<Name>;

  /** @category Operations */
  Xor(a: Bool<Name> | boolean, b: Bool<Name> | boolean): Bool<Name>;

  /** @category Operations */
  Not(a: Probe<Name>): Probe<Name>;

  /** @category Operations */
  Not(a: Bool<Name> | boolean): Bool<Name>;

  /** @category Operations */
  And(): Bool<Name>;

  /** @category Operations */
  And(vector: AstVector<Name, Bool<Name>>): Bool<Name>;

  /** @category Operations */
  And(...args: (Bool<Name> | boolean)[]): Bool<Name>;

  /** @category Operations */
  And(...args: Probe<Name>[]): Probe<Name>;

  /** @category Operations */
  Or(): Bool<Name>;

  /** @category Operations */
  Or(vector: AstVector<Name, Bool<Name>>): Bool<Name>;

  /** @category Operations */
  Or(...args: (Bool<Name> | boolean)[]): Bool<Name>;

  /** @category Operations */
  Or(...args: Probe<Name>[]): Probe<Name>;

  /** @category Operations */
  PbEq(args: [Bool<Name>, ...Bool<Name>[]], coeffs: [number, ...number[]], k: number): Bool<Name>;

  /** @category Operations */
  PbGe(args: [Bool<Name>, ...Bool<Name>[]], coeffs: [number, ...number[]], k: number): Bool<Name>;

  /** @category Operations */
  PbLe(args: [Bool<Name>, ...Bool<Name>[]], coeffs: [number, ...number[]], k: number): Bool<Name>;

  // Quantifiers

  /** @category Operations */
  ForAll<QVarSorts extends NonEmptySortArray<Name>>(
    quantifiers: ArrayIndexType<Name, QVarSorts>,
    body: Bool<Name>,
    weight?: number,
  ): Quantifier<Name, QVarSorts, BoolSort<Name>> & Bool<Name>;

  /** @category Operations */
  Exists<QVarSorts extends NonEmptySortArray<Name>>(
    quantifiers: ArrayIndexType<Name, QVarSorts>,
    body: Bool<Name>,
    weight?: number,
  ): Quantifier<Name, QVarSorts, BoolSort<Name>> & Bool<Name>;

  /** @category Operations */
  Lambda<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
    quantifiers: ArrayIndexType<Name, DomainSort>,
    expr: SortToExprMap<RangeSort, Name>,
  ): Quantifier<Name, DomainSort, SMTArraySort<Name, DomainSort, RangeSort>> & SMTArray<Name, DomainSort, RangeSort>;

  // Arithmetic
  /** @category Operations */
  ToReal(expr: Arith<Name> | bigint): Arith<Name>;

  /** @category Operations */
  ToInt(expr: Arith<Name> | number | CoercibleRational | string): Arith<Name>;

  /**
   * Create an IsInt Z3 predicate
   *
   * ```typescript
   * const x = Real.const('x');
   * await solve(IsInt(x.add("1/2")), x.gt(0), x.lt(1))
   * // x = 1/2
   * await solve(IsInt(x.add("1/2")), x.gt(0), x.lt(1), x.neq("1/2"))
   * // unsat
   * ```
   * @category Operations */
  IsInt(expr: Arith<Name> | number | CoercibleRational | string): Bool<Name>;

  /**
   * Returns a Z3 expression representing square root of a
   *
   * ```typescript
   * const a = Real.const('a');
   *
   * Sqrt(a);
   * // a**(1/2)
   * ```
   * @category Operations */
  Sqrt(a: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Returns a Z3 expression representing cubic root of a
   *
   * ```typescript
   * const a = Real.const('a');
   *
   * Cbrt(a);
   * // a**(1/3)
   * ```
   * @category Operations */
  Cbrt(a: CoercibleToArith<Name>): Arith<Name>;

  // Bit Vectors
  /** @category Operations */
  BV2Int(a: BitVec<number, Name>, isSigned: boolean): Arith<Name>;

  /** @category Operations */
  Int2BV<Bits extends number>(a: Arith<Name> | bigint | number, bits: Bits): BitVec<Bits, Name>;

  /** @category Operations */
  Concat(...bitvecs: BitVec<number, Name>[]): BitVec<number, Name>;

  /** @category Operations */
  Cond(probe: Probe<Name>, onTrue: Tactic<Name>, onFalse: Tactic<Name>): Tactic<Name>;

  // Arith

  /** @category Operations */
  LT(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name>;

  /** @category Operations */
  GT(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name>;

  /** @category Operations */
  LE(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name>;

  /** @category Operations */
  GE(a: Arith<Name>, b: CoercibleToArith<Name>): Bool<Name>;

  // Bit Vectors

  /** @category Operations */
  ULT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  UGT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  ULE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  UGE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  SLT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  SGT<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  SGE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  SLE<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Operations */
  Sum(arg0: Arith<Name>, ...args: CoercibleToArith<Name>[]): Arith<Name>;

  Sum<Bits extends number>(arg0: BitVec<Bits, Name>, ...args: CoercibleToBitVec<Bits, Name>[]): BitVec<Bits, Name>;

  Sub(arg0: Arith<Name>, ...args: CoercibleToArith<Name>[]): Arith<Name>;

  Sub<Bits extends number>(arg0: BitVec<Bits, Name>, ...args: CoercibleToBitVec<Bits, Name>[]): BitVec<Bits, Name>;

  Product(arg0: Arith<Name>, ...args: CoercibleToArith<Name>[]): Arith<Name>;

  Product<Bits extends number>(arg0: BitVec<Bits, Name>, ...args: CoercibleToBitVec<Bits, Name>[]): BitVec<Bits, Name>;

  Div(arg0: Arith<Name>, arg1: CoercibleToArith<Name>): Arith<Name>;

  Div<Bits extends number>(arg0: BitVec<Bits, Name>, arg1: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  BUDiv<Bits extends number>(arg0: BitVec<Bits, Name>, arg1: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  Neg(a: Arith<Name>): Arith<Name>;

  Neg<Bits extends number>(a: BitVec<Bits, Name>): BitVec<Bits, Name>;

  Mod(a: Arith<Name>, b: CoercibleToArith<Name>): Arith<Name>;

  Mod<Bits extends number>(a: BitVec<Bits, Name>, b: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  // Arrays

  /** @category Operations */
  Select<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name> = Sort<Name>>(
    array: SMTArray<Name, DomainSort, RangeSort>,
    ...indices: CoercibleToArrayIndexType<Name, DomainSort>
  ): SortToExprMap<RangeSort, Name>;

  /** @category Operations */
  Store<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name> = Sort<Name>>(
    array: SMTArray<Name, DomainSort, RangeSort>,
    ...indicesAndValue: [
      ...CoercibleToArrayIndexType<Name, DomainSort>,
      CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
    ]
  ): SMTArray<Name, DomainSort, RangeSort>;

  /** @category Operations */
  Extract<Bits extends number>(hi: number, lo: number, val: BitVec<Bits, Name>): BitVec<number, Name>;

  /** @category Operations */
  ast_from_string(s: string): Ast<Name>;

  /** @category Operations */
  substitute(t: Expr<Name>, ...substitutions: [Expr<Name>, Expr<Name>][]): Expr<Name>;

  simplify(expr: Expr<Name>): Promise<Expr<Name>>;
  
  /** @category Operations */
  SetUnion<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;
  
  /** @category Operations */
  SetIntersect<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;
  
  /** @category Operations */
  SetDifference<ElemSort extends AnySort<Name>>(a: SMTSet<Name, ElemSort>, b: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort>;
  
  /** @category Operations */
  SetHasSize<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>, size: bigint | number | string | IntNum<Name>): Bool<Name>;

  /** @category Operations */
  SetAdd<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>, elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetDel<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>, elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetComplement<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort>;
  
  /** @category Operations */
  EmptySet<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort>;

  /** @category Operations */
  FullSet<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort>;
  
  /** @category Operations */
  isMember<ElemSort extends AnySort<Name>>(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>, set: SMTSet<Name, ElemSort>): Bool<Name>;

  /** @category Operations */
  isSubset<ElemSort extends AnySort<Name>>(a: SMTSet<Name, ElemSort>, b: SMTSet<Name, ElemSort>): Bool<Name>;
}

export interface Ast<Name extends string = 'main', Ptr = unknown> {
  /** @hidden */
  readonly __typename: 'Ast' | Sort['__typename'] | FuncDecl['__typename'] | Expr['__typename'];

  readonly ctx: Context<Name>;
  /** @hidden */
  readonly ptr: Ptr;

  /** @virtual */
  get ast(): Z3_ast;

  /** @virtual */
  id(): number;

  eqIdentity(other: Ast<Name>): boolean;

  neqIdentity(other: Ast<Name>): boolean;

  sexpr(): string;

  hash(): number;
}

/** @hidden */
export interface SolverCtor<Name extends string> {
  new (): Solver<Name>;
}

export interface Solver<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Solver';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_solver;

  set(key: string, value: any): void;

  /* TODO(ritave): Decide on how to discern between integer and float parameters
      set(params: Record<string, any>): void;
      */
  push(): void;

  pop(num?: number): void;

  numScopes(): number;

  reset(): void;

  add(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): void;

  addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string): void;

  assertions(): AstVector<Name, Bool<Name>>;

  fromString(s: string): void;

  check(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): Promise<CheckSatResult>;

  model(): Model<Name>;

  /**
   * Manually decrease the reference count of the solver
   * This is automatically done when the solver is garbage collected,
   * but calling this eagerly can help release memory sooner.
   */
  release(): void;
}

export interface Optimize<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Optimize';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_optimize;

  set(key: string, value: any): void;

  push(): void;

  pop(num?: number): void;

  add(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): void;

  addSoft(expr: Bool<Name>, weight: number | bigint | string | CoercibleRational, id?: number | string): void;

  addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string): void;

  assertions(): AstVector<Name, Bool<Name>>;

  fromString(s: string): void;

  maximize(expr: Arith<Name>): void;

  minimize(expr: Arith<Name>): void;

  check(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): Promise<CheckSatResult>;

  model(): Model<Name>;

  /**
   * Manually decrease the reference count of the optimize
   * This is automatically done when the optimize is garbage collected,
   * but calling this eagerly can help release memory sooner.
   */
  release(): void;
}

/** @hidden */
export interface ModelCtor<Name extends string> {
  new (): Model<Name>;
}

export interface Model<Name extends string = 'main'> extends Iterable<FuncDecl<Name>> {
  /** @hidden */
  readonly __typename: 'Model';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_model;

  length(): number;

  entries(): IterableIterator<[number, FuncDecl<Name>]>;

  keys(): IterableIterator<number>;

  values(): IterableIterator<FuncDecl<Name>>;

  decls(): FuncDecl<Name>[];

  sexpr(): string;

  eval(expr: Bool<Name>, modelCompletion?: boolean): Bool<Name>;

  eval(expr: Arith<Name>, modelCompletion?: boolean): Arith<Name>;

  eval<Bits extends number = number>(expr: BitVec<Bits, Name>, modelCompletion?: boolean): BitVecNum<Bits, Name>;

  eval(expr: Expr<Name>, modelCompletion?: boolean): Expr<Name>;

  get(i: number): FuncDecl<Name>;

  get(from: number, to: number): FuncDecl<Name>[];

  get(declaration: FuncDecl<Name>): FuncInterp<Name> | Expr<Name>;

  get(constant: Expr<Name>): Expr<Name>;

  get(sort: Sort<Name>): AstVector<Name, AnyExpr<Name>>;

  updateValue(decl: FuncDecl<Name> | Expr<Name>, a: Ast<Name> | FuncInterp<Name>): void;

  addFuncInterp<DomainSort extends Sort<Name>[] = Sort<Name>[], RangeSort extends Sort<Name> = Sort<Name>>(
    decl: FuncDecl<Name, DomainSort, RangeSort>,
    defaultValue: CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
  ): FuncInterp<Name>;

  /**
   * Manually decrease the reference count of the model
   * This is automatically done when the model is garbage collected,
   * but calling this eagerly can help release memory sooner.
   */
  release(): void;
}

/**
 * Part of {@link Context}. Used to declare uninterpreted sorts
 *
 * ```typescript
 * const A = context.Sort.declare('A');
 * const a = context.Const('a', A);
 * const b = context.const('b', A);
 *
 * a.sort.eqIdentity(A)
 * // true
 * b.sort.eqIdentity(A)
 * // true
 * a.eq(b)
 * // a == b
 * ```
 */
export interface SortCreation<Name extends string> {
  declare(name: string): Sort<Name>;
}

export interface Sort<Name extends string = 'main'> extends Ast<Name, Z3_sort> {
  /** @hidden */
  readonly __typename:
    | 'Sort'
    | BoolSort['__typename']
    | ArithSort['__typename']
    | BitVecSort['__typename']
    | SMTArraySort['__typename'];

  kind(): Z3_sort_kind;

  /** @virtual */
  subsort(other: Sort<Name>): boolean;

  /** @virtual */
  cast(expr: CoercibleToExpr<Name>): Expr<Name>;

  name(): string | number;
}

/**
 * @category Functions
 */
export interface FuncEntry<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'FuncEntry';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_func_entry;

  numArgs(): number;

  argValue(i: number): Expr<Name>;

  value(): Expr<Name>;
}

/**
 * @category Functions
 */
export interface FuncInterp<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'FuncInterp';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_func_interp;

  elseValue(): Expr<Name>;

  numEntries(): number;

  arity(): number;

  entry(i: number): FuncEntry<Name>;

  addEntry(args: Expr<Name>[], value: Expr<Name>): void;
}

/** @hidden */
export type FuncDeclSignature<Name extends string> = [Sort<Name>, Sort<Name>, ...Sort<Name>[]];

/**
 * Part of {@link Context}. Used to declare functions
 * @category Functions
 */
export interface FuncDeclCreation<Name extends string> {
  /**
   * Declare a new function
   *
   * ```typescript
   * const f = ctx.Function.declare('f', ctx.Bool.sort(), ctx.Real.sort(), ctx.Int.sort())
   *
   * f.call(true, "1/3").eq(5)
   * // f(true, 1/3) == 5
   * ```
   * @param name Name of the function
   * @param signature The domains, and last parameter - the range of the function
   */
  declare<DomainSort extends Sort<Name>[], RangeSort extends Sort<Name>>(
    name: string,
    ...signature: [...DomainSort, RangeSort]
  ): FuncDecl<Name, DomainSort, RangeSort>;

  fresh<DomainSort extends Sort<Name>[], RangeSort extends Sort<Name>>(
    ...signature: [...DomainSort, RangeSort]
  ): FuncDecl<Name, DomainSort, RangeSort>;
}

/**
 * @category Functions
 */
export interface RecFuncCreation<Name extends string> {
  declare(name: string, ...signature: FuncDeclSignature<Name>): FuncDecl<Name>;

  addDefinition(f: FuncDecl<Name>, args: Expr<Name>[], body: Expr<Name>): void;
}

/**
 * @category Functions
 */
export interface FuncDecl<
  Name extends string = 'main',
  DomainSort extends Sort<Name>[] = Sort<Name>[],
  RangeSort extends Sort<Name> = Sort<Name>,
> extends Ast<Name, Z3_func_decl> {
  /** @hidden */
  readonly __typename: 'FuncDecl';

  name(): string | number;

  arity(): number;

  domain<T extends number>(i: T): DomainSort[T];

  range(): RangeSort;

  kind(): Z3_decl_kind;

  params(): (number | string | Sort<Name> | Expr<Name> | FuncDecl<Name>)[];

  call(...args: CoercibleToArrayIndexType<Name, DomainSort>): SortToExprMap<RangeSort, Name>;
}

export interface Expr<Name extends string = 'main', S extends Sort<Name> = AnySort<Name>, Ptr = unknown>
  extends Ast<Name, Ptr> {
  /** @hidden */
  readonly __typename:
    | 'Expr'
    | Bool['__typename']
    | Arith['__typename']
    | BitVec['__typename']
    | SMTArray['__typename'];

  get sort(): S;

  eq(other: CoercibleToExpr<Name>): Bool<Name>;

  neq(other: CoercibleToExpr<Name>): Bool<Name>;

  params(): ReturnType<FuncDecl<Name>['params']>;

  name(): ReturnType<FuncDecl<Name>['name']>;

  decl(): FuncDecl<Name>;

  numArgs(): number;

  arg(i: number): AnyExpr<Name>;

  children(): AnyExpr<Name>[];
}

/** @category Booleans */
export interface BoolSort<Name extends string = 'main'> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'BoolSort';

  cast(expr: Bool<Name> | boolean): Bool<Name>;

  cast(expr: CoercibleToExpr<Name>): never;
}

/** @category Booleans */
export interface BoolCreation<Name extends string = 'main'> {
  sort(): BoolSort<Name>;

  const(name: string): Bool<Name>;

  consts(names: string | string[]): Bool<Name>[];

  vector(prefix: string, count: number): Bool<Name>[];

  fresh(prefix?: string): Bool<Name>;

  val(value: boolean): Bool<Name>;
}

/** @category Booleans */
export interface Bool<Name extends string = 'main'> extends Expr<Name, BoolSort<Name>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'Bool' | 'NonLambdaQuantifier';

  not(): Bool<Name>;

  and(other: Bool<Name> | boolean): Bool<Name>;

  or(other: Bool<Name> | boolean): Bool<Name>;

  xor(other: Bool<Name> | boolean): Bool<Name>;

  implies(other: Bool<Name> | boolean): Bool<Name>;
}

// TODO: properly implement pattern
/** @category Quantifiers */
export interface Pattern<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Pattern';
}

/**
 * A Sort that represents Integers or Real numbers
 * @category Arithmetic
 */
export interface ArithSort<Name extends string = 'main'> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'ArithSort';

  cast(other: bigint | number | string): IntNum<Name> | RatNum<Name>;

  cast(other: CoercibleRational | RatNum<Name>): RatNum<Name>;

  cast(other: IntNum<Name>): IntNum<Name>;

  cast(other: bigint | number | string | Bool<Name> | Arith<Name> | CoercibleRational): Arith<Name>;

  cast(other: CoercibleToExpr<Name> | string): never;
}

/** @category Arithmetic */
export interface IntCreation<Name extends string> {
  sort(): ArithSort<Name>;

  const(name: string): Arith<Name>;

  consts(names: string | string[]): Arith<Name>[];

  vector(prefix: string, count: number): Arith<Name>[];

  fresh(prefix?: string): Arith<Name>;

  val(value: bigint | number | string): IntNum<Name>;
}

/** @category Arithmetic */
export interface RealCreation<Name extends string> {
  sort(): ArithSort<Name>;

  const(name: string): Arith<Name>;

  consts(names: string | string[]): Arith<Name>[];

  vector(prefix: string, count: number): Arith<Name>[];

  fresh(prefix?: string): Arith<Name>;

  val(value: number | string | bigint | CoercibleRational): RatNum<Name>;
}

/**
 * Represents Integer or Real number expression
 * @category Arithmetic
 */
export interface Arith<Name extends string = 'main'> extends Expr<Name, ArithSort<Name>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'Arith' | IntNum['__typename'] | RatNum['__typename'];

  /**
   * Adds two numbers together
   */
  add(other: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Multiplies two numbers together
   */
  mul(other: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Subtract second number from the first one
   */
  sub(other: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Applies power to the number
   *
   * ```typescript
   * const x = Int.const('x');
   *
   * await solve(x.pow(2).eq(4), x.lt(0)); // x**2 == 4, x < 0
   * // x=-2
   * ```
   */
  pow(exponent: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Divides the number by the second one
   */
  div(other: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Returns a number modulo second one
   *
   * ```typescript
   * const x = Int.const('x');
   *
   * await solve(x.mod(7).eq(1), x.gt(7)) // x % 7 == 1, x > 7
   * // x=8
   * ```
   */
  mod(other: CoercibleToArith<Name>): Arith<Name>;

  /**
   * Returns a negation of the number
   */
  neg(): Arith<Name>;

  /**
   * Return whether the number is less or equal than the second one (`<=`)
   */
  le(other: CoercibleToArith<Name>): Bool<Name>;

  /**
   * Returns whether the number is less than the second one (`<`)
   */
  lt(other: CoercibleToArith<Name>): Bool<Name>;

  /**
   * Returns whether the number is greater than the second one (`>`)
   */
  gt(other: CoercibleToArith<Name>): Bool<Name>;

  /**
   * Returns whether the number is greater or equal than the second one (`>=`)
   */
  ge(other: CoercibleToArith<Name>): Bool<Name>;
}

/**
 * A constant Integer value expression
 * @category Arithmetic
 */
export interface IntNum<Name extends string = 'main'> extends Arith<Name> {
  /** @hidden */
  readonly __typename: 'IntNum';

  value(): bigint;

  asString(): string;

  asBinary(): string;
}

/**
 * A constant Rational value expression
 *
 * ```typescript
 * const num = Real.val('1/3');
 *
 * num.asString()
 * // '1/3'
 * num.value
 * // { numerator: 1n, denominator: 3n }
 * num.asNumber()
 * // 0.3333333333333333
 * ```
 * @category Arithmetic
 */
export interface RatNum<Name extends string = 'main'> extends Arith<Name> {
  /** @hidden */
  readonly __typename: 'RatNum';

  value(): { numerator: bigint; denominator: bigint };

  numerator(): IntNum<Name>;

  denominator(): IntNum<Name>;

  asNumber(): number;

  asDecimal(prec?: number): string;

  asString(): string;
}

/**
 * A Sort representing Bit Vector numbers of specified {@link BitVecSort.size size}
 *
 * @typeParam Bits - A number representing amount of bits for this sort
 * @category Bit Vectors
 */
export interface BitVecSort<Bits extends number = number, Name extends string = 'main'> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'BitVecSort';

  /**
   * The amount of bits inside the sort
   *
   * ```typescript
   * const x = BitVec.const('x', 32);
   *
   * console.log(x.sort.size)
   * // 32
   * ```
   */
  size(): Bits;

  cast(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  cast(other: CoercibleToExpr<Name>): Expr<Name>;
}

/** @category Bit Vectors */
export interface BitVecCreation<Name extends string> {
  sort<Bits extends number = number>(bits: Bits): BitVecSort<Bits, Name>;

  const<Bits extends number = number>(name: string, bits: Bits | BitVecSort<Bits, Name>): BitVec<Bits, Name>;

  consts<Bits extends number = number>(
    names: string | string[],
    bits: Bits | BitVecSort<Bits, Name>,
  ): BitVec<Bits, Name>[];

  val<Bits extends number = number>(
    value: bigint | number | boolean,
    bits: Bits | BitVecSort<Bits, Name>,
  ): BitVecNum<Bits, Name>;
}

/**
 * Represents Bit Vector expression
 * @category Bit Vectors
 */
export interface BitVec<Bits extends number = number, Name extends string = 'main'>
  extends Expr<Name, BitVecSort<Bits, Name>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'BitVec' | BitVecNum['__typename'];

  /**
   * The amount of bits of this BitVectors sort
   *
   * ```typescript
   * const x = BitVec.const('x', 32);
   *
   * x.size
   * // 32
   *
   * const Y = BitVec.sort(8);
   * const y = BitVec.const('y', Y);
   *
   * y.size
   * // 8
   * ```
   */
  size(): Bits;

  /** @category Arithmetic */
  add(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  mul(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  sub(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  sdiv(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  udiv(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  smod(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  urem(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  srem(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /** @category Arithmetic */
  neg(): BitVec<Bits, Name>;

  /**
   * Creates a bitwise-or between two bitvectors
   * @category4 Bitwise
   */
  or(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a bitwise-and between two bitvectors
   * @category Bitwise
   */
  and(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a bitwise-not-and between two bitvectors
   * @category Bitwise
   */
  nand(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a bitwise-exclusive-or between two bitvectors
   * @category Bitwise
   */
  xor(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a bitwise-exclusive-not-or between two bitvectors
   * @category Bitwise
   */
  xnor(other: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates an arithmetic shift right operation
   * @category Bitwise
   */
  shr(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a logical shift right operation
   * @category Bitwise
   */
  lshr(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a shift left operation
   * @category Bitwise
   */
  shl(count: CoercibleToBitVec<Bits, Name>): BitVec<Bits, Name>;

  /**
   * Creates a rotate right operation
   * @category Bitwise
   */
  rotateRight(count: CoercibleToBitVec<number, Name>): BitVec<Bits, Name>;

  /**
   * Creates a rotate left operation
   * @category Bitwise
   */
  rotateLeft(count: CoercibleToBitVec<number, Name>): BitVec<Bits, Name>;

  /**
   * Creates a bitwise not operation
   * @category Bitwise
   */
  not(): BitVec<Bits, Name>;

  /**
   * Creates an extraction operation.
   * Bits are indexed starting from 1 from the most right one (least significant) increasing to left (most significant)
   *
   * ```typescript
   * const x = BitVec.const('x', 8);
   *
   * x.extract(6, 2)
   * // Extract(6, 2, x)
   * x.extract(6, 2).sort
   * // BitVec(5)
   * ```
   * @param high The most significant bit to be extracted
   * @param low  The least significant bit to be extracted
   */
  extract(high: number, low: number): BitVec<number, Name>;

  signExt(count: number): BitVec<number, Name>;

  zeroExt(count: number): BitVec<number, Name>;

  repeat(count: number): BitVec<number, Name>;

  /**
   * Creates a signed less-or-equal operation (`<=`)
   * @category Comparison
   */
  sle(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates an unsigned less-or-equal operation (`<=`)
   * @category Comparison
   */
  ule(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates a signed less-than operation (`<`)
   * @category Comparison
   */
  slt(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates an unsigned less-than operation (`<`)
   * @category Comparison
   */
  ult(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates a signed greater-or-equal operation (`>=`)
   * @category Comparison
   */
  sge(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates an unsigned greater-or-equal operation (`>=`)
   * @category Comparison
   */
  uge(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates a signed greater-than operation (`>`)
   * @category Comparison
   */
  sgt(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates an unsigned greater-than operation (`>`)
   * @category Comparison
   */
  ugt(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /**
   * Creates a reduction-and operation
   */
  redAnd(): BitVec<number, Name>;

  /**
   * Creates a reduction-or operation
   */
  redOr(): BitVec<number, Name>;

  /** @category Boolean */
  addNoOverflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name>;

  /** @category Boolean */
  addNoUnderflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Boolean */
  subNoOverflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Boolean */
  subNoUndeflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name>;

  /** @category Boolean */
  sdivNoOverflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Boolean */
  mulNoOverflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name>;

  /** @category Boolean */
  mulNoUndeflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Boolean */
  negNoOverflow(): Bool<Name>;
}

/**
 * Represents Bit Vector constant value
 * @category Bit Vectors
 */
export interface BitVecNum<Bits extends number = number, Name extends string = 'main'> extends BitVec<Bits, Name> {
  /** @hidden */
  readonly __typename: 'BitVecNum';

  value(): bigint;

  asSignedValue(): bigint;

  asString(): string;

  asBinaryString(): string;
}

/**
 * A Sort representing a SMT Array with range of sort {@link SMTArraySort.range range}
 * and a domain of sort {@link SMTArraySort.domain domain}
 *
 * @typeParam DomainSort The sort of the domain of the array (provided as an array of sorts)
 * @typeParam RangeSort The sort of the array range
 * @category Arrays
 */
export interface SMTArraySort<
  Name extends string = 'main',
  DomainSort extends NonEmptySortArray<Name> = [Sort<Name>, ...Sort<Name>[]],
  RangeSort extends AnySort<Name> = AnySort<Name>,
> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'ArraySort';

  /**
   * The sort of the first dimension of the domain
   */
  domain(): DomainSort[0];

  /**
   * The sort of the i-th (0-indexed) dimension of the domain
   *
   * @param i index of the dimension of the domain being requested
   */
  domain_n<T extends number>(i: T): DomainSort[T];

  /**
   * The sort of the range
   */
  range(): RangeSort;
}

/** @category Arrays */
export interface SMTArrayCreation<Name extends string> {
  sort<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
    ...sig: [...DomainSort, RangeSort]
  ): SMTArraySort<Name, DomainSort, RangeSort>;

  const<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
    name: string,
    ...sig: [...DomainSort, RangeSort]
  ): SMTArray<Name, DomainSort, RangeSort>;

  consts<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name>>(
    names: string | string[],
    ...sig: [...DomainSort, RangeSort]
  ): SMTArray<Name, DomainSort, RangeSort>[];

  K<DomainSort extends AnySort<Name>, RangeSort extends AnySort<Name>>(
    domain: DomainSort,
    value: SortToExprMap<RangeSort, Name>,
  ): SMTArray<Name, [DomainSort], RangeSort>;
}

export type NonEmptySortArray<Name extends string = 'main'> = [Sort<Name>, ...Array<Sort<Name>>];

export type ArrayIndexType<Name extends string, DomainSort extends Sort<Name>[]> = [
  ...{
    [Key in keyof DomainSort]: DomainSort[Key] extends AnySort<Name>
      ? SortToExprMap<DomainSort[Key], Name>
      : DomainSort[Key];
  },
];

export type CoercibleToArrayIndexType<Name extends string, DomainSort extends Sort<Name>[]> = [
  ...{
    [Key in keyof DomainSort]: DomainSort[Key] extends AnySort<Name>
      ? CoercibleToMap<SortToExprMap<DomainSort[Key], Name>, Name>
      : DomainSort[Key];
  },
];

/**
 * Represents Array expression
 *
 * @typeParam DomainSort The sort of the domain of the array (provided as an array of sorts)
 * @typeParam RangeSort The sort of the array range
 * @category Arrays
 */
export interface SMTArray<
  Name extends string = 'main',
  DomainSort extends NonEmptySortArray<Name> = [Sort<Name>, ...Sort<Name>[]],
  RangeSort extends Sort<Name> = Sort<Name>,
> extends Expr<Name, SMTArraySort<Name, DomainSort, RangeSort>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'Array' | 'Lambda';

  domain(): DomainSort[0];

  domain_n<T extends number>(i: T): DomainSort[T];

  range(): RangeSort;

  select(...indices: CoercibleToArrayIndexType<Name, DomainSort>): SortToExprMap<RangeSort, Name>;

  /**
   * value should be coercible to RangeSort
   *
   * @param indicesAndValue (idx0, idx1, ..., idxN, value)
   */
  store(
    ...indicesAndValue: [
      ...CoercibleToArrayIndexType<Name, DomainSort>,
      CoercibleToMap<SortToExprMap<RangeSort, Name>, Name>,
    ]
  ): SMTArray<Name, DomainSort, RangeSort>;
}

/**
 * Set Implemented using Arrays
 * 
 * @typeParam ElemSort The sort of the element of the set
 * @category Sets
 */
export type SMTSetSort<Name extends string = 'main', ElemSort extends AnySort<Name> = Sort<Name>> = SMTArraySort<Name, [ElemSort], BoolSort<Name>>;


/** @category Sets*/
export interface SMTSetCreation<Name extends string> {
  sort<ElemSort extends AnySort<Name>>(elemSort: ElemSort): SMTSetSort<Name, ElemSort>;

  const<ElemSort extends AnySort<Name>>(name: string, elemSort: ElemSort): SMTSet<Name, ElemSort>;

  consts<ElemSort extends AnySort<Name>>(names: string | string[], elemSort: ElemSort): SMTSet<Name, ElemSort>[];
  
  empty<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort>;
  
  val<ElemSort extends AnySort<Name>>(values: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>[], sort: ElemSort): SMTSet<Name, ElemSort>;
}

/**
 * Represents Set expression
 *
 * @typeParam ElemSort The sort of the element of the set
 * @category Arrays
 */
export interface SMTSet<Name extends string = 'main', ElemSort extends AnySort<Name> = Sort<Name>>  extends Expr<Name, SMTSetSort<Name, ElemSort>, Z3_ast> {
  readonly __typename: 'Array';
  
  elemSort(): ElemSort;

  union(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;
  intersect(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;
  diff(b: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort>;
  
  hasSize(size: bigint | number | string | IntNum<Name>): Bool<Name>;

  add(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort>;
  del(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort>;
  complement(): SMTSet<Name, ElemSort>;
  
  contains(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): Bool<Name>;
  subsetOf(b: SMTSet<Name, ElemSort>): Bool<Name>;

}

/**
 * Defines the expression type of the body of a quantifier expression
 *
 * @category Quantifiers
 */
// prettier-ignore
export type BodyT<
  Name extends string = 'main',
  QVarSorts extends NonEmptySortArray<Name> = [Sort<Name>, ...Sort<Name>[]],
  QSort extends BoolSort<Name> | SMTArraySort<Name, QVarSorts> = BoolSort<Name> | SMTArraySort<Name, QVarSorts>,
> = QSort extends BoolSort<Name>
  ? Bool<Name>
  : QSort extends SMTArray<Name, QVarSorts, infer RangeSort>
  ? SortToExprMap<RangeSort, Name>
  : never;

/** @category Quantifiers */
export interface Quantifier<
  Name extends string = 'main',
  QVarSorts extends NonEmptySortArray<Name> = [Sort<Name>, ...Sort<Name>[]],
  QSort extends BoolSort<Name> | SMTArraySort<Name, QVarSorts> = BoolSort<Name> | SMTArraySort<Name, QVarSorts>,
> extends Expr<Name, QSort> {
  readonly __typename: 'NonLambdaQuantifier' | 'Lambda';

  is_forall(): boolean;

  is_exists(): boolean;

  is_lambda(): boolean;

  weight(): number;

  num_patterns(): number;

  pattern(i: number): Pattern<Name>;

  num_no_patterns(): number;

  no_pattern(i: number): Expr<Name>;

  body(): BodyT<Name, QVarSorts, QSort>;

  num_vars(): number;

  var_name(i: number): string | number;

  var_sort<T extends number>(i: T): QVarSorts[T];

  children(): [BodyT<Name, QVarSorts, QSort>];
}

export interface Probe<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Probe';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_probe;
}

/** @hidden */
export interface TacticCtor<Name extends string> {
  new (name: string): Tactic<Name>;
}

export interface Tactic<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Tactic';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_tactic;
}

/** @hidden */
export interface AstVectorCtor<Name extends string> {
  new <Item extends Ast<Name> = AnyAst<Name>>(): AstVector<Name, Item>;
}

/**
 * Stores multiple {@link Ast} objects
 *
 * ```typescript
 * const vector = new AstVector<Bool>();
 * vector.push(Bool.val(5));
 * vector.push(Bool.const('x'))
 *
 * vector.length
 * // 2
 * vector.get(1)
 * // x
 * [...vector.values()]
 * // [2, x]
 * ```
 */
export interface AstVector<Name extends string = 'main', Item extends Ast<Name> = AnyAst<Name>> extends Iterable<Item> {
  /** @hidden */
  readonly __typename: 'AstVector';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_ast_vector;

  length(): number;

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

/** @hidden */
export interface AstMapCtor<Name extends string> {
  new <Key extends Ast<Name> = AnyAst<Name>, Value extends Ast<Name> = AnyAst<Name>>(): AstMap<Name, Key, Value>;
}

/**
 * Stores a mapping between different {@link Ast} objects
 *
 * ```typescript
 * const map = new Map<Arith, Bool>();
 * const x = Int.const('x')
 * const y = Int.const('y')
 * map.set(x, Bool.val(true))
 * map.Set(y, Bool.val(false))
 *
 * map.size
 * // 2
 * map.has(x)
 * // true
 * [...map.entries()]
 * // [[x, true], [y, false]]
 * map.clear()
 * map.size
 * // 0
 * ```
 */
export interface AstMap<
  Name extends string = 'main',
  Key extends Ast<Name> = AnyAst<Name>,
  Value extends Ast<Name> = AnyAst<Name>,
> extends Iterable<[Key, Value]> {
  /** @hidden */
  readonly __typename: 'AstMap';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_ast_map;

  get size(): number;

  entries(): IterableIterator<[Key, Value]>;

  keys(): AstVector<Name, Key>;

  values(): IterableIterator<Value>;

  get(key: Key): Value | undefined;

  set(key: Key, value: Value): void;

  delete(key: Key): void;

  clear(): void;

  has(key: Key): boolean;

  sexpr(): string;
}

/**
 * @category Global
 */
export interface Z3HighLevel {
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

  /**
   * Set a Z3 parameter
   *
   * ```typescript
   * setParam('pp.decimal', true);
   * ```
   */
  setParam(key: string, value: any): void;

  /**
   * Set multiple Z3 parameters at once
   *
   * ```typescript
   * setParam({
   *   'pp.decimal': true,
   *   'pp.decimal_precision': 20
   * });
   * ```
   */
  setParam(key: Record<string, any>): void;

  /**
   * Resets all Z3 parameters
   */
  resetParams(): void;

  /**
   * Returns a global Z3 parameter
   */
  getParam(name: string): string | null;

  /**
   * Use this to create new contexts
   * @see {@link Context}
   */
  readonly Context: ContextCtor;
}
