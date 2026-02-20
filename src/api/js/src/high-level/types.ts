import {
  Z3_ast,
  Z3_ast_map,
  Z3_ast_print_mode,
  Z3_ast_vector,
  Z3_context,
  Z3_constructor,
  Z3_constructor_list,
  Z3_decl_kind,
  Z3_fixedpoint,
  Z3_func_decl,
  Z3_func_entry,
  Z3_func_interp,
  Z3_model,
  Z3_probe,
  Z3_solver,
  Z3_optimize,
  Z3_sort,
  Z3_sort_kind,
  Z3_stats,
  Z3_tactic,
  Z3_goal,
  Z3_apply_result,
  Z3_goal_prec,
  Z3_param_descrs,
  Z3_params,
  Z3_simplifier,
} from '../low-level';

/** @hidden */
export type AnySort<Name extends string = 'main'> =
  | Sort<Name>
  | BoolSort<Name>
  | ArithSort<Name>
  | BitVecSort<number, Name>
  | SMTArraySort<Name>
  | FPSort<Name>
  | FPRMSort<Name>
  | SeqSort<Name>
  | ReSort<Name>;
/** @hidden */
export type AnyExpr<Name extends string = 'main'> =
  | Expr<Name>
  | Bool<Name>
  | Arith<Name>
  | IntNum<Name>
  | RatNum<Name>
  | BitVec<number, Name>
  | BitVecNum<number, Name>
  | SMTArray<Name>
  | FP<Name>
  | FPNum<Name>
  | FPRM<Name>
  | Seq<Name>
  | Re<Name>
  | FiniteSet<Name>;
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
  : S extends FPSort<Name>
  ? FP<Name>
  : S extends FPRMSort<Name>
  ? FPRM<Name>
  : S extends SeqSort<Name>
  ? Seq<Name>
  : S extends ReSort<Name>
  ? Re<Name>
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

/** @hidden */
export type CoercibleToFP<Name extends string = 'main'> = number | FP<Name>;

export type CoercibleRational = { numerator: bigint | number; denominator: bigint | number };

/** @hidden */
export type CoercibleToExpr<Name extends string = 'main'> =
  | number
  | string
  | bigint
  | boolean
  | CoercibleRational
  | Expr<Name>;

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
  : T extends FP<Name>
  ? CoercibleToFP<Name>
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
  new <Name extends string>(name: Name, options?: Record<string, any>): Context<Name>;
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

  /**
   * Set the pretty printing mode for ASTs.
   *
   * @param mode - The print mode to use:
   *   - Z3_PRINT_SMTLIB_FULL (0): Print AST nodes in SMTLIB verbose format.
   *   - Z3_PRINT_LOW_LEVEL (1): Print AST nodes using a low-level format.
   *   - Z3_PRINT_SMTLIB2_COMPLIANT (2): Print AST nodes in SMTLIB 2.x compliant format.
   *
   * @category Functions
   */
  setPrintMode(mode: Z3_ast_print_mode): void;

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
  isRCFNum(obj: unknown): obj is RCFNum<Name>;

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
  isFPSort(obj: unknown): obj is FPSort<Name>;

  /** @category Functions */
  isFP(obj: unknown): obj is FP<Name>;

  /** @category Functions */
  isFPVal(obj: unknown): obj is FPNum<Name>;

  /** @category Functions */
  isFPRMSort(obj: unknown): obj is FPRMSort<Name>;

  /** @category Functions */
  isFPRM(obj: unknown): obj is FPRM<Name>;

  /** @category Functions */
  isSeqSort(obj: unknown): obj is SeqSort<Name>;

  /** @category Functions */
  isSeq(obj: unknown): obj is Seq<Name>;

  /** @category Functions */
  isStringSort(obj: unknown): obj is SeqSort<Name>;

  /** @category Functions */
  isString(obj: unknown): obj is Seq<Name>;

  /** @category Functions */
  isFiniteSetSort(obj: unknown): obj is FiniteSetSort<Name>;

  /** @category Functions */
  isFiniteSet(obj: unknown): obj is FiniteSet<Name>;

  /** @category Functions */
  isProbe(obj: unknown): obj is Probe<Name>;

  /** @category Functions */
  isTactic(obj: unknown): obj is Tactic<Name>;

  /** @category Functions */
  isGoal(obj: unknown): obj is Goal<Name>;

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

  readonly Fixedpoint: new () => Fixedpoint<Name>;

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
  /** @category Classes */
  readonly Goal: new (models?: boolean, unsat_cores?: boolean, proofs?: boolean) => Goal<Name>;
  /** @category Classes */
  readonly Params: new () => Params<Name>;
  /** @category Classes */
  readonly Simplifier: new (name: string) => Simplifier<Name>;

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
  readonly RCFNum: RCFNumCreation<Name>;
  /** @category Expressions */
  readonly BitVec: BitVecCreation<Name>;
  /** @category Expressions */
  readonly Float: FPCreation<Name>;
  /** @category Expressions */
  readonly FloatRM: FPRMCreation<Name>;
  /** @category Expressions */
  readonly String: StringCreation<Name>;
  /** @category Expressions */
  readonly Seq: SeqCreation<Name>;
  /** @category Expressions */
  readonly Re: ReCreation<Name>;
  /** @category Expressions */
  readonly Array: SMTArrayCreation<Name>;
  /** @category Expressions */
  readonly Set: SMTSetCreation<Name>;
  /** @category Expressions */
  readonly FiniteSet: FiniteSetCreation<Name>;
  /** @category Expressions */
  readonly Datatype: DatatypeCreation<Name>;

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

  /** @category Operations */
  AtMost(args: [Bool<Name>, ...Bool<Name>[]], k: number): Bool<Name>;

  /** @category Operations */
  AtLeast(args: [Bool<Name>, ...Bool<Name>[]], k: number): Bool<Name>;

  // Tactic Combinators

  /**
   * Compose two tactics sequentially. Applies t1 to a goal, then t2 to each subgoal.
   * @category Tactics
   */
  AndThen(t1: Tactic<Name> | string, t2: Tactic<Name> | string, ...ts: (Tactic<Name> | string)[]): Tactic<Name>;

  /**
   * Create a tactic that applies t1, and if it fails, applies t2.
   * @category Tactics
   */
  OrElse(t1: Tactic<Name> | string, t2: Tactic<Name> | string, ...ts: (Tactic<Name> | string)[]): Tactic<Name>;

  /**
   * Repeat a tactic up to max times (default: unbounded).
   * @category Tactics
   */
  Repeat(t: Tactic<Name> | string, max?: number): Tactic<Name>;

  /**
   * Apply tactic with a timeout in milliseconds.
   * @category Tactics
   */
  TryFor(t: Tactic<Name> | string, ms: number): Tactic<Name>;

  /**
   * Apply tactic only if probe condition is true.
   * @category Tactics
   */
  When(p: Probe<Name>, t: Tactic<Name> | string): Tactic<Name>;

  /**
   * Create a tactic that always succeeds and does nothing (skip).
   * @category Tactics
   */
  Skip(): Tactic<Name>;

  /**
   * Create a tactic that always fails.
   * @category Tactics
   */
  Fail(): Tactic<Name>;

  /**
   * Create a tactic that fails if probe condition is true.
   * @category Tactics
   */
  FailIf(p: Probe<Name>): Tactic<Name>;

  /**
   * Apply tactics in parallel and return first successful result.
   * @category Tactics
   */
  ParOr(...tactics: (Tactic<Name> | string)[]): Tactic<Name>;

  /**
   * Compose two tactics in parallel (t1 and then t2 in parallel).
   * @category Tactics
   */
  ParAndThen(t1: Tactic<Name> | string, t2: Tactic<Name> | string): Tactic<Name>;

  /**
   * Apply tactic with given parameters.
   * @category Tactics
   */
  With(t: Tactic<Name> | string, params: Record<string, any>): Tactic<Name>;

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
  Ext<DomainSort extends NonEmptySortArray<Name>, RangeSort extends Sort<Name> = Sort<Name>>(
    a: SMTArray<Name, DomainSort, RangeSort>,
    b: SMTArray<Name, DomainSort, RangeSort>,
  ): SortToExprMap<DomainSort[0], Name>;

  /** @category Operations */
  Extract<Bits extends number>(hi: number, lo: number, val: BitVec<Bits, Name>): BitVec<number, Name>;

  /** @category Operations */
  ast_from_string(s: string): Ast<Name>;

  /** @category Operations */
  substitute(t: Expr<Name>, ...substitutions: [Expr<Name>, Expr<Name>][]): Expr<Name>;

  /** @category Operations */
  substituteVars(t: Expr<Name>, ...to: Expr<Name>[]): Expr<Name>;

  /** @category Operations */
  substituteFuns(t: Expr<Name>, ...substitutions: [FuncDecl<Name>, Expr<Name>][]): Expr<Name>;

  /** @category Operations */
  updateField(t: DatatypeExpr<Name>, fieldAccessor: FuncDecl<Name>, newValue: Expr<Name>): DatatypeExpr<Name>;

  simplify(expr: Expr<Name>): Promise<Expr<Name>>;

  /** @category Operations */
  SetUnion<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetIntersect<ElemSort extends AnySort<Name>>(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetDifference<ElemSort extends AnySort<Name>>(
    a: SMTSet<Name, ElemSort>,
    b: SMTSet<Name, ElemSort>,
  ): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetAdd<ElemSort extends AnySort<Name>>(
    set: SMTSet<Name, ElemSort>,
    elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>,
  ): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetDel<ElemSort extends AnySort<Name>>(
    set: SMTSet<Name, ElemSort>,
    elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>,
  ): SMTSet<Name, ElemSort>;

  /** @category Operations */
  SetComplement<ElemSort extends AnySort<Name>>(set: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort>;

  /** @category Operations */
  EmptySet<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort>;

  /** @category Operations */
  FullSet<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort>;

  /** @category Operations */
  isMember<ElemSort extends AnySort<Name>>(
    elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>,
    set: SMTSet<Name, ElemSort>,
  ): Bool<Name>;

  /** @category Operations */
  isSubset<ElemSort extends AnySort<Name>>(a: SMTSet<Name, ElemSort>, b: SMTSet<Name, ElemSort>): Bool<Name>;

  //////////////////////
  // Regular Expressions
  //////////////////////

  /** @category RegularExpression */
  InRe(seq: Seq<Name> | string, re: Re<Name>): Bool<Name>;

  /** @category RegularExpression */
  Union<SeqSortRef extends SeqSort<Name>>(...res: Re<Name, SeqSortRef>[]): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Intersect<SeqSortRef extends SeqSort<Name>>(...res: Re<Name, SeqSortRef>[]): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  ReConcat<SeqSortRef extends SeqSort<Name>>(...res: Re<Name, SeqSortRef>[]): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Plus<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Star<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Option<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Complement<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Diff<SeqSortRef extends SeqSort<Name>>(a: Re<Name, SeqSortRef>, b: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Range<SeqSortRef extends SeqSort<Name>>(lo: Seq<Name, SeqSortRef> | string, hi: Seq<Name, SeqSortRef> | string): Re<Name, SeqSortRef>;

  /**
   * Create a bounded repetition regex
   * @param re The regex to repeat
   * @param lo Minimum number of repetitions
   * @param hi Maximum number of repetitions (0 means unbounded, i.e., at least lo)
   * @category RegularExpression
   */
  Loop<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>, lo: number, hi?: number): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Power<SeqSortRef extends SeqSort<Name>>(re: Re<Name, SeqSortRef>, n: number): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  AllChar<SeqSortRef extends SeqSort<Name>>(reSort: ReSort<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Empty<SeqSortRef extends SeqSort<Name>>(reSort: ReSort<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category RegularExpression */
  Full<SeqSortRef extends SeqSort<Name>>(reSort: ReSort<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /**
   * Create a partial order relation over a sort.
   * @param sort The sort of the relation
   * @param index The index of the relation
   * @category Operations
   */
  mkPartialOrder(sort: Sort<Name>, index: number): FuncDecl<Name>;

  /**
   * Create the transitive closure of a binary relation.
   * The resulting relation is recursive.
   * @param f A binary relation represented as a function declaration
   * @category Operations
   */
  mkTransitiveClosure(f: FuncDecl<Name>): FuncDecl<Name>;

  /**
   * Return the nonzero subresultants of p and q with respect to the "variable" x.
   * Note that any subterm that cannot be viewed as a polynomial is assumed to be a variable.
   * @param p Arithmetic term
   * @param q Arithmetic term
   * @param x Variable with respect to which subresultants are computed
   * @category Operations
   */
  polynomialSubresultants(p: Arith<Name>, q: Arith<Name>, x: Arith<Name>): Promise<AstVector<Name, Arith<Name>>>;
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

  /**
   * Assert a constraint and associate it with a tracking literal (Boolean constant).
   * This is the TypeScript equivalent of `assertAndTrack` in other Z3 language bindings.
   *
   * When the solver returns `unsat`, the tracked literals that contributed to
   * unsatisfiability can be retrieved via {@link unsatCore}.
   *
   * @param expr - The Boolean expression to assert
   * @param constant - A Boolean constant (or its name as a string) used as the tracking literal
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * const p1 = Bool.const('p1');
   * const p2 = Bool.const('p2');
   * solver.addAndTrack(x.gt(0), p1);
   * solver.addAndTrack(x.lt(0), p2);
   * if (await solver.check() === 'unsat') {
   *   const core = solver.unsatCore(); // contains p1 and p2
   * }
   * ```
   */
  addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string): void;

  /**
   * Attach a simplifier to the solver for incremental pre-processing.
   * The solver will use the simplifier for incremental pre-processing of assertions.
   * @param simplifier - The simplifier to attach
   */
  addSimplifier(simplifier: Simplifier<Name>): void;

  assertions(): AstVector<Name, Bool<Name>>;

  fromString(s: string): void;

  /**
   * Check whether the assertions in the solver are consistent or not.
   *
   * Optionally, you can provide additional boolean expressions as assumptions.
   * These assumptions are temporary and only used for this check - they are not
   * permanently added to the solver.
   *
   * @param exprs - Optional assumptions to check in addition to the solver's assertions.
   *                These are temporary and do not modify the solver state.
   * @returns A promise resolving to:
   *          - `'sat'` if the assertions (plus assumptions) are satisfiable
   *          - `'unsat'` if they are unsatisfiable
   *          - `'unknown'` if Z3 cannot determine satisfiability
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * solver.add(x.gt(0));
   *
   * // Check without assumptions
   * await solver.check(); // 'sat'
   *
   * // Check with temporary assumption (doesn't modify solver)
   * await solver.check(x.lt(0)); // 'unsat'
   * await solver.check(); // still 'sat' - assumption was temporary
   * ```
   *
   * @see {@link unsatCore} - Retrieve unsat core after checking with assumptions
   */
  check(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): Promise<CheckSatResult>;

  /**
   * Retrieve the unsat core after a check that returned `'unsat'`.
   *
   * The unsat core is a (typically small) subset of the assumptions that were
   * sufficient to determine unsatisfiability. This is useful for understanding
   * which assumptions are conflicting.
   *
   * Note: To use unsat cores effectively, you should call {@link check} with
   * assumptions (not just assertions added via {@link add}).
   *
   * @returns An AstVector containing the subset of assumptions that caused UNSAT
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * const y = Bool.const('y');
   * const z = Bool.const('z');
   * solver.add(x.or(y));
   * solver.add(x.or(z));
   *
   * const result = await solver.check(x.not(), y.not(), z.not());
   * if (result === 'unsat') {
   *   const core = solver.unsatCore();
   *   // core will contain a minimal set of conflicting assumptions
   *   console.log('UNSAT core size:', core.length());
   * }
   * ```
   *
   * @see {@link check} - Check with assumptions to use with unsat core
   */
  unsatCore(): AstVector<Name, Bool<Name>>;

  model(): Model<Name>;

  /**
   * Retrieve statistics for the solver.
   * Returns performance metrics, memory usage, decision counts, and other diagnostic information.
   *
   * @returns A Statistics object containing solver metrics
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * solver.add(x.gt(0));
   * await solver.check();
   * const stats = solver.statistics();
   * console.log('Statistics size:', stats.size());
   * for (const entry of stats) {
   *   console.log(`${entry.key}: ${entry.value}`);
   * }
   * ```
   */
  statistics(): Statistics<Name>;

  /**
   * Return a string describing why the last call to {@link check} returned `'unknown'`.
   *
   * @returns A string explaining the reason, or an empty string if the last check didn't return unknown
   *
   * @example
   * ```typescript
   * const result = await solver.check();
   * if (result === 'unknown') {
   *   console.log('Reason:', solver.reasonUnknown());
   * }
   * ```
   */
  reasonUnknown(): string;

  /**
   * Retrieve the set of literals that were inferred by the solver as unit literals.
   * These are boolean literals that the solver has determined must be true in all models.
   *
   * @returns An AstVector containing the unit literals
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * solver.add(x.or(x)); // simplifies to x
   * await solver.check();
   * const units = solver.units();
   * console.log('Unit literals:', units.length());
   * ```
   */
  units(): AstVector<Name, Bool<Name>>;

  /**
   * Retrieve the set of tracked boolean literals that are not unit literals.
   *
   * @returns An AstVector containing the non-unit literals
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * const y = Bool.const('y');
   * solver.add(x.or(y));
   * await solver.check();
   * const nonUnits = solver.nonUnits();
   * ```
   */
  nonUnits(): AstVector<Name, Bool<Name>>;

  /**
   * Retrieve the trail of boolean literals assigned by the solver during solving.
   * The trail represents the sequence of decisions and propagations made by the solver.
   *
   * @returns An AstVector containing the trail of assigned literals
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * const y = Bool.const('y');
   * solver.add(x.implies(y));
   * solver.add(x);
   * await solver.check();
   * const trail = solver.trail();
   * console.log('Trail length:', trail.length());
   * ```
   */
  trail(): AstVector<Name, Bool<Name>>;

  /**
   * Retrieve the decision levels for each literal in the solver's trail.
   * The returned array has one entry per trail literal, indicating at which
   * decision level it was assigned.
   *
   * @returns An array of numbers where element i is the decision level of the i-th trail literal
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * solver.add(x);
   * await solver.check();
   * const levels = solver.trailLevels();
   * console.log('Trail levels:', levels);
   * ```
   */
  trailLevels(): number[];

  /**
   * Extract cubes from the solver for cube-and-conquer parallel solving.
   * Each call returns the next cube (conjunction of literals) from the solver.
   * Returns an empty AstVector when the search space is exhausted.
   *
   * @param vars - Optional vector of variables to use as cube variables
   * @param cutoff - Backtrack level cutoff for cube generation (default: 0xFFFFFFFF)
   * @returns A promise resolving to an AstVector containing the cube literals
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * const y = Bool.const('y');
   * solver.add(x.or(y));
   * const cube = await solver.cube(undefined, 1);
   * console.log('Cube length:', cube.length());
   * ```
   */
  cube(vars?: AstVector<Name, Bool<Name>>, cutoff?: number): Promise<AstVector<Name, Bool<Name>>>;

  /**
   * Retrieve fixed assignments to a set of variables as consequences given assumptions.
   * Each consequence is an implication: assumptions => variable = value.
   *
   * @param assumptions - Assumptions to use during consequence finding
   * @param variables - Variables to find consequences for
   * @returns A promise resolving to the status and a vector of consequence expressions
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Bool.const('x');
   * const y = Bool.const('y');
   * solver.add(x.implies(y));
   * const [status, consequences] = await solver.getConsequences([], [x, y]);
   * ```
   */
  getConsequences(
    assumptions: (Bool<Name> | AstVector<Name, Bool<Name>>)[],
    variables: Expr<Name>[],
  ): Promise<[CheckSatResult, AstVector<Name, Bool<Name>>]>;

  /**
   * Solve constraints treating given variables symbolically, replacing their
   * occurrences by terms. Guards condition the substitutions.
   *
   * @param variables - Variables to solve for
   * @param terms - Substitution terms for the variables
   * @param guards - Boolean guards for the substitutions
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * const y = Int.const('y');
   * solver.add(x.eq(y.add(1)));
   * solver.solveFor([x], [y.add(1)], []);
   * ```
   */
  solveFor(variables: Expr<Name>[], terms: Expr<Name>[], guards: Bool<Name>[]): void;

  /**
   * Set an initial value hint for a variable to guide the solver's search heuristics.
   * This can improve performance when a good initial value is known.
   *
   * @param variable - The variable to set an initial value for
   * @param value - The initial value for the variable
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * solver.setInitialValue(x, Int.val(42));
   * solver.add(x.gt(0));
   * await solver.check();
   * ```
   */
  setInitialValue(variable: Expr<Name>, value: Expr<Name>): void;

  /**
   * Retrieve the root of the congruence class containing the given expression.
   * This is useful for understanding equality reasoning in the solver.
   *
   * Note: This works primarily with SimpleSolver and may not work with terms
   * eliminated during preprocessing.
   *
   * @param expr - The expression to find the congruence root for
   * @returns The root expression of the congruence class
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * const y = Int.const('y');
   * solver.add(x.eq(y));
   * await solver.check();
   * const root = solver.congruenceRoot(x);
   * ```
   */
  congruenceRoot(expr: Expr<Name>): Expr<Name>;

  /**
   * Retrieve the next expression in the congruence class containing the given expression.
   * The congruence class forms a circular linked list.
   *
   * Note: This works primarily with SimpleSolver and may not work with terms
   * eliminated during preprocessing.
   *
   * @param expr - The expression to find the next congruent expression for
   * @returns The next expression in the congruence class
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * const y = Int.const('y');
   * const z = Int.const('z');
   * solver.add(x.eq(y));
   * solver.add(y.eq(z));
   * await solver.check();
   * const next = solver.congruenceNext(x);
   * ```
   */
  congruenceNext(expr: Expr<Name>): Expr<Name>;

  /**
   * Explain why two expressions are congruent according to the solver's reasoning.
   * Returns a proof term explaining the congruence.
   *
   * Note: This works primarily with SimpleSolver and may not work with terms
   * eliminated during preprocessing.
   *
   * @param a - First expression
   * @param b - Second expression
   * @returns An expression representing the proof of congruence
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * const y = Int.const('y');
   * solver.add(x.eq(y));
   * await solver.check();
   * const explanation = solver.congruenceExplain(x, y);
   * ```
   */
  congruenceExplain(a: Expr<Name>, b: Expr<Name>): Expr<Name>;

  /**
   * Load SMT-LIB2 format assertions from a file into the solver.
   *
   * @param filename - Path to the file containing SMT-LIB2 format assertions
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * solver.fromFile('problem.smt2');
   * const result = await solver.check();
   * ```
   */
  fromFile(filename: string): void;

  /**
   * Convert the solver's assertions to SMT-LIB2 format as a benchmark.
   * 
   * This exports the current set of assertions in the solver as an SMT-LIB2 string,
   * which can be used for bug reporting, sharing problems, or benchmarking.
   *
   * @param status - Status string such as "sat", "unsat", or "unknown" (default: "unknown")
   * @returns A string representation of the solver's assertions in SMT-LIB2 format
   *
   * @example
   * ```typescript
   * const solver = new Solver();
   * const x = Int.const('x');
   * const y = Int.const('y');
   * solver.add(x.gt(0));
   * solver.add(y.eq(x.add(1)));
   * const smtlib2 = solver.toSmtlib2('unknown');
   * console.log(smtlib2); // Prints SMT-LIB2 formatted problem
   * ```
   */
  toSmtlib2(status?: string): string;

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

  /**
   * Assert a constraint and associate it with a tracking literal (Boolean constant).
   * This is the TypeScript equivalent of `assertAndTrack` in other Z3 language bindings.
   *
   * When the optimizer returns `unsat`, the tracked literals that contributed to
   * unsatisfiability can be used to identify which constraints caused the conflict.
   *
   * @param expr - The Boolean expression to assert
   * @param constant - A Boolean constant (or its name as a string) used as the tracking literal
   *
   * @example
   * ```typescript
   * const opt = new Optimize();
   * const x = Int.const('x');
   * const p1 = Bool.const('p1');
   * const p2 = Bool.const('p2');
   * opt.addAndTrack(x.gt(0), p1);
   * opt.addAndTrack(x.lt(0), p2);
   * const result = await opt.check(); // 'unsat'
   * ```
   */
  addAndTrack(expr: Bool<Name>, constant: Bool<Name> | string): void;

  assertions(): AstVector<Name, Bool<Name>>;

  fromString(s: string): void;

  maximize(expr: Arith<Name>): void;

  minimize(expr: Arith<Name>): void;

  check(...exprs: (Bool<Name> | AstVector<Name, Bool<Name>>)[]): Promise<CheckSatResult>;

  model(): Model<Name>;

  statistics(): Statistics<Name>;

  /**
   * Set an initial value hint for a variable to guide the optimizer's search heuristics.
   * This can improve performance when a good initial value is known.
   *
   * @param variable - The variable to set an initial value for
   * @param value - The initial value for the variable
   *
   * @example
   * ```typescript
   * const opt = new Optimize();
   * const x = Int.const('x');
   * opt.setInitialValue(x, Int.val(42));
   * opt.add(x.gt(0));
   * opt.maximize(x);
   * await opt.check();
   * ```
   */
  setInitialValue(variable: Expr<Name>, value: Expr<Name>): void;

  /**
   * Manually decrease the reference count of the optimize
   * This is automatically done when the optimize is garbage collected,
   * but calling this eagerly can help release memory sooner.
   */
  release(): void;
}

export interface Fixedpoint<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Fixedpoint';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_fixedpoint;

  /**
   * Set a configuration option for the fixedpoint solver.
   * @param key - Configuration parameter name
   * @param value - Configuration parameter value
   */
  set(key: string, value: any): void;

  /**
   * Return a string describing all available options.
   */
  help(): string;

  /**
   * Assert a constraint (or multiple) into the fixedpoint solver as background axioms.
   */
  add(...constraints: Bool<Name>[]): void;

  /**
   * Register a predicate as a recursive relation.
   * @param pred - Function declaration to register as a recursive relation
   */
  registerRelation(pred: FuncDecl<Name>): void;

  /**
   * Add a rule (Horn clause) to the fixedpoint solver.
   * @param rule - The rule as a Boolean expression (implication)
   * @param name - Optional name for the rule
   */
  addRule(rule: Bool<Name>, name?: string): void;

  /**
   * Add a table fact to the fixedpoint solver.
   * @param pred - The predicate (function declaration)
   * @param args - Arguments to the predicate as integers
   */
  addFact(pred: FuncDecl<Name>, ...args: number[]): void;

  /**
   * Update a named rule in the fixedpoint solver.
   * @param rule - The rule as a Boolean expression (implication)
   * @param name - Name of the rule to update
   */
  updateRule(rule: Bool<Name>, name: string): void;

  /**
   * Query the fixedpoint solver to determine if the formula is derivable.
   * @param query - The query as a Boolean expression
   * @returns A promise that resolves to 'sat', 'unsat', or 'unknown'
   */
  query(query: Bool<Name>): Promise<CheckSatResult>;

  /**
   * Query the fixedpoint solver for a set of relations.
   * @param relations - Array of function declarations representing relations to query
   * @returns A promise that resolves to 'sat', 'unsat', or 'unknown'
   */
  queryRelations(...relations: FuncDecl<Name>[]): Promise<CheckSatResult>;

  /**
   * Retrieve the answer (satisfying instance or proof of unsatisfiability) from the last query.
   * @returns Expression containing the answer, or null if not available
   */
  getAnswer(): Expr<Name> | null;

  /**
   * Retrieve the reason why the fixedpoint engine returned 'unknown'.
   * @returns A string explaining why the result was unknown
   */
  getReasonUnknown(): string;

  /**
   * Retrieve the number of levels explored for a given predicate.
   * @param pred - The predicate function declaration
   * @returns The number of levels
   */
  getNumLevels(pred: FuncDecl<Name>): number;

  /**
   * Retrieve the cover of a predicate at a given level.
   * @param level - The level to query
   * @param pred - The predicate function declaration
   * @returns Expression representing the cover, or null if not available
   */
  getCoverDelta(level: number, pred: FuncDecl<Name>): Expr<Name> | null;

  /**
   * Add a property about the predicate at the given level.
   * @param level - The level to add the property at
   * @param pred - The predicate function declaration
   * @param property - The property as an expression
   */
  addCover(level: number, pred: FuncDecl<Name>, property: Expr<Name>): void;

  /**
   * Retrieve set of rules added to the fixedpoint context.
   * @returns Vector of rules
   */
  getRules(): AstVector<Name, Bool<Name>>;

  /**
   * Retrieve set of assertions added to the fixedpoint context.
   * @returns Vector of assertions
   */
  getAssertions(): AstVector<Name, Bool<Name>>;

  /**
   * Set predicate representation for the Datalog engine.
   * @param pred - The predicate function declaration
   * @param kinds - Array of representation kinds
   */
  setPredicateRepresentation(pred: FuncDecl<Name>, kinds: string[]): void;

  /**
   * Convert the fixedpoint context to a string.
   * @returns String representation of the fixedpoint context
   */
  toString(): string;

  /**
   * Parse an SMT-LIB2 string with fixedpoint rules and add them to the context.
   * @param s - SMT-LIB2 string to parse
   * @returns Vector of queries from the parsed string
   */
  fromString(s: string): AstVector<Name, Bool<Name>>;

  /**
   * Parse an SMT-LIB2 file with fixedpoint rules and add them to the context.
   * @param file - Path to the file to parse
   * @returns Vector of queries from the parsed file
   */
  fromFile(file: string): AstVector<Name, Bool<Name>>;

  /**
   * Retrieve statistics for the fixedpoint solver.
   * Returns performance metrics and diagnostic information.
   * @returns A Statistics object containing solver metrics
   */
  statistics(): Statistics<Name>;

  /**
   * Manually decrease the reference count of the fixedpoint
   * This is automatically done when the fixedpoint is garbage collected,
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
   * Return the number of uninterpreted sorts that have an interpretation in the model.
   *
   * @returns The number of uninterpreted sorts
   *
   * @example
   * ```typescript
   * const { Solver, Sort } = await init();
   * const solver = new Solver();
   * const A = Sort.declare('A');
   * const x = Const('x', A);
   * solver.add(x.eq(x));
   * await solver.check();
   * const model = solver.model();
   * console.log('Number of sorts:', model.numSorts());
   * ```
   */
  numSorts(): number;

  /**
   * Return the uninterpreted sort at the given index.
   *
   * @param i - Index of the sort (must be less than numSorts())
   * @returns The sort at the given index
   *
   * @example
   * ```typescript
   * const model = solver.model();
   * for (let i = 0; i < model.numSorts(); i++) {
   *   const sort = model.getSort(i);
   *   console.log('Sort:', sort.toString());
   * }
   * ```
   */
  getSort(i: number): Sort<Name>;

  /**
   * Return all uninterpreted sorts that have an interpretation in the model.
   *
   * @returns An array of all uninterpreted sorts
   *
   * @example
   * ```typescript
   * const model = solver.model();
   * const sorts = model.getSorts();
   * for (const sort of sorts) {
   *   console.log('Sort:', sort.toString());
   *   const universe = model.sortUniverse(sort);
   *   console.log('Universe size:', universe.length());
   * }
   * ```
   */
  getSorts(): Sort<Name>[];

  /**
   * Return the finite set of elements that represent the interpretation for the given sort.
   * This is only applicable to uninterpreted sorts with finite interpretations.
   *
   * @param sort - The sort to get the universe for
   * @returns An AstVector containing all elements in the sort's universe
   *
   * @example
   * ```typescript
   * const { Solver, Sort, Const } = await init();
   * const solver = new Solver();
   * const A = Sort.declare('A');
   * const x = Const('x', A);
   * const y = Const('y', A);
   * solver.add(x.neq(y));
   * await solver.check();
   * const model = solver.model();
   * const universe = model.sortUniverse(A);
   * console.log('Universe has', universe.length(), 'elements');
   * for (let i = 0; i < universe.length(); i++) {
   *   console.log('Element:', universe.get(i).toString());
   * }
   * ```
   */
  sortUniverse(sort: Sort<Name>): AstVector<Name, AnyExpr<Name>>;

  /**
   * Manually decrease the reference count of the model
   * This is automatically done when the model is garbage collected,
   * but calling this eagerly can help release memory sooner.
   */
  release(): void;
}

/**
 * Statistics entry representing a single key-value pair from solver statistics
 */
export interface StatisticsEntry<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'StatisticsEntry';

  /** The key/name of this statistic */
  readonly key: string;

  /** The numeric value of this statistic */
  readonly value: number;

  /** True if this statistic is stored as an unsigned integer */
  readonly isUint: boolean;

  /** True if this statistic is stored as a double */
  readonly isDouble: boolean;
}

export interface StatisticsCtor<Name extends string> {
  new (): Statistics<Name>;
}

/**
 * Statistics for solver operations
 *
 * Provides access to performance metrics, memory usage, decision counts,
 * and other diagnostic information from solver operations.
 */
export interface Statistics<Name extends string = 'main'> extends Iterable<StatisticsEntry<Name>> {
  /** @hidden */
  readonly __typename: 'Statistics';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_stats;

  /**
   * Return the number of statistical data points
   * @returns The number of statistics entries
   */
  size(): number;

  /**
   * Return the keys of all statistical data
   * @returns Array of statistic keys
   */
  keys(): string[];

  /**
   * Return a specific statistic value by key
   * @param key - The key of the statistic to retrieve
   * @returns The numeric value of the statistic
   * @throws Error if the key doesn't exist
   */
  get(key: string): number;

  /**
   * Return all statistics as an array of entries
   * @returns Array of all statistics entries
   */
  entries(): StatisticsEntry<Name>[];

  /**
   * Manually decrease the reference count of the statistics object
   * This is automatically done when the statistics is garbage collected,
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
    | SMTArraySort['__typename']
    | DatatypeSort['__typename']
    | FPSort['__typename']
    | FPRMSort['__typename']
    | SeqSort['__typename']
    | ReSort['__typename']
    | FiniteSetSort['__typename'];

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
    | FP['__typename']
    | FPRM['__typename']
    | Seq['__typename']
    | Re['__typename']
    | SMTArray['__typename']
    | DatatypeExpr['__typename']
    | FiniteSet['__typename'];

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
 * A Real Closed Field (RCF) numeral.
 *
 * RCF numerals can represent:
 * - Rational numbers
 * - Algebraic numbers (roots of polynomials)
 * - Transcendental extensions (e.g., pi, e)
 * - Infinitesimal extensions
 *
 * ```typescript
 * const { RCFNum } = Context('main');
 *
 * // Create pi
 * const pi = RCFNum.pi();
 * console.log(pi.toDecimal(10)); // "3.1415926536"
 *
 * // Create a rational
 * const half = new RCFNum('1/2');
 *
 * // Arithmetic
 * const sum = pi.add(half);
 *
 * // Check properties
 * console.log(pi.isTranscendental()); // true
 * console.log(half.isRational()); // true
 * ```
 * @category Arithmetic
 */
export interface RCFNum<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'RCFNum';

  /** @hidden */
  readonly ctx: Context<Name>;

  /**
   * Add two RCF numerals.
   * @param other - The RCF numeral to add
   * @returns this + other
   */
  add(other: RCFNum<Name>): RCFNum<Name>;

  /**
   * Subtract two RCF numerals.
   * @param other - The RCF numeral to subtract
   * @returns this - other
   */
  sub(other: RCFNum<Name>): RCFNum<Name>;

  /**
   * Multiply two RCF numerals.
   * @param other - The RCF numeral to multiply
   * @returns this * other
   */
  mul(other: RCFNum<Name>): RCFNum<Name>;

  /**
   * Divide two RCF numerals.
   * @param other - The RCF numeral to divide by
   * @returns this / other
   */
  div(other: RCFNum<Name>): RCFNum<Name>;

  /**
   * Negate this RCF numeral.
   * @returns -this
   */
  neg(): RCFNum<Name>;

  /**
   * Compute the multiplicative inverse.
   * @returns 1/this
   */
  inv(): RCFNum<Name>;

  /**
   * Raise this RCF numeral to a power.
   * @param k - The exponent
   * @returns this^k
   */
  power(k: number): RCFNum<Name>;

  /**
   * Check if this RCF numeral is less than another.
   * @param other - The RCF numeral to compare with
   * @returns true if this < other
   */
  lt(other: RCFNum<Name>): boolean;

  /**
   * Check if this RCF numeral is greater than another.
   * @param other - The RCF numeral to compare with
   * @returns true if this > other
   */
  gt(other: RCFNum<Name>): boolean;

  /**
   * Check if this RCF numeral is less than or equal to another.
   * @param other - The RCF numeral to compare with
   * @returns true if this <= other
   */
  le(other: RCFNum<Name>): boolean;

  /**
   * Check if this RCF numeral is greater than or equal to another.
   * @param other - The RCF numeral to compare with
   * @returns true if this >= other
   */
  ge(other: RCFNum<Name>): boolean;

  /**
   * Check if this RCF numeral is equal to another.
   * @param other - The RCF numeral to compare with
   * @returns true if this == other
   */
  eq(other: RCFNum<Name>): boolean;

  /**
   * Check if this RCF numeral is not equal to another.
   * @param other - The RCF numeral to compare with
   * @returns true if this != other
   */
  neq(other: RCFNum<Name>): boolean;

  /**
   * Check if this RCF numeral is a rational number.
   * @returns true if this is rational
   */
  isRational(): boolean;

  /**
   * Check if this RCF numeral is an algebraic number.
   * @returns true if this is algebraic
   */
  isAlgebraic(): boolean;

  /**
   * Check if this RCF numeral is an infinitesimal.
   * @returns true if this is infinitesimal
   */
  isInfinitesimal(): boolean;

  /**
   * Check if this RCF numeral is a transcendental number.
   * @returns true if this is transcendental
   */
  isTranscendental(): boolean;

  /**
   * Convert this RCF numeral to a string.
   * @param compact - If true, use compact representation
   * @returns String representation
   */
  toString(compact?: boolean): string;

  /**
   * Convert this RCF numeral to a decimal string.
   * @param precision - Number of decimal places
   * @returns Decimal string representation
   */
  toDecimal(precision: number): string;
}

/**
 * Creation interface for RCF numerals
 * @category Arithmetic
 */
export interface RCFNumCreation<Name extends string> {
  /**
   * Create an RCF numeral from a rational string.
   * @param value - String representation of a rational number (e.g., "3/2", "0.5", "42")
   */
  (value: string): RCFNum<Name>;

  /**
   * Create an RCF numeral from a small integer.
   * @param value - Integer value
   */
  (value: number): RCFNum<Name>;

  /**
   * Create an RCF numeral representing pi.
   */
  pi(): RCFNum<Name>;

  /**
   * Create an RCF numeral representing e (Euler's constant).
   */
  e(): RCFNum<Name>;

  /**
   * Create an RCF numeral representing an infinitesimal.
   */
  infinitesimal(): RCFNum<Name>;

  /**
   * Find roots of a polynomial.
   *
   * The polynomial is a[n-1]*x^(n-1) + ... + a[1]*x + a[0].
   *
   * @param coefficients - Polynomial coefficients (constant term first)
   * @returns Array of RCF numerals representing the roots
   */
  roots(coefficients: RCFNum<Name>[]): RCFNum<Name>[];
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
  subNoUnderflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name>;

  /** @category Boolean */
  sdivNoOverflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

  /** @category Boolean */
  mulNoOverflow(other: CoercibleToBitVec<Bits, Name>, isSigned: boolean): Bool<Name>;

  /** @category Boolean */
  mulNoUnderflow(other: CoercibleToBitVec<Bits, Name>): Bool<Name>;

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

  /**
   * Access the array default value.
   * Produces the default range value, for arrays that can be represented as
   * finite maps with a default range value.
   */
  default(): SortToExprMap<RangeSort, Name>;
}

/**
 * Set Implemented using Arrays
 *
 * @typeParam ElemSort The sort of the element of the set
 * @category Sets
 */
export type SMTSetSort<Name extends string = 'main', ElemSort extends AnySort<Name> = Sort<Name>> = SMTArraySort<
  Name,
  [ElemSort],
  BoolSort<Name>
>;

/** @category Sets*/
export interface SMTSetCreation<Name extends string> {
  sort<ElemSort extends AnySort<Name>>(elemSort: ElemSort): SMTSetSort<Name, ElemSort>;

  const<ElemSort extends AnySort<Name>>(name: string, elemSort: ElemSort): SMTSet<Name, ElemSort>;

  consts<ElemSort extends AnySort<Name>>(names: string | string[], elemSort: ElemSort): SMTSet<Name, ElemSort>[];

  empty<ElemSort extends AnySort<Name>>(sort: ElemSort): SMTSet<Name, ElemSort>;

  val<ElemSort extends AnySort<Name>>(
    values: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>[],
    sort: ElemSort,
  ): SMTSet<Name, ElemSort>;
}

/**
 * Represents Set expression
 *
 * @typeParam ElemSort The sort of the element of the set
 * @category Arrays
 */
export interface SMTSet<Name extends string = 'main', ElemSort extends AnySort<Name> = Sort<Name>>
  extends Expr<Name, SMTSetSort<Name, ElemSort>, Z3_ast> {
  readonly __typename: 'Array';

  elemSort(): ElemSort;

  union(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;
  intersect(...args: SMTSet<Name, ElemSort>[]): SMTSet<Name, ElemSort>;
  diff(b: SMTSet<Name, ElemSort>): SMTSet<Name, ElemSort>;

  add(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort>;
  del(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): SMTSet<Name, ElemSort>;
  complement(): SMTSet<Name, ElemSort>;

  contains(elem: CoercibleToMap<SortToExprMap<ElemSort, Name>, Name>): Bool<Name>;
  subsetOf(b: SMTSet<Name, ElemSort>): Bool<Name>;
}
//////////////////////////////////////////
//
// Finite Sets
//
//////////////////////////////////////////

/**
 * Represents a finite set sort
 *
 * @typeParam ElemSort The sort of elements in the finite set
 * @category Finite Sets
 */
export interface FiniteSetSort<Name extends string = 'main', ElemSort extends Sort<Name> = Sort<Name>>
  extends Sort<Name> {
  readonly __typename: 'FiniteSetSort';
  /** Returns the element sort of this finite set sort */
  elemSort(): ElemSort;
}

/** @category Finite Sets */
export interface FiniteSetCreation<Name extends string> {
  sort<ElemSort extends Sort<Name>>(elemSort: ElemSort): FiniteSetSort<Name, ElemSort>;

  const<ElemSort extends Sort<Name>>(name: string, elemSort: ElemSort): FiniteSet<Name, ElemSort>;

  consts<ElemSort extends Sort<Name>>(names: string | string[], elemSort: ElemSort): FiniteSet<Name, ElemSort>[];

  empty<ElemSort extends Sort<Name>>(sort: ElemSort): FiniteSet<Name, ElemSort>;

  singleton<ElemSort extends Sort<Name>>(elem: Expr<Name>): FiniteSet<Name, ElemSort>;

  range(low: Expr<Name>, high: Expr<Name>): FiniteSet<Name, Sort<Name>>;
}

/**
 * Represents a finite set expression
 *
 * @typeParam ElemSort The sort of elements in the finite set
 * @category Finite Sets
 */
export interface FiniteSet<Name extends string = 'main', ElemSort extends Sort<Name> = Sort<Name>>
  extends Expr<Name, FiniteSetSort<Name, ElemSort>, Z3_ast> {
  readonly __typename: 'FiniteSet';

  union(other: FiniteSet<Name, ElemSort>): FiniteSet<Name, ElemSort>;
  intersect(other: FiniteSet<Name, ElemSort>): FiniteSet<Name, ElemSort>;
  diff(other: FiniteSet<Name, ElemSort>): FiniteSet<Name, ElemSort>;
  contains(elem: Expr<Name>): Bool<Name>;
  size(): Expr<Name>;
  subsetOf(other: FiniteSet<Name, ElemSort>): Bool<Name>;
  map(f: Expr<Name>): FiniteSet<Name, Sort<Name>>;
  filter(f: Expr<Name>): FiniteSet<Name, ElemSort>;
}

//////////////////////////////////////////
//
// Datatypes
//
//////////////////////////////////////////

/**
 * Helper class for declaring Z3 datatypes.
 *
 * Follows the same pattern as Python Z3 API for declaring constructors
 * before creating the actual datatype sort.
 *
 * @example
 * ```typescript
 * const List = new ctx.Datatype('List');
 * List.declare('cons', ['car', ctx.Int.sort()], ['cdr', List]);
 * List.declare('nil');
 * const ListSort = List.create();
 * ```
 *
 * @category Datatypes
 */
export interface Datatype<Name extends string = 'main'> {
  readonly ctx: Context<Name>;
  readonly name: string;

  /**
   * Declare a constructor for this datatype.
   *
   * @param name Constructor name
   * @param fields Array of [field_name, field_sort] pairs
   */
  declare(name: string, ...fields: Array<[string, AnySort<Name> | Datatype<Name>]>): this;

  /**
   * Create the actual datatype sort from the declared constructors.
   * For mutually recursive datatypes, use Context.createDatatypes instead.
   */
  create(): DatatypeSort<Name>;
}

/**
 * @category Datatypes
 */
export interface DatatypeCreation<Name extends string> {
  /**
   * Create a new datatype declaration helper.
   */
  (name: string): Datatype<Name>;

  /**
   * Create mutually recursive datatypes.
   *
   * @param datatypes Array of Datatype declarations
   * @returns Array of created DatatypeSort instances
   */
  createDatatypes(...datatypes: Datatype<Name>[]): DatatypeSort<Name>[];
}

/**
 * A Sort representing an algebraic datatype.
 *
 * After creation, this sort will have constructor, recognizer, and accessor
 * functions dynamically attached based on the declared constructors.
 *
 * @category Datatypes
 */
export interface DatatypeSort<Name extends string = 'main'> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'DatatypeSort';

  /**
   * Number of constructors in this datatype
   */
  numConstructors(): number;

  /**
   * Get the idx'th constructor function declaration
   */
  constructorDecl(idx: number): FuncDecl<Name>;

  /**
   * Get the idx'th recognizer function declaration
   */
  recognizer(idx: number): FuncDecl<Name>;

  /**
   * Get the accessor function declaration for the idx_a'th field of the idx_c'th constructor
   */
  accessor(constructorIdx: number, accessorIdx: number): FuncDecl<Name>;

  cast(other: CoercibleToExpr<Name>): DatatypeExpr<Name>;

  cast(other: DatatypeExpr<Name>): DatatypeExpr<Name>;
}

/**
 * Represents expressions of datatype sorts.
 *
 * @category Datatypes
 */
export interface DatatypeExpr<Name extends string = 'main'> extends Expr<Name, DatatypeSort<Name>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'DatatypeExpr';
}

///////////////////////
// Floating-Point API //
///////////////////////

/**
 * Floating-point rounding mode sort
 * @category Floating-Point
 */
export interface FPRMSort<Name extends string = 'main'> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'FPRMSort';

  cast(other: FPRM<Name>): FPRM<Name>;
  cast(other: CoercibleToExpr<Name>): never;
}

/**
 * Floating-point sort (IEEE 754)
 * @category Floating-Point
 */
export interface FPSort<Name extends string = 'main'> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'FPSort';

  /**
   * Number of exponent bits
   */
  ebits(): number;

  /**
   * Number of significand bits (including hidden bit)
   */
  sbits(): number;

  cast(other: CoercibleToFP<Name>): FP<Name>;
  cast(other: CoercibleToExpr<Name>): Expr<Name>;
}

/** @category Floating-Point */
export interface FPCreation<Name extends string> {
  /**
   * Create a floating-point sort with custom exponent and significand bit sizes
   * @param ebits Number of exponent bits
   * @param sbits Number of significand bits (including hidden bit)
   */
  sort(ebits: number, sbits: number): FPSort<Name>;

  /**
   * IEEE 754 16-bit floating-point sort (half precision)
   */
  sort16(): FPSort<Name>;

  /**
   * IEEE 754 32-bit floating-point sort (single precision)
   */
  sort32(): FPSort<Name>;

  /**
   * IEEE 754 64-bit floating-point sort (double precision)
   */
  sort64(): FPSort<Name>;

  /**
   * IEEE 754 128-bit floating-point sort (quadruple precision)
   */
  sort128(): FPSort<Name>;

  /**
   * Create a floating-point constant
   */
  const(name: string, sort: FPSort<Name>): FP<Name>;

  /**
   * Create multiple floating-point constants
   */
  consts(names: string | string[], sort: FPSort<Name>): FP<Name>[];

  /**
   * Create a floating-point value from a number
   */
  val(value: number, sort: FPSort<Name>): FPNum<Name>;

  /**
   * Create floating-point NaN
   */
  NaN(sort: FPSort<Name>): FPNum<Name>;

  /**
   * Create floating-point infinity
   * @param negative If true, creates negative infinity
   */
  inf(sort: FPSort<Name>, negative?: boolean): FPNum<Name>;

  /**
   * Create floating-point zero
   * @param negative If true, creates negative zero
   */
  zero(sort: FPSort<Name>, negative?: boolean): FPNum<Name>;
}

/** @category Floating-Point */
export interface FPRMCreation<Name extends string> {
  /**
   * Get the floating-point rounding mode sort
   */
  sort(): FPRMSort<Name>;

  /**
   * Round nearest, ties to even (default rounding mode)
   */
  RNE(): FPRM<Name>;

  /**
   * Round nearest, ties to away
   */
  RNA(): FPRM<Name>;

  /**
   * Round toward positive infinity
   */
  RTP(): FPRM<Name>;

  /**
   * Round toward negative infinity
   */
  RTN(): FPRM<Name>;

  /**
   * Round toward zero
   */
  RTZ(): FPRM<Name>;
}

/**
 * Floating-point rounding mode expression
 * @category Floating-Point
 */
export interface FPRM<Name extends string = 'main'> extends Expr<Name, FPRMSort<Name>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'FPRM';
}

/**
 * Floating-point expression (IEEE 754)
 * @category Floating-Point
 */
export interface FP<Name extends string = 'main'> extends Expr<Name, FPSort<Name>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'FP' | FPNum['__typename'];

  /** @category Arithmetic */
  add(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name>;

  /** @category Arithmetic */
  sub(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name>;

  /** @category Arithmetic */
  mul(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name>;

  /** @category Arithmetic */
  div(rm: FPRM<Name>, other: CoercibleToFP<Name>): FP<Name>;

  /** @category Arithmetic */
  neg(): FP<Name>;

  /** @category Arithmetic */
  abs(): FP<Name>;

  /** @category Arithmetic */
  sqrt(rm: FPRM<Name>): FP<Name>;

  /** @category Arithmetic */
  rem(other: CoercibleToFP<Name>): FP<Name>;

  /** @category Arithmetic */
  fma(rm: FPRM<Name>, y: CoercibleToFP<Name>, z: CoercibleToFP<Name>): FP<Name>;

  /** @category Comparison */
  lt(other: CoercibleToFP<Name>): Bool<Name>;

  /** @category Comparison */
  gt(other: CoercibleToFP<Name>): Bool<Name>;

  /** @category Comparison */
  le(other: CoercibleToFP<Name>): Bool<Name>;

  /** @category Comparison */
  ge(other: CoercibleToFP<Name>): Bool<Name>;

  /** @category Predicates */
  isNaN(): Bool<Name>;

  /** @category Predicates */
  isInf(): Bool<Name>;

  /** @category Predicates */
  isZero(): Bool<Name>;

  /** @category Predicates */
  isNormal(): Bool<Name>;

  /** @category Predicates */
  isSubnormal(): Bool<Name>;

  /** @category Predicates */
  isNegative(): Bool<Name>;

  /** @category Predicates */
  isPositive(): Bool<Name>;
}

/**
 * Floating-point numeral value
 * @category Floating-Point
 */
export interface FPNum<Name extends string = 'main'> extends FP<Name> {
  /** @hidden */
  readonly __typename: 'FPNum';

  /**
   * Get the floating-point value as a JavaScript number
   * Note: May lose precision for values outside JavaScript number range
   */
  value(): number;
}

///////////////////////
// String/Sequence API //
///////////////////////

/**
 * Sequence sort (can be string or sequence of any element type)
 * @category String/Sequence
 */
export interface SeqSort<Name extends string = 'main', ElemSort extends Sort<Name> = Sort<Name>> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'SeqSort';

  /**
   * Check if this is a string sort
   */
  isString(): boolean;

  /**
   * Get the element sort of this sequence
   */
  basis(): Sort<Name>;

  cast(other: Seq<Name>): Seq<Name>;
  cast(other: string): Seq<Name>;
  cast(other: CoercibleToExpr<Name>): Expr<Name>;
}

/** @category String/Sequence */
export interface StringCreation<Name extends string> {
  /**
   * Create a string sort
   */
  sort(): SeqSort<Name>;

  /**
   * Create a string constant
   */
  const(name: string): Seq<Name>;

  /**
   * Create multiple string constants
   */
  consts(names: string | string[]): Seq<Name>[];

  /**
   * Create a string value
   */
  val(value: string): Seq<Name>;
}

/** @category String/Sequence */
export interface SeqCreation<Name extends string> {
  /**
   * Create a sequence sort over the given element sort
   */
  sort<ElemSort extends Sort<Name>>(elemSort: ElemSort): SeqSort<Name, ElemSort>;

  /**
   * Create an empty sequence
   */
  empty<ElemSort extends Sort<Name>>(elemSort: ElemSort): Seq<Name, ElemSort>;

  /**
   * Create a unit sequence (sequence with single element)
   */
  unit<ElemSort extends Sort<Name>>(elem: Expr<Name>): Seq<Name, ElemSort>;
}

/**
 * Sequence expression (includes strings)
 * @category String/Sequence
 */
export interface Seq<Name extends string = 'main', ElemSort extends Sort<Name> = Sort<Name>>
  extends Expr<Name, SeqSort<Name, ElemSort>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'Seq';

  /**
   * Check if this is a string value
   */
  isString(): boolean;

  /**
   * Get string value if this is a concrete string
   */
  asString(): string;

  /** @category Operations */
  concat(other: Seq<Name, ElemSort> | string): Seq<Name, ElemSort>;

  /** @category Operations */
  length(): Arith<Name>;

  /** @category Operations */
  at(index: Arith<Name> | number | bigint): Seq<Name, ElemSort>;

  /** @category Operations */
  nth(index: Arith<Name> | number | bigint): Expr<Name>;

  /** @category Operations */
  extract(offset: Arith<Name> | number | bigint, length: Arith<Name> | number | bigint): Seq<Name, ElemSort>;

  /** @category Operations */
  indexOf(substr: Seq<Name, ElemSort> | string, offset?: Arith<Name> | number | bigint): Arith<Name>;

  /** @category Operations */
  lastIndexOf(substr: Seq<Name, ElemSort> | string): Arith<Name>;

  /** @category Operations */
  contains(substr: Seq<Name, ElemSort> | string): Bool<Name>;

  /** @category Operations */
  prefixOf(s: Seq<Name, ElemSort> | string): Bool<Name>;

  /** @category Operations */
  suffixOf(s: Seq<Name, ElemSort> | string): Bool<Name>;

  /** @category Operations */
  replace(src: Seq<Name, ElemSort> | string, dst: Seq<Name, ElemSort> | string): Seq<Name, ElemSort>;

  /** @category Operations */
  replaceAll(src: Seq<Name, ElemSort> | string, dst: Seq<Name, ElemSort> | string): Seq<Name, ElemSort>;
}

///////////////////////
// Regular Expressions
///////////////////////

/**
 * Regular expression sort
 * @category RegularExpression
 */
export interface ReSort<Name extends string = 'main', SeqSortRef extends SeqSort<Name> = SeqSort<Name>> extends Sort<Name> {
  /** @hidden */
  readonly __typename: 'ReSort';

  /**
   * Get the basis (underlying sequence sort) of this regular expression sort
   */
  basis(): SeqSortRef;

  cast(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;
  cast(other: CoercibleToExpr<Name>): Expr<Name>;
}

/** @category RegularExpression */
export interface ReCreation<Name extends string> {
  /**
   * Create a regular expression sort over the given sequence sort
   */
  sort<SeqSortRef extends SeqSort<Name>>(seqSort: SeqSortRef): ReSort<Name, SeqSortRef>;

  /**
   * Convert a sequence to a regular expression that accepts exactly that sequence
   */
  toRe(seq: Seq<Name> | string): Re<Name>;
}

/**
 * Regular expression expression
 * @category RegularExpression
 */
export interface Re<Name extends string = 'main', SeqSortRef extends SeqSort<Name> = SeqSort<Name>>
  extends Expr<Name, ReSort<Name, SeqSortRef>, Z3_ast> {
  /** @hidden */
  readonly __typename: 'Re';

  /** @category Operations */
  plus(): Re<Name, SeqSortRef>;

  /** @category Operations */
  star(): Re<Name, SeqSortRef>;

  /** @category Operations */
  option(): Re<Name, SeqSortRef>;

  /** @category Operations */
  complement(): Re<Name, SeqSortRef>;

  /** @category Operations */
  union(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category Operations */
  intersect(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category Operations */
  diff(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /** @category Operations */
  concat(other: Re<Name, SeqSortRef>): Re<Name, SeqSortRef>;

  /**
   * Create a bounded repetition of this regex
   * @param lo Minimum number of repetitions
   * @param hi Maximum number of repetitions (0 means unbounded, i.e., at least lo)
   * @category Operations
   */
  loop(lo: number, hi?: number): Re<Name, SeqSortRef>;

  /** @category Operations */
  power(n: number): Re<Name, SeqSortRef>;
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

/** @hidden */
export interface GoalCtor<Name extends string> {
  new (models?: boolean, unsat_cores?: boolean, proofs?: boolean): Goal<Name>;
}

/**
 * Goal is a collection of constraints we want to find a solution or show to be unsatisfiable.
 * Goals are processed using Tactics. A Tactic transforms a goal into a set of subgoals.
 * @category Tactics
 */
export interface Goal<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Goal';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_goal;

  /**
   * Add constraints to the goal.
   */
  add(...constraints: (Bool<Name> | boolean)[]): void;

  /**
   * Return the number of constraints in the goal.
   */
  size(): number;

  /**
   * Return a constraint from the goal at the given index.
   */
  get(i: number): Bool<Name>;

  /**
   * Return the depth of the goal (number of tactics applied).
   */
  depth(): number;

  /**
   * Return true if the goal contains the False constraint.
   */
  inconsistent(): boolean;

  /**
   * Return the precision of the goal (precise, under-approximation, over-approximation).
   */
  precision(): Z3_goal_prec;

  /**
   * Reset the goal to empty.
   */
  reset(): void;

  /**
   * Return the number of expressions in the goal.
   */
  numExprs(): number;

  /**
   * Return true if the goal is decided to be satisfiable.
   */
  isDecidedSat(): boolean;

  /**
   * Return true if the goal is decided to be unsatisfiable.
   */
  isDecidedUnsat(): boolean;

  /**
   * Convert a model for the goal to a model for the original goal.
   */
  convertModel(model: Model<Name>): Model<Name>;

  /**
   * Convert the goal to a single Boolean expression (conjunction of all constraints).
   */
  asExpr(): Bool<Name>;

  /**
   * Return a string representation of the goal.
   */
  toString(): string;

  /**
   * Return a DIMACS string representation of the goal.
   */
  dimacs(includeNames?: boolean): string;
}

/**
 * ApplyResult contains the subgoals produced by applying a tactic to a goal.
 * @category Tactics
 */
export interface ApplyResult<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'ApplyResult';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_apply_result;

  /**
   * Return the number of subgoals in the result.
   */
  length(): number;

  /**
   * Return a subgoal at the given index.
   */
  getSubgoal(i: number): Goal<Name>;

  /**
   * Return a string representation of the apply result.
   */
  toString(): string;

  /**
   * Get subgoal at index (alias for getSubgoal).
   */
  [index: number]: Goal<Name>;
}

export interface Probe<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Probe';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_probe;

  /**
   * Apply the probe to a goal and return the result as a number.
   */
  apply(goal: Goal<Name>): number;
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

  /**
   * Apply the tactic to a goal and return the resulting subgoals.
   */
  apply(goal: Goal<Name> | Bool<Name>): Promise<ApplyResult<Name>>;

  /**
   * Create a solver from this tactic.
   * The solver will always solve each check() from scratch using this tactic.
   */
  solver(): Solver<Name>;

  /**
   * Get help string describing the tactic.
   */
  help(): string;

  /**
   * Get parameter descriptions for the tactic.
   * Returns a ParamDescrs object for introspecting available parameters.
   */
  paramDescrs(): ParamDescrs<Name>;

  /**
   * Return a tactic that uses the given configuration parameters.
   * @param params - Parameters to configure the tactic
   */
  usingParams(params: Params<Name>): Tactic<Name>;
}

/**
 * Params is a set of parameters used to configure Solvers, Tactics and Simplifiers in Z3.
 * @category Tactics
 */
export interface Params<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Params';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_params;

  /**
   * Set a parameter with the given name and value.
   * @param name - Parameter name
   * @param value - Parameter value (boolean, number, or string)
   */
  set(name: string, value: boolean | number | string): void;

  /**
   * Validate the parameter set against a parameter description set.
   * @param descrs - Parameter descriptions to validate against
   */
  validate(descrs: ParamDescrs<Name>): void;

  /**
   * Convert the parameter set to a string representation.
   */
  toString(): string;
}

/** @hidden */
export interface ParamsCtor<Name extends string> {
  new (): Params<Name>;
}

/**
 * ParamDescrs is a set of parameter descriptions for Solvers, Tactics and Simplifiers in Z3.
 * @category Tactics
 */
export interface ParamDescrs<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'ParamDescrs';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_param_descrs;

  /**
   * Return the number of parameters in the description set.
   */
  size(): number;

  /**
   * Return the name of the parameter at the given index.
   * @param i - Index of the parameter
   */
  getName(i: number): string;

  /**
   * Return the kind (type) of the parameter with the given name.
   * @param name - Parameter name
   */
  getKind(name: string): number;

  /**
   * Return the documentation string for the parameter with the given name.
   * @param name - Parameter name
   */
  getDocumentation(name: string): string;

  /**
   * Convert the parameter description set to a string representation.
   */
  toString(): string;
}

/**
 * Simplifiers act as pre-processing utilities for solvers.
 * Build a custom simplifier and add it to a solver for incremental preprocessing.
 * @category Tactics
 */
export interface Simplifier<Name extends string = 'main'> {
  /** @hidden */
  readonly __typename: 'Simplifier';

  readonly ctx: Context<Name>;
  readonly ptr: Z3_simplifier;

  /**
   * Return a string containing a description of parameters accepted by this simplifier.
   */
  help(): string;

  /**
   * Return the parameter description set for this simplifier.
   */
  paramDescrs(): ParamDescrs<Name>;

  /**
   * Return a simplifier that uses the given configuration parameters.
   * @param params - Parameters to configure the simplifier
   */
  usingParams(params: Params<Name>): Simplifier<Name>;

  /**
   * Return a simplifier that applies this simplifier and then another simplifier.
   * @param other - The simplifier to apply after this one
   */
  andThen(other: Simplifier<Name>): Simplifier<Name>;
}

/** @hidden */
export interface SimplifierCtor<Name extends string> {
  new (name: string): Simplifier<Name>;
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
