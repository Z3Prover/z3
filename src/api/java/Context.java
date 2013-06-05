/**
 * This file was automatically generated from Context.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import java.util.Map;

import com.microsoft.z3.enumerations.Z3_ast_print_mode;

/**
 * The main interaction with Z3 happens via the Context.
 **/
public class Context extends IDisposable
{
    /**
     * Constructor.
     **/
    public Context() throws Z3Exception
    {
        super();
        m_ctx = Native.mkContextRc(0);
        initContext();
    }

    /**
     * Constructor.
     * <remarks>
     * The following parameters can be set:        
     *     - proof  (Boolean)           Enable proof generation
     *     - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting 
     *     - trace  (Boolean)           Tracing support for VCC
     *     - trace_file_name (String)   Trace out file for VCC traces
     *     - timeout (unsigned)         default timeout (in milliseconds) used for solvers
     *     - well_sorted_check          type checker
     *     - auto_config                use heuristics to automatically select solver and configure it
     *     - model                      model generation for solvers, this parameter can be overwritten when creating a solver
     *     - model_validate             validate models produced by solvers
     *     - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver
     * Note that in previous versions of Z3, this constructor was also used to set global and 
     * module parameters. For this purpose we should now use <see cref="Global.setParameter"/>
     * </remarks>
     **/
    public Context(Map<String, String> settings) throws Z3Exception
    {
        super();
        long cfg = Native.mkConfig();
        for (Map.Entry<String, String> kv : settings.entrySet())
            Native.setParamValue(cfg, kv.getKey(), kv.getValue());
        m_ctx = Native.mkContextRc(cfg);
        Native.delConfig(cfg);
        initContext();
    }

    /**
     * Creates a new symbol using an integer. <remarks> Not all integers can be
     * passed to this function. The legal range of unsigned integers is 0 to
     * 2^30-1. </remarks>
     **/
    public IntSymbol mkSymbol(int i) throws Z3Exception
    {
        return new IntSymbol(this, i);
    }

    /**
     * Create a symbol using a string.
     **/
    public StringSymbol mkSymbol(String name) throws Z3Exception
    {
        return new StringSymbol(this, name);
    }

    /**
     * Create an array of symbols.
     **/
    Symbol[] MkSymbols(String[] names) throws Z3Exception
    {
        if (names == null)
            return null;
        Symbol[] result = new Symbol[names.length];
        for (int i = 0; i < names.length; ++i)
            result[i] = mkSymbol(names[i]);
        return result;
    }

    private BoolSort m_boolSort = null;
    private IntSort m_intSort = null;
    private RealSort m_realSort = null;

    /**
     * Retrieves the Boolean sort of the context.
     **/
    public BoolSort getBoolSort() throws Z3Exception
    {
        if (m_boolSort == null)
            m_boolSort = new BoolSort(this);
        return m_boolSort;
    }

    /**
     * Retrieves the Integer sort of the context.
     **/
    public IntSort getIntSort() throws Z3Exception
    {
        if (m_intSort == null)
            m_intSort = new IntSort(this);
        return m_intSort;
    }

    /**
     * Retrieves the Real sort of the context.
     **/
    public RealSort getRealSort() throws Z3Exception
    {
        if (m_realSort == null)
            m_realSort = new RealSort(this);
        return m_realSort;
    }

    /**
     * Create a new Boolean sort.
     **/
    public BoolSort mkBoolSort() throws Z3Exception
    {

        return new BoolSort(this);
    }

    /**
     * Create a new uninterpreted sort.
     **/
    public UninterpretedSort mkUninterpretedSort(Symbol s) throws Z3Exception
    {

        checkContextMatch(s);
        return new UninterpretedSort(this, s);
    }

    /**
     * Create a new uninterpreted sort.
     **/
    public UninterpretedSort mkUninterpretedSort(String str) throws Z3Exception
    {

        return mkUninterpretedSort(mkSymbol(str));
    }

    /**
     * Create a new integer sort.
     **/
    public IntSort mkIntSort() throws Z3Exception
    {

        return new IntSort(this);
    }

    /**
     * Create a real sort.
     **/
    public RealSort mkRealSort() throws Z3Exception
    {

        return new RealSort(this);
    }

    /**
     * Create a new bit-vector sort.
     **/
    public BitVecSort mkBitVecSort(int size) throws Z3Exception
    {

        return new BitVecSort(this, Native.mkBvSort(nCtx(), size));
    }

    /**
     * Create a new array sort.
     **/
    public ArraySort mkArraySort(Sort domain, Sort range) throws Z3Exception
    {

        checkContextMatch(domain);
        checkContextMatch(range);
        return new ArraySort(this, domain, range);
    }

    /**
     * Create a new tuple sort.
     **/
    public TupleSort mkTupleSort(Symbol name, Symbol[] fieldNames,
            Sort[] fieldSorts) throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(fieldNames);
        checkContextMatch(fieldSorts);
        return new TupleSort(this, name, (int) fieldNames.length, fieldNames,
                fieldSorts);
    }

    /**
     * Create a new enumeration sort.
     **/
    public EnumSort mkEnumSort(Symbol name, Symbol... enumNames)
            throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(enumNames);
        return new EnumSort(this, name, enumNames);
    }

    /**
     * Create a new enumeration sort.
     **/
    public EnumSort mkEnumSort(String name, String... enumNames)
            throws Z3Exception
    {
        return new EnumSort(this, mkSymbol(name), MkSymbols(enumNames));
    }

    /**
     * Create a new list sort.
     **/
    public ListSort mkListSort(Symbol name, Sort elemSort) throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(elemSort);
        return new ListSort(this, name, elemSort);
    }

    /**
     * Create a new list sort.
     **/
    public ListSort mkListSort(String name, Sort elemSort) throws Z3Exception
    {

        checkContextMatch(elemSort);
        return new ListSort(this, mkSymbol(name), elemSort);
    }

    /**
     * Create a new finite domain sort.
     **/
    public FiniteDomainSort mkFiniteDomainSort(Symbol name, long size)
            throws Z3Exception
    {

        checkContextMatch(name);
        return new FiniteDomainSort(this, name, size);
    }

    /**
     * Create a new finite domain sort.
     **/
    public FiniteDomainSort mkFiniteDomainSort(String name, long size)
            throws Z3Exception
    {

        return new FiniteDomainSort(this, mkSymbol(name), size);
    }

    /**
     * Create a datatype constructor. <param name="name">constructor
     * name</param> <param name="recognizer">name of recognizer
     * function.</param> <param name="fieldNames">names of the constructor
     * fields.</param> <param name="sorts">field sorts, 0 if the field sort
     * refers to a recursive sort.</param> <param name="sortRefs">reference to
     * datatype sort that is an argument to the constructor; if the
     * corresponding sort reference is 0, then the value in sort_refs should be
     * an index referring to one of the recursive datatypes that is
     * declared.</param>
     **/
    public Constructor mkConstructor(Symbol name, Symbol recognizer,
            Symbol[] fieldNames, Sort[] sorts, int[] sortRefs)
            throws Z3Exception
    {

        return new Constructor(this, name, recognizer, fieldNames, sorts,
                sortRefs);
    }

    /**
     * Create a datatype constructor. <param name="name"></param> <param
     * name="recognizer"></param> <param name="fieldNames"></param> <param
     * name="sorts"></param> <param name="sortRefs"></param>
     * 
     * @return
     **/
    public Constructor mkConstructor(String name, String recognizer,
            String[] fieldNames, Sort[] sorts, int[] sortRefs)
            throws Z3Exception
    {

        return new Constructor(this, mkSymbol(name), mkSymbol(recognizer),
                MkSymbols(fieldNames), sorts, sortRefs);
    }

    /**
     * Create a new datatype sort.
     **/
    public DatatypeSort mkDatatypeSort(Symbol name, Constructor[] constructors)
            throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(constructors);
        return new DatatypeSort(this, name, constructors);
    }

    /**
     * Create a new datatype sort.
     **/
    public DatatypeSort mkDatatypeSort(String name, Constructor[] constructors)
            throws Z3Exception
    {

        checkContextMatch(constructors);
        return new DatatypeSort(this, mkSymbol(name), constructors);
    }

    /**
     * Create mutually recursive datatypes. <param name="names">names of
     * datatype sorts</param> <param name="c">list of constructors, one list per
     * sort.</param>
     **/
    public DatatypeSort[] mkDatatypeSorts(Symbol[] names, Constructor[][] c)
            throws Z3Exception
    {

        checkContextMatch(names);
        int n = (int) names.length;
        ConstructorList[] cla = new ConstructorList[n];
        long[] n_constr = new long[n];
        for (int i = 0; i < n; i++)
        {
            Constructor[] constructor = c[i];

            checkContextMatch(constructor);
            cla[i] = new ConstructorList(this, constructor);
            n_constr[i] = cla[i].getNativeObject();
        }
        long[] n_res = new long[n];
        Native.mkDatatypes(nCtx(), n, Symbol.arrayToNative(names), n_res,
                n_constr);
        DatatypeSort[] res = new DatatypeSort[n];
        for (int i = 0; i < n; i++)
            res[i] = new DatatypeSort(this, n_res[i]);
        return res;
    }

    /**
     * Create mutually recursive data-types. <param name="names"></param> <param
     * name="c"></param>
     * 
     * @return
     **/
    public DatatypeSort[] mkDatatypeSorts(String[] names, Constructor[][] c)
            throws Z3Exception
    {

        return mkDatatypeSorts(MkSymbols(names), c);
    }

    /**
     * Creates a new function declaration.
     **/
    public FuncDecl mkFuncDecl(Symbol name, Sort[] domain, Sort range)
            throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(domain);
        checkContextMatch(range);
        return new FuncDecl(this, name, domain, range);
    }

    /**
     * Creates a new function declaration.
     **/
    public FuncDecl mkFuncDecl(Symbol name, Sort domain, Sort range)
            throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(domain);
        checkContextMatch(range);
        Sort[] q = new Sort[] { domain };
        return new FuncDecl(this, name, q, range);
    }

    /**
     * Creates a new function declaration.
     **/
    public FuncDecl mkFuncDecl(String name, Sort[] domain, Sort range)
            throws Z3Exception
    {

        checkContextMatch(domain);
        checkContextMatch(range);
        return new FuncDecl(this, mkSymbol(name), domain, range);
    }

    /**
     * Creates a new function declaration.
     **/
    public FuncDecl mkFuncDecl(String name, Sort domain, Sort range)
            throws Z3Exception
    {

        checkContextMatch(domain);
        checkContextMatch(range);
        Sort[] q = new Sort[] { domain };
        return new FuncDecl(this, mkSymbol(name), q, range);
    }

    /**
     * Creates a fresh function declaration with a name prefixed with <paramref
     * name="prefix"/>. <seealso cref="MkFuncDecl(string,Sort,Sort)"/> <seealso
     * cref="MkFuncDecl(string,Sort[],Sort)"/>
     **/
    public FuncDecl mkFreshFuncDecl(String prefix, Sort[] domain, Sort range)
            throws Z3Exception
    {

        checkContextMatch(domain);
        checkContextMatch(range);
        return new FuncDecl(this, prefix, domain, range);
    }

    /**
     * Creates a new constant function declaration.
     **/
    public FuncDecl mkConstDecl(Symbol name, Sort range) throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(range);
        return new FuncDecl(this, name, null, range);
    }

    /**
     * Creates a new constant function declaration.
     **/
    public FuncDecl mkConstDecl(String name, Sort range) throws Z3Exception
    {

        checkContextMatch(range);
        return new FuncDecl(this, mkSymbol(name), null, range);
    }

    /**
     * Creates a fresh constant function declaration with a name prefixed with
     * <paramref name="prefix"/>. <seealso cref="MkFuncDecl(string,Sort,Sort)"/>
     * <seealso cref="MkFuncDecl(string,Sort[],Sort)"/>
     **/
    public FuncDecl mkFreshConstDecl(String prefix, Sort range)
            throws Z3Exception
    {

        checkContextMatch(range);
        return new FuncDecl(this, prefix, null, range);
    }

    /**
     * Creates a new bound variable. <param name="index">The de-Bruijn index of
     * the variable</param> <param name="ty">The sort of the variable</param>
     **/
    public Expr mkBound(int index, Sort ty) throws Z3Exception
    {
        return Expr.create(this,
                Native.mkBound(nCtx(), index, ty.getNativeObject()));
    }

    /**
     * Create a quantifier pattern.
     **/
    public Pattern mkPattern(Expr... terms) throws Z3Exception
    {
        if (terms.length == 0)
            throw new Z3Exception("Cannot create a pattern from zero terms");

        long[] termsNative = AST.arrayToNative(terms);
        return new Pattern(this, Native.mkPattern(nCtx(), (int) terms.length,
                termsNative));
    }

    /**
     * Creates a new Constant of sort <paramref name="range"/> and named
     * <paramref name="name"/>.
     **/
    public Expr mkConst(Symbol name, Sort range) throws Z3Exception
    {

        checkContextMatch(name);
        checkContextMatch(range);

        return Expr.create(
                this,
                Native.mkConst(nCtx(), name.getNativeObject(),
                        range.getNativeObject()));
    }

    /**
     * Creates a new Constant of sort <paramref name="range"/> and named
     * <paramref name="name"/>.
     **/
    public Expr mkConst(String name, Sort range) throws Z3Exception
    {

        return mkConst(mkSymbol(name), range);
    }

    /**
     * Creates a fresh Constant of sort <paramref name="range"/> and a name
     * prefixed with <paramref name="prefix"/>.
     **/
    public Expr mkFreshConst(String prefix, Sort range) throws Z3Exception
    {

        checkContextMatch(range);
        return Expr.create(this,
                Native.mkFreshConst(nCtx(), prefix, range.getNativeObject()));
    }

    /**
     * Creates a fresh constant from the FuncDecl <paramref name="f"/>. <param
     * name="f">A decl of a 0-arity function</param>
     **/
    public Expr mkConst(FuncDecl f) throws Z3Exception
    {

        return mkApp(f, (Expr[]) null);
    }

    /**
     * Create a Boolean constant.
     **/
    public BoolExpr mkBoolConst(Symbol name) throws Z3Exception
    {

        return (BoolExpr) mkConst(name, getBoolSort());
    }

    /**
     * Create a Boolean constant.
     **/
    public BoolExpr mkBoolConst(String name) throws Z3Exception
    {

        return (BoolExpr) mkConst(mkSymbol(name), getBoolSort());
    }

    /**
     * Creates an integer constant.
     **/
    public IntExpr mkIntConst(Symbol name) throws Z3Exception
    {

        return (IntExpr) mkConst(name, getIntSort());
    }

    /**
     * Creates an integer constant.
     **/
    public IntExpr mkIntConst(String name) throws Z3Exception
    {

        return (IntExpr) mkConst(name, getIntSort());
    }

    /**
     * Creates a real constant.
     **/
    public RealExpr mkRealConst(Symbol name) throws Z3Exception
    {

        return (RealExpr) mkConst(name, getRealSort());
    }

    /**
     * Creates a real constant.
     **/
    public RealExpr mkRealConst(String name) throws Z3Exception
    {

        return (RealExpr) mkConst(name, getRealSort());
    }

    /**
     * Creates a bit-vector constant.
     **/
    public BitVecExpr mkBVConst(Symbol name, int size) throws Z3Exception
    {

        return (BitVecExpr) mkConst(name, mkBitVecSort(size));
    }

    /**
     * Creates a bit-vector constant.
     **/
    public BitVecExpr mkBVConst(String name, int size) throws Z3Exception
    {

        return (BitVecExpr) mkConst(name, mkBitVecSort(size));
    }

    /**
     * Create a new function application.
     **/
    public Expr mkApp(FuncDecl f, Expr... args) throws Z3Exception
    {
        checkContextMatch(f);
        checkContextMatch(args);
        return Expr.create(this, f, args);
    }

    /**
     * The true Term.
     **/
    public BoolExpr mkTrue() throws Z3Exception
    {
        return new BoolExpr(this, Native.mkTrue(nCtx()));
    }

    /**
     * The false Term.
     **/
    public BoolExpr mkFalse() throws Z3Exception
    {
        return new BoolExpr(this, Native.mkFalse(nCtx()));
    }

    /**
     * Creates a Boolean value.
     **/
    public BoolExpr mkBool(boolean value) throws Z3Exception
    {
        return value ? mkTrue() : mkFalse();
    }

    /**
     * Creates the equality <paramref name="x"/> = <paramref name="y"/>.
     **/
    public BoolExpr mkEq(Expr x, Expr y) throws Z3Exception
    {
        checkContextMatch(x);
        checkContextMatch(y);
        return new BoolExpr(this, Native.mkEq(nCtx(), x.getNativeObject(),
                y.getNativeObject()));
    }

    /**
     * Creates a <code>distinct</code> term.
     **/
    public BoolExpr mkDistinct(Expr... args) throws Z3Exception
    {
        checkContextMatch(args);
        return new BoolExpr(this, Native.mkDistinct(nCtx(), (int) args.length,
                AST.arrayToNative(args)));
    }

    /**
     * Mk an expression representing <code>not(a)</code>.
     **/
    public BoolExpr mkNot(BoolExpr a) throws Z3Exception
    {

        checkContextMatch(a);
        return new BoolExpr(this, Native.mkNot(nCtx(), a.getNativeObject()));
    }

    /**
     * Create an expression representing an if-then-else:
     * <code>ite(t1, t2, t3)</code>. <param name="t1">An expression with Boolean
     * sort</param> <param name="t2">An expression </param> <param name="t3">An
     * expression with the same sort as <paramref name="t2"/></param>
     **/
    public Expr mkITE(BoolExpr t1, Expr t2, Expr t3) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        checkContextMatch(t3);
        return Expr.create(this, Native.mkIte(nCtx(), t1.getNativeObject(),
                t2.getNativeObject(), t3.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 iff t2</code>.
     **/
    public BoolExpr mkIff(BoolExpr t1, BoolExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkIff(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 -> t2</code>.
     **/
    public BoolExpr mkImplies(BoolExpr t1, BoolExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkImplies(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 xor t2</code>.
     **/
    public BoolExpr mkXor(BoolExpr t1, BoolExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkXor(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t[0] and t[1] and ...</code>.
     **/
    public BoolExpr mkAnd(BoolExpr... t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BoolExpr(this, Native.mkAnd(nCtx(), (int) t.length,
                AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing <code>t[0] or t[1] or ...</code>.
     **/
    public BoolExpr mkOr(BoolExpr... t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BoolExpr(this, Native.mkOr(nCtx(), (int) t.length,
                AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing <code>t[0] + t[1] + ...</code>.
     **/
    public ArithExpr mkAdd(ArithExpr... t) throws Z3Exception
    {

        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkAdd(nCtx(), (int) t.length, AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing <code>t[0] * t[1] * ...</code>.
     **/
    public ArithExpr mkMul(ArithExpr... t) throws Z3Exception
    {

        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkMul(nCtx(), (int) t.length, AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing <code>t[0] - t[1] - ...</code>.
     **/
    public ArithExpr mkSub(ArithExpr... t) throws Z3Exception
    {

        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkSub(nCtx(), (int) t.length, AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing <code>-t</code>.
     **/
    public ArithExpr mkUnaryMinus(ArithExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkUnaryMinus(nCtx(), t.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 / t2</code>.
     **/
    public ArithExpr mkDiv(ArithExpr t1, ArithExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return (ArithExpr) Expr.create(this, Native.mkDiv(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 mod t2</code>. <remarks>The
     * arguments must have int type.</remarks>
     **/
    public IntExpr mkMod(IntExpr t1, IntExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new IntExpr(this, Native.mkMod(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 rem t2</code>. <remarks>The
     * arguments must have int type.</remarks>
     **/
    public IntExpr mkRem(IntExpr t1, IntExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new IntExpr(this, Native.mkRem(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 ^ t2</code>.
     **/
    public ArithExpr mkPower(ArithExpr t1, ArithExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return (ArithExpr) Expr.create(
                this,
                Native.mkPower(nCtx(), t1.getNativeObject(),
                        t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 &lt; t2</code>
     **/
    public BoolExpr mkLt(ArithExpr t1, ArithExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkLt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 &lt;= t2</code>
     **/
    public BoolExpr mkLe(ArithExpr t1, ArithExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkLe(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 &gt; t2</code>
     **/
    public BoolExpr mkGt(ArithExpr t1, ArithExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkGt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing <code>t1 &gt;= t2</code>
     **/
    public BoolExpr mkGe(ArithExpr t1, ArithExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkGe(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Coerce an integer to a real. <remarks> There is also a converse operation
     * exposed. It follows the semantics prescribed by the SMT-LIB standard.
     * 
     * You can take the floor of a real by creating an auxiliary integer Term
     * <code>k</code> and and asserting
     * <code>MakeInt2Real(k) &lt;= t1 &lt; MkInt2Real(k)+1</code>. The argument
     * must be of integer sort. </remarks>
     **/
    public RealExpr mkInt2Real(IntExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new RealExpr(this,
                Native.mkInt2real(nCtx(), t.getNativeObject()));
    }

    /**
     * Coerce a real to an integer. <remarks> The semantics of this function
     * follows the SMT-LIB standard for the function to_int. The argument must
     * be of real sort. </remarks>
     **/
    public IntExpr mkReal2Int(RealExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new IntExpr(this, Native.mkReal2int(nCtx(), t.getNativeObject()));
    }

    /**
     * Creates an expression that checks whether a real number is an integer.
     **/
    public BoolExpr mkIsInteger(RealExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BoolExpr(this, Native.mkIsInt(nCtx(), t.getNativeObject()));
    }

    /**
     * Bitwise negation. <remarks>The argument must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVNot(BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvnot(nCtx(), t.getNativeObject()));
    }

    /**
     * Take conjunction of bits in a vector, return vector of length 1.
     * <remarks>The argument must have a bit-vector sort.</remarks>
     **/
    public BitVecExpr mkBVRedAND(BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvredand(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Take disjunction of bits in a vector, return vector of length 1.
     * <remarks>The argument must have a bit-vector sort.</remarks>
     **/
    public BitVecExpr mkBVRedOR(BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvredor(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Bitwise conjunction. <remarks>The arguments must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVAND(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvand(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise disjunction. <remarks>The arguments must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVOR(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvor(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Bitwise XOR. <remarks>The arguments must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVXOR(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvxor(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise NAND. <remarks>The arguments must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVNAND(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvnand(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise NOR. <remarks>The arguments must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVNOR(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvnor(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise XNOR. <remarks>The arguments must have a bit-vector
     * sort.</remarks>
     **/
    public BitVecExpr mkBVXNOR(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvxnor(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Standard two's complement unary minus. <remarks>The arguments must have a
     * bit-vector sort.</remarks>
     **/
    public BitVecExpr mkBVNeg(BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvneg(nCtx(), t.getNativeObject()));
    }

    /**
     * Two's complement addition. <remarks>The arguments must have the same
     * bit-vector sort.</remarks>
     **/
    public BitVecExpr mkBVAdd(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvadd(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Two's complement subtraction. <remarks>The arguments must have the same
     * bit-vector sort.</remarks>
     **/
    public BitVecExpr mkBVSub(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsub(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Two's complement multiplication. <remarks>The arguments must have the
     * same bit-vector sort.</remarks>
     **/
    public BitVecExpr mkBVMul(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvmul(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Unsigned division. <remarks> It is defined as the floor of
     * <code>t1/t2</code> if \c t2 is different from zero. If <code>t2</code> is
     * zero, then the result is undefined. The arguments must have the same
     * bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVUDiv(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvudiv(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Signed division. <remarks> It is defined in the following way:
     * 
     * - The \c floor of <code>t1/t2</code> if \c t2 is different from zero, and
     * <code>t1*t2 >= 0</code>.
     * 
     * - The \c ceiling of <code>t1/t2</code> if \c t2 is different from zero,
     * and <code>t1*t2 &lt; 0</code>.
     * 
     * If <code>t2</code> is zero, then the result is undefined. The arguments
     * must have the same bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVSDiv(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsdiv(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Unsigned remainder. <remarks> It is defined as
     * <code>t1 - (t1 /u t2) * t2</code>, where <code>/u</code> represents
     * unsigned division. If <code>t2</code> is zero, then the result is
     * undefined. The arguments must have the same bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVURem(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvurem(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Signed remainder. <remarks> It is defined as
     * <code>t1 - (t1 /s t2) * t2</code>, where <code>/s</code> represents
     * signed division. The most significant bit (sign) of the result is equal
     * to the most significant bit of \c t1.
     * 
     * If <code>t2</code> is zero, then the result is undefined. The arguments
     * must have the same bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVSRem(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsrem(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Two's complement signed remainder (sign follows divisor). <remarks> If
     * <code>t2</code> is zero, then the result is undefined. The arguments must
     * have the same bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVSMod(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsmod(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Unsigned less-than <remarks> The arguments must have the same bit-vector
     * sort. </remarks>
     **/
    public BoolExpr mkBVULT(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvult(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed less-than <remarks> The arguments must have the
     * same bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSLT(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvslt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Unsigned less-than or equal to. <remarks> The arguments must have the
     * same bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVULE(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvule(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed less-than or equal to. <remarks> The arguments
     * must have the same bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSLE(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsle(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Unsigned greater than or equal to. <remarks> The arguments must have the
     * same bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVUGE(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvuge(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed greater than or equal to. <remarks> The arguments
     * must have the same bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSGE(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsge(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Unsigned greater-than. <remarks> The arguments must have the same
     * bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVUGT(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvugt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed greater-than. <remarks> The arguments must have
     * the same bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSGT(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsgt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Bit-vector concatenation. <remarks> The arguments must have a bit-vector
     * sort. </remarks>
     * 
     * @return The result is a bit-vector of size <code>n1+n2</code>, where
     *         <code>n1</code> (<code>n2</code>) is the size of <code>t1</code>
     *         (<code>t2</code>).
     * 
     **/
    public BitVecExpr mkConcat(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkConcat(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bit-vector extraction. <remarks> Extract the bits <paramref name="high"/>
     * down to <paramref name="low"/> from a bitvector of size <code>m</code> to
     * yield a new bitvector of size <code>n</code>, where
     * <code>n = high - low + 1</code>. The argument <paramref name="t"/> must
     * have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkExtract(int high, int low, BitVecExpr t)
            throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkExtract(nCtx(), high, low,
                t.getNativeObject()));
    }

    /**
     * Bit-vector sign extension. <remarks> Sign-extends the given bit-vector to
     * the (signed) equivalent bitvector of size <code>m+i</code>, where \c m is
     * the size of the given bit-vector. The argument <paramref name="t"/> must
     * have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkSignExt(int i, BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkSignExt(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Bit-vector zero extension. <remarks> Extend the given bit-vector with
     * zeros to the (unsigned) equivalent bitvector of size <code>m+i</code>,
     * where \c m is the size of the given bit-vector. The argument <paramref
     * name="t"/> must have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkZeroExt(int i, BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkZeroExt(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Bit-vector repetition. <remarks> The argument <paramref name="t"/> must
     * have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkRepeat(int i, BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkRepeat(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Shift left. <remarks> It is equivalent to multiplication by
     * <code>2^x</code> where \c x is the value of <paramref name="t2"/>.
     * 
     * NB. The semantics of shift operations varies between environments. This
     * definition does not necessarily capture directly the semantics of the
     * programming language or assembly architecture you are modeling.
     * 
     * The arguments must have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVSHL(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvshl(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Logical shift right <remarks> It is equivalent to unsigned division by
     * <code>2^x</code> where \c x is the value of <paramref name="t2"/>.
     * 
     * NB. The semantics of shift operations varies between environments. This
     * definition does not necessarily capture directly the semantics of the
     * programming language or assembly architecture you are modeling.
     * 
     * The arguments must have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVLSHR(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvlshr(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Arithmetic shift right <remarks> It is like logical shift right except
     * that the most significant bits of the result always copy the most
     * significant bit of the second argument.
     * 
     * NB. The semantics of shift operations varies between environments. This
     * definition does not necessarily capture directly the semantics of the
     * programming language or assembly architecture you are modeling.
     * 
     * The arguments must have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVASHR(BitVecExpr t1, BitVecExpr t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvashr(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Rotate Left. <remarks> Rotate bits of \c t to the left \c i times. The
     * argument <paramref name="t"/> must have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVRotateLeft(int i, BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkRotateLeft(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Rotate Right. <remarks> Rotate bits of \c t to the right \c i times. The
     * argument <paramref name="t"/> must have a bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVRotateRight(int i, BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkRotateRight(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Rotate Left. <remarks> Rotate bits of <paramref name="t1"/> to the left
     * <paramref name="t2"/> times. The arguments must have the same bit-vector
     * sort. </remarks>
     **/
    public BitVecExpr mkBVRotateLeft(BitVecExpr t1, BitVecExpr t2)
            throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkExtRotateLeft(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Rotate Right. <remarks> Rotate bits of <paramref name="t1"/> to the
     * right<paramref name="t2"/> times. The arguments must have the same
     * bit-vector sort. </remarks>
     **/
    public BitVecExpr mkBVRotateRight(BitVecExpr t1, BitVecExpr t2)
            throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkExtRotateRight(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an <paramref name="n"/> bit bit-vector from the integer argument
     * <paramref name="t"/>. <remarks> NB. This function is essentially treated
     * as uninterpreted. So you cannot expect Z3 to precisely reflect the
     * semantics of this function when solving constraints with this function.
     * 
     * The argument must be of integer sort. </remarks>
     **/
    public BitVecExpr mkInt2BV(int n, IntExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkInt2bv(nCtx(), n,
                t.getNativeObject()));
    }

    /**
     * Create an integer from the bit-vector argument <paramref name="t"/>.
     * <remarks> If \c is_signed is false, then the bit-vector \c t1 is treated
     * as unsigned. So the result is non-negative and in the range
     * <code>[0..2^N-1]</code>, where N are the number of bits in <paramref
     * name="t"/>. If \c is_signed is true, \c t1 is treated as a signed
     * bit-vector.
     * 
     * NB. This function is essentially treated as uninterpreted. So you cannot
     * expect Z3 to precisely reflect the semantics of this function when
     * solving constraints with this function.
     * 
     * The argument must be of bit-vector sort. </remarks>
     **/
    public IntExpr mkBV2Int(BitVecExpr t, boolean signed) throws Z3Exception
    {

        checkContextMatch(t);
        return new IntExpr(this, Native.mkBv2int(nCtx(), t.getNativeObject(),
                (signed) ? true : false));
    }

    /**
     * Create a predicate that checks that the bit-wise addition does not
     * overflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVAddNoOverflow(BitVecExpr t1, BitVecExpr t2,
            boolean isSigned) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvaddNoOverflow(nCtx(), t1
                .getNativeObject(), t2.getNativeObject(), (isSigned) ? true
                : false));
    }

    /**
     * Create a predicate that checks that the bit-wise addition does not
     * underflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVAddNoUnderflow(BitVecExpr t1, BitVecExpr t2)
            throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvaddNoUnderflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise subtraction does not
     * overflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSubNoOverflow(BitVecExpr t1, BitVecExpr t2)
            throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsubNoOverflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise subtraction does not
     * underflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSubNoUnderflow(BitVecExpr t1, BitVecExpr t2,
            boolean isSigned) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsubNoUnderflow(nCtx(), t1
                .getNativeObject(), t2.getNativeObject(), (isSigned) ? true
                : false));
    }

    /**
     * Create a predicate that checks that the bit-wise signed division does not
     * overflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVSDivNoOverflow(BitVecExpr t1, BitVecExpr t2)
            throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsdivNoOverflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise negation does not
     * overflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVNegNoOverflow(BitVecExpr t) throws Z3Exception
    {

        checkContextMatch(t);
        return new BoolExpr(this, Native.mkBvnegNoOverflow(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise multiplication does not
     * overflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVMulNoOverflow(BitVecExpr t1, BitVecExpr t2,
            boolean isSigned) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvmulNoOverflow(nCtx(), t1
                .getNativeObject(), t2.getNativeObject(), (isSigned) ? true
                : false));
    }

    /**
     * Create a predicate that checks that the bit-wise multiplication does not
     * underflow. <remarks> The arguments must be of bit-vector sort. </remarks>
     **/
    public BoolExpr mkBVMulNoUnderflow(BitVecExpr t1, BitVecExpr t2)
            throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvmulNoUnderflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an array constant.
     **/
    public ArrayExpr mkArrayConst(Symbol name, Sort domain, Sort range)
            throws Z3Exception
    {

        return (ArrayExpr) mkConst(name, mkArraySort(domain, range));
    }

    /**
     * Create an array constant.
     **/
    public ArrayExpr mkArrayConst(String name, Sort domain, Sort range)
            throws Z3Exception
    {

        return (ArrayExpr) mkConst(mkSymbol(name), mkArraySort(domain, range));
    }

    /**
     * Array read. <remarks> The argument <code>a</code> is the array and
     * <code>i</code> is the index of the array that gets read.
     * 
     * The node <code>a</code> must have an array sort
     * <code>[domain -> range]</code>, and <code>i</code> must have the sort
     * <code>domain</code>. The sort of the result is <code>range</code>.
     * <seealso cref="MkArraySort"/> <seealso cref="MkStore"/> </remarks>
     **/
    public Expr mkSelect(ArrayExpr a, Expr i) throws Z3Exception
    {

        checkContextMatch(a);
        checkContextMatch(i);
        return Expr.create(
                this,
                Native.mkSelect(nCtx(), a.getNativeObject(),
                        i.getNativeObject()));
    }

    /**
     * Array update. <remarks> The node <code>a</code> must have an array sort
     * <code>[domain -> range]</code>, <code>i</code> must have sort
     * <code>domain</code>, <code>v</code> must have sort range. The sort of the
     * result is <code>[domain -> range]</code>. The semantics of this function
     * is given by the theory of arrays described in the SMT-LIB standard. See
     * http://smtlib.org for more details. The result of this function is an
     * array that is equal to <code>a</code> (with respect to
     * <code>select</code>) on all indices except for <code>i</code>, where it
     * maps to <code>v</code> (and the <code>select</code> of <code>a</code>
     * with respect to <code>i</code> may be a different value). <seealso
     * cref="MkArraySort"/> <seealso cref="MkSelect"/> </remarks>
     **/
    public ArrayExpr mkStore(ArrayExpr a, Expr i, Expr v) throws Z3Exception
    {

        checkContextMatch(a);
        checkContextMatch(i);
        checkContextMatch(v);
        return new ArrayExpr(this, Native.mkStore(nCtx(), a.getNativeObject(),
                i.getNativeObject(), v.getNativeObject()));
    }

    /**
     * Create a constant array. <remarks> The resulting term is an array, such
     * that a <code>select</code>on an arbitrary index produces the value
     * <code>v</code>. <seealso cref="MkArraySort"/> <seealso cref="MkSelect"/>
     * </remarks>
     **/
    public ArrayExpr mkConstArray(Sort domain, Expr v) throws Z3Exception
    {

        checkContextMatch(domain);
        checkContextMatch(v);
        return new ArrayExpr(this, Native.mkConstArray(nCtx(),
                domain.getNativeObject(), v.getNativeObject()));
    }

    /**
     * Maps f on the argument arrays. <remarks> Eeach element of
     * <code>args</code> must be of an array sort
     * <code>[domain_i -> range_i]</code>. The function declaration
     * <code>f</code> must have type <code> range_1 .. range_n -> range</code>.
     * <code>v</code> must have sort range. The sort of the result is
     * <code>[domain_i -> range]</code>. <seealso cref="MkArraySort"/> <seealso
     * cref="MkSelect"/> <seealso cref="MkStore"/> </remarks>
     **/
    public ArrayExpr mkMap(FuncDecl f, ArrayExpr... args) throws Z3Exception
    {

        checkContextMatch(f);
        checkContextMatch(args);
        return (ArrayExpr) Expr.create(this, Native.mkMap(nCtx(),
                f.getNativeObject(), AST.arrayLength(args),
                AST.arrayToNative(args)));
    }

    /**
     * Access the array default value. <remarks> Produces the default range
     * value, for arrays that can be represented as finite maps with a default
     * range value. </remarks>
     **/
    public Expr mkTermArray(ArrayExpr array) throws Z3Exception
    {

        checkContextMatch(array);
        return Expr.create(this,
                Native.mkArrayDefault(nCtx(), array.getNativeObject()));
    }

    /**
     * Create a set type.
     **/
    public SetSort mkSetSort(Sort ty) throws Z3Exception
    {

        checkContextMatch(ty);
        return new SetSort(this, ty);
    }

    /**
     * Create an empty set.
     **/
    public Expr mkEmptySet(Sort domain) throws Z3Exception
    {

        checkContextMatch(domain);
        return Expr.create(this,
                Native.mkEmptySet(nCtx(), domain.getNativeObject()));
    }

    /**
     * Create the full set.
     **/
    public Expr mkFullSet(Sort domain) throws Z3Exception
    {

        checkContextMatch(domain);
        return Expr.create(this,
                Native.mkFullSet(nCtx(), domain.getNativeObject()));
    }

    /**
     * Add an element to the set.
     **/
    public Expr mkSetAdd(Expr set, Expr element) throws Z3Exception
    {

        checkContextMatch(set);
        checkContextMatch(element);
        return Expr.create(
                this,
                Native.mkSetAdd(nCtx(), set.getNativeObject(),
                        element.getNativeObject()));
    }

    /**
     * Remove an element from a set.
     **/
    public Expr mkSetDel(Expr set, Expr element) throws Z3Exception
    {

        checkContextMatch(set);
        checkContextMatch(element);
        return Expr.create(
                this,
                Native.mkSetDel(nCtx(), set.getNativeObject(),
                        element.getNativeObject()));
    }

    /**
     * Take the union of a list of sets.
     **/
    public Expr mkSetUnion(Expr... args) throws Z3Exception
    {

        checkContextMatch(args);
        return Expr.create(
                this,
                Native.mkSetUnion(nCtx(), (int) args.length,
                        AST.arrayToNative(args)));
    }

    /**
     * Take the intersection of a list of sets.
     **/
    public Expr mkSetIntersection(Expr... args) throws Z3Exception
    {

        checkContextMatch(args);
        return Expr.create(
                this,
                Native.mkSetIntersect(nCtx(), (int) args.length,
                        AST.arrayToNative(args)));
    }

    /**
     * Take the difference between two sets.
     **/
    public Expr mkSetDifference(Expr arg1, Expr arg2) throws Z3Exception
    {

        checkContextMatch(arg1);
        checkContextMatch(arg2);
        return Expr.create(
                this,
                Native.mkSetDifference(nCtx(), arg1.getNativeObject(),
                        arg2.getNativeObject()));
    }

    /**
     * Take the complement of a set.
     **/
    public Expr mkSetComplement(Expr arg) throws Z3Exception
    {

        checkContextMatch(arg);
        return Expr.create(this,
                Native.mkSetComplement(nCtx(), arg.getNativeObject()));
    }

    /**
     * Check for set membership.
     **/
    public Expr mkSetMembership(Expr elem, Expr set) throws Z3Exception
    {

        checkContextMatch(elem);
        checkContextMatch(set);
        return Expr.create(
                this,
                Native.mkSetMember(nCtx(), elem.getNativeObject(),
                        set.getNativeObject()));
    }

    /**
     * Check for subsetness of sets.
     **/
    public Expr mkSetSubset(Expr arg1, Expr arg2) throws Z3Exception
    {

        checkContextMatch(arg1);
        checkContextMatch(arg2);
        return Expr.create(
                this,
                Native.mkSetSubset(nCtx(), arg1.getNativeObject(),
                        arg2.getNativeObject()));
    }

    /**
     * Create a Term of a given sort. <param name="v">A string representing the
     * Term value in decimal notation. If the given sort is a real, then the
     * Term can be a rational, that is, a string of the form
     * <code>[num]* / [num]*</code>.</param> <param name="ty">The sort of the
     * numeral. In the current implementation, the given sort can be an int,
     * real, or bit-vectors of arbitrary size. </param>
     * 
     * @return A Term with value <paramref name="v"/> and sort <paramref
     *         name="ty"/>
     **/
    public Expr mkNumeral(String v, Sort ty) throws Z3Exception
    {

        checkContextMatch(ty);
        return Expr.create(this,
                Native.mkNumeral(nCtx(), v, ty.getNativeObject()));
    }

    /**
     * Create a Term of a given sort. This function can be use to create
     * numerals that fit in a machine integer. It is slightly faster than
     * <code>MakeNumeral</code> since it is not necessary to parse a string.
     * <param name="v">Value of the numeral</param> <param name="ty">Sort of the
     * numeral</param>
     * 
     * @return A Term with value <paramref name="v"/> and type <paramref
     *         name="ty"/>
     **/
    public Expr mkNumeral(int v, Sort ty) throws Z3Exception
    {

        checkContextMatch(ty);
        return Expr.create(this, Native.mkInt(nCtx(), v, ty.getNativeObject()));
    }

    /**
     * Create a Term of a given sort. This function can be use to create
     * numerals that fit in a machine integer. It is slightly faster than
     * <code>MakeNumeral</code> since it is not necessary to parse a string.
     * <param name="v">Value of the numeral</param> <param name="ty">Sort of the
     * numeral</param>
     * 
     * @return A Term with value <paramref name="v"/> and type <paramref
     *         name="ty"/>
     **/
    public Expr mkNumeral(long v, Sort ty) throws Z3Exception
    {

        checkContextMatch(ty);
        return Expr.create(this,
                Native.mkInt64(nCtx(), v, ty.getNativeObject()));
    }

    /**
     * Create a real from a fraction. <param name="num">numerator of
     * rational.</param> <param name="den">denominator of rational.</param>
     * 
     * @return A Term with value <paramref name="num"/>/<paramref name="den"/>
     *         and sort Real <seealso cref="MkNumeral(string, Sort)"/>
     **/
    public RatNum mkReal(int num, int den) throws Z3Exception
    {
        if (den == 0)
            throw new Z3Exception("Denominator is zero");

        return new RatNum(this, Native.mkReal(nCtx(), num, den));
    }

    /**
     * Create a real numeral. <param name="v">A string representing the Term
     * value in decimal notation.</param>
     * 
     * @return A Term with value <paramref name="v"/> and sort Real
     **/
    public RatNum mkReal(String v) throws Z3Exception
    {

        return new RatNum(this, Native.mkNumeral(nCtx(), v, getRealSort()
                .getNativeObject()));
    }

    /**
     * Create a real numeral. <param name="v">value of the numeral.</param>
     * 
     * @return A Term with value <paramref name="v"/> and sort Real
     **/
    public RatNum mkReal(int v) throws Z3Exception
    {

        return new RatNum(this, Native.mkInt(nCtx(), v, getRealSort()
                .getNativeObject()));
    }

    /**
     * Create a real numeral. <param name="v">value of the numeral.</param>
     * 
     * @return A Term with value <paramref name="v"/> and sort Real
     **/
    public RatNum mkReal(long v) throws Z3Exception
    {

        return new RatNum(this, Native.mkInt64(nCtx(), v, getRealSort()
                .getNativeObject()));
    }

    /**
     * Create an integer numeral. <param name="v">A string representing the Term
     * value in decimal notation.</param>
     **/
    public IntNum mkInt(String v) throws Z3Exception
    {

        return new IntNum(this, Native.mkNumeral(nCtx(), v, getIntSort()
                .getNativeObject()));
    }

    /**
     * Create an integer numeral. <param name="v">value of the numeral.</param>
     * 
     * @return A Term with value <paramref name="v"/> and sort Integer
     **/
    public IntNum mkInt(int v) throws Z3Exception
    {

        return new IntNum(this, Native.mkInt(nCtx(), v, getIntSort()
                .getNativeObject()));
    }

    /**
     * Create an integer numeral. <param name="v">value of the numeral.</param>
     * 
     * @return A Term with value <paramref name="v"/> and sort Integer
     **/
    public IntNum mkInt(long v) throws Z3Exception
    {

        return new IntNum(this, Native.mkInt64(nCtx(), v, getIntSort()
                .getNativeObject()));
    }

    /**
     * Create a bit-vector numeral. <param name="v">A string representing the
     * value in decimal notation.</param> <param name="size">the size of the
     * bit-vector</param>
     **/
    public BitVecNum mkBV(String v, int size) throws Z3Exception
    {

        return (BitVecNum) mkNumeral(v, mkBitVecSort(size));
    }

    /**
     * Create a bit-vector numeral. <param name="v">value of the
     * numeral.</param> <param name="size">the size of the bit-vector</param>
     **/
    public BitVecNum mkBV(int v, int size) throws Z3Exception
    {

        return (BitVecNum) mkNumeral(v, mkBitVecSort(size));
    }

    /**
     * Create a bit-vector numeral. <param name="v">value of the
     * numeral.</param> * <param name="size">the size of the bit-vector</param>
     **/
    public BitVecNum mkBV(long v, int size) throws Z3Exception
    {

        return (BitVecNum) mkNumeral(v, mkBitVecSort(size));
    }

    /**
     * Create a universal Quantifier. <remarks> Creates a forall formula, where
     * <paramref name="weight"/> is the weight, <paramref name="patterns"/> is
     * an array of patterns, <paramref name="sorts"/> is an array with the sorts
     * of the bound variables, <paramref name="names"/> is an array with the
     * 'names' of the bound variables, and <paramref name="body"/> is the body
     * of the quantifier. Quantifiers are associated with weights indicating the
     * importance of using the quantifier during instantiation. </remarks>
     * <param name="sorts">the sorts of the bound variables.</param> <param
     * name="names">names of the bound variables</param> <param name="body">the
     * body of the quantifier.</param> <param name="weight">quantifiers are
     * associated with weights indicating the importance of using the quantifier
     * during instantiation. By default, pass the weight 0.</param> <param
     * name="patterns">array containing the patterns created using
     * <code>MkPattern</code>.</param> <param name="noPatterns">array containing
     * the anti-patterns created using <code>MkPattern</code>.</param> <param
     * name="quantifierID">optional symbol to track quantifier.</param> <param
     * name="skolemID">optional symbol to track skolem constants.</param>
     **/
    public Quantifier mkForall(Sort[] sorts, Symbol[] names, Expr body,
            int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID) throws Z3Exception
    {

        return new Quantifier(this, true, sorts, names, body, weight, patterns,
                noPatterns, quantifierID, skolemID);
    }

    /**
     * Create a universal Quantifier.
     **/
    public Quantifier mkForall(Expr[] boundConstants, Expr body, int weight,
            Pattern[] patterns, Expr[] noPatterns, Symbol quantifierID,
            Symbol skolemID) throws Z3Exception
    {

        return new Quantifier(this, true, boundConstants, body, weight,
                patterns, noPatterns, quantifierID, skolemID);
    }

    /**
     * Create an existential Quantifier. <seealso cref=
     * "MkForall(Sort[],Symbol[],Expr,uint,Pattern[],Expr[],Symbol,Symbol)"/>
     **/
    public Quantifier mkExists(Sort[] sorts, Symbol[] names, Expr body,
            int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID) throws Z3Exception
    {

        return new Quantifier(this, false, sorts, names, body, weight,
                patterns, noPatterns, quantifierID, skolemID);
    }

    /**
     * Create an existential Quantifier.
     **/
    public Quantifier mkExists(Expr[] boundConstants, Expr body, int weight,
            Pattern[] patterns, Expr[] noPatterns, Symbol quantifierID,
            Symbol skolemID) throws Z3Exception
    {

        return new Quantifier(this, false, boundConstants, body, weight,
                patterns, noPatterns, quantifierID, skolemID);
    }

    /**
     * Create a Quantifier.
     **/
    public Quantifier mkQuantifier(boolean universal, Sort[] sorts,
            Symbol[] names, Expr body, int weight, Pattern[] patterns,
            Expr[] noPatterns, Symbol quantifierID, Symbol skolemID)
            throws Z3Exception
    {

        if (universal)
            return mkForall(sorts, names, body, weight, patterns, noPatterns,
                    quantifierID, skolemID);
        else
            return mkExists(sorts, names, body, weight, patterns, noPatterns,
                    quantifierID, skolemID);
    }

    /**
     * Create a Quantifier.
     **/
    public Quantifier mkQuantifier(boolean universal, Expr[] boundConstants,
            Expr body, int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID) throws Z3Exception
    {

        if (universal)
            return mkForall(boundConstants, body, weight, patterns, noPatterns,
                    quantifierID, skolemID);
        else
            return mkExists(boundConstants, body, weight, patterns, noPatterns,
                    quantifierID, skolemID);
    }

    /**
     * Selects the format used for pretty-printing expressions. <remarks> The
     * default mode for pretty printing expressions is to produce SMT-LIB style
     * output where common subexpressions are printed at each occurrence. The
     * mode is called Z3_PRINT_SMTLIB_FULL. To print shared common
     * subexpressions only once, use the Z3_PRINT_LOW_LEVEL mode. To print in
     * way that conforms to SMT-LIB standards and uses let expressions to share
     * common sub-expressions use Z3_PRINT_SMTLIB_COMPLIANT. </remarks> <seealso
     * cref="AST.ToString()"/> <seealso cref="Pattern.ToString()"/> <seealso
     * cref="FuncDecl.ToString()"/> <seealso cref="Sort.ToString()"/>
     **/
    public void setPrintMode(Z3_ast_print_mode value) throws Z3Exception
    {
        Native.setAstPrintMode(nCtx(), value.toInt());
    }

    /**
     * Convert a benchmark into an SMT-LIB formatted string. <param
     * name="name">Name of the benchmark. The argument is optional.</param>
     * <param name="logic">The benchmark logic. </param> <param
     * name="status">The status string (sat, unsat, or unknown)</param> <param
     * name="attributes">Other attributes, such as source, difficulty or
     * category.</param> <param name="assumptions">Auxiliary
     * assumptions.</param> <param name="formula">Formula to be checked for
     * consistency in conjunction with assumptions.</param>
     * 
     * @return A string representation of the benchmark.
     **/
    public String benchmarkToSMTString(String name, String logic,
            String status, String attributes, BoolExpr[] assumptions,
            BoolExpr formula) throws Z3Exception
    {

        return Native.benchmarkToSmtlibString(nCtx(), name, logic, status,
                attributes, (int) assumptions.length,
                AST.arrayToNative(assumptions), formula.getNativeObject());
    }

    /**
     * Parse the given string using the SMT-LIB parser. <remarks> The symbol
     * table of the parser can be initialized using the given sorts and
     * declarations. The symbols in the arrays <paramref name="sortNames"/> and
     * <paramref name="declNames"/> don't need to match the names of the sorts
     * and declarations in the arrays <paramref name="sorts"/> and <paramref
     * name="decls"/>. This is a useful feature since we can use arbitrary names
     * to reference sorts and declarations. </remarks>
     **/
    public void parseSMTLIBString(String str, Symbol[] sortNames, Sort[] sorts,
            Symbol[] declNames, FuncDecl[] decls) throws Z3Exception
    {
        int csn = Symbol.arrayLength(sortNames);
        int cs = Sort.arrayLength(sorts);
        int cdn = Symbol.arrayLength(declNames);
        int cd = AST.arrayLength(decls);
        if (csn != cs || cdn != cd)
            throw new Z3Exception("Argument size mismatch");
        Native.parseSmtlibString(nCtx(), str, AST.arrayLength(sorts),
                Symbol.arrayToNative(sortNames), AST.arrayToNative(sorts),
                AST.arrayLength(decls), Symbol.arrayToNative(declNames),
                AST.arrayToNative(decls));
    }

    /**
     * Parse the given file using the SMT-LIB parser. <seealso
     * cref="ParseSMTLIBString"/>
     **/
    public void parseSMTLIBFile(String fileName, Symbol[] sortNames,
            Sort[] sorts, Symbol[] declNames, FuncDecl[] decls)
            throws Z3Exception
    {
        int csn = Symbol.arrayLength(sortNames);
        int cs = Sort.arrayLength(sorts);
        int cdn = Symbol.arrayLength(declNames);
        int cd = AST.arrayLength(decls);
        if (csn != cs || cdn != cd)
            throw new Z3Exception("Argument size mismatch");
        Native.parseSmtlibFile(nCtx(), fileName, AST.arrayLength(sorts),
                Symbol.arrayToNative(sortNames), AST.arrayToNative(sorts),
                AST.arrayLength(decls), Symbol.arrayToNative(declNames),
                AST.arrayToNative(decls));
    }

    /**
     * The number of SMTLIB formulas parsed by the last call to
     * <code>ParseSMTLIBString</code> or <code>ParseSMTLIBFile</code>.
     **/
    public int getNumSMTLIBFormulas() throws Z3Exception
    {
        return Native.getSmtlibNumFormulas(nCtx());
    }

    /**
     * The formulas parsed by the last call to <code>ParseSMTLIBString</code> or
     * <code>ParseSMTLIBFile</code>.
     **/
    public BoolExpr[] getSMTLIBFormulas() throws Z3Exception
    {

        int n = getNumSMTLIBFormulas();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (BoolExpr) Expr.create(this,
                    Native.getSmtlibFormula(nCtx(), i));
        return res;
    }

    /**
     * The number of SMTLIB assumptions parsed by the last call to
     * <code>ParseSMTLIBString</code> or <code>ParseSMTLIBFile</code>.
     **/
    public int getNumSMTLIBAssumptions() throws Z3Exception
    {
        return Native.getSmtlibNumAssumptions(nCtx());
    }

    /**
     * The assumptions parsed by the last call to <code>ParseSMTLIBString</code>
     * or <code>ParseSMTLIBFile</code>.
     **/
    public BoolExpr[] getSMTLIBAssumptions() throws Z3Exception
    {

        int n = getNumSMTLIBAssumptions();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (BoolExpr) Expr.create(this,
                    Native.getSmtlibAssumption(nCtx(), i));
        return res;
    }

    /**
     * The number of SMTLIB declarations parsed by the last call to
     * <code>ParseSMTLIBString</code> or <code>ParseSMTLIBFile</code>.
     **/
    public int getNumSMTLIBDecls() throws Z3Exception
    {
        return Native.getSmtlibNumDecls(nCtx());
    }

    /**
     * The declarations parsed by the last call to
     * <code>ParseSMTLIBString</code> or <code>ParseSMTLIBFile</code>.
     **/
    public FuncDecl[] getSMTLIBDecls() throws Z3Exception
    {

        int n = getNumSMTLIBDecls();
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl(this, Native.getSmtlibDecl(nCtx(), i));
        return res;
    }

    /**
     * The number of SMTLIB sorts parsed by the last call to
     * <code>ParseSMTLIBString</code> or <code>ParseSMTLIBFile</code>.
     **/
    public int getNumSMTLIBSorts() throws Z3Exception
    {
        return Native.getSmtlibNumSorts(nCtx());
    }

    /**
     * The declarations parsed by the last call to
     * <code>ParseSMTLIBString</code> or <code>ParseSMTLIBFile</code>.
     **/
    public Sort[] getSMTLIBSorts() throws Z3Exception
    {

        int n = getNumSMTLIBSorts();
        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.create(this, Native.getSmtlibSort(nCtx(), i));
        return res;
    }

    /**
     * Parse the given string using the SMT-LIB2 parser. <seealso
     * cref="ParseSMTLIBString"/>
     * 
     * @return A conjunction of assertions in the scope (up to push/pop) at the
     *         end of the string.
     **/
    public BoolExpr parseSMTLIB2String(String str, Symbol[] sortNames,
            Sort[] sorts, Symbol[] declNames, FuncDecl[] decls)
            throws Z3Exception
    {

        int csn = Symbol.arrayLength(sortNames);
        int cs = Sort.arrayLength(sorts);
        int cdn = Symbol.arrayLength(declNames);
        int cd = AST.arrayLength(decls);
        if (csn != cs || cdn != cd)
            throw new Z3Exception("Argument size mismatch");
        return (BoolExpr) Expr.create(this, Native.parseSmtlib2String(nCtx(),
                str, AST.arrayLength(sorts), Symbol.arrayToNative(sortNames),
                AST.arrayToNative(sorts), AST.arrayLength(decls),
                Symbol.arrayToNative(declNames), AST.arrayToNative(decls)));
    }

    /**
     * Parse the given file using the SMT-LIB2 parser. <seealso
     * cref="ParseSMTLIB2String"/>
     **/
    public BoolExpr parseSMTLIB2File(String fileName, Symbol[] sortNames,
            Sort[] sorts, Symbol[] declNames, FuncDecl[] decls)
            throws Z3Exception
    {

        int csn = Symbol.arrayLength(sortNames);
        int cs = Sort.arrayLength(sorts);
        int cdn = Symbol.arrayLength(declNames);
        int cd = AST.arrayLength(decls);
        if (csn != cs || cdn != cd)
            throw new Z3Exception("Argument size mismatch");
        return (BoolExpr) Expr.create(this, Native.parseSmtlib2File(nCtx(),
                fileName, AST.arrayLength(sorts),
                Symbol.arrayToNative(sortNames), AST.arrayToNative(sorts),
                AST.arrayLength(decls), Symbol.arrayToNative(declNames),
                AST.arrayToNative(decls)));
    }

    /**
     * Creates a new Goal. <remarks> Note that the Context must have been
     * created with proof generation support if <paramref name="proofs"/> is set
     * to true here. </remarks> <param name="models">Indicates whether model
     * generation should be enabled.</param> <param name="unsatCores">Indicates
     * whether unsat core generation should be enabled.</param> <param
     * name="proofs">Indicates whether proof generation should be
     * enabled.</param>
     **/
    public Goal mkGoal(boolean models, boolean unsatCores, boolean proofs)
            throws Z3Exception
    {

        return new Goal(this, models, unsatCores, proofs);
    }

    /**
     * Creates a new ParameterSet.
     **/
    public Params mkParams() throws Z3Exception
    {

        return new Params(this);
    }

    /**
     * The number of supported tactics.
     **/
    public int getNumTactics() throws Z3Exception
    {
        return Native.getNumTactics(nCtx());
    }

    /**
     * The names of all supported tactics.
     **/
    public String[] getTacticNames() throws Z3Exception
    {

        int n = getNumTactics();
        String[] res = new String[n];
        for (int i = 0; i < n; i++)
            res[i] = Native.getTacticName(nCtx(), i);
        return res;
    }

    /**
     * Returns a string containing a description of the tactic with the given
     * name.
     **/
    public String getTacticDescription(String name) throws Z3Exception
    {

        return Native.tacticGetDescr(nCtx(), name);
    }

    /**
     * Creates a new Tactic.
     **/
    public Tactic mkTactic(String name) throws Z3Exception
    {

        return new Tactic(this, name);
    }

    /**
     * Create a tactic that applies <paramref name="t1"/> to a Goal and then
     * <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.
     **/
    public Tactic andThen(Tactic t1, Tactic t2, Tactic... ts)
            throws Z3Exception
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        checkContextMatch(ts);

        long last = 0;
        if (ts != null && ts.length > 0)
        {
            last = ts[ts.length - 1].getNativeObject();
            for (int i = ts.length - 2; i >= 0; i--)
                last = Native.tacticAndThen(nCtx(), ts[i].getNativeObject(),
                        last);
        }
        if (last != 0)
        {
            last = Native.tacticAndThen(nCtx(), t2.getNativeObject(), last);
            return new Tactic(this, Native.tacticAndThen(nCtx(),
                    t1.getNativeObject(), last));
        } else
            return new Tactic(this, Native.tacticAndThen(nCtx(),
                    t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a tactic that applies <paramref name="t1"/> to a Goal and then
     * <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.
     * <remarks> Shorthand for <code>AndThen</code>. </remarks>
     **/
    public Tactic then(Tactic t1, Tactic t2, Tactic... ts) throws Z3Exception
    {
        return andThen(t1, t2, ts);
    }

    /**
     * Create a tactic that first applies <paramref name="t1"/> to a Goal and if
     * it fails then returns the result of <paramref name="t2"/> applied to the
     * Goal.
     **/
    public Tactic orElse(Tactic t1, Tactic t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new Tactic(this, Native.tacticOrElse(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a tactic that applies <paramref name="t"/> to a goal for <paramref
     * name="ms"/> milliseconds. <remarks> If <paramref name="t"/> does not
     * terminate within <paramref name="ms"/> milliseconds, then it fails.
     * </remarks>
     **/
    public Tactic tryFor(Tactic t, int ms) throws Z3Exception
    {

        checkContextMatch(t);
        return new Tactic(this, Native.tacticTryFor(nCtx(),
                t.getNativeObject(), ms));
    }

    /**
     * Create a tactic that applies <paramref name="t"/> to a given goal if the
     * probe <paramref name="p"/> evaluates to true. <remarks> If <paramref
     * name="p"/> evaluates to false, then the new tactic behaves like the
     * <code>skip</code> tactic. </remarks>
     **/
    public Tactic when(Probe p, Tactic t) throws Z3Exception
    {

        checkContextMatch(t);
        checkContextMatch(p);
        return new Tactic(this, Native.tacticWhen(nCtx(), p.getNativeObject(),
                t.getNativeObject()));
    }

    /**
     * Create a tactic that applies <paramref name="t1"/> to a given goal if the
     * probe <paramref name="p"/> evaluates to true and <paramref name="t2"/>
     * otherwise.
     **/
    public Tactic cond(Probe p, Tactic t1, Tactic t2) throws Z3Exception
    {

        checkContextMatch(p);
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new Tactic(this, Native.tacticCond(nCtx(), p.getNativeObject(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a tactic that keeps applying <paramref name="t"/> until the goal
     * is not modified anymore or the maximum number of iterations <paramref
     * name="max"/> is reached.
     **/
    public Tactic repeat(Tactic t, int max) throws Z3Exception
    {

        checkContextMatch(t);
        return new Tactic(this, Native.tacticRepeat(nCtx(),
                t.getNativeObject(), max));
    }

    /**
     * Create a tactic that just returns the given goal.
     **/
    public Tactic skip() throws Z3Exception
    {

        return new Tactic(this, Native.tacticSkip(nCtx()));
    }

    /**
     * Create a tactic always fails.
     **/
    public Tactic fail() throws Z3Exception
    {

        return new Tactic(this, Native.tacticFail(nCtx()));
    }

    /**
     * Create a tactic that fails if the probe <paramref name="p"/> evaluates to
     * false.
     **/
    public Tactic failIf(Probe p) throws Z3Exception
    {

        checkContextMatch(p);
        return new Tactic(this,
                Native.tacticFailIf(nCtx(), p.getNativeObject()));
    }

    /**
     * Create a tactic that fails if the goal is not triviall satisfiable (i.e.,
     * empty) or trivially unsatisfiable (i.e., contains `false').
     **/
    public Tactic failIfNotDecided() throws Z3Exception
    {
        return new Tactic(this, Native.tacticFailIfNotDecided(nCtx()));
    }

    /**
     * Create a tactic that applies <paramref name="t"/> using the given set of
     * parameters <paramref name="p"/>.
     **/
    public Tactic usingParams(Tactic t, Params p) throws Z3Exception
    {
        checkContextMatch(t);
        checkContextMatch(p);
        return new Tactic(this, Native.tacticUsingParams(nCtx(),
                t.getNativeObject(), p.getNativeObject()));
    }

    /**
     * Create a tactic that applies <paramref name="t"/> using the given set of
     * parameters <paramref name="p"/>. <remarks>Alias for
     * <code>UsingParams</code></remarks>
     **/
    public Tactic with(Tactic t, Params p) throws Z3Exception
    {
        return usingParams(t, p);
    }

    /**
     * Create a tactic that applies the given tactics in parallel.
     **/
    public Tactic parOr(Tactic... t) throws Z3Exception
    {
        checkContextMatch(t);
        return new Tactic(this, Native.tacticParOr(nCtx(),
                Tactic.arrayLength(t), Tactic.arrayToNative(t)));
    }

    /**
     * Create a tactic that applies <paramref name="t1"/> to a given goal and
     * then <paramref name="t2"/> to every subgoal produced by <paramref
     * name="t1"/>. The subgoals are processed in parallel.
     **/
    public Tactic parAndThen(Tactic t1, Tactic t2) throws Z3Exception
    {

        checkContextMatch(t1);
        checkContextMatch(t2);
        return new Tactic(this, Native.tacticParAndThen(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Interrupt the execution of a Z3 procedure. <remarks>This procedure can be
     * used to interrupt: solvers, simplifiers and tactics.</remarks>
     **/
    public void interrupt() throws Z3Exception
    {
        Native.interrupt(nCtx());
    }

    /**
     * The number of supported Probes.
     **/
    public int getNumProbes() throws Z3Exception
    {
        return Native.getNumProbes(nCtx());
    }

    /**
     * The names of all supported Probes.
     **/
    public String[] getProbeNames() throws Z3Exception
    {

        int n = getNumProbes();
        String[] res = new String[n];
        for (int i = 0; i < n; i++)
            res[i] = Native.getProbeName(nCtx(), i);
        return res;
    }

    /**
     * Returns a string containing a description of the probe with the given
     * name.
     **/
    public String getProbeDescription(String name) throws Z3Exception
    {
        return Native.probeGetDescr(nCtx(), name);
    }

    /**
     * Creates a new Probe.
     **/
    public Probe mkProbe(String name) throws Z3Exception
    {
        return new Probe(this, name);
    }

    /**
     * Create a probe that always evaluates to <paramref name="val"/>.
     **/
    public Probe constProbe(double val) throws Z3Exception
    {
        return new Probe(this, Native.probeConst(nCtx(), val));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * <paramref name="p1"/> is less than the value returned by <paramref
     * name="p2"/>
     **/
    public Probe lt(Probe p1, Probe p2) throws Z3Exception
    {

        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeLt(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * <paramref name="p1"/> is greater than the value returned by <paramref
     * name="p2"/>
     **/
    public Probe gt(Probe p1, Probe p2) throws Z3Exception
    {

        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeGt(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * <paramref name="p1"/> is less than or equal the value returned by
     * <paramref name="p2"/>
     **/
    public Probe le(Probe p1, Probe p2) throws Z3Exception
    {

        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeLe(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * <paramref name="p1"/> is greater than or equal the value returned by
     * <paramref name="p2"/>
     **/
    public Probe ge(Probe p1, Probe p2) throws Z3Exception
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeGe(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * <paramref name="p1"/> is equal to the value returned by <paramref
     * name="p2"/>
     **/
    public Probe eq(Probe p1, Probe p2) throws Z3Exception
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeEq(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value <paramref
     * name="p1"/> and <paramref name="p2"/> evaluate to "true".
     **/
    public Probe and(Probe p1, Probe p2) throws Z3Exception
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeAnd(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value <paramref
     * name="p1"/> or <paramref name="p2"/> evaluate to "true".
     **/
    public Probe or(Probe p1, Probe p2) throws Z3Exception
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeOr(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value <paramref
     * name="p"/> does not evaluate to "true".
     **/
    public Probe not(Probe p) throws Z3Exception
    {

        checkContextMatch(p);
        return new Probe(this, Native.probeNot(nCtx(), p.getNativeObject()));
    }

    /**
     * Creates a new (incremental) solver. <remarks> This solver also uses a set
     * of builtin tactics for handling the first check-sat command, and
     * check-sat commands that take more than a given number of milliseconds to
     * be solved. </remarks>
     **/
    public Solver mkSolver() throws Z3Exception
    {
        return mkSolver((Symbol) null);
    }

    /**
     * Creates a new (incremental) solver. <remarks> This solver also uses a set
     * of builtin tactics for handling the first check-sat command, and
     * check-sat commands that take more than a given number of milliseconds to
     * be solved. </remarks>
     **/
    public Solver mkSolver(Symbol logic) throws Z3Exception
    {

        if (logic == null)
            return new Solver(this, Native.mkSolver(nCtx()));
        else
            return new Solver(this, Native.mkSolverForLogic(nCtx(),
                    logic.getNativeObject()));
    }

    /**
     * Creates a new (incremental) solver. <seealso cref="MkSolver(Symbol)"/>
     **/
    public Solver mkSolver(String logic) throws Z3Exception
    {

        return mkSolver(mkSymbol(logic));
    }

    /**
     * Creates a new (incremental) solver.
     **/
    public Solver mkSimpleSolver() throws Z3Exception
    {

        return new Solver(this, Native.mkSimpleSolver(nCtx()));
    }

    /**
     * Creates a solver that is implemented using the given tactic. <remarks>
     * The solver supports the commands <code>Push</code> and <code>Pop</code>,
     * but it will always solve each check from scratch. </remarks>
     **/
    public Solver mkSolver(Tactic t) throws Z3Exception
    {

        return new Solver(this, Native.mkSolverFromTactic(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Create a Fixedpoint context.
     **/
    public Fixedpoint mkFixedpoint() throws Z3Exception
    {

        return new Fixedpoint(this);
    }

    /**
     * Wraps an AST. <remarks>This function is used for transitions between
     * native and managed objects. Note that <paramref name="nativeObject"/>
     * must be a native object obtained from Z3 (e.g., through <seealso
     * cref="UnwrapAST"/>) and that it must have a correct reference count (see
     * e.g., <seealso cref="Native.Z3_inc_ref"/>.</remarks> <seealso
     * cref="UnwrapAST"/> <param name="nativeObject">The native pointer to
     * wrap.</param>
     **/
    public AST wrapAST(long nativeObject) throws Z3Exception
    {

        return AST.create(this, nativeObject);
    }

    /**
     * Unwraps an AST. <remarks>This function is used for transitions between
     * native and managed objects. It returns the native pointer to the AST.
     * Note that AST objects are reference counted and unwrapping an AST
     * disables automatic reference counting, i.e., all references to the IntPtr
     * that is returned must be handled externally and through native calls (see
     * e.g., <seealso cref="Native.Z3_inc_ref"/>).</remarks> <seealso
     * cref="WrapAST"/> <param name="a">The AST to unwrap.</param>
     **/
    public long unwrapAST(AST a)
    {
        return a.getNativeObject();
    }

    /**
     * Return a string describing all available parameters to
     * <code>Expr.Simplify</code>.
     **/
    public String SimplifyHelp() throws Z3Exception
    {

        return Native.simplifyGetHelp(nCtx());
    }

    /**
     * Retrieves parameter descriptions for simplifier.
     **/
    public ParamDescrs getSimplifyParameterDescriptions() throws Z3Exception
    {
        return new ParamDescrs(this, Native.simplifyGetParamDescrs(nCtx()));
    }

    /**
     * Enable/disable printing of warning messages to the console. <remarks>Note
     * that this function is static and effects the behaviour of all contexts
     * globally.</remarks>
     **/
    public static void ToggleWarningMessages(boolean enabled)
            throws Z3Exception
    {
        Native.toggleWarningMessages((enabled) ? true : false);
    }

    /**
     * Update a mutable configuration parameter. <remarks> The list of all
     * configuration parameters can be obtained using the Z3 executable:
     * <code>z3.exe -ini?</code> Only a few configuration parameters are mutable
     * once the context is created. An exception is thrown when trying to modify
     * an immutable parameter. </remarks> <seealso cref="GetParamValue"/>
     **/
    public void updateParamValue(String id, String value) throws Z3Exception
    {
        Native.updateParamValue(nCtx(), id, value);
    }

    /**
     * Get a configuration parameter. <remarks> Returns null if the parameter
     * value does not exist. </remarks> <seealso cref="UpdateParamValue"/>
     **/
    public String getParamValue(String id) throws Z3Exception
    {
        Native.StringPtr res = new Native.StringPtr();
        boolean r = Native.getParamValue(nCtx(), id, res);
        if (!r)
            return null;
        else
            return res.value;
    }

    long m_ctx = 0;

    long nCtx()
    {
        return m_ctx;
    }

    void initContext() throws Z3Exception
    {
        setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
        Native.setInternalErrorHandler(nCtx());
    }

    void checkContextMatch(Z3Object other) throws Z3Exception
    {
        if (this != other.getContext())
            throw new Z3Exception("Context mismatch");
    }

    void checkContextMatch(Z3Object[] arr) throws Z3Exception
    {
        if (arr != null)
            for (Z3Object a : arr)
                checkContextMatch(a);
    }

    private ASTDecRefQueue m_AST_DRQ = new ASTDecRefQueue();
    private ASTMapDecRefQueue m_ASTMap_DRQ = new ASTMapDecRefQueue();
    private ASTVectorDecRefQueue m_ASTVector_DRQ = new ASTVectorDecRefQueue();
    private ApplyResultDecRefQueue m_ApplyResult_DRQ = new ApplyResultDecRefQueue();
    private FuncInterpEntryDecRefQueue m_FuncEntry_DRQ = new FuncInterpEntryDecRefQueue();
    private FuncInterpDecRefQueue m_FuncInterp_DRQ = new FuncInterpDecRefQueue();
    private GoalDecRefQueue m_Goal_DRQ = new GoalDecRefQueue();
    private ModelDecRefQueue m_Model_DRQ = new ModelDecRefQueue();
    private ParamsDecRefQueue m_Params_DRQ = new ParamsDecRefQueue();
    private ParamDescrsDecRefQueue m_ParamDescrs_DRQ = new ParamDescrsDecRefQueue();
    private ProbeDecRefQueue m_Probe_DRQ = new ProbeDecRefQueue();
    private SolverDecRefQueue m_Solver_DRQ = new SolverDecRefQueue();
    private StatisticsDecRefQueue m_Statistics_DRQ = new StatisticsDecRefQueue();
    private TacticDecRefQueue m_Tactic_DRQ = new TacticDecRefQueue();
    private FixedpointDecRefQueue m_Fixedpoint_DRQ = new FixedpointDecRefQueue();

    ASTDecRefQueue ast_DRQ()
    {
        return m_AST_DRQ;
    }

    ASTMapDecRefQueue astmap_DRQ()
    {
        return m_ASTMap_DRQ;
    }

    ASTVectorDecRefQueue astvector_DRQ()
    {
        return m_ASTVector_DRQ;
    }

    ApplyResultDecRefQueue applyResult_DRQ()
    {
        return m_ApplyResult_DRQ;
    }

    FuncInterpEntryDecRefQueue funcEntry_DRQ()
    {
        return m_FuncEntry_DRQ;
    }

    FuncInterpDecRefQueue funcInterp_DRQ()
    {
        return m_FuncInterp_DRQ;
    }

    GoalDecRefQueue goal_DRQ()
    {
        return m_Goal_DRQ;
    }

    ModelDecRefQueue model_DRQ()
    {
        return m_Model_DRQ;
    }

    ParamsDecRefQueue params_DRQ()
    {
        return m_Params_DRQ;
    }

    ParamDescrsDecRefQueue paramDescrs_DRQ()
    {
        return m_ParamDescrs_DRQ;
    }

    ProbeDecRefQueue probe_DRQ()
    {
        return m_Probe_DRQ;
    }

    SolverDecRefQueue solver_DRQ()
    {
        return m_Solver_DRQ;
    }

    StatisticsDecRefQueue statistics_DRQ()
    {
        return m_Statistics_DRQ;
    }

    TacticDecRefQueue tactic_DRQ()
    {
        return m_Tactic_DRQ;
    }

    FixedpointDecRefQueue fixedpoint_DRQ()
    {
        return m_Fixedpoint_DRQ;
    }

    protected long m_refCount = 0;

    /**
     * Finalizer.
     **/
    protected void finalize()
    {
        dispose();

        if (m_refCount == 0)
        {
            try
            {
                Native.delContext(m_ctx);
            } catch (Z3Exception e)
            {
                // OK.
            }
            m_ctx = 0;
        } 
        /*
        else
            CMW: re-queue the finalizer? */
    }

    /**
     * Disposes of the context.
     **/
    public void dispose()
    {
        m_AST_DRQ.clear(this);
        m_ASTMap_DRQ.clear(this);
        m_ASTVector_DRQ.clear(this);
        m_ApplyResult_DRQ.clear(this);
        m_FuncEntry_DRQ.clear(this);
        m_FuncInterp_DRQ.clear(this);
        m_Goal_DRQ.clear(this);
        m_Model_DRQ.clear(this);
        m_Params_DRQ.clear(this);
        m_Probe_DRQ.clear(this);
        m_Solver_DRQ.clear(this);
        m_Statistics_DRQ.clear(this);
        m_Tactic_DRQ.clear(this);
        m_Fixedpoint_DRQ.clear(this);

        m_boolSort = null;
        m_intSort = null;
        m_realSort = null;
    }
}
