/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Context.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
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
    public Context()
    {
        super();
        m_ctx = Native.mkContextRc(0);
        initContext();
    }

    /**
     * Constructor.
     * Remarks:
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
     * module parameters. For this purpose we should now use {@code Global.setParameter}
     **/
    public Context(Map<String, String> settings)
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
     * Creates a new symbol using an integer. 
     * Remarks: Not all integers can be passed to this function. 
     * The legal range of unsigned integers is 0 to 2^30-1.
     **/
    public IntSymbol mkSymbol(int i)
    {
        return new IntSymbol(this, i);
    }

    /**
     * Create a symbol using a string.
     **/
    public StringSymbol mkSymbol(String name)
    {
        return new StringSymbol(this, name);
    }

    /**
     * Create an array of symbols.
     **/
    Symbol[] mkSymbols(String[] names)
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
    public BoolSort getBoolSort()
    {
        if (m_boolSort == null)
            m_boolSort = new BoolSort(this);
        return m_boolSort;
    }

    /**
     * Retrieves the Integer sort of the context.
     **/
    public IntSort getIntSort()
    {
        if (m_intSort == null)
            m_intSort = new IntSort(this);
        return m_intSort;
    }

    /**
     * Retrieves the Real sort of the context.
     **/
    public RealSort getRealSort()
    {
        if (m_realSort == null)
            m_realSort = new RealSort(this);
        return m_realSort;
    }

    /**
     * Create a new Boolean sort.
     **/
    public BoolSort mkBoolSort()
    {
        return new BoolSort(this);
    }

    /**
     * Create a new uninterpreted sort.
     **/
    public UninterpretedSort mkUninterpretedSort(Symbol s)
    {
        checkContextMatch(s);
        return new UninterpretedSort(this, s);
    }

    /**
     * Create a new uninterpreted sort.
     **/
    public UninterpretedSort mkUninterpretedSort(String str)
    {
        return mkUninterpretedSort(mkSymbol(str));
    }

    /**
     * Create a new integer sort.
     **/
    public IntSort mkIntSort()
    {
        return new IntSort(this);
    }

    /**
     * Create a real sort.
     **/
    public RealSort mkRealSort()
    {
        return new RealSort(this);
    }

    /**
     * Create a new bit-vector sort.
     **/
    public BitVecSort mkBitVecSort(int size)
    {
        return new BitVecSort(this, Native.mkBvSort(nCtx(), size));
    }

    /**
     * Create a new array sort.
     **/
    public ArraySort mkArraySort(Sort domain, Sort range)
    {
        checkContextMatch(domain);
        checkContextMatch(range);
        return new ArraySort(this, domain, range);
    }

    /**
     * Create a new tuple sort.
     **/
    public TupleSort mkTupleSort(Symbol name, Symbol[] fieldNames,
            Sort[] fieldSorts)
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
           
    {
        checkContextMatch(name);
        checkContextMatch(enumNames);
        return new EnumSort(this, name, enumNames);
    }

    /**
     * Create a new enumeration sort.
     **/
    public EnumSort mkEnumSort(String name, String... enumNames)
           
    {
        return new EnumSort(this, mkSymbol(name), mkSymbols(enumNames));
    }

    /**
     * Create a new list sort.
     **/
    public ListSort mkListSort(Symbol name, Sort elemSort)
    {
        checkContextMatch(name);
        checkContextMatch(elemSort);
        return new ListSort(this, name, elemSort);
    }

    /**
     * Create a new list sort.
     **/
    public ListSort mkListSort(String name, Sort elemSort)
    {
        checkContextMatch(elemSort);
        return new ListSort(this, mkSymbol(name), elemSort);
    }

    /**
     * Create a new finite domain sort.
     **/
    public FiniteDomainSort mkFiniteDomainSort(Symbol name, long size)
           
    {
        checkContextMatch(name);
        return new FiniteDomainSort(this, name, size);
    }

    /**
     * Create a new finite domain sort.
     **/
    public FiniteDomainSort mkFiniteDomainSort(String name, long size)
           
    {
        return new FiniteDomainSort(this, mkSymbol(name), size);
    }

    /**
     * Create a datatype constructor. 
     * @param name constructor name 
     * @param recognizer name of recognizer function. 
     * @param fieldNames names of the constructor fields. 
     * @param sorts field sorts, 0 if the field sort refers to a recursive sort. 
     * @param sortRefs reference to datatype sort that is an argument to the 
     * constructor; if the corresponding sort reference is 0, then the value in sort_refs should be
     * an index referring to one of the recursive datatypes that is
     * declared.
     **/
    public Constructor mkConstructor(Symbol name, Symbol recognizer,
            Symbol[] fieldNames, Sort[] sorts, int[] sortRefs)
           
    {

        return new Constructor(this, name, recognizer, fieldNames, sorts,
                sortRefs);
    }

    /**
     * Create a datatype constructor. 
     * @param name  
     * @param recognizer  
     * @param fieldNames  
     * @param sorts  
     * @param sortRefs 
     * 
     * @return
     **/
    public Constructor mkConstructor(String name, String recognizer,
            String[] fieldNames, Sort[] sorts, int[] sortRefs)
           
    {

        return new Constructor(this, mkSymbol(name), mkSymbol(recognizer),
                mkSymbols(fieldNames), sorts, sortRefs);
    }

    /**
     * Create a new datatype sort.
     **/
    public DatatypeSort mkDatatypeSort(Symbol name, Constructor[] constructors)
           
    {
        checkContextMatch(name);
        checkContextMatch(constructors);
        return new DatatypeSort(this, name, constructors);
    }

    /**
     * Create a new datatype sort.
     **/
    public DatatypeSort mkDatatypeSort(String name, Constructor[] constructors)
           
    {
        checkContextMatch(constructors);
        return new DatatypeSort(this, mkSymbol(name), constructors);
    }

    /**
     * Create mutually recursive datatypes. 
     * @param names names of datatype sorts 
     * @param c list of constructors, one list per sort.
     **/
    public DatatypeSort[] mkDatatypeSorts(Symbol[] names, Constructor[][] c)
           
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
     * Create mutually recursive data-types. 
     * @param names  
     * @param c 
     * 
     * @return
     **/
    public DatatypeSort[] mkDatatypeSorts(String[] names, Constructor[][] c)
           
    {
        return mkDatatypeSorts(mkSymbols(names), c);
    }

    /**
     * Update a datatype field at expression t with value v.
     * The function performs a record update at t. The field
     * that is passed in as argument is updated with value v,
     * the remainig fields of t are unchanged.	
     **/
    public Expr MkUpdateField(FuncDecl field, Expr t, Expr v) 
            throws Z3Exception
    {
	return Expr.create
	    (this, 
	     Native.datatypeUpdateField
	     (nCtx(), field.getNativeObject(),
	      t.getNativeObject(), v.getNativeObject()));		
    }


    /**
     * Creates a new function declaration.
     **/
    public FuncDecl mkFuncDecl(Symbol name, Sort[] domain, Sort range)
           
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
           
    {
        checkContextMatch(domain);
        checkContextMatch(range);
        return new FuncDecl(this, mkSymbol(name), domain, range);
    }

    /**
     * Creates a new function declaration.
     **/
    public FuncDecl mkFuncDecl(String name, Sort domain, Sort range)
           
    {
        checkContextMatch(domain);
        checkContextMatch(range);
        Sort[] q = new Sort[] { domain };
        return new FuncDecl(this, mkSymbol(name), q, range);
    }

    /**
     * Creates a fresh function declaration with a name prefixed with
     * {@code prefix}. 
     * @see mkFuncDecl(String,Sort,Sort)
     * @see mkFuncDecl(String,Sort[],Sort)
     **/
    public FuncDecl mkFreshFuncDecl(String prefix, Sort[] domain, Sort range)
           
    {
        checkContextMatch(domain);
        checkContextMatch(range);
        return new FuncDecl(this, prefix, domain, range);
    }

    /**
     * Creates a new constant function declaration.
     **/
    public FuncDecl mkConstDecl(Symbol name, Sort range)
    {
        checkContextMatch(name);
        checkContextMatch(range);
        return new FuncDecl(this, name, null, range);
    }

    /**
     * Creates a new constant function declaration.
     **/
    public FuncDecl mkConstDecl(String name, Sort range)
    {
        checkContextMatch(range);
        return new FuncDecl(this, mkSymbol(name), null, range);
    }

    /**
     * Creates a fresh constant function declaration with a name prefixed with
     * {@code prefix"}. 
     * @see mkFuncDecl(String,Sort,Sort)
     * @see mkFuncDecl(String,Sort[],Sort)
     **/
    public FuncDecl mkFreshConstDecl(String prefix, Sort range)
           
    {
        checkContextMatch(range);
        return new FuncDecl(this, prefix, null, range);
    }

    /**
     * Creates a new bound variable. 
     * @param index The de-Bruijn index of the variable 
     * @param ty The sort of the variable
     **/
    public Expr mkBound(int index, Sort ty)
    {
        return Expr.create(this,
                Native.mkBound(nCtx(), index, ty.getNativeObject()));
    }

    /**
     * Create a quantifier pattern.
     **/
    public Pattern mkPattern(Expr... terms)
    {
        if (terms.length == 0)
            throw new Z3Exception("Cannot create a pattern from zero terms");

        long[] termsNative = AST.arrayToNative(terms);
        return new Pattern(this, Native.mkPattern(nCtx(), (int) terms.length,
                termsNative));
    }

    /**
     * Creates a new Constant of sort {@code range} and named
     * {@code name}.
     **/
    public Expr mkConst(Symbol name, Sort range)
    {
        checkContextMatch(name);
        checkContextMatch(range);

        return Expr.create(
                this,
                Native.mkConst(nCtx(), name.getNativeObject(),
                        range.getNativeObject()));
    }

    /**
     * Creates a new Constant of sort {@code range} and named
     * {@code name}.
     **/
    public Expr mkConst(String name, Sort range)
    {
        return mkConst(mkSymbol(name), range);
    }

    /**
     * Creates a fresh Constant of sort {@code range} and a name
     * prefixed with {@code prefix}.
     **/
    public Expr mkFreshConst(String prefix, Sort range)
    {
        checkContextMatch(range);
        return Expr.create(this,
                Native.mkFreshConst(nCtx(), prefix, range.getNativeObject()));
    }

    /**
     * Creates a fresh constant from the FuncDecl {@code f}. 
     * @param f A decl of a 0-arity function
     **/
    public Expr mkConst(FuncDecl f)
    {
        return mkApp(f, (Expr[]) null);
    }

    /**
     * Create a Boolean constant.
     **/
    public BoolExpr mkBoolConst(Symbol name)
    {
        return (BoolExpr) mkConst(name, getBoolSort());
    }

    /**
     * Create a Boolean constant.
     **/
    public BoolExpr mkBoolConst(String name)
    {
        return (BoolExpr) mkConst(mkSymbol(name), getBoolSort());
    }

    /**
     * Creates an integer constant.
     **/
    public IntExpr mkIntConst(Symbol name)
    {
        return (IntExpr) mkConst(name, getIntSort());
    }

    /**
     * Creates an integer constant.
     **/
    public IntExpr mkIntConst(String name)
    {
        return (IntExpr) mkConst(name, getIntSort());
    }

    /**
     * Creates a real constant.
     **/
    public RealExpr mkRealConst(Symbol name)
    {
        return (RealExpr) mkConst(name, getRealSort());
    }

    /**
     * Creates a real constant.
     **/
    public RealExpr mkRealConst(String name)
    {
        return (RealExpr) mkConst(name, getRealSort());
    }

    /**
     * Creates a bit-vector constant.
     **/
    public BitVecExpr mkBVConst(Symbol name, int size)
    {
        return (BitVecExpr) mkConst(name, mkBitVecSort(size));
    }

    /**
     * Creates a bit-vector constant.
     **/
    public BitVecExpr mkBVConst(String name, int size)
    {
        return (BitVecExpr) mkConst(name, mkBitVecSort(size));
    }

    /**
     * Create a new function application.
     **/
    public Expr mkApp(FuncDecl f, Expr... args)
    {
        checkContextMatch(f);
        checkContextMatch(args);
        return Expr.create(this, f, args);
    }

    /**
     * The true Term.
     **/
    public BoolExpr mkTrue()
    {
        return new BoolExpr(this, Native.mkTrue(nCtx()));
    }

    /**
     * The false Term.
     **/
    public BoolExpr mkFalse()
    {
        return new BoolExpr(this, Native.mkFalse(nCtx()));
    }

    /**
     * Creates a Boolean value.
     **/
    public BoolExpr mkBool(boolean value)
    {
        return value ? mkTrue() : mkFalse();
    }

    /**
     * Creates the equality {@code x"/> = <paramref name="y}.
     **/
    public BoolExpr mkEq(Expr x, Expr y)
    {
        checkContextMatch(x);
        checkContextMatch(y);
        return new BoolExpr(this, Native.mkEq(nCtx(), x.getNativeObject(),
                y.getNativeObject()));
    }

    /**
     * Creates a {@code distinct} term.
     **/
    public BoolExpr mkDistinct(Expr... args)
    {
        checkContextMatch(args);
        return new BoolExpr(this, Native.mkDistinct(nCtx(), (int) args.length,
                AST.arrayToNative(args)));
    }

    /**
     * Mk an expression representing {@code not(a)}.
     **/
    public BoolExpr mkNot(BoolExpr a)
    {
        checkContextMatch(a);
        return new BoolExpr(this, Native.mkNot(nCtx(), a.getNativeObject()));
    }

    /**
     * Create an expression representing an if-then-else:
     * {@code ite(t1, t2, t3)}. 
     * @param t1 An expression with Boolean sort 
     * @param t2 An expression  
     * @param t3 An expression with the same sort as {@code t2}
     **/
    public Expr mkITE(BoolExpr t1, Expr t2, Expr t3)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        checkContextMatch(t3);
        return Expr.create(this, Native.mkIte(nCtx(), t1.getNativeObject(),
                t2.getNativeObject(), t3.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 iff t2}.
     **/
    public BoolExpr mkIff(BoolExpr t1, BoolExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkIff(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 -> t2}.
     **/
    public BoolExpr mkImplies(BoolExpr t1, BoolExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkImplies(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 xor t2}.
     **/
    public BoolExpr mkXor(BoolExpr t1, BoolExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkXor(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t[0] and t[1] and ...}.
     **/
    public BoolExpr mkAnd(BoolExpr... t)
    {
        checkContextMatch(t);
        return new BoolExpr(this, Native.mkAnd(nCtx(), (int) t.length,
                AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing {@code t[0] or t[1] or ...}.
     **/
    public BoolExpr mkOr(BoolExpr... t)
    {
        checkContextMatch(t);
        return new BoolExpr(this, Native.mkOr(nCtx(), (int) t.length,
                AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing {@code t[0] + t[1] + ...}.
     **/
    public ArithExpr mkAdd(ArithExpr... t)
    {
        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkAdd(nCtx(), (int) t.length, AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing {@code t[0] * t[1] * ...}.
     **/
    public ArithExpr mkMul(ArithExpr... t)
    {
        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkMul(nCtx(), (int) t.length, AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing {@code t[0] - t[1] - ...}.
     **/
    public ArithExpr mkSub(ArithExpr... t)
    {
        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkSub(nCtx(), (int) t.length, AST.arrayToNative(t)));
    }

    /**
     * Create an expression representing {@code -t}.
     **/
    public ArithExpr mkUnaryMinus(ArithExpr t)
    {
        checkContextMatch(t);
        return (ArithExpr) Expr.create(this,
                Native.mkUnaryMinus(nCtx(), t.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 / t2}.
     **/
    public ArithExpr mkDiv(ArithExpr t1, ArithExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return (ArithExpr) Expr.create(this, Native.mkDiv(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 mod t2}.
     * Remarks: The
     * arguments must have int type.
     **/
    public IntExpr mkMod(IntExpr t1, IntExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new IntExpr(this, Native.mkMod(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 rem t2}.
     * Remarks: The
     * arguments must have int type.
     **/
    public IntExpr mkRem(IntExpr t1, IntExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new IntExpr(this, Native.mkRem(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 ^ t2}.
     **/
    public ArithExpr mkPower(ArithExpr t1, ArithExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return (ArithExpr) Expr.create(
                this,
                Native.mkPower(nCtx(), t1.getNativeObject(),
                        t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 &lt; t2}
     **/
    public BoolExpr mkLt(ArithExpr t1, ArithExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkLt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 &lt;= t2}
     **/
    public BoolExpr mkLe(ArithExpr t1, ArithExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkLe(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 &gt; t2}
     **/
    public BoolExpr mkGt(ArithExpr t1, ArithExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkGt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Create an expression representing {@code t1 &gt;= t2}
     **/
    public BoolExpr mkGe(ArithExpr t1, ArithExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkGe(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Coerce an integer to a real.
     * Remarks:  There is also a converse operation
     * exposed. It follows the semantics prescribed by the SMT-LIB standard.
     * 
     * You can take the floor of a real by creating an auxiliary integer Term
     * {@code k} and and asserting
     * {@code MakeInt2Real(k) &lt;= t1 &lt; MkInt2Real(k)+1}. The argument
     * must be of integer sort. 
     **/
    public RealExpr mkInt2Real(IntExpr t)
    {
        checkContextMatch(t);
        return new RealExpr(this,
                Native.mkInt2real(nCtx(), t.getNativeObject()));
    }

    /**
     * Coerce a real to an integer.
     * Remarks:  The semantics of this function
     * follows the SMT-LIB standard for the function to_int. The argument must
     * be of real sort. 
     **/
    public IntExpr mkReal2Int(RealExpr t)
    {
        checkContextMatch(t);
        return new IntExpr(this, Native.mkReal2int(nCtx(), t.getNativeObject()));
    }

    /**
     * Creates an expression that checks whether a real number is an integer.
     **/
    public BoolExpr mkIsInteger(RealExpr t)
    {
        checkContextMatch(t);
        return new BoolExpr(this, Native.mkIsInt(nCtx(), t.getNativeObject()));
    }

    /**
     * Bitwise negation.
     * Remarks: The argument must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVNot(BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvnot(nCtx(), t.getNativeObject()));
    }

    /**
     * Take conjunction of bits in a vector, return vector of length 1.
     * 
     * Remarks: The argument must have a bit-vector sort.
     **/
    public BitVecExpr mkBVRedAND(BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvredand(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Take disjunction of bits in a vector, return vector of length 1.
     * 
     * Remarks: The argument must have a bit-vector sort.
     **/
    public BitVecExpr mkBVRedOR(BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvredor(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Bitwise conjunction.
     * Remarks: The arguments must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVAND(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvand(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise disjunction.
     * Remarks: The arguments must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVOR(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvor(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Bitwise XOR.
     * Remarks: The arguments must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVXOR(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvxor(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise NAND.
     * Remarks: The arguments must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVNAND(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvnand(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise NOR.
     * Remarks: The arguments must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVNOR(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvnor(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bitwise XNOR.
     * Remarks: The arguments must have a bit-vector
     * sort.
     **/
    public BitVecExpr mkBVXNOR(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvxnor(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Standard two's complement unary minus.
     * Remarks: The arguments must have a
     * bit-vector sort.
     **/
    public BitVecExpr mkBVNeg(BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkBvneg(nCtx(), t.getNativeObject()));
    }

    /**
     * Two's complement addition.
     * Remarks: The arguments must have the same
     * bit-vector sort.
     **/
    public BitVecExpr mkBVAdd(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvadd(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Two's complement subtraction.
     * Remarks: The arguments must have the same
     * bit-vector sort.
     **/
    public BitVecExpr mkBVSub(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsub(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Two's complement multiplication.
     * Remarks: The arguments must have the
     * same bit-vector sort.
     **/
    public BitVecExpr mkBVMul(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvmul(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Unsigned division.
     * Remarks:  It is defined as the floor of
     * {@code t1/t2} if \c t2 is different from zero. If {@code t2} is
     * zero, then the result is undefined. The arguments must have the same
     * bit-vector sort. 
     **/
    public BitVecExpr mkBVUDiv(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvudiv(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Signed division.
     * Remarks:  It is defined in the following way:
     * 
     * - The \c floor of {@code t1/t2} if \c t2 is different from zero, and
     * {@code t1*t2 >= 0}.
     * 
     * - The \c ceiling of {@code t1/t2} if \c t2 is different from zero,
     * and {@code t1*t2 &lt; 0}.
     * 
     * If {@code t2} is zero, then the result is undefined. The arguments
     * must have the same bit-vector sort. 
     **/
    public BitVecExpr mkBVSDiv(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsdiv(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Unsigned remainder.
     * Remarks:  It is defined as
     * {@code t1 - (t1 /u t2) * t2}, where {@code /u} represents
     * unsigned division. If {@code t2} is zero, then the result is
     * undefined. The arguments must have the same bit-vector sort. 
     **/
    public BitVecExpr mkBVURem(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvurem(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Signed remainder.
     * Remarks:  It is defined as
     * {@code t1 - (t1 /s t2) * t2}, where {@code /s} represents
     * signed division. The most significant bit (sign) of the result is equal
     * to the most significant bit of \c t1.
     * 
     * If {@code t2} is zero, then the result is undefined. The arguments
     * must have the same bit-vector sort. 
     **/
    public BitVecExpr mkBVSRem(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsrem(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Two's complement signed remainder (sign follows divisor).
     * Remarks:  If
     * {@code t2} is zero, then the result is undefined. The arguments must
     * have the same bit-vector sort. 
     **/
    public BitVecExpr mkBVSMod(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvsmod(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Unsigned less-than
     * Remarks:  The arguments must have the same bit-vector
     * sort. 
     **/
    public BoolExpr mkBVULT(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvult(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed less-than
     * Remarks:  The arguments must have the
     * same bit-vector sort. 
     **/
    public BoolExpr mkBVSLT(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvslt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Unsigned less-than or equal to.
     * Remarks:  The arguments must have the
     * same bit-vector sort. 
     **/
    public BoolExpr mkBVULE(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvule(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed less-than or equal to.
     * Remarks:  The arguments
     * must have the same bit-vector sort. 
     **/
    public BoolExpr mkBVSLE(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsle(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Unsigned greater than or equal to.
     * Remarks:  The arguments must have the
     * same bit-vector sort. 
     **/
    public BoolExpr mkBVUGE(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvuge(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed greater than or equal to.
     * Remarks:  The arguments
     * must have the same bit-vector sort. 
     **/
    public BoolExpr mkBVSGE(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsge(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Unsigned greater-than.
     * Remarks:  The arguments must have the same
     * bit-vector sort. 
     **/
    public BoolExpr mkBVUGT(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvugt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Two's complement signed greater-than.
     * Remarks:  The arguments must have
     * the same bit-vector sort. 
     **/
    public BoolExpr mkBVSGT(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsgt(nCtx(), t1.getNativeObject(),
                t2.getNativeObject()));
    }

    /**
     * Bit-vector concatenation.
     * Remarks:  The arguments must have a bit-vector
     * sort. 
     * 
     * @return The result is a bit-vector of size {@code n1+n2}, where
     *         {@code n1} ({@code n2}) is the size of {@code t1}
     *         ({@code t2}).
     * 
     **/
    public BitVecExpr mkConcat(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkConcat(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Bit-vector extraction.
     * Remarks:  Extract the bits {@code high}
     * down to {@code low} from a bitvector of size {@code m} to
     * yield a new bitvector of size {@code n}, where
     * {@code n = high - low + 1}. The argument {@code t} must
     * have a bit-vector sort. 
     **/
    public BitVecExpr mkExtract(int high, int low, BitVecExpr t)
           
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkExtract(nCtx(), high, low,
                t.getNativeObject()));
    }

    /**
     * Bit-vector sign extension.
     * Remarks:  Sign-extends the given bit-vector to
     * the (signed) equivalent bitvector of size {@code m+i}, where \c m is
     * the size of the given bit-vector. The argument {@code t} must
     * have a bit-vector sort. 
     **/
    public BitVecExpr mkSignExt(int i, BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkSignExt(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Bit-vector zero extension.
     * Remarks:  Extend the given bit-vector with
     * zeros to the (unsigned) equivalent bitvector of size {@code m+i},
     * where \c m is the size of the given bit-vector. The argument {@code t}
     * must have a bit-vector sort. 
     **/
    public BitVecExpr mkZeroExt(int i, BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkZeroExt(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Bit-vector repetition.
     * Remarks:  The argument {@code t} must
     * have a bit-vector sort. 
     **/
    public BitVecExpr mkRepeat(int i, BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkRepeat(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Shift left.
     * Remarks:  It is equivalent to multiplication by
     * {@code 2^x} where \c x is the value of {@code t2}.
     * 
     * NB. The semantics of shift operations varies between environments. This
     * definition does not necessarily capture directly the semantics of the
     * programming language or assembly architecture you are modeling.
     * 
     * The arguments must have a bit-vector sort. 
     **/
    public BitVecExpr mkBVSHL(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvshl(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Logical shift right
     * Remarks:  It is equivalent to unsigned division by
     * {@code 2^x} where \c x is the value of {@code t2}.
     * 
     * NB. The semantics of shift operations varies between environments. This
     * definition does not necessarily capture directly the semantics of the
     * programming language or assembly architecture you are modeling.
     * 
     * The arguments must have a bit-vector sort. 
     **/
    public BitVecExpr mkBVLSHR(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvlshr(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Arithmetic shift right
     * Remarks:  It is like logical shift right except
     * that the most significant bits of the result always copy the most
     * significant bit of the second argument.
     * 
     * NB. The semantics of shift operations varies between environments. This
     * definition does not necessarily capture directly the semantics of the
     * programming language or assembly architecture you are modeling.
     * 
     * The arguments must have a bit-vector sort. 
     **/
    public BitVecExpr mkBVASHR(BitVecExpr t1, BitVecExpr t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkBvashr(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Rotate Left.
     * Remarks:  Rotate bits of \c t to the left \c i times. The
     * argument {@code t} must have a bit-vector sort. 
     **/
    public BitVecExpr mkBVRotateLeft(int i, BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkRotateLeft(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Rotate Right.
     * Remarks:  Rotate bits of \c t to the right \c i times. The
     * argument {@code t} must have a bit-vector sort. 
     **/
    public BitVecExpr mkBVRotateRight(int i, BitVecExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkRotateRight(nCtx(), i,
                t.getNativeObject()));
    }

    /**
     * Rotate Left.
     * Remarks:  Rotate bits of {@code t1} to the left
     * {@code t2} times. The arguments must have the same bit-vector
     * sort. 
     **/
    public BitVecExpr mkBVRotateLeft(BitVecExpr t1, BitVecExpr t2)
           
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkExtRotateLeft(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Rotate Right.
     * Remarks:  Rotate bits of {@code t1} to the
     * right{@code t2} times. The arguments must have the same
     * bit-vector sort. 
     **/
    public BitVecExpr mkBVRotateRight(BitVecExpr t1, BitVecExpr t2)
           
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BitVecExpr(this, Native.mkExtRotateRight(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create an {@code n} bit bit-vector from the integer argument
     * {@code t}.
     * Remarks:  NB. This function is essentially treated
     * as uninterpreted. So you cannot expect Z3 to precisely reflect the
     * semantics of this function when solving constraints with this function.
     * 
     * The argument must be of integer sort. 
     **/
    public BitVecExpr mkInt2BV(int n, IntExpr t)
    {
        checkContextMatch(t);
        return new BitVecExpr(this, Native.mkInt2bv(nCtx(), n,
                t.getNativeObject()));
    }

    /**
     * Create an integer from the bit-vector argument {@code t}.
     * Remarks:  If \c is_signed is false, then the bit-vector \c t1 is treated
     * as unsigned. So the result is non-negative and in the range
     * {@code [0..2^N-1]}, where N are the number of bits in {@code t}. 
     * If \c is_signed is true, \c t1 is treated as a signed
     * bit-vector.
     * 
     * NB. This function is essentially treated as uninterpreted. So you cannot
     * expect Z3 to precisely reflect the semantics of this function when
     * solving constraints with this function.
     * 
     * The argument must be of bit-vector sort. 
     **/
    public IntExpr mkBV2Int(BitVecExpr t, boolean signed)
    {
        checkContextMatch(t);
        return new IntExpr(this, Native.mkBv2int(nCtx(), t.getNativeObject(),
                (signed) ? true : false));
    }

    /**
     * Create a predicate that checks that the bit-wise addition does not
     * overflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVAddNoOverflow(BitVecExpr t1, BitVecExpr t2,
            boolean isSigned)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvaddNoOverflow(nCtx(), t1
                .getNativeObject(), t2.getNativeObject(), (isSigned) ? true
                : false));
    }

    /**
     * Create a predicate that checks that the bit-wise addition does not
     * underflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVAddNoUnderflow(BitVecExpr t1, BitVecExpr t2)
           
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvaddNoUnderflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise subtraction does not
     * overflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVSubNoOverflow(BitVecExpr t1, BitVecExpr t2)
           
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsubNoOverflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise subtraction does not
     * underflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVSubNoUnderflow(BitVecExpr t1, BitVecExpr t2,
            boolean isSigned)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsubNoUnderflow(nCtx(), t1
                .getNativeObject(), t2.getNativeObject(), (isSigned) ? true
                : false));
    }

    /**
     * Create a predicate that checks that the bit-wise signed division does not
     * overflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVSDivNoOverflow(BitVecExpr t1, BitVecExpr t2)
           
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvsdivNoOverflow(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise negation does not
     * overflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVNegNoOverflow(BitVecExpr t)
    {
        checkContextMatch(t);
        return new BoolExpr(this, Native.mkBvnegNoOverflow(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Create a predicate that checks that the bit-wise multiplication does not
     * overflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVMulNoOverflow(BitVecExpr t1, BitVecExpr t2,
            boolean isSigned)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new BoolExpr(this, Native.mkBvmulNoOverflow(nCtx(), t1
                .getNativeObject(), t2.getNativeObject(), (isSigned) ? true
                : false));
    }

    /**
     * Create a predicate that checks that the bit-wise multiplication does not
     * underflow. 
     * Remarks:  The arguments must be of bit-vector sort. 
     **/
    public BoolExpr mkBVMulNoUnderflow(BitVecExpr t1, BitVecExpr t2)
           
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
           
    {
        return (ArrayExpr) mkConst(name, mkArraySort(domain, range));
    }

    /**
     * Create an array constant.
     **/
    public ArrayExpr mkArrayConst(String name, Sort domain, Sort range)
           
    {
        return (ArrayExpr) mkConst(mkSymbol(name), mkArraySort(domain, range));
    }

    /**
     * Array read.
     * Remarks:  The argument {@code a} is the array and
     * {@code i} is the index of the array that gets read.
     * 
     * The node {@code a} must have an array sort
     * {@code [domain -> range]}, and {@code i} must have the sort
     * {@code domain}. The sort of the result is {@code range}.
     * 
     * @see mkArraySort
     * @see mkStore

     **/
    public Expr mkSelect(ArrayExpr a, Expr i)
    {
        checkContextMatch(a);
        checkContextMatch(i);
        return Expr.create(
                this,
                Native.mkSelect(nCtx(), a.getNativeObject(),
                        i.getNativeObject()));
    }

    /**
     * Array update.
     * Remarks:  The node {@code a} must have an array sort
     * {@code [domain -> range]}, {@code i} must have sort
     * {@code domain}, {@code v} must have sort range. The sort of the
     * result is {@code [domain -> range]}. The semantics of this function
     * is given by the theory of arrays described in the SMT-LIB standard. See
     * http://smtlib.org for more details. The result of this function is an
     * array that is equal to {@code a} (with respect to
     * {@code select}) on all indices except for {@code i}, where it
     * maps to {@code v} (and the {@code select} of {@code a}
     * with respect to {@code i} may be a different value). 
     * @see mkArraySort 
     * @see mkSelect

     **/
    public ArrayExpr mkStore(ArrayExpr a, Expr i, Expr v)
    {
        checkContextMatch(a);
        checkContextMatch(i);
        checkContextMatch(v);
        return new ArrayExpr(this, Native.mkStore(nCtx(), a.getNativeObject(),
                i.getNativeObject(), v.getNativeObject()));
    }

    /**
     * Create a constant array.
     * Remarks:  The resulting term is an array, such
     * that a {@code select} on an arbitrary index produces the value
     * {@code v}. 
     * @see mkArraySort
     * @see mkSelect
     * 
     **/
    public ArrayExpr mkConstArray(Sort domain, Expr v)
    {
        checkContextMatch(domain);
        checkContextMatch(v);
        return new ArrayExpr(this, Native.mkConstArray(nCtx(),
                domain.getNativeObject(), v.getNativeObject()));
    }

    /**
     * Maps f on the argument arrays.
     * Remarks:  Eeach element of
     * {@code args} must be of an array sort
     * {@code [domain_i -> range_i]}. The function declaration
     * {@code f} must have type {@code  range_1 .. range_n -> range}.
     * {@code v} must have sort range. The sort of the result is
     * {@code [domain_i -> range]}. 
     * @see mkArraySort
     * @see mkSelect 
     * @see mkStore

     **/
    public ArrayExpr mkMap(FuncDecl f, ArrayExpr... args)
    {
        checkContextMatch(f);
        checkContextMatch(args);
        return (ArrayExpr) Expr.create(this, Native.mkMap(nCtx(),
                f.getNativeObject(), AST.arrayLength(args),
                AST.arrayToNative(args)));
    }

    /**
     * Access the array default value.
     * Remarks:  Produces the default range
     * value, for arrays that can be represented as finite maps with a default
     * range value. 
     **/
    public Expr mkTermArray(ArrayExpr array)
    {
        checkContextMatch(array);
        return Expr.create(this,
                Native.mkArrayDefault(nCtx(), array.getNativeObject()));
    }

    /**
     * Create a set type.
     **/
    public SetSort mkSetSort(Sort ty)
    {
        checkContextMatch(ty);
        return new SetSort(this, ty);
    }

    /**
     * Create an empty set.
     **/
    public Expr mkEmptySet(Sort domain)
    {
        checkContextMatch(domain);
        return Expr.create(this,
                Native.mkEmptySet(nCtx(), domain.getNativeObject()));
    }

    /**
     * Create the full set.
     **/
    public Expr mkFullSet(Sort domain)
    {
        checkContextMatch(domain);
        return Expr.create(this,
                Native.mkFullSet(nCtx(), domain.getNativeObject()));
    }

    /**
     * Add an element to the set.
     **/
    public Expr mkSetAdd(Expr set, Expr element)
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
    public Expr mkSetDel(Expr set, Expr element)
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
    public Expr mkSetUnion(Expr... args)
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
    public Expr mkSetIntersection(Expr... args)
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
    public Expr mkSetDifference(Expr arg1, Expr arg2)
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
    public Expr mkSetComplement(Expr arg)
    {
        checkContextMatch(arg);
        return Expr.create(this,
                Native.mkSetComplement(nCtx(), arg.getNativeObject()));
    }

    /**
     * Check for set membership.
     **/
    public BoolExpr mkSetMembership(Expr elem, Expr set)
    {
        checkContextMatch(elem);
        checkContextMatch(set);
        return (BoolExpr) Expr.create(
                this,
                Native.mkSetMember(nCtx(), elem.getNativeObject(),
                        set.getNativeObject()));
    }

    /**
     * Check for subsetness of sets.
     **/
    public BoolExpr mkSetSubset(Expr arg1, Expr arg2)
    {
        checkContextMatch(arg1);
        checkContextMatch(arg2);
        return (BoolExpr) Expr.create(
                this,
                Native.mkSetSubset(nCtx(), arg1.getNativeObject(),
                        arg2.getNativeObject()));
    }

    /**
     * Create a Term of a given sort. 
     * @param v A string representing the term value in decimal notation. If the given sort is a real, then the
     * Term can be a rational, that is, a string of the form
     * {@code [num]* / [num]*}.
     * @param ty The sort of the
     * numeral. In the current implementation, the given sort can be an int,
     * real, or bit-vectors of arbitrary size.
     * 
     * @return A Term with value {@code v} and sort {@code ty}
     **/
    public Expr mkNumeral(String v, Sort ty)
    {
        checkContextMatch(ty);
        return Expr.create(this,
                Native.mkNumeral(nCtx(), v, ty.getNativeObject()));
    }

    /**
     * Create a Term of a given sort. This function can be use to create
     * numerals that fit in a machine integer. It is slightly faster than
     * {@code MakeNumeral} since it is not necessary to parse a string.
     * 
     * @param v Value of the numeral 
     * @param ty Sort of the numeral
     * 
     * @return A Term with value {@code v} and type {@code ty}
     **/
    public Expr mkNumeral(int v, Sort ty)
    {
        checkContextMatch(ty);
        return Expr.create(this, Native.mkInt(nCtx(), v, ty.getNativeObject()));
    }

    /**
     * Create a Term of a given sort. This function can be use to create
     * numerals that fit in a machine integer. It is slightly faster than
     * {@code MakeNumeral} since it is not necessary to parse a string.
     * 
     * @param v Value of the numeral 
     * @param ty Sort of the numeral
     * 
     * @return A Term with value {@code v} and type {@code ty}
     **/
    public Expr mkNumeral(long v, Sort ty)
    {
        checkContextMatch(ty);
        return Expr.create(this,
                Native.mkInt64(nCtx(), v, ty.getNativeObject()));
    }

    /**
     * Create a real from a fraction. 
     * @param num numerator of rational. 
     * @param den denominator of rational.
     * 
     * @return A Term with value {@code num}/{@code den}
     *         and sort Real 
     * @see mkNumeral(String,Sort)
     **/
    public RatNum mkReal(int num, int den)
    {
        if (den == 0)
            throw new Z3Exception("Denominator is zero");

        return new RatNum(this, Native.mkReal(nCtx(), num, den));
    }

    /**
     * Create a real numeral. 
     * @param v A string representing the Term value in decimal notation.
     * 
     * @return A Term with value {@code v} and sort Real
     **/
    public RatNum mkReal(String v)
    {

        return new RatNum(this, Native.mkNumeral(nCtx(), v, getRealSort()
                .getNativeObject()));
    }

    /**
     * Create a real numeral. 
     * @param v value of the numeral.
     * 
     * @return A Term with value {@code v} and sort Real
     **/
    public RatNum mkReal(int v)
    {

        return new RatNum(this, Native.mkInt(nCtx(), v, getRealSort()
                .getNativeObject()));
    }

    /**
     * Create a real numeral. 
     * @param v value of the numeral.
     * 
     * @return A Term with value {@code v} and sort Real
     **/
    public RatNum mkReal(long v)
    {

        return new RatNum(this, Native.mkInt64(nCtx(), v, getRealSort()
                .getNativeObject()));
    }

    /**
     * Create an integer numeral. 
     * @param v A string representing the Term value in decimal notation.
     **/
    public IntNum mkInt(String v)
    {

        return new IntNum(this, Native.mkNumeral(nCtx(), v, getIntSort()
                .getNativeObject()));
    }

    /**
     * Create an integer numeral. 
     * @param v value of the numeral.
     * 
     * @return A Term with value {@code v} and sort Integer
     **/
    public IntNum mkInt(int v)
    {

        return new IntNum(this, Native.mkInt(nCtx(), v, getIntSort()
                .getNativeObject()));
    }

    /**
     * Create an integer numeral. 
     * @param v value of the numeral.
     * 
     * @return A Term with value {@code v} and sort Integer
     **/
    public IntNum mkInt(long v)
    {

        return new IntNum(this, Native.mkInt64(nCtx(), v, getIntSort()
                .getNativeObject()));
    }

    /**
     * Create a bit-vector numeral. 
     * @param v A string representing the value in decimal notation. 
     * @param size the size of the bit-vector
     **/
    public BitVecNum mkBV(String v, int size)
    {
        return (BitVecNum) mkNumeral(v, mkBitVecSort(size));
    }

    /**
     * Create a bit-vector numeral. 
     * @param v value of the numeral. 
     * @param size the size of the bit-vector
     **/
    public BitVecNum mkBV(int v, int size)
    {
        return (BitVecNum) mkNumeral(v, mkBitVecSort(size));
    }

    /**
     * Create a bit-vector numeral. 
     * @param v value of the numeral. * 
     * @param size the size of the bit-vector
     **/
    public BitVecNum mkBV(long v, int size)
    {
        return (BitVecNum) mkNumeral(v, mkBitVecSort(size));
    }

    /**
     * Create a universal Quantifier.
     * @param sorts the sorts of the bound variables. 
     * @param names names of the bound variables 
     * @param body the body of the quantifier. 
     * @param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
     * @param patterns array containing the patterns created using {@code MkPattern}. 
     * @param noPatterns array containing the anti-patterns created using {@code MkPattern}. 
     * @param quantifierID optional symbol to track quantifier. 
     * @param skolemID optional symbol to track skolem constants.
     * 
     * Remarks:  Creates a forall formula, where
     * {@code weight"/> is the weight, <paramref name="patterns} is
     * an array of patterns, {@code sorts} is an array with the sorts
     * of the bound variables, {@code names} is an array with the
     * 'names' of the bound variables, and {@code body} is the body
     * of the quantifier. Quantifiers are associated with weights indicating the
     * importance of using the quantifier during instantiation.
     **/
    public Quantifier mkForall(Sort[] sorts, Symbol[] names, Expr body,
            int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID)
    {

        return new Quantifier(this, true, sorts, names, body, weight, patterns,
                noPatterns, quantifierID, skolemID);
    }

    /**
     * Create a universal Quantifier.
     **/
    public Quantifier mkForall(Expr[] boundConstants, Expr body, int weight,
            Pattern[] patterns, Expr[] noPatterns, Symbol quantifierID,
            Symbol skolemID)
    {

        return new Quantifier(this, true, boundConstants, body, weight,
                patterns, noPatterns, quantifierID, skolemID);
    }

    /**
     * Create an existential Quantifier. 
     * @see mkForall(Sort[],Symbol[],Expr,int,Pattern[],Expr[],Symbol,Symbol)
     **/
    public Quantifier mkExists(Sort[] sorts, Symbol[] names, Expr body,
            int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID)
    {

        return new Quantifier(this, false, sorts, names, body, weight,
                patterns, noPatterns, quantifierID, skolemID);
    }

    /**
     * Create an existential Quantifier.
     **/
    public Quantifier mkExists(Expr[] boundConstants, Expr body, int weight,
            Pattern[] patterns, Expr[] noPatterns, Symbol quantifierID,
            Symbol skolemID)
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
            Symbol quantifierID, Symbol skolemID)
    {

        if (universal)
            return mkForall(boundConstants, body, weight, patterns, noPatterns,
                    quantifierID, skolemID);
        else
            return mkExists(boundConstants, body, weight, patterns, noPatterns,
                    quantifierID, skolemID);
    }

    /**
     * Selects the format used for pretty-printing expressions.
     * Remarks:  The
     * default mode for pretty printing expressions is to produce SMT-LIB style
     * output where common subexpressions are printed at each occurrence. The
     * mode is called Z3_PRINT_SMTLIB_FULL. To print shared common
     * subexpressions only once, use the Z3_PRINT_LOW_LEVEL mode. To print in
     * way that conforms to SMT-LIB standards and uses let expressions to share
     * common sub-expressions use Z3_PRINT_SMTLIB_COMPLIANT.  
     * @see AST#toString
     * @see Pattern#toString
     * @see FuncDecl#toString
     * @see Sort#toString
     **/
    public void setPrintMode(Z3_ast_print_mode value)
    {
        Native.setAstPrintMode(nCtx(), value.toInt());
    }

    /**
     * Convert a benchmark into an SMT-LIB formatted string. 
     * @param name Name of the benchmark. The argument is optional.
     * 
     * @param logic The benchmark logic.  
     * @param status The status string (sat, unsat, or unknown) 
     * @param attributes Other attributes, such as source, difficulty or
     * category.
     * @param assumptions Auxiliary assumptions. 
     * @param formula Formula to be checked for consistency in conjunction with assumptions.
     * 
     * @return A string representation of the benchmark.
     **/
    public String benchmarkToSMTString(String name, String logic,
            String status, String attributes, BoolExpr[] assumptions,
            BoolExpr formula)
    {

        return Native.benchmarkToSmtlibString(nCtx(), name, logic, status,
                attributes, (int) assumptions.length,
                AST.arrayToNative(assumptions), formula.getNativeObject());
    }

    /**
     * Parse the given string using the SMT-LIB parser.
     * Remarks:  The symbol
     * table of the parser can be initialized using the given sorts and
     * declarations. The symbols in the arrays {@code sortNames} and
     * {@code declNames} don't need to match the names of the sorts
     * and declarations in the arrays {@code sorts} and {@code decls}. This is a useful feature since we can use arbitrary names
     * to reference sorts and declarations. 
     **/
    public void parseSMTLIBString(String str, Symbol[] sortNames, Sort[] sorts,
            Symbol[] declNames, FuncDecl[] decls)
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
     * Parse the given file using the SMT-LIB parser. 
     * @see parseSMTLIBString
     **/
    public void parseSMTLIBFile(String fileName, Symbol[] sortNames,
            Sort[] sorts, Symbol[] declNames, FuncDecl[] decls)
           
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
     * {@code ParseSMTLIBString} or {@code ParseSMTLIBFile}.
     **/
    public int getNumSMTLIBFormulas()
    {
        return Native.getSmtlibNumFormulas(nCtx());
    }

    /**
     * The formulas parsed by the last call to {@code ParseSMTLIBString} or
     * {@code ParseSMTLIBFile}.
     **/
    public BoolExpr[] getSMTLIBFormulas()
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
     * {@code ParseSMTLIBString} or {@code ParseSMTLIBFile}.
     **/
    public int getNumSMTLIBAssumptions()
    {
        return Native.getSmtlibNumAssumptions(nCtx());
    }

    /**
     * The assumptions parsed by the last call to {@code ParseSMTLIBString}
     * or {@code ParseSMTLIBFile}.
     **/
    public BoolExpr[] getSMTLIBAssumptions()
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
     * {@code ParseSMTLIBString} or {@code ParseSMTLIBFile}.
     **/
    public int getNumSMTLIBDecls()
    {
        return Native.getSmtlibNumDecls(nCtx());
    }

    /**
     * The declarations parsed by the last call to
     * {@code ParseSMTLIBString} or {@code ParseSMTLIBFile}.
     **/
    public FuncDecl[] getSMTLIBDecls()
    {

        int n = getNumSMTLIBDecls();
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl(this, Native.getSmtlibDecl(nCtx(), i));
        return res;
    }

    /**
     * The number of SMTLIB sorts parsed by the last call to
     * {@code ParseSMTLIBString} or {@code ParseSMTLIBFile}.
     **/
    public int getNumSMTLIBSorts()
    {
        return Native.getSmtlibNumSorts(nCtx());
    }

    /**
     * The declarations parsed by the last call to
     * {@code ParseSMTLIBString} or {@code ParseSMTLIBFile}.
     **/
    public Sort[] getSMTLIBSorts()
    {

        int n = getNumSMTLIBSorts();
        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.create(this, Native.getSmtlibSort(nCtx(), i));
        return res;
    }

    /**
     * Parse the given string using the SMT-LIB2 parser. 
     * @see parseSMTLIBString
     * 
     * @return A conjunction of assertions in the scope (up to push/pop) at the
     *         end of the string.
     **/
    public BoolExpr parseSMTLIB2String(String str, Symbol[] sortNames,
            Sort[] sorts, Symbol[] declNames, FuncDecl[] decls)
           
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
     * Parse the given file using the SMT-LIB2 parser. 
     * @see parseSMTLIB2String
     **/
    public BoolExpr parseSMTLIB2File(String fileName, Symbol[] sortNames,
            Sort[] sorts, Symbol[] declNames, FuncDecl[] decls)
           
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
     * Creates a new Goal.
     * Remarks:  Note that the Context must have been
     * created with proof generation support if {@code proofs} is set
     * to true here.  
     * @param models Indicates whether model generation should be enabled. 
     * @param unsatCores Indicates whether unsat core generation should be enabled. 
     * @param proofs Indicates whether proof generation should be
     * enabled.
     **/
    public Goal mkGoal(boolean models, boolean unsatCores, boolean proofs)
           
    {
        return new Goal(this, models, unsatCores, proofs);
    }

    /**
     * Creates a new ParameterSet.
     **/
    public Params mkParams()
    {
        return new Params(this);
    }

    /**
     * The number of supported tactics.
     **/
    public int getNumTactics()
    {
        return Native.getNumTactics(nCtx());
    }

    /**
     * The names of all supported tactics.
     **/
    public String[] getTacticNames()
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
    public String getTacticDescription(String name)
    {
        return Native.tacticGetDescr(nCtx(), name);
    }

    /**
     * Creates a new Tactic.
     **/
    public Tactic mkTactic(String name)
    {
        return new Tactic(this, name);
    }

    /**
     * Create a tactic that applies {@code t1} to a Goal and then
     * {@code t2"/> to every subgoal produced by <paramref name="t1}.
     **/
    public Tactic andThen(Tactic t1, Tactic t2, Tactic... ts)
           
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
     * Create a tactic that applies {@code t1} to a Goal and then
     * {@code t2"/> to every subgoal produced by <paramref name="t1}.
     * 
     * Remarks:  Shorthand for {@code AndThen}. 
     **/
    public Tactic then(Tactic t1, Tactic t2, Tactic... ts)
    {
        return andThen(t1, t2, ts);
    }

    /**
     * Create a tactic that first applies {@code t1} to a Goal and if
     * it fails then returns the result of {@code t2} applied to the
     * Goal.
     **/
    public Tactic orElse(Tactic t1, Tactic t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new Tactic(this, Native.tacticOrElse(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a tactic that applies {@code t} to a goal for {@code ms} milliseconds.
     * Remarks:  If {@code t} does not
     * terminate within {@code ms} milliseconds, then it fails.
     * 
     **/
    public Tactic tryFor(Tactic t, int ms)
    {
        checkContextMatch(t);
        return new Tactic(this, Native.tacticTryFor(nCtx(),
                t.getNativeObject(), ms));
    }

    /**
     * Create a tactic that applies {@code t} to a given goal if the
     * probe {@code p} evaluates to true.
     * Remarks:  If {@code p} evaluates to false, then the new tactic behaves like the
     * {@code skip} tactic. 
     **/
    public Tactic when(Probe p, Tactic t)
    {
        checkContextMatch(t);
        checkContextMatch(p);
        return new Tactic(this, Native.tacticWhen(nCtx(), p.getNativeObject(),
                t.getNativeObject()));
    }

    /**
     * Create a tactic that applies {@code t1} to a given goal if the
     * probe {@code p"/> evaluates to true and <paramref name="t2}
     * otherwise.
     **/
    public Tactic cond(Probe p, Tactic t1, Tactic t2)
    {
        checkContextMatch(p);
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new Tactic(this, Native.tacticCond(nCtx(), p.getNativeObject(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Create a tactic that keeps applying {@code t} until the goal
     * is not modified anymore or the maximum number of iterations {@code max} is reached.
     **/
    public Tactic repeat(Tactic t, int max)
    {
        checkContextMatch(t);
        return new Tactic(this, Native.tacticRepeat(nCtx(),
                t.getNativeObject(), max));
    }

    /**
     * Create a tactic that just returns the given goal.
     **/
    public Tactic skip()
    {
        return new Tactic(this, Native.tacticSkip(nCtx()));
    }

    /**
     * Create a tactic always fails.
     **/
    public Tactic fail()
    {
        return new Tactic(this, Native.tacticFail(nCtx()));
    }

    /**
     * Create a tactic that fails if the probe {@code p} evaluates to
     * false.
     **/
    public Tactic failIf(Probe p)
    {
        checkContextMatch(p);
        return new Tactic(this,
                Native.tacticFailIf(nCtx(), p.getNativeObject()));
    }

    /**
     * Create a tactic that fails if the goal is not triviall satisfiable (i.e.,
     * empty) or trivially unsatisfiable (i.e., contains `false').
     **/
    public Tactic failIfNotDecided()
    {
        return new Tactic(this, Native.tacticFailIfNotDecided(nCtx()));
    }

    /**
     * Create a tactic that applies {@code t} using the given set of
     * parameters {@code p}.
     **/
    public Tactic usingParams(Tactic t, Params p)
    {
        checkContextMatch(t);
        checkContextMatch(p);
        return new Tactic(this, Native.tacticUsingParams(nCtx(),
                t.getNativeObject(), p.getNativeObject()));
    }

    /**
     * Create a tactic that applies {@code t} using the given set of
     * parameters {@code p}.
     * Remarks: Alias for
     * {@code UsingParams}
     **/
    public Tactic with(Tactic t, Params p)
    {
        return usingParams(t, p);
    }

    /**
     * Create a tactic that applies the given tactics in parallel.
     **/
    public Tactic parOr(Tactic... t)
    {
        checkContextMatch(t);
        return new Tactic(this, Native.tacticParOr(nCtx(),
                Tactic.arrayLength(t), Tactic.arrayToNative(t)));
    }

    /**
     * Create a tactic that applies {@code t1} to a given goal and
     * then {@code t2} to every subgoal produced by {@code t1}. The subgoals are processed in parallel.
     **/
    public Tactic parAndThen(Tactic t1, Tactic t2)
    {
        checkContextMatch(t1);
        checkContextMatch(t2);
        return new Tactic(this, Native.tacticParAndThen(nCtx(),
                t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Interrupt the execution of a Z3 procedure.
     * Remarks: This procedure can be
     * used to interrupt: solvers, simplifiers and tactics.
     **/
    public void interrupt()
    {
        Native.interrupt(nCtx());
    }

    /**
     * The number of supported Probes.
     **/
    public int getNumProbes()
    {
        return Native.getNumProbes(nCtx());
    }

    /**
     * The names of all supported Probes.
     **/
    public String[] getProbeNames()
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
    public String getProbeDescription(String name)
    {
        return Native.probeGetDescr(nCtx(), name);
    }

    /**
     * Creates a new Probe.
     **/
    public Probe mkProbe(String name)
    {
        return new Probe(this, name);
    }

    /**
     * Create a probe that always evaluates to {@code val}.
     **/
    public Probe constProbe(double val)
    {
        return new Probe(this, Native.probeConst(nCtx(), val));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * {@code p1} is less than the value returned by {@code p2}
     **/
    public Probe lt(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeLt(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * {@code p1} is greater than the value returned by {@code p2}
     **/
    public Probe gt(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeGt(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * {@code p1} is less than or equal the value returned by
     * {@code p2}
     **/
    public Probe le(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeLe(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * {@code p1} is greater than or equal the value returned by
     * {@code p2}
     **/
    public Probe ge(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeGe(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value returned by
     * {@code p1} is equal to the value returned by {@code p2}
     **/
    public Probe eq(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeEq(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value {@code p1} and {@code p2} evaluate to "true".
     **/
    public Probe and(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeAnd(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value {@code p1} or {@code p2} evaluate to "true".
     **/
    public Probe or(Probe p1, Probe p2)
    {
        checkContextMatch(p1);
        checkContextMatch(p2);
        return new Probe(this, Native.probeOr(nCtx(), p1.getNativeObject(),
                p2.getNativeObject()));
    }

    /**
     * Create a probe that evaluates to "true" when the value {@code p} does not evaluate to "true".
     **/
    public Probe not(Probe p)
    {
        checkContextMatch(p);
        return new Probe(this, Native.probeNot(nCtx(), p.getNativeObject()));
    }

    /**
     * Creates a new (incremental) solver.
     * Remarks:  This solver also uses a set
     * of builtin tactics for handling the first check-sat command, and
     * check-sat commands that take more than a given number of milliseconds to
     * be solved. 
     **/
    public Solver mkSolver()
    {
        return mkSolver((Symbol) null);
    }

    /**
     * Creates a new (incremental) solver.
     * Remarks:  This solver also uses a set
     * of builtin tactics for handling the first check-sat command, and
     * check-sat commands that take more than a given number of milliseconds to
     * be solved. 
     **/
    public Solver mkSolver(Symbol logic)
    {

        if (logic == null)
            return new Solver(this, Native.mkSolver(nCtx()));
        else
            return new Solver(this, Native.mkSolverForLogic(nCtx(),
                    logic.getNativeObject()));
    }

    /**
     * Creates a new (incremental) solver. 
     * @see mkSolver(Symbol)
     **/
    public Solver mkSolver(String logic)
    {
        return mkSolver(mkSymbol(logic));
    }

    /**
     * Creates a new (incremental) solver.
     **/
    public Solver mkSimpleSolver()
    {
        return new Solver(this, Native.mkSimpleSolver(nCtx()));
    }

    /**
     * Creates a solver that is implemented using the given tactic.
     * Remarks: 
     * The solver supports the commands {@code Push} and {@code Pop},
     * but it will always solve each check from scratch. 
     **/
    public Solver mkSolver(Tactic t)
    {

        return new Solver(this, Native.mkSolverFromTactic(nCtx(),
                t.getNativeObject()));
    }

    /**
     * Create a Fixedpoint context.
     **/
    public Fixedpoint mkFixedpoint()
    {
        return new Fixedpoint(this);
    }

    
    /**
     * Create the floating-point RoundingMode sort.
     * @throws Z3Exception 
     **/    
    public FPRMSort mkFPRoundingModeSort()
    {
        return new FPRMSort(this);
    }

    /**
     * Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMExpr mkFPRoundNearestTiesToEven()
    {
        return new FPRMExpr(this, Native.mkFpaRoundNearestTiesToEven(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRNE()
    {
        return new FPRMNum(this, Native.mkFpaRne(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRoundNearestTiesToAway()
    {
        return new FPRMNum(this, Native.mkFpaRoundNearestTiesToAway(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRNA()
    {
        return new FPRMNum(this, Native.mkFpaRna(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the RoundTowardPositive rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRoundTowardPositive()
    {
        return new FPRMNum(this, Native.mkFpaRoundTowardPositive(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the RoundTowardPositive rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRTP()
    {
        return new FPRMNum(this, Native.mkFpaRtp(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the RoundTowardNegative rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRoundTowardNegative()
    {
        return new FPRMNum(this, Native.mkFpaRoundTowardNegative(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the RoundTowardNegative rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRTN()
    {
        return new FPRMNum(this, Native.mkFpaRtn(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the RoundTowardZero rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRoundTowardZero()
    {
        return new FPRMNum(this, Native.mkFpaRoundTowardZero(nCtx()));
    }

    /**
     * Create a numeral of RoundingMode sort which represents the RoundTowardZero rounding mode.
     * @throws Z3Exception 
     **/
    public FPRMNum mkFPRTZ()
    {
        return new FPRMNum(this, Native.mkFpaRtz(nCtx()));
    }        

    /**
     * Create a FloatingPoint sort.
     * @param ebits exponent bits in the FloatingPoint sort.
     * @param sbits significand bits in the FloatingPoint sort.
     * @throws Z3Exception 
     **/     
    public FPSort mkFPSort(int ebits, int sbits)
    {
        return new FPSort(this, ebits, sbits);
    }

    /**
     * Create the half-precision (16-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSortHalf()
    {
        return new FPSort(this, Native.mkFpaSortHalf(nCtx()));
    }

    /**
     * Create the half-precision (16-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSort16()
    {
        return new FPSort(this, Native.mkFpaSort16(nCtx()));
    }

    /**
     * Create the single-precision (32-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSortSingle()
    {
        return new FPSort(this, Native.mkFpaSortSingle(nCtx()));
    }

    /**
     * Create the single-precision (32-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSort32()
    {
        return new FPSort(this, Native.mkFpaSort32(nCtx()));
    }

    /**
     * Create the double-precision (64-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSortDouble()
    {
        return new FPSort(this, Native.mkFpaSortDouble(nCtx()));
    }

    /**
     * Create the double-precision (64-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSort64()
    {
        return new FPSort(this, Native.mkFpaSort64(nCtx()));
    }

    /**
     * Create the quadruple-precision (128-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSortQuadruple()
    {        
        return new FPSort(this, Native.mkFpaSortQuadruple(nCtx()));
    }

    /**
     * Create the quadruple-precision (128-bit) FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPSort mkFPSort128()
    {
        return new FPSort(this, Native.mkFpaSort128(nCtx()));
    }


    /**
     * Create a NaN of sort s.
     * @param s FloatingPoint sort.     
     * @throws Z3Exception 
     **/               
    public FPNum mkFPNaN(FPSort s)
    {
        return new FPNum(this, Native.mkFpaNan(nCtx(), s.getNativeObject()));
    }

    /**
     * Create a floating-point infinity of sort s.
     * @param s FloatingPoint sort.   
     * @param negative indicates whether the result should be negative.
     * @throws Z3Exception 
     **/             
    public FPNum mkFPInf(FPSort s, boolean negative)
    {
        return new FPNum(this, Native.mkFpaInf(nCtx(), s.getNativeObject(), negative));
    }

    /**
     * Create a floating-point zero of sort s.
     * @param s FloatingPoint sort.   
     * @param negative indicates whether the result should be negative.
     * @throws Z3Exception 
     **/             
    public FPNum mkFPZero(FPSort s, boolean negative)
    {
        return new FPNum(this, Native.mkFpaZero(nCtx(), s.getNativeObject(), negative));
    }

    /**
     * Create a numeral of FloatingPoint sort from a float.
     * @param v numeral value.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/        
    public FPNum mkFPNumeral(float v, FPSort s)
    {
        return new FPNum(this, Native.mkFpaNumeralFloat(nCtx(), v, s.getNativeObject()));
    }

    /**
     * Create a numeral of FloatingPoint sort from a float.
     * @param v numeral value.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/        
    public FPNum mkFPNumeral(double v, FPSort s)
    {
        return new FPNum(this, Native.mkFpaNumeralDouble(nCtx(), v, s.getNativeObject()));
    }

    /**
     * Create a numeral of FloatingPoint sort from an int.
     * * @param v numeral value.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/                    
    public FPNum mkFPNumeral(int v, FPSort s)
    {
        return new FPNum(this, Native.mkFpaNumeralInt(nCtx(), v, s.getNativeObject()));
    }

    /**
     * Create a numeral of FloatingPoint sort from a sign bit and two integers.
     * @param sgn the sign.
     * @param sig the significand.
     * @param exp the exponent.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/            
    public FPNum mkFPNumeral(boolean sgn, int exp, int sig, FPSort s)
    {
        return new FPNum(this, Native.mkFpaNumeralIntUint(nCtx(), sgn, exp, sig, s.getNativeObject()));    
    }

    /**
     * Create a numeral of FloatingPoint sort from a sign bit and two 64-bit integers.
     * @param sgn the sign.
     * @param sig the significand.
     * @param exp the exponent.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/
    public FPNum mkFPNumeral(boolean sgn, long exp, long sig, FPSort s)
    {
        return new FPNum(this, Native.mkFpaNumeralInt64Uint64(nCtx(), sgn, exp, sig, s.getNativeObject()));
    }

    /**
     * Create a numeral of FloatingPoint sort from a float.
     * @param v numeral value.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/        
    public FPNum mkFP(float v, FPSort s)
    {
        return mkFPNumeral(v, s);
    }

    /**
     * Create a numeral of FloatingPoint sort from a float.
     * @param v numeral value.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/             
    public FPNum mkFP(double v, FPSort s)
    {
        return mkFPNumeral(v, s);
    }

    /**
     * Create a numeral of FloatingPoint sort from an int.
     * @param v numeral value.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/        
            
    public FPNum mkFP(int v, FPSort s)
    {
        return mkFPNumeral(v, s);
    }

    /**
     * Create a numeral of FloatingPoint sort from a sign bit and two integers.
     * @param sgn the sign.        
     * @param exp the exponent.
     * @param sig the significand.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/                     
    public FPNum mkFP(boolean sgn, int exp, int sig, FPSort s)
    {
        return mkFPNumeral(sgn, sig, exp, s);
    }

    /**
     * Create a numeral of FloatingPoint sort from a sign bit and two 64-bit integers.
     * @param sgn the sign.        
     * @param exp the exponent.
     * @param sig the significand.
     * @param s FloatingPoint sort.
     * @throws Z3Exception 
     **/                     
    public FPNum mkFP(boolean sgn, long exp, long sig, FPSort s)
    {
        return mkFPNumeral(sgn, sig, exp, s);
    }


    /**
     * Floating-point absolute value
     * @param t floating-point term
     * @throws Z3Exception 
     **/     
    public FPExpr mkFPAbs(FPExpr t) 
    {
        return new FPExpr(this, Native.mkFpaAbs(nCtx(), t.getNativeObject()));
    }

    /**
     * Floating-point negation
     * @param t floating-point term
     * @throws Z3Exception 
     **/     
    public FPExpr mkFPNeg(FPExpr t) 
    {
        return new FPExpr(this, Native.mkFpaNeg(nCtx(), t.getNativeObject()));
    }

    /**
     * Floating-point addition
     * @param rm rounding mode term
     * @param t1 floating-point term
     * @param t2 floating-point term     
     * @throws Z3Exception 
     **/     
    public FPExpr mkFPAdd(FPRMExpr rm, FPExpr t1, FPExpr t2) 
    {
        return new FPExpr(this, Native.mkFpaAdd(nCtx(), rm.getNativeObject(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point subtraction
     * @param rm rounding mode term
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/     
    public FPExpr mkFPSub(FPRMExpr rm, FPExpr t1, FPExpr t2) 
    {
        return new FPExpr(this, Native.mkFpaSub(nCtx(), rm.getNativeObject(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point multiplication
     * @param rm rounding mode term
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/     
    public FPExpr mkFPMul(FPRMExpr rm, FPExpr t1, FPExpr t2) 
    {
        return new FPExpr(this, Native.mkFpaMul(nCtx(), rm.getNativeObject(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point division
     * @param rm rounding mode term
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/     
    public FPExpr mkFPDiv(FPRMExpr rm, FPExpr t1, FPExpr t2) 
    {
        return new FPExpr(this, Native.mkFpaDiv(nCtx(), rm.getNativeObject(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point fused multiply-add
     * @param rm rounding mode term
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @param t3 floating-point term
     * Remarks:
     * The result is round((t1 * t2) + t3)
     * @throws Z3Exception 
     **/
    public FPExpr mkFPFMA(FPRMExpr rm, FPExpr t1, FPExpr t2, FPExpr t3) 
    {
        return new FPExpr(this, Native.mkFpaFma(nCtx(), rm.getNativeObject(), t1.getNativeObject(), t2.getNativeObject(), t3.getNativeObject()));
    }

    /**
     * Floating-point square root
     * @param rm rounding mode term        
     * @param t floating-point term
     * @throws Z3Exception 
     **/        
    public FPExpr mkFPSqrt(FPRMExpr rm, FPExpr t) 
    {
        return new FPExpr(this, Native.mkFpaSqrt(nCtx(), rm.getNativeObject(), t.getNativeObject()));
    }

    /**
     * Floating-point remainder
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/             
    public FPExpr mkFPRem(FPExpr t1, FPExpr t2) 
    {
        return new FPExpr(this, Native.mkFpaRem(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point roundToIntegral. Rounds a floating-point number to 
     * the closest integer, again represented as a floating-point number.
     * @param rm term of RoundingMode sort
     * @param t floating-point term
     * @throws Z3Exception 
     **/             
    public FPExpr mkFPRoundToIntegral(FPRMExpr rm, FPExpr t)
    {            
        return new FPExpr(this, Native.mkFpaRoundToIntegral(nCtx(), rm.getNativeObject(), t.getNativeObject()));
    }

    /**
     * Minimum of floating-point numbers.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/
    public FPExpr mkFPMin(FPExpr t1, FPExpr t2)
    {
        return new FPExpr(this, Native.mkFpaMin(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Maximum of floating-point numbers.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/             
    public FPExpr mkFPMax(FPExpr t1, FPExpr t2)
    {
        return new FPExpr(this, Native.mkFpaMax(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }   
    
    /**
     * Floating-point less than or equal.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/             
    public BoolExpr mkFPLEq(FPExpr t1, FPExpr t2) 
    {            
        return new BoolExpr(this, Native.mkFpaLeq(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point less than.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/             
    public BoolExpr mkFPLt(FPExpr t1, FPExpr t2) 
    {                    
        return new BoolExpr(this, Native.mkFpaLt(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point greater than or equal.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/             
    public BoolExpr mkFPGEq(FPExpr t1, FPExpr t2) 
    {                    
        return new BoolExpr(this, Native.mkFpaGeq(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point greater than.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * @throws Z3Exception 
     **/             
    public BoolExpr mkFPGt(FPExpr t1, FPExpr t2) 
    {            
        return new BoolExpr(this, Native.mkFpaGt(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Floating-point equality.
     * @param t1 floating-point term
     * @param t2 floating-point term
     * Remarks:
     * Note that this is IEEE 754 equality (as opposed to standard =).
     * @throws Z3Exception 
     **/
    public BoolExpr mkFPEq(FPExpr t1, FPExpr t2)
    {
        return new BoolExpr(this, Native.mkFpaEq(nCtx(), t1.getNativeObject(), t2.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a normal floating-point number.\
     * @param t floating-point term
     * @throws Z3Exception 
     **/
    public BoolExpr mkFPIsNormal(FPExpr t) 
    {
        return new BoolExpr(this, Native.mkFpaIsNormal(nCtx(), t.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a subnormal floating-point number.\
     * @param t floating-point term
     * @throws Z3Exception 
     **/        
    public BoolExpr mkFPIsSubnormal(FPExpr t) 
    {                   
        return new BoolExpr(this, Native.mkFpaIsSubnormal(nCtx(), t.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a floating-point number with zero value, i.e., +0 or -0.
     * @param t floating-point term
     * @throws Z3Exception 
     **/        
    public BoolExpr mkFPIsZero(FPExpr t)
    {
        return new BoolExpr(this, Native.mkFpaIsZero(nCtx(), t.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a floating-point number representing +oo or -oo.
     * @param t floating-point term
     * @throws Z3Exception 
     **/        
    public BoolExpr mkFPIsInfinite(FPExpr t)
    {    
        return new BoolExpr(this, Native.mkFpaIsInfinite(nCtx(), t.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a NaN.
     * @param t floating-point term
     * @throws Z3Exception 
     **/             
    public BoolExpr mkFPIsNaN(FPExpr t) 
    {                   
        return new BoolExpr(this, Native.mkFpaIsNan(nCtx(), t.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a negative floating-point number.
     * @param t floating-point term
     * @throws Z3Exception 
     **/        
    public BoolExpr mkFPIsNegative(FPExpr t)
    {     
        return new BoolExpr(this, Native.mkFpaIsNegative(nCtx(), t.getNativeObject()));
    }

    /**
     * Predicate indicating whether t is a positive floating-point number.
     * @param t floating-point term
     * @throws Z3Exception 
     **/        
    public BoolExpr mkFPIsPositive(FPExpr t)
    {
        return new BoolExpr(this, Native.mkFpaIsPositive(nCtx(), t.getNativeObject()));
    }        

    /**
     * Create an expression of FloatingPoint sort from three bit-vector expressions.     
     * @param sgn bit-vector term (of size 1) representing the sign.
     * @param sig bit-vector term representing the significand.
     * @param exp bit-vector term representing the exponent.
     * Remarks:
     * This is the operator named `fp' in the SMT FP theory definition. 
     * Note that sgn is required to be a bit-vector of size 1. Significand and exponent 
     * are required to be greater than 1 and 2 respectively. The FloatingPoint sort 
     * of the resulting expression is automatically determined from the bit-vector sizes
     * of the arguments.
     * @throws Z3Exception 
     **/
    public FPExpr mkFP(BitVecExpr sgn, BitVecExpr sig, BitVecExpr exp)
    {
        return new FPExpr(this, Native.mkFpaFp(nCtx(), sgn.getNativeObject(), sig.getNativeObject(), exp.getNativeObject()));
    }

    /**
     * Conversion of a single IEEE 754-2008 bit-vector into a floating-point number.
     * @param bv bit-vector value (of size m).
     * @param s FloatingPoint sort (ebits+sbits == m)
     * Remarks:
     * Produces a term that represents the conversion of a bit-vector term bv to a 
     * floating-point term of sort s. The bit-vector size of bv (m) must be equal 
     * to ebits+sbits of s. The format of the bit-vector is as defined by the 
     * IEEE 754-2008 interchange format.
     * @throws Z3Exception 
     **/
    public FPExpr mkFPToFP(BitVecExpr bv, FPSort s)
    {
        return new FPExpr(this, Native.mkFpaToFpBv(nCtx(), bv.getNativeObject(), s.getNativeObject()));
    }

    /**
     * Conversion of a FloatingPoint term into another term of different FloatingPoint sort.
     * @param rm RoundingMode term.
     * @param t FloatingPoint term.
     * @param s FloatingPoint sort.
     * Remarks:
     * Produces a term that represents the conversion of a floating-point term t to a
     * floating-point term of sort s. If necessary, the result will be rounded according
     * to rounding mode rm.
     * @throws Z3Exception 
     **/
    public FPExpr mkFPToFP(FPRMExpr rm, FPExpr t, FPSort s)
    {
        return new FPExpr(this, Native.mkFpaToFpFloat(nCtx(), rm.getNativeObject(), t.getNativeObject(), s.getNativeObject()));
    }

    /**
     * Conversion of a term of real sort into a term of FloatingPoint sort.
     * @param rm RoundingMode term.
     * @param t term of Real sort.
     * @param s FloatingPoint sort.
     * Remarks:
     * Produces a term that represents the conversion of term t of real sort into a
     * floating-point term of sort s. If necessary, the result will be rounded according
     * to rounding mode rm.
     * @throws Z3Exception 
     **/
    public FPExpr mkFPToFP(FPRMExpr rm, RealExpr t, FPSort s)
    {
        return new FPExpr(this, Native.mkFpaToFpReal(nCtx(), rm.getNativeObject(), t.getNativeObject(), s.getNativeObject()));
    }

    /**
     * Conversion of a 2's complement signed bit-vector term into a term of FloatingPoint sort.
     * @param rm RoundingMode term.
     * @param t term of bit-vector sort.
     * @param s FloatingPoint sort.
     * @param signed flag indicating whether t is interpreted as signed or unsigned bit-vector.
     * Remarks:
     * Produces a term that represents the conversion of the bit-vector term t into a
     * floating-point term of sort s. The bit-vector t is taken to be in signed 
     * 2's complement format (when signed==true, otherwise unsigned). If necessary, the 
     * result will be rounded according to rounding mode rm.
     * @throws Z3Exception 
     **/
    public FPExpr mkFPToFP(FPRMExpr rm, BitVecExpr t, FPSort s, boolean signed)
    {
        if (signed)
            return new FPExpr(this, Native.mkFpaToFpSigned(nCtx(), rm.getNativeObject(), t.getNativeObject(), s.getNativeObject()));
        else
            return new FPExpr(this, Native.mkFpaToFpUnsigned(nCtx(), rm.getNativeObject(), t.getNativeObject(), s.getNativeObject()));
    }

    /**
     * Conversion of a floating-point number to another FloatingPoint sort s.
     * @param s FloatingPoint sort
     * @param rm floating-point rounding mode term
     * @param t floating-point term
     * Remarks:
     * Produces a term that represents the conversion of a floating-point term t to a different
     * FloatingPoint sort s. If necessary, rounding according to rm is applied. 
     * @throws Z3Exception 
     **/
    public FPExpr mkFPToFP(FPSort s, FPRMExpr rm, FPExpr t)
    {
        return new FPExpr(this, Native.mkFpaToFpFloat(nCtx(), s.getNativeObject(), rm.getNativeObject(), t.getNativeObject()));
    }

    /**
     * Conversion of a floating-point term into a bit-vector.
     * @param rm RoundingMode term.
     * @param t FloatingPoint term
     * @param sz Size of the resulting bit-vector.
     * @param signed Indicates whether the result is a signed or unsigned bit-vector.
     * Remarks:
     * Produces a term that represents the conversion of the floating-poiunt term t into a
     * bit-vector term of size sz in 2's complement format (signed when signed==true). If necessary, 
     * the result will be rounded according to rounding mode rm.        
     * @throws Z3Exception 
     **/
    public BitVecExpr mkFPToBV(FPRMExpr rm, FPExpr t, int sz, boolean signed)
    {
        if (signed)
            return new BitVecExpr(this, Native.mkFpaToSbv(nCtx(), rm.getNativeObject(), t.getNativeObject(), sz));
        else
            return new BitVecExpr(this, Native.mkFpaToUbv(nCtx(), rm.getNativeObject(), t.getNativeObject(), sz));
    }

    /**
     * Conversion of a floating-point term into a real-numbered term.
     * @param t FloatingPoint term
     * Remarks:
     * Produces a term that represents the conversion of the floating-poiunt term t into a
     * real number. Note that this type of conversion will often result in non-linear 
     * constraints over real terms.
     * @throws Z3Exception 
     **/
    public RealExpr mkFPToReal(FPExpr t)
    {
        return new RealExpr(this, Native.mkFpaToReal(nCtx(), t.getNativeObject()));
    }

    /**
     * Conversion of a floating-point term into a bit-vector term in IEEE 754-2008 format.
     * @param t FloatingPoint term.
     * Remarks:
     * The size of the resulting bit-vector is automatically determined. Note that 
     * IEEE 754-2008 allows multiple different representations of NaN. This conversion 
     * knows only one NaN and it will always produce the same bit-vector represenatation of 
     * that NaN. 
     * @throws Z3Exception 
     **/
    public BitVecExpr mkFPToIEEEBV(FPExpr t)
    {
        return new BitVecExpr(this, Native.mkFpaToIeeeBv(nCtx(), t.getNativeObject()));
    }

    /**
     * Conversion of a real-sorted significand and an integer-sorted exponent into a term of FloatingPoint sort.
     * @param rm RoundingMode term.
     * @param exp Exponent term of Int sort.
     * @param sig Significand term of Real sort.
     * @param s FloatingPoint sort.
     * Remarks:
     * Produces a term that represents the conversion of sig * 2^exp into a 
     * floating-point term of sort s. If necessary, the result will be rounded
     * according to rounding mode rm.
     * @throws Z3Exception 
     **/
         
    public BitVecExpr mkFPToFP(FPRMExpr rm, IntExpr exp, RealExpr sig, FPSort s)
    {
        return new BitVecExpr(this, Native.mkFpaToFpIntReal(nCtx(), rm.getNativeObject(), exp.getNativeObject(), sig.getNativeObject(), s.getNativeObject()));
    }
    
    
    /**
     * Wraps an AST.
     * Remarks: This function is used for transitions between
     * native and managed objects. Note that {@code nativeObject}
     * must be a native object obtained from Z3 (e.g., through 
     * {@code UnwrapAST}) and that it must have a correct reference count.
     * @see Native#incRef 
     * @see unwrapAST
     * @param nativeObject The native pointer to wrap.
     **/
    public AST wrapAST(long nativeObject)
    {
        return AST.create(this, nativeObject);
    }

    /**
     * Unwraps an AST.
     * Remarks: This function is used for transitions between
     * native and managed objects. It returns the native pointer to the AST.
     * Note that AST objects are reference counted and unwrapping an AST
     * disables automatic reference counting, i.e., all references to the IntPtr
     * that is returned must be handled externally and through native calls (see
     * e.g., 
     * @see Native#incRef 
     * @see wrapAST 
     * @param a The AST to unwrap.
     **/
    public long unwrapAST(AST a)
    {
        return a.getNativeObject();
    }

    /**
     * Return a string describing all available parameters to
     * {@code Expr.Simplify}.
     **/
    public String SimplifyHelp()
    {
        return Native.simplifyGetHelp(nCtx());
    }

    /**
     * Retrieves parameter descriptions for simplifier.
     **/
    public ParamDescrs getSimplifyParameterDescriptions()
    {
        return new ParamDescrs(this, Native.simplifyGetParamDescrs(nCtx()));
    }

    /**
     * Update a mutable configuration parameter.
     * Remarks:  The list of all
     * configuration parameters can be obtained using the Z3 executable:
     * {@code z3.exe -ini?} Only a few configuration parameters are mutable
     * once the context is created. An exception is thrown when trying to modify
     * an immutable parameter.  
     **/
    public void updateParamValue(String id, String value)
    {
        Native.updateParamValue(nCtx(), id, value);
    }

    long m_ctx = 0;

    long nCtx()
    {
        return m_ctx;
    }

    void initContext()
    {
        setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
        Native.setInternalErrorHandler(nCtx());
    }

    void checkContextMatch(Z3Object other)
    {
        if (this != other.getContext())
            throw new Z3Exception("Context mismatch");
    }

    void checkContextMatch(Z3Object[] arr)
    {
        if (arr != null)
            for (Z3Object a : arr)
                checkContextMatch(a);
    }

    private ASTDecRefQueue m_AST_DRQ = new ASTDecRefQueue();
    private ASTMapDecRefQueue m_ASTMap_DRQ = new ASTMapDecRefQueue(10);
    private ASTVectorDecRefQueue m_ASTVector_DRQ = new ASTVectorDecRefQueue(10);
    private ApplyResultDecRefQueue m_ApplyResult_DRQ = new ApplyResultDecRefQueue(10);
    private FuncInterpEntryDecRefQueue m_FuncEntry_DRQ = new FuncInterpEntryDecRefQueue(10);
    private FuncInterpDecRefQueue m_FuncInterp_DRQ = new FuncInterpDecRefQueue(10);
    private GoalDecRefQueue m_Goal_DRQ = new GoalDecRefQueue(10);
    private ModelDecRefQueue m_Model_DRQ = new ModelDecRefQueue(10);
    private ParamsDecRefQueue m_Params_DRQ = new ParamsDecRefQueue(10);
    private ParamDescrsDecRefQueue m_ParamDescrs_DRQ = new ParamDescrsDecRefQueue(10);
    private ProbeDecRefQueue m_Probe_DRQ = new ProbeDecRefQueue(10);
    private SolverDecRefQueue m_Solver_DRQ = new SolverDecRefQueue(10);
    private StatisticsDecRefQueue m_Statistics_DRQ = new StatisticsDecRefQueue(10);
    private TacticDecRefQueue m_Tactic_DRQ = new TacticDecRefQueue(10);
    private FixedpointDecRefQueue m_Fixedpoint_DRQ = new FixedpointDecRefQueue(10);

    public IDecRefQueue getASTDRQ()
    {
        return m_AST_DRQ;
    }

    public IDecRefQueue getASTMapDRQ()
    {
        return m_ASTMap_DRQ;
    }

    public IDecRefQueue getASTVectorDRQ()
    {
        return m_ASTVector_DRQ;
    }

    public IDecRefQueue getApplyResultDRQ()
    {
        return m_ApplyResult_DRQ;
    }

    public IDecRefQueue getFuncEntryDRQ()
    {
        return m_FuncEntry_DRQ;
    }

    public IDecRefQueue getFuncInterpDRQ()
    {
        return m_FuncInterp_DRQ;
    }

    public IDecRefQueue getGoalDRQ()
    {
        return m_Goal_DRQ;
    }

    public IDecRefQueue getModelDRQ()
    {
        return m_Model_DRQ;
    }

    public IDecRefQueue getParamsDRQ()
    {
        return m_Params_DRQ;
    }

    public IDecRefQueue getParamDescrsDRQ()
    {
        return m_ParamDescrs_DRQ;
    }

    public IDecRefQueue getProbeDRQ()
    {
        return m_Probe_DRQ;
    }

    public IDecRefQueue getSolverDRQ()
    {
        return m_Solver_DRQ;
    }

    public IDecRefQueue getStatisticsDRQ()
    {
        return m_Statistics_DRQ;
    }

    public IDecRefQueue getTacticDRQ()
    {
        return m_Tactic_DRQ;
    }

    public IDecRefQueue getFixedpointDRQ()
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
