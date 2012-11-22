/**
 * This file was automatically generated from Expr.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Expressions are terms.     
     **/
    public class Expr extends AST
    {
        /**
         * Returns a simplified version of the expression.
         * <param name="p">A set of parameters to configure the simplifier</param>
         * <seealso cref="Context.SimplifyHelp"/>
         **/
        public Expr Simplify(Params p)
        {
            

            if (p == null)
                return Expr.Create(Context, Native.simplify(Context.nCtx, NativeObject));
            else
                return Expr.Create(Context, Native.simplifyEx(Context.nCtx, NativeObject, p.NativeObject));
        }

        /**
         * The function declaration of the function that is applied in this expression.
         **/
        public FuncDecl FuncDecl()  {
                
                return new FuncDecl(Context, Native.getAppDecl(Context.nCtx, NativeObject)); }

        /**
         * Indicates whether the expression is the true or false expression
         * or something else (Z3_L_UNDEF).
         **/
        public Z3_lboolean BoolValue()  { return (Z3Lboolean)Native.getBooleanValue(Context.nCtx, NativeObject); }

        /**
         * The number of arguments of the expression.
         **/
        public Integer NumArgs()  { return Native.getAppNumArgs(Context.nCtx, NativeObject); }

        /**
         * The arguments of the expression.
         **/
        public Expr[] Args() 
            {
                

                Integer n = NumArgs;
                Expr[] res = new Expr[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = Expr.Create(Context, Native.getAppArg(Context.nCtx, NativeObject, i));
                return res;
        }

        /**
         * Update the arguments of the expression using the arguments <paramref name="args"/>
         * The number of new arguments should coincide with the current number of arguments.
         **/
        public void Update(Expr[] args)
        {
            
            

            Context.CheckContextMatch(args);
            if (args.Length != NumArgs)
                throw new Z3Exception("Number of arguments does not match");
            NativeObject = Native.updateTerm(Context.nCtx, NativeObject, (Integer)args.Length, Expr.ArrayToNative(args));
        }

        /**
         * Substitute every occurrence of <code>from[i]</code> in the expression with <code>to[i]</code>, for <code>i</code> smaller than <code>num_exprs</code>.
         * <remarks>
         * The result is the new expression. The arrays <code>from</code> and <code>to</code> must have size <code>num_exprs</code>.
         * For every <code>i</code> smaller than <code>num_exprs</code>, we must have that 
         * sort of <code>from[i]</code> must be equal to sort of <code>to[i]</code>.
         * </remarks>    
         **/
        public Expr Substitute(Expr[] from, Expr[] to)
        {
            
            
            
            
            

            Context.CheckContextMatch(from);
            Context.CheckContextMatch(to);
            if (from.Length != to.Length)
                throw new Z3Exception("Argument sizes do not match");
            return Expr.Create(Context, Native.substitute(Context.nCtx, NativeObject, (Integer)from.Length, Expr.ArrayToNative(from), Expr.ArrayToNative(to)));
        }

        /**
         * Substitute every occurrence of <code>from</code> in the expression with <code>to</code>.
         * <seealso cref="Substitute(Expr[],Expr[])"/>
         **/
        public Expr Substitute(Expr from, Expr to)
        {
            
            
            

            return Substitute(new Expr[] { from }, new Expr[] { to });
        }

        /**
         * Substitute the free variables in the expression with the expressions in <paramref name="to"/>
         * <remarks>
         * For every <code>i</code> smaller than <code>num_exprs</code>, the variable with de-Bruijn index <code>i</code> is replaced with term <code>to[i]</code>.
         * </remarks>
         **/
        public Expr SubstituteVars(Expr[] to)
        {
            
            
            

            Context.CheckContextMatch(to);
            return Expr.Create(Context, Native.substituteVars(Context.nCtx, NativeObject, (Integer)to.Length, Expr.ArrayToNative(to)));
        }

        /**
         * Translates (copies) the term to the Context <paramref name="ctx"/>.
         * <param name="ctx">A context</param>
         * @return A copy of the term which is associated with <paramref name="ctx"/>
         **/
        public Expr Translate(Context ctx)
        {
            
            

            if (ReferenceEquals(Context, ctx))
                return this;
            else
                return Expr.Create(ctx, Native.translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /**
         * Returns a string representation of the expression.
         **/
        public String toString()
        {
            return super.toString();
        }        

        /**
         * Indicates whether the term is a numeral
         **/
        public boolean IsNumeral()  { return Native.isNumeralAst(Context.nCtx, NativeObject) != 0; }

        /**
         * Indicates whether the term is well-sorted.
         * @return True if the term is well-sorted, false otherwise.
         **/
        public boolean IsWellSorted()  { return Native.isWellSorted(Context.nCtx, NativeObject) != 0; }

        /**
         * The Sort of the term.
         **/
        public Sort Sort()  {
                
                return Sort.Create(Context, Native.getSort(Context.nCtx, NativeObject)); }

        /**
         * Indicates whether the term represents a constant.
         **/
        public boolean IsConst()  { return IsExpr && NumArgs == 0 && FuncDecl.DomainSize == 0; }

        /**
         * Indicates whether the term is an integer numeral.
         **/
        public boolean IsIntNum()  { return IsNumeral && IsInt; }

        /**
         * Indicates whether the term is a real numeral.
         **/
        public boolean IsRatNum()  { return IsNumeral && IsReal; }

        /**
         * Indicates whether the term is an algebraic number
         **/
        public boolean IsAlgebraicNumber()  { return Native.isAlgebraicNumber(Context.nCtx, NativeObject) != 0; }


        /**
         * Indicates whether the term has Boolean sort.
         **/
        public boolean IsBool() 
            {
                return (IsExpr &&
                        Native.isEqSort(Context.nCtx,
                                              Native.mkBooleanSort(Context.nCtx),
                                              Native.getSort(Context.nCtx, NativeObject)) != 0);
        }

        /**
         * Indicates whether the term is the constant true.
         **/
         /* Overloaded operators are not translated. */
        }

        /**
         * Indicates whether the term is of sort real.
         **/
        public boolean IsReal()  { return Native.getSortKind(Context.nCtx, Native.getSort(Context.nCtx, NativeObject)) == (Integer)Z3SortKind.Z3REALSORT; }

        /**
         * Indicates whether the term is an arithmetic numeral.
         **/
         /* Overloaded operators are not translated. */
        }

        /**
         * Indicates whether the term is an array store. 
         * <remarks>It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j). 
         * Array store takes at least 3 arguments. </remarks>
         **/
         /* Overloaded operators are not translated. */

        /**
         * Indicates whether the term is a bit-vector numeral
         **/
         /* Overloaded operators are not translated. */
        }

        /**
         * Indicates whether the term is an relation store
         * <remarks>
         * Insert a record into a relation.
         * The function takes <code>n+1</code> arguments, where the first argument is the relation and the remaining <code>n</code> elements 
         * correspond to the <code>n</code> columns of the relation.
         * </remarks>
         **/
         /* Overloaded operators are not translated. */
        }

        /**
         * Indicates whether the term is a less than predicate over a finite domain.
         **/
         /* Overloaded operators are not translated. */
        }

        /** Constructor for Expr </summary>
         **/
        protected Expr(Context ctx) { super(ctx);  }
        /** Constructor for Expr </summary>
         **/
        protected Expr(Context ctx, IntPtr obj) { super(ctx, obj);  }

        void CheckNativeObject(IntPtr obj)
        {
            if (Native.isApp(Context.nCtx, obj) == 0 &&
                (Z3AstKind)Native.getAstKind(Context.nCtx, obj) != Z3AstKind.Z3VARAST &&
                (Z3AstKind)Native.getAstKind(Context.nCtx, obj) != Z3AstKind.Z3QUANTIFIERAST)
                throw new Z3Exception("Underlying object is not a term");
            super.CheckNativeObject(obj);
        }

        static Expr Create(Context ctx, FuncDecl f, params Expr[] arguments)
        {
            
            
            

            IntPtr obj = Native.mkApp(ctx.nCtx, f.NativeObject, 
                                          AST.ArrayLength(arguments), 
                                          AST.ArrayToNative(arguments));
            return Create(ctx, obj);
        }        

        new static Expr Create(Context ctx, IntPtr obj)
        {
            
            

            Z3AstKind k = (Z3AstKind)Native.getAstKind(ctx.nCtx, obj);
            if (k == Z3AstKind.Z3QUANTIFIERAST)
                return new Quantifier(ctx, obj);
            IntPtr s = Native.getSort(ctx.nCtx, obj);
            Z3SortKind sk = (Z3SortKind)Native.getSortKind(ctx.nCtx, s);

            if (Native.isAlgebraicNumber(ctx.nCtx, obj) != 0) // is this a numeral ast?
                return new AlgebraicNum(ctx, obj);

            if (Native.isNumeralAst(ctx.nCtx, obj) != 0)
            {
                switch (sk)
                {
                    case Z3SortKind.Z3INTSORT: return new IntNum(ctx, obj);
                    case Z3SortKind.Z3REALSORT: return new RatNum(ctx, obj);
                    case Z3SortKind.Z3BVSORT: return new BitVecNum(ctx, obj);
                }
            }

            switch (sk)
            {
                case Z3SortKind.Z3BOOLSORT: return new BoolExpr(ctx, obj);
                case Z3SortKind.Z3INTSORT: return new IntExpr(ctx, obj);
                case Z3SortKind.Z3REALSORT: return new RealExpr(ctx, obj);
                case Z3SortKind.Z3BVSORT: return new BitVecExpr(ctx, obj);
                case Z3SortKind.Z3ARRAYSORT: return new ArrayExpr(ctx, obj);
                case Z3SortKind.Z3DATATYPESORT: return new DatatypeExpr(ctx, obj);
            }

            return new Expr(ctx, obj);
        }
    }

    /**
     * Boolean expressions
     **/
    public class BoolExpr extends Expr
    {
        /** Constructor for BoolExpr </summary>
     **/
        protected BoolExpr(Context ctx) { super(ctx);  }
        /** Constructor for BoolExpr </summary>
     **/
        BoolExpr(Context ctx, IntPtr obj) { super(ctx, obj);  }
    }

    /**
     * Arithmetic expressions (int/real)
     **/
    public class ArithExpr extends Expr
    {
        /** Constructor for ArithExpr </summary>
     **/
        protected ArithExpr(Context ctx)
            { super(ctx);
            
        }
        ArithExpr(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }

    /**
     * Int expressions
     **/
    public class IntExpr extends ArithExpr
    {
        /** Constructor for IntExpr </summary>
     **/
        protected IntExpr(Context ctx)
            { super(ctx);
            
        }
        IntExpr(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }

    /**
     * Real expressions
     **/
    public class RealExpr extends ArithExpr
    {
        /** Constructor for RealExpr </summary>
     **/
        protected RealExpr(Context ctx)
            { super(ctx);
            
        }
        RealExpr(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }

    /**
     * Bit-vector expressions
     **/
    public class BitVecExpr extends Expr
    {

        /**
         * The size of the sort of a bit-vector term.
         **/
        public Integer SortSize()  { return ((BitVecSort)Sort).Size; }

        /** Constructor for BitVecExpr </summary>
         **/
        protected BitVecExpr(Context ctx) { super(ctx);  }
        BitVecExpr(Context ctx, IntPtr obj) { super(ctx, obj);  }
    }

    /**
     * Array expressions
     **/
    public class ArrayExpr extends Expr
    {
        /** Constructor for ArrayExpr </summary>
     **/
        protected ArrayExpr(Context ctx)
            { super(ctx);
            
        }
        ArrayExpr(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }

    /**
     * Datatype expressions
     **/
    public class DatatypeExpr extends Expr
    {
        /** Constructor for DatatypeExpr </summary>
     **/
        protected DatatypeExpr(Context ctx)
            { super(ctx);
            
        }
        DatatypeExpr(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }
