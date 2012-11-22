/**
 * This file was automatically generated from Model.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * A Model contains interpretations (assignments) of constants and functions. 
     **/
    public class Model extends Z3Object
    {
        /**
         * Retrieves the interpretation (the assignment) of <paramref name="a"/> in the model. 
         * <param name="a">A Constant</param>
         * @return An expression if the constant has an interpretation in the model, null otherwise.
         **/
        public Expr ConstInterp(Expr a)
        {
            

            Context.CheckContextMatch(a);
            return ConstInterp(a.FuncDecl);
        }

        /**
         * Retrieves the interpretation (the assignment) of <paramref name="f"/> in the model. 
         * <param name="f">A function declaration of zero arity</param>
         * @return An expression if the function has an interpretation in the model, null otherwise.    
         **/
        public Expr ConstInterp(FuncDecl f)
        {
            

            Context.CheckContextMatch(f);
            if (f.Arity != 0 ||
                Native.getSortKind(Context.nCtx, Native.getRange(Context.nCtx, f.NativeObject)) == (Integer)Z3SortKind.Z3ARRAYSORT)
                throw new Z3Exception("Non-zero arity functions and arrays have FunctionInterpretations as a model. Use FuncInterp.");

            IntPtr n = Native.modelGetConstInterp(Context.nCtx, NativeObject, f.NativeObject);
            if (n == IntPtr.Zero)
                return null;
            else
                return Expr.Create(Context, n);
        }

        /**
         * Retrieves the interpretation (the assignment) of a non-constant <paramref name="f"/> in the model. 
         * <param name="f">A function declaration of non-zero arity</param>
         * @return A FunctionInterpretation if the function has an interpretation in the model, null otherwise. 
         **/
        public FuncInterp FuncInterp(FuncDecl f)
        {
            

            Context.CheckContextMatch(f);

            Z3SortKind sk = (Z3SortKind)Native.getSortKind(Context.nCtx, Native.getRange(Context.nCtx, f.NativeObject));

            if (f.Arity == 0)
            {
                IntPtr n = Native.modelGetConstInterp(Context.nCtx, NativeObject, f.NativeObject);

                if (sk == Z3SortKind.Z3ARRAYSORT)
                {
                    if (n == IntPtr.Zero)
                        return null;
                    else
                    {
                        if (Native.isAsArray(Context.nCtx, n) == 0)
                            throw new Z3Exception("Argument was not an array constant");
                        IntPtr fd = Native.getAsArrayFuncDecl(Context.nCtx, n);
                        return FuncInterp(new FuncDecl(Context, fd));
                    }
                }
                else
                {
                    throw new Z3Exception("Constant functions do not have a function interpretation; use ConstInterp");
                }
            }
            else
            {
                IntPtr n = Native.modelGetFuncInterp(Context.nCtx, NativeObject, f.NativeObject);
                if (n == IntPtr.Zero)
                    return null;
                else
                    return new FuncInterp(Context, n);
            }
        }

        /**
         * The number of constants that have an interpretation in the model.
         **/
        public Integer NumConsts()  { return Native.modelGetNumConsts(Context.nCtx, NativeObject); }

        /**
         * The function declarations of the constants in the model.
         **/
        public FuncDecl[] ConstDecls() 
            {
                

                Integer n = NumConsts;
                FuncDecl[] res = new FuncDecl[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.modelGetConstDecl(Context.nCtx, NativeObject, i));
                return res;
        }

        /**
         * The number of function interpretations in the model.
         **/
        public Integer NumFuncs()  { return Native.modelGetNumFuncs(Context.nCtx, NativeObject); }

        /**
         * The function declarations of the function interpretations in the model.
         **/
        public FuncDecl[] FuncDecls() 
            {
                

                Integer n = NumFuncs;
                FuncDecl[] res = new FuncDecl[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.modelGetFuncDecl(Context.nCtx, NativeObject, i));
                return res;
        }

        /**
         * All symbols that have an interpretation in the model.
         **/
        public FuncDecl[] Decls() 
            {
                

                var nFuncs = NumFuncs;
                var nConsts = NumConsts;
                Integer n = nFuncs + nConsts;
                FuncDecl[] res = new FuncDecl[n];
                for (Integer i = 0; i < nConsts; i++)
                    res[i] = new FuncDecl(Context, Native.modelGetConstDecl(Context.nCtx, NativeObject, i));
                for (Integer i = 0; i < nFuncs; i++)
                    res[nConsts + i] = new FuncDecl(Context, Native.modelGetFuncDecl(Context.nCtx, NativeObject, i));                
                return res;
        }

        /**
         * A ModelEvaluationFailedException is thrown when an expression cannot be evaluated by the model.
         **/
        public class ModelEvaluationFailedException extends Z3Exception
        {
            /**
             * An exception that is thrown when model evaluation fails.
             **/
            public ModelEvaluationFailedException() { super(); }
        }

        /**
         * Evaluates the expression <paramref name="t"/> in the current model.
         * <remarks>
         * This function may fail if <paramref name="t"/> contains quantifiers, 
         * is partial (MODEL_PARTIAL enabled), or if <paramref name="t"/> is not well-sorted.
         * In this case a <code>ModelEvaluationFailedException</code> is thrown.
         * </remarks>
         * <param name="t">An expression</param>
         * <param name="completion">
         * When this flag is enabled, a model value will be assigned to any constant 
         * or function that does not have an interpretation in the model.
         * </param>
         * @return The evaluation of <paramref name="t"/> in the model.        
         **/
        public Expr Eval(Expr t, boolean completion)
        {
            
            

            IntPtr v = IntPtr.Zero;
            if (Native.modelEval(Context.nCtx, NativeObject, t.NativeObject, (completion) ? 1 : 0, v) == 0)
                throw new ModelEvaluationFailedException();
            else
                return Expr.Create(Context, v);
        }

        /**
         * Alias for <code>Eval</code>.
         **/
        public Expr Evaluate(Expr t, boolean completion)
        {
            
            

            return Eval(t, completion);
        }

        /**
         * The number of uninterpreted sorts that the model has an interpretation for.
         **/
        public Integer NumSorts () { return Native.modelGetNumSorts(Context.nCtx, NativeObject); }

        /**
         * The uninterpreted sorts that the model has an interpretation for. 
         * <remarks>
         * Z3 also provides an intepretation for uninterpreted sorts used in a formula.
         * The interpretation for a sort is a finite set of distinct values. We say this finite set is
         * the "universe" of the sort.
         * </remarks>
         * <seealso cref="NumSorts"/>
         * <seealso cref="SortUniverse"/>
         **/
        public Sort[] Sorts() 
            {
                

                Integer n = NumSorts;
                Sort[] res = new Sort[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.modelGetSort(Context.nCtx, NativeObject, i));
                return res;
        }

        /**
         * The finite set of distinct values that represent the interpretation for sort <paramref name="s"/>.
         * <seealso cref="Sorts"/>
         * <param name="s">An uninterpreted sort</param>
         * @return An array of expressions, where each is an element of the universe of <paramref name="s"/>
         **/
        public Expr[] SortUniverse(Sort s)
        {
            
            

            ASTVector nUniv = new ASTVector(Context, Native.modelGetSortUniverse(Context.nCtx, NativeObject, s.NativeObject));
            Integer n = nUniv.Size;
            Expr[] res = new Expr[n];
            for (Integer i = 0; i < n; i++)
                res[i] = Expr.Create(Context, nUniv[i].NativeObject);
            return res;
        }

        /**
         * Conversion of models to strings. 
         * @return A string representation of the model.
         **/
        public String toString()
        {
            return Native.modeltoString(Context.nCtx, NativeObject);
        }

        Model(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.modelIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.modelDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.ModelDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.ModelDRQ.Add(o);
            super.DecRef(o);
        }
    }
