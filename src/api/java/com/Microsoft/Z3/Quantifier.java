/**
 * This file was automatically generated from Quantifier.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Quantifier expressions.
     **/
    public class Quantifier extends BoolExpr
    {
        /**
         * Indicates whether the quantifier is universal.
         **/
        public boolean IsUniversal()  { return Native.isQuantifierForall(Context.nCtx, NativeObject) != 0; }

        /**
         * Indicates whether the quantifier is existential.
         **/
        public boolean IsExistential()  { return !IsUniversal; }

        /**
         * The weight of the quantifier.
         **/
        public long Weight()  { return Native.getQuantifierWeight(Context.nCtx, NativeObject); }

        /**
         * The number of patterns.
         **/
        public long NumPatterns()  { return Native.getQuantifierNumPatterns(Context.nCtx, NativeObject); }

        /**
         * The patterns.
         **/
        public Pattern[] Patterns() 
            {
                

                long n = NumPatterns;
                Pattern[] res = new Pattern[n];
                for (long i = 0; i < n; i++)
                    res[i] = new Pattern(Context, Native.getQuantifierPatternAst(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The number of no-patterns.
         **/
        public long NumNoPatterns()  { return Native.getQuantifierNumNoPatterns(Context.nCtx, NativeObject); }

        /**
         * The no-patterns.
         **/
        public Pattern[] NoPatterns() 
            {
                

                long n = NumNoPatterns;
                Pattern[] res = new Pattern[n];
                for (long i = 0; i < n; i++)
                    res[i] = new Pattern(Context, Native.getQuantifierNoPatternAst(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The number of bound variables.
         **/
        public long NumBound()  { return Native.getQuantifierNumBound(Context.nCtx, NativeObject); }

        /**
         * The symbols for the bound variables.
         **/
        public Symbol[] BoundVariableNames() 
            {
                

                long n = NumBound;
                Symbol[] res = new Symbol[n];
                for (long i = 0; i < n; i++)
                    res[i] = Symbol.Create(Context, Native.getQuantifierBoundName(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The sorts of the bound variables.
         **/
        public Sort[] BoundVariableSorts() 
            {
                

                long n = NumBound;
                Sort[] res = new Sort[n];
                for (long i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.getQuantifierBoundSort(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The body of the quantifier.
         **/
        public BoolExpr Body()  {
                
                
                return new BoolExpr(Context, Native.getQuantifierBody(Context.nCtx, NativeObject)); }
        }

        Quantifier(Context ctx, boolean isForall, Sort[] sorts, Symbol[] names, Expr body,
                            long weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null,
                            Symbol quantifierID = null, Symbol skolemID = null
                            )
            { super(ctx);
            
            
            
            
            
            
            
            
            

            Context.CheckContextMatch(patterns);
            Context.CheckContextMatch(noPatterns);
            Context.CheckContextMatch(sorts);
            Context.CheckContextMatch(names);
            Context.CheckContextMatch(body);

            if (sorts.Length != names.Length)
                throw new Z3Exception("Number of sorts does not match number of names");

            IntPtr[] _patterns = AST.ArrayToNative(patterns);

            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                NativeObject = Native.mkQuantifier(ctx.nCtx, (isForall) ? 1 : 0, weight,
                                           AST.ArrayLength(patterns),  AST.ArrayToNative(patterns),
                                           AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
                                           Symbol.ArrayToNative(names),
                                           body.NativeObject);
            else
            {
                NativeObject = Native.mkQuantifierEx(ctx.nCtx, (isForall) ? 1 : 0, weight,
                                  AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
                                  AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                  AST.ArrayLength(noPatterns), AST.ArrayToNative(noPatterns),
                                  AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
                                  Symbol.ArrayToNative(names),
                                  body.NativeObject);
            }
        }

        Quantifier(Context ctx, boolean isForall, Expr[] bound, Expr body,
                            long weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null,
                            Symbol quantifierID = null, Symbol skolemID = null
            )
            { super(ctx);
            
            

                   
            
            

            Context.CheckContextMatch(noPatterns);
            Context.CheckContextMatch(patterns);
            //Context.CheckContextMatch(bound);
            Context.CheckContextMatch(body);
            
            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                NativeObject = Native.mkQuantifierConst(ctx.nCtx, (isForall) ? 1 : 0, weight,
                                                 AST.ArrayLength(bound), AST.ArrayToNative(bound),
                                                 AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                                 body.NativeObject);
            }
            else
            {
                NativeObject = Native.mkQuantifierConstEx(ctx.nCtx, (isForall) ? 1 : 0, weight,
                                        AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
                                        AST.ArrayLength(bound), AST.ArrayToNative(bound),
                                        AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                        AST.ArrayLength(noPatterns), AST.ArrayToNative(noPatterns),
                                        body.NativeObject);
            }
        }


        Quantifier(Context ctx, IntPtr obj) { super(ctx, obj);  }

        void CheckNativeObject(IntPtr obj)
        {
            if ((Z3_ast_kind)Native.getAstKind(Context.nCtx, obj) != Z3_ast_kind.Z3_QUANTIFIER_AST)
                throw new Z3Exception("Underlying object is not a quantifier");
            super.CheckNativeObject(obj);
        }
    }
