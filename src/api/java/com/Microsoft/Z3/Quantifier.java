/**
 * This file was automatically generated from Quantifier.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * Quantifier expressions.
     **/
    public class Quantifier extends BoolExpr
    {
        /**
         * Indicates whether the quantifier is universal.
         **/
        public boolean IsUniversal()  { return Native.isQuantifierForall(Context().nCtx(), NativeObject()) ; }

        /**
         * Indicates whether the quantifier is existential.
         **/
        public boolean IsExistential()  { return !IsUniversal(); }

        /**
         * The weight of the quantifier.
         **/
        public int Weight()  { return Native.getQuantifierWeight(Context().nCtx(), NativeObject()); }

        /**
         * The number of patterns.
         **/
        public int NumPatterns()  { return Native.getQuantifierNumPatterns(Context().nCtx(), NativeObject()); }

        /**
         * The patterns.
         **/
        public Pattern[] Patterns() 
            {
                

                int n = NumPatterns();
                Pattern[] res = new Pattern[n];
                for (int i = 0; i < n; i++)
                    res[i] = new Pattern(Context(), Native.getQuantifierPatternAst(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The number of no-patterns.
         **/
        public int NumNoPatterns()  { return Native.getQuantifierNumNoPatterns(Context().nCtx(), NativeObject()); }

        /**
         * The no-patterns.
         **/
        public Pattern[] NoPatterns() 
            {
                

                int n = NumNoPatterns();
                Pattern[] res = new Pattern[n];
                for (int i = 0; i < n; i++)
                    res[i] = new Pattern(Context(), Native.getQuantifierNoPatternAst(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The number of bound variables.
         **/
        public int NumBound()  { return Native.getQuantifierNumBound(Context().nCtx(), NativeObject()); }

        /**
         * The symbols for the bound variables.
         **/
        public Symbol[] BoundVariableNames() 
            {
                

                int n = NumBound();
                Symbol[] res = new Symbol[n];
                for (int i = 0; i < n; i++)
                    res[i] = Symbol.Create(Context(), Native.getQuantifierBoundName(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The sorts of the bound variables.
         **/
        public Sort[] BoundVariableSorts() 
            {
                

                int n = NumBound();
                Sort[] res = new Sort[n];
                for (int i = 0; i < n; i++)
                    res[i] = Sort.Create(Context(), Native.getQuantifierBoundSort(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The body of the quantifier.
         **/
        public BoolExpr Body() 
            {
                

                return new BoolExpr(Context(), Native.getQuantifierBody(Context().nCtx(), NativeObject()));
            }

        Quantifier(Context ctx, boolean isForall, Sort[] sorts, Symbol[] names, Expr body, int weight, Pattern[] patterns, Expr[] noPatterns, Symbol quantifierID, Symbol skolemID)
        { super(ctx);
            
            
            
            
            
            
            
            
            

            Context().CheckContextMatch(patterns);
            Context().CheckContextMatch(noPatterns);
            Context().CheckContextMatch(sorts);
            Context().CheckContextMatch(names);
            Context().CheckContextMatch(body);

            if (sorts.length != names.length)
                throw new Z3Exception("Number of sorts does not match number of names");

            long[] _patterns = AST.ArrayToNative(patterns);

            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                setNativeObject(Native.mkQuantifier(ctx.nCtx(), (isForall) ? true : false, weight,
						 AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
						 AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
						 Symbol.ArrayToNative(names),
						 body.NativeObject()));
            }
            else
            {
                setNativeObject(Native.mkQuantifierEx(ctx.nCtx(), (isForall) ? true : false, weight,
						      AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
						      AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
						      AST.ArrayLength(noPatterns), AST.ArrayToNative(noPatterns),
						      AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
						      Symbol.ArrayToNative(names),
						      body.NativeObject()));
            }
        }

        Quantifier(Context ctx, boolean isForall, Expr[] bound, Expr body, int weight, Pattern[] patterns, Expr[] noPatterns, Symbol quantifierID, Symbol skolemID)
        { super(ctx);
            
            

            
            
            

            Context().CheckContextMatch(noPatterns);
            Context().CheckContextMatch(patterns);
            //Context().CheckContextMatch(bound);
            Context().CheckContextMatch(body);

            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                setNativeObject(Native.mkQuantifierConst(ctx.nCtx(), (isForall) ? true : false, weight,
							 AST.ArrayLength(bound), AST.ArrayToNative(bound),
							 AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
							 body.NativeObject()));
            }
            else
            {
                setNativeObject(Native.mkQuantifierConstEx(ctx.nCtx(), (isForall) ? true : false, weight,
							   AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
							   AST.ArrayLength(bound), AST.ArrayToNative(bound),
							   AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
							   AST.ArrayLength(noPatterns), AST.ArrayToNative(noPatterns),
							   body.NativeObject()));
            }
        }


    Quantifier(Context ctx, long obj) { super(ctx, obj); {  }}

        void CheckNativeObject(long obj)
        {
            if (Native.getAstKind(Context().nCtx(), obj) != Z3_ast_kind.Z3_QUANTIFIER_AST.toInt())
                throw new Z3Exception("Underlying object is not a quantifier");
            super.CheckNativeObject(obj);
        }
    }
