/**
 * This file was automatically generated from Pattern.cs 
 **/

package com.Microsoft.Z3;

/* using System; */
/* using System.Runtime.InteropServices; */

    /**
     * Patterns comprise a list of terms. The list should be
     * non-empty.  If the list comprises of more than one term, it is
     * also called a multi-pattern.
     **/
    public class Pattern extends AST
    {
        /**
         * The number of terms in the pattern.
         **/
        public long NumTerms()  { return Native.getPatternNumTerms(Context.nCtx, NativeObject); }

        /**
         * The terms in the pattern.
         **/
        public Expr[] Terms() 
            {
                

                long n = NumTerms;
                Expr[] res = new Expr[n];
                for (long i = 0; i < n; i++)
                    res[i] = Expr.Create(Context, Native.getPattern(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * A string representation of the pattern.
         **/
        public String toString()
        {
            return Native.patterntoString(Context.nCtx, NativeObject);
        }

        Pattern(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }
