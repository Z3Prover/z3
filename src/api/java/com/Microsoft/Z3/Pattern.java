/**
 * This file was automatically generated from Pattern.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

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
        public int NumTerms()  { return Native.getPatternNumTerms(Context().nCtx(), NativeObject()); }

        /**
         * The terms in the pattern.
         **/
        public Expr[] Terms() 
            {
                

                int n = NumTerms();
                Expr[] res = new Expr[n];
                for (int i = 0; i < n; i++)
                    res[i] = Expr.Create(Context(), Native.getPattern(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * A string representation of the pattern.
         **/
        public String toString()
        {
            return Native.patternToString(Context().nCtx(), NativeObject());
        }

        Pattern(Context ctx, long obj)
        { super(ctx, obj);
            
        }
    }
