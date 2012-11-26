/**
 * This file was automatically generated from AlgebraicNum.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;
/* using System; */

/* using System.Numerics; */

    /**
     * Algebraic numbers
     **/
    public class AlgebraicNum extends ArithExpr
    {
        /**
         * Return a upper bound for a given real algebraic number. 
         * The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
         * <seealso cref="Expr.IsAlgebraicNumber"/>   
         * <param name="precision">the precision of the result</param>
         * @return A numeral Expr of sort Real
         **/
        public RatNum ToUpper(int precision)
        {
            

            return new RatNum(Context(), Native.getAlgebraicNumberUpper(Context().nCtx(), NativeObject(), precision));
        }

        /**
         * Return a lower bound for the given real algebraic number. 
         * The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
         * <seealso cref="Expr.IsAlgebraicNumber"/>
         * <param name="precision"></param>
         * @return A numeral Expr of sort Real
         **/
        public RatNum ToLower(int precision)
        {
            

            return new RatNum(Context(), Native.getAlgebraicNumberLower(Context().nCtx(), NativeObject(), precision));
        }

        /**
         * Returns a string representation in decimal notation.
         * <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>    
         **/
        public String ToDecimal(int precision)
        {
            

            return Native.getNumeralDecimalString(Context().nCtx(), NativeObject(), precision);
        }

        AlgebraicNum(Context ctx, long obj)
        { super(ctx, obj);
            
        }
    }
