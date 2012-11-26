/**
 * This file was automatically generated from BitVecExpr.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;
/* using System; */
/* using System.Collections.Generic; */
/* using System.Linq; */
/* using System.Text; */


    /**
     * Bit-vector expressions
     **/
    public class BitVecExpr extends Expr
    {

        /**
         * The size of the sort of a bit-vector term.
         **/
        public int SortSize()  { return ((BitVecSort)Sort).Size; }

        /** Constructor for BitVecExpr </summary>
         **/
    protected BitVecExpr(Context ctx) { super(ctx); {  }}
    BitVecExpr(Context ctx, long obj) { super(ctx, obj); {  }}
    }
