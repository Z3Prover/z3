/**
 * This file was automatically generated from BitVecSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Bit-vector sorts.
     **/
    public class BitVecSort extends Sort
    {
        /**
         * The size of the bit-vector sort.
         **/
        public long Size()  { return Native.getBvSortSize(Context().nCtx(), NativeObject()); }

    BitVecSort(Context ctx, long obj) { super(ctx, obj); {  }}
    BitVecSort(Context ctx, long size) { super(ctx, Native.mkBvSort(ctx.nCtx(), size)); {  }}
    };
