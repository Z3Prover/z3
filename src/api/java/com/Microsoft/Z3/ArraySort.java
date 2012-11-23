/**
 * This file was automatically generated from ArraySort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Array sorts.
     **/
    public class ArraySort extends Sort
    {
        /**
         * The domain of the array sort.
         **/
        public Sort Domain() 
            {
                

                return Sort.Create(Context, Native.getArraySortDomain(Context().nCtx(), NativeObject()));
            }

        /**
         * The range of the array sort.
         **/
        public Sort Range() 
            {
                

                return Sort.Create(Context, Native.getArraySortRange(Context().nCtx(), NativeObject()));
            }

    ArraySort(Context ctx, long obj) { super(ctx, obj); {  }}
        ArraySort(Context ctx, Sort domain, Sort range)
        { super(ctx, Native.mkArraySort(ctx.nCtx(), domain.NativeObject, range.NativeObject));
            
            
            
        }
    };

