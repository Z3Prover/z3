/**
 * This file was automatically generated from FiniteDomainSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Finite domain sorts.
     **/
    public class FiniteDomainSort extends Sort
    {
        /**
         * The size of the finite domain sort.
         **/
        public long Size() 
            {
                long res = 0;
                Native.getFiniteDomainSortSize(Context().nCtx(), NativeObject(), res);
                return res;
            }

        FiniteDomainSort(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        FiniteDomainSort(Context ctx, Symbol name, long size)
        { super(ctx, Native.mkFiniteDomainSort(ctx.nCtx(), name.NativeObject, size));
            
            

        }
    }
