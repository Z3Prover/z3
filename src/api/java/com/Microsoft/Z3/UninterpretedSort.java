/**
 * This file was automatically generated from UninterpretedSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Uninterpreted Sorts
     **/
    public class UninterpretedSort extends Sort
    {
        UninterpretedSort(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        UninterpretedSort(Context ctx, Symbol s)
        { super(ctx, Native.mkUninterpretedSort(ctx.nCtx(), s.NativeObject));
            
            
        }
    }
