/**
 * This file was automatically generated from IntSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     *  An Integer sort
     **/
    public class IntSort extends ArithSort
    {
        IntSort(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        IntSort(Context ctx)
        { super(ctx, Native.mkIntSort(ctx.nCtx()));
            
        }
    }
