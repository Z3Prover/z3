/**
 * This file was automatically generated from RealSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * A real sort
     **/
    public class RealSort extends ArithSort
    {
        RealSort(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        RealSort(Context ctx)
        { super(ctx, Native.mkRealSort(ctx.nCtx()));
            
        }
    }
