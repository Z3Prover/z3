/**
 * This file was automatically generated from SetSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * Set sorts.
     **/
    public class SetSort extends Sort
    {
        SetSort(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        SetSort(Context ctx, Sort ty)
        { super(ctx, Native.mkSetSort(ctx.nCtx(), ty.NativeObject()));
            
            
        }
    }
