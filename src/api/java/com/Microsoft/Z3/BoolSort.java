/**
 * This file was automatically generated from BoolSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * A Boolean sort.
     **/
    public class BoolSort extends Sort
    {
    BoolSort(Context ctx, long obj) { super(ctx, obj); {  }}
    BoolSort(Context ctx) { super(ctx, Native.mkBoolSort(ctx.nCtx())); {  }}
    };
