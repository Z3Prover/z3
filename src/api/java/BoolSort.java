/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    BoolSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * A Boolean sort.
 **/
public class BoolSort extends Sort
{
    BoolSort(Context ctx, long obj) { super(ctx, obj); {  }}
    BoolSort(Context ctx) { super(ctx, Native.mkBoolSort(ctx.nCtx())); {  }}
};
