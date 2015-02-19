/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ArithSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * An arithmetic sort, i.e., Int or Real.
 **/
public class ArithSort extends Sort
{
    ArithSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
};
