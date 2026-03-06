/**
Copyright (c) 2024 Microsoft Corporation
   
Module Name:

    TypeVarSort.java

Abstract:

Author:

    GitHub Copilot 2024-01-30

Notes:
    
**/

package com.microsoft.z3;

/**
 * A type variable sort for use in polymorphic functions and datatypes.
 **/
public class TypeVarSort extends Sort
{
    TypeVarSort(Context ctx, long obj) { super(ctx, obj); }
    TypeVarSort(Context ctx, Symbol s) { super(ctx, Native.mkTypeVariable(ctx.nCtx(), s.getNativeObject())); }
}
