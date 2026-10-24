/* Copyright (c) 2026 Microsoft Corporation */
package com.microsoft.z3;

/** The Complex sort, representing pairs of Reals. */
public class ComplexSort extends ArithSort
{
    ComplexSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    ComplexSort(Context ctx)
    {
        super(ctx, Native.mkComplexSort(ctx.nCtx()));
    }
}
