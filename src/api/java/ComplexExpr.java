/* Copyright (c) 2026 Microsoft Corporation */
package com.microsoft.z3;

/** A Complex expression. Complex numbers have no ordering. */
public class ComplexExpr extends ArithExpr<ComplexSort>
{
    ComplexExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    /** Returns the Real-valued real component. */
    public RealExpr getRealPart()
    {
        return getContext().mkRealPart(this);
    }

    /** Returns the Real-valued imaginary component. */
    public RealExpr getImagPart()
    {
        return getContext().mkImagPart(this);
    }
}
