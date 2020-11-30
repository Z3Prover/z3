/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMExpr.java

Abstract:

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
package com.microsoft.z3;

/**
 * FloatingPoint RoundingMode Expressions
 */
public class FPRMExpr extends Expr<FPRMSort>
{       
    public FPRMExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }

}
