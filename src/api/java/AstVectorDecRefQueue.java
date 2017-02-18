/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    AstVectorDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class ASTVectorDecRefQueue extends IDecRefQueue<ASTVector> {
    public ASTVectorDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.astVectorDecRef(ctx.nCtx(), obj);
    }
}
