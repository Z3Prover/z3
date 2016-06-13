/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    AstMapDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class ASTMapDecRefQueue extends IDecRefQueue<ASTMap> {
    public ASTMapDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.astMapDecRef(ctx.nCtx(), obj);
    }
}
