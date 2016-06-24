/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ConstructorList.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Lists of constructors
 **/
public class ConstructorList extends Z3Object {

    ConstructorList(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        // Constructor lists are not reference counted.
    }

    @Override
    void addToReferenceQueue() {
        getContext().getConstructorListDRQ().storeReference(getContext(), this);
    }

    ConstructorList(Context ctx, Constructor[] constructors)
    {
        super(ctx, Native.mkConstructorList(ctx.nCtx(),
                constructors.length,
                Constructor.arrayToNative(constructors)));
    }
}
