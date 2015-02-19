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
public class ConstructorList extends Z3Object
{
    /**
     * Destructor.
     * @throws Z3Exception on error
     **/
    protected void finalize() throws Z3Exception
    {
        Native.delConstructorList(getContext().nCtx(), getNativeObject());
    }

    ConstructorList(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    ConstructorList(Context ctx, Constructor[] constructors) throws Z3Exception
    {
        super(ctx);

        setNativeObject(Native.mkConstructorList(getContext().nCtx(),
                (int) constructors.length,
                Constructor.arrayToNative(constructors)));
    }
}
