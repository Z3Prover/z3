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
     * @throws Throwable 
     * @throws Z3Exception on error
     **/
    protected void finalize() throws Throwable
    {
        try {        
            Native.delConstructorList(getContext().nCtx(), getNativeObject());            
        }
        catch (Throwable t) {
            throw t;
        }
        finally {
            super.finalize();
        }
    }

    ConstructorList(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    ConstructorList(Context ctx, Constructor[] constructors)
    {
        super(ctx);

        setNativeObject(Native.mkConstructorList(getContext().nCtx(),
                (int) constructors.length,
                Constructor.arrayToNative(constructors)));
    }
}
