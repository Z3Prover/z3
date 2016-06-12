/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ASTMap.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Map from AST to AST
 **/
class ASTMap extends Z3Object {
    /**
     * Checks whether the map contains the key {@code k}. 
     * @param k An AST
     * 
     * @return True if {@code k} is a key in the map, false
     *         otherwise.
     **/
    public boolean contains(AST k)
    {

        return Native.astMapContains(getContext().nCtx(), getNativeObject(),
                k.getNativeObject());
    }

    /**
     * Finds the value associated with the key {@code k}. 
     * Remarks: This function signs an error when {@code k} is not a key in
     * the map. 
     * @param k An AST
     * 
     * @throws Z3Exception
     **/
    public AST find(AST k)
    {
        return new AST(getContext(), Native.astMapFind(getContext().nCtx(),
                getNativeObject(), k.getNativeObject()));
    }

    /**
     * Stores or replaces a new key/value pair in the map. 
     * @param k The key AST
     * @param v The value AST
     **/
    public void insert(AST k, AST v)
    {

        Native.astMapInsert(getContext().nCtx(), getNativeObject(), k.getNativeObject(),
                v.getNativeObject());
    }

    /**
     * Erases the key {@code k} from the map. 
     * @param k An AST
     **/
    public void erase(AST k)
    {
        Native.astMapErase(getContext().nCtx(), getNativeObject(), k.getNativeObject());
    }

    /**
     * Removes all keys from the map.
     **/
    public void reset()
    {
        Native.astMapReset(getContext().nCtx(), getNativeObject());
    }

    /**
     * The size of the map
     **/
    public int size()
    {
        return Native.astMapSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * The keys stored in the map.
     * 
     * @throws Z3Exception
     **/
    public AST[] getKeys()
    {
        ASTVector av = new ASTVector(getContext(), Native.astMapKeys(getContext().nCtx(), getNativeObject()));
        return av.ToArray();
    }

    /**
     * Retrieves a string representation of the map.
     **/
    @Override
    public String toString()
    {
        return Native.astMapToString(getContext().nCtx(), getNativeObject());
    }

    ASTMap(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    ASTMap(Context ctx)
    {
        super(ctx, Native.mkAstMap(ctx.nCtx()));
    }

    @Override
    void incRef() {
        Native.astMapIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getASTMapDRQ().storeReference(getContext(), this);
    }
}
