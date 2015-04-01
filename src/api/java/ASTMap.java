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
class ASTMap extends Z3Object
{
    /**
     * Checks whether the map contains the key {@code k}. 
     * @param k An AST
     * 
     * @return True if {@code k} is a key in the map, false
     *         otherwise.
     **/
    public boolean contains(AST k) throws Z3Exception
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
    public AST find(AST k) throws Z3Exception
    {
        return new AST(getContext(), Native.astMapFind(getContext().nCtx(),
                getNativeObject(), k.getNativeObject()));
    }

    /**
     * Stores or replaces a new key/value pair in the map. 
     * @param k The key AST
     * @param v The value AST
     **/
    public void insert(AST k, AST v) throws Z3Exception
    {

        Native.astMapInsert(getContext().nCtx(), getNativeObject(), k.getNativeObject(),
                v.getNativeObject());
    }

    /**
     * Erases the key {@code k} from the map. 
     * @param k An AST
     **/
    public void erase(AST k) throws Z3Exception
    {
        Native.astMapErase(getContext().nCtx(), getNativeObject(), k.getNativeObject());
    }

    /**
     * Removes all keys from the map.
     **/
    public void reset() throws Z3Exception
    {
        Native.astMapReset(getContext().nCtx(), getNativeObject());
    }

    /**
     * The size of the map
     **/
    public int size() throws Z3Exception
    {
        return Native.astMapSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * The keys stored in the map.
     * 
     * @throws Z3Exception
     **/
    public ASTVector getKeys() throws Z3Exception
    {
        return new ASTVector(getContext(), Native.astMapKeys(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Retrieves a string representation of the map.
     **/
    public String toString()
    {
        try
        {
            return Native.astMapToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    ASTMap(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    ASTMap(Context ctx) throws Z3Exception
    {
        super(ctx, Native.mkAstMap(ctx.nCtx()));
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().getASTMapDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().getASTMapDRQ().add(o);
        super.decRef(o);
    }
}
