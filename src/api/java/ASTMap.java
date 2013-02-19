/**
 * This file was automatically generated from ASTMap.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Map from AST to AST
 **/
class ASTMap extends Z3Object
{
    /**
     * Checks whether the map contains the key <paramref name="k"/>. <param
     * name="k">An AST</param>
     * 
     * @return True if <paramref name="k"/> is a key in the map, false
     *         otherwise.
     **/
    public boolean contains(AST k) throws Z3Exception
    {

        return Native.astMapContains(getContext().nCtx(), getNativeObject(),
                k.getNativeObject());
    }

    /**
     * Finds the value associated with the key <paramref name="k"/>. <remarks>
     * This function signs an error when <paramref name="k"/> is not a key in
     * the map. </remarks> <param name="k">An AST</param>
     * 
     * @throws Z3Exception
     **/
    public AST find(AST k) throws Z3Exception
    {
        return new AST(getContext(), Native.astMapFind(getContext().nCtx(),
                getNativeObject(), k.getNativeObject()));
    }

    /**
     * Stores or replaces a new key/value pair in the map. <param name="k">The
     * key AST</param> <param name="v">The value AST</param>
     **/
    public void insert(AST k, AST v) throws Z3Exception
    {

        Native.astMapInsert(getContext().nCtx(), getNativeObject(), k.getNativeObject(),
                v.getNativeObject());
    }

    /**
     * Erases the key <paramref name="k"/> from the map. <param name="k">An
     * AST</param>
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
        getContext().astmap_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().astmap_DRQ().add(o);
        super.decRef(o);
    }
}
