/**
 * This file was automatically generated from ASTVector.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Vectors of ASTs.
 **/
class ASTVector extends Z3Object
{
    /**
     * The size of the vector
     **/
    public int size() throws Z3Exception
    {
        return Native.astVectorSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieves the i-th object in the vector. <remarks>May throw an
     * IndexOutOfBoundsException when <paramref name="i"/> is out of
     * range.</remarks> <param name="i">Index</param>
     * 
     * @return An AST
     * @throws Z3Exception
     **/
    public AST get(int i) throws Z3Exception
    {
        return new AST(getContext(), Native.astVectorGet(getContext().nCtx(),
                getNativeObject(), i));
    }

    public void set(int i, AST value) throws Z3Exception
    {

        Native.astVectorSet(getContext().nCtx(), getNativeObject(), i,
                value.getNativeObject());
    }

    /**
     * Resize the vector to <paramref name="newSize"/>. <param
     * name="newSize">The new size of the vector.</param>
     **/
    public void resize(int newSize) throws Z3Exception
    {
        Native.astVectorResize(getContext().nCtx(), getNativeObject(), newSize);
    }

    /**
     * Add the AST <paramref name="a"/> to the back of the vector. The size is
     * increased by 1. <param name="a">An AST</param>
     **/
    public void push(AST a) throws Z3Exception
    {
        Native.astVectorPush(getContext().nCtx(), getNativeObject(), a.getNativeObject());
    }

    /**
     * Translates all ASTs in the vector to <paramref name="ctx"/>. <param
     * name="ctx">A context</param>
     * 
     * @return A new ASTVector
     * @throws Z3Exception
     **/
    public ASTVector translate(Context ctx) throws Z3Exception
    {
        return new ASTVector(getContext(), Native.astVectorTranslate(getContext()
                .nCtx(), getNativeObject(), ctx.nCtx()));
    }

    /**
     * Retrieves a string representation of the vector.
     **/
    public String toString()
    {
        try
        {
            return Native.astVectorToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    ASTVector(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    ASTVector(Context ctx) throws Z3Exception
    {
        super(ctx, Native.mkAstVector(ctx.nCtx()));
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().astvector_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().astvector_DRQ().add(o);
        super.decRef(o);
    }
}
