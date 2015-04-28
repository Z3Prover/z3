/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ASTVector.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Vectors of ASTs.
 **/
public class ASTVector extends Z3Object
{
    /**
     * The size of the vector
     **/
    public int size()
    {
        return Native.astVectorSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieves the i-th object in the vector.
     * Remarks: May throw an {@code IndexOutOfBoundsException} when 
     * {@code i} is out of range. 
     * @param i Index
     * 
     * @return An AST
     * @throws Z3Exception
     **/
    public AST get(int i)
    {
        return new AST(getContext(), Native.astVectorGet(getContext().nCtx(),
                getNativeObject(), i));
    }

    public void set(int i, AST value)
    {

        Native.astVectorSet(getContext().nCtx(), getNativeObject(), i,
                value.getNativeObject());
    }

    /**
     * Resize the vector to {@code newSize}. 
     * @param newSize The new size of the vector.
     **/
    public void resize(int newSize)
    {
        Native.astVectorResize(getContext().nCtx(), getNativeObject(), newSize);
    }

    /**
     * Add the AST {@code a} to the back of the vector. The size is
     * increased by 1. 
     * @param a An AST
     **/
    public void push(AST a)
    {
        Native.astVectorPush(getContext().nCtx(), getNativeObject(), a.getNativeObject());
    }

    /**
     * Translates all ASTs in the vector to {@code ctx}. 
     * @param ctx A context
     * 
     * @return A new ASTVector
     * @throws Z3Exception
     **/
    public ASTVector translate(Context ctx)
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

    ASTVector(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    ASTVector(Context ctx)
    {
        super(ctx, Native.mkAstVector(ctx.nCtx()));
    }

    void incRef(long o)
    {
        getContext().getASTVectorDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o)
    {
        getContext().getASTVectorDRQ().add(o);
        super.decRef(o);
    }
}
