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
	public int Size()
	{
		return Native.astVectorSize(Context().nCtx(), NativeObject());
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
		return new AST(Context(), Native.astVectorGet(Context().nCtx(),
				NativeObject(), i));
	}

	public void set(int i, AST value)
	{

		Native.astVectorSet(Context().nCtx(), NativeObject(), i,
				value.NativeObject());
	}

	/**
	 * Resize the vector to <paramref name="newSize"/>. <param
	 * name="newSize">The new size of the vector.</param>
	 **/
	public void Resize(int newSize)
	{
		Native.astVectorResize(Context().nCtx(), NativeObject(), newSize);
	}

	/**
	 * Add the AST <paramref name="a"/> to the back of the vector. The size is
	 * increased by 1. <param name="a">An AST</param>
	 **/
	public void Push(AST a)
	{

		Native.astVectorPush(Context().nCtx(), NativeObject(), a.NativeObject());
	}

	/**
	 * Translates all ASTs in the vector to <paramref name="ctx"/>. <param
	 * name="ctx">A context</param>
	 * 
	 * @return A new ASTVector
	 * @throws Z3Exception
	 **/
	public ASTVector Translate(Context ctx) throws Z3Exception
	{
		return new ASTVector(Context(), Native.astVectorTranslate(Context()
				.nCtx(), NativeObject(), ctx.nCtx()));
	}

	/**
	 * Retrieves a string representation of the vector.
	 **/
	public String toString()
	{
		return Native.astVectorToString(Context().nCtx(), NativeObject());
	}

	ASTVector(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	ASTVector(Context ctx) throws Z3Exception
	{
		super(ctx, Native.mkAstVector(ctx.nCtx()));
	}

	void IncRef(long o) throws Z3Exception
	{
		Context().ASTVector_DRQ().IncAndClear(Context(), o);
		super.IncRef(o);
	}

	void DecRef(long o) throws Z3Exception
	{
		Context().ASTVector_DRQ().Add(o);
		super.DecRef(o);
	}
}
