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
	public boolean Contains(AST k)
	{

		return Native.astMapContains(Context().nCtx(), NativeObject(),
				k.NativeObject());
	}

	/**
	 * Finds the value associated with the key <paramref name="k"/>. <remarks>
	 * This function signs an error when <paramref name="k"/> is not a key in
	 * the map. </remarks> <param name="k">An AST</param>
	 * @throws Z3Exception 
	 **/
	public AST Find(AST k) throws Z3Exception
	{
		return new AST(Context(), Native.astMapFind(Context().nCtx(),
				NativeObject(), k.NativeObject()));
	}

	/**
	 * Stores or replaces a new key/value pair in the map. <param name="k">The
	 * key AST</param> <param name="v">The value AST</param>
	 **/
	public void Insert(AST k, AST v)
	{

		Native.astMapInsert(Context().nCtx(), NativeObject(), k.NativeObject(),
				v.NativeObject());
	}

	/**
	 * Erases the key <paramref name="k"/> from the map. <param name="k">An
	 * AST</param>
	 **/
	public void Erase(AST k)
	{

		Native.astMapErase(Context().nCtx(), NativeObject(), k.NativeObject());
	}

	/**
	 * Removes all keys from the map.
	 **/
	public void Reset()
	{
		Native.astMapReset(Context().nCtx(), NativeObject());
	}

	/**
	 * The size of the map
	 **/
	public int Size()
	{
		return Native.astMapSize(Context().nCtx(), NativeObject());
	}

	/**
	 * The keys stored in the map.
	 * @throws Z3Exception 
	 **/
	public ASTVector Keys() throws Z3Exception
	{
		return new ASTVector(Context(), Native.astMapKeys(Context().nCtx(),
				NativeObject()));
	}

	/**
	 * Retrieves a string representation of the map.
	 **/
	public String toString()
	{
		return Native.astMapToString(Context().nCtx(), NativeObject());
	}

	ASTMap(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	ASTMap(Context ctx) throws Z3Exception
	{
		super(ctx, Native.mkAstMap(ctx.nCtx()));
	}

	void IncRef(long o) throws Z3Exception
	{
		Context().ASTMap_DRQ().IncAndClear(Context(), o);
		super.IncRef(o);
	}

	void DecRef(long o) throws Z3Exception
	{
		Context().ASTMap_DRQ().Add(o);
		super.DecRef(o);
	}
}
