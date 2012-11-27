/**
 * This file was automatically generated from ConstructorList.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

/**
 * Lists of constructors
 **/
public class ConstructorList extends Z3Object
{
	/**
	 * Destructor.
	 **/
	protected void finalize()
	{
		Native.delConstructorList(Context().nCtx(), NativeObject());
	}

	ConstructorList(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	ConstructorList(Context ctx, Constructor[] constructors) throws Z3Exception
	{
		super(ctx);

		setNativeObject(Native.mkConstructorList(Context().nCtx(),
				(int) constructors.length,
				Constructor.ArrayToNative(constructors)));
	}
}
