/**
 * This file was automatically generated from ConstructorList.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Lists of constructors
 **/
public class ConstructorList extends Z3Object
{
	/**
	 * Destructor.
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
