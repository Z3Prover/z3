/**
 * This file was automatically generated from DatatypeSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Datatype sorts.
 **/
public class DatatypeSort extends Sort
{
	/**
	 * The number of constructors of the datatype sort.
	 **/
	public int NumConstructors() throws Z3Exception
	{
		return Native.getDatatypeSortNumConstructors(Context().nCtx(),
				NativeObject());
	}

	/**
	 * The constructors.
	 * 
	 * @throws Z3Exception
	 **/
	public FuncDecl[] Constructors() throws Z3Exception
	{
		int n = NumConstructors();
		FuncDecl[] res = new FuncDecl[n];
		for (int i = 0; i < n; i++)
			res[i] = new FuncDecl(Context(), Native.getDatatypeSortConstructor(
					Context().nCtx(), NativeObject(), i));
		return res;
	}

	/**
	 * The recognizers.
	 * 
	 * @throws Z3Exception
	 **/
	public FuncDecl[] Recognizers() throws Z3Exception
	{
		int n = NumConstructors();
		FuncDecl[] res = new FuncDecl[n];
		for (int i = 0; i < n; i++)
			res[i] = new FuncDecl(Context(), Native.getDatatypeSortRecognizer(
					Context().nCtx(), NativeObject(), i));
		return res;
	}

	/**
	 * The constructor accessors.
	 * 
	 * @throws Z3Exception
	 **/
	public FuncDecl[][] Accessors() throws Z3Exception
	{

		int n = NumConstructors();
		FuncDecl[][] res = new FuncDecl[n][];
		for (int i = 0; i < n; i++)
		{
			FuncDecl fd = new FuncDecl(Context(),
					Native.getDatatypeSortConstructor(Context().nCtx(),
							NativeObject(), i));
			int ds = fd.DomainSize();
			FuncDecl[] tmp = new FuncDecl[ds];
			for (int j = 0; j < ds; j++)
				tmp[j] = new FuncDecl(Context(),
						Native.getDatatypeSortConstructorAccessor(Context()
								.nCtx(), NativeObject(), i, j));
			res[i] = tmp;
		}
		return res;
	}

	DatatypeSort(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	DatatypeSort(Context ctx, Symbol name, Constructor[] constructors)
			throws Z3Exception
	{
		super(ctx, Native.mkDatatype(ctx.nCtx(), name.NativeObject(),
				(int) constructors.length, ArrayToNative(constructors)));

	}
};
