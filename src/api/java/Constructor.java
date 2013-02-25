/**
 * This file was automatically generated from Constructor.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Constructors are used for datatype sorts.
 **/
public class Constructor extends Z3Object
{
	/**
	 * The number of fields of the constructor.
	 * @throws Z3Exception 
	 **/
	public int getNumFields() throws Z3Exception
	{	
		return n;
	}

	/**
	 * The function declaration of the constructor.
	 * @throws Z3Exception 
	 **/
	public FuncDecl ConstructorDecl() throws Z3Exception
	{
	    Native.LongPtr constructor = new Native.LongPtr();
	    Native.LongPtr tester = new Native.LongPtr();
	    long[] accessors = new long[n];
        Native.queryConstructor(getContext().nCtx(), getNativeObject(), n, constructor, tester, accessors);
        return new FuncDecl(getContext(), constructor.value);         
	}

	/**
	 * The function declaration of the tester.
	 * @throws Z3Exception 
	 **/
	public FuncDecl getTesterDecl() throws Z3Exception
	{
	    Native.LongPtr constructor = new Native.LongPtr();
        Native.LongPtr tester = new Native.LongPtr();
        long[] accessors = new long[n];
        Native.queryConstructor(getContext().nCtx(), getNativeObject(), n, constructor, tester, accessors);
        return new FuncDecl(getContext(), tester.value);
	}

	/**
	 * The function declarations of the accessors
	 * @throws Z3Exception 
	 **/
	public FuncDecl[] getAccessorDecls() throws Z3Exception
	{
	    Native.LongPtr constructor = new Native.LongPtr();
        Native.LongPtr tester = new Native.LongPtr();
        long[] accessors = new long[n];
        Native.queryConstructor(getContext().nCtx(), getNativeObject(), n, constructor, tester, accessors);
        FuncDecl[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl(getContext(), accessors[i]); 
        return t;
	}

	/**
	 * Destructor.
	 **/
	protected void finalize() throws Z3Exception
	{
		Native.delConstructor(getContext().nCtx(), getNativeObject());
	}

	private int n = 0;

	Constructor(Context ctx, Symbol name, Symbol recognizer,
			Symbol[] fieldNames, Sort[] sorts, int[] sortRefs)
			throws Z3Exception
	{
		super(ctx);

		n = AST.arrayLength(fieldNames);

		if (n != AST.arrayLength(sorts))
			throw new Z3Exception(
					"Number of field names does not match number of sorts");
		if (sortRefs != null && sortRefs.length != n)
			throw new Z3Exception(
					"Number of field names does not match number of sort refs");

		if (sortRefs == null)
			sortRefs = new int[n];

		setNativeObject(Native.mkConstructor(ctx.nCtx(), name.getNativeObject(),
				recognizer.getNativeObject(), n, Symbol.arrayToNative(fieldNames),
				Sort.arrayToNative(sorts), sortRefs));

	}
}
