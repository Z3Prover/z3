/**
 * This file was automatically generated from EnumSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Enumeration sorts.
 **/
public class EnumSort extends Sort
{
	/**
	 * The function declarations of the constants in the enumeration.
	 **/
	public FuncDecl[] getConstDecls() throws Z3Exception
	{
	    int n = Native.getDatatypeSortNumConstructors(getContext().nCtx(), getNativeObject());
        FuncDecl[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), i));
        return t;
	}

	/**
	 * The constants in the enumeration.
	 **/
	public Expr[] getConsts() throws Z3Exception
	{	    
	    FuncDecl[] cds = getConstDecls();
        Expr[] t = new Expr[cds.length];
        for (int i = 0; i < t.length; i++)
            t[i] = getContext().mkApp(cds[i]);
        return t;
	}

	/**
	 * The test predicates for the constants in the enumeration.
	 **/
	public FuncDecl[] getTesterDecls() throws Z3Exception
	{
	    int n = Native.getDatatypeSortNumConstructors(getContext().nCtx(), getNativeObject());
        FuncDecl[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), i));
        return t;
	}

	EnumSort(Context ctx, Symbol name, Symbol[] enumNames) throws Z3Exception
	{
		super(ctx);

		int n = enumNames.length;
		long[] n_constdecls = new long[n];
		long[] n_testers = new long[n];
		setNativeObject(Native.mkEnumerationSort(ctx.nCtx(),
				name.getNativeObject(), (int) n, Symbol.arrayToNative(enumNames),
				n_constdecls, n_testers));		
	}
};
