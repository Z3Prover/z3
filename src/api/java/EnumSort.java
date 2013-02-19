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
	public FuncDecl[] getConstDecls()
	{
		return _constdecls;
	}

	/**
	 * The constants in the enumeration.
	 **/
	public Expr[] getConsts()
	{
		return _consts;
	}

	/**
	 * The test predicates for the constants in the enumeration.
	 **/
	public FuncDecl[] getTesterDecls()
	{
		return _testerdecls;
	}

	private FuncDecl[] _constdecls = null, _testerdecls = null;
	private Expr[] _consts = null;

	EnumSort(Context ctx, Symbol name, Symbol[] enumNames) throws Z3Exception
	{
		super(ctx);

		int n = enumNames.length;
		long[] n_constdecls = new long[n];
		long[] n_testers = new long[n];
		setNativeObject(Native.mkEnumerationSort(ctx.nCtx(),
				name.getNativeObject(), (int) n, Symbol.arrayToNative(enumNames),
				n_constdecls, n_testers));
		_constdecls = new FuncDecl[n];
		for (int i = 0; i < n; i++)
		    _constdecls[i] = new FuncDecl(ctx, n_constdecls[i]);
		_testerdecls = new FuncDecl[n];
		for (int i = 0; i < n; i++)
		    _testerdecls[i] = new FuncDecl(ctx, n_testers[i]);
		_consts = new Expr[n];
		for (int i = 0; i < n; i++)
		    _consts[i] = ctx.mkApp(_constdecls[i], (Expr[])null);
	}
};
