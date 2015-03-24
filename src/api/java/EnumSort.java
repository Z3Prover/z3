/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    EnumSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Enumeration sorts.
 **/
public class EnumSort extends Sort
{
    /**
     * The function declarations of the constants in the enumeration.
     * @throws Z3Exception on error
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
     * Retrieves the inx'th constant declaration in the enumeration.
     * @throws Z3Exception on error
     **/
    public FuncDecl getConstDecl(int inx) throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), inx));
    }

    /**
     * The constants in the enumeration.
     * @throws Z3Exception on error
     * @return an Expr[]
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
     * Retrieves the inx'th constant in the enumeration.
     * @throws Z3Exception on error
     * @return an Expr
     **/
    public Expr getConst(int inx) throws Z3Exception
    {        
    	return getContext().mkApp(getConstDecl(inx));
    }

    /**
     * The test predicates for the constants in the enumeration.
     * @throws Z3Exception on error
     **/
    public FuncDecl[] getTesterDecls() throws Z3Exception
    {
        int n = Native.getDatatypeSortNumConstructors(getContext().nCtx(), getNativeObject());
        FuncDecl[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), i));
        return t;
    }
    
    /**
     * Retrieves the inx'th tester/recognizer declaration in the enumeration.
     * @throws Z3Exception on error
     **/
    public FuncDecl getTesterDecl(int inx) throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), inx));
    }

    EnumSort(Context ctx, Symbol name, Symbol[] enumNames) throws Z3Exception
    {
        super(ctx, 0);

        int n = enumNames.length;
        long[] n_constdecls = new long[n];
        long[] n_testers = new long[n];
        setNativeObject(Native.mkEnumerationSort(ctx.nCtx(),
                name.getNativeObject(), (int) n, Symbol.arrayToNative(enumNames),
                n_constdecls, n_testers));        
    }
};
