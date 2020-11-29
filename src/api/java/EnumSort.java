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
@SuppressWarnings("unchecked")
public class EnumSort<R> extends Sort
{
    /**
     * The function declarations of the constants in the enumeration.
     * @throws Z3Exception on error
     **/
    public FuncDecl<EnumSort<R>>[] getConstDecls()
    {
        int n = Native.getDatatypeSortNumConstructors(getContext().nCtx(), getNativeObject());
        FuncDecl<?>[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl<>(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), i));
        return (FuncDecl<EnumSort<R>>[]) t;
    }
    
    /**
     * Retrieves the inx'th constant declaration in the enumeration.
     * @throws Z3Exception on error
     **/
    public FuncDecl<EnumSort<R>> getConstDecl(int inx)
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), inx));
    }

    /**
     * The constants in the enumeration.
     * @throws Z3Exception on error
     * @return an Expr[]
     **/
    public Expr<EnumSort<R>>[] getConsts()
    {        
        FuncDecl<?>[] cds = getConstDecls();
        Expr<?>[] t = new Expr[cds.length];
        for (int i = 0; i < t.length; i++)
            t[i] = getContext().mkApp(cds[i]);
        return (Expr<EnumSort<R>>[]) t;
    }
    
    /**
     * Retrieves the inx'th constant in the enumeration.
     * @throws Z3Exception on error
     * @return an Expr
     **/
    public Expr<EnumSort<R>> getConst(int inx)
    {        
        return getContext().mkApp(getConstDecl(inx));
    }

    /**
     * The test predicates for the constants in the enumeration.
     * @throws Z3Exception on error
     **/
    @SuppressWarnings("unchecked")
    public FuncDecl<BoolSort>[] getTesterDecls()
    {
        int n = Native.getDatatypeSortNumConstructors(getContext().nCtx(), getNativeObject());
        FuncDecl<BoolSort>[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl<>(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), i));
        return t;
    }
    
    /**
     * Retrieves the inx'th tester/recognizer declaration in the enumeration.
     * @throws Z3Exception on error
     **/
    public FuncDecl<BoolSort> getTesterDecl(int inx)
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), inx));
    }

    EnumSort(Context ctx, Symbol name, Symbol[] enumNames)
    {
        super(ctx, Native.mkEnumerationSort(ctx.nCtx(),
                name.getNativeObject(), enumNames.length,
                Symbol.arrayToNative(enumNames),
                new long[enumNames.length], new long[enumNames.length]));
    }
};
