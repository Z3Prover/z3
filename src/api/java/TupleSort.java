/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    TupleSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Tuple sorts.
 **/
public class TupleSort extends Sort
{
    /**
     * The constructor function of the tuple.
     * @throws Z3Exception 
     **/
    public FuncDecl<TupleSort> mkDecl()
    {

        return new FuncDecl<>(getContext(), Native.getTupleSortMkDecl(getContext()
                .nCtx(), getNativeObject()));
    }

    /**
     * The number of fields in the tuple.
     **/
    public int getNumFields()
    {
        return Native.getTupleSortNumFields(getContext().nCtx(), getNativeObject());
    }

    /**
     * The field declarations.
     * @throws Z3Exception 
     **/
    public FuncDecl<?>[] getFieldDecls()
    {

        int n = getNumFields();
        FuncDecl<?>[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl<>(getContext(), Native.getTupleSortFieldDecl(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    TupleSort(Context ctx, Symbol name, int numFields, Symbol[] fieldNames,
            Sort[] fieldSorts)
    {
        super(ctx, Native.mkTupleSort(ctx.nCtx(), name.getNativeObject(),
                numFields, Symbol.arrayToNative(fieldNames),
                AST.arrayToNative(fieldSorts), new Native.LongPtr(),
                new long[numFields]));
    }
};
