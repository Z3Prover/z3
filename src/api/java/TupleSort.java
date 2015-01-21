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
    public FuncDecl mkDecl() throws Z3Exception
    {

        return new FuncDecl(getContext(), Native.getTupleSortMkDecl(getContext()
                .nCtx(), getNativeObject()));
    }

    /**
     * The number of fields in the tuple.
     **/
    public int getNumFields() throws Z3Exception
    {
        return Native.getTupleSortNumFields(getContext().nCtx(), getNativeObject());
    }

    /**
     * The field declarations.
     * @throws Z3Exception 
     **/
    public FuncDecl[] getFieldDecls() throws Z3Exception
    {

        int n = getNumFields();
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl(getContext(), Native.getTupleSortFieldDecl(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    TupleSort(Context ctx, Symbol name, int numFields, Symbol[] fieldNames,
            Sort[] fieldSorts) throws Z3Exception
    {
        super(ctx, 0);

        Native.LongPtr t = new Native.LongPtr();
        setNativeObject(Native.mkTupleSort(ctx.nCtx(), name.getNativeObject(),
                numFields, Symbol.arrayToNative(fieldNames),
                AST.arrayToNative(fieldSorts), t, new long[numFields]));
    }
};
