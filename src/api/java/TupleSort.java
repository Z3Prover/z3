/**
 * This file was automatically generated from TupleSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
        super(ctx);

        Native.LongPtr t = new Native.LongPtr();
        setNativeObject(Native.mkTupleSort(ctx.nCtx(), name.getNativeObject(),
                numFields, Symbol.arrayToNative(fieldNames),
                AST.arrayToNative(fieldSorts), t, new long[numFields]));
    }
};
