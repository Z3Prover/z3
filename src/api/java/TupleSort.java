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
    public FuncDecl MkDecl() throws Z3Exception
    {

        return new FuncDecl(Context(), Native.getTupleSortMkDecl(Context()
                .nCtx(), NativeObject()));
    }

    /**
     * The number of fields in the tuple.
     **/
    public int NumFields()
    {
        return Native.getTupleSortNumFields(Context().nCtx(), NativeObject());
    }

    /**
     * The field declarations.
     * @throws Z3Exception 
     **/
    public FuncDecl[] FieldDecls() throws Z3Exception
    {

        int n = NumFields();
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl(Context(), Native.getTupleSortFieldDecl(
                    Context().nCtx(), NativeObject(), i));
        return res;
    }

    TupleSort(Context ctx, Symbol name, int numFields, Symbol[] fieldNames,
            Sort[] fieldSorts) throws Z3Exception
    {
        super(ctx);

        Native.LongPtr t = new Native.LongPtr();
        setNativeObject(Native.mkTupleSort(ctx.nCtx(), name.NativeObject(),
                numFields, Symbol.ArrayToNative(fieldNames),
                AST.ArrayToNative(fieldSorts), t, new long[numFields]));
    }
};
