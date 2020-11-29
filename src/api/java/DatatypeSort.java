/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    DatatypeSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Datatype sorts.
 **/
public class DatatypeSort<R> extends Sort
{
    /**
     * The number of constructors of the datatype sort.
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getNumConstructors()
    {
        return Native.getDatatypeSortNumConstructors(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * The constructors.
     * 
     * @throws Z3Exception
     * @throws Z3Exception on error
     **/
    @SuppressWarnings("unchecked")
    public FuncDecl<DatatypeSort<R>>[] getConstructors()
    {
        int n = getNumConstructors();
        FuncDecl<DatatypeSort<R>>[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl<>(getContext(), Native.getDatatypeSortConstructor(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The recognizers.
     * 
     * @throws Z3Exception
     * @throws Z3Exception on error
     **/
    @SuppressWarnings("unchecked")
    public FuncDecl<BoolSort>[] getRecognizers()
    {
        int n = getNumConstructors();
        FuncDecl<BoolSort>[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl<>(getContext(), Native.getDatatypeSortRecognizer(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The constructor accessors.
     * 
     * @throws Z3Exception
     * @throws Z3Exception on error
     **/
    public FuncDecl<?>[][] getAccessors()
    {

        int n = getNumConstructors();
        FuncDecl<?>[][] res = new FuncDecl[n][];
        for (int i = 0; i < n; i++)
        {
            FuncDecl<?> fd = new FuncDecl<>(getContext(),
                    Native.getDatatypeSortConstructor(getContext().nCtx(),
                            getNativeObject(), i));
            int ds = fd.getDomainSize();
            FuncDecl<?>[] tmp = new FuncDecl[ds];
            for (int j = 0; j < ds; j++)
                tmp[j] = new FuncDecl<>(getContext(),
                        Native.getDatatypeSortConstructorAccessor(getContext()
                                .nCtx(), getNativeObject(), i, j));
            res[i] = tmp;
        }
        return res;
    }

    DatatypeSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    DatatypeSort(Context ctx, Symbol name, Constructor<R>[] constructors)
           
    {
        super(ctx, Native.mkDatatype(ctx.nCtx(), name.getNativeObject(),
                constructors.length, arrayToNative(constructors)));

    }
};
