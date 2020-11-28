/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ListSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.Native.LongPtr;

/**
 * List sorts.
 **/
public class ListSort<R extends Sort> extends Sort
{
    /**
     * The declaration of the nil function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl<ListSort<R>> getNilDecl()
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), 0));
    }

    /**
     * The empty list.
     * @throws Z3Exception 
     **/
    public Expr<ListSort<R>> getNil()
    {
        return getContext().mkApp(getNilDecl());
    }

    /**
     * The declaration of the isNil function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl<BoolSort> getIsNilDecl()
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), 0));
    }

    /**
     * The declaration of the cons function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl<ListSort<R>> getConsDecl()
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), 1));
    }

    /**
     * The declaration of the isCons function of this list sort.
     * @throws Z3Exception 
     * 
     **/
    public FuncDecl<BoolSort> getIsConsDecl()
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), 1));
    }

    /**
     * The declaration of the head function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl<R> getHeadDecl()
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortConstructorAccessor(getContext().nCtx(), getNativeObject(), 1, 0));
    }

    /**
     * The declaration of the tail function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl<ListSort<R>> getTailDecl()
    {
        return new FuncDecl<>(getContext(), Native.getDatatypeSortConstructorAccessor(getContext().nCtx(), getNativeObject(), 1, 1));
    }

    ListSort(Context ctx, Symbol name, Sort elemSort)
    {
        super(ctx, Native.mkListSort(ctx.nCtx(), name.getNativeObject(),
                elemSort.getNativeObject(),
                new LongPtr(), new Native.LongPtr(), new LongPtr(),
                new LongPtr(), new LongPtr(), new LongPtr()));
    }
};
