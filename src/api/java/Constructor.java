/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Constructor.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Constructors are used for datatype sorts.
 **/
public class Constructor<R> extends Z3Object {
    private final int n;

    Constructor(Context ctx, int n, long nativeObj) {
        super(ctx, nativeObj);
        this.n = n;
    }

    /**
     * The number of fields of the constructor.
     * @throws Z3Exception 
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getNumFields()
    {    
        return n;
    }

    /**
     * The function declaration of the constructor.
     * @throws Z3Exception 
     * @throws Z3Exception on error
     **/
    public FuncDecl<DatatypeSort<R>> ConstructorDecl()
    {
        Native.LongPtr constructor = new Native.LongPtr();
        Native.LongPtr tester = new Native.LongPtr();
        long[] accessors = new long[n];
        Native.queryConstructor(getContext().nCtx(), getNativeObject(), n, constructor, tester, accessors);
        return new FuncDecl<>(getContext(), constructor.value);
    }

    /**
     * The function declaration of the tester.
     * @throws Z3Exception 
     * @throws Z3Exception on error
     **/
    public FuncDecl<BoolSort> getTesterDecl()
    {
        Native.LongPtr constructor = new Native.LongPtr();
        Native.LongPtr tester = new Native.LongPtr();
        long[] accessors = new long[n];
        Native.queryConstructor(getContext().nCtx(), getNativeObject(), n, constructor, tester, accessors);
        return new FuncDecl<>(getContext(), tester.value);
    }

    /**
     * The function declarations of the accessors
     * @throws Z3Exception 
     * @throws Z3Exception on error
     **/
    public FuncDecl<?>[] getAccessorDecls()
    {
        Native.LongPtr constructor = new Native.LongPtr();
        Native.LongPtr tester = new Native.LongPtr();
        long[] accessors = new long[n];
        Native.queryConstructor(getContext().nCtx(), getNativeObject(), n, constructor, tester, accessors);
        FuncDecl<?>[] t = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            t[i] = new FuncDecl<>(getContext(), accessors[i]);
        return t;
    }

    @Override
    void incRef() {
        // Datatype constructors are not reference counted.
    }

    @Override
    void addToReferenceQueue() {
        getContext().getConstructorDRQ().storeReference(getContext(), this);
    }

    static <R> Constructor<R> of(Context ctx, Symbol name, Symbol recognizer,
            Symbol[] fieldNames, Sort[] sorts, int[] sortRefs) {
        int n = AST.arrayLength(fieldNames);

        if (n != AST.arrayLength(sorts))
            throw new Z3Exception(
                    "Number of field names does not match number of sorts");
        if (sortRefs != null && sortRefs.length != n)
            throw new Z3Exception(
                    "Number of field names does not match number of sort refs");

        if (sortRefs == null)
            sortRefs = new int[n];

        long nativeObj = Native.mkConstructor(ctx.nCtx(), name.getNativeObject(),
                recognizer.getNativeObject(), n, Symbol.arrayToNative(fieldNames),
                Sort.arrayToNative(sorts), sortRefs);
        return new Constructor<>(ctx, n, nativeObj);

    }
}
