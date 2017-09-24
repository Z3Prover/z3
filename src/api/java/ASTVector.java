/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ASTVector.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Vectors of ASTs.
 **/
public class ASTVector extends Z3Object {
    /**
     * The size of the vector
     **/
    public int size()
    {
        return Native.astVectorSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieves the i-th object in the vector.
     * Remarks: May throw an {@code IndexOutOfBoundsException} when 
     * {@code i} is out of range. 
     * @param i Index
     * 
     * @return An AST
     * @throws Z3Exception
     **/
    public AST get(int i)
    {
        return new AST(getContext(), Native.astVectorGet(getContext().nCtx(),
                getNativeObject(), i));
    }

    public void set(int i, AST value)
    {

        Native.astVectorSet(getContext().nCtx(), getNativeObject(), i,
                value.getNativeObject());
    }

    /**
     * Resize the vector to {@code newSize}. 
     * @param newSize The new size of the vector.
     **/
    public void resize(int newSize)
    {
        Native.astVectorResize(getContext().nCtx(), getNativeObject(), newSize);
    }

    /**
     * Add the AST {@code a} to the back of the vector. The size is
     * increased by 1. 
     * @param a An AST
     **/
    public void push(AST a)
    {
        Native.astVectorPush(getContext().nCtx(), getNativeObject(), a.getNativeObject());
    }

    /**
     * Translates all ASTs in the vector to {@code ctx}. 
     * @param ctx A context
     * 
     * @return A new ASTVector
     * @throws Z3Exception
     **/
    public ASTVector translate(Context ctx)
    {
        return new ASTVector(getContext(), Native.astVectorTranslate(getContext()
                .nCtx(), getNativeObject(), ctx.nCtx()));
    }

    /**
     * Retrieves a string representation of the vector.
     **/
    @Override
    public String toString() {
        return Native.astVectorToString(getContext().nCtx(), getNativeObject());
    }

    ASTVector(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    ASTVector(Context ctx)
    {
        super(ctx, Native.mkAstVector(ctx.nCtx()));
    }

    @Override
    void incRef() {
        Native.astVectorIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getASTVectorDRQ().storeReference(getContext(), this);
    }

    /**
     * Translates the AST vector into an AST[]
     * */
    public AST[] ToArray()
    {
        int n = size();
        AST[] res = new AST[n];
        for (int i = 0; i < n; i++)
            res[i] = AST.create(getContext(), get(i).getNativeObject());
        return res;
    }
    
    /**
     * Translates the AST vector into an Expr[]
     * */
    public Expr[] ToExprArray() {
        int n = size();
        Expr[] res = new Expr[n];
        for (int i = 0; i < n; i++)
            res[i] = Expr.create(getContext(), get(i).getNativeObject());
        return res;    
    }

    /**
     * Translates the AST vector into an BoolExpr[]
     * */  
    public BoolExpr[] ToBoolExprArray()
    {
        int n = size();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (BoolExpr) Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an BitVecExpr[]
     * */    
    public BitVecExpr[] ToBitVecExprArray()
    {
        int n = size();
        BitVecExpr[] res = new BitVecExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (BitVecExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an ArithExpr[]
     * */   
    public ArithExpr[] ToArithExprExprArray()
    {
        int n = size();
        ArithExpr[] res = new ArithExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (ArithExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an ArrayExpr[]
     * */  
    public ArrayExpr[] ToArrayExprArray()
    {
        int n = size();
        ArrayExpr[] res = new ArrayExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (ArrayExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an DatatypeExpr[]
     * */ 
    public DatatypeExpr[] ToDatatypeExprArray()
    {
        int n = size();
        DatatypeExpr[] res = new DatatypeExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (DatatypeExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an FPExpr[]
     * */   
    public FPExpr[] ToFPExprArray()
    {
        int n = size();
        FPExpr[] res = new FPExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (FPExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an FPRMExpr[]
     * */
    public FPRMExpr[] ToFPRMExprArray()
    {
        int n = size();
        FPRMExpr[] res = new FPRMExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (FPRMExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an IntExpr[]
     * */ 
    public IntExpr[] ToIntExprArray()
    {
        int n = size();
        IntExpr[] res = new IntExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (IntExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }

    /**
     * Translates the AST vector into an RealExpr[]
     * */   
    public RealExpr[] ToRealExprArray()
    {
        int n = size();
        RealExpr[] res = new RealExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = (RealExpr)Expr.create(getContext(), get(i).getNativeObject());
        return res;
    }
}