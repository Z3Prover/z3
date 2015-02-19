/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Quantifier.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;

/**
 * Quantifier expressions.
 **/
public class Quantifier extends BoolExpr
{
    /**
     * Indicates whether the quantifier is universal.
     **/
    public boolean isUniversal() throws Z3Exception
    {
        return Native.isQuantifierForall(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the quantifier is existential.
     **/
    public boolean isExistential() throws Z3Exception
    {
        return !isUniversal();
    }

    /**
     * The weight of the quantifier.
     **/
    public int getWeight() throws Z3Exception
    {
        return Native.getQuantifierWeight(getContext().nCtx(), getNativeObject());
    }

    /**
     * The number of patterns.
     **/
    public int getNumPatterns() throws Z3Exception
    {
        return Native
                .getQuantifierNumPatterns(getContext().nCtx(), getNativeObject());
    }

    /**
     * The patterns.
     * 
     * @throws Z3Exception
     **/
    public Pattern[] getPatterns() throws Z3Exception
    {
        int n = getNumPatterns();
        Pattern[] res = new Pattern[n];
        for (int i = 0; i < n; i++)
            res[i] = new Pattern(getContext(), Native.getQuantifierPatternAst(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The number of no-patterns.
     **/
    public int getNumNoPatterns() throws Z3Exception
    {
        return Native.getQuantifierNumNoPatterns(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * The no-patterns.
     * 
     * @throws Z3Exception
     **/
    public Pattern[] getNoPatterns() throws Z3Exception
    {
        int n = getNumNoPatterns();
        Pattern[] res = new Pattern[n];
        for (int i = 0; i < n; i++)
            res[i] = new Pattern(getContext(), Native.getQuantifierNoPatternAst(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The number of bound variables.
     **/
    public int getNumBound() throws Z3Exception
    {
        return Native.getQuantifierNumBound(getContext().nCtx(), getNativeObject());
    }

    /**
     * The symbols for the bound variables.
     * 
     * @throws Z3Exception
     **/
    public Symbol[] getBoundVariableNames() throws Z3Exception
    {
        int n = getNumBound();
        Symbol[] res = new Symbol[n];
        for (int i = 0; i < n; i++)
            res[i] = Symbol.create(getContext(), Native.getQuantifierBoundName(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The sorts of the bound variables.
     * 
     * @throws Z3Exception
     **/
    public Sort[] getBoundVariableSorts() throws Z3Exception
    {
        int n = getNumBound();
        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.create(getContext(), Native.getQuantifierBoundSort(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The body of the quantifier.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr getBody() throws Z3Exception
    {
        return new BoolExpr(getContext(), Native.getQuantifierBody(getContext()
                .nCtx(), getNativeObject()));
    }

    Quantifier(Context ctx, boolean isForall, Sort[] sorts, Symbol[] names,
            Expr body, int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID) throws Z3Exception
    {
        super(ctx, 0);

        getContext().checkContextMatch(patterns);
        getContext().checkContextMatch(noPatterns);
        getContext().checkContextMatch(sorts);
        getContext().checkContextMatch(names);
        getContext().checkContextMatch(body);

        if (sorts.length != names.length)
            throw new Z3Exception(
                    "Number of sorts does not match number of names");

        if (noPatterns == null && quantifierID == null && skolemID == null)
        {
            setNativeObject(Native.mkQuantifier(ctx.nCtx(), (isForall) ? true
                    : false, weight, AST.arrayLength(patterns), AST
                    .arrayToNative(patterns), AST.arrayLength(sorts), AST
                    .arrayToNative(sorts), Symbol.arrayToNative(names), body
                    .getNativeObject()));
        } else
        {
            setNativeObject(Native.mkQuantifierEx(ctx.nCtx(), 
            (isForall) ? true : false, weight, AST.getNativeObject(quantifierID), 
             AST.getNativeObject(skolemID), 
             AST.arrayLength(patterns), AST.arrayToNative(patterns), 
             AST.arrayLength(noPatterns), AST.arrayToNative(noPatterns), 
             AST.arrayLength(sorts), AST.arrayToNative(sorts), 
             Symbol.arrayToNative(names), 
             body.getNativeObject()));
        }
    }

    Quantifier(Context ctx, boolean isForall, Expr[] bound, Expr body,
            int weight, Pattern[] patterns, Expr[] noPatterns,
            Symbol quantifierID, Symbol skolemID) throws Z3Exception
    {
        super(ctx, 0);

        getContext().checkContextMatch(noPatterns);
        getContext().checkContextMatch(patterns);
        // Context().CheckContextMatch(bound);
        getContext().checkContextMatch(body);

        if (noPatterns == null && quantifierID == null && skolemID == null)
        {
            setNativeObject(Native.mkQuantifierConst(ctx.nCtx(),
                    (isForall) ? true : false, weight, AST.arrayLength(bound),
                    AST.arrayToNative(bound), AST.arrayLength(patterns),
                    AST.arrayToNative(patterns), body.getNativeObject()));
        } else
        {
            setNativeObject(Native.mkQuantifierConstEx(ctx.nCtx(),
                    (isForall) ? true : false, weight,
                    AST.getNativeObject(quantifierID),
                    AST.getNativeObject(skolemID), AST.arrayLength(bound),
                    AST.arrayToNative(bound), AST.arrayLength(patterns),
                    AST.arrayToNative(patterns), AST.arrayLength(noPatterns),
                    AST.arrayToNative(noPatterns), body.getNativeObject()));
        }
    }

    Quantifier(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void checkNativeObject(long obj) throws Z3Exception
    {
        if (Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_QUANTIFIER_AST
                .toInt())
            throw new Z3Exception("Underlying object is not a quantifier");
        super.checkNativeObject(obj);
    }
}
