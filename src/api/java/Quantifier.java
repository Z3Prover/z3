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
    public boolean isUniversal()
    {
        return Native.isQuantifierForall(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the quantifier is existential.
     **/
    public boolean isExistential()
    {
        return Native.isQuantifierExists(getContext().nCtx(), getNativeObject());
    }

    /**
     * The weight of the quantifier.
     **/
    public int getWeight()
    {
        return Native.getQuantifierWeight(getContext().nCtx(), getNativeObject());
    }

    /**
     * The number of patterns.
     **/
    public int getNumPatterns()
    {
        return Native
                .getQuantifierNumPatterns(getContext().nCtx(), getNativeObject());
    }

    /**
     * The patterns.
     * 
     * @throws Z3Exception
     **/
    public Pattern[] getPatterns()
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
    public int getNumNoPatterns()
    {
        return Native.getQuantifierNumNoPatterns(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * The no-patterns.
     * 
     * @throws Z3Exception
     **/
    public Pattern[] getNoPatterns()
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
    public int getNumBound()
    {
        return Native.getQuantifierNumBound(getContext().nCtx(), getNativeObject());
    }

    /**
     * The symbols for the bound variables.
     * 
     * @throws Z3Exception
     **/
    public Symbol[] getBoundVariableNames()
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
    public Sort[] getBoundVariableSorts()
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
    public BoolExpr getBody()
    {
        return (BoolExpr) Expr.create(getContext(), Native.getQuantifierBody(getContext()
                .nCtx(), getNativeObject()));
    }

    /**
     * Translates (copies) the quantifier to the Context {@code ctx}.
     * 
     * @param ctx A context
     * 
     * @return A copy of the quantifier which is associated with {@code ctx}
     * @throws Z3Exception on error
     **/
    public Quantifier translate(Context ctx)
    {
        return (Quantifier) super.translate(ctx);
    }

    /**
     * Create a quantified expression.
     *
     * @param patterns Nullable patterns
     * @param noPatterns Nullable noPatterns
     * @param quantifierID Nullable quantifierID
     * @param skolemID Nullable skolemID
     */
    public static Quantifier of(
            Context ctx, boolean isForall, Sort[] sorts, Symbol[] names,
            Expr<BoolSort> body, int weight, Pattern[] patterns, Expr<?>[] noPatterns,
            Symbol quantifierID, Symbol skolemID) {
        ctx.checkContextMatch(patterns);
        ctx.checkContextMatch(noPatterns);
        ctx.checkContextMatch(sorts);
        ctx.checkContextMatch(names);
        ctx.checkContextMatch(body);

        if (sorts.length != names.length) {
            throw new Z3Exception(
                    "Number of sorts does not match number of names");
        }

        long nativeObj;
        if (noPatterns == null && quantifierID == null && skolemID == null) {
            nativeObj = Native.mkQuantifier(ctx.nCtx(), (isForall), weight, AST.arrayLength(patterns), AST
                    .arrayToNative(patterns), AST.arrayLength(sorts), AST
                    .arrayToNative(sorts), Symbol.arrayToNative(names), body
                    .getNativeObject());
        } else {
            nativeObj = Native.mkQuantifierEx(ctx.nCtx(),
                    (isForall), weight, AST.getNativeObject(quantifierID),
                    AST.getNativeObject(skolemID),
                    AST.arrayLength(patterns), AST.arrayToNative(patterns),
                    AST.arrayLength(noPatterns), AST.arrayToNative(noPatterns),
                    AST.arrayLength(sorts), AST.arrayToNative(sorts),
                    Symbol.arrayToNative(names),
                    body.getNativeObject());
        }
        return new Quantifier(ctx, nativeObj);
    }


    /**
     * @param ctx Context to create the quantifier on.
     * @param isForall Quantifier type.
     * @param bound Bound variables.
     * @param body Body of the quantifier.
     * @param weight Weight.
     * @param patterns Nullable array of patterns.
     * @param noPatterns Nullable array of noPatterns.
     * @param quantifierID Nullable quantifier identifier.
     * @param skolemID Nullable skolem identifier.
     */
    public static Quantifier of(Context ctx, boolean isForall, Expr<?>[] bound, Expr<BoolSort> body,
            int weight, Pattern[] patterns, Expr<?>[] noPatterns,
            Symbol quantifierID, Symbol skolemID) {
        ctx.checkContextMatch(noPatterns);
        ctx.checkContextMatch(patterns);
        ctx.checkContextMatch(body);

        long nativeObj;
        if (noPatterns == null && quantifierID == null && skolemID == null) {
            nativeObj = Native.mkQuantifierConst(ctx.nCtx(),
                isForall, weight, AST.arrayLength(bound),
                    AST.arrayToNative(bound), AST.arrayLength(patterns),
                    AST.arrayToNative(patterns), body.getNativeObject());
        } else {
            nativeObj = Native.mkQuantifierConstEx(ctx.nCtx(),
                isForall, weight,
                    AST.getNativeObject(quantifierID),
                    AST.getNativeObject(skolemID), AST.arrayLength(bound),
                    AST.arrayToNative(bound), AST.arrayLength(patterns),
                    AST.arrayToNative(patterns), AST.arrayLength(noPatterns),
                    AST.arrayToNative(noPatterns), body.getNativeObject());
        }
        return new Quantifier(ctx, nativeObj);
    }

    Quantifier(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void checkNativeObject(long obj) {
        if (Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_QUANTIFIER_AST
                .toInt()) {
            throw new Z3Exception("Underlying object is not a quantifier");
        }
        super.checkNativeObject(obj);
    }
}
