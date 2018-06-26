/**
Copyright (c) 2017 Microsoft Corporation

Module Name:

    Lambda.java

Abstract:

    Z3 Java API: Lambda

Author:

    Christoph Wintersteiger (cwinter) 2012-03-19

Notes:

**/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;


/**
 * Lambda expressions.
*/public class Lambda extends ArrayExpr
{

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
        return new BoolExpr(getContext(), Native.getQuantifierBody(getContext()
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
    public Lambda translate(Context ctx)
    {
        return (Lambda) super.translate(ctx);
    }
    
       
    public static Lambda of(Context ctx, Sort[] sorts, Symbol[] names, Expr body) 
    {
        ctx.checkContextMatch(sorts);
        ctx.checkContextMatch(names);
        ctx.checkContextMatch(body);
	
        if (sorts.length != names.length) 
            throw new Z3Exception("Number of sorts does not match number of names");
	
	
	long nativeObject = Native.mkLambda(ctx.nCtx(), 
					    AST.arrayLength(sorts), AST.arrayToNative(sorts),
					    Symbol.arrayToNative(names),
					    body.getNativeObject());
	
        return new Lambda(ctx, nativeObject);
    }

    /**
     * @param ctx Context to create the lambda on.
     * @param bound Bound variables.
     * @param body Body of the lambda expression.
     */

    public static Lambda of(Context ctx, Expr[] bound, Expr body) {
        ctx.checkContextMatch(body);

              
       long nativeObject = Native.mkLambdaConst(ctx.nCtx(),
					   AST.arrayLength(bound), AST.arrayToNative(bound),
					   body.getNativeObject());
       return new Lambda(ctx, nativeObject);
   }


    private Lambda(Context ctx, long obj)
    {
        super(ctx, obj);
    }

}
