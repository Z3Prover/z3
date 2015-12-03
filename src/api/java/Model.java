/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Model.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_sort_kind;

/**
 * A Model contains interpretations (assignments) of constants and functions.
 **/
public class Model extends Z3Object
{
    /**
     * Retrieves the interpretation (the assignment) of {@code a} in
     * the model. 
     * @param a A Constant
     * 
     * @return An expression if the constant has an interpretation in the model,
     *         null otherwise.
     * @throws Z3Exception
     **/
    public Expr getConstInterp(Expr a)
    {
        getContext().checkContextMatch(a);
        return getConstInterp(a.getFuncDecl());
    }

    /**
     * Retrieves the interpretation (the assignment) of {@code f} in
     * the model. 
     * @param f A function declaration of zero arity
     * 
     * @return An expression if the function has an interpretation in the model,
     *         null otherwise.
     * @throws Z3Exception
     **/
    public Expr getConstInterp(FuncDecl f)
    {
        getContext().checkContextMatch(f);
        if (f.getArity() != 0
                || Native.getSortKind(getContext().nCtx(),
                        Native.getRange(getContext().nCtx(), f.getNativeObject())) == Z3_sort_kind.Z3_ARRAY_SORT
                        .toInt())
            throw new Z3Exception(
                    "Non-zero arity functions and arrays have FunctionInterpretations as a model. Use getFuncInterp.");

        long n = Native.modelGetConstInterp(getContext().nCtx(), getNativeObject(),
                f.getNativeObject());
        if (n == 0)
            return null;
        else
            return Expr.create(getContext(), n);
    }

    /**
     * Retrieves the interpretation (the assignment) of a non-constant {@code f} in the model. 
     * @param f A function declaration of non-zero arity
     * 
     * @return A FunctionInterpretation if the function has an interpretation in
     *         the model, null otherwise.
     * @throws Z3Exception
     **/
    public FuncInterp getFuncInterp(FuncDecl f)
    {
        getContext().checkContextMatch(f);

        Z3_sort_kind sk = Z3_sort_kind.fromInt(Native.getSortKind(getContext()
                .nCtx(), Native.getRange(getContext().nCtx(), f.getNativeObject())));

        if (f.getArity() == 0)
        {
            long n = Native.modelGetConstInterp(getContext().nCtx(),
                    getNativeObject(), f.getNativeObject());

            if (sk == Z3_sort_kind.Z3_ARRAY_SORT)
            {
                if (n == 0)
                    return null;
                else
                {
                    if (Native.isAsArray(getContext().nCtx(), n) ^ true)
                        throw new Z3Exception(
                                "Argument was not an array constant");
                    long fd = Native.getAsArrayFuncDecl(getContext().nCtx(), n);
                    return getFuncInterp(new FuncDecl(getContext(), fd));
                }
            } else
            {
                throw new Z3Exception(
                        "Constant functions do not have a function interpretation; use getConstInterp");
            }
        } else
        {
            long n = Native.modelGetFuncInterp(getContext().nCtx(),
                    getNativeObject(), f.getNativeObject());
            if (n == 0)
                return null;
            else
                return new FuncInterp(getContext(), n);
        }
    }

    /**
     * The number of constants that have an interpretation in the model.
     **/
    public int getNumConsts()
    {
        return Native.modelGetNumConsts(getContext().nCtx(), getNativeObject());
    }

    /**
     * The function declarations of the constants in the model.
     * 
     * @throws Z3Exception
     **/
    public FuncDecl[] getConstDecls()
    {
        int n = getNumConsts();
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl(getContext(), Native.modelGetConstDecl(getContext()
                    .nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The number of function interpretations in the model.
     **/
    public int getNumFuncs()
    {
        return Native.modelGetNumFuncs(getContext().nCtx(), getNativeObject());
    }

    /**
     * The function declarations of the function interpretations in the model.
     * 
     * @throws Z3Exception
     **/
    public FuncDecl[] getFuncDecls()
    {
        int n = getNumFuncs();
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < n; i++)
            res[i] = new FuncDecl(getContext(), Native.modelGetFuncDecl(getContext()
                    .nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * All symbols that have an interpretation in the model.
     * 
     * @throws Z3Exception
     **/
    public FuncDecl[] getDecls()
    {
        int nFuncs = getNumFuncs();
        int nConsts = getNumConsts();
        int n = nFuncs + nConsts;
        FuncDecl[] res = new FuncDecl[n];
        for (int i = 0; i < nConsts; i++)
            res[i] = new FuncDecl(getContext(), Native.modelGetConstDecl(getContext()
                    .nCtx(), getNativeObject(), i));
        for (int i = 0; i < nFuncs; i++)
            res[nConsts + i] = new FuncDecl(getContext(), Native.modelGetFuncDecl(
                    getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * A ModelEvaluationFailedException is thrown when an expression cannot be
     * evaluated by the model.
     **/
    @SuppressWarnings("serial")
    public class ModelEvaluationFailedException extends Z3Exception
    {
        /**
         * An exception that is thrown when model evaluation fails.
         **/
        public ModelEvaluationFailedException()
        {
            super();
        }
    }

    /**
     * Evaluates the expression {@code t} in the current model.
     * Remarks:  This function may fail if {@code t} contains
     * quantifiers, is partial (MODEL_PARTIAL enabled), or if {@code t} is not well-sorted. In this case a
     * {@code ModelEvaluationFailedException} is thrown.  
	 * @param t the expression to evaluate
     * @param completion An expression {@code completion} When this flag
     * is enabled, a model value will be assigned to any constant or function
     * that does not have an interpretation in the model.

     * @return The evaluation of {@code t} in the model.
     * @throws Z3Exception
     **/
    public Expr eval(Expr t, boolean completion)
    {
        Native.LongPtr v = new Native.LongPtr();
        if (Native.modelEval(getContext().nCtx(), getNativeObject(),
                t.getNativeObject(), (completion) ? true : false, v) ^ true)
            throw new ModelEvaluationFailedException();
        else
            return Expr.create(getContext(), v.value);
    }

    /**
     * Alias for {@code Eval}.
     * 
     * @throws Z3Exception
     **/
    public Expr evaluate(Expr t, boolean completion)
    {
        return eval(t, completion);
    }

    /**
     * The number of uninterpreted sorts that the model has an interpretation
     * for.
     **/
    public int getNumSorts()
    {
        return Native.modelGetNumSorts(getContext().nCtx(), getNativeObject());
    }

    /**
     * The uninterpreted sorts that the model has an interpretation for.
     * Remarks:  Z3 also provides an intepretation for uninterpreted sorts used
     * in a formula. The interpretation for a sort is a finite set of distinct
     * values. We say this finite set is the "universe" of the sort. 
     * 
     * @see getNumSorts
     * @see getSortUniverse
     * 
     * @throws Z3Exception
     **/
    public Sort[] getSorts()
    {

        int n = getNumSorts();
        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.create(getContext(),
                    Native.modelGetSort(getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The finite set of distinct values that represent the interpretation for
     * sort {@code s}. 
     * @param s An uninterpreted sort
     * 
     * @return An array of expressions, where each is an element of the universe
     *         of {@code s}
     * @throws Z3Exception
     **/
    public Expr[] getSortUniverse(Sort s)
    {

        ASTVector nUniv = new ASTVector(getContext(), Native.modelGetSortUniverse(
                getContext().nCtx(), getNativeObject(), s.getNativeObject()));
        return nUniv.ToExprArray();
    }

    /**
     * Conversion of models to strings.
     * 
     * @return A string representation of the model.
     **/
    public String toString()
    {
        try
        {
            return Native.modelToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    Model(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    void incRef(long o)
    {
        getContext().getModelDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o)
    {
        getContext().getModelDRQ().add(o);
        super.decRef(o);
    }
}
