/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Fixedpoint.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_lbool;

/**
 * Object for managing fixedpoints
 **/
public class Fixedpoint extends Z3Object
{

    /**
     * A string that describes all available fixedpoint solver parameters.
     **/
    public String getHelp()
    {
        return Native.fixedpointGetHelp(getContext().nCtx(), getNativeObject());
    }

    /**
     * Sets the fixedpoint solver parameters.
     * 
     * @throws Z3Exception
     **/
    public void setParameters(Params value)
    {

        getContext().checkContextMatch(value);
        Native.fixedpointSetParams(getContext().nCtx(), getNativeObject(),
                value.getNativeObject());
    }

    /**
     * Retrieves parameter descriptions for Fixedpoint solver.
     * 
     * @throws Z3Exception
     **/
    public ParamDescrs getParameterDescriptions()
    {
        return new ParamDescrs(getContext(), Native.fixedpointGetParamDescrs(
                getContext().nCtx(), getNativeObject()));
    }

    /**
     * Assert a constraint (or multiple) into the fixedpoint solver.
     * 
     * @throws Z3Exception
     **/
    public void add(BoolExpr ... constraints)
    {
        getContext().checkContextMatch(constraints);
        for (BoolExpr a : constraints)
        {
            Native.fixedpointAssert(getContext().nCtx(), getNativeObject(),
                    a.getNativeObject());
        }
    }

    /**
     * Register predicate as recursive relation.
     * 
     * @throws Z3Exception
     **/
    public void registerRelation(FuncDecl f)
    {

        getContext().checkContextMatch(f);
        Native.fixedpointRegisterRelation(getContext().nCtx(), getNativeObject(),
                f.getNativeObject());
    }

    /**
     * Add rule into the fixedpoint solver.
     *
     * @param rule implication (Horn clause) representing rule
     * @param name Nullable rule name.
     * @throws Z3Exception
     **/
    public void addRule(BoolExpr rule, Symbol name) {
        getContext().checkContextMatch(rule);
        Native.fixedpointAddRule(getContext().nCtx(), getNativeObject(),
                rule.getNativeObject(), AST.getNativeObject(name));
    }

    /**
     * Add table fact to the fixedpoint solver.
     * 
     * @throws Z3Exception
     **/
    public void addFact(FuncDecl pred, int ... args) {
        getContext().checkContextMatch(pred);
        Native.fixedpointAddFact(getContext().nCtx(), getNativeObject(),
                pred.getNativeObject(), args.length, args);
    }

    /**
     * Query the fixedpoint solver. A query is a conjunction of constraints. The
     * constraints may include the recursively defined relations. The query is
     * satisfiable if there is an instance of the query variables and a
     * derivation for it. The query is unsatisfiable if there are no derivations
     * satisfying the query variables.
     * 
     * @throws Z3Exception
     **/
    public Status query(BoolExpr query) {
        getContext().checkContextMatch(query);
        Z3_lbool r = Z3_lbool.fromInt(Native.fixedpointQuery(getContext().nCtx(),
                getNativeObject(), query.getNativeObject()));
        switch (r)
        {
        case Z3_L_TRUE:
            return Status.SATISFIABLE;
        case Z3_L_FALSE:
            return Status.UNSATISFIABLE;
        default:
            return Status.UNKNOWN;
        }
    }

    /**
     * Query the fixedpoint solver. A query is an array of relations. The query
     * is satisfiable if there is an instance of some relation that is
     * non-empty. The query is unsatisfiable if there are no derivations
     * satisfying any of the relations.
     * 
     * @throws Z3Exception
     **/
    public Status query(FuncDecl[] relations) {
        getContext().checkContextMatch(relations);
        Z3_lbool r = Z3_lbool.fromInt(Native.fixedpointQueryRelations(getContext()
                .nCtx(), getNativeObject(), AST.arrayLength(relations), AST
                .arrayToNative(relations)));
        switch (r)
        {
        case Z3_L_TRUE:
            return Status.SATISFIABLE;
        case Z3_L_FALSE:
            return Status.UNSATISFIABLE;
        default:
            return Status.UNKNOWN;
        }
    }

    /**
     * Creates a backtracking point. 
     * @see #pop
     **/
    public void push() {
        Native.fixedpointPush(getContext().nCtx(), getNativeObject());
    }

    /**
     * Backtrack one backtracking point.
     * Remarks: Note that an exception is thrown if {@code pop} 
     * is called without a corresponding {@code push}
     *  
     * @see #push
     **/
    public void pop() {
        Native.fixedpointPop(getContext().nCtx(), getNativeObject());
    }

    /**
     * Update named rule into in the fixedpoint solver.
     *
     * @param rule implication (Horn clause) representing rule
     * @param name Nullable rule name.
     * @throws Z3Exception
     **/
    public void updateRule(BoolExpr rule, Symbol name) {
        getContext().checkContextMatch(rule);
        Native.fixedpointUpdateRule(getContext().nCtx(), getNativeObject(),
                rule.getNativeObject(), AST.getNativeObject(name));
    }

    /**
     * Retrieve satisfying instance or instances of solver, or definitions for
     * the recursive predicates that show unsatisfiability.
     * 
     * @throws Z3Exception
     **/
    public Expr getAnswer()
    {
        long ans = Native.fixedpointGetAnswer(getContext().nCtx(), getNativeObject());
        return (ans == 0) ? null : Expr.create(getContext(), ans);
    }

    /**
     * Retrieve explanation why fixedpoint engine returned status Unknown.
     **/
    public String getReasonUnknown()
    {
        return Native.fixedpointGetReasonUnknown(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * Retrieve the number of levels explored for a given predicate.
     **/
    public int getNumLevels(FuncDecl predicate)
    {
        return Native.fixedpointGetNumLevels(getContext().nCtx(), getNativeObject(),
                predicate.getNativeObject());
    }

    /**
     * Retrieve the cover of a predicate.
     * 
     * @throws Z3Exception
     **/
    public Expr getCoverDelta(int level, FuncDecl predicate)
    {
        long res = Native.fixedpointGetCoverDelta(getContext().nCtx(),
                getNativeObject(), level, predicate.getNativeObject());
        return (res == 0) ? null : Expr.create(getContext(), res);
    }

    /**
     * Add <tt>property</tt> about the <tt>predicate</tt>. The property is added
     * at <tt>level</tt>.
     **/
    public void addCover(int level, FuncDecl predicate, Expr property)
           
    {
        Native.fixedpointAddCover(getContext().nCtx(), getNativeObject(), level,
                predicate.getNativeObject(), property.getNativeObject());
    }

    /**
     * Retrieve internal string representation of fixedpoint object.
     **/
    @Override
    public String toString()
    {
        return Native.fixedpointToString(getContext().nCtx(), getNativeObject(),
                    0, null);
    }

    /**
     * Instrument the Datalog engine on which table representation to use for
     * recursive predicate.
     **/
    public void setPredicateRepresentation(FuncDecl f, Symbol[] kinds)
    {

        Native.fixedpointSetPredicateRepresentation(getContext().nCtx(),
                getNativeObject(), f.getNativeObject(), AST.arrayLength(kinds),
                Symbol.arrayToNative(kinds));

    }

    /**
     * Convert benchmark given as set of axioms, rules and queries to a string.
     **/
    public String toString(BoolExpr[] queries)
    {

        return Native.fixedpointToString(getContext().nCtx(), getNativeObject(),
                AST.arrayLength(queries), AST.arrayToNative(queries));
    }

    /**
     * Retrieve set of rules added to fixedpoint context.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getRules()
    {
        ASTVector v = new ASTVector(getContext(), Native.fixedpointGetRules(getContext().nCtx(), getNativeObject()));
        return v.ToBoolExprArray();
    }

    /**
     * Retrieve set of assertions added to fixedpoint context.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getAssertions()
    {
        ASTVector v = new ASTVector(getContext(), Native.fixedpointGetAssertions(getContext().nCtx(), getNativeObject()));
        return v.ToBoolExprArray();
    }

    /**
     * Fixedpoint statistics.
     * 
     * @throws Z3Exception
     **/
    public Statistics getStatistics()
    {
        return new Statistics(getContext(), Native.fixedpointGetStatistics(
                getContext().nCtx(), getNativeObject()));
    }

    /** 
     * Parse an SMT-LIB2 file with fixedpoint rules. 
     * Add the rules to the current fixedpoint context. 
     * Return the set of queries in the file.
     **/        
    public BoolExpr[] ParseFile(String file)
    {
        ASTVector av = new ASTVector(getContext(), Native.fixedpointFromFile(getContext().nCtx(), getNativeObject(), file));
        return av.ToBoolExprArray();
    }

    /** 
     * Parse an SMT-LIB2 string with fixedpoint rules. 
     * Add the rules to the current fixedpoint context. 
     * Return the set of queries in the file.
     **/ 
    public BoolExpr[] ParseString(String s)
    {
        ASTVector av = new ASTVector(getContext(), Native.fixedpointFromString(getContext().nCtx(), getNativeObject(), s));
        return av.ToBoolExprArray();
    }
    

    Fixedpoint(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    Fixedpoint(Context ctx)
    {
        super(ctx, Native.mkFixedpoint(ctx.nCtx()));
    }

    @Override
    void incRef() {
        Native.fixedpointIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getFixedpointDRQ().storeReference(getContext(), this);
    }

    @Override
    void checkNativeObject(long obj) { }
}
