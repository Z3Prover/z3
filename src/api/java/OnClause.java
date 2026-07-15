/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    OnClause.java

Abstract:

    Callback on clause inferences

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-19

Notes:

**/

package com.microsoft.z3;

/**
 * Clause inference callback.
 * <p>
 * Allows users to observe clauses learned during solving.
 * Useful for custom learning strategies, clause sharing in parallel solvers,
 * debugging, and proof extraction.
 * </p>
 * <p>
 * Usage: create an instance, override {@link #onClause(Expr, int[], ASTVector)},
 * and close the instance when done.
 * </p>
 **/
public class OnClause implements AutoCloseable {

    private long javainfo;
    private final Context ctx;

    /**
     * Creates an on-clause callback for the given solver.
     *
     * @param ctx    The Z3 context
     * @param solver The solver to register the callback with
     * @throws Z3Exception
     **/
    public OnClause(Context ctx, Solver solver) {
        this.ctx = ctx;
        javainfo = Native.onClauseInit(this, ctx.nCtx(), solver.getNativeObject());
    }

    /**
     * Called when a clause is inferred during solving.
     * <p>
     * The life-time of {@code proof_hint} and {@code literals} is limited to
     * the scope of this callback. If you want to store them, you must duplicate
     * the expressions or extract the literals before returning.
     * </p>
     *
     * @param proof_hint A partial or comprehensive derivation justifying the inference (may be null)
     * @param deps       Dependency indices
     * @param literals   The inferred clause as a vector of literals
     **/
    public void onClause(Expr<?> proof_hint, int[] deps, ASTVector literals) {}

    /**
     * Internal wrapper called from JNI. Do not override.
     **/
    final void onClauseWrapper(long proofHintPtr, int[] deps, long literalsPtr) {
        Expr<?> proof_hint = proofHintPtr != 0 ? (Expr<?>) Expr.create(ctx, proofHintPtr) : null;
        ASTVector literals = new ASTVector(ctx, literalsPtr);
        onClause(proof_hint, deps, literals);
    }

    /**
     * Unregisters the callback and frees associated resources.
     * Must be called when the callback is no longer needed.
     **/
    @Override
    public void close() {
        if (javainfo != 0) {
            Native.onClauseDestroy(javainfo);
            javainfo = 0;
        }
    }
}
