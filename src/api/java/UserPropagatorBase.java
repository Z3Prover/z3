package com.microsoft.z3;

import com.microsoft.z3.Context;
import com.microsoft.z3.enumerations.Z3_lbool;

public abstract class UserPropagatorBase extends Native.UserPropagatorBase {
    private Context ctx;
    private Solver solver;

    public UserPropagatorBase(Context _ctx, Solver _solver) {
        super(_ctx.nCtx(), _solver.getNativeObject());   
        ctx = _ctx;
        solver = _solver; 
    }

    public final Context getCtx() {
        return ctx;
    }

    public final Solver getSolver() {
        return solver;
    }

    @Override
    protected final void pushWrapper() {
        push();
    }

    @Override
    protected final void popWrapper(int number) {
        pop(number);
    }

    @Override
    protected final void finWrapper() {
        fin();
    }

    @Override
    protected final void eqWrapper(long lx, long ly) {
        Expr x = new Expr(ctx, lx);
        Expr y = new Expr(ctx, ly);
        eq(x, y);
    }

    @Override
    protected final UserPropagatorBase freshWrapper(long lctx) {
        return fresh(new Context(lctx));
    }

    @Override
    protected final void createdWrapper(long last) {
        created(new Expr(ctx, last));
    }

    @Override
    protected final void fixedWrapper(long lvar, long lvalue) {
        Expr var = new Expr(ctx, lvar);
        Expr value = new Expr(ctx, lvalue);
        fixed(var, value);
    }

    @Override
    protected final void decideWrapper(long lvar, int bit, boolean is_pos) {
        Expr var = new Expr(ctx, lvar);
        decide(var, bit, is_pos);
    }

    public abstract void push();

    public abstract void pop(int number);

    public abstract UserPropagatorBase fresh(Context ctx);

    public <R extends Sort> void created(Expr<R> ast) {}

    public <R extends Sort> void fixed(Expr<R> var, Expr<R> value) {}

    public <R extends Sort> void eq(Expr<R> x, Expr<R> y) {}

    public <R extends Sort> void decide(Expr<R> var, int bit, boolean is_pos) {}

    public void fin() {}

    public final <R extends Sort> void add(Expr<R> expr) {
        Native.propagateAdd(this, ctx.nCtx(), solver.getNativeObject(), javainfo, expr.getNativeObject());
    }

    public final <R extends Sort> boolean conflict(Expr<R>[] fixed) {
        return conflict(fixed, new Expr[0], new Expr[0]);
    }

    public final <R extends Sort> boolean conflict(Expr<R>[] fixed, Expr<R>[] lhs, Expr<R>[] rhs) {
        AST conseq = ctx.mkBool(false);
        return consequence(fixed, lhs, rhs, conseq);
    }

    public final <R extends Sort> boolean consequence(Expr<R>[] fixed, Expr<R>[] lhs,
                                                      Expr<R>[] rhs, Expr<R> conseq) {
        return Native.propagateConflict(
            this, ctx.nCtx(), solver.getNativeObject(), javainfo,
            fixed.length, AST.arrayToNative(fixed), lhs.length, AST.arrayToNative(lhs), AST.arrayToNative(rhs), conseq.getNativeObject());
    }

    public final <R extends Sort> boolean nextSplit(Expr<R> e, long idx, Z3_lbool phase) {
        return Native.propagateNextSplit(
            this, ctx.nCtx(), solver.getNativeObject(), javainfo,
            e.getNativeObject(), idx, phase.toInt());
    }
}
