/**
Copyright (c) 2024 Microsoft Corporation
   
Module Name:

    RCFNum.java

Abstract:

    Real Closed Field (RCF) numerals

Author:

    GitHub Copilot 2024-01-12

Notes:
    
**/

package com.microsoft.z3;

/**
 * Real Closed Field (RCF) numerals.
 * 
 * RCF numerals can represent:
 * - Rational numbers
 * - Algebraic numbers (roots of polynomials)
 * - Transcendental extensions (e.g., pi, e)
 * - Infinitesimal extensions
 **/
public class RCFNum extends Z3Object {
    
    /**
     * Create an RCF numeral from a rational string.
     * @param ctx Z3 context
     * @param value String representation of a rational number (e.g., "3/2", "0.5", "42")
     * @throws Z3Exception on error
     **/
    public RCFNum(Context ctx, String value) {
        super(ctx, Native.rcfMkRational(ctx.nCtx(), value));
    }
    
    /**
     * Create an RCF numeral from a small integer.
     * @param ctx Z3 context
     * @param value Integer value
     * @throws Z3Exception on error
     **/
    public RCFNum(Context ctx, int value) {
        super(ctx, Native.rcfMkSmallInt(ctx.nCtx(), value));
    }
    
    /**
     * Internal constructor for wrapping native RCF numeral pointers.
     **/
    RCFNum(Context ctx, long obj) {
        super(ctx, obj);
    }
    
    /**
     * Create an RCF numeral representing pi.
     * @param ctx Z3 context
     * @return RCF numeral for pi
     * @throws Z3Exception on error
     **/
    public static RCFNum mkPi(Context ctx) {
        return new RCFNum(ctx, Native.rcfMkPi(ctx.nCtx()));
    }
    
    /**
     * Create an RCF numeral representing e (Euler's constant).
     * @param ctx Z3 context
     * @return RCF numeral for e
     * @throws Z3Exception on error
     **/
    public static RCFNum mkE(Context ctx) {
        return new RCFNum(ctx, Native.rcfMkE(ctx.nCtx()));
    }
    
    /**
     * Create an RCF numeral representing an infinitesimal.
     * @param ctx Z3 context
     * @return RCF numeral for an infinitesimal
     * @throws Z3Exception on error
     **/
    public static RCFNum mkInfinitesimal(Context ctx) {
        return new RCFNum(ctx, Native.rcfMkInfinitesimal(ctx.nCtx()));
    }
    
    /**
     * Find roots of a polynomial.
     * 
     * The polynomial is a[n-1]*x^(n-1) + ... + a[1]*x + a[0].
     * 
     * @param ctx Z3 context
     * @param coefficients Polynomial coefficients (constant term first)
     * @return Array of RCF numerals representing the roots
     * @throws Z3Exception on error
     **/
    public static RCFNum[] mkRoots(Context ctx, RCFNum[] coefficients) {
        if (coefficients == null || coefficients.length == 0) {
            throw new Z3Exception("Polynomial coefficients cannot be empty");
        }
        
        int n = coefficients.length;
        long[] a = new long[n];
        long[] roots = new long[n];
        
        for (int i = 0; i < n; i++) {
            a[i] = coefficients[i].getNativeObject();
        }
        
        int numRoots = Native.rcfMkRoots(ctx.nCtx(), n, a, roots);
        
        RCFNum[] result = new RCFNum[numRoots];
        for (int i = 0; i < numRoots; i++) {
            result[i] = new RCFNum(ctx, roots[i]);
        }
        
        return result;
    }
    
    /**
     * Add two RCF numerals.
     * @param other The RCF numeral to add
     * @return this + other
     * @throws Z3Exception on error
     **/
    public RCFNum add(RCFNum other) {
        checkContext(other);
        return new RCFNum(getContext(), Native.rcfAdd(getContext().nCtx(), 
                                                       getNativeObject(), 
                                                       other.getNativeObject()));
    }
    
    /**
     * Subtract two RCF numerals.
     * @param other The RCF numeral to subtract
     * @return this - other
     * @throws Z3Exception on error
     **/
    public RCFNum sub(RCFNum other) {
        checkContext(other);
        return new RCFNum(getContext(), Native.rcfSub(getContext().nCtx(), 
                                                       getNativeObject(), 
                                                       other.getNativeObject()));
    }
    
    /**
     * Multiply two RCF numerals.
     * @param other The RCF numeral to multiply
     * @return this * other
     * @throws Z3Exception on error
     **/
    public RCFNum mul(RCFNum other) {
        checkContext(other);
        return new RCFNum(getContext(), Native.rcfMul(getContext().nCtx(), 
                                                       getNativeObject(), 
                                                       other.getNativeObject()));
    }
    
    /**
     * Divide two RCF numerals.
     * @param other The RCF numeral to divide by
     * @return this / other
     * @throws Z3Exception on error
     **/
    public RCFNum div(RCFNum other) {
        checkContext(other);
        return new RCFNum(getContext(), Native.rcfDiv(getContext().nCtx(), 
                                                       getNativeObject(), 
                                                       other.getNativeObject()));
    }
    
    /**
     * Negate this RCF numeral.
     * @return -this
     * @throws Z3Exception on error
     **/
    public RCFNum neg() {
        return new RCFNum(getContext(), Native.rcfNeg(getContext().nCtx(), 
                                                       getNativeObject()));
    }
    
    /**
     * Compute the multiplicative inverse.
     * @return 1/this
     * @throws Z3Exception on error
     **/
    public RCFNum inv() {
        return new RCFNum(getContext(), Native.rcfInv(getContext().nCtx(), 
                                                       getNativeObject()));
    }
    
    /**
     * Raise this RCF numeral to a power.
     * @param k The exponent
     * @return this^k
     * @throws Z3Exception on error
     **/
    public RCFNum power(int k) {
        return new RCFNum(getContext(), Native.rcfPower(getContext().nCtx(), 
                                                         getNativeObject(), k));
    }
    
    /**
     * Check if this RCF numeral is less than another.
     * @param other The RCF numeral to compare with
     * @return true if this < other
     * @throws Z3Exception on error
     **/
    public boolean lt(RCFNum other) {
        checkContext(other);
        return Native.rcfLt(getContext().nCtx(), getNativeObject(), 
                           other.getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is greater than another.
     * @param other The RCF numeral to compare with
     * @return true if this > other
     * @throws Z3Exception on error
     **/
    public boolean gt(RCFNum other) {
        checkContext(other);
        return Native.rcfGt(getContext().nCtx(), getNativeObject(), 
                           other.getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is less than or equal to another.
     * @param other The RCF numeral to compare with
     * @return true if this <= other
     * @throws Z3Exception on error
     **/
    public boolean le(RCFNum other) {
        checkContext(other);
        return Native.rcfLe(getContext().nCtx(), getNativeObject(), 
                           other.getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is greater than or equal to another.
     * @param other The RCF numeral to compare with
     * @return true if this >= other
     * @throws Z3Exception on error
     **/
    public boolean ge(RCFNum other) {
        checkContext(other);
        return Native.rcfGe(getContext().nCtx(), getNativeObject(), 
                           other.getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is equal to another.
     * @param other The RCF numeral to compare with
     * @return true if this == other
     * @throws Z3Exception on error
     **/
    public boolean eq(RCFNum other) {
        checkContext(other);
        return Native.rcfEq(getContext().nCtx(), getNativeObject(), 
                           other.getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is not equal to another.
     * @param other The RCF numeral to compare with
     * @return true if this != other
     * @throws Z3Exception on error
     **/
    public boolean neq(RCFNum other) {
        checkContext(other);
        return Native.rcfNeq(getContext().nCtx(), getNativeObject(), 
                            other.getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is a rational number.
     * @return true if this is rational
     * @throws Z3Exception on error
     **/
    public boolean isRational() {
        return Native.rcfIsRational(getContext().nCtx(), getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is an algebraic number.
     * @return true if this is algebraic
     * @throws Z3Exception on error
     **/
    public boolean isAlgebraic() {
        return Native.rcfIsAlgebraic(getContext().nCtx(), getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is an infinitesimal.
     * @return true if this is infinitesimal
     * @throws Z3Exception on error
     **/
    public boolean isInfinitesimal() {
        return Native.rcfIsInfinitesimal(getContext().nCtx(), getNativeObject());
    }
    
    /**
     * Check if this RCF numeral is a transcendental number.
     * @return true if this is transcendental
     * @throws Z3Exception on error
     **/
    public boolean isTranscendental() {
        return Native.rcfIsTranscendental(getContext().nCtx(), getNativeObject());
    }
    
    /**
     * Convert this RCF numeral to a string.
     * @param compact If true, use compact representation
     * @return String representation
     * @throws Z3Exception on error
     **/
    public String toString(boolean compact) {
        return Native.rcfNumToString(getContext().nCtx(), getNativeObject(), 
                                     compact, false);
    }
    
    /**
     * Convert this RCF numeral to a string (non-compact).
     * @return String representation
     * @throws Z3Exception on error
     **/
    @Override
    public String toString() {
        return toString(false);
    }
    
    /**
     * Convert this RCF numeral to a decimal string.
     * @param precision Number of decimal places
     * @return Decimal string representation
     * @throws Z3Exception on error
     **/
    public String toDecimal(int precision) {
        return Native.rcfNumToDecimalString(getContext().nCtx(), 
                                            getNativeObject(), precision);
    }
    
    @Override
    void incRef() {
        // RCF numerals don't use standard reference counting
        // They are managed through Z3_rcf_del
    }
    
    @Override
    void addToReferenceQueue() {
        getContext().getReferenceQueue().storeReference(this, RCFNumRef::new);
    }
    
    private static class RCFNumRef extends Z3ReferenceQueue.Reference<RCFNum> {
        
        private RCFNumRef(RCFNum referent, java.lang.ref.ReferenceQueue<Z3Object> q) {
            super(referent, q);
        }
        
        @Override
        void decRef(Context ctx, long z3Obj) {
            Native.rcfDel(ctx.nCtx(), z3Obj);
        }
    }
    
    private void checkContext(RCFNum other) {
        if (getContext() != other.getContext()) {
            throw new Z3Exception("RCF numerals from different contexts");
        }
    }
}
