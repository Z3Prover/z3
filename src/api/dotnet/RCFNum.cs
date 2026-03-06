/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    RCFNum.cs

Abstract:

    Z3 Managed API: Real Closed Field (RCF) Numerals

Author:

    GitHub Copilot 2024-01-12

Notes:
    
--*/
using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Real Closed Field (RCF) numerals.
    /// 
    /// RCF numerals can represent:
    /// - Rational numbers
    /// - Algebraic numbers (roots of polynomials)
    /// - Transcendental extensions (e.g., pi, e)
    /// - Infinitesimal extensions
    /// </summary>
    public class RCFNum : Z3Object
    {
        /// <summary>
        /// Create an RCF numeral from a rational string.
        /// </summary>
        /// <param name="ctx">Z3 context</param>
        /// <param name="value">String representation of a rational number (e.g., "3/2", "0.5", "42")</param>
        public RCFNum(Context ctx, string value)
            : base(ctx, Native.Z3_rcf_mk_rational(ctx.nCtx, value))
        {
            Debug.Assert(ctx != null);
        }

        /// <summary>
        /// Create an RCF numeral from a small integer.
        /// </summary>
        /// <param name="ctx">Z3 context</param>
        /// <param name="value">Integer value</param>
        public RCFNum(Context ctx, int value)
            : base(ctx, Native.Z3_rcf_mk_small_int(ctx.nCtx, value))
        {
            Debug.Assert(ctx != null);
        }

        /// <summary>
        /// Internal constructor for wrapping native RCF numeral pointers.
        /// </summary>
        internal RCFNum(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }

        /// <summary>
        /// Create an RCF numeral representing pi.
        /// </summary>
        /// <param name="ctx">Z3 context</param>
        /// <returns>RCF numeral for pi</returns>
        public static RCFNum MkPi(Context ctx)
        {
            return new RCFNum(ctx, Native.Z3_rcf_mk_pi(ctx.nCtx));
        }

        /// <summary>
        /// Create an RCF numeral representing e (Euler's constant).
        /// </summary>
        /// <param name="ctx">Z3 context</param>
        /// <returns>RCF numeral for e</returns>
        public static RCFNum MkE(Context ctx)
        {
            return new RCFNum(ctx, Native.Z3_rcf_mk_e(ctx.nCtx));
        }

        /// <summary>
        /// Create an RCF numeral representing an infinitesimal.
        /// </summary>
        /// <param name="ctx">Z3 context</param>
        /// <returns>RCF numeral for an infinitesimal</returns>
        public static RCFNum MkInfinitesimal(Context ctx)
        {
            return new RCFNum(ctx, Native.Z3_rcf_mk_infinitesimal(ctx.nCtx));
        }

        /// <summary>
        /// Find roots of a polynomial.
        /// 
        /// The polynomial is a[n-1]*x^(n-1) + ... + a[1]*x + a[0].
        /// </summary>
        /// <param name="ctx">Z3 context</param>
        /// <param name="coefficients">Polynomial coefficients (constant term first)</param>
        /// <returns>Array of RCF numerals representing the roots</returns>
        public static RCFNum[] MkRoots(Context ctx, RCFNum[] coefficients)
        {
            if (coefficients == null || coefficients.Length == 0)
            {
                throw new Z3Exception("Polynomial coefficients cannot be empty");
            }

            uint n = (uint)coefficients.Length;
            IntPtr[] a = new IntPtr[n];
            IntPtr[] roots = new IntPtr[n];

            for (uint i = 0; i < n; i++)
            {
                a[i] = coefficients[i].NativeObject;
            }

            uint numRoots = Native.Z3_rcf_mk_roots(ctx.nCtx, n, a, roots);

            RCFNum[] result = new RCFNum[numRoots];
            for (uint i = 0; i < numRoots; i++)
            {
                result[i] = new RCFNum(ctx, roots[i]);
            }

            return result;
        }

        /// <summary>
        /// Add two RCF numerals.
        /// </summary>
        /// <param name="other">The RCF numeral to add</param>
        /// <returns>this + other</returns>
        public RCFNum Add(RCFNum other)
        {
            CheckContext(other);
            return new RCFNum(Context, Native.Z3_rcf_add(Context.nCtx, NativeObject, other.NativeObject));
        }

        /// <summary>
        /// Subtract two RCF numerals.
        /// </summary>
        /// <param name="other">The RCF numeral to subtract</param>
        /// <returns>this - other</returns>
        public RCFNum Sub(RCFNum other)
        {
            CheckContext(other);
            return new RCFNum(Context, Native.Z3_rcf_sub(Context.nCtx, NativeObject, other.NativeObject));
        }

        /// <summary>
        /// Multiply two RCF numerals.
        /// </summary>
        /// <param name="other">The RCF numeral to multiply</param>
        /// <returns>this * other</returns>
        public RCFNum Mul(RCFNum other)
        {
            CheckContext(other);
            return new RCFNum(Context, Native.Z3_rcf_mul(Context.nCtx, NativeObject, other.NativeObject));
        }

        /// <summary>
        /// Divide two RCF numerals.
        /// </summary>
        /// <param name="other">The RCF numeral to divide by</param>
        /// <returns>this / other</returns>
        public RCFNum Div(RCFNum other)
        {
            CheckContext(other);
            return new RCFNum(Context, Native.Z3_rcf_div(Context.nCtx, NativeObject, other.NativeObject));
        }

        /// <summary>
        /// Negate this RCF numeral.
        /// </summary>
        /// <returns>-this</returns>
        public RCFNum Neg()
        {
            return new RCFNum(Context, Native.Z3_rcf_neg(Context.nCtx, NativeObject));
        }

        /// <summary>
        /// Compute the multiplicative inverse.
        /// </summary>
        /// <returns>1/this</returns>
        public RCFNum Inv()
        {
            return new RCFNum(Context, Native.Z3_rcf_inv(Context.nCtx, NativeObject));
        }

        /// <summary>
        /// Raise this RCF numeral to a power.
        /// </summary>
        /// <param name="k">The exponent</param>
        /// <returns>this^k</returns>
        public RCFNum Power(uint k)
        {
            return new RCFNum(Context, Native.Z3_rcf_power(Context.nCtx, NativeObject, k));
        }

        /// <summary>
        /// Operator overload for addition.
        /// </summary>
        public static RCFNum operator +(RCFNum a, RCFNum b)
        {
            return a.Add(b);
        }

        /// <summary>
        /// Operator overload for subtraction.
        /// </summary>
        public static RCFNum operator -(RCFNum a, RCFNum b)
        {
            return a.Sub(b);
        }

        /// <summary>
        /// Operator overload for multiplication.
        /// </summary>
        public static RCFNum operator *(RCFNum a, RCFNum b)
        {
            return a.Mul(b);
        }

        /// <summary>
        /// Operator overload for division.
        /// </summary>
        public static RCFNum operator /(RCFNum a, RCFNum b)
        {
            return a.Div(b);
        }

        /// <summary>
        /// Operator overload for negation.
        /// </summary>
        public static RCFNum operator -(RCFNum a)
        {
            return a.Neg();
        }

        /// <summary>
        /// Check if this RCF numeral is less than another.
        /// </summary>
        /// <param name="other">The RCF numeral to compare with</param>
        /// <returns>true if this &lt; other</returns>
        public bool Lt(RCFNum other)
        {
            CheckContext(other);
            return 0 != Native.Z3_rcf_lt(Context.nCtx, NativeObject, other.NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is greater than another.
        /// </summary>
        /// <param name="other">The RCF numeral to compare with</param>
        /// <returns>true if this &gt; other</returns>
        public bool Gt(RCFNum other)
        {
            CheckContext(other);
            return 0 != Native.Z3_rcf_gt(Context.nCtx, NativeObject, other.NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is less than or equal to another.
        /// </summary>
        /// <param name="other">The RCF numeral to compare with</param>
        /// <returns>true if this &lt;= other</returns>
        public bool Le(RCFNum other)
        {
            CheckContext(other);
            return 0 != Native.Z3_rcf_le(Context.nCtx, NativeObject, other.NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is greater than or equal to another.
        /// </summary>
        /// <param name="other">The RCF numeral to compare with</param>
        /// <returns>true if this &gt;= other</returns>
        public bool Ge(RCFNum other)
        {
            CheckContext(other);
            return 0 != Native.Z3_rcf_ge(Context.nCtx, NativeObject, other.NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is equal to another.
        /// </summary>
        /// <param name="other">The RCF numeral to compare with</param>
        /// <returns>true if this == other</returns>
        public bool Eq(RCFNum other)
        {
            CheckContext(other);
            return 0 != Native.Z3_rcf_eq(Context.nCtx, NativeObject, other.NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is not equal to another.
        /// </summary>
        /// <param name="other">The RCF numeral to compare with</param>
        /// <returns>true if this != other</returns>
        public bool Neq(RCFNum other)
        {
            CheckContext(other);
            return 0 != Native.Z3_rcf_neq(Context.nCtx, NativeObject, other.NativeObject);
        }

        /// <summary>
        /// Operator overload for less than.
        /// </summary>
        public static bool operator <(RCFNum a, RCFNum b)
        {
            return a.Lt(b);
        }

        /// <summary>
        /// Operator overload for greater than.
        /// </summary>
        public static bool operator >(RCFNum a, RCFNum b)
        {
            return a.Gt(b);
        }

        /// <summary>
        /// Operator overload for less than or equal.
        /// </summary>
        public static bool operator <=(RCFNum a, RCFNum b)
        {
            return a.Le(b);
        }

        /// <summary>
        /// Operator overload for greater than or equal.
        /// </summary>
        public static bool operator >=(RCFNum a, RCFNum b)
        {
            return a.Ge(b);
        }

        /// <summary>
        /// Operator overload for equality.
        /// </summary>
        public static bool operator ==(RCFNum a, RCFNum b)
        {
            if (ReferenceEquals(a, b)) return true;
            if (ReferenceEquals(a, null) || ReferenceEquals(b, null)) return false;
            return a.Eq(b);
        }

        /// <summary>
        /// Operator overload for inequality.
        /// </summary>
        public static bool operator !=(RCFNum a, RCFNum b)
        {
            return !(a == b);
        }

        /// <summary>
        /// Check if this RCF numeral is a rational number.
        /// </summary>
        /// <returns>true if this is rational</returns>
        public bool IsRational()
        {
            return 0 != Native.Z3_rcf_is_rational(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is an algebraic number.
        /// </summary>
        /// <returns>true if this is algebraic</returns>
        public bool IsAlgebraic()
        {
            return 0 != Native.Z3_rcf_is_algebraic(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is an infinitesimal.
        /// </summary>
        /// <returns>true if this is infinitesimal</returns>
        public bool IsInfinitesimal()
        {
            return 0 != Native.Z3_rcf_is_infinitesimal(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Check if this RCF numeral is a transcendental number.
        /// </summary>
        /// <returns>true if this is transcendental</returns>
        public bool IsTranscendental()
        {
            return 0 != Native.Z3_rcf_is_transcendental(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Convert this RCF numeral to a string.
        /// </summary>
        /// <param name="compact">If true, use compact representation</param>
        /// <returns>String representation</returns>
        public string ToString(bool compact)
        {
            return Native.Z3_rcf_num_to_string(Context.nCtx, NativeObject, compact ? (byte)1 : (byte)0, 0);
        }

        /// <summary>
        /// Convert this RCF numeral to a string (non-compact).
        /// </summary>
        /// <returns>String representation</returns>
        public override string ToString()
        {
            return ToString(false);
        }

        /// <summary>
        /// Convert this RCF numeral to a decimal string.
        /// </summary>
        /// <param name="precision">Number of decimal places</param>
        /// <returns>Decimal string representation</returns>
        public string ToDecimal(uint precision)
        {
            return Native.Z3_rcf_num_to_decimal_string(Context.nCtx, NativeObject, precision);
        }

        /// <summary>
        /// Override Equals for proper equality semantics.
        /// </summary>
        public override bool Equals(object obj)
        {
            if (obj is RCFNum other)
            {
                return this == other;
            }
            return false;
        }

        /// <summary>
        /// Override GetHashCode for proper equality semantics.
        /// </summary>
        public override int GetHashCode()
        {
            return NativeObject.GetHashCode();
        }

        #region Internal
        internal override void DecRef(IntPtr o)
        {
            Native.Z3_rcf_del(Context.nCtx, o);
        }

        private void CheckContext(RCFNum other)
        {
            if (Context != other.Context)
            {
                throw new Z3Exception("RCF numerals from different contexts");
            }
        }
        #endregion
    }
}
