/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    ArithExpr.cs

Abstract:

    Z3 Managed API: Arith Expressions

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Arithmetic expressions (int/real)
    /// </summary>
    public class ArithExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for ArithExpr </summary>
        internal ArithExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkSub(a, b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkAdd(a, b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkMul(a, b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, int b)
        {
            return a.Context.MkMul(a, (ArithExpr)a.Context.MkNumeral(b, a.Context.MkIntSort()));
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, double b)
        {
            return a.Context.MkMul(a, (ArithExpr)a.Context.MkNumeral(b.ToString(), a.Context.MkRealSort()));
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(int a, ArithExpr b)
        {
            return b.Context.MkMul((ArithExpr)b.Context.MkNumeral(a, b.Context.MkIntSort()), b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(double a, ArithExpr b)
        {
            return b.Context.MkMul((ArithExpr)b.Context.MkNumeral(a.ToString(), b.Context.MkRealSort()), b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkLe(a, b); 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, int b)
        {
            return a <= (ArithExpr)a.Context.MkNumeral(b, a.Context.MkIntSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, double b)
        {
            return a <= (ArithExpr)a.Context.MkNumeral(b.ToString(), a.Context.MkRealSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(int a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a, b.Context.MkIntSort()) <= b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(double a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a.ToString(), b.Context.MkRealSort()) <= b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkLt(a, b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, int b)
        {
            return a < (ArithExpr)a.Context.MkNumeral(b, a.Context.MkIntSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, double b)
        {
            return a < (ArithExpr)a.Context.MkNumeral(b.ToString(), a.Context.MkRealSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(int a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a, b.Context.MkIntSort()) < b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(double a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a.ToString(), b.Context.MkRealSort()) < b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkGe(a, b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, int b)
        {
            return a >= (ArithExpr)a.Context.MkNumeral(b, a.Context.MkIntSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, double b)
        {
            return a >= (ArithExpr)a.Context.MkNumeral(b.ToString(), a.Context.MkRealSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(int a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a, b.Context.MkIntSort()) >= b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(double a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a.ToString(), b.Context.MkRealSort()) >= b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, ArithExpr b)
        {
            return a.Context.MkGt(a, b);
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, int b)
        {
            return a > (ArithExpr)a.Context.MkNumeral(b, a.Context.MkIntSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, double b)
        {
            return a > (ArithExpr)a.Context.MkNumeral(b.ToString(), a.Context.MkRealSort());
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(int a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a, b.Context.MkIntSort()) > b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(double a, ArithExpr b)
        {
            return (ArithExpr)b.Context.MkNumeral(a.ToString(), b.Context.MkRealSort()) > b;
        }
    }
}
