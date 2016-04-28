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

        #region Operators

        private static ArithExpr MkNum(ArithExpr e, int i) { return (ArithExpr)e.Context.MkNumeral(i, e.Context.MkIntSort()); }        

        private static ArithExpr MkNum(ArithExpr e, double d) { return (ArithExpr)e.Context.MkNumeral(d.ToString(), e.Context.MkRealSort()); }        

        /// <summary> Operator overloading for arithmetical divsion operator (over reals) </summary>
        public static ArithExpr operator /(ArithExpr a, ArithExpr b) { return a.Context.MkDiv(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(ArithExpr a, int b) { return a / MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(ArithExpr a, double b) { return a / MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(int a, ArithExpr b) { return MkNum(b, a) / b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(double a, ArithExpr b) { return MkNum(b, a) / b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a) { return a.Context.MkUnaryMinus(a); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, ArithExpr b) { return a.Context.MkSub(a, b); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, int b) { return a - MkNum(a, b); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, double b) { return a - MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(int a, ArithExpr b) { return MkNum(b, a) - b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(double a, ArithExpr b) { return MkNum(b, a) - b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, ArithExpr b) { return a.Context.MkAdd(a, b); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, int b) { return a + MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, double b) { return a + MkNum(a, b); }
 
        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(int a, ArithExpr b) { return MkNum(b, a) + b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(double a, ArithExpr b) { return MkNum(b, a) + b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, ArithExpr b) { return a.Context.MkMul(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, int b) { return a * MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, double b) { return a * MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(int a, ArithExpr b) { return MkNum(b, a) * b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(double a, ArithExpr b) { return MkNum(b, a) * b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, ArithExpr b) { return a.Context.MkLe(a, b); }         

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, int b) { return a <= MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, double b) { return a <= MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(int a, ArithExpr b) { return MkNum(b, a) <= b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(double a, ArithExpr b) { return MkNum(b, a) <= b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, ArithExpr b) { return a.Context.MkLt(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, int b) { return a < MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, double b) { return a < MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(int a, ArithExpr b) { return MkNum(b, a) < b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(double a, ArithExpr b) { return MkNum(b, a) < b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, ArithExpr b) { return a.Context.MkGt(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, int b) { return a > MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, double b) { return a > MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(int a, ArithExpr b) { return MkNum(b, a) > b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(double a, ArithExpr b) { return MkNum(b, a) > b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, ArithExpr b) { return a.Context.MkGe(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, int b) { return a >= MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, double b) { return a >= MkNum(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(int a, ArithExpr b) { return MkNum(b, a) >= b; }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(double a, ArithExpr b) { return MkNum(b, a) >= b; }

        #endregion
    }
}
