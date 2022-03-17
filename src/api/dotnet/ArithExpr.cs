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
using System.Diagnostics;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

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
            Debug.Assert(ctx != null);
        }
        #endregion

        #region Operators

        private static ArithExpr MkNum(ArithExpr e, int i)
        { 
            using var sort = e.Context.MkIntSort();
            return (ArithExpr)e.Context.MkNumeral(i, sort); 
        }        

        private static ArithExpr MkNum(ArithExpr e, double d) 
        { 
            using var sort = e.Context.MkRealSort();
            return (ArithExpr)e.Context.MkNumeral(d.ToString(), sort); 
        }        

        /// <summary> Operator overloading for arithmetical division operator (over reals) </summary>
        public static ArithExpr operator /(ArithExpr a, ArithExpr b) { return a.Context.MkDiv(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(ArithExpr a, int b) 
        {
            using var denominator = MkNum(a, b);
            return a / denominator;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(ArithExpr a, double b) 
        {
            using var denominator = MkNum(a, b);
            return a / denominator;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(int a, ArithExpr b) 
        {
            using var numerator = MkNum(b, a);
            return numerator / b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator /(double a, ArithExpr b) 
        {
            using var numerator = MkNum(b, a);
            return numerator / b;
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a) { return a.Context.MkUnaryMinus(a); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, ArithExpr b) { return a.Context.MkSub(a, b); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, int b) 
        { 
            using var rhs = MkNum(a, b);
            return a - rhs; 
        }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(ArithExpr a, double b) 
        {
            using var rhs = MkNum(a, b);
            return a - rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(int a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs - b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator -(double a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs - b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, ArithExpr b) { return a.Context.MkAdd(a, b); }        

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, int b) 
        { 
            using var rhs = MkNum(a, b);
            return a + rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(ArithExpr a, double b)
        { 
            using var rhs = MkNum(a, b);
            return a + rhs; 
        }
 
        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(int a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs + b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator +(double a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs + b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, ArithExpr b) { return a.Context.MkMul(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, int b) 
        { 
            using var rhs = MkNum(a, b);
            return a * rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(ArithExpr a, double b) 
        { 
            using var rhs = MkNum(a, b);
            return a * rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(int a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs * b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static ArithExpr operator *(double a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs * b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, ArithExpr b) { return a.Context.MkLe(a, b); }         

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, int b) 
        { 
            using var rhs = MkNum(a, b);
            return a <= rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(ArithExpr a, double b) 
        { 
            using var rhs = MkNum(a, b);
            return a <= rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(int a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs <= b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <=(double a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs <= b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, ArithExpr b) { return a.Context.MkLt(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, int b) 
        {
            using var rhs = MkNum(a, b);
            return a < rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(ArithExpr a, double b) 
        { 
            using var rhs = MkNum(a, b);
            return a < rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(int a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs < b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator <(double a, ArithExpr b) 
        {
            using var lhs = MkNum(b, a);
            return lhs < b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, ArithExpr b) { return a.Context.MkGt(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, int b) 
        { 
            using var rhs = MkNum(a, b);
            return a > rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(ArithExpr a, double b) 
        { 
            using var rhs = MkNum(a, b);
            return a > rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(int a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs > b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >(double a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs > b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, ArithExpr b) { return a.Context.MkGe(a, b); }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, int b) 
        { 
            using var rhs = MkNum(a, b);
            return a >= rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(ArithExpr a, double b) 
        { 
            using var rhs = MkNum(a, b);
            return a >= rhs; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(int a, ArithExpr b)
        { 
            using var lhs = MkNum(b, a);
            return lhs >= b; 
        }

        /// <summary> Operator overloading for arithmetical operator </summary>
        public static BoolExpr operator >=(double a, ArithExpr b) 
        { 
            using var lhs = MkNum(b, a);
            return lhs >= b; 
        }

        #endregion
    }
}
