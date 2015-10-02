
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Z3;
using Microsoft.SolverFoundation.Common;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    public class Utils
    {
        /// <summary>
        /// Returns the Z3 term corresponding to the MSF rational number.
        /// </summary>
        /// <param name="rational">The MSF rational</param>
        /// <returns>The Z3 term</returns>
        public static ArithExpr GetNumeral(Context context, Rational rational, Sort sort = null)
        {
            try
            {
                sort = rational.IsInteger() ? ((Sort)context.IntSort) : (sort == null ? (Sort)context.RealSort : sort);
                return (ArithExpr)context.MkNumeral(rational.ToString(), sort);                
            }
            catch (Z3Exception e)
            {
                Console.Error.WriteLine("Conversion of {0} failed:\n {1}", rational, e);
                throw new NotSupportedException();
            }
        }

        private static long BASE = 10 ^ 18;

        private static Rational ToRational(System.Numerics.BigInteger bi)
        {
            if (System.Numerics.BigInteger.Abs(bi) <= BASE) 
            {
                return (Rational)((long)bi);
            }
            return BASE * ToRational(bi / BASE) + ToRational(bi % BASE);
        }

        public static Rational ToRational(IntNum i)
        {
            return ToRational(i.BigInteger);
        }

        public static Rational ToRational(RatNum r)
        {
            return ToRational(r.BigIntNumerator) / ToRational(r.BigIntDenominator);
        }

        public static Rational ToRational(Expr expr)
        {
            Debug.Assert(expr is ArithExpr, "Only accept ArithExpr for now.");
            var e = expr as ArithExpr;

            if (e is IntNum) 
            {
                Debug.Assert(expr.IsIntNum, "Number should be an integer.");
                return ToRational(expr as IntNum);
            }
            
            if (e is RatNum)
            {
                Debug.Assert(expr.IsRatNum, "Number should be a rational.");
                return ToRational(expr as RatNum);
            }
            
            if (e.IsAdd)
            {
                Rational r = Rational.Zero;
                foreach (var arg in e.Args)
                {
                    r += ToRational(arg);
                }
                return r;
            }
            
            if (e.IsMul)
            {
                Rational r = Rational.One;
                foreach (var arg in e.Args)
                {
                    r *= ToRational(arg);
                }
                return r;
            }
            
            if (e.IsUMinus)
            {
                return -ToRational(e.Args[0]);
            }
            
            if (e.IsDiv)
            {
                return ToRational(e.Args[0]) / ToRational(e.Args[1]);
            }
            
            if (e.IsSub)
            {
                Rational r = ToRational(e.Args[0]);
                for (int i = 1; i < e.Args.Length; ++i)
                {
                    r -= ToRational(e.Args[i]);
                }
                return r;
            }
            
            if (e.IsConst && e.FuncDecl.Name.ToString() == "oo")
            {
                return Rational.PositiveInfinity;
            }
            
            if (e.IsConst && e.FuncDecl.Name.ToString() == "epsilon")
            {
                return Rational.One/Rational.PositiveInfinity;              
            }

            Debug.Assert(false, "Should not happen");
            return Rational.One;
        }
    }
}
