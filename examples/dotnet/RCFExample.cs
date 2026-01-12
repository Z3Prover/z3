/**
   Example demonstrating the RCF (Real Closed Field) API in C#.
   
   This example shows how to use RCF numerals to work with:
   - Transcendental numbers (pi, e)
   - Algebraic numbers (roots of polynomials)
   - Infinitesimals
   - Exact real arithmetic
*/

using Microsoft.Z3;
using System;

class RCFExample
{
    static void RcfBasicExample()
    {
        Console.WriteLine("RCF Basic Example");
        Console.WriteLine("=================");

        using (Context ctx = new Context())
        {
            // Create pi and e
            RCFNum pi = RCFNum.MkPi(ctx);
            RCFNum e = RCFNum.MkE(ctx);

            Console.WriteLine("pi = " + pi);
            Console.WriteLine("e = " + e);

            // Arithmetic operations
            RCFNum sum = pi + e;
            RCFNum prod = pi * e;

            Console.WriteLine("pi + e = " + sum);
            Console.WriteLine("pi * e = " + prod);

            // Decimal approximations
            Console.WriteLine("pi (10 decimals) = " + pi.ToDecimal(10));
            Console.WriteLine("e (10 decimals) = " + e.ToDecimal(10));

            // Comparisons
            Console.WriteLine("pi < e? " + (pi < e ? "yes" : "no"));
            Console.WriteLine("pi > e? " + (pi > e ? "yes" : "no"));
        }
    }

    static void RcfRationalExample()
    {
        Console.WriteLine("\nRCF Rational Example");
        Console.WriteLine("====================");

        using (Context ctx = new Context())
        {
            // Create rational numbers
            RCFNum half = new RCFNum(ctx, "1/2");
            RCFNum third = new RCFNum(ctx, "1/3");

            Console.WriteLine("1/2 = " + half);
            Console.WriteLine("1/3 = " + third);

            // Arithmetic
            RCFNum sum = half + third;
            Console.WriteLine("1/2 + 1/3 = " + sum);

            // Type queries
            Console.WriteLine("Is 1/2 rational? " + (half.IsRational() ? "yes" : "no"));
            Console.WriteLine("Is 1/2 algebraic? " + (half.IsAlgebraic() ? "yes" : "no"));
        }
    }

    static void RcfRootsExample()
    {
        Console.WriteLine("\nRCF Roots Example");
        Console.WriteLine("=================");

        using (Context ctx = new Context())
        {
            // Find roots of x^2 - 2 = 0
            // Polynomial: -2 + 0*x + 1*x^2
            RCFNum[] coeffs = new RCFNum[] {
                new RCFNum(ctx, -2),   // constant term
                new RCFNum(ctx, 0),    // x coefficient
                new RCFNum(ctx, 1)     // x^2 coefficient
            };

            RCFNum[] roots = RCFNum.MkRoots(ctx, coeffs);

            Console.WriteLine("Roots of x^2 - 2 = 0:");
            for (int i = 0; i < roots.Length; i++)
            {
                Console.WriteLine("  root[" + i + "] = " + roots[i]);
                Console.WriteLine("  decimal = " + roots[i].ToDecimal(15));
                Console.WriteLine("  is_algebraic = " + (roots[i].IsAlgebraic() ? "yes" : "no"));
            }
        }
    }

    static void RcfInfinitesimalExample()
    {
        Console.WriteLine("\nRCF Infinitesimal Example");
        Console.WriteLine("=========================");

        using (Context ctx = new Context())
        {
            // Create an infinitesimal
            RCFNum eps = RCFNum.MkInfinitesimal(ctx);
            Console.WriteLine("eps = " + eps);
            Console.WriteLine("Is eps infinitesimal? " + (eps.IsInfinitesimal() ? "yes" : "no"));

            // Infinitesimals are smaller than any positive real number
            RCFNum tiny = new RCFNum(ctx, "1/1000000000");
            Console.WriteLine("eps < 1/1000000000? " + (eps < tiny ? "yes" : "no"));
        }
    }

    static void Main(string[] args)
    {
        try
        {
            RcfBasicExample();
            RcfRationalExample();
            RcfRootsExample();
            RcfInfinitesimalExample();

            Console.WriteLine("\nAll RCF examples completed successfully!");
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine("Error: " + ex.Message);
            Console.Error.WriteLine(ex.StackTrace);
        }
    }
}
