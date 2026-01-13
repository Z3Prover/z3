/**
   Example demonstrating the RCF (Real Closed Field) API in Java.
   
   This example shows how to use RCF numerals to work with:
   - Transcendental numbers (pi, e)
   - Algebraic numbers (roots of polynomials)
   - Infinitesimals
   - Exact real arithmetic
*/

package com.microsoft.z3;

public class RCFExample {
    
    public static void rcfBasicExample() {
        System.out.println("RCF Basic Example");
        System.out.println("=================");
        
        try (Context ctx = new Context()) {
            // Create pi and e
            RCFNum pi = RCFNum.mkPi(ctx);
            RCFNum e = RCFNum.mkE(ctx);
            
            System.out.println("pi = " + pi);
            System.out.println("e = " + e);
            
            // Arithmetic operations
            RCFNum sum = pi.add(e);
            RCFNum prod = pi.mul(e);
            
            System.out.println("pi + e = " + sum);
            System.out.println("pi * e = " + prod);
            
            // Decimal approximations
            System.out.println("pi (10 decimals) = " + pi.toDecimal(10));
            System.out.println("e (10 decimals) = " + e.toDecimal(10));
            
            // Comparisons
            System.out.println("pi < e? " + (pi.lt(e) ? "yes" : "no"));
            System.out.println("pi > e? " + (pi.gt(e) ? "yes" : "no"));
        }
    }
    
    public static void rcfRationalExample() {
        System.out.println("\nRCF Rational Example");
        System.out.println("====================");
        
        try (Context ctx = new Context()) {
            // Create rational numbers
            RCFNum half = new RCFNum(ctx, "1/2");
            RCFNum third = new RCFNum(ctx, "1/3");
            
            System.out.println("1/2 = " + half);
            System.out.println("1/3 = " + third);
            
            // Arithmetic
            RCFNum sum = half.add(third);
            System.out.println("1/2 + 1/3 = " + sum);
            
            // Type queries
            System.out.println("Is 1/2 rational? " + (half.isRational() ? "yes" : "no"));
            System.out.println("Is 1/2 algebraic? " + (half.isAlgebraic() ? "yes" : "no"));
        }
    }
    
    public static void rcfRootsExample() {
        System.out.println("\nRCF Roots Example");
        System.out.println("=================");
        
        try (Context ctx = new Context()) {
            // Find roots of x^2 - 2 = 0
            // Polynomial: -2 + 0*x + 1*x^2
            RCFNum[] coeffs = new RCFNum[] {
                new RCFNum(ctx, -2),   // constant term
                new RCFNum(ctx, 0),    // x coefficient
                new RCFNum(ctx, 1)     // x^2 coefficient
            };
            
            RCFNum[] roots = RCFNum.mkRoots(ctx, coeffs);
            
            System.out.println("Roots of x^2 - 2 = 0:");
            for (int i = 0; i < roots.length; i++) {
                System.out.println("  root[" + i + "] = " + roots[i]);
                System.out.println("  decimal = " + roots[i].toDecimal(15));
                System.out.println("  is_algebraic = " + (roots[i].isAlgebraic() ? "yes" : "no"));
            }
        }
    }
    
    public static void rcfInfinitesimalExample() {
        System.out.println("\nRCF Infinitesimal Example");
        System.out.println("=========================");
        
        try (Context ctx = new Context()) {
            // Create an infinitesimal
            RCFNum eps = RCFNum.mkInfinitesimal(ctx);
            System.out.println("eps = " + eps);
            System.out.println("Is eps infinitesimal? " + (eps.isInfinitesimal() ? "yes" : "no"));
            
            // Infinitesimals are smaller than any positive real number
            RCFNum tiny = new RCFNum(ctx, "1/1000000000");
            System.out.println("eps < 1/1000000000? " + (eps.lt(tiny) ? "yes" : "no"));
        }
    }
    
    public static void main(String[] args) {
        try {
            rcfBasicExample();
            rcfRationalExample();
            rcfRootsExample();
            rcfInfinitesimalExample();
            
            System.out.println("\nAll RCF examples completed successfully!");
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
