/*++
 Copyright (c) 2024 Microsoft Corporation

Module Name:

    SolverIntrospectionExample.java

Abstract:

    Z3 Java API: Example demonstrating solver introspection APIs
    (getUnits, getNonUnits, getTrail)

Author:

    GitHub Copilot 2024-01-09

Notes:
    
    This example demonstrates the use of the following solver introspection methods:
    - getUnits(): Retrieves currently inferred unit literals
    - getNonUnits(): Retrieves non-unit atomic formulas in the solver state
    - getTrail(): Retrieves the solver decision trail
    
    These methods are useful for:
    - Debugging solver behavior
    - Understanding solver decisions
    - Implementing custom solving strategies
    - Analyzing propagation
--*/

import com.microsoft.z3.*;

class SolverIntrospectionExample {
    
    /**
     * Demonstrates getUnits() and getNonUnits() with a basic solver
     */
    static void demonstrateUnitsAndNonUnits(Context ctx) throws Z3Exception {
        System.out.println("=== Demonstrating getUnits() and getNonUnits() ===\n");
        
        Solver solver = ctx.mkSolver();
        
        // Create some boolean variables
        BoolExpr x = ctx.mkBoolConst("x");
        BoolExpr y = ctx.mkBoolConst("y");
        BoolExpr z = ctx.mkBoolConst("z");
        
        // Add constraints
        solver.add(ctx.mkOr(x, y));
        solver.add(ctx.mkOr(ctx.mkNot(x), z));
        
        System.out.println("Constraints:");
        System.out.println("  " + ctx.mkOr(x, y));
        System.out.println("  " + ctx.mkOr(ctx.mkNot(x), z));
        
        // Check satisfiability
        Status status = solver.check();
        System.out.println("\nStatus: " + status);
        
        if (status == Status.SATISFIABLE) {
            // Get units - literals that have been inferred by the solver
            BoolExpr[] units = solver.getUnits();
            System.out.println("\nUnits (inferred literals): " + units.length);
            for (BoolExpr unit : units) {
                System.out.println("  " + unit);
            }
            
            // Get non-units - atomic formulas that are not units
            BoolExpr[] nonUnits = solver.getNonUnits();
            System.out.println("\nNon-units (atomic formulas not inferred as units): " + nonUnits.length);
            for (BoolExpr nonUnit : nonUnits) {
                System.out.println("  " + nonUnit);
            }
        }
        System.out.println();
    }
    
    /**
     * Demonstrates getTrail() with a SimpleSolver
     */
    static void demonstrateTrail(Context ctx) throws Z3Exception {
        System.out.println("=== Demonstrating getTrail() ===\n");
        
        // Use SimpleSolver for trail support
        Solver solver = ctx.mkSimpleSolver();
        
        // Create boolean variables
        BoolExpr a = ctx.mkBoolConst("a");
        BoolExpr b = ctx.mkBoolConst("b");
        BoolExpr c = ctx.mkBoolConst("c");
        
        // Add constraints that will cause propagation
        solver.add(ctx.mkOr(a, b));      // a or b must be true
        solver.add(ctx.mkNot(b));         // b is false, so a must be true
        solver.add(ctx.mkOr(ctx.mkNot(a), c));  // if a is true, then c must be true
        
        System.out.println("Constraints:");
        System.out.println("  " + ctx.mkOr(a, b));
        System.out.println("  " + ctx.mkNot(b));
        System.out.println("  " + ctx.mkOr(ctx.mkNot(a), c));
        
        // Check satisfiability
        Status status = solver.check();
        System.out.println("\nStatus: " + status);
        
        if (status == Status.SATISFIABLE) {
            // Get the trail - sequence of decisions and propagations
            BoolExpr[] trail = solver.getTrail();
            System.out.println("\nTrail (sequence of assignments): " + trail.length);
            for (int i = 0; i < trail.length; i++) {
                System.out.println("  [" + i + "] " + trail[i]);
            }
            
            // Get units to see what was propagated
            BoolExpr[] units = solver.getUnits();
            System.out.println("\nUnits: " + units.length);
            for (BoolExpr unit : units) {
                System.out.println("  " + unit);
            }
            
            // Get the model
            Model model = solver.getModel();
            System.out.println("\nModel:");
            System.out.println("  a = " + model.eval(a, false));
            System.out.println("  b = " + model.eval(b, false));
            System.out.println("  c = " + model.eval(c, false));
        }
        System.out.println();
    }
    
    /**
     * Demonstrates introspection with arithmetic constraints
     */
    static void demonstrateArithmeticIntrospection(Context ctx) throws Z3Exception {
        System.out.println("=== Demonstrating introspection with arithmetic ===\n");
        
        Solver solver = ctx.mkSimpleSolver();
        
        // Create integer variables
        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        
        // Create boolean conditions
        BoolExpr cond1 = ctx.mkGt(x, ctx.mkInt(0));
        BoolExpr cond2 = ctx.mkLt(y, ctx.mkInt(10));
        BoolExpr cond3 = ctx.mkEq(ctx.mkAdd(x, y), ctx.mkInt(15));
        
        // Add constraints
        solver.add(cond1);
        solver.add(cond2);
        solver.add(cond3);
        
        System.out.println("Constraints:");
        System.out.println("  " + cond1);
        System.out.println("  " + cond2);
        System.out.println("  " + cond3);
        
        // Check satisfiability
        Status status = solver.check();
        System.out.println("\nStatus: " + status);
        
        if (status == Status.SATISFIABLE) {
            // Get units
            BoolExpr[] units = solver.getUnits();
            System.out.println("\nUnits: " + units.length);
            for (BoolExpr unit : units) {
                System.out.println("  " + unit);
            }
            
            // Get trail
            BoolExpr[] trail = solver.getTrail();
            System.out.println("\nTrail length: " + trail.length);
            if (trail.length > 0) {
                System.out.println("First few trail entries:");
                for (int i = 0; i < Math.min(5, trail.length); i++) {
                    System.out.println("  [" + i + "] " + trail[i]);
                }
                if (trail.length > 5) {
                    System.out.println("  ... (" + (trail.length - 5) + " more)");
                }
            }
            
            // Get the model
            Model model = solver.getModel();
            System.out.println("\nModel:");
            System.out.println("  x = " + model.eval(x, false));
            System.out.println("  y = " + model.eval(y, false));
        }
        System.out.println();
    }
    
    /**
     * Main entry point
     */
    public static void main(String[] args) {
        try {
            System.out.println("Z3 Solver Introspection API Examples");
            System.out.println("=====================================\n");
            
            Context ctx = new Context();
            
            // Run demonstrations
            demonstrateUnitsAndNonUnits(ctx);
            demonstrateTrail(ctx);
            demonstrateArithmeticIntrospection(ctx);
            
            System.out.println("All examples completed successfully!");
            
            ctx.close();
            
        } catch (Z3Exception e) {
            System.err.println("Z3 Exception: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
    }
}
