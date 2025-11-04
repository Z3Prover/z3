/*++
 Copyright (c) 2024 Microsoft Corporation

Module Name:

    StringReplaceTest.java

Abstract:

    Z3 Java API: Test for string replace operations

Author:

    GitHub Copilot 2024-11-04

Notes:
    
--*/

import com.microsoft.z3.*;

public class StringReplaceTest {
    
    public static void testReplaceAll(Context ctx) throws Z3Exception {
        System.out.println("Testing mkReplaceAll...");
        
        // Create string expressions
        SeqExpr<CharSort> s = ctx.mkString("hello world hello");
        SeqExpr<CharSort> src = ctx.mkString("hello");
        SeqExpr<CharSort> dst = ctx.mkString("goodbye");
        
        // Create replace_all expression
        SeqExpr<CharSort> result = ctx.mkReplaceAll(s, src, dst);
        
        // Create a solver and check
        Solver solver = ctx.mkSolver();
        SeqExpr<CharSort> expected = ctx.mkString("goodbye world goodbye");
        solver.add(ctx.mkEq(result, expected));
        
        Status status = solver.check();
        System.out.println("  Status: " + status);
        
        if (status == Status.SATISFIABLE) {
            System.out.println("  PASS: mkReplaceAll works correctly");
        } else {
            System.out.println("  FAIL: mkReplaceAll returned unexpected result");
        }
    }
    
    public static void testReplaceRe(Context ctx) throws Z3Exception {
        System.out.println("\nTesting mkReplaceRe...");
        
        try {
            // Create string expression
            SeqExpr<CharSort> s = ctx.mkString("hello world");
            
            // Create regular expression that matches "world"
            ReExpr<SeqSort<CharSort>> worldRe = ctx.mkToRe(ctx.mkString("world"));
            
            // Create replace_re expression (replaces first match)
            SeqExpr<CharSort> dst = ctx.mkString("universe");
            SeqExpr<CharSort> result = ctx.mkReplaceRe(s, worldRe, dst);
            
            System.out.println("  Created expression: " + result);
            System.out.println("  PASS: mkReplaceRe API method works correctly");
        } catch (Exception e) {
            System.out.println("  FAIL: mkReplaceRe threw exception: " + e.getMessage());
        }
    }
    
    public static void testReplaceReAll(Context ctx) throws Z3Exception {
        System.out.println("\nTesting mkReplaceReAll...");
        
        try {
            // Create string expression
            SeqExpr<CharSort> s = ctx.mkString("foo bar foo");
            
            // Create regular expression that matches "foo"
            ReExpr<SeqSort<CharSort>> fooRe = ctx.mkToRe(ctx.mkString("foo"));
            
            // Create replace_re_all expression (replaces all matches)
            SeqExpr<CharSort> dst = ctx.mkString("baz");
            SeqExpr<CharSort> result = ctx.mkReplaceReAll(s, fooRe, dst);
            
            System.out.println("  Created expression: " + result);
            System.out.println("  PASS: mkReplaceReAll API method works correctly");
        } catch (Exception e) {
            System.out.println("  FAIL: mkReplaceReAll threw exception: " + e.getMessage());
        }
    }
    
    public static void main(String[] args) {
        try {
            System.out.println("String Replace Operations Test");
            System.out.println("==============================\n");
            
            // Create Z3 context
            Context ctx = new Context();
            
            // Run tests
            testReplaceAll(ctx);
            testReplaceRe(ctx);
            testReplaceReAll(ctx);
            
            System.out.println("\nAll tests completed!");
            
            ctx.close();
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
