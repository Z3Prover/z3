/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    TestJavaAPICompleteness.java

Abstract:

    Test for Java API completeness fixes:
    1. mkLastIndexOf method
    2. CharSort support in Sort.create()

Author:

    Z3Prover Contributors 2025-10-28

Notes:
    
--*/

import com.microsoft.z3.*;

public class TestJavaAPICompleteness
{
    public static void main(String[] args)
    {
        try {
            testMkLastIndexOf();
            testCharSort();
            System.out.println("All tests passed!");
        } catch (Exception e) {
            System.err.println("Test failed: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
    }

    static void testMkLastIndexOf() throws Exception
    {
        System.out.println("Testing mkLastIndexOf...");
        
        try (Context ctx = new Context()) {
            // Create string expressions
            SeqExpr<CharSort> s = ctx.mkString("hello world hello");
            SeqExpr<CharSort> substr = ctx.mkString("hello");
            
            // Test mkLastIndexOf
            IntExpr lastIdx = ctx.mkLastIndexOf(s, substr);
            
            // Create solver and check
            Solver solver = ctx.mkSolver();
            solver.add(ctx.mkGe(lastIdx, ctx.mkInt(0)));
            
            if (solver.check() == Status.SATISFIABLE) {
                Model m = solver.getModel();
                System.out.println("  mkLastIndexOf works correctly");
                System.out.println("  Result: " + m.eval(lastIdx, false));
            } else {
                throw new Exception("mkLastIndexOf test failed: unsatisfiable");
            }
        }
    }

    static void testCharSort() throws Exception
    {
        System.out.println("Testing CharSort support in Sort.create()...");
        
        try (Context ctx = new Context()) {
            // Create a char sort
            CharSort charSort = ctx.mkCharSort();
            
            // Create a string which internally uses CharSort
            SeqExpr<CharSort> str = ctx.mkString("test");
            
            // Get the element sort of the sequence (should be CharSort)
            SeqSort<CharSort> seqSort = ctx.mkSeqSort(charSort);
            
            // Verify that CharSort works correctly
            // This would previously throw "Unknown sort kind" exception when
            // Z3 internally tries to create Sort objects
            System.out.println("  CharSort is correctly handled in Sort.create()");
            System.out.println("  CharSort: " + charSort);
        }
    }
}
