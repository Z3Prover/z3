/**
 * Test example for new sequence operations (SeqMap, SeqMapi, SeqFoldl, SeqFoldli)
 */

import com.microsoft.z3.*;

public class SeqOperationsExample {
    public static void main(String[] args) {
        Context ctx = new Context();
        
        try {
            System.out.println("Testing new sequence operations in Java API\n");
            
            // Test 1: mkSeqMap
            System.out.println("Test 1: mkSeqMap");
            IntSort intSort = ctx.mkIntSort();
            SeqSort<IntSort> seqIntSort = ctx.mkSeqSort(intSort);
            
            // Create a sequence variable
            Expr<SeqSort<IntSort>> seq = ctx.mkConst("s", seqIntSort);
            
            // Create a lambda function that adds 1 to an integer: (lambda (x) (+ x 1))
            Expr<IntSort> x = ctx.mkIntConst("x");
            Lambda<IntSort> f = ctx.mkLambda(new Expr<?>[] { x }, ctx.mkAdd(x, ctx.mkInt(1)));
            
            // Create map expression (conceptually maps f over seq)
            SeqExpr<IntSort> mapped = ctx.mkSeqMap(f, seq);
            System.out.println("mkSeqMap result type: " + mapped.getClass().getName());
            System.out.println("mkSeqMap created successfully: " + mapped);
            System.out.println();
            
            // Test 2: mkSeqMapi
            System.out.println("Test 2: mkSeqMapi");
            // Lambda that takes index and element: (lambda (i x) (+ x i))
            Expr<IntSort> xElem = ctx.mkIntConst("xElem");
            Expr<IntSort> iIdx = ctx.mkIntConst("iIdx");
            Lambda<IntSort> fWithIdx = ctx.mkLambda(new Expr<?>[] { iIdx, xElem }, ctx.mkAdd(xElem, iIdx));
            IntExpr i = ctx.mkIntConst("start_idx");
            SeqExpr<IntSort> mappedWithIndex = ctx.mkSeqMapi(fWithIdx, i, seq);
            System.out.println("mkSeqMapi result type: " + mappedWithIndex.getClass().getName());
            System.out.println("mkSeqMapi created successfully: " + mappedWithIndex);
            System.out.println();
            
            // Test 3: mkSeqFoldl
            System.out.println("Test 3: mkSeqFoldl");
            // Lambda that accumulates: (lambda (acc elem) (+ acc elem))
            IntExpr accVar = ctx.mkIntConst("accVar");
            IntExpr elemVar = ctx.mkIntConst("elemVar");
            Lambda<IntSort> foldFunc = ctx.mkLambda(new Expr<?>[] { accVar, elemVar }, ctx.mkAdd(accVar, elemVar));
            IntExpr acc = ctx.mkIntConst("acc");
            Expr<IntSort> folded = ctx.mkSeqFoldl(foldFunc, acc, seq);
            System.out.println("mkSeqFoldl result type: " + folded.getClass().getName());
            System.out.println("mkSeqFoldl created successfully: " + folded);
            System.out.println();
            
            // Test 4: mkSeqFoldli
            System.out.println("Test 4: mkSeqFoldli");
            // Lambda with index: (lambda (idx acc elem) (+ acc elem idx))
            IntExpr idxVar = ctx.mkIntConst("idxVar");
            IntExpr accVar2 = ctx.mkIntConst("accVar2");
            IntExpr elemVar2 = ctx.mkIntConst("elemVar2");
            ArithExpr<?> tempSum = ctx.mkAdd(accVar2, elemVar2);
            ArithExpr<?> finalSum = ctx.mkAdd(tempSum, idxVar);
            Lambda<IntSort> foldFuncWithIdx = ctx.mkLambda(
                new Expr<?>[] { idxVar, accVar2, elemVar2 }, 
                (IntExpr) finalSum);
            IntExpr idx = ctx.mkIntConst("start_idx2");
            IntExpr acc2 = ctx.mkIntConst("acc2");
            Expr<IntSort> foldedWithIndex = ctx.mkSeqFoldli(foldFuncWithIdx, idx, acc2, seq);
            System.out.println("mkSeqFoldli result type: " + foldedWithIndex.getClass().getName());
            System.out.println("mkSeqFoldli created successfully: " + foldedWithIndex);
            System.out.println();
            
            System.out.println("All tests passed!");
            
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        } finally {
            ctx.close();
        }
    }
}
