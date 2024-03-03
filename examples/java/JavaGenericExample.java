/*++
 Copyright (c) 2012 Microsoft Corporation

Module Name:

    Program.java

Abstract:

    Z3 Java API: Example program

Author:

    Christoph Wintersteiger (cwinter) 2012-11-27

Notes:
    
--*/

import com.microsoft.z3.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.util.stream.Stream.concat;

class JavaGenericExample
{
    @SuppressWarnings("serial")
    static class TestFailedException extends Exception
    {
        public TestFailedException()
        {
            super("Check FAILED");
        }
    }

    // / Create axiom: function f is injective in the i-th argument.

    // / <remarks>
    // / The following axiom is produced:
    // / <code>
    // / forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
    // / </code>
    // / Where, <code>finv</code>is a fresh function declaration.

    public <R extends Sort> BoolExpr injAxiom(Context ctx, FuncDecl<R> f, int i)
    {
        Sort[] domain = f.getDomain();
        int sz = f.getDomainSize();

        if (i >= sz)
        {
            System.out.println("failed to create inj axiom");
            return null;
        }

        /* declare the i-th inverse of f: finv */
        Sort finv_domain = f.getRange();
        Sort finv_range = domain[i];
        FuncDecl<Sort> finv = ctx.mkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        /* fill types, names and xs */
        Sort[] types = domain.clone();
        List<Expr<Sort>> xs = IntStream.range(0, sz).mapToObj(j -> ctx.mkBound(j, types[j])).collect(Collectors.toList());
        Symbol[] names = IntStream.range(0, sz).mapToObj(j -> ctx.mkSymbol(String.format("x_%d", j))).toArray(Symbol[]::new);

        Expr<Sort> x_i = xs.get(i);

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr<R> fxs = f.apply(xs.toArray(new Expr[0]));

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr<Sort> finv_fxs = finv.apply(fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        BoolExpr eq = ctx.mkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = ctx.mkPattern(fxs);

        /* create & assert quantifier */

        return ctx.mkForall(types, /* types of quantified variables */
                names, /* names of quantified variables */
                eq, 1, new Pattern[] { p } /* patterns */, null, null, null);
    }

    // / Create axiom: function f is injective in the i-th argument.

    // / <remarks>
    // / The following axiom is produced:
    // / <code>
    // / forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
    // / </code>
    // / Where, <code>finv</code>is a fresh function declaration.

    public <R extends Sort> BoolExpr injAxiomAbs(Context ctx, FuncDecl<R> f, int i)
    {
        Sort[] domain = f.getDomain();
        int sz = f.getDomainSize();

        if (i >= sz)
        {
            System.out.println("failed to create inj axiom");
            return null;
        }

        /* declare the i-th inverse of f: finv */
        R finv_domain = f.getRange();
        Sort finv_range = domain[i];
        FuncDecl<Sort> finv = ctx.mkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        List<Expr<Sort>> xs = IntStream.range(0, sz).mapToObj(j -> ctx.mkConst(String.format("x_%d", j), domain[j])).collect(Collectors.toList());

        /* fill types, names and xs */
        Expr<Sort> x_i = xs.get(i);

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr<R> fxs = f.apply(xs.toArray(new Expr[0]));

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr<Sort> finv_fxs = finv.apply(fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        BoolExpr eq = ctx.mkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = ctx.mkPattern(fxs);

        /* create & assert quantifier */
        return ctx.mkForall(xs.toArray(new Expr[0]), /* types of quantified variables */
                eq, /* names of quantified variables */
                1, new Pattern[] { p } /* patterns */, null, null, null);
    }

    // / Assert the axiom: function f is commutative.

    // / <remarks>
    // / This example uses the SMT-LIB parser to simplify the axiom
    // construction.
    // / </remarks>
    private <R extends Sort> BoolExpr commAxiom(Context ctx, FuncDecl<R> f) throws Exception
    {
        R t = f.getRange();
        Sort[] dom = f.getDomain();

        if (dom.length != 2 || !t.equals(dom[0]) || !t.equals(dom[1]))
        {
            System.out.printf("%d %s %s %s%n", dom.length, dom[0], dom[1], t);
            throw new Exception("function must be binary, and argument types must be equal to return type");
        }

        String bench = String.format("(assert (forall (x %s) (y %s) (= (%s x y) (%s y x))))", t.getName(), t.getName(), f.getName(), f.getName());
        return ctx.parseSMTLIB2String(bench, new Symbol[] { t.getName() },
                new Sort[] { t }, new Symbol[] { f.getName() },
                new FuncDecl[] { f })[0];
    }

    // / "Hello world" example: create a Z3 logical context, and delete it.

    public void simpleExample()
    {
        System.out.println("SimpleExample");
        Log.append("SimpleExample");

        {
            Context ctx = new Context();
            /* do something with the context */

            /* be kind to dispose manually and not wait for the GC. */
            ctx.close();
        }
    }

    @SuppressWarnings("unchecked")
    Model check(Context ctx, Expr<BoolSort> f, Status sat) throws TestFailedException
    {
        Solver s = ctx.mkSolver();
        s.add(f);
        if (s.check() != sat)
            throw new TestFailedException();
        if (sat == Status.SATISFIABLE)
            return s.getModel();
        else
            return null;
    }

    void solveTactical(Context ctx, Tactic t, Goal g, Status sat)
            throws TestFailedException
    {
        Solver s = ctx.mkSolver(t);
        System.out.printf("%nTactical solver: %s%n", s);

        s.add(g.getFormulas());
        System.out.printf("Solver: %s%n", s);

        if (s.check() != sat)
            throw new TestFailedException();
    }

    ApplyResult applyTactic(Context ctx, Tactic t, Goal g)
    {
        System.out.printf("%nGoal: %s%n", g);

        ApplyResult res = t.apply(g);
        System.out.printf("Application result: %s%n", res);

        Status q = Status.UNKNOWN;
        for (Goal sg : res.getSubgoals())
            if (sg.isDecidedSat())
                q = Status.SATISFIABLE;
            else if (sg.isDecidedUnsat())
                q = Status.UNSATISFIABLE;

        switch (q)
        {
        case UNKNOWN:
            System.out.println("Tactic result: Undecided");
            break;
        case SATISFIABLE:
            System.out.println("Tactic result: SAT");
            break;
        case UNSATISFIABLE:
            System.out.println("Tactic result: UNSAT");
            break;
        }

        return res;
    }

    void prove(Context ctx, Expr<BoolSort> f, boolean useMBQI) throws TestFailedException
    {
        BoolExpr[] assumptions = new BoolExpr[0];
        prove(ctx, f, useMBQI, assumptions);
    }

    @SafeVarargs
    final void prove(Context ctx, Expr<BoolSort> f, boolean useMBQI,
                     Expr<BoolSort>... assumptions) throws TestFailedException
    {
        System.out.printf("Proving: %s%n", f);
        Solver s = ctx.mkSolver();
        Params p = ctx.mkParams();
        p.add("mbqi", useMBQI);
        s.setParameters(p);
        s.add(assumptions);
        s.add(ctx.mkNot(f));
        Status q = s.check();

        switch (q)
        {
        case UNKNOWN:
            System.out.printf("Unknown because: %s%n", s.getReasonUnknown());
            break;
        case SATISFIABLE:
            throw new TestFailedException();
        case UNSATISFIABLE:
            System.out.printf("OK, proof: %s%n", s.getProof());
            break;
        }
    }

    void disprove(Context ctx, Expr<BoolSort> f, boolean useMBQI)
        throws TestFailedException
    {
        BoolExpr[] a = {};
        disprove(ctx, f, useMBQI, a);
    }

    @SafeVarargs
    final void disprove(Context ctx, Expr<BoolSort> f, boolean useMBQI,
                        Expr<BoolSort>... assumptions) throws TestFailedException
    {
        System.out.printf("Disproving: %s%n", f);
        Solver s = ctx.mkSolver();
        Params p = ctx.mkParams();
        p.add("mbqi", useMBQI);
        s.setParameters(p);
        s.add(assumptions);
        s.add(ctx.mkNot(f));
        Status q = s.check();

        switch (q)
        {
        case UNKNOWN:
            System.out.printf("Unknown because: %s%n", s.getReasonUnknown());
            break;
        case SATISFIABLE:
            System.out.printf("OK, model: %s%n", s.getModel());
            break;
        case UNSATISFIABLE:
            throw new TestFailedException();
        }
    }

    @SuppressWarnings("unchecked")
    void modelConverterTest(Context ctx) throws TestFailedException
    {
        System.out.println("ModelConverterTest");

        Expr<RealSort> xr = ctx.mkConst(ctx.mkSymbol("x"), ctx.mkRealSort());
        Expr<RealSort> yr = ctx.mkConst(ctx.mkSymbol("y"), ctx.mkRealSort());
        Goal g4 = ctx.mkGoal(true, false, false);
        g4.add(ctx.mkGt(xr, ctx.mkReal(10, 1)));
        g4.add(ctx.mkEq(yr, ctx.mkAdd(xr, ctx.mkReal(1, 1))));
        g4.add(ctx.mkGt(yr, ctx.mkReal(1, 1)));

        ApplyResult ar = applyTactic(ctx, ctx.mkTactic("simplify"), g4);
        if (ar.getNumSubgoals() == 1
                && (ar.getSubgoals()[0].isDecidedSat() || ar.getSubgoals()[0]
                        .isDecidedUnsat()))
            throw new TestFailedException();

        ar = applyTactic(ctx, ctx.andThen(ctx.mkTactic("simplify"),
                ctx.mkTactic("solve-eqs")), g4);
        if (ar.getNumSubgoals() == 1
                && (ar.getSubgoals()[0].isDecidedSat() || ar.getSubgoals()[0]
                        .isDecidedUnsat()))
            throw new TestFailedException();

        Solver s = ctx.mkSolver();
        for (BoolExpr e : ar.getSubgoals()[0].getFormulas())
            s.add(e);
        Status q = s.check();
        System.out.printf("Solver says: %s%n", q);
        System.out.printf("Model: %n%s%n", s.getModel());
        if (q != Status.SATISFIABLE)
            throw new TestFailedException();
    }

    // / A simple array example.

    @SuppressWarnings("unchecked")
    void arrayExample1(Context ctx) throws TestFailedException
    {
        System.out.println("ArrayExample1");
        Log.append("ArrayExample1");

        Goal g = ctx.mkGoal(true, false, false);
        ArraySort<IntSort, BitVecSort> asort = ctx.mkArraySort(ctx.getIntSort(),
                ctx.mkBitVecSort(32));
        Expr<ArraySort<IntSort, BitVecSort>> aex = ctx.mkConst(ctx.mkSymbol("MyArray"), asort);
        Expr<BitVecSort> sel = ctx.mkSelect(aex, ctx.mkInt(0));
        g.add(ctx.mkEq(sel, ctx.mkBV(42, 32)));
        Symbol xs = ctx.mkSymbol("x");
        IntExpr xc = (IntExpr) ctx.mkConst(xs, ctx.getIntSort());

        Symbol fname = ctx.mkSymbol("f");
        Sort[] domain = { ctx.getIntSort() };
        FuncDecl<IntSort> fd = ctx.mkFuncDecl(fname, domain, ctx.getIntSort());
        Expr<?>[] fargs = { ctx.mkConst(xs, ctx.getIntSort()) };
        Expr<IntSort> fapp = ctx.mkApp(fd, fargs);

        g.add(ctx.mkEq(ctx.mkAdd(xc, fapp), ctx.mkInt(123)));

        Solver s = ctx.mkSolver();
        for (BoolExpr a : g.getFormulas())
            s.add(a);
        System.out.printf("Solver: %s%n", s);

        Status q = s.check();
        System.out.printf("Status: %s%n", q);

        if (q != Status.SATISFIABLE)
            throw new TestFailedException();

        System.out.printf("Model = %s%n", s.getModel());

        System.out.printf("Interpretation of MyArray:%n%s%n", s.getModel().getFuncInterp(aex.getFuncDecl()));
        System.out.printf("Interpretation of x:%n%s%n", s.getModel().getConstInterp(xc));
        System.out.printf("Interpretation of f:%n%s%n", s.getModel().getFuncInterp(fd));
        System.out.printf("Interpretation of MyArray as Term:%n%s%n", s.getModel().getFuncInterp(aex.getFuncDecl()));
    }

    // / Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2
    // = i3 or select(a1, i3) = select(a2, i3))</tt>.

    // / <remarks>This example demonstrates how to use the array
    // theory.</remarks>
    public void arrayExample2(Context ctx) throws TestFailedException
    {
        System.out.println("ArrayExample2");
        Log.append("ArrayExample2");

        IntSort int_type = ctx.getIntSort();
        ArraySort<IntSort, IntSort> array_type = ctx.mkArraySort(int_type, int_type);

        Expr<ArraySort<IntSort, IntSort>> a1 = ctx.mkConst("a1", array_type);
        ArrayExpr<IntSort, IntSort> a2 = ctx.mkArrayConst("a2", int_type, int_type);
        Expr<IntSort> i1 = ctx.mkConst("i1", int_type);
        Expr<IntSort> i2 = ctx.mkConst("i2", int_type);
        Expr<IntSort> i3 = ctx.mkConst("i3", int_type);
        Expr<IntSort> v1 = ctx.mkConst("v1", int_type);
        Expr<IntSort> v2 = ctx.mkConst("v2", int_type);

        ArrayExpr<IntSort, IntSort> st1 = ctx.mkStore(a1, i1, v1);
        ArrayExpr<IntSort, IntSort> st2 = ctx.mkStore(a2, i2, v2);

        Expr<IntSort> sel1 = ctx.mkSelect(a1, i3);
        Expr<IntSort> sel2 = ctx.mkSelect(a2, i3);

        /* create antecedent */
        BoolExpr antecedent = ctx.mkEq(st1, st2);

        /*
         * create consequent: i1 = i3 or i2 = i3 or select(a1, i3) = select(a2,
         * i3)
         */
        BoolExpr consequent = ctx.mkOr(ctx.mkEq(i1, i3), ctx.mkEq(i2, i3), ctx.mkEq(sel1, sel2));

        /*
         * prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 =
         * i3 or select(a1, i3) = select(a2, i3))
         */
        BoolExpr thm = ctx.mkImplies(antecedent, consequent);
        System.out.println("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))");
        System.out.println(thm);
        prove(ctx, thm, false);
    }

    // / Show that <code>distinct(a_0, ... , a_n)</code> is
    // / unsatisfiable when <code>a_i</code>'s are arrays from boolean to
    // / boolean and n > 4.

    // / <remarks>This example also shows how to use the <code>distinct</code>
    // construct.</remarks>
    @SuppressWarnings("unchecked")
    public void arrayExample3(Context ctx) throws TestFailedException
    {
        System.out.println("ArrayExample3");
        Log.append("ArrayExample2");

        for (int n = 2; n <= 5; n++)
        {
            System.out.printf("n = %d%n", n);

            BoolSort bool_type = ctx.mkBoolSort();
            ArraySort<BoolSort, BoolSort> array_type = ctx.mkArraySort(bool_type, bool_type);
            List<Expr<ArraySort<BoolSort, BoolSort>>> a = IntStream.range(0, n).mapToObj(i -> ctx.mkConst(String.format("array_%d", i), array_type)).collect(Collectors.toList());

            /* create arrays */

            /* assert distinct(a[0], ..., a[n]) */
            BoolExpr d = ctx.mkDistinct(a.toArray(new Expr[0]));
            System.out.println(d);

            /* context is satisfiable if n < 5 */
            Model model = check(ctx, d, n < 5 ? Status.SATISFIABLE : Status.UNSATISFIABLE);
            if (n < 5)
            {
                for (int i = 0; i < n; i++)
                {
                    System.out.printf("%s = %s%n", a.get(i), model.evaluate(a.get(i), false));
                }
            }
        }
    }

    // / Sudoku solving example.

    @SuppressWarnings({"unchecked", "CodeBlock2Expr"})
    void sudokuExample(Context ctx) throws TestFailedException
    {
        System.out.println("SudokuExample");
        Log.append("SudokuExample");

        // 9x9 matrix of integer variables
        List<List<Expr<IntSort>>> X = IntStream.range(0, 9).mapToObj(i -> IntStream.range(0, 9).mapToObj(j ->
                ctx.mkConst(ctx.mkSymbol(String.format("x_%d_%d", i + 1, j + 1)), ctx.getIntSort()))
                .collect(Collectors.toList())).collect(Collectors.toList());

        // each cell contains a value in {1, ..., 9}
        List<List<BoolExpr>> cells_c = X.stream().map(r -> r.stream().map(c ->
                ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), c), ctx.mkLe(c, ctx.mkInt(9))))
                .collect(Collectors.toList())).collect(Collectors.toList());

        // each row contains a digit at most once
        List<BoolExpr> rows_c = new ArrayList<>();
        for (int i1 = 0; i1 < 9; i1++) {
            BoolExpr boolExpr = ctx.mkDistinct(X.get(i1).toArray(new Expr[0]));
            rows_c.add(boolExpr);
        }

        // each column contains a digit at most once
        List<BoolExpr> cols_c = new ArrayList<>();
        for (int idx = 0; idx < 9; idx++) {
            int j1 = idx;
            BoolExpr boolExpr = ctx.mkDistinct(X.stream().map(r -> r.get(j1)).toArray(Expr[]::new));
            cols_c.add(boolExpr);
        }

        // each 3x3 square contains a digit at most once
        List<List<BoolExpr>> sq_c = new ArrayList<>();
        for (int i0 = 0; i0 < 3; i0++) {
            List<BoolExpr> collect = new ArrayList<>();
            for (int j0 = 0; j0 < 3; j0++) {
                List<Expr<IntSort>> list = new ArrayList<>();
                for (int i = 0; i < 3; i++) {
                    for (int j = 0; j < 3; j++) {
                        Expr<IntSort> intSortExpr = X.get(3 * i0 + i).get(3 * j0 + j);
                        list.add(intSortExpr);
                    }
                }
                BoolExpr boolExpr = ctx.mkDistinct(list.toArray(new Expr[0]));
                collect.add(boolExpr);
            }
            sq_c.add(collect);
        }

        Stream<BoolExpr> sudoku_s = cells_c.stream().flatMap(Collection::stream);
        sudoku_s = concat(sudoku_s, rows_c.stream());
        sudoku_s = concat(sudoku_s, cols_c.stream());
        sudoku_s = concat(sudoku_s, sq_c.stream().flatMap(Collection::stream));
        BoolExpr sudoku_c = ctx.mkAnd(sudoku_s.toArray(BoolExpr[]::new));

        // sudoku instance, we use '0' for empty cells
        int[][] instance = {
                { 0, 0, 0, 0, 9, 4, 0, 3, 0 },
                { 0, 0, 0, 5, 1, 0, 0, 0, 7 },
                { 0, 8, 9, 0, 0, 0, 0, 4, 0 },
                { 0, 0, 0, 0, 0, 0, 2, 0, 8 },
                { 0, 6, 0, 2, 0, 1, 0, 5, 0 },
                { 1, 0, 2, 0, 0, 0, 0, 0, 0 },
                { 0, 7, 0, 0, 0, 0, 5, 2, 0 },
                { 9, 0, 0, 0, 6, 5, 0, 0, 0 },
                { 0, 4, 0, 9, 7, 0, 0, 0, 0 }
        };

        // assert the variables we know
        BoolExpr instance_c = ctx.mkAnd(IntStream.range(0, 9).boxed().flatMap(i -> IntStream.range(0, 9).filter(j -> instance[i][j] != 0).mapToObj(j -> ctx.mkEq(X.get(i).get(j), ctx.mkInt(instance[i][j])))).toArray(Expr[]::new));

        Solver s = ctx.mkSolver();
        s.add(sudoku_c);
        s.add(instance_c);

        if (s.check() == Status.SATISFIABLE)
        {
            Model m = s.getModel();
            List<List<Expr<IntSort>>> R = X.stream().map(r -> r.stream().map(c -> m.eval(c, false)).collect(Collectors.toList())).collect(Collectors.toList());
            System.out.println("Sudoku solution:");
            R.forEach(r -> System.out.println(r.stream().map(Objects::toString).collect(Collectors.joining(" "))));
        } else
        {
            System.out.println("Failed to solve sudoku");
            throw new TestFailedException();
        }
    }

    // / A basic example of how to use quantifiers.

    @SuppressWarnings("unchecked")
    void quantifierExample1(Context ctx)
    {
        System.out.println("QuantifierExample");
        Log.append("QuantifierExample");

        IntSort[] types = new IntSort[3];
        Arrays.fill(types, ctx.getIntSort());
        Symbol[] names = IntStream.range(0, 3).mapToObj(j -> ctx.mkSymbol(String.format("x_%d", j))).toArray(Symbol[]::new);
        List<Expr<IntSort>> xs = IntStream.range(0, 3).mapToObj(j -> ctx.mkConst(names[j], types[j])).collect(Collectors.toList());
        List<Expr<IntSort>> vars = IntStream.range(0, 3).mapToObj(j -> ctx.mkBound(2 - j, types[j])).collect(Collectors.toList());

        BoolExpr body_vars = ctx.mkAnd(
                ctx.mkEq(ctx.mkAdd(vars.get(0), ctx.mkInt(1)), ctx.mkInt(2)),
                ctx.mkEq(ctx.mkAdd(vars.get(1), ctx.mkInt(2)),
                        ctx.mkAdd(vars.get(2), ctx.mkInt(3))));

        BoolExpr body_const = ctx.mkAnd(
                ctx.mkEq(ctx.mkAdd(xs.get(0), ctx.mkInt(1)), ctx.mkInt(2)),
                ctx.mkEq(ctx.mkAdd(xs.get(1), ctx.mkInt(2)),
                        ctx.mkAdd(xs.get(2), ctx.mkInt(3))));

        Quantifier x = ctx.mkForall(types, names, body_vars, 1, null, null,
                ctx.mkSymbol("Q1"), ctx.mkSymbol("skid1"));
        System.out.printf("Quantifier X: %s%n", x.toString());

        Quantifier y = ctx.mkForall(xs.toArray(new Expr[0]), body_const, 1, null, null,
                ctx.mkSymbol("Q2"), ctx.mkSymbol("skid2"));
        System.out.printf("Quantifier Y: %s%n", y.toString());
    }

    void quantifierExample2(Context ctx)
    {

        System.out.println("QuantifierExample2");
        Log.append("QuantifierExample2");

        Quantifier q1, q2;
        FuncDecl<IntSort> f = ctx.mkFuncDecl("f", ctx.getIntSort(), ctx.getIntSort());
        FuncDecl<IntSort> g = ctx.mkFuncDecl("g", ctx.getIntSort(), ctx.getIntSort());

        // Quantifier with Exprs as the bound variables.
        {
            Expr<IntSort> x = ctx.mkConst("x", ctx.getIntSort());
            Expr<IntSort> y = ctx.mkConst("y", ctx.getIntSort());
            Expr<IntSort> f_x = ctx.mkApp(f, x);
            Expr<IntSort> f_y = ctx.mkApp(f, y);
            Expr<IntSort> g_y = ctx.mkApp(g, y);
            @SuppressWarnings("unused")
            Pattern[] pats = new Pattern[] { ctx.mkPattern(f_x, g_y) };
            Expr[] no_pats = new Expr[] { f_y };
            Expr[] bound = new Expr[] { x, y };
            BoolExpr body = ctx.mkAnd(ctx.mkEq(f_x, f_y), ctx.mkEq(f_y, g_y));

            q1 = ctx.mkForall(bound, body, 1, null, no_pats, ctx.mkSymbol("q"),
                    ctx.mkSymbol("sk"));

            System.out.println(q1);
        }

        // Quantifier with de-Bruijn indices.
        {
            Expr<IntSort> x = ctx.mkBound(1, ctx.getIntSort());
            Expr<IntSort> y = ctx.mkBound(0, ctx.getIntSort());
            Expr<IntSort> f_x = ctx.mkApp(f, x);
            Expr<IntSort> f_y = ctx.mkApp(f, y);
            Expr<IntSort> g_y = ctx.mkApp(g, y);
            @SuppressWarnings("unused")
            Pattern[] pats = new Pattern[] { ctx.mkPattern(f_x, g_y) };
            Expr[] no_pats = new Expr[] { f_y };
            Symbol[] names = new Symbol[] { ctx.mkSymbol("x"),
                    ctx.mkSymbol("y") };
            Sort[] sorts = new Sort[] { ctx.getIntSort(), ctx.getIntSort() };
            BoolExpr body = ctx.mkAnd(ctx.mkEq(f_x, f_y), ctx.mkEq(f_y, g_y));

            q2 = ctx.mkForall(sorts, names, body, 1, null, // pats,
                    no_pats, ctx.mkSymbol("q"), ctx.mkSymbol("sk"));
            System.out.println(q2);
        }

        System.out.println(q1.equals(q2));
    }

    // / Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
    // / <code>f</code> is injective in the second argument. <seealso
    // cref="inj_axiom"/>

    public void quantifierExample3(Context ctx) throws TestFailedException
    {
        System.out.println("QuantifierExample3");
        Log.append("QuantifierExample3");

        /*
         * If quantified formulas are asserted in a logical context, then the
         * model produced by Z3 should be viewed as a potential model.
         */

        /* declare function f */
        IntSort I = ctx.getIntSort();
        FuncDecl<IntSort> f = ctx.mkFuncDecl("f", new Sort[] { I, I }, I);

        /* f is injective in the second argument. */
        BoolExpr inj = injAxiom(ctx, f, 1);

        /* create x, y, v, w, fxy, fwv */
        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr v = ctx.mkIntConst("v");
        IntExpr w = ctx.mkIntConst("w");
        Expr<IntSort> fxy = ctx.mkApp(f, x, y);
        Expr<IntSort> fwv = ctx.mkApp(f, w, v);

        /* f(x, y) = f(w, v) */
        BoolExpr p1 = ctx.mkEq(fxy, fwv);

        /* prove f(x, y) = f(w, v) implies y = v */
        BoolExpr p2 = ctx.mkEq(y, v);
        prove(ctx, p2, false, inj, p1);

        /* disprove f(x, y) = f(w, v) implies x = w */
        BoolExpr p3 = ctx.mkEq(x, w);
        disprove(ctx, p3, false, inj, p1);
    }

    // / Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
    // / <code>f</code> is injective in the second argument. <seealso
    // cref="inj_axiom"/>

    public void quantifierExample4(Context ctx) throws TestFailedException
    {
        System.out.println("QuantifierExample4");
        Log.append("QuantifierExample4");

        /*
         * If quantified formulas are asserted in a logical context, then the
         * model produced by Z3 should be viewed as a potential model.
         */

        /* declare function f */
        IntSort I = ctx.getIntSort();
        FuncDecl<IntSort> f = ctx.mkFuncDecl("f", new Sort[] { I, I }, I);

        /* f is injective in the second argument. */
        BoolExpr inj = injAxiomAbs(ctx, f, 1);

        /* create x, y, v, w, fxy, fwv */
        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr v = ctx.mkIntConst("v");
        IntExpr w = ctx.mkIntConst("w");
        Expr<IntSort> fxy = ctx.mkApp(f, x, y);
        Expr<IntSort> fwv = ctx.mkApp(f, w, v);

        /* f(x, y) = f(w, v) */
        BoolExpr p1 = ctx.mkEq(fxy, fwv);

        /* prove f(x, y) = f(w, v) implies y = v */
        BoolExpr p2 = ctx.mkEq(y, v);
        prove(ctx, p2, false, inj, p1);

        /* disprove f(x, y) = f(w, v) implies x = w */
        BoolExpr p3 = ctx.mkEq(x, w);
        disprove(ctx, p3, false, inj, p1);
    }

    // / Some basic tests.

    void basicTests(Context ctx) throws TestFailedException
    {
        System.out.println("BasicTests");

        Symbol fname = ctx.mkSymbol("f");
        Symbol x = ctx.mkSymbol("x");
        Symbol y = ctx.mkSymbol("y");

        BoolSort bs = ctx.mkBoolSort();

        Sort[] domain = { bs, bs };
        FuncDecl<BoolSort> f = ctx.mkFuncDecl(fname, domain, bs);
        Expr<BoolSort> fapp = ctx.mkApp(f, ctx.mkConst(x, bs), ctx.mkConst(y, bs));

        Expr<?>[] fargs2 = { ctx.mkFreshConst("cp", bs) };
        Sort[] domain2 = { bs };
        Expr<BoolSort> fapp2 = ctx.mkApp(ctx.mkFreshFuncDecl("fp", domain2, bs), fargs2);

        BoolExpr trivial_eq = ctx.mkEq(fapp, fapp);
        BoolExpr nontrivial_eq = ctx.mkEq(fapp, fapp2);

        Goal g = ctx.mkGoal(true, false, false);
        g.add(trivial_eq);
        g.add(nontrivial_eq);
        System.out.printf("Goal: %s%n", g);

        Solver solver = ctx.mkSolver();

        solver.add(g.getFormulas());

        if (solver.check() != Status.SATISFIABLE)
            throw new TestFailedException();

        ApplyResult ar = applyTactic(ctx, ctx.mkTactic("simplify"), g);
        if (ar.getNumSubgoals() == 1
                && (ar.getSubgoals()[0].isDecidedSat() || ar.getSubgoals()[0]
                        .isDecidedUnsat()))
            throw new TestFailedException();

        ar = applyTactic(ctx, ctx.mkTactic("smt"), g);
        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedSat())
            throw new TestFailedException();

        g.add(ctx.mkEq(ctx.mkNumeral(1, ctx.mkBitVecSort(32)),
                ctx.mkNumeral(2, ctx.mkBitVecSort(32))));
        ar = applyTactic(ctx, ctx.mkTactic("smt"), g);
        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedUnsat())
            throw new TestFailedException();

        Goal g2 = ctx.mkGoal(true, true, false);
        ar = applyTactic(ctx, ctx.mkTactic("smt"), g2);
        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedSat())
            throw new TestFailedException();

        g2 = ctx.mkGoal(true, true, false);
        g2.add(ctx.mkFalse());
        ar = applyTactic(ctx, ctx.mkTactic("smt"), g2);
        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedUnsat())
            throw new TestFailedException();

        Goal g3 = ctx.mkGoal(true, true, false);
        Expr<IntSort> xc = ctx.mkConst(ctx.mkSymbol("x"), ctx.getIntSort());
        Expr<IntSort> yc = ctx.mkConst(ctx.mkSymbol("y"), ctx.getIntSort());
        g3.add(ctx.mkEq(xc, ctx.mkNumeral(1, ctx.getIntSort())));
        g3.add(ctx.mkEq(yc, ctx.mkNumeral(2, ctx.getIntSort())));
        BoolExpr constr = ctx.mkEq(xc, yc);
        g3.add(constr);
        ar = applyTactic(ctx, ctx.mkTactic("smt"), g3);
        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedUnsat())
            throw new TestFailedException();

        modelConverterTest(ctx);

        // Real num/den test.
        RatNum rn = ctx.mkReal(42, 43);
        IntNum inum = rn.getNumerator();
        IntNum iden = rn.getDenominator();
        System.out.printf("Numerator: %s Denominator: %s%n", inum, iden);
        if (!inum.toString().equals("42") || !iden.toString().equals("43"))
            throw new TestFailedException();

        if (!rn.toDecimalString(3).equals("0.976?"))
            throw new TestFailedException();

        bigIntCheck(ctx, ctx.mkReal("-1231231232/234234333"));
        bigIntCheck(ctx, ctx.mkReal("-123123234234234234231232/234234333"));
        bigIntCheck(ctx, ctx.mkReal("-234234333"));
        bigIntCheck(ctx, ctx.mkReal("234234333/2"));

        String bn = "1234567890987654321";

        if (!ctx.mkInt(bn).getBigInteger().toString().equals(bn))
            throw new TestFailedException();

        if (!ctx.mkBV(bn, 128).getBigInteger().toString().equals(bn))
            throw new TestFailedException();

        if (ctx.mkBV(bn, 32).getBigInteger().toString().equals(bn))
            throw new TestFailedException();

        // Error handling test.
        try
        {
            @SuppressWarnings("unused")
            IntExpr i = ctx.mkInt("1/2");
            throw new TestFailedException(); // unreachable
        } catch (Z3Exception ignored)
        {
        }

        // Coercing type change in Z3
        Expr<IntSort> integerDivision = ctx.mkDiv(ctx.mkInt(1), ctx.mkInt(2));
        System.out.printf("%s -> %s%n", integerDivision, integerDivision.simplify()); // (div 1 2) -> 0

        Expr<RealSort> realDivision = ctx.mkDiv(ctx.mkReal(1), ctx.mkReal(2));
        System.out.printf("%s -> %s%n", realDivision, realDivision.simplify()); // (/ 1.0 2.0) -> 1/2

        Expr<ArithSort> mixedDivision1 = ctx.mkDiv(ctx.mkReal(1), ctx.mkInt(2));
        Expr<ArithSort> tmp = mixedDivision1;
        // the return type is a Expr<ArithSort> here but since we know it is a
        // real view it as such.
        Expr<RealSort> mixedDivision2 = mixedDivision1.distillSort(RealSort.class);
        System.out.printf("%s -> %s%n", mixedDivision2, mixedDivision2.simplify()); // (/ 1.0 (to_real 2)) -> 1/2

        // empty distillSort
        mixedDivision1.distillSort(ArithSort.class);

        try {
            mixedDivision1.distillSort(IntSort.class);
            throw new TestFailedException(); // unreachable
        } catch (Z3Exception exception) {
            System.out.println(exception); // com.microsoft.z3.Z3Exception: Cannot cast expression of sort
                                           // com.microsoft.z3.RealSort to com.microsoft.z3.IntSort.
        }
        
        Expr<BoolSort> eq1 = ctx.mkEq(realDivision, integerDivision);
        System.out.printf("%s -> %s%n", eq1, eq1.simplify()); // (= (/ 1.0 2.0) (to_real (div 1 2))) -> false

        Expr<BoolSort> eq2 = ctx.mkEq(realDivision, mixedDivision2);
        System.out.printf("%s -> %s%n", eq2, eq2.simplify()); // (= (/ 1.0 2.0) (/ 1.0 (to_real 2))) -> true
    }

    // / Shows how to use Solver(logic)

    // / @param ctx 
    void logicExample(Context ctx) throws TestFailedException
    {
        System.out.println("LogicTest");
        Log.append("LogicTest");

        Global.ToggleWarningMessages(true);

        BitVecSort bvs = ctx.mkBitVecSort(32);
        Expr<BitVecSort> x = ctx.mkConst("x", bvs);
        Expr<BitVecSort> y = ctx.mkConst("y", bvs);
        BoolExpr eq = ctx.mkEq(x, y);

        // Use a solver for QF_BV
        Solver s = ctx.mkSolver("QF_BV");
        s.add(eq);
        Status res = s.check();
        System.out.printf("solver result: %s%n", res);

        // Or perhaps a tactic for QF_BV
        Goal g = ctx.mkGoal(true, false, false);
        g.add(eq);

        Tactic t = ctx.mkTactic("qfbv");
        ApplyResult ar = t.apply(g);
        System.out.printf("tactic result: %s%n", ar);

        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedSat())
            throw new TestFailedException();
    }

    // / Demonstrates how to use the ParOr tactic.

    void parOrExample(Context ctx) throws TestFailedException
    {
        System.out.println("ParOrExample");
        Log.append("ParOrExample");

        BitVecSort bvs = ctx.mkBitVecSort(32);
        Expr<BitVecSort> x = ctx.mkConst("x", bvs);
        Expr<BitVecSort> y = ctx.mkConst("y", bvs);
        BoolExpr q = ctx.mkEq(x, y);

        Goal g = ctx.mkGoal(true, false, false);
        g.add(q);

        Tactic t1 = ctx.mkTactic("qfbv");
        Tactic t2 = ctx.mkTactic("qfbv");
        Tactic p = ctx.parOr(t1, t2);

        ApplyResult ar = p.apply(g);

        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedSat())
            throw new TestFailedException();
    }

    void bigIntCheck(Context ctx, RatNum r)
    {
        System.out.printf("Num: %s%n", r.getBigIntNumerator());
        System.out.printf("Den: %s%n", r.getBigIntDenominator());
    }

    // / Find a model for <code>x xor y</code>.

    public void findModelExample1(Context ctx) throws TestFailedException
    {
        System.out.println("FindModelExample1");
        Log.append("FindModelExample1");

        BoolExpr x = ctx.mkBoolConst("x");
        BoolExpr y = ctx.mkBoolConst("y");
        BoolExpr x_xor_y = ctx.mkXor(x, y);

        Model model = check(ctx, x_xor_y, Status.SATISFIABLE);
        System.out.printf("x = %s, y = %s%n", model.evaluate(x, false), model.evaluate(y, false));
    }

    // / Find a model for <tt>x < y + 1, x > 2</tt>.
    // / Then, assert <tt>not(x = y)</tt>, and find another model.

    public void findModelExample2(Context ctx) throws TestFailedException
    {
        System.out.println("FindModelExample2");
        Log.append("FindModelExample2");

        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntNum one = ctx.mkInt(1);
        IntNum two = ctx.mkInt(2);

        ArithExpr<IntSort> y_plus_one = ctx.mkAdd(y, one);

        BoolExpr c1 = ctx.mkLt(x, y_plus_one);
        BoolExpr c2 = ctx.mkGt(x, two);

        BoolExpr q = ctx.mkAnd(c1, c2);

        System.out.println("model for: x < y + 1, x > 2");
        Model model = check(ctx, q, Status.SATISFIABLE);
        System.out.printf("x = %s, y =%s%n", model.evaluate(x, false), model.evaluate(y, false));

        /* assert not(x = y) */
        BoolExpr x_eq_y = ctx.mkEq(x, y);
        BoolExpr c3 = ctx.mkNot(x_eq_y);

        q = ctx.mkAnd(q, c3);

        System.out.println("model for: x < y + 1, x > 2, not(x = y)");
        model = check(ctx, q, Status.SATISFIABLE);
        System.out.printf("x = %s, y = %s%n", model.evaluate(x, false), model.evaluate(y, false));
    }

    // / Prove <tt>x = y implies g(x) = g(y)</tt>, and
    // / disprove <tt>x = y implies g(g(x)) = g(y)</tt>.

    // / <remarks>This function demonstrates how to create uninterpreted
    // / types and functions.</remarks>
    public void proveExample1(Context ctx) throws TestFailedException
    {
        System.out.println("ProveExample1");
        Log.append("ProveExample1");

        /* create uninterpreted type. */
        UninterpretedSort U = ctx.mkUninterpretedSort(ctx.mkSymbol("U"));

        /* declare function g */
        FuncDecl<UninterpretedSort> g = ctx.mkFuncDecl("g", U, U);

        /* create x and y */
        Expr<UninterpretedSort> x = ctx.mkConst("x", U);
        Expr<UninterpretedSort> y = ctx.mkConst("y", U);
        /* create g(x), g(y) */
        Expr<UninterpretedSort> gx = g.apply(x);
        Expr<UninterpretedSort> gy = g.apply(y);

        /* assert x = y */
        BoolExpr eq = ctx.mkEq(x, y);

        /* prove g(x) = g(y) */
        BoolExpr f = ctx.mkEq(gx, gy);
        System.out.println("prove: x = y implies g(x) = g(y)");
        prove(ctx, ctx.mkImplies(eq, f), false);

        /* create g(g(x)) */
        Expr<UninterpretedSort> ggx = g.apply(gx);

        /* disprove g(g(x)) = g(y) */
        f = ctx.mkEq(ggx, gy);
        System.out.println("disprove: x = y implies g(g(x)) = g(y)");
        disprove(ctx, ctx.mkImplies(eq, f), false);

        /* Print the model using the custom model printer */
        Model m = check(ctx, ctx.mkNot(f), Status.SATISFIABLE);
        System.out.println(m);
    }

    // / Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0
    // </tt>.
    // / Then, show that <tt>z < -1</tt> is not implied.

    // / <remarks>This example demonstrates how to combine uninterpreted
    // functions
    // / and arithmetic.</remarks>
    public void proveExample2(Context ctx) throws TestFailedException
    {
        System.out.println("ProveExample2");
        Log.append("ProveExample2");

        /* declare function g */
        IntSort I = ctx.getIntSort();

        FuncDecl<IntSort> g = ctx.mkFuncDecl("g", I, I);

        /* create x, y, and z */
        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr z = ctx.mkIntConst("z");

        /* create gx, gy, gz */
        Expr<IntSort> gx = ctx.mkApp(g, x);
        Expr<IntSort> gy = ctx.mkApp(g, y);
        Expr<IntSort> gz = ctx.mkApp(g, z);

        /* create zero */
        IntNum zero = ctx.mkInt(0);

        /* assert not(g(g(x) - g(y)) = g(z)) */
        ArithExpr<IntSort> gx_gy = ctx.mkSub(gx, gy);
        Expr<IntSort> ggx_gy = ctx.mkApp(g, gx_gy);
        BoolExpr eq = ctx.mkEq(ggx_gy, gz);
        BoolExpr c1 = ctx.mkNot(eq);

        /* assert x + z <= y */
        ArithExpr<IntSort> x_plus_z = ctx.mkAdd(x, z);
        BoolExpr c2 = ctx.mkLe(x_plus_z, y);

        /* assert y <= x */
        BoolExpr c3 = ctx.mkLe(y, x);

        /* prove z < 0 */
        BoolExpr f = ctx.mkLt(z, zero);
        System.out.println("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0");
        prove(ctx, f, false, c1, c2, c3);

        /* disprove z < -1 */
        IntNum minus_one = ctx.mkInt(-1);
        f = ctx.mkLt(z, minus_one);
        System.out.println("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1");
        disprove(ctx, f, false, c1, c2, c3);
    }

    // / Show how push & pop can be used to create "backtracking" points.

    // / <remarks>This example also demonstrates how big numbers can be
    // / created in ctx.</remarks>
    public void pushPopExample1(Context ctx) throws TestFailedException
    {
        System.out.println("PushPopExample1");
        Log.append("PushPopExample1");

        /* create a big number */
        IntSort int_type = ctx.getIntSort();
        IntNum big_number = ctx.mkInt("1000000000000000000000000000000000000000000000000000000");

        /* create number 3 */
        IntExpr three = (IntExpr) ctx.mkNumeral("3", int_type);

        /* create x */
        IntExpr x = ctx.mkIntConst("x");

        Solver solver = ctx.mkSolver();

        /* assert x >= "big number" */
        BoolExpr c1 = ctx.mkGe(x, big_number);
        System.out.println("assert: x >= 'big number'");
        solver.add(c1);

        /* create a backtracking point */
        System.out.println("push");
        solver.push();

        /* assert x <= 3 */
        BoolExpr c2 = ctx.mkLe(x, three);
        System.out.println("assert: x <= 3");
        solver.add(c2);

        /* context is inconsistent at this point */
        if (solver.check() != Status.UNSATISFIABLE)
            throw new TestFailedException();

        /*
         * backtrack: the constraint x <= 3 will be removed, since it was
         * asserted after the last ctx.Push.
         */
        System.out.println("pop");
        solver.pop(1);

        /* the context is consistent again. */
        if (solver.check() != Status.SATISFIABLE)
            throw new TestFailedException();

        /* new constraints can be asserted... */

        /* create y */
        IntExpr y = ctx.mkIntConst("y");

        /* assert y > x */
        BoolExpr c3 = ctx.mkGt(y, x);
        System.out.println("assert: y > x");
        solver.add(c3);

        /* the context is still consistent. */
        if (solver.check() != Status.SATISFIABLE)
            throw new TestFailedException();
    }

    // / Tuples.

    // / <remarks>Check that the projection of a tuple
    // / returns the corresponding element.</remarks>
    public void tupleExample(Context ctx) throws TestFailedException
    {
        System.out.println("TupleExample");
        Log.append("TupleExample");

        IntSort int_type = ctx.getIntSort();
        TupleSort tuple = ctx.mkTupleSort(ctx.mkSymbol("mk_tuple"), // name of
                                                                    // tuple
                                                                    // constructor
                new Symbol[] { ctx.mkSymbol("first"), ctx.mkSymbol("second") }, // names
                                                                                // of
                                                                                // projection
                                                                                // operators
                new Sort[] { int_type, int_type } // types of projection
                                                  // operators
                );
        // have to cast here because it is not possible to type a member of an array of mixed generics
        @SuppressWarnings("unchecked")
        FuncDecl<IntSort> first = (FuncDecl<IntSort>) tuple.getFieldDecls()[0]; // declarations are for
                                                   // projections
        @SuppressWarnings("unused")
        FuncDecl<?> second = tuple.getFieldDecls()[1];
        Expr<IntSort> x = ctx.mkConst("x", int_type);
        Expr<IntSort> y = ctx.mkConst("y", int_type);
        Expr<TupleSort> n1 = tuple.mkDecl().apply(x, y);
        Expr<IntSort> n2 = first.apply(n1);
        BoolExpr n3 = ctx.mkEq(x, n2);
        System.out.printf("Tuple example: %s%n", n3);
        prove(ctx, n3, false);
    }

    // / Simple bit-vector example.

    // / <remarks>
    // / This example disproves that x - 10 &lt;= 0 IFF x &lt;= 10 for (32-bit)
    // machine integers
    // / </remarks>
    public void bitvectorExample1(Context ctx) throws TestFailedException
    {
        System.out.println("BitvectorExample1");
        Log.append("BitvectorExample1");

        BitVecSort bv_type = ctx.mkBitVecSort(32);
        Expr<BitVecSort> x = ctx.mkConst("x", bv_type);
        Expr<BitVecSort> zero = ctx.mkNumeral("0", bv_type);
        BitVecNum ten = ctx.mkBV(10, 32);
        BitVecExpr x_minus_ten = ctx.mkBVSub(x, ten);
        /* bvsle is signed less than or equal to */
        BoolExpr c1 = ctx.mkBVSLE(x, ten);
        BoolExpr c2 = ctx.mkBVSLE(x_minus_ten, zero);
        BoolExpr thm = ctx.mkIff(c1, c2);
        System.out.println("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers");
        disprove(ctx, thm, false);
    }

    // / Find x and y such that: x ^ y - 103 == x * y

    public void bitvectorExample2(Context ctx) throws TestFailedException
    {
        System.out.println("BitvectorExample2");
        Log.append("BitvectorExample2");

        /* construct x ^ y - 103 == x * y */
        BitVecSort bv_type = ctx.mkBitVecSort(32);
        BitVecExpr x = ctx.mkBVConst("x", 32);
        BitVecExpr y = ctx.mkBVConst("y", 32);
        BitVecExpr x_xor_y = ctx.mkBVXOR(x, y);
        Expr<BitVecSort> c103 = ctx.mkNumeral("103", bv_type);
        BitVecExpr lhs = ctx.mkBVSub(x_xor_y, c103);
        BitVecExpr rhs = ctx.mkBVMul(x, y);
        BoolExpr ctr = ctx.mkEq(lhs, rhs);

        System.out.println("find values of x and y, such that x ^ y - 103 == x * y");

        /* find a model (i.e., values for x an y that satisfy the constraint */
        Model m = check(ctx, ctr, Status.SATISFIABLE);
        System.out.println(m);
    }

    // / Demonstrates how to use the SMTLIB parser.

    public void parserExample1(Context ctx) throws TestFailedException
    {
        System.out.println("ParserExample1");
        Log.append("ParserExample1");

        BoolExpr f = ctx.parseSMTLIB2String(
                "(declare-const x Int) (declare-const y Int) (assert (and (> x y) (> x 0)))",
                null, null, null, null)[0];
        System.out.printf("formula %s%n", f);

        @SuppressWarnings("unused")
        Model m = check(ctx, f, Status.SATISFIABLE);
    }

    // / Demonstrates how to initialize the parser symbol table.

    public void parserExample2(Context ctx) throws TestFailedException
    {
        System.out.println("ParserExample2");
        Log.append("ParserExample2");

        Symbol[] declNames = { ctx.mkSymbol("a"), ctx.mkSymbol("b") };
        FuncDecl<IntSort> a = ctx.mkConstDecl(declNames[0], ctx.mkIntSort());
        FuncDecl<IntSort> b = ctx.mkConstDecl(declNames[1], ctx.mkIntSort());
        FuncDecl[] decls = new FuncDecl[] { a, b };

        BoolExpr f = ctx.parseSMTLIB2String("(assert (> a b))", null, null, declNames, decls)[0];
        System.out.printf("formula: %s%n", f);
        check(ctx, f, Status.SATISFIABLE);
    }

    // / Demonstrates how to initialize the parser symbol table.

    public void parserExample3(Context ctx) throws Exception
    {
        System.out.println("ParserExample3");
        Log.append("ParserExample3");

        /* declare function g */
        IntSort I = ctx.mkIntSort();
        FuncDecl<IntSort> g = ctx.mkFuncDecl("g", new Sort[] { I, I }, I);

        BoolExpr ca = commAxiom(ctx, g);

        BoolExpr thm = ctx.parseSMTLIB2String(
                "(declare-fun (Int Int) Int) (assert (forall ((x Int) (y Int)) (=> (= x y) (= (gg x 0) (gg 0 y)))))",
                null, null, new Symbol[] { ctx.mkSymbol("gg") },
                new FuncDecl[] { g })[0];
        System.out.printf("formula: %s%n", thm);
        prove(ctx, thm, false, ca);
    }


    // / Demonstrates how to handle parser errors using Z3 error handling
    // support.

    // / <remarks></remarks>
    public void parserExample5(Context ctx)
    {
        System.out.println("ParserExample5");

        try
        {
            ctx.parseSMTLIB2String(
                    /*
                     * the following string has a parsing error: missing
                     * parenthesis
                     */
                    "(declare-const x Int (declare-const y Int)) (assert (> x y))",
                    null, null, null, null);
        } catch (Z3Exception e)
        {
            System.out.printf("Z3 error: %s%n", e);
        }
    }

    // / Create an ite-Expr (if-then-else Exprs).

    public void iteExample(Context ctx)
    {
        System.out.println("ITEExample");
        Log.append("ITEExample");

        BoolExpr f = ctx.mkFalse();
        IntNum one = ctx.mkInt(1);
        IntNum zero = ctx.mkInt(0);
        Expr<IntSort> ite = ctx.mkITE(f, one, zero);

        System.out.printf("Expr: %s%n", ite);
    }

    // / Create an enumeration data type.

    public <T extends Sort> void enumExampleTyped(Context ctx) throws TestFailedException
    {
        System.out.println("EnumExample");
        Log.append("EnumExample");

        Symbol name = ctx.mkSymbol("fruit");

        EnumSort<T> fruit = ctx.mkEnumSort(name, ctx.mkSymbol("apple"),
                ctx.mkSymbol("banana"), ctx.mkSymbol("orange"));

        // helper function for consistent typing: https://docs.oracle.com/javase/tutorial/java/generics/capture.html
        System.out.println((fruit.getConsts()[0]));
        System.out.println((fruit.getConsts()[1]));
        System.out.println((fruit.getConsts()[2]));

        System.out.println((fruit.getTesterDecls()[0]));
        System.out.println((fruit.getTesterDecls()[1]));
        System.out.println((fruit.getTesterDecls()[2]));

        Expr<EnumSort<T>> apple = fruit.getConsts()[0];
        Expr<EnumSort<T>> banana = fruit.getConsts()[1];
        Expr<EnumSort<T>> orange = fruit.getConsts()[2];

        /* Apples are different from oranges */
        prove(ctx, ctx.mkNot(ctx.mkEq(apple, orange)), false);

        /* Apples pass the apple test */
        prove(ctx, ctx.mkApp(fruit.getTesterDecls()[0], apple),
                false);

        /* Oranges fail the apple test */
        disprove(ctx, ctx.mkApp(fruit.getTesterDecls()[0], orange), false);
        prove(ctx, ctx.mkNot(ctx.mkApp(fruit.getTesterDecls()[0], orange)), false);

        Expr<EnumSort<T>> fruity = ctx.mkConst("fruity", fruit);

        /* If something is fruity, then it is an apple, banana, or orange */

        prove(ctx, ctx.mkOr(ctx.mkEq(fruity, apple), ctx.mkEq(fruity, banana), ctx.mkEq(fruity, orange)), false);
    }

    // while you can do this untyped, it's safer to have a helper function -- this will prevent you from
    // mixing up your enum types
    public void enumExampleUntyped(Context ctx) throws TestFailedException
    {
        System.out.println("EnumExample");
        Log.append("EnumExample");

        Symbol name = ctx.mkSymbol("fruit2");

        EnumSort<Object> fruit = ctx.mkEnumSort(name, ctx.mkSymbol("apple2"),
                ctx.mkSymbol("banana2"), ctx.mkSymbol("orange2"));

        System.out.println((fruit.getConsts()[0]));
        System.out.println((fruit.getConsts()[1]));
        System.out.println((fruit.getConsts()[2]));

        System.out.println((fruit.getTesterDecls()[0]));
        System.out.println((fruit.getTesterDecls()[1]));
        System.out.println((fruit.getTesterDecls()[2]));

        Expr<EnumSort<Object>> apple = fruit.getConsts()[0];
        Expr<EnumSort<Object>> banana = fruit.getConsts()[1];
        Expr<EnumSort<Object>> orange = fruit.getConsts()[2];

        /* Apples are different from oranges */
        prove(ctx, ctx.mkNot(ctx.mkEq(apple, orange)), false);

        /* Apples pass the apple test */
        prove(ctx, ctx.mkApp(fruit.getTesterDecls()[0], apple),
                false);

        /* Oranges fail the apple test */
        disprove(ctx, ctx.mkApp(fruit.getTesterDecls()[0], orange), false);
        prove(ctx, ctx.mkNot(ctx.mkApp(fruit.getTesterDecls()[0], orange)), false);

        Expr<EnumSort<Object>> fruity = ctx.mkConst("fruity", fruit);

        /* If something is fruity, then it is an apple, banana, or orange */

        prove(ctx, ctx.mkOr(ctx.mkEq(fruity, apple), ctx.mkEq(fruity, banana), ctx.mkEq(fruity, orange)), false);
    }

    // / Create a list datatype.

    @SuppressWarnings("unchecked")
    public void listExample(Context ctx) throws TestFailedException
    {
        System.out.println("ListExample");
        Log.append("ListExample");

        IntSort int_ty = ctx.mkIntSort();

        ListSort<IntSort> int_list = ctx.mkListSort(ctx.mkSymbol("int_list"), int_ty);

        Expr<ListSort<IntSort>> nil = ctx.mkConst(int_list.getNilDecl());
        Expr<ListSort<IntSort>> l1 = ctx.mkApp(int_list.getConsDecl(), ctx.mkInt(1), nil);
        Expr<ListSort<IntSort>> l2 = ctx.mkApp(int_list.getConsDecl(), ctx.mkInt(2), nil);

        /* nil != cons(1, nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(nil, l1)), false);

        /* cons(2,nil) != cons(1, nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(l1, l2)), false);

        /* cons(x,nil) = cons(y, nil) => x = y */
        Expr<IntSort> x = ctx.mkConst("x", int_ty);
        Expr<IntSort> y = ctx.mkConst("y", int_ty);
        l1 = ctx.mkApp(int_list.getConsDecl(), x, nil);
        l2 = ctx.mkApp(int_list.getConsDecl(), y, nil);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* cons(x,u) = cons(x, v) => u = v */
        Expr<ListSort<IntSort>> u = ctx.mkConst("u", int_list);
        Expr<ListSort<IntSort>> v = ctx.mkConst("v", int_list);
        l1 = ctx.mkApp(int_list.getConsDecl(), x, u);
        l2 = ctx.mkApp(int_list.getConsDecl(), y, v);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(u, v)), false);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* is_nil(u) or is_cons(u) */
        prove(ctx, ctx.mkOr(ctx.mkApp(int_list.getIsNilDecl(), u), ctx.mkApp(int_list.getIsConsDecl(), u)), false);

        /* occurs check u != cons(x,u) */
        prove(ctx, ctx.mkNot(ctx.mkEq(u, l1)), false);

        /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
        BoolExpr fml1 = ctx.mkEq(u, ctx.mkApp(int_list.getConsDecl(),
                        ctx.mkApp(int_list.getHeadDecl(), u),
                        ctx.mkApp(int_list.getTailDecl(), u)));
        BoolExpr fml = ctx.mkImplies(ctx.mkApp(int_list.getIsConsDecl(), u), fml1);
        System.out.printf("Formula %s%n", fml);

        prove(ctx, fml, false);

        disprove(ctx, fml1, false);
    }

    // / Create a binary tree datatype.

    @SuppressWarnings("unchecked")
    public <Tree> void treeExample(Context ctx) throws TestFailedException
    {
        System.out.println("TreeExample");
        Log.append("TreeExample");

        String[] head_tail = new String[] { "car", "cdr" };
        Sort[] sorts = new Sort[] { null, null };
        int[] sort_refs = new int[] { 0, 0 };
        Constructor<Tree> nil_con, cons_con;

        nil_con = ctx.mkConstructor("nil", "is_nil", null, null, null);
        cons_con = ctx.mkConstructor("cons", "is_cons", head_tail, sorts,
                sort_refs);
        Constructor<Tree>[] constructors = new Constructor[] { nil_con, cons_con };

        DatatypeSort<Tree> cell = ctx.mkDatatypeSort("cell", constructors);

        FuncDecl<DatatypeSort<Tree>> nil_decl = nil_con.ConstructorDecl();
        FuncDecl<BoolSort> is_nil_decl = nil_con.getTesterDecl();
        FuncDecl<DatatypeSort<Tree>> cons_decl = cons_con.ConstructorDecl();
        FuncDecl<BoolSort> is_cons_decl = cons_con.getTesterDecl();
        FuncDecl<?>[] cons_accessors = cons_con.getAccessorDecls();
        FuncDecl<?> car_decl = cons_accessors[0];
        FuncDecl<?> cdr_decl = cons_accessors[1];

        Expr<DatatypeSort<Tree>> nil = ctx.mkConst(nil_decl);
        Expr<DatatypeSort<Tree>> l1 = ctx.mkApp(cons_decl, nil, nil);
        Expr<DatatypeSort<Tree>> l2 = ctx.mkApp(cons_decl, l1, nil);

        /* nil != cons(nil, nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(nil, l1)), false);

        /* cons(x,u) = cons(x, v) => u = v */
        Expr<DatatypeSort<Tree>> u = ctx.mkConst("u", cell);
        Expr<DatatypeSort<Tree>> v = ctx.mkConst("v", cell);
        Expr<DatatypeSort<Tree>> x = ctx.mkConst("x", cell);
        Expr<DatatypeSort<Tree>> y = ctx.mkConst("y", cell);
        l1 = ctx.mkApp(cons_decl, x, u);
        l2 = ctx.mkApp(cons_decl, y, v);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(u, v)), false);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* is_nil(u) or is_cons(u) */
        prove(ctx, ctx.mkOr(ctx.mkApp(is_nil_decl, u), ctx.mkApp(is_cons_decl, u)), false);

        /* occurs check u != cons(x,u) */
        prove(ctx, ctx.mkNot(ctx.mkEq(u, l1)), false);

        /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
        BoolExpr fml1 = ctx.mkEq(u, ctx.mkApp(cons_decl, ctx.mkApp(car_decl, u), ctx.mkApp(cdr_decl, u)));
        BoolExpr fml = ctx.mkImplies(ctx.mkApp(is_cons_decl, u), fml1);
        System.out.printf("Formula %s%n", fml);
        prove(ctx, fml, false);

        disprove(ctx, fml1, false);
    }

    // / Create a forest of trees.

    // / <remarks>
    // / forest ::= nil | cons(tree, forest)
    // / tree ::= nil | cons(forest, forest)
    // / </remarks>
    @SuppressWarnings({"unchecked", "unused", "UnusedAssignment"})
    public <Tree, Forest> void forestExample(Context ctx) throws TestFailedException
    {
        System.out.println("ForestExample");
        Log.append("ForestExample");

        DatatypeSort<Forest> forest;
        DatatypeSort<Tree> tree;
        FuncDecl<DatatypeSort<Forest>> nil1_decl, cons1_decl, cdr1_decl, car2_decl, cdr2_decl;
        FuncDecl<DatatypeSort<Tree>> car1_decl, nil2_decl, cons2_decl;
        FuncDecl<BoolSort> is_nil1_decl, is_nil2_decl, is_cons1_decl, is_cons2_decl;

        //
        // Declare the names of the accessors for cons.
        // Then declare the sorts of the accessors.
        // For this example, all sorts refer to the new types 'forest' and
        // 'tree'
        // being declared, so we pass in null for both sorts1 and sorts2.
        // On the other hand, the sort_refs arrays contain the indices of the
        // two new sorts being declared. The first element in sort1_refs
        // points to 'tree', which has index 1, the second element in sort1_refs
        // array points to 'forest', which has index 0.
        //
        Symbol[] head_tail1 = new Symbol[] { ctx.mkSymbol("head"),
                ctx.mkSymbol("tail") };
        Sort[] sorts1 = new Sort[] { null, null };
        int[] sort1_refs = new int[] { 1, 0 }; // the first item points to a
                                               // tree, the second to a forest

        Symbol[] head_tail2 = new Symbol[] { ctx.mkSymbol("car"),
                ctx.mkSymbol("cdr") };
        Sort[] sorts2 = new Sort[] { null, null };
        int[] sort2_refs = new int[] { 0, 0 }; // both items point to the forest
                                               // datatype.
        Constructor<Forest> nil1_con, cons1_con;
        Constructor<Tree> nil2_con, cons2_con;
        Constructor<Forest>[] constructors1 = new Constructor[2];
        Constructor<Tree>[] constructors2 = new Constructor[2];
        Symbol[] sort_names = { ctx.mkSymbol("forest"), ctx.mkSymbol("tree") };

        /* build a forest */
        nil1_con = ctx.mkConstructor(ctx.mkSymbol("nil1"),
                ctx.mkSymbol("is_nil1"), null, null, null);
        cons1_con = ctx.mkConstructor(ctx.mkSymbol("cons1"),
                ctx.mkSymbol("is_cons1"), head_tail1, sorts1, sort1_refs);
        constructors1[0] = nil1_con;
        constructors1[1] = cons1_con;

        /* build a tree */
        nil2_con = ctx.mkConstructor(ctx.mkSymbol("nil2"),
                ctx.mkSymbol("is_nil2"), null, null, null);
        cons2_con = ctx.mkConstructor(ctx.mkSymbol("cons2"),
                ctx.mkSymbol("is_cons2"), head_tail2, sorts2, sort2_refs);
        constructors2[0] = nil2_con;
        constructors2[1] = cons2_con;

        Constructor<Object>[][] clists = new Constructor[][] { constructors1,
                constructors2 };

        Sort[] sorts = ctx.mkDatatypeSorts(sort_names, clists);
        forest = (DatatypeSort<Forest>) sorts[0];
        tree = (DatatypeSort<Tree>) sorts[1];

        //
        // Now that the datatype has been created.
        // Query the constructors for the constructor
        // functions, testers, and field accessors.
        //
        nil1_decl = nil1_con.ConstructorDecl();
        is_nil1_decl = nil1_con.getTesterDecl();
        cons1_decl = cons1_con.ConstructorDecl();
        is_cons1_decl = cons1_con.getTesterDecl();
        FuncDecl<?>[] cons1_accessors = cons1_con.getAccessorDecls();
        car1_decl = (FuncDecl<DatatypeSort<Tree>>) cons1_accessors[0];
        cdr1_decl = (FuncDecl<DatatypeSort<Forest>>) cons1_accessors[1];

        nil2_decl = nil2_con.ConstructorDecl();
        is_nil2_decl = nil2_con.getTesterDecl();
        cons2_decl = cons2_con.ConstructorDecl();
        is_cons2_decl = cons2_con.getTesterDecl();
        FuncDecl<?>[] cons2_accessors = cons2_con.getAccessorDecls();
        car2_decl = (FuncDecl<DatatypeSort<Forest>>) cons2_accessors[0];
        cdr2_decl = (FuncDecl<DatatypeSort<Forest>>) cons2_accessors[1];

        Expr<DatatypeSort<Forest>> nil1 = ctx.mkConst(nil1_decl);
        Expr<DatatypeSort<Tree>> nil2 = ctx.mkConst(nil2_decl);
        Expr<DatatypeSort<Forest>> f1 = ctx.mkApp(cons1_decl, nil2, nil1);
        Expr<DatatypeSort<Tree>> t1 = ctx.mkApp(cons2_decl, nil1, nil1);
        Expr<DatatypeSort<Tree>> t2 = ctx.mkApp(cons2_decl, f1, nil1);
        Expr<DatatypeSort<Tree>> t3 = ctx.mkApp(cons2_decl, f1, f1);
        Expr<DatatypeSort<Tree>> t4 = ctx.mkApp(cons2_decl, nil1, f1);
        Expr<DatatypeSort<Forest>> f2 = ctx.mkApp(cons1_decl, t1, nil1);
        Expr<DatatypeSort<Forest>> f3 = ctx.mkApp(cons1_decl, t1, f1);

        /* nil != cons(nil,nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(nil1, f1)), false);
        prove(ctx, ctx.mkNot(ctx.mkEq(nil2, t1)), false);

        /* cons(x,u) = cons(x, v) => u = v */
        Expr<DatatypeSort<Forest>> u = ctx.mkConst("u", forest);
        Expr<DatatypeSort<Forest>> v = ctx.mkConst("v", forest);
        Expr<DatatypeSort<Tree>> x = ctx.mkConst("x", tree);
        Expr<DatatypeSort<Tree>> y = ctx.mkConst("y", tree);
        Expr<DatatypeSort<Forest>> l1 = ctx.mkApp(cons1_decl, x, u);
        Expr<DatatypeSort<Forest>> l2 = ctx.mkApp(cons1_decl, y, v);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(u, v)), false);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* is_nil(u) or is_cons(u) */
        prove(ctx, ctx.mkOr(ctx.mkApp(is_nil1_decl, u), ctx.mkApp(is_cons1_decl, u)), false);

        /* occurs check u != cons(x,u) */
        prove(ctx, ctx.mkNot(ctx.mkEq(u, l1)), false);
    }

    // / Demonstrate how to use #Eval.

    public void evalExample1(Context ctx)
    {
        System.out.println("EvalExample1");
        Log.append("EvalExample1");

        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntNum two = ctx.mkInt(2);

        Solver solver = ctx.mkSolver();

        /* assert x < y */
        solver.add(ctx.mkLt(x, y));

        /* assert x > 2 */
        solver.add(ctx.mkGt(x, two));

        /* find model for the constraints above */
        Model model = null;
        if (Status.SATISFIABLE == solver.check())
        {
            model = solver.getModel();
            System.out.println(model);
            System.out.println("\nevaluating x+y");
            Expr<IntSort> v = model.evaluate(ctx.mkAdd(x, y), false);
            if (v != null)
            {
                System.out.printf("result = %s%n", v);
            } else
            {
                System.out.println("Failed to evaluate: x+y");
            }
        } else
        {
            System.out.println("BUG, the constraints are satisfiable.");
        }
    }

    // / Demonstrate how to use #Eval on tuples.

    @SuppressWarnings("unchecked")
    public void evalExample2(Context ctx)
    {
        System.out.println("EvalExample2");
        Log.append("EvalExample2");

        IntSort int_type = ctx.getIntSort();
        TupleSort tuple = ctx.mkTupleSort(ctx.mkSymbol("mk_tuple"), // name of
                                                                    // tuple
                                                                    // constructor
                new Symbol[] { ctx.mkSymbol("first"), ctx.mkSymbol("second") }, // names
                                                                                // of
                                                                                // projection
                                                                                // operators
                new Sort[] { int_type, int_type } // types of projection
                                                  // operators
                );
        FuncDecl<IntSort> first = (FuncDecl<IntSort>) tuple.getFieldDecls()[0]; // declarations are for
                                                   // projections
        FuncDecl<IntSort> second = (FuncDecl<IntSort>) tuple.getFieldDecls()[1];
        Expr<TupleSort> tup1 = ctx.mkConst("t1", tuple);
        Expr<TupleSort> tup2 = ctx.mkConst("t2", tuple);

        Solver solver = ctx.mkSolver();

        /* assert tup1 != tup2 */
        solver.add(ctx.mkNot(ctx.mkEq(tup1, tup2)));
        /* assert first tup1 = first tup2 */
        solver.add(ctx.mkEq(ctx.mkApp(first, tup1), ctx.mkApp(first, tup2)));

        /* find model for the constraints above */
        Model model = null;
        if (Status.SATISFIABLE == solver.check())
        {
            model = solver.getModel();
            System.out.println(model);
            System.out.printf("evaluating tup1 %s%n", model.evaluate(tup1, false));
            System.out.printf("evaluating tup2 %s%n", model.evaluate(tup2, false));
            System.out.printf("evaluating second(tup2) %s%n", model.evaluate(ctx.mkApp(second, tup2), false));
        } else
        {
            System.out.println("BUG, the constraints are satisfiable.");
        }
    }

    // / Demonstrate how to use <code>Push</code>and <code>Pop</code>to
    // / control the size of models.

    // / <remarks>Note: this test is specialized to 32-bit bitvectors.</remarks>
    public void checkSmall(Context ctx, Solver solver, BitVecExpr... to_minimize)
    {
        int num_Exprs = to_minimize.length;
        int[] upper = new int[num_Exprs];
        int[] lower = new int[num_Exprs];
        for (int i = 0; i < upper.length; ++i)
        {
            upper[i] = Integer.MAX_VALUE;
            lower[i] = 0;
        }
        boolean some_work = true;
        int last_index = -1;
        int last_upper = 0;
        while (some_work)
        {
            solver.push();

            boolean check_is_sat = true;
            while (some_work)
            {
                // Assert all feasible bounds.
                for (int i = 0; i < num_Exprs; ++i)
                {
                    solver.add(ctx.mkBVULE(to_minimize[i],
                            ctx.mkBV(upper[i], 32)));
                }

                check_is_sat = Status.SATISFIABLE == solver.check();
                if (!check_is_sat)
                {
                    if (last_index != -1)
                    {
                        lower[last_index] = last_upper + 1;
                    }
                    break;
                }
                System.out.println(solver.getModel());

                // narrow the bounds based on the current model.
                for (int i = 0; i < num_Exprs; ++i)
                {
                    Expr<BitVecSort> v = solver.getModel().evaluate(to_minimize[i], false);
                    // we still have to cast because we want to use a method in BitVecNum
                    // however, we cannot cast to a type which doesn't match the generic, e.g. IntNum
                    int ui = ((BitVecNum) v).getInt();
                    if (ui < upper[i])
                    {
                        upper[i] = ui;
                    }
                    System.out.printf("%d %d %d%n", i, lower[i], upper[i]);
                }

                // find a new bound to add
                some_work = false;
                last_index = 0;
                for (int i = 0; i < num_Exprs; ++i)
                {
                    if (lower[i] < upper[i])
                    {
                        last_upper = (upper[i] + lower[i]) / 2;
                        last_index = i;
                        solver.add(ctx.mkBVULE(to_minimize[i],
                                ctx.mkBV(last_upper, 32)));
                        some_work = true;
                        break;
                    }
                }
            }
            solver.pop();
        }
    }

    // / Reduced-size model generation example.

    public void findSmallModelExample(Context ctx)
    {
        System.out.println("FindSmallModelExample");
        Log.append("FindSmallModelExample");

        BitVecExpr x = ctx.mkBVConst("x", 32);
        BitVecExpr y = ctx.mkBVConst("y", 32);
        BitVecExpr z = ctx.mkBVConst("z", 32);

        Solver solver = ctx.mkSolver();

        solver.add(ctx.mkBVULE(x, ctx.mkBVAdd(y, z)));
        checkSmall(ctx, solver, x, y, z);
    }

    // / Simplifier example.

    @SuppressWarnings("unchecked")
    public void simplifierExample(Context ctx)
    {
        System.out.println("SimplifierExample");
        Log.append("SimplifierExample");

        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr z = ctx.mkIntConst("z");
        @SuppressWarnings("unused")
        IntExpr u = ctx.mkIntConst("u");

        ArithExpr<IntSort> t1 = ctx.mkAdd(x, ctx.mkSub(y, ctx.mkAdd(x, z)));
        Expr<IntSort> t2 = t1.simplify();
        System.out.printf("%s -> %s%n", t1, t2);
    }

    // / Extract unsatisfiable core example

    public void unsatCoreAndProofExample(Context ctx)
    {
        System.out.println("UnsatCoreAndProofExample");
        Log.append("UnsatCoreAndProofExample");

        Solver solver = ctx.mkSolver();

        BoolExpr pa = ctx.mkBoolConst("PredA");
        BoolExpr pb = ctx.mkBoolConst("PredB");
        BoolExpr pc = ctx.mkBoolConst("PredC");
        BoolExpr pd = ctx.mkBoolConst("PredD");
        BoolExpr p1 = ctx.mkBoolConst("P1");
        BoolExpr p2 = ctx.mkBoolConst("P2");
        BoolExpr p3 = ctx.mkBoolConst("P3");
        BoolExpr p4 = ctx.mkBoolConst("P4");
        BoolExpr[] assumptions = new BoolExpr[] { ctx.mkNot(p1), ctx.mkNot(p2),
                ctx.mkNot(p3), ctx.mkNot(p4) };
        BoolExpr f1 = ctx.mkAnd(pa, pb, pc);
        BoolExpr f2 = ctx.mkAnd(pa, ctx.mkNot(pb), pc);
        BoolExpr f3 = ctx.mkOr(ctx.mkNot(pa), ctx.mkNot(pc));
        BoolExpr f4 = pd;

        solver.add(ctx.mkOr(f1, p1));
        solver.add(ctx.mkOr(f2, p2));
        solver.add(ctx.mkOr(f3, p3));
        solver.add(ctx.mkOr(f4, p4));
        Status result = solver.check(assumptions);

        if (result == Status.UNSATISFIABLE)
        {
            System.out.println("unsat");
            System.out.printf("proof: %s%n", solver.getProof());
            System.out.println("core: ");
            for (Expr<?> c : solver.getUnsatCore())
            {
                System.out.println(c);
            }
        }
    }

    /// Extract unsatisfiable core example with AssertAndTrack

    public void unsatCoreAndProofExample2(Context ctx)
    {
        System.out.println("UnsatCoreAndProofExample2");
        Log.append("UnsatCoreAndProofExample2");

        Solver solver = ctx.mkSolver();

        BoolExpr pa = ctx.mkBoolConst("PredA");
        BoolExpr pb = ctx.mkBoolConst("PredB");
        BoolExpr pc = ctx.mkBoolConst("PredC");
        BoolExpr pd = ctx.mkBoolConst("PredD");

        BoolExpr f1 = ctx.mkAnd(new BoolExpr[] { pa, pb, pc });
        BoolExpr f2 = ctx.mkAnd(new BoolExpr[] { pa, ctx.mkNot(pb), pc });
        BoolExpr f3 = ctx.mkOr(ctx.mkNot(pa), ctx.mkNot(pc));
        BoolExpr f4 = pd;

        BoolExpr p1 = ctx.mkBoolConst("P1");
        BoolExpr p2 = ctx.mkBoolConst("P2");
        BoolExpr p3 = ctx.mkBoolConst("P3");
        BoolExpr p4 = ctx.mkBoolConst("P4");

        solver.assertAndTrack(f1, p1);
        solver.assertAndTrack(f2, p2);
        solver.assertAndTrack(f3, p3);
        solver.assertAndTrack(f4, p4);
        Status result = solver.check();

        if (result == Status.UNSATISFIABLE)
        {
            System.out.println("unsat");
            System.out.println("core: ");
            for (Expr<?> c : solver.getUnsatCore())
            {
                System.out.println(c);
            }
        }
    }

    public <S, T> void finiteDomainExample(Context ctx)
    {
        System.out.println("FiniteDomainExample");
        Log.append("FiniteDomainExample");

        FiniteDomainSort<S> s = ctx.mkFiniteDomainSort("S", 10);
        FiniteDomainSort<T> t = ctx.mkFiniteDomainSort("T", 10);
        FiniteDomainNum<S> s1 = (FiniteDomainNum<S>) ctx.mkNumeral(1, s);
        FiniteDomainNum<T> t1 = (FiniteDomainNum<T>) ctx.mkNumeral(1, t);
        System.out.println(s);
        System.out.println(t);
        System.out.println(s1);
        System.out.println(t1);
        System.out.println(s1.getInt());
        System.out.println(t1.getInt());
        // But you cannot mix numerals of different sorts
        // even if the size of their domains are the same:
        // System.out.println(ctx.mkEq(s1, t1));
    }

    public void floatingPointExample1(Context ctx) throws TestFailedException
    {
        System.out.println("FloatingPointExample1");
        Log.append("FloatingPointExample1");

        FPSort s = ctx.mkFPSort(11, 53);
        System.out.printf("Sort: %s%n", s);

        FPNum x = (FPNum)ctx.mkNumeral("-1e1", s); /* -1 * 10^1 = -10 */
        FPNum y = (FPNum)ctx.mkNumeral("-10", s); /* -10 */
        FPNum z = (FPNum)ctx.mkNumeral("-1.25p3", s); /* -1.25 * 2^3 = -1.25 * 8 = -10 */
        System.out.printf("x=%s; y=%s; z=%s%n", x.toString(), y.toString(), z.toString());

        BoolExpr a = ctx.mkAnd(ctx.mkFPEq(x, y), ctx.mkFPEq(y, z));
        check(ctx, ctx.mkNot(a), Status.UNSATISFIABLE);

        /* nothing is equal to NaN according to floating-point
         * equality, so NaN == k should be unsatisfiable. */
        FPExpr k = (FPExpr)ctx.mkConst("x", s);
        FPExpr nan = ctx.mkFPNaN(s);

        /* solver that runs the default tactic for QF_FP. */
        Solver slvr = ctx.mkSolver("QF_FP");
        slvr.add(ctx.mkFPEq(nan, k));
        if (slvr.check() != Status.UNSATISFIABLE)
            throw new TestFailedException();
        System.out.printf("OK, unsat:%n%s%n", slvr);

        /* NaN is equal to NaN according to normal equality. */
        slvr = ctx.mkSolver("QF_FP");
        slvr.add(ctx.mkEq(nan, nan));
        if (slvr.check() != Status.SATISFIABLE)
            throw new TestFailedException();
        System.out.printf("OK, sat:%n%s%n", slvr);

        /* Let's prove -1e1 * -1.25e3 == +100 */
        x = (FPNum)ctx.mkNumeral("-1e1", s);
        y = (FPNum)ctx.mkNumeral("-1.25p3", s);
        FPExpr x_plus_y = (FPExpr)ctx.mkConst("x_plus_y", s);
        FPNum r = (FPNum)ctx.mkNumeral("100", s);
        slvr = ctx.mkSolver("QF_FP");

        slvr.add(ctx.mkEq(x_plus_y, ctx.mkFPMul(ctx.mkFPRoundNearestTiesToAway(), x, y)));
        slvr.add(ctx.mkNot(ctx.mkFPEq(x_plus_y, r)));
        if (slvr.check() != Status.UNSATISFIABLE)
            throw new TestFailedException();
        System.out.printf("OK, unsat:%n%s%n", slvr);
    }

    public void floatingPointExample2(Context ctx) throws TestFailedException
    {
        System.out.println("FloatingPointExample2");
        Log.append("FloatingPointExample2");
        FPSort double_sort = ctx.mkFPSort(11, 53);
        FPRMSort rm_sort = ctx.mkFPRoundingModeSort();

        FPRMExpr rm = (FPRMExpr)ctx.mkConst(ctx.mkSymbol("rm"), rm_sort);
        BitVecExpr x = (BitVecExpr)ctx.mkConst(ctx.mkSymbol("x"), ctx.mkBitVecSort(64));
        FPExpr y = (FPExpr)ctx.mkConst(ctx.mkSymbol("y"), double_sort);
        FPExpr fp_val = ctx.mkFP(42, double_sort);

        BoolExpr c1 = ctx.mkEq(y, fp_val);
        BoolExpr c2 = ctx.mkEq(x, ctx.mkFPToBV(rm, y, 64, false));
        BoolExpr c3 = ctx.mkEq(x, ctx.mkBV(42, 64));
        BoolExpr c4 = ctx.mkEq(ctx.mkNumeral(42, ctx.getRealSort()), ctx.mkFPToReal(fp_val));
        BoolExpr c5 = ctx.mkAnd(c1, c2, c3, c4);
        System.out.printf("c5 = %s%n", c5);

        /* Generic solver */
        Solver s = ctx.mkSolver();
        s.add(c5);

        if (s.check() != Status.SATISFIABLE)
            throw new TestFailedException();

        System.out.printf("OK, model: %s%n", s.getModel());
    }

    @SuppressWarnings("unchecked")
    public void optimizeExample(Context ctx)
    {
        System.out.println("Opt");

        Optimize opt = ctx.mkOptimize();

        // Set constraints.
        IntExpr xExp = ctx.mkIntConst("x");
        IntExpr yExp = ctx.mkIntConst("y");

        opt.Add(ctx.mkEq(ctx.mkAdd(xExp, yExp), ctx.mkInt(10)),
                ctx.mkGe(xExp, ctx.mkInt(0)),
                ctx.mkGe(yExp, ctx.mkInt(0)));

        // Set objectives.
        Optimize.Handle<IntSort> mx = opt.MkMaximize(xExp);
        Optimize.Handle<IntSort> my = opt.MkMaximize(yExp);

        System.out.println(opt.Check());
        System.out.println(mx);
        System.out.println(my);
    }

    public void translationExample() {
        Context ctx1 = new Context();
        Context ctx2 = new Context();

        Sort s1 = ctx1.getIntSort();
        Sort s2 = ctx2.getIntSort();
        Sort s3 = s1.translate(ctx2);

        System.out.println(s1 == s2);
        System.out.println(s1.equals(s2));
        System.out.println(s2.equals(s3));
        System.out.println(s1.equals(s3));

        IntExpr e1 = ctx1.mkIntConst("e1");
        IntExpr e2 = ctx2.mkIntConst("e1");
        Expr<IntSort> e3 = e1.translate(ctx2);

        System.out.println(e1 == e2);
        System.out.println(e1.equals(e2));
        System.out.println(e2.equals(e3));
        System.out.println(e1.equals(e3));
    }

    public static void main(String[] args)
    {
        JavaGenericExample p = new JavaGenericExample();
        try
        {
            Global.ToggleWarningMessages(true);
            Log.open("test.log");

            System.out.print("Z3 Major Version: ");
            System.out.println(Version.getMajor());
            System.out.print("Z3 Full Version: ");
            System.out.println(Version.getString());
            System.out.print("Z3 Full Version String: ");
            System.out.println(Version.getFullVersion());

            p.simpleExample();

            { // These examples need model generation turned on.
                HashMap<String, String> cfg = new HashMap<>();
                cfg.put("model", "true");
                Context ctx = new Context(cfg);

                p.optimizeExample(ctx);
                p.basicTests(ctx);
                p.sudokuExample(ctx);
                p.quantifierExample1(ctx);
                p.quantifierExample2(ctx);
                p.logicExample(ctx);
                p.parOrExample(ctx);
                p.findModelExample1(ctx);
                p.findModelExample2(ctx);
                p.pushPopExample1(ctx);
                p.arrayExample1(ctx);
                p.arrayExample3(ctx);
                p.bitvectorExample1(ctx);
                p.bitvectorExample2(ctx);
                p.parserExample1(ctx);
                p.parserExample2(ctx);
                p.parserExample5(ctx);
                p.iteExample(ctx);
                p.evalExample1(ctx);
                p.evalExample2(ctx);
                p.findSmallModelExample(ctx);
                p.simplifierExample(ctx);
                p.finiteDomainExample(ctx);
                p.floatingPointExample1(ctx);
                // core dumps: p.floatingPointExample2(ctx);
            }

            { // These examples need proof generation turned on.
                HashMap<String, String> cfg = new HashMap<>();
                cfg.put("proof", "true");
                Context ctx = new Context(cfg);
                p.proveExample1(ctx);
                p.proveExample2(ctx);
                p.arrayExample2(ctx);
                p.tupleExample(ctx);
                // throws p.parserExample3(ctx);
                p.enumExampleTyped(ctx);
                p.enumExampleUntyped(ctx);
                p.listExample(ctx);
                p.treeExample(ctx);
                p.forestExample(ctx);
                p.unsatCoreAndProofExample(ctx);
                p.unsatCoreAndProofExample2(ctx);
            }

            { // These examples need proof generation turned on and auto-config
              // set to false.
                HashMap<String, String> cfg = new HashMap<>();
                cfg.put("proof", "true");
                cfg.put("auto-config", "false");
                Context ctx = new Context(cfg);
                p.quantifierExample3(ctx);
                p.quantifierExample4(ctx);
            }

            p.translationExample();

            Log.close();
            if (Log.isOpen())
                System.out.println("Log is still open!");
        } catch (Z3Exception ex)
        {
            System.out.printf("Z3 Managed Exception: %s%n", ex.getMessage());
            System.out.println("Stack trace: ");
            ex.printStackTrace(System.out);
        } catch (TestFailedException ex)
        {
            System.out.printf("TEST CASE FAILED: %s%n", ex.getMessage());
            System.out.println("Stack trace: ");
            ex.printStackTrace(System.out);
        } catch (Exception ex)
        {
            System.out.printf("Unknown Exception: %s%n", ex.getMessage());
            System.out.println("Stack trace: ");
            ex.printStackTrace(System.out);
        }
    }
}
