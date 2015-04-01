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

import java.util.*;

import com.microsoft.z3.*;

class JavaExample
{
    @SuppressWarnings("serial")
    class TestFailedException extends Exception
    {
        public TestFailedException()
        {
            super("Check FAILED");
        }
    };

    // / Create axiom: function f is injective in the i-th argument.

    // / <remarks>
    // / The following axiom is produced:
    // / <code>
    // / forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
    // / </code>
    // / Where, <code>finv</code>is a fresh function declaration.

    public BoolExpr injAxiom(Context ctx, FuncDecl f, int i) throws Z3Exception
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
        FuncDecl finv = ctx.mkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        Expr[] xs = new Expr[sz];
        Symbol[] names = new Symbol[sz];
        Sort[] types = new Sort[sz];

        /* fill types, names and xs */

        for (int j = 0; j < sz; j++)
        {
            types[j] = domain[j];
            names[j] = ctx.mkSymbol("x_" + Integer.toString(j));
            xs[j] = ctx.mkBound(j, types[j]);
        }
        Expr x_i = xs[i];

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr fxs = f.apply(xs);

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr finv_fxs = finv.apply(fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Expr eq = ctx.mkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = ctx.mkPattern(fxs);

        /* create & assert quantifier */
        BoolExpr q = ctx.mkForall(types, /* types of quantified variables */
                names, /* names of quantified variables */
                eq, 1, new Pattern[] { p } /* patterns */, null, null, null);

        return q;
    }

    // / Create axiom: function f is injective in the i-th argument.

    // / <remarks>
    // / The following axiom is produced:
    // / <code>
    // / forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
    // / </code>
    // / Where, <code>finv</code>is a fresh function declaration.

    public BoolExpr injAxiomAbs(Context ctx, FuncDecl f, int i)
            throws Z3Exception
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
        FuncDecl finv = ctx.mkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        Expr[] xs = new Expr[sz];

        /* fill types, names and xs */
        for (int j = 0; j < sz; j++)
        {
            xs[j] = ctx.mkConst("x_" + Integer.toString(j), domain[j]);
        }
        Expr x_i = xs[i];

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr fxs = f.apply(xs);

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr finv_fxs = finv.apply(fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Expr eq = ctx.mkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = ctx.mkPattern(fxs);

        /* create & assert quantifier */
        BoolExpr q = ctx.mkForall(xs, /* types of quantified variables */
                eq, /* names of quantified variables */
                1, new Pattern[] { p } /* patterns */, null, null, null);

        return q;
    }

    // / Assert the axiom: function f is commutative.

    // / <remarks>
    // / This example uses the SMT-LIB parser to simplify the axiom
    // construction.
    // / </remarks>
    private BoolExpr commAxiom(Context ctx, FuncDecl f) throws Exception
    {
        Sort t = f.getRange();
        Sort[] dom = f.getDomain();

        if (dom.length != 2 || !t.equals(dom[0]) || !t.equals(dom[1]))
        {
            System.out.println(Integer.toString(dom.length) + " "
                    + dom[0].toString() + " " + dom[1].toString() + " "
                    + t.toString());
            throw new Exception(
                    "function must be binary, and argument types must be equal to return type");
        }

        String bench = "(benchmark comm :formula (forall (x " + t.getName()
                + ") (y " + t.getName() + ") (= (" + f.getName() + " x y) ("
                + f.getName() + " y x))))";
        ctx.parseSMTLIBString(bench, new Symbol[] { t.getName() },
                new Sort[] { t }, new Symbol[] { f.getName() },
                new FuncDecl[] { f });
        return ctx.getSMTLIBFormulas()[0];
    }

    // / "Hello world" example: create a Z3 logical context, and delete it.

    public void simpleExample() throws Z3Exception
    {
        System.out.println("SimpleExample");
        Log.append("SimpleExample");

        {
            Context ctx = new Context();
            /* do something with the context */

            /* be kind to dispose manually and not wait for the GC. */
            ctx.dispose();
        }
    }

    Model check(Context ctx, BoolExpr f, Status sat) throws Z3Exception,
            TestFailedException
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
            throws Z3Exception, TestFailedException
    {
        Solver s = ctx.mkSolver(t);
        System.out.println("\nTactical solver: " + s);

        for (BoolExpr a : g.getFormulas())
            s.add(a);
        System.out.println("Solver: " + s);

        if (s.check() != sat)
            throw new TestFailedException();
    }

    ApplyResult applyTactic(Context ctx, Tactic t, Goal g) throws Z3Exception
    {
        System.out.println("\nGoal: " + g);

        ApplyResult res = t.apply(g);
        System.out.println("Application result: " + res);

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

    void prove(Context ctx, BoolExpr f, boolean useMBQI) throws Z3Exception,
            TestFailedException
    {
        BoolExpr[] assumptions = new BoolExpr[0];
        prove(ctx, f, useMBQI, assumptions);
    }

    void prove(Context ctx, BoolExpr f, boolean useMBQI,
            BoolExpr... assumptions) throws Z3Exception, TestFailedException
    {
        System.out.println("Proving: " + f);
        Solver s = ctx.mkSolver();
        Params p = ctx.mkParams();
        p.add("mbqi", useMBQI);
        s.setParameters(p);
        for (BoolExpr a : assumptions)
            s.add(a);
        s.add(ctx.mkNot(f));
        Status q = s.check();

        switch (q)
        {
        case UNKNOWN:
            System.out.println("Unknown because: " + s.getReasonUnknown());
            break;
        case SATISFIABLE:
            throw new TestFailedException();
        case UNSATISFIABLE:
            System.out.println("OK, proof: " + s.getProof());
            break;
        }
    }

    void disprove(Context ctx, BoolExpr f, boolean useMBQI) throws Z3Exception,
            TestFailedException
    {
        BoolExpr[] a = {};
        disprove(ctx, f, useMBQI, a);
    }

    void disprove(Context ctx, BoolExpr f, boolean useMBQI,
            BoolExpr... assumptions) throws Z3Exception, TestFailedException
    {
        System.out.println("Disproving: " + f);
        Solver s = ctx.mkSolver();
        Params p = ctx.mkParams();
        p.add("mbqi", useMBQI);
        s.setParameters(p);
        for (BoolExpr a : assumptions)
            s.add(a);
        s.add(ctx.mkNot(f));
        Status q = s.check();

        switch (q)
        {
        case UNKNOWN:
            System.out.println("Unknown because: " + s.getReasonUnknown());
            break;
        case SATISFIABLE:
            System.out.println("OK, model: " + s.getModel());
            break;
        case UNSATISFIABLE:
            throw new TestFailedException();
        }
    }

    void modelConverterTest(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ModelConverterTest");

        ArithExpr xr = (ArithExpr) ctx.mkConst(ctx.mkSymbol("x"),
                ctx.mkRealSort());
        ArithExpr yr = (ArithExpr) ctx.mkConst(ctx.mkSymbol("y"),
                ctx.mkRealSort());
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
        System.out.println("Solver says: " + q);
        System.out.println("Model: \n" + s.getModel());
        System.out.println("Converted Model: \n"
                + ar.convertModel(0, s.getModel()));
        if (q != Status.SATISFIABLE)
            throw new TestFailedException();
    }

    // / A simple array example.

    void arrayExample1(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("ArrayExample1");
        Log.append("ArrayExample1");

        Goal g = ctx.mkGoal(true, false, false);
        ArraySort asort = ctx.mkArraySort(ctx.getIntSort(),
                ctx.mkBitVecSort(32));
        ArrayExpr aex = (ArrayExpr) ctx.mkConst(ctx.mkSymbol("MyArray"), asort);
        Expr sel = ctx.mkSelect(aex, ctx.mkInt(0));
        g.add(ctx.mkEq(sel, ctx.mkBV(42, 32)));
        Symbol xs = ctx.mkSymbol("x");
        IntExpr xc = (IntExpr) ctx.mkConst(xs, ctx.getIntSort());

        Symbol fname = ctx.mkSymbol("f");
        Sort[] domain = { ctx.getIntSort() };
        FuncDecl fd = ctx.mkFuncDecl(fname, domain, ctx.getIntSort());
        Expr[] fargs = { ctx.mkConst(xs, ctx.getIntSort()) };
        IntExpr fapp = (IntExpr) ctx.mkApp(fd, fargs);

        g.add(ctx.mkEq(ctx.mkAdd(xc, fapp), ctx.mkInt(123)));

        Solver s = ctx.mkSolver();
        for (BoolExpr a : g.getFormulas())
            s.add(a);
        System.out.println("Solver: " + s);

        Status q = s.check();
        System.out.println("Status: " + q);

        if (q != Status.SATISFIABLE)
            throw new TestFailedException();

        System.out.println("Model = " + s.getModel());

        System.out.println("Interpretation of MyArray:\n"
                + s.getModel().getFuncInterp(aex.getFuncDecl()));
        System.out.println("Interpretation of x:\n"
                + s.getModel().getConstInterp(xc));
        System.out.println("Interpretation of f:\n"
                + s.getModel().getFuncInterp(fd));
        System.out.println("Interpretation of MyArray as Term:\n"
                + s.getModel().getFuncInterp(aex.getFuncDecl()));
    }

    // / Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2
    // = i3 or select(a1, i3) = select(a2, i3))</tt>.

    // / <remarks>This example demonstrates how to use the array
    // theory.</remarks>
    public void arrayExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ArrayExample2");
        Log.append("ArrayExample2");

        Sort int_type = ctx.getIntSort();
        Sort array_type = ctx.mkArraySort(int_type, int_type);

        ArrayExpr a1 = (ArrayExpr) ctx.mkConst("a1", array_type);
        ArrayExpr a2 = ctx.mkArrayConst("a2", int_type, int_type);
        Expr i1 = ctx.mkConst("i1", int_type);
        Expr i2 = ctx.mkConst("i2", int_type);
        Expr i3 = ctx.mkConst("i3", int_type);
        Expr v1 = ctx.mkConst("v1", int_type);
        Expr v2 = ctx.mkConst("v2", int_type);

        Expr st1 = ctx.mkStore(a1, i1, v1);
        Expr st2 = ctx.mkStore(a2, i2, v2);

        Expr sel1 = ctx.mkSelect(a1, i3);
        Expr sel2 = ctx.mkSelect(a2, i3);

        /* create antecedent */
        BoolExpr antecedent = ctx.mkEq(st1, st2);

        /*
         * create consequent: i1 = i3 or i2 = i3 or select(a1, i3) = select(a2,
         * i3)
         */
        BoolExpr consequent = ctx.mkOr(ctx.mkEq(i1, i3), ctx.mkEq(i2, i3),
                ctx.mkEq(sel1, sel2));

        /*
         * prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 =
         * i3 or select(a1, i3) = select(a2, i3))
         */
        BoolExpr thm = ctx.mkImplies(antecedent, consequent);
        System.out
                .println("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))");
        System.out.println(thm);
        prove(ctx, thm, false);
    }

    // / Show that <code>distinct(a_0, ... , a_n)</code> is
    // / unsatisfiable when <code>a_i</code>'s are arrays from boolean to
    // / boolean and n > 4.

    // / <remarks>This example also shows how to use the <code>distinct</code>
    // construct.</remarks>
    public void arrayExample3(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ArrayExample3");
        Log.append("ArrayExample2");

        for (int n = 2; n <= 5; n++)
        {
            System.out.println("n = " + Integer.toString(n));

            Sort bool_type = ctx.mkBoolSort();
            Sort array_type = ctx.mkArraySort(bool_type, bool_type);
            Expr[] a = new Expr[n];

            /* create arrays */
            for (int i = 0; i < n; i++)
            {
                a[i] = ctx.mkConst("array_" + Integer.toString(i), array_type);
            }

            /* assert distinct(a[0], ..., a[n]) */
            BoolExpr d = ctx.mkDistinct(a);
            System.out.println(d);

            /* context is satisfiable if n < 5 */
            Model model = check(ctx, d, n < 5 ? Status.SATISFIABLE
                    : Status.UNSATISFIABLE);
            if (n < 5)
            {
                for (int i = 0; i < n; i++)
                {
                    System.out.println(a[i].toString() + " = "
                            + model.evaluate(a[i], false));
                }
            }
        }
    }

    // / Sudoku solving example.

    void sudokuExample(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("SudokuExample");
        Log.append("SudokuExample");

        // 9x9 matrix of integer variables
        IntExpr[][] X = new IntExpr[9][];
        for (int i = 0; i < 9; i++)
        {
            X[i] = new IntExpr[9];
            for (int j = 0; j < 9; j++)
                X[i][j] = (IntExpr) ctx.mkConst(
                        ctx.mkSymbol("x_" + (i + 1) + "_" + (j + 1)),
                        ctx.getIntSort());
        }

        // each cell contains a value in {1, ..., 9}
        BoolExpr[][] cells_c = new BoolExpr[9][];
        for (int i = 0; i < 9; i++)
        {
            cells_c[i] = new BoolExpr[9];
            for (int j = 0; j < 9; j++)
                cells_c[i][j] = ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), X[i][j]),
                        ctx.mkLe(X[i][j], ctx.mkInt(9)));
        }

        // each row contains a digit at most once
        BoolExpr[] rows_c = new BoolExpr[9];
        for (int i = 0; i < 9; i++)
            rows_c[i] = ctx.mkDistinct(X[i]);

        // each column contains a digit at most once
        BoolExpr[] cols_c = new BoolExpr[9];
        for (int j = 0; j < 9; j++)
            cols_c[j] = ctx.mkDistinct(X[j]);

        // each 3x3 square contains a digit at most once
        BoolExpr[][] sq_c = new BoolExpr[3][];
        for (int i0 = 0; i0 < 3; i0++)
        {
            sq_c[i0] = new BoolExpr[3];
            for (int j0 = 0; j0 < 3; j0++)
            {
                IntExpr[] square = new IntExpr[9];
                for (int i = 0; i < 3; i++)
                    for (int j = 0; j < 3; j++)
                        square[3 * i + j] = X[3 * i0 + i][3 * j0 + j];
                sq_c[i0][j0] = ctx.mkDistinct(square);
            }
        }

        BoolExpr sudoku_c = ctx.mkTrue();
        for (BoolExpr[] t : cells_c)
            sudoku_c = ctx.mkAnd(ctx.mkAnd(t), sudoku_c);
        sudoku_c = ctx.mkAnd(ctx.mkAnd(rows_c), sudoku_c);
        sudoku_c = ctx.mkAnd(ctx.mkAnd(cols_c), sudoku_c);
        for (BoolExpr[] t : sq_c)
            sudoku_c = ctx.mkAnd(ctx.mkAnd(t), sudoku_c);

        // sudoku instance, we use '0' for empty cells
        int[][] instance = { { 0, 0, 0, 0, 9, 4, 0, 3, 0 },
                { 0, 0, 0, 5, 1, 0, 0, 0, 7 }, { 0, 8, 9, 0, 0, 0, 0, 4, 0 },
                { 0, 0, 0, 0, 0, 0, 2, 0, 8 }, { 0, 6, 0, 2, 0, 1, 0, 5, 0 },
                { 1, 0, 2, 0, 0, 0, 0, 0, 0 }, { 0, 7, 0, 0, 0, 0, 5, 2, 0 },
                { 9, 0, 0, 0, 6, 5, 0, 0, 0 }, { 0, 4, 0, 9, 7, 0, 0, 0, 0 } };

        BoolExpr instance_c = ctx.mkTrue();
        for (int i = 0; i < 9; i++)
            for (int j = 0; j < 9; j++)
                instance_c = ctx.mkAnd(
                        instance_c,
                        (BoolExpr) ctx.mkITE(
                                ctx.mkEq(ctx.mkInt(instance[i][j]),
                                        ctx.mkInt(0)), ctx.mkTrue(),
                                ctx.mkEq(X[i][j], ctx.mkInt(instance[i][j]))));

        Solver s = ctx.mkSolver();
        s.add(sudoku_c);
        s.add(instance_c);

        if (s.check() == Status.SATISFIABLE)
        {
            Model m = s.getModel();
            Expr[][] R = new Expr[9][9];
            for (int i = 0; i < 9; i++)
                for (int j = 0; j < 9; j++)
                    R[i][j] = m.evaluate(X[i][j], false);
            System.out.println("Sudoku solution:");
            for (int i = 0; i < 9; i++)
            {
                for (int j = 0; j < 9; j++)
                    System.out.print(" " + R[i][j]);
                System.out.println();
            }
        } else
        {
            System.out.println("Failed to solve sudoku");
            throw new TestFailedException();
        }
    }

    // / A basic example of how to use quantifiers.

    void quantifierExample1(Context ctx) throws Z3Exception
    {
        System.out.println("QuantifierExample");
        Log.append("QuantifierExample");

        Sort[] types = new Sort[3];
        IntExpr[] xs = new IntExpr[3];
        Symbol[] names = new Symbol[3];
        IntExpr[] vars = new IntExpr[3];

        for (int j = 0; j < 3; j++)
        {
            types[j] = ctx.getIntSort();
            names[j] = ctx.mkSymbol("x_" + Integer.toString(j));
            xs[j] = (IntExpr) ctx.mkConst(names[j], types[j]);
            vars[j] = (IntExpr) ctx.mkBound(2 - j, types[j]); // <-- vars
                                                              // reversed!
        }

        Expr body_vars = ctx.mkAnd(
                ctx.mkEq(ctx.mkAdd(vars[0], ctx.mkInt(1)), ctx.mkInt(2)),
                ctx.mkEq(ctx.mkAdd(vars[1], ctx.mkInt(2)),
                        ctx.mkAdd(vars[2], ctx.mkInt(3))));

        Expr body_const = ctx.mkAnd(
                ctx.mkEq(ctx.mkAdd(xs[0], ctx.mkInt(1)), ctx.mkInt(2)),
                ctx.mkEq(ctx.mkAdd(xs[1], ctx.mkInt(2)),
                        ctx.mkAdd(xs[2], ctx.mkInt(3))));

        Expr x = ctx.mkForall(types, names, body_vars, 1, null, null,
                ctx.mkSymbol("Q1"), ctx.mkSymbol("skid1"));
        System.out.println("Quantifier X: " + x.toString());

        Expr y = ctx.mkForall(xs, body_const, 1, null, null,
                ctx.mkSymbol("Q2"), ctx.mkSymbol("skid2"));
        System.out.println("Quantifier Y: " + y.toString());
    }

    void quantifierExample2(Context ctx) throws Z3Exception
    {

        System.out.println("QuantifierExample2");
        Log.append("QuantifierExample2");

        Expr q1, q2;
        FuncDecl f = ctx.mkFuncDecl("f", ctx.getIntSort(), ctx.getIntSort());
        FuncDecl g = ctx.mkFuncDecl("g", ctx.getIntSort(), ctx.getIntSort());

        // Quantifier with Exprs as the bound variables.
        {
            Expr x = ctx.mkConst("x", ctx.getIntSort());
            Expr y = ctx.mkConst("y", ctx.getIntSort());
            Expr f_x = ctx.mkApp(f, x);
            Expr f_y = ctx.mkApp(f, y);
            Expr g_y = ctx.mkApp(g, y);
            @SuppressWarnings("unused")
            Pattern[] pats = new Pattern[] { ctx.mkPattern(f_x, g_y) };
            Expr[] no_pats = new Expr[] { f_y };
            Expr[] bound = new Expr[] { x, y };
            Expr body = ctx.mkAnd(ctx.mkEq(f_x, f_y), ctx.mkEq(f_y, g_y));

            q1 = ctx.mkForall(bound, body, 1, null, no_pats, ctx.mkSymbol("q"),
                    ctx.mkSymbol("sk"));

            System.out.println(q1);
        }

        // Quantifier with de-Brujin indices.
        {
            Expr x = ctx.mkBound(1, ctx.getIntSort());
            Expr y = ctx.mkBound(0, ctx.getIntSort());
            Expr f_x = ctx.mkApp(f, x);
            Expr f_y = ctx.mkApp(f, y);
            Expr g_y = ctx.mkApp(g, y);
            @SuppressWarnings("unused")
            Pattern[] pats = new Pattern[] { ctx.mkPattern(f_x, g_y) };
            Expr[] no_pats = new Expr[] { f_y };
            Symbol[] names = new Symbol[] { ctx.mkSymbol("x"),
                    ctx.mkSymbol("y") };
            Sort[] sorts = new Sort[] { ctx.getIntSort(), ctx.getIntSort() };
            Expr body = ctx.mkAnd(ctx.mkEq(f_x, f_y), ctx.mkEq(f_y, g_y));

            q2 = ctx.mkForall(sorts, names, body, 1, null, // pats,
                    no_pats, ctx.mkSymbol("q"), ctx.mkSymbol("sk"));
            System.out.println(q2);
        }

        System.out.println(q1.equals(q2));
    }

    // / Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
    // / <code>f</code> is injective in the second argument. <seealso
    // cref="inj_axiom"/>

    public void quantifierExample3(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("QuantifierExample3");
        Log.append("QuantifierExample3");

        /*
         * If quantified formulas are asserted in a logical context, then the
         * model produced by Z3 should be viewed as a potential model.
         */

        /* declare function f */
        Sort I = ctx.getIntSort();
        FuncDecl f = ctx.mkFuncDecl("f", new Sort[] { I, I }, I);

        /* f is injective in the second argument. */
        BoolExpr inj = injAxiom(ctx, f, 1);

        /* create x, y, v, w, fxy, fwv */
        Expr x = ctx.mkIntConst("x");
        Expr y = ctx.mkIntConst("y");
        Expr v = ctx.mkIntConst("v");
        Expr w = ctx.mkIntConst("w");
        Expr fxy = ctx.mkApp(f, x, y);
        Expr fwv = ctx.mkApp(f, w, v);

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

    public void quantifierExample4(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("QuantifierExample4");
        Log.append("QuantifierExample4");

        /*
         * If quantified formulas are asserted in a logical context, then the
         * model produced by Z3 should be viewed as a potential model.
         */

        /* declare function f */
        Sort I = ctx.getIntSort();
        FuncDecl f = ctx.mkFuncDecl("f", new Sort[] { I, I }, I);

        /* f is injective in the second argument. */
        BoolExpr inj = injAxiomAbs(ctx, f, 1);

        /* create x, y, v, w, fxy, fwv */
        Expr x = ctx.mkIntConst("x");
        Expr y = ctx.mkIntConst("y");
        Expr v = ctx.mkIntConst("v");
        Expr w = ctx.mkIntConst("w");
        Expr fxy = ctx.mkApp(f, x, y);
        Expr fwv = ctx.mkApp(f, w, v);

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

    void basicTests(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("BasicTests");

        Symbol fname = ctx.mkSymbol("f");
        Symbol x = ctx.mkSymbol("x");
        Symbol y = ctx.mkSymbol("y");

        Sort bs = ctx.mkBoolSort();

        Sort[] domain = { bs, bs };
        FuncDecl f = ctx.mkFuncDecl(fname, domain, bs);
        Expr fapp = ctx.mkApp(f, ctx.mkConst(x, bs), ctx.mkConst(y, bs));

        Expr[] fargs2 = { ctx.mkFreshConst("cp", bs) };
        Sort[] domain2 = { bs };
        Expr fapp2 = ctx.mkApp(ctx.mkFreshFuncDecl("fp", domain2, bs), fargs2);

        BoolExpr trivial_eq = ctx.mkEq(fapp, fapp);
        BoolExpr nontrivial_eq = ctx.mkEq(fapp, fapp2);

        Goal g = ctx.mkGoal(true, false, false);
        g.add(trivial_eq);
        g.add(nontrivial_eq);
        System.out.println("Goal: " + g);

        Solver solver = ctx.mkSolver();

        for (BoolExpr a : g.getFormulas())
            solver.add(a);

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
        Expr xc = ctx.mkConst(ctx.mkSymbol("x"), ctx.getIntSort());
        Expr yc = ctx.mkConst(ctx.mkSymbol("y"), ctx.getIntSort());
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
        Expr inum = rn.getNumerator();
        Expr iden = rn.getDenominator();
        System.out.println("Numerator: " + inum + " Denominator: " + iden);
        if (!inum.toString().equals("42") || !iden.toString().equals("43"))
            throw new TestFailedException();

        if (!rn.toDecimalString(3).toString().equals("0.976?"))
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
        } catch (Z3Exception e)
        {
        }
    }

    // / Some basic expression casting tests.

    void castingTest(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("CastingTest");

        Sort[] domain = { ctx.getBoolSort(), ctx.getBoolSort() };
        FuncDecl f = ctx.mkFuncDecl("f", domain, ctx.getBoolSort());

        AST upcast = ctx.mkFuncDecl(ctx.mkSymbol("q"), domain,
                ctx.getBoolSort());

        try
        {
            @SuppressWarnings("unused")
            FuncDecl downcast = (FuncDecl) f; // OK
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        try
        {
            @SuppressWarnings("unused")
            Expr uc = (Expr) upcast;
            throw new TestFailedException(); // should not be reachable!
        } catch (ClassCastException e)
        {
        }

        Symbol s = ctx.mkSymbol(42);
        IntSymbol si = (s.getClass() == IntSymbol.class) ? (IntSymbol) s : null;
        if (si == null)
            throw new TestFailedException();
        try
        {
            @SuppressWarnings("unused")
            IntSymbol si2 = (IntSymbol) s;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        s = ctx.mkSymbol("abc");
        StringSymbol ss = (s.getClass() == StringSymbol.class) ? (StringSymbol) s
                : null;
        if (ss == null)
            throw new TestFailedException();
        try
        {
            @SuppressWarnings("unused")
            StringSymbol ss2 = (StringSymbol) s;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }
        try
        {
            @SuppressWarnings("unused")
            IntSymbol si2 = (IntSymbol) s;
            throw new TestFailedException(); // unreachable
        } catch (Exception e)
        {
        }

        Sort srt = ctx.mkBitVecSort(32);
        BitVecSort bvs = null;
        try
        {
            bvs = (BitVecSort) srt;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        if (bvs.getSize() != 32)
            throw new TestFailedException();

        Expr q = ctx.mkAdd(ctx.mkInt(1), ctx.mkInt(2));
        Expr q2 = q.getArgs()[1];
        Sort qs = q2.getSort();
        if (qs.getClass() != IntSort.class)
            throw new TestFailedException();
        try
        {
            @SuppressWarnings("unused")
            IntSort isrt = (IntSort) qs;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        AST a = ctx.mkInt(42);

        try
        {
            Expr.class.cast(a);
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        try
        {
            ArithExpr.class.cast(a);
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        try
        {
            IntExpr.class.cast(a);
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        try
        {
            IntNum.class.cast(a);
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        Expr[][] earr = new Expr[2][];
        earr[0] = new Expr[2];
        earr[1] = new Expr[2];
        earr[0][0] = ctx.mkTrue();
        earr[0][1] = ctx.mkTrue();
        earr[1][0] = ctx.mkFalse();
        earr[1][1] = ctx.mkFalse();
        for (Expr[] ea : earr)
            for (Expr e : ea)
            {
                try
                {
                    Expr ns = ctx.mkNot((BoolExpr) e);
                    @SuppressWarnings("unused")
                    BoolExpr ens = (BoolExpr) ns;
                } catch (ClassCastException ex)
                {
                    throw new TestFailedException();
                }
            }
    }

    // / Shows how to read an SMT1 file.

    void smt1FileTest(String filename) throws Z3Exception
    {
        System.out.print("SMT File test ");

        {
            HashMap<String, String> cfg = new HashMap<String, String>();
            Context ctx = new Context(cfg);
            ctx.parseSMTLIBFile(filename, null, null, null, null);

            BoolExpr a = ctx.mkAnd(ctx.getSMTLIBFormulas());
            System.out.println("read formula: " + a);
        }
    }

    // / Shows how to read an SMT2 file.

    void smt2FileTest(String filename) throws Z3Exception
    {
        Date before = new Date();

        System.out.println("SMT2 File test ");
        System.gc();

        {
            HashMap<String, String> cfg = new HashMap<String, String>();
            cfg.put("model", "true");
            Context ctx = new Context(cfg);
            Expr a = ctx.parseSMTLIB2File(filename, null, null, null, null);

            long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;

            System.out.println("SMT2 file read time: " + t_diff + " sec");

            // Iterate over the formula.

            LinkedList<Expr> q = new LinkedList<Expr>();
            q.add(a);
            int cnt = 0;
            while (q.size() > 0)
            {
                AST cur = (AST) q.removeFirst();
                cnt++;

                if (cur.getClass() == Expr.class)
                    if (!(cur.isVar()))
                        for (Expr c : ((Expr) cur).getArgs())
                            q.add(c);
            }
            System.out.println(cnt + " ASTs");
        }

        long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;
        System.out.println("SMT2 file test took " + t_diff + " sec");
    }

    // / Shows how to use Solver(logic)

    // / @param ctx 
    void logicExample(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("LogicTest");
        Log.append("LogicTest");

        com.microsoft.z3.Global.ToggleWarningMessages(true);

        BitVecSort bvs = ctx.mkBitVecSort(32);
        Expr x = ctx.mkConst("x", bvs);
        Expr y = ctx.mkConst("y", bvs);
        BoolExpr eq = ctx.mkEq(x, y);

        // Use a solver for QF_BV
        Solver s = ctx.mkSolver("QF_BV");
        s.add(eq);
        Status res = s.check();
        System.out.println("solver result: " + res);

        // Or perhaps a tactic for QF_BV
        Goal g = ctx.mkGoal(true, false, false);
        g.add(eq);

        Tactic t = ctx.mkTactic("qfbv");
        ApplyResult ar = t.apply(g);
        System.out.println("tactic result: " + ar);

        if (ar.getNumSubgoals() != 1 || !ar.getSubgoals()[0].isDecidedSat())
            throw new TestFailedException();
    }

    // / Demonstrates how to use the ParOr tactic.

    void parOrExample(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("ParOrExample");
        Log.append("ParOrExample");

        BitVecSort bvs = ctx.mkBitVecSort(32);
        Expr x = ctx.mkConst("x", bvs);
        Expr y = ctx.mkConst("y", bvs);
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

    void bigIntCheck(Context ctx, RatNum r) throws Z3Exception
    {
        System.out.println("Num: " + r.getBigIntNumerator());
        System.out.println("Den: " + r.getBigIntDenominator());
    }

    // / Find a model for <code>x xor y</code>.

    public void findModelExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("FindModelExample1");
        Log.append("FindModelExample1");

        BoolExpr x = ctx.mkBoolConst("x");
        BoolExpr y = ctx.mkBoolConst("y");
        BoolExpr x_xor_y = ctx.mkXor(x, y);

        Model model = check(ctx, x_xor_y, Status.SATISFIABLE);
        System.out.println("x = " + model.evaluate(x, false) + ", y = "
                + model.evaluate(y, false));
    }

    // / Find a model for <tt>x < y + 1, x > 2</tt>.
    // / Then, assert <tt>not(x = y)</tt>, and find another model.

    public void findModelExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("FindModelExample2");
        Log.append("FindModelExample2");

        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr one = ctx.mkInt(1);
        IntExpr two = ctx.mkInt(2);

        ArithExpr y_plus_one = ctx.mkAdd(y, one);

        BoolExpr c1 = ctx.mkLt(x, y_plus_one);
        BoolExpr c2 = ctx.mkGt(x, two);

        BoolExpr q = ctx.mkAnd(c1, c2);

        System.out.println("model for: x < y + 1, x > 2");
        Model model = check(ctx, q, Status.SATISFIABLE);
        System.out.println("x = " + model.evaluate(x, false) + ", y ="
                + model.evaluate(y, false));

        /* assert not(x = y) */
        BoolExpr x_eq_y = ctx.mkEq(x, y);
        BoolExpr c3 = ctx.mkNot(x_eq_y);

        q = ctx.mkAnd(q, c3);

        System.out.println("model for: x < y + 1, x > 2, not(x = y)");
        model = check(ctx, q, Status.SATISFIABLE);
        System.out.println("x = " + model.evaluate(x, false) + ", y = "
                + model.evaluate(y, false));
    }

    // / Prove <tt>x = y implies g(x) = g(y)</tt>, and
    // / disprove <tt>x = y implies g(g(x)) = g(y)</tt>.

    // / <remarks>This function demonstrates how to create uninterpreted
    // / types and functions.</remarks>
    public void proveExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ProveExample1");
        Log.append("ProveExample1");

        /* create uninterpreted type. */
        Sort U = ctx.mkUninterpretedSort(ctx.mkSymbol("U"));

        /* declare function g */
        FuncDecl g = ctx.mkFuncDecl("g", U, U);

        /* create x and y */
        Expr x = ctx.mkConst("x", U);
        Expr y = ctx.mkConst("y", U);
        /* create g(x), g(y) */
        Expr gx = g.apply(x);
        Expr gy = g.apply(y);

        /* assert x = y */
        BoolExpr eq = ctx.mkEq(x, y);

        /* prove g(x) = g(y) */
        BoolExpr f = ctx.mkEq(gx, gy);
        System.out.println("prove: x = y implies g(x) = g(y)");
        prove(ctx, ctx.mkImplies(eq, f), false);

        /* create g(g(x)) */
        Expr ggx = g.apply(gx);

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
    public void proveExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ProveExample2");
        Log.append("ProveExample2");

        /* declare function g */
        Sort I = ctx.getIntSort();

        FuncDecl g = ctx.mkFuncDecl("g", I, I);

        /* create x, y, and z */
        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr z = ctx.mkIntConst("z");

        /* create gx, gy, gz */
        Expr gx = ctx.mkApp(g, x);
        Expr gy = ctx.mkApp(g, y);
        Expr gz = ctx.mkApp(g, z);

        /* create zero */
        IntExpr zero = ctx.mkInt(0);

        /* assert not(g(g(x) - g(y)) = g(z)) */
        ArithExpr gx_gy = ctx.mkSub((IntExpr) gx, (IntExpr) gy);
        Expr ggx_gy = ctx.mkApp(g, gx_gy);
        BoolExpr eq = ctx.mkEq(ggx_gy, gz);
        BoolExpr c1 = ctx.mkNot(eq);

        /* assert x + z <= y */
        ArithExpr x_plus_z = ctx.mkAdd(x, z);
        BoolExpr c2 = ctx.mkLe(x_plus_z, y);

        /* assert y <= x */
        BoolExpr c3 = ctx.mkLe(y, x);

        /* prove z < 0 */
        BoolExpr f = ctx.mkLt(z, zero);
        System.out
                .println("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0");
        prove(ctx, f, false, c1, c2, c3);

        /* disprove z < -1 */
        IntExpr minus_one = ctx.mkInt(-1);
        f = ctx.mkLt(z, minus_one);
        System.out
                .println("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1");
        disprove(ctx, f, false, c1, c2, c3);
    }

    // / Show how push & pop can be used to create "backtracking" points.

    // / <remarks>This example also demonstrates how big numbers can be
    // / created in ctx.</remarks>
    public void pushPopExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("PushPopExample1");
        Log.append("PushPopExample1");

        /* create a big number */
        IntSort int_type = ctx.getIntSort();
        IntExpr big_number = ctx
                .mkInt("1000000000000000000000000000000000000000000000000000000");

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
    public void tupleExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("TupleExample");
        Log.append("TupleExample");

        Sort int_type = ctx.getIntSort();
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
        FuncDecl first = tuple.getFieldDecls()[0]; // declarations are for
                                                   // projections
        @SuppressWarnings("unused")
        FuncDecl second = tuple.getFieldDecls()[1];
        Expr x = ctx.mkConst("x", int_type);
        Expr y = ctx.mkConst("y", int_type);
        Expr n1 = tuple.mkDecl().apply(x, y);
        Expr n2 = first.apply(n1);
        BoolExpr n3 = ctx.mkEq(x, n2);
        System.out.println("Tuple example: " + n3);
        prove(ctx, n3, false);
    }

    // / Simple bit-vector example.

    // / <remarks>
    // / This example disproves that x - 10 &lt;= 0 IFF x &lt;= 10 for (32-bit)
    // machine integers
    // / </remarks>
    public void bitvectorExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("BitvectorExample1");
        Log.append("BitvectorExample1");

        Sort bv_type = ctx.mkBitVecSort(32);
        BitVecExpr x = (BitVecExpr) ctx.mkConst("x", bv_type);
        BitVecNum zero = (BitVecNum) ctx.mkNumeral("0", bv_type);
        BitVecNum ten = ctx.mkBV(10, 32);
        BitVecExpr x_minus_ten = ctx.mkBVSub(x, ten);
        /* bvsle is signed less than or equal to */
        BoolExpr c1 = ctx.mkBVSLE(x, ten);
        BoolExpr c2 = ctx.mkBVSLE(x_minus_ten, zero);
        BoolExpr thm = ctx.mkIff(c1, c2);
        System.out
                .println("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers");
        disprove(ctx, thm, false);
    }

    // / Find x and y such that: x ^ y - 103 == x * y

    public void bitvectorExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("BitvectorExample2");
        Log.append("BitvectorExample2");

        /* construct x ^ y - 103 == x * y */
        Sort bv_type = ctx.mkBitVecSort(32);
        BitVecExpr x = ctx.mkBVConst("x", 32);
        BitVecExpr y = ctx.mkBVConst("y", 32);
        BitVecExpr x_xor_y = ctx.mkBVXOR(x, y);
        BitVecExpr c103 = (BitVecNum) ctx.mkNumeral("103", bv_type);
        BitVecExpr lhs = ctx.mkBVSub(x_xor_y, c103);
        BitVecExpr rhs = ctx.mkBVMul(x, y);
        BoolExpr ctr = ctx.mkEq(lhs, rhs);

        System.out
                .println("find values of x and y, such that x ^ y - 103 == x * y");

        /* find a model (i.e., values for x an y that satisfy the constraint */
        Model m = check(ctx, ctr, Status.SATISFIABLE);
        System.out.println(m);
    }

    // / Demonstrates how to use the SMTLIB parser.

    public void parserExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ParserExample1");
        Log.append("ParserExample1");

        ctx.parseSMTLIBString(
                "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))",
                null, null, null, null);
        for (BoolExpr f : ctx.getSMTLIBFormulas())
            System.out.println("formula " + f);

        @SuppressWarnings("unused")
        Model m = check(ctx, ctx.mkAnd(ctx.getSMTLIBFormulas()),
                Status.SATISFIABLE);
    }

    // / Demonstrates how to initialize the parser symbol table.

    public void parserExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ParserExample2");
        Log.append("ParserExample2");

        Symbol[] declNames = { ctx.mkSymbol("a"), ctx.mkSymbol("b") };
        FuncDecl a = ctx.mkConstDecl(declNames[0], ctx.mkIntSort());
        FuncDecl b = ctx.mkConstDecl(declNames[1], ctx.mkIntSort());
        FuncDecl[] decls = new FuncDecl[] { a, b };

        ctx.parseSMTLIBString("(benchmark tst :formula (> a b))", null, null,
                declNames, decls);
        BoolExpr f = ctx.getSMTLIBFormulas()[0];
        System.out.println("formula: " + f);
        check(ctx, f, Status.SATISFIABLE);
    }

    // / Demonstrates how to initialize the parser symbol table.

    public void parserExample3(Context ctx) throws Exception
    {
        System.out.println("ParserExample3");
        Log.append("ParserExample3");

        /* declare function g */
        Sort I = ctx.mkIntSort();
        FuncDecl g = ctx.mkFuncDecl("g", new Sort[] { I, I }, I);

        BoolExpr ca = commAxiom(ctx, g);

        ctx.parseSMTLIBString(
                "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (gg x 0) (gg 0 y)))))",
                null, null, new Symbol[] { ctx.mkSymbol("gg") },
                new FuncDecl[] { g });

        BoolExpr thm = ctx.getSMTLIBFormulas()[0];
        System.out.println("formula: " + thm);
        prove(ctx, thm, false, ca);
    }

    // / Display the declarations, assumptions and formulas in a SMT-LIB string.

    public void parserExample4(Context ctx) throws Z3Exception
    {
        System.out.println("ParserExample4");
        Log.append("ParserExample4");

        ctx.parseSMTLIBString(
                "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))",
                null, null, null, null);
        for (FuncDecl decl : ctx.getSMTLIBDecls())
        {
            System.out.println("Declaration: " + decl);
        }
        for (BoolExpr f : ctx.getSMTLIBAssumptions())
        {
            System.out.println("Assumption: " + f);
        }
        for (BoolExpr f : ctx.getSMTLIBFormulas())
        {
            System.out.println("Formula: " + f);
        }
    }

    // / Demonstrates how to handle parser errors using Z3 error handling
    // support.

    // / <remarks></remarks>
    public void parserExample5(Context ctx)
    {
        System.out.println("ParserExample5");

        try
        {
            ctx.parseSMTLIBString(
                    /*
                     * the following string has a parsing error: missing
                     * parenthesis
                     */
                    "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))",
                    null, null, null, null);
        } catch (Z3Exception e)
        {
            System.out.println("Z3 error: " + e);
        }
    }

    // / Create an ite-Expr (if-then-else Exprs).

    public void iteExample(Context ctx) throws Z3Exception
    {
        System.out.println("ITEExample");
        Log.append("ITEExample");

        BoolExpr f = ctx.mkFalse();
        Expr one = ctx.mkInt(1);
        Expr zero = ctx.mkInt(0);
        Expr ite = ctx.mkITE(f, one, zero);

        System.out.println("Expr: " + ite);
    }

    // / Create an enumeration data type.

    public void enumExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("EnumExample");
        Log.append("EnumExample");

        Symbol name = ctx.mkSymbol("fruit");

        EnumSort fruit = ctx.mkEnumSort(name, ctx.mkSymbol("apple"),
                ctx.mkSymbol("banana"), ctx.mkSymbol("orange"));

        System.out.println((fruit.getConsts()[0]));
        System.out.println((fruit.getConsts()[1]));
        System.out.println((fruit.getConsts()[2]));

        System.out.println((fruit.getTesterDecls()[0]));
        System.out.println((fruit.getTesterDecls()[1]));
        System.out.println((fruit.getTesterDecls()[2]));

        Expr apple = fruit.getConsts()[0];
        Expr banana = fruit.getConsts()[1];
        Expr orange = fruit.getConsts()[2];

        /* Apples are different from oranges */
        prove(ctx, ctx.mkNot(ctx.mkEq(apple, orange)), false);

        /* Apples pass the apple test */
        prove(ctx, (BoolExpr) ctx.mkApp(fruit.getTesterDecls()[0], apple),
                false);

        /* Oranges fail the apple test */
        disprove(ctx, (BoolExpr) ctx.mkApp(fruit.getTesterDecls()[0], orange),
                false);
        prove(ctx,
                (BoolExpr) ctx.mkNot((BoolExpr) ctx.mkApp(
                        fruit.getTesterDecls()[0], orange)), false);

        Expr fruity = ctx.mkConst("fruity", fruit);

        /* If something is fruity, then it is an apple, banana, or orange */

        prove(ctx,
                ctx.mkOr(ctx.mkEq(fruity, apple), ctx.mkEq(fruity, banana),
                        ctx.mkEq(fruity, orange)), false);
    }

    // / Create a list datatype.

    public void listExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ListExample");
        Log.append("ListExample");

        Sort int_ty;
        ListSort int_list;
        Expr nil, l1, l2, x, y, u, v;
        BoolExpr fml, fml1;

        int_ty = ctx.mkIntSort();

        int_list = ctx.mkListSort(ctx.mkSymbol("int_list"), int_ty);

        nil = ctx.mkConst(int_list.getNilDecl());
        l1 = ctx.mkApp(int_list.getConsDecl(), ctx.mkInt(1), nil);
        l2 = ctx.mkApp(int_list.getConsDecl(), ctx.mkInt(2), nil);

        /* nil != cons(1, nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(nil, l1)), false);

        /* cons(2,nil) != cons(1, nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(l1, l2)), false);

        /* cons(x,nil) = cons(y, nil) => x = y */
        x = ctx.mkConst("x", int_ty);
        y = ctx.mkConst("y", int_ty);
        l1 = ctx.mkApp(int_list.getConsDecl(), x, nil);
        l2 = ctx.mkApp(int_list.getConsDecl(), y, nil);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* cons(x,u) = cons(x, v) => u = v */
        u = ctx.mkConst("u", int_list);
        v = ctx.mkConst("v", int_list);
        l1 = ctx.mkApp(int_list.getConsDecl(), x, u);
        l2 = ctx.mkApp(int_list.getConsDecl(), y, v);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(u, v)), false);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* is_nil(u) or is_cons(u) */
        prove(ctx, ctx.mkOr((BoolExpr) ctx.mkApp(int_list.getIsNilDecl(), u),
                (BoolExpr) ctx.mkApp(int_list.getIsConsDecl(), u)), false);

        /* occurs check u != cons(x,u) */
        prove(ctx, ctx.mkNot(ctx.mkEq(u, l1)), false);

        /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
        fml1 = ctx.mkEq(
                u,
                ctx.mkApp(int_list.getConsDecl(),
                        ctx.mkApp(int_list.getHeadDecl(), u),
                        ctx.mkApp(int_list.getTailDecl(), u)));
        fml = ctx.mkImplies((BoolExpr) ctx.mkApp(int_list.getIsConsDecl(), u),
                fml1);
        System.out.println("Formula " + fml);

        prove(ctx, fml, false);

        disprove(ctx, fml1, false);
    }

    // / Create a binary tree datatype.

    public void treeExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("TreeExample");
        Log.append("TreeExample");

        Sort cell;
        FuncDecl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
        Expr nil, l1, l2, x, y, u, v;
        BoolExpr fml, fml1;
        String[] head_tail = new String[] { "car", "cdr" };
        Sort[] sorts = new Sort[] { null, null };
        int[] sort_refs = new int[] { 0, 0 };
        Constructor nil_con, cons_con;

        nil_con = ctx.mkConstructor("nil", "is_nil", null, null, null);
        cons_con = ctx.mkConstructor("cons", "is_cons", head_tail, sorts,
                sort_refs);
        Constructor[] constructors = new Constructor[] { nil_con, cons_con };

        cell = ctx.mkDatatypeSort("cell", constructors);

        nil_decl = nil_con.ConstructorDecl();
        is_nil_decl = nil_con.getTesterDecl();
        cons_decl = cons_con.ConstructorDecl();
        is_cons_decl = cons_con.getTesterDecl();
        FuncDecl[] cons_accessors = cons_con.getAccessorDecls();
        car_decl = cons_accessors[0];
        cdr_decl = cons_accessors[1];

        nil = ctx.mkConst(nil_decl);
        l1 = ctx.mkApp(cons_decl, nil, nil);
        l2 = ctx.mkApp(cons_decl, l1, nil);

        /* nil != cons(nil, nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(nil, l1)), false);

        /* cons(x,u) = cons(x, v) => u = v */
        u = ctx.mkConst("u", cell);
        v = ctx.mkConst("v", cell);
        x = ctx.mkConst("x", cell);
        y = ctx.mkConst("y", cell);
        l1 = ctx.mkApp(cons_decl, x, u);
        l2 = ctx.mkApp(cons_decl, y, v);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(u, v)), false);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* is_nil(u) or is_cons(u) */
        prove(ctx,
                ctx.mkOr((BoolExpr) ctx.mkApp(is_nil_decl, u),
                        (BoolExpr) ctx.mkApp(is_cons_decl, u)), false);

        /* occurs check u != cons(x,u) */
        prove(ctx, ctx.mkNot(ctx.mkEq(u, l1)), false);

        /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
        fml1 = ctx.mkEq(
                u,
                ctx.mkApp(cons_decl, ctx.mkApp(car_decl, u),
                        ctx.mkApp(cdr_decl, u)));
        fml = ctx.mkImplies((BoolExpr) ctx.mkApp(is_cons_decl, u), fml1);
        System.out.println("Formula " + fml);
        prove(ctx, fml, false);

        disprove(ctx, fml1, false);
    }

    // / Create a forest of trees.

    // / <remarks>
    // / forest ::= nil | cons(tree, forest)
    // / tree ::= nil | cons(forest, forest)
    // / </remarks>
    public void forestExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ForestExample");
        Log.append("ForestExample");

        Sort tree, forest;
        @SuppressWarnings("unused")
        FuncDecl nil1_decl, is_nil1_decl, cons1_decl, is_cons1_decl, car1_decl, cdr1_decl;
        @SuppressWarnings("unused")
        FuncDecl nil2_decl, is_nil2_decl, cons2_decl, is_cons2_decl, car2_decl, cdr2_decl;
        @SuppressWarnings("unused")
        Expr nil1, nil2, t1, t2, t3, t4, f1, f2, f3, l1, l2, x, y, u, v;

        //
        // Declare the names of the accessors for cons.
        // Then declare the sorts of the accessors.
        // For this example, all sorts refer to the new types 'forest' and
        // 'tree'
        // being declared, so we pass in null for both sorts1 and sorts2.
        // On the other hand, the sort_refs arrays contain the indices of the
        // two new sorts being declared. The first element in sort1_refs
        // points to 'tree', which has index 1, the second element in sort1_refs
        // array
        // points to 'forest', which has index 0.
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
        Constructor nil1_con, cons1_con, nil2_con, cons2_con;
        Constructor[] constructors1 = new Constructor[2], constructors2 = new Constructor[2];
        Symbol[] sort_names = { ctx.mkSymbol("forest"), ctx.mkSymbol("tree") };

        /* build a forest */
        nil1_con = ctx.mkConstructor(ctx.mkSymbol("nil"),
                ctx.mkSymbol("is_nil"), null, null, null);
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

        Constructor[][] clists = new Constructor[][] { constructors1,
                constructors2 };

        Sort[] sorts = ctx.mkDatatypeSorts(sort_names, clists);
        forest = sorts[0];
        tree = sorts[1];

        //
        // Now that the datatype has been created.
        // Query the constructors for the constructor
        // functions, testers, and field accessors.
        //
        nil1_decl = nil1_con.ConstructorDecl();
        is_nil1_decl = nil1_con.getTesterDecl();
        cons1_decl = cons1_con.ConstructorDecl();
        is_cons1_decl = cons1_con.getTesterDecl();
        FuncDecl[] cons1_accessors = cons1_con.getAccessorDecls();
        car1_decl = cons1_accessors[0];
        cdr1_decl = cons1_accessors[1];

        nil2_decl = nil2_con.ConstructorDecl();
        is_nil2_decl = nil2_con.getTesterDecl();
        cons2_decl = cons2_con.ConstructorDecl();
        is_cons2_decl = cons2_con.getTesterDecl();
        FuncDecl[] cons2_accessors = cons2_con.getAccessorDecls();
        car2_decl = cons2_accessors[0];
        cdr2_decl = cons2_accessors[1];

        nil1 = ctx.mkConst(nil1_decl);
        nil2 = ctx.mkConst(nil2_decl);
        f1 = ctx.mkApp(cons1_decl, nil2, nil1);
        t1 = ctx.mkApp(cons2_decl, nil1, nil1);
        t2 = ctx.mkApp(cons2_decl, f1, nil1);
        t3 = ctx.mkApp(cons2_decl, f1, f1);
        t4 = ctx.mkApp(cons2_decl, nil1, f1);
        f2 = ctx.mkApp(cons1_decl, t1, nil1);
        f3 = ctx.mkApp(cons1_decl, t1, f1);

        /* nil != cons(nil,nil) */
        prove(ctx, ctx.mkNot(ctx.mkEq(nil1, f1)), false);
        prove(ctx, ctx.mkNot(ctx.mkEq(nil2, t1)), false);

        /* cons(x,u) = cons(x, v) => u = v */
        u = ctx.mkConst("u", forest);
        v = ctx.mkConst("v", forest);
        x = ctx.mkConst("x", tree);
        y = ctx.mkConst("y", tree);
        l1 = ctx.mkApp(cons1_decl, x, u);
        l2 = ctx.mkApp(cons1_decl, y, v);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(u, v)), false);
        prove(ctx, ctx.mkImplies(ctx.mkEq(l1, l2), ctx.mkEq(x, y)), false);

        /* is_nil(u) or is_cons(u) */
        prove(ctx,
                ctx.mkOr((BoolExpr) ctx.mkApp(is_nil1_decl, u),
                        (BoolExpr) ctx.mkApp(is_cons1_decl, u)), false);

        /* occurs check u != cons(x,u) */
        prove(ctx, ctx.mkNot(ctx.mkEq(u, l1)), false);
    }

    // / Demonstrate how to use #Eval.

    public void evalExample1(Context ctx) throws Z3Exception
    {
        System.out.println("EvalExample1");
        Log.append("EvalExample1");

        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr two = ctx.mkInt(2);

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
            Expr v = model.evaluate(ctx.mkAdd(x, y), false);
            if (v != null)
            {
                System.out.println("result = " + (v));
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

    public void evalExample2(Context ctx) throws Z3Exception
    {
        System.out.println("EvalExample2");
        Log.append("EvalExample2");

        Sort int_type = ctx.getIntSort();
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
        FuncDecl first = tuple.getFieldDecls()[0]; // declarations are for
                                                   // projections
        FuncDecl second = tuple.getFieldDecls()[1];
        Expr tup1 = ctx.mkConst("t1", tuple);
        Expr tup2 = ctx.mkConst("t2", tuple);

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
            System.out.println("evaluating tup1 "
                    + (model.evaluate(tup1, false)));
            System.out.println("evaluating tup2 "
                    + (model.evaluate(tup2, false)));
            System.out.println("evaluating second(tup2) "
                    + (model.evaluate(ctx.mkApp(second, tup2), false)));
        } else
        {
            System.out.println("BUG, the constraints are satisfiable.");
        }
    }

    // / Demonstrate how to use <code>Push</code>and <code>Pop</code>to
    // / control the size of models.

    // / <remarks>Note: this test is specialized to 32-bit bitvectors.</remarks>
    public void checkSmall(Context ctx, Solver solver,
            BitVecExpr... to_minimize) throws Z3Exception
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
            while (check_is_sat && some_work)
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
                    Expr v = solver.getModel().evaluate(to_minimize[i], false);
                    int ui = ((BitVecNum) v).getInt();
                    if (ui < upper[i])
                    {
                        upper[i] = (int) ui;
                    }
                    System.out.println(i + " " + lower[i] + " " + upper[i]);
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

    public void findSmallModelExample(Context ctx) throws Z3Exception
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

    public void simplifierExample(Context ctx) throws Z3Exception
    {
        System.out.println("SimplifierExample");
        Log.append("SimplifierExample");

        IntExpr x = ctx.mkIntConst("x");
        IntExpr y = ctx.mkIntConst("y");
        IntExpr z = ctx.mkIntConst("z");
        @SuppressWarnings("unused")
        IntExpr u = ctx.mkIntConst("u");

        Expr t1 = ctx.mkAdd(x, ctx.mkSub(y, ctx.mkAdd(x, z)));
        Expr t2 = t1.simplify();
        System.out.println((t1) + " -> " + (t2));
    }

    // / Extract unsatisfiable core example

    public void unsatCoreAndProofExample(Context ctx) throws Z3Exception
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
            System.out.println("proof: " + solver.getProof());
            System.out.println("core: ");
            for (Expr c : solver.getUnsatCore())
            {
                System.out.println(c);
            }
        }
    }
    
    /// Extract unsatisfiable core example with AssertAndTrack
    
    public void unsatCoreAndProofExample2(Context ctx) throws Z3Exception
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
            for (Expr c : solver.getUnsatCore())
            {
                System.out.println(c);
            }
        }
    }

    public void finiteDomainExample(Context ctx) throws Z3Exception
    {
        System.out.println("FiniteDomainExample");
        Log.append("FiniteDomainExample");

        FiniteDomainSort s = ctx.mkFiniteDomainSort("S", 10);
        FiniteDomainSort t = ctx.mkFiniteDomainSort("T", 10);
        Expr s1 = ctx.mkNumeral(1, s);
        Expr t1 = ctx.mkNumeral(1, t);
        System.out.println(s);
        System.out.println(t);
        System.out.println(s1);
        System.out.println(ctx.mkNumeral(2, s));
        System.out.println(t1);
        // But you cannot mix numerals of different sorts
        // even if the size of their domains are the same:
        // System.out.println(ctx.mkEq(s1, t1));
    }    

    public void floatingPointExample1(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("FloatingPointExample1");
        Log.append("FloatingPointExample1");
        
        FPSort s = ctx.mkFPSort(11, 53);
        System.out.println("Sort: " + s);

        FPNum x = (FPNum)ctx.mkNumeral("-1e1", s); /* -1 * 10^1 = -10 */
        FPNum y = (FPNum)ctx.mkNumeral("-10", s); /* -10 */
        FPNum z = (FPNum)ctx.mkNumeral("-1.25p3", s); /* -1.25 * 2^3 = -1.25 * 8 = -10 */
        System.out.println("x=" + x.toString()  + 
                           "; y=" + y.toString() + 
                           "; z=" + z.toString());
        
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
        System.out.println("OK, unsat:" + System.getProperty("line.separator") + slvr);

        /* NaN is equal to NaN according to normal equality. */
        slvr = ctx.mkSolver("QF_FP");
        slvr.add(ctx.mkEq(nan, nan));
        if (slvr.check() != Status.SATISFIABLE)
            throw new TestFailedException();
        System.out.println("OK, sat:" + System.getProperty("line.separator")  + slvr);

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
        System.out.println("OK, unsat:" + System.getProperty("line.separator")  + slvr);
    }

    public void floatingPointExample2(Context ctx) throws Z3Exception, TestFailedException
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
        System.out.println("c5 = " + c5);

        /* Generic solver */
        Solver s = ctx.mkSolver();
        s.add(c5);

        if (s.check() != Status.SATISFIABLE)
            throw new TestFailedException();

        System.out.println("OK, model: " + s.getModel().toString());        
    }
    
    public static void main(String[] args)
    {
        JavaExample p = new JavaExample();
        try
        {
            com.microsoft.z3.Global.ToggleWarningMessages(true);
            Log.open("test.log");

            System.out.print("Z3 Major Version: ");
            System.out.println(Version.getMajor());
            System.out.print("Z3 Full Version: ");
            System.out.println(Version.getString());

            p.simpleExample();

            { // These examples need model generation turned on.
                HashMap<String, String> cfg = new HashMap<String, String>();
                cfg.put("model", "true");
                Context ctx = new Context(cfg);
                p.basicTests(ctx);
                p.castingTest(ctx);
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
                p.parserExample4(ctx);
                p.parserExample5(ctx);
                p.iteExample(ctx);
                p.evalExample1(ctx);
                p.evalExample2(ctx);
                p.findSmallModelExample(ctx);
                p.simplifierExample(ctx);
                p.finiteDomainExample(ctx);
                p.floatingPointExample1(ctx);
                p.floatingPointExample2(ctx);
            }

            { // These examples need proof generation turned on.
                HashMap<String, String> cfg = new HashMap<String, String>();
                cfg.put("proof", "true");
                Context ctx = new Context(cfg);
                p.proveExample1(ctx);
                p.proveExample2(ctx);
                p.arrayExample2(ctx);
                p.tupleExample(ctx);
                p.parserExample3(ctx);
                p.enumExample(ctx);
                p.listExample(ctx);
                p.treeExample(ctx);
                p.forestExample(ctx);
                p.unsatCoreAndProofExample(ctx);
                p.unsatCoreAndProofExample2(ctx);
            }

            { // These examples need proof generation turned on and auto-config
              // set to false.
                HashMap<String, String> cfg = new HashMap<String, String>();
                cfg.put("proof", "true");
                cfg.put("auto-config", "false");
                Context ctx = new Context(cfg);
                p.quantifierExample3(ctx);
                p.quantifierExample4(ctx);
            }            

            Log.close();
            if (Log.isOpen())
                System.out.println("Log is still open!");
        } catch (Z3Exception ex)
        {
            System.out.println("Z3 Managed Exception: " + ex.getMessage());
            System.out.println("Stack trace: ");
            ex.printStackTrace(System.out);
        } catch (TestFailedException ex)
        {
            System.out.println("TEST CASE FAILED: " + ex.getMessage());
            System.out.println("Stack trace: ");
            ex.printStackTrace(System.out);
        } catch (Exception ex)
        {
            System.out.println("Unknown Exception: " + ex.getMessage());
            System.out.println("Stack trace: ");
            ex.printStackTrace(System.out);
        }
    }
}
