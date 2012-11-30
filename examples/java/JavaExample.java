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

    public BoolExpr InjAxiom(Context ctx, FuncDecl f, int i) throws Z3Exception
    {
        Sort[] domain = f.Domain();
        int sz = f.DomainSize();

        if (i >= sz)
        {
            System.out.println("failed to create inj axiom");
            return null;
        }

        /* declare the i-th inverse of f: finv */
        Sort finv_domain = f.Range();
        Sort finv_range = domain[i];
        FuncDecl finv = ctx.MkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        Expr[] xs = new Expr[sz];
        Symbol[] names = new Symbol[sz];
        Sort[] types = new Sort[sz];

        /* fill types, names and xs */

        for (int j = 0; j < sz; j++)
        {
            types[j] = domain[j];
            names[j] = ctx.MkSymbol("x_" + Integer.toString(j));
            xs[j] = ctx.MkBound(j, types[j]);
        }
        Expr x_i = xs[i];

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr fxs = f.Apply(xs);

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr finv_fxs = finv.Apply(fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Expr eq = ctx.MkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = ctx.MkPattern(new Expr[] { fxs });

        /* create & assert quantifier */
        BoolExpr q = ctx.MkForall(types, /* types of quantified variables */
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

    public BoolExpr InjAxiomAbs(Context ctx, FuncDecl f, int i)
            throws Z3Exception
    {
        Sort[] domain = f.Domain();
        int sz = f.DomainSize();

        if (i >= sz)
        {
            System.out.println("failed to create inj axiom");
            return null;
        }

        /* declare the i-th inverse of f: finv */
        Sort finv_domain = f.Range();
        Sort finv_range = domain[i];
        FuncDecl finv = ctx.MkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        Expr[] xs = new Expr[sz];

        /* fill types, names and xs */
        for (int j = 0; j < sz; j++)
        {
            xs[j] = ctx.MkConst("x_" + Integer.toString(j), domain[j]);
        }
        Expr x_i = xs[i];

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr fxs = f.Apply(xs);

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr finv_fxs = finv.Apply(fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Expr eq = ctx.MkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = ctx.MkPattern(new Expr[] { fxs });

        /* create & assert quantifier */
        BoolExpr q = ctx.MkForall(xs, /* types of quantified variables */
                eq, /* names of quantified variables */
                1, new Pattern[] { p } /* patterns */, null, null, null);

        return q;
    }

    // / Assert the axiom: function f is commutative.

    // / <remarks>
    // / This example uses the SMT-LIB parser to simplify the axiom
    // construction.
    // / </remarks>
    private BoolExpr CommAxiom(Context ctx, FuncDecl f) throws Exception
    {
        Sort t = f.Range();
        Sort[] dom = f.Domain();

        if (dom.length != 2 || !t.equals(dom[0]) || !t.equals(dom[1]))
        {
            System.out.println(Integer.toString(dom.length) + " "
                    + dom[0].toString() + " " + dom[1].toString() + " "
                    + t.toString());
            throw new Exception(
                    "function must be binary, and argument types must be equal to return type");
        }

        String bench = "(benchmark comm :formula (forall (x " + t.Name()
                + ") (y " + t.Name() + ") (= (" + f.Name() + " x y) ("
                + f.Name() + " y x))))";
        ctx.ParseSMTLIBString(bench, new Symbol[] { t.Name() },
                new Sort[] { t }, new Symbol[] { f.Name() },
                new FuncDecl[] { f });
        return ctx.SMTLIBFormulas()[0];
    }

    // / "Hello world" example: create a Z3 logical context, and delete it.

    public void SimpleExample() throws Z3Exception
    {
        System.out.println("SimpleExample");

        {
            Context ctx = new Context();
            /* do something with the context */

            /* be kind to dispose manually and not wait for the GC. */
            ctx.Dispose();
        }
    }

    Model Check(Context ctx, BoolExpr f, Status sat) throws Z3Exception,
            TestFailedException
    {
        Solver s = ctx.MkSolver();
        s.Assert(f);
        if (s.Check() != sat)
            throw new TestFailedException();
        if (sat == Status.SATISFIABLE)
            return s.Model();
        else
            return null;
    }

    void SolveTactical(Context ctx, Tactic t, Goal g, Status sat)
            throws Z3Exception, TestFailedException
    {
        Solver s = ctx.MkSolver(t);
        System.out.println("\nTactical solver: " + s);

        for (BoolExpr a : g.Formulas())
            s.Assert(a);
        System.out.println("Solver: " + s);

        if (s.Check() != sat)
            throw new TestFailedException();
    }

    ApplyResult ApplyTactic(Context ctx, Tactic t, Goal g) throws Z3Exception
    {
        System.out.println("\nGoal: " + g);

        ApplyResult res = t.Apply(g);
        System.out.println("Application result: " + res);

        Status q = Status.UNKNOWN;
        for (Goal sg : res.Subgoals())
            if (sg.IsDecidedSat())
                q = Status.SATISFIABLE;
            else if (sg.IsDecidedUnsat())
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

    void Prove(Context ctx, BoolExpr f) throws Z3Exception, TestFailedException
    {
        BoolExpr[] assumptions = new BoolExpr[0];
        Prove(ctx, f, assumptions);
    }

    void Prove(Context ctx, BoolExpr f, BoolExpr assumption)
            throws Z3Exception, TestFailedException
    {
        BoolExpr[] assumptions = { assumption };
        Prove(ctx, f, assumptions);
    }

    void Prove(Context ctx, BoolExpr f, BoolExpr[] assumptions)
            throws Z3Exception, TestFailedException
    {
        System.out.println("Proving: " + f);
        Solver s = ctx.MkSolver();
        for (BoolExpr a : assumptions)
            s.Assert(a);
        s.Assert(ctx.MkNot(f));
        Status q = s.Check();

        switch (q)
        {
        case UNKNOWN:
            System.out.println("Unknown because: " + s.ReasonUnknown());
            break;
        case SATISFIABLE:
            throw new TestFailedException();
        case UNSATISFIABLE:
            System.out.println("OK, proof: " + s.Proof());
            break;
        }
    }

    void Disprove(Context ctx, BoolExpr f) throws Z3Exception,
            TestFailedException
    {
        BoolExpr[] a = {};
        Disprove(ctx, f, a);
    }

    void Disprove(Context ctx, BoolExpr f, BoolExpr assumption)
            throws Z3Exception, TestFailedException
    {
        BoolExpr[] a = { assumption };
        Disprove(ctx, f, a);
    }

    void Disprove(Context ctx, BoolExpr f, BoolExpr[] assumptions)
            throws Z3Exception, TestFailedException
    {
        System.out.println("Disproving: " + f);
        Solver s = ctx.MkSolver();
        for (BoolExpr a : assumptions)
            s.Assert(a);
        s.Assert(ctx.MkNot(f));
        Status q = s.Check();

        switch (q)
        {
        case UNKNOWN:
            System.out.println("Unknown because: " + s.ReasonUnknown());
            break;
        case SATISFIABLE:
            System.out.println("OK, model: " + s.Model());
            break;
        case UNSATISFIABLE:
            throw new TestFailedException();
        }
    }

    void ModelConverterTest(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ModelConverterTest");

        ArithExpr xr = (ArithExpr) ctx.MkConst(ctx.MkSymbol("x"),
                ctx.MkRealSort());
        ArithExpr yr = (ArithExpr) ctx.MkConst(ctx.MkSymbol("y"),
                ctx.MkRealSort());
        Goal g4 = ctx.MkGoal(true, false, true);
        g4.Assert(ctx.MkGt(xr, ctx.MkReal(10, 1)));
        g4.Assert(ctx.MkEq(yr,
                ctx.MkAdd(new ArithExpr[] { xr, ctx.MkReal(1, 1) })));
        g4.Assert(ctx.MkGt(yr, ctx.MkReal(1, 1)));

        ApplyResult ar = ApplyTactic(ctx, ctx.MkTactic("simplify"), g4);
        if (ar.NumSubgoals() == 1
                && (ar.Subgoals()[0].IsDecidedSat() || ar.Subgoals()[0]
                        .IsDecidedUnsat()))
            throw new TestFailedException();

        ar = ApplyTactic(ctx, ctx.AndThen(ctx.MkTactic("simplify"),
                ctx.MkTactic("solve-eqs"), null), g4);
        if (ar.NumSubgoals() == 1
                && (ar.Subgoals()[0].IsDecidedSat() || ar.Subgoals()[0]
                        .IsDecidedUnsat()))
            throw new TestFailedException();

        Solver s = ctx.MkSolver();
        for (BoolExpr e : ar.Subgoals()[0].Formulas())
            s.Assert(e);
        Status q = s.Check();
        System.out.println("Solver says: " + q);
        System.out.println("Model: \n" + s.Model());
        System.out.println("Converted Model: \n"
                + ar.ConvertModel(0, s.Model()));
        if (q != Status.SATISFIABLE)
            throw new TestFailedException();
    }

    // / A simple array example.

    void ArrayExample1(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("ArrayExample1");

        Goal g = ctx.MkGoal(true, false, false);
        ArraySort asort = ctx.MkArraySort(ctx.IntSort(), ctx.MkBitVecSort(32));
        ArrayExpr aex = (ArrayExpr) ctx.MkConst(ctx.MkSymbol("MyArray"), asort);
        Expr sel = ctx.MkSelect(aex, ctx.MkInt(0));
        g.Assert(ctx.MkEq(sel, ctx.MkBV(42, 32)));
        Symbol xs = ctx.MkSymbol("x");
        IntExpr xc = (IntExpr) ctx.MkConst(xs, ctx.IntSort());

        Symbol fname = ctx.MkSymbol("f");
        Sort[] domain = { ctx.IntSort() };
        FuncDecl fd = ctx.MkFuncDecl(fname, domain, ctx.IntSort());
        Expr[] fargs = { ctx.MkConst(xs, ctx.IntSort()) };
        IntExpr fapp = (IntExpr) ctx.MkApp(fd, fargs);

        g.Assert(ctx.MkEq(ctx.MkAdd(new ArithExpr[] { xc, fapp }),
                ctx.MkInt(123)));

        Solver s = ctx.MkSolver();
        for (BoolExpr a : g.Formulas())
            s.Assert(a);
        System.out.println("Solver: " + s);

        Status q = s.Check();
        System.out.println("Status: " + q);

        if (q != Status.SATISFIABLE)
            throw new TestFailedException();

        System.out.println("Model = " + s.Model());

        System.out.println("Interpretation of MyArray:\n"
                + s.Model().FuncInterp(aex.FuncDecl()));
        System.out
                .println("Interpretation of x:\n" + s.Model().ConstInterp(xc));
        System.out.println("Interpretation of f:\n" + s.Model().FuncInterp(fd));
        System.out.println("Interpretation of MyArray as Term:\n"
                + s.Model().FuncInterp(aex.FuncDecl()));
    }

    // / Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2
    // = i3 or select(a1, i3) = select(a2, i3))</tt>.

    // / <remarks>This example demonstrates how to use the array
    // theory.</remarks>
    public void ArrayExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ArrayExample2");

        Sort int_type = ctx.IntSort();
        Sort array_type = ctx.MkArraySort(int_type, int_type);

        ArrayExpr a1 = (ArrayExpr) ctx.MkConst("a1", array_type);
        ArrayExpr a2 = ctx.MkArrayConst("a2", int_type, int_type);
        Expr i1 = ctx.MkConst("i1", int_type);
        Expr i2 = ctx.MkConst("i2", int_type);
        Expr i3 = ctx.MkConst("i3", int_type);
        Expr v1 = ctx.MkConst("v1", int_type);
        Expr v2 = ctx.MkConst("v2", int_type);

        Expr st1 = ctx.MkStore(a1, i1, v1);
        Expr st2 = ctx.MkStore(a2, i2, v2);

        Expr sel1 = ctx.MkSelect(a1, i3);
        Expr sel2 = ctx.MkSelect(a2, i3);

        /* create antecedent */
        BoolExpr antecedent = ctx.MkEq(st1, st2);

        /*
         * create consequent: i1 = i3 or i2 = i3 or select(a1, i3) = select(a2,
         * i3)
         */
        BoolExpr consequent = ctx.MkOr(new BoolExpr[] { ctx.MkEq(i1, i3),
                ctx.MkEq(i2, i3), ctx.MkEq(sel1, sel2) });

        /*
         * prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 =
         * i3 or select(a1, i3) = select(a2, i3))
         */
        BoolExpr thm = ctx.MkImplies(antecedent, consequent);
        System.out
                .println("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))");
        System.out.println(thm);
        Prove(ctx, thm);
    }

    // / Show that <code>distinct(a_0, ... , a_n)</code> is
    // / unsatisfiable when <code>a_i</code>'s are arrays from boolean to
    // / boolean and n > 4.

    // / <remarks>This example also shows how to use the <code>distinct</code>
    // construct.</remarks>
    public void ArrayExample3(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ArrayExample3");

        for (int n = 2; n <= 5; n++)
        {
            System.out.println("n = " + Integer.toString(n));

            Sort bool_type = ctx.MkBoolSort();
            Sort array_type = ctx.MkArraySort(bool_type, bool_type);
            Expr[] a = new Expr[n];

            /* create arrays */
            for (int i = 0; i < n; i++)
            {
                a[i] = ctx.MkConst("array_" + Integer.toString(i), array_type);
            }

            /* assert distinct(a[0], ..., a[n]) */
            BoolExpr d = ctx.MkDistinct(a);
            System.out.println(d);

            /* context is satisfiable if n < 5 */
            Model model = Check(ctx, d, n < 5 ? Status.SATISFIABLE
                    : Status.UNSATISFIABLE);
            if (n < 5)
            {
                for (int i = 0; i < n; i++)
                {
                    System.out.println(a[i].toString() + " = "
                            + model.Evaluate(a[i], false));
                }
            }
        }
    }

    // / Sudoku solving example.

    void SudokuExample(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("SudokuExample");

        // 9x9 matrix of integer variables
        IntExpr[][] X = new IntExpr[9][];
        for (int i = 0; i < 9; i++)
        {
            X[i] = new IntExpr[9];
            for (int j = 0; j < 9; j++)
                X[i][j] = (IntExpr) ctx.MkConst(
                        ctx.MkSymbol("x_" + (i + 1) + "_" + (j + 1)),
                        ctx.IntSort());
        }

        // each cell contains a value in {1, ..., 9}
        BoolExpr[][] cells_c = new BoolExpr[9][];
        for (int i = 0; i < 9; i++)
        {
            cells_c[i] = new BoolExpr[9];
            for (int j = 0; j < 9; j++)
                cells_c[i][j] = ctx.MkAnd(new BoolExpr[] {
                        ctx.MkLe(ctx.MkInt(1), X[i][j]),
                        ctx.MkLe(X[i][j], ctx.MkInt(9)) });
        }

        // each row contains a digit at most once
        BoolExpr[] rows_c = new BoolExpr[9];
        for (int i = 0; i < 9; i++)
            rows_c[i] = ctx.MkDistinct(X[i]);

        // each column contains a digit at most once
        BoolExpr[] cols_c = new BoolExpr[9];
        for (int j = 0; j < 9; j++)
            cols_c[j] = ctx.MkDistinct(X[j]);

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
                sq_c[i0][j0] = ctx.MkDistinct(square);
            }
        }

        BoolExpr sudoku_c = ctx.MkTrue();
        for (BoolExpr[] t : cells_c)
            sudoku_c = ctx.MkAnd(new BoolExpr[] { ctx.MkAnd(t), sudoku_c });
        sudoku_c = ctx.MkAnd(new BoolExpr[] { ctx.MkAnd(rows_c), sudoku_c });
        sudoku_c = ctx.MkAnd(new BoolExpr[] { ctx.MkAnd(cols_c), sudoku_c });
        for (BoolExpr[] t : sq_c)
            sudoku_c = ctx.MkAnd(new BoolExpr[] { ctx.MkAnd(t), sudoku_c });

        // sudoku instance, we use '0' for empty cells
        int[][] instance = { { 0, 0, 0, 0, 9, 4, 0, 3, 0 },
                { 0, 0, 0, 5, 1, 0, 0, 0, 7 }, { 0, 8, 9, 0, 0, 0, 0, 4, 0 },
                { 0, 0, 0, 0, 0, 0, 2, 0, 8 }, { 0, 6, 0, 2, 0, 1, 0, 5, 0 },
                { 1, 0, 2, 0, 0, 0, 0, 0, 0 }, { 0, 7, 0, 0, 0, 0, 5, 2, 0 },
                { 9, 0, 0, 0, 6, 5, 0, 0, 0 }, { 0, 4, 0, 9, 7, 0, 0, 0, 0 } };

        BoolExpr instance_c = ctx.MkTrue();
        for (int i = 0; i < 9; i++)
            for (int j = 0; j < 9; j++)
                instance_c = ctx
                        .MkAnd(new BoolExpr[] {
                                instance_c,
                                (BoolExpr) ctx.MkITE(
                                        ctx.MkEq(ctx.MkInt(instance[i][j]),
                                                ctx.MkInt(0)),
                                        ctx.MkTrue(),
                                        ctx.MkEq(X[i][j],
                                                ctx.MkInt(instance[i][j]))) });

        Solver s = ctx.MkSolver();
        s.Assert(sudoku_c);
        s.Assert(instance_c);

        if (s.Check() == Status.SATISFIABLE)
        {
            Model m = s.Model();
            Expr[][] R = new Expr[9][9];
            for (int i = 0; i < 9; i++)
                for (int j = 0; j < 9; j++)
                    R[i][j] = m.Evaluate(X[i][j], false);
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

    void QuantifierExample1(Context ctx) throws Z3Exception
    {
        System.out.println("QuantifierExample");

        Sort[] types = new Sort[3];
        IntExpr[] xs = new IntExpr[3];
        Symbol[] names = new Symbol[3];
        IntExpr[] vars = new IntExpr[3];

        for (int j = 0; j < 3; j++)
        {
            types[j] = ctx.IntSort();
            names[j] = ctx.MkSymbol("x_" + Integer.toString(j));
            xs[j] = (IntExpr) ctx.MkConst(names[j], types[j]);
            vars[j] = (IntExpr) ctx.MkBound(2 - j, types[j]); // <-- vars
                                                              // reversed!
        }

        Expr body_vars = ctx
                .MkAnd(new BoolExpr[] {
                        ctx.MkEq(
                                ctx.MkAdd(new ArithExpr[] { vars[0],
                                        ctx.MkInt(1) }), ctx.MkInt(2)),
                        ctx.MkEq(
                                ctx.MkAdd(new ArithExpr[] { vars[1],
                                        ctx.MkInt(2) }),
                                ctx.MkAdd(new ArithExpr[] { vars[2],
                                        ctx.MkInt(3) })) });

        Expr body_const = ctx.MkAnd(new BoolExpr[] {
                ctx.MkEq(ctx.MkAdd(new ArithExpr[] { xs[0], ctx.MkInt(1) }),
                        ctx.MkInt(2)),
                ctx.MkEq(ctx.MkAdd(new ArithExpr[] { xs[1], ctx.MkInt(2) }),
                        ctx.MkAdd(new ArithExpr[] { xs[2], ctx.MkInt(3) })) });

        Expr x = ctx.MkForall(types, names, body_vars, 1, null, null,
                ctx.MkSymbol("Q1"), ctx.MkSymbol("skid1"));
        System.out.println("Quantifier X: " + x.toString());

        Expr y = ctx.MkForall(xs, body_const, 1, null, null,
                ctx.MkSymbol("Q2"), ctx.MkSymbol("skid2"));
        System.out.println("Quantifier Y: " + y.toString());
    }

    void QuantifierExample2(Context ctx) throws Z3Exception
    {

        System.out.println("QuantifierExample2");

        Expr q1, q2;
        FuncDecl f = ctx.MkFuncDecl("f", ctx.IntSort(), ctx.IntSort());
        FuncDecl g = ctx.MkFuncDecl("g", ctx.IntSort(), ctx.IntSort());

        // Quantifier with Exprs as the bound variables.
        {
            Expr x = ctx.MkConst("x", ctx.IntSort());
            Expr y = ctx.MkConst("y", ctx.IntSort());
            Expr f_x = ctx.MkApp(f, new Expr[] { x });
            Expr f_y = ctx.MkApp(f, new Expr[] { y });
            Expr g_y = ctx.MkApp(g, new Expr[] { y });
            Pattern[] pats = new Pattern[] { ctx.MkPattern(new Expr[] { f_x,
                    g_y }) };
            Expr[] no_pats = new Expr[] { f_y };
            Expr[] bound = new Expr[] { x, y };
            Expr body = ctx.MkAnd(new BoolExpr[] { ctx.MkEq(f_x, f_y),
                    ctx.MkEq(f_y, g_y) });

            q1 = ctx.MkForall(bound, body, 1, null, no_pats, ctx.MkSymbol("q"),
                    ctx.MkSymbol("sk"));

            System.out.println(q1);
        }

        // Quantifier with de-Brujin indices.
        {
            Expr x = ctx.MkBound(1, ctx.IntSort());
            Expr y = ctx.MkBound(0, ctx.IntSort());
            Expr f_x = ctx.MkApp(f, new Expr[] { x });
            Expr f_y = ctx.MkApp(f, new Expr[] { y });
            Expr g_y = ctx.MkApp(g, new Expr[] { y });
            Pattern[] pats = new Pattern[] { ctx.MkPattern(new Expr[] { f_x,
                    g_y }) };
            Expr[] no_pats = new Expr[] { f_y };
            Symbol[] names = new Symbol[] { ctx.MkSymbol("x"),
                    ctx.MkSymbol("y") };
            Sort[] sorts = new Sort[] { ctx.IntSort(), ctx.IntSort() };
            Expr body = ctx.MkAnd(new BoolExpr[] { ctx.MkEq(f_x, f_y),
                    ctx.MkEq(f_y, g_y) });

            q2 = ctx.MkForall(sorts, names, body, 1, null, // pats,
                    no_pats, ctx.MkSymbol("q"), ctx.MkSymbol("sk"));
            System.out.println(q2);
        }

        System.out.println(q1.equals(q2));
    }

    // / Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
    // / <code>f</code> is injective in the second argument. <seealso
    // cref="inj_axiom"/>

    public void QuantifierExample3() throws Z3Exception, TestFailedException
    {
        System.out.println("QuantifierExample3");

        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("MBQI", "false");
        cfg.put("PROOF_MODE", "2");
        cfg.put("AUTO_CONFIG", "false");

        /*
         * If quantified formulas are asserted in a logical context, then the
         * model produced by Z3 should be viewed as a potential model.
         */

        {
            Context ctx = new Context(cfg);

            /* declare function f */
            Sort I = ctx.IntSort();
            FuncDecl f = ctx.MkFuncDecl("f", new Sort[] { I, I }, I);

            /* f is injective in the second argument. */
            BoolExpr inj = InjAxiom(ctx, f, 1);

            /* create x, y, v, w, fxy, fwv */
            Expr x = ctx.MkIntConst("x");
            Expr y = ctx.MkIntConst("y");
            Expr v = ctx.MkIntConst("v");
            Expr w = ctx.MkIntConst("w");
            Expr fxy = ctx.MkApp(f, new Expr[] { x, y });
            Expr fwv = ctx.MkApp(f, new Expr[] { w, v });

            /* f(x, y) = f(w, v) */
            BoolExpr p1 = ctx.MkEq(fxy, fwv);

            /* prove f(x, y) = f(w, v) implies y = v */
            BoolExpr p2 = ctx.MkEq(y, v);
            Prove(ctx, p2, new BoolExpr[] { inj, p1 });

            /* disprove f(x, y) = f(w, v) implies x = w */
            BoolExpr p3 = ctx.MkEq(x, w);
            Disprove(ctx, p3, new BoolExpr[] { inj, p1 });
        }
    }

    // / Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
    // / <code>f</code> is injective in the second argument. <seealso
    // cref="inj_axiom"/>

    public void QuantifierExample4() throws Z3Exception, TestFailedException
    {
        System.out.println("QuantifierExample4");

        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("MBQI", "false");
        cfg.put("PROOF_MODE", "2");
        cfg.put("AUTO_CONFIG", "false");

        /*
         * If quantified formulas are asserted in a logical context, then the
         * model produced by Z3 should be viewed as a potential model.
         */

        {
            Context ctx = new Context(cfg);
            /* declare function f */
            Sort I = ctx.IntSort();
            FuncDecl f = ctx.MkFuncDecl("f", new Sort[] { I, I }, I);

            /* f is injective in the second argument. */
            BoolExpr inj = InjAxiomAbs(ctx, f, 1);

            /* create x, y, v, w, fxy, fwv */
            Expr x = ctx.MkIntConst("x");
            Expr y = ctx.MkIntConst("y");
            Expr v = ctx.MkIntConst("v");
            Expr w = ctx.MkIntConst("w");
            Expr fxy = ctx.MkApp(f, new Expr[] { x, y });
            Expr fwv = ctx.MkApp(f, new Expr[] { w, v });

            /* f(x, y) = f(w, v) */
            BoolExpr p1 = ctx.MkEq(fxy, fwv);

            /* prove f(x, y) = f(w, v) implies y = v */
            BoolExpr p2 = ctx.MkEq(y, v);
            Prove(ctx, p2, new BoolExpr[] { inj, p1 });

            /* disprove f(x, y) = f(w, v) implies x = w */
            BoolExpr p3 = ctx.MkEq(x, w);
            Disprove(ctx, p3, new BoolExpr[] { inj, p1 });
        }
    }

    // / Some basic tests.

    void BasicTests(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("BasicTests");

        Symbol fname = ctx.MkSymbol("f");
        Symbol x = ctx.MkSymbol("x");
        Symbol y = ctx.MkSymbol("y");

        Sort bs = ctx.MkBoolSort();

        Sort[] domain = { bs, bs };
        FuncDecl f = ctx.MkFuncDecl(fname, domain, bs);
        Expr fapp = ctx.MkApp(f,
                new Expr[] { ctx.MkConst(x, bs), ctx.MkConst(y, bs) });

        Expr[] fargs2 = { ctx.MkFreshConst("cp", bs) };
        Sort[] domain2 = { bs };
        Expr fapp2 = ctx.MkApp(ctx.MkFreshFuncDecl("fp", domain2, bs), fargs2);

        BoolExpr trivial_eq = ctx.MkEq(fapp, fapp);
        BoolExpr nontrivial_eq = ctx.MkEq(fapp, fapp2);

        Goal g = ctx.MkGoal(true, false, true);
        g.Assert(trivial_eq);
        g.Assert(nontrivial_eq);
        System.out.println("Goal: " + g);

        Solver solver = ctx.MkSolver();

        for (BoolExpr a : g.Formulas())
            solver.Assert(a);

        if (solver.Check() != Status.SATISFIABLE)
            throw new TestFailedException();

        ApplyResult ar = ApplyTactic(ctx, ctx.MkTactic("simplify"), g);
        if (ar.NumSubgoals() == 1
                && (ar.Subgoals()[0].IsDecidedSat() || ar.Subgoals()[0]
                        .IsDecidedUnsat()))
            throw new TestFailedException();

        ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g);
        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedSat())
            throw new TestFailedException();

        g.Assert(ctx.MkEq(ctx.MkNumeral(1, ctx.MkBitVecSort(32)),
                ctx.MkNumeral(2, ctx.MkBitVecSort(32))));
        ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g);
        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedUnsat())
            throw new TestFailedException();

        Goal g2 = ctx.MkGoal(true, true, false);
        ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g2);
        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedSat())
            throw new TestFailedException();

        g2 = ctx.MkGoal(true, true, false);
        g2.Assert(ctx.MkFalse());
        ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g2);
        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedUnsat())
            throw new TestFailedException();

        Goal g3 = ctx.MkGoal(true, true, false);
        Expr xc = ctx.MkConst(ctx.MkSymbol("x"), ctx.IntSort());
        Expr yc = ctx.MkConst(ctx.MkSymbol("y"), ctx.IntSort());
        g3.Assert(ctx.MkEq(xc, ctx.MkNumeral(1, ctx.IntSort())));
        g3.Assert(ctx.MkEq(yc, ctx.MkNumeral(2, ctx.IntSort())));
        BoolExpr constr = ctx.MkEq(xc, yc);
        g3.Assert(constr);
        ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g3);
        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedUnsat())
            throw new TestFailedException();

        ModelConverterTest(ctx);

        // Real num/den test.
        RatNum rn = ctx.MkReal(42, 43);
        Expr inum = rn.Numerator();
        Expr iden = rn.Denominator();
        System.out.println("Numerator: " + inum + " Denominator: " + iden);
        if (!inum.toString().equals("42") || !iden.toString().equals("43"))
            throw new TestFailedException();

        if (!rn.ToDecimalString(3).toString().equals("0.976?"))
            throw new TestFailedException();

        BigIntCheck(ctx, ctx.MkReal("-1231231232/234234333"));
        BigIntCheck(ctx, ctx.MkReal("-123123234234234234231232/234234333"));
        BigIntCheck(ctx, ctx.MkReal("-234234333"));
        BigIntCheck(ctx, ctx.MkReal("234234333/2"));

        String bn = "1234567890987654321";

        if (!ctx.MkInt(bn).BigInteger().toString().equals(bn))
            throw new TestFailedException();

        if (!ctx.MkBV(bn, 128).BigInteger().toString().equals(bn))
            throw new TestFailedException();

        if (ctx.MkBV(bn, 32).BigInteger().toString().equals(bn))
            throw new TestFailedException();

        // Error handling test.
        try
        {
            IntExpr i = ctx.MkInt("0.5");
            throw new TestFailedException(); // unreachable
        } catch (Z3Exception e)
        {
            System.out.println("GOT: " + e.getMessage());
        }
    }

    // / Some basic expression casting tests.

    void CastingTest(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("CastingTest");

        Sort[] domain = { ctx.BoolSort(), ctx.BoolSort() };
        FuncDecl f = ctx.MkFuncDecl("f", domain, ctx.BoolSort());

        AST upcast = ctx.MkFuncDecl(ctx.MkSymbol("q"), domain, ctx.BoolSort());

        try
        {
            FuncDecl downcast = (FuncDecl) f; // OK
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        try
        {
            Expr uc = (Expr) upcast;
            throw new TestFailedException(); // should not be reachable!
        } catch (ClassCastException e)
        {
        }

        Symbol s = ctx.MkSymbol(42);
        IntSymbol si = (s.getClass() == IntSymbol.class) ? (IntSymbol) s : null;
        if (si == null)
            throw new TestFailedException();
        try
        {
            IntSymbol si2 = (IntSymbol) s;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        s = ctx.MkSymbol("abc");
        StringSymbol ss = (s.getClass() == StringSymbol.class) ? (StringSymbol) s
                : null;
        if (ss == null)
            throw new TestFailedException();
        try
        {
            StringSymbol ss2 = (StringSymbol) s;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }
        try
        {
            IntSymbol si2 = (IntSymbol) s;
            throw new TestFailedException(); // unreachable
        } catch (Exception e)
        {
        }

        Sort srt = ctx.MkBitVecSort(32);
        BitVecSort bvs = null;
        try
        {
            bvs = (BitVecSort) srt;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        if (bvs.Size() != 32)
            throw new TestFailedException();

        Expr q = ctx.MkAdd(new ArithExpr[] { ctx.MkInt(1), ctx.MkInt(2) });
        Expr q2 = q.Args()[1];
        Sort qs = q2.Sort();
        if (qs.getClass() != IntSort.class)
            throw new TestFailedException();
        try
        {
            IntSort isrt = (IntSort) qs;
        } catch (ClassCastException e)
        {
            throw new TestFailedException();
        }

        AST a = ctx.MkInt(42);
        Expr ae = (a.getClass() == Expr.class) ? ((Expr) a) : null;
        if (ae == null)
            throw new TestFailedException();
        ArithExpr aae = (a.getClass() == ArithExpr.class) ? ((ArithExpr) a)
                : null;
        if (aae == null)
            throw new TestFailedException();
        IntExpr aie = (a.getClass() == IntExpr.class) ? ((IntExpr) a) : null;
        if (aie == null)
            throw new TestFailedException();
        IntNum ain = (a.getClass() == IntNum.class) ? ((IntNum) a) : null;
        if (ain == null)
            throw new TestFailedException();

        Expr[][] earr = new Expr[2][];
        earr[0] = new Expr[2];
        earr[1] = new Expr[2];
        earr[0][0] = ctx.MkTrue();
        earr[0][1] = ctx.MkTrue();
        earr[1][0] = ctx.MkFalse();
        earr[1][1] = ctx.MkFalse();
        for (Expr[] ea : earr)
            for (Expr e : ea)
            {
                try
                {
                    Expr ns = ctx.MkNot((BoolExpr) e);
                    BoolExpr ens = (BoolExpr) ns;
                } catch (ClassCastException ex)
                {
                    throw new TestFailedException();
                }
            }
    }

    // / Shows how to read an SMT1 file.

    void SMT1FileTest(String filename) throws Z3Exception
    {
        System.out.print("SMT File test ");

        {
            HashMap<String, String> cfg = new HashMap<String, String>();
            Context ctx = new Context(cfg);
            ctx.ParseSMTLIBFile(filename, null, null, null, null);

            BoolExpr a = ctx.MkAnd(ctx.SMTLIBFormulas());
            System.out.println("read formula: " + a);
        }
    }

    // / Shows how to read an SMT2 file.

    void SMT2FileTest(String filename) throws Z3Exception
    {
        Date before = new Date();

        System.out.println("SMT2 File test ");
        System.gc();

        {
            HashMap<String, String> cfg = new HashMap<String, String>();
            cfg.put("MODEL", "true");
            Context ctx = new Context(cfg);
            Expr a = ctx.ParseSMTLIB2File(filename, null, null, null, null);

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
                    if (!(cur.IsVar()))
                        for (Expr c : ((Expr) cur).Args())
                            q.add(c);
            }
            System.out.println(cnt + " ASTs");
        }

        long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;
        System.out.println("SMT2 file test took " + t_diff + " sec");
    }

    // / Shows how to use Solver(logic)

    // / <param name="ctx"></param>
    void LogicExample(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("LogicTest");

        Context.ToggleWarningMessages(true);

        BitVecSort bvs = ctx.MkBitVecSort(32);
        Expr x = ctx.MkConst("x", bvs);
        Expr y = ctx.MkConst("y", bvs);
        BoolExpr eq = ctx.MkEq(x, y);

        // Use a solver for QF_BV
        Solver s = ctx.MkSolver("QF_BV");
        s.Assert(eq);
        Status res = s.Check();
        System.out.println("solver result: " + res);

        // Or perhaps a tactic for QF_BV
        Goal g = ctx.MkGoal(true, false, true);
        g.Assert(eq);

        Tactic t = ctx.MkTactic("qfbv");
        ApplyResult ar = t.Apply(g);
        System.out.println("tactic result: " + ar);

        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedSat())
            throw new TestFailedException();
    }

    // / Demonstrates how to use the ParOr tactic.

    void ParOrExample(Context ctx) throws Z3Exception, TestFailedException
    {
        System.out.println("ParOrExample");

        BitVecSort bvs = ctx.MkBitVecSort(32);
        Expr x = ctx.MkConst("x", bvs);
        Expr y = ctx.MkConst("y", bvs);
        BoolExpr q = ctx.MkEq(x, y);

        Goal g = ctx.MkGoal(true, false, true);
        g.Assert(q);

        Tactic t1 = ctx.MkTactic("qfbv");
        Tactic t2 = ctx.MkTactic("qfbv");
        Tactic p = ctx.ParOr(new Tactic[] { t1, t2 });

        ApplyResult ar = p.Apply(g);

        if (ar.NumSubgoals() != 1 || !ar.Subgoals()[0].IsDecidedSat())
            throw new TestFailedException();
    }

    void BigIntCheck(Context ctx, RatNum r) throws Z3Exception
    {
        System.out.println("Num: " + r.BigIntNumerator());
        System.out.println("Den: " + r.BigIntDenominator());
    }

    // / Find a model for <code>x xor y</code>.

    public void FindModelExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("FindModelExample1");

        BoolExpr x = ctx.MkBoolConst("x");
        BoolExpr y = ctx.MkBoolConst("y");
        BoolExpr x_xor_y = ctx.MkXor(x, y);

        Model model = Check(ctx, x_xor_y, Status.SATISFIABLE);
        System.out.println("x = " + model.Evaluate(x, false) + ", y = "
                + model.Evaluate(y, false));
    }

    // / Find a model for <tt>x < y + 1, x > 2</tt>.
    // / Then, assert <tt>not(x = y)</tt>, and find another model.

    public void FindModelExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("find_model_example2");

        IntExpr x = ctx.MkIntConst("x");
        IntExpr y = ctx.MkIntConst("y");
        IntExpr one = ctx.MkInt(1);
        IntExpr two = ctx.MkInt(2);

        ArithExpr y_plus_one = ctx.MkAdd(new ArithExpr[] { y, one });

        BoolExpr c1 = ctx.MkLt(x, y_plus_one);
        BoolExpr c2 = ctx.MkGt(x, two);

        BoolExpr q = ctx.MkAnd(new BoolExpr[] { c1, c2 });

        System.out.println("model for: x < y + 1, x > 2");
        Model model = Check(ctx, q, Status.SATISFIABLE);
        System.out.println("x = " + model.Evaluate(x, false) + ", y ="
                + model.Evaluate(y, false));

        /* assert not(x = y) */
        BoolExpr x_eq_y = ctx.MkEq(x, y);
        BoolExpr c3 = ctx.MkNot(x_eq_y);

        q = ctx.MkAnd(new BoolExpr[] { q, c3 });

        System.out.println("model for: x < y + 1, x > 2, not(x = y)");
        model = Check(ctx, q, Status.SATISFIABLE);
        System.out.println("x = " + model.Evaluate(x, false) + ", y = "
                + model.Evaluate(y, false));
    }

    // / Prove <tt>x = y implies g(x) = g(y)</tt>, and
    // / disprove <tt>x = y implies g(g(x)) = g(y)</tt>.

    // / <remarks>This function demonstrates how to create uninterpreted
    // / types and functions.</remarks>
    public void ProveExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ProveExample1");

        /* create uninterpreted type. */
        Sort U = ctx.MkUninterpretedSort(ctx.MkSymbol("U"));

        /* declare function g */
        FuncDecl g = ctx.MkFuncDecl("g", U, U);

        /* create x and y */
        Expr x = ctx.MkConst("x", U);
        Expr y = ctx.MkConst("y", U);
        /* create g(x), g(y) */
        Expr gx = g.Apply(x);
        Expr gy = g.Apply(y);

        /* assert x = y */
        BoolExpr eq = ctx.MkEq(x, y);

        /* prove g(x) = g(y) */
        BoolExpr f = ctx.MkEq(gx, gy);
        System.out.println("prove: x = y implies g(x) = g(y)");
        Prove(ctx, ctx.MkImplies(eq, f));

        /* create g(g(x)) */
        Expr ggx = g.Apply(gx);

        /* disprove g(g(x)) = g(y) */
        f = ctx.MkEq(ggx, gy);
        System.out.println("disprove: x = y implies g(g(x)) = g(y)");
        Disprove(ctx, ctx.MkImplies(eq, f));

        /* Print the model using the custom model printer */
        Model m = Check(ctx, ctx.MkNot(f), Status.SATISFIABLE);
        System.out.println(m);
    }

    // / Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0
    // </tt>.
    // / Then, show that <tt>z < -1</tt> is not implied.

    // / <remarks>This example demonstrates how to combine uninterpreted
    // functions
    // / and arithmetic.</remarks>
    public void ProveExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ProveExample2");

        /* declare function g */
        Sort I = ctx.IntSort();

        FuncDecl g = ctx.MkFuncDecl("g", I, I);

        /* create x, y, and z */
        IntExpr x = ctx.MkIntConst("x");
        IntExpr y = ctx.MkIntConst("y");
        IntExpr z = ctx.MkIntConst("z");

        /* create gx, gy, gz */
        Expr gx = ctx.MkApp(g, x);
        Expr gy = ctx.MkApp(g, y);
        Expr gz = ctx.MkApp(g, z);

        /* create zero */
        IntExpr zero = ctx.MkInt(0);

        /* assert not(g(g(x) - g(y)) = g(z)) */
        ArithExpr gx_gy = ctx.MkSub(new ArithExpr[] { (IntExpr) gx,
                (IntExpr) gy });
        Expr ggx_gy = ctx.MkApp(g, gx_gy);
        BoolExpr eq = ctx.MkEq(ggx_gy, gz);
        BoolExpr c1 = ctx.MkNot(eq);

        /* assert x + z <= y */
        ArithExpr x_plus_z = ctx.MkAdd(new ArithExpr[] { x, z });
        BoolExpr c2 = ctx.MkLe(x_plus_z, y);

        /* assert y <= x */
        BoolExpr c3 = ctx.MkLe(y, x);

        /* prove z < 0 */
        BoolExpr f = ctx.MkLt(z, zero);
        System.out
                .println("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0");
        Prove(ctx, f, new BoolExpr[] { c1, c2, c3 });

        /* disprove z < -1 */
        IntExpr minus_one = ctx.MkInt(-1);
        f = ctx.MkLt(z, minus_one);
        System.out
                .println("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1");
        Disprove(ctx, f, new BoolExpr[] { c1, c2, c3 });
    }

    // / Show how push & pop can be used to create "backtracking" points.

    // / <remarks>This example also demonstrates how big numbers can be
    // / created in ctx.</remarks>
    public void PushPopExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("PushPopExample1");

        /* create a big number */
        IntSort int_type = ctx.IntSort();
        IntExpr big_number = ctx
                .MkInt("1000000000000000000000000000000000000000000000000000000");

        /* create number 3 */
        IntExpr three = (IntExpr) ctx.MkNumeral("3", int_type);

        /* create x */
        IntExpr x = ctx.MkIntConst("x");

        Solver solver = ctx.MkSolver();

        /* assert x >= "big number" */
        BoolExpr c1 = ctx.MkGe(x, big_number);
        System.out.println("assert: x >= 'big number'");
        solver.Assert(c1);

        /* create a backtracking point */
        System.out.println("push");
        solver.Push();

        /* assert x <= 3 */
        BoolExpr c2 = ctx.MkLe(x, three);
        System.out.println("assert: x <= 3");
        solver.Assert(c2);

        /* context is inconsistent at this point */
        if (solver.Check() != Status.UNSATISFIABLE)
            throw new TestFailedException();

        /*
         * backtrack: the constraint x <= 3 will be removed, since it was
         * asserted after the last ctx.Push.
         */
        System.out.println("pop");
        solver.Pop(1);

        /* the context is consistent again. */
        if (solver.Check() != Status.SATISFIABLE)
            throw new TestFailedException();

        /* new constraints can be asserted... */

        /* create y */
        IntExpr y = ctx.MkIntConst("y");

        /* assert y > x */
        BoolExpr c3 = ctx.MkGt(y, x);
        System.out.println("assert: y > x");
        solver.Assert(c3);

        /* the context is still consistent. */
        if (solver.Check() != Status.SATISFIABLE)
            throw new TestFailedException();
    }

    // / Tuples.

    // / <remarks>Check that the projection of a tuple
    // / returns the corresponding element.</remarks>
    public void TupleExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("TupleExample");

        Sort int_type = ctx.IntSort();
        TupleSort tuple = ctx.MkTupleSort(ctx.MkSymbol("mk_tuple"), // name of
                                                                    // tuple
                                                                    // constructor
                new Symbol[] { ctx.MkSymbol("first"), ctx.MkSymbol("second") }, // names
                                                                                // of
                                                                                // projection
                                                                                // operators
                new Sort[] { int_type, int_type } // types of projection
                                                  // operators
                );
        FuncDecl first = tuple.FieldDecls()[0]; // declarations are for
                                                // projections
        FuncDecl second = tuple.FieldDecls()[1];
        Expr x = ctx.MkConst("x", int_type);
        Expr y = ctx.MkConst("y", int_type);
        Expr n1 = tuple.MkDecl().Apply(new Expr[] { x, y });
        Expr n2 = first.Apply(n1);
        BoolExpr n3 = ctx.MkEq(x, n2);
        System.out.println("Tuple example: " + n3);
        Prove(ctx, n3);
    }

    // / Simple bit-vector example.

    // / <remarks>
    // / This example disproves that x - 10 &lt;= 0 IFF x &lt;= 10 for (32-bit)
    // machine integers
    // / </remarks>
    public void BitvectorExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("BitvectorExample1");

        Sort bv_type = ctx.MkBitVecSort(32);
        BitVecExpr x = (BitVecExpr) ctx.MkConst("x", bv_type);
        BitVecNum zero = (BitVecNum) ctx.MkNumeral("0", bv_type);
        BitVecNum ten = ctx.MkBV(10, 32);
        BitVecExpr x_minus_ten = ctx.MkBVSub(x, ten);
        /* bvsle is signed less than or equal to */
        BoolExpr c1 = ctx.MkBVSLE(x, ten);
        BoolExpr c2 = ctx.MkBVSLE(x_minus_ten, zero);
        BoolExpr thm = ctx.MkIff(c1, c2);
        System.out
                .println("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers");
        Disprove(ctx, thm);
    }

    // / Find x and y such that: x ^ y - 103 == x * y

    public void BitvectorExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("BitvectorExample2");

        /* construct x ^ y - 103 == x * y */
        Sort bv_type = ctx.MkBitVecSort(32);
        BitVecExpr x = ctx.MkBVConst("x", 32);
        BitVecExpr y = ctx.MkBVConst("y", 32);
        BitVecExpr x_xor_y = ctx.MkBVXOR(x, y);
        BitVecExpr c103 = (BitVecNum) ctx.MkNumeral("103", bv_type);
        BitVecExpr lhs = ctx.MkBVSub(x_xor_y, c103);
        BitVecExpr rhs = ctx.MkBVMul(x, y);
        BoolExpr ctr = ctx.MkEq(lhs, rhs);

        System.out
                .println("find values of x and y, such that x ^ y - 103 == x * y");

        /* find a model (i.e., values for x an y that satisfy the constraint */
        Model m = Check(ctx, ctr, Status.SATISFIABLE);
        System.out.println(m);
    }

    // / Demonstrates how to use the SMTLIB parser.

    public void ParserExample1(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ParserExample1");

        ctx.ParseSMTLIBString(
                "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))",
                null, null, null, null);
        for (BoolExpr f : ctx.SMTLIBFormulas())
            System.out.println("formula " + f);

        Model m = Check(ctx, ctx.MkAnd(ctx.SMTLIBFormulas()),
                Status.SATISFIABLE);
    }

    // / Demonstrates how to initialize the parser symbol table.

    public void ParserExample2(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ParserExample2");

        Symbol[] declNames = { ctx.MkSymbol("a"), ctx.MkSymbol("b") };
        FuncDecl a = ctx.MkConstDecl(declNames[0], ctx.MkIntSort());
        FuncDecl b = ctx.MkConstDecl(declNames[1], ctx.MkIntSort());
        FuncDecl[] decls = new FuncDecl[] { a, b };

        ctx.ParseSMTLIBString("(benchmark tst :formula (> a b))", null, null,
                declNames, decls);
        BoolExpr f = ctx.SMTLIBFormulas()[0];
        System.out.println("formula: " + f);
        Check(ctx, f, Status.SATISFIABLE);
    }

    // / Demonstrates how to initialize the parser symbol table.

    public void ParserExample3(Context ctx) throws Exception
    {
        System.out.println("ParserExample3");

        /* declare function g */
        Sort I = ctx.MkIntSort();
        FuncDecl g = ctx.MkFuncDecl("g", new Sort[] { I, I }, I);

        BoolExpr ca = CommAxiom(ctx, g);

        ctx.ParseSMTLIBString(
                "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (gg x 0) (gg 0 y)))))",
                null, null, new Symbol[] { ctx.MkSymbol("gg") },
                new FuncDecl[] { g });

        BoolExpr thm = ctx.SMTLIBFormulas()[0];
        System.out.println("formula: " + thm);
        Prove(ctx, thm, ca);
    }

    // / Display the declarations, assumptions and formulas in a SMT-LIB string.

    public void ParserExample4(Context ctx) throws Z3Exception
    {
        System.out.println("ParserExample4");

        ctx.ParseSMTLIBString(
                "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))",
                null, null, null, null);
        for (FuncDecl decl : ctx.SMTLIBDecls())
        {
            System.out.println("Declaration: " + decl);
        }
        for (BoolExpr f : ctx.SMTLIBAssumptions())
        {
            System.out.println("Assumption: " + f);
        }
        for (BoolExpr f : ctx.SMTLIBFormulas())
        {
            System.out.println("Formula: " + f);
        }
    }

    // / Demonstrates how to handle parser errors using Z3 error handling
    // support.

    // / <remarks></remarks>
    public void ParserExample5(Context ctx)
    {
        System.out.println("ParserExample5");

        try
        {
            ctx.ParseSMTLIBString(
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

    public void ITEExample(Context ctx) throws Z3Exception
    {
        System.out.println("ITEExample");

        BoolExpr f = ctx.MkFalse();
        Expr one = ctx.MkInt(1);
        Expr zero = ctx.MkInt(0);
        Expr ite = ctx.MkITE(f, one, zero);

        System.out.println("Expr: " + ite);
    }

    // / Create an enumeration data type.

    public void EnumExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("EnumExample");

        Symbol name = ctx.MkSymbol("fruit");

        EnumSort fruit = ctx.MkEnumSort(ctx.MkSymbol("fruit"),
                new Symbol[] { ctx.MkSymbol("apple"), ctx.MkSymbol("banana"),
                        ctx.MkSymbol("orange") });

        System.out.println((fruit.Consts()[0]));
        System.out.println((fruit.Consts()[1]));
        System.out.println((fruit.Consts()[2]));

        System.out.println((fruit.TesterDecls()[0]));
        System.out.println((fruit.TesterDecls()[1]));
        System.out.println((fruit.TesterDecls()[2]));

        Expr apple = fruit.Consts()[0];
        Expr banana = fruit.Consts()[1];
        Expr orange = fruit.Consts()[2];

        /* Apples are different from oranges */
        Prove(ctx, ctx.MkNot(ctx.MkEq(apple, orange)));

        /* Apples pass the apple test */
        Prove(ctx, (BoolExpr) ctx.MkApp(fruit.TesterDecls()[0], apple));

        /* Oranges fail the apple test */
        Disprove(ctx, (BoolExpr) ctx.MkApp(fruit.TesterDecls()[0], orange));
        Prove(ctx, (BoolExpr) ctx.MkNot((BoolExpr) ctx.MkApp(
                fruit.TesterDecls()[0], orange)));

        Expr fruity = ctx.MkConst("fruity", fruit);

        /* If something is fruity, then it is an apple, banana, or orange */

        Prove(ctx,
                ctx.MkOr(new BoolExpr[] { ctx.MkEq(fruity, apple),
                        ctx.MkEq(fruity, banana), ctx.MkEq(fruity, orange) }));
    }

    // / Create a list datatype.

    public void ListExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ListExample");

        Sort int_ty;
        ListSort int_list;
        Expr nil, l1, l2, x, y, u, v;
        BoolExpr fml, fml1;

        int_ty = ctx.MkIntSort();

        int_list = ctx.MkListSort(ctx.MkSymbol("int_list"), int_ty);

        nil = ctx.MkConst(int_list.NilDecl());
        l1 = ctx.MkApp(int_list.ConsDecl(), new Expr[] { ctx.MkInt(1), nil });
        l2 = ctx.MkApp(int_list.ConsDecl(), new Expr[] { ctx.MkInt(2), nil });

        /* nil != cons(1, nil) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(nil, l1)));

        /* cons(2,nil) != cons(1, nil) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(l1, l2)));

        /* cons(x,nil) = cons(y, nil) => x = y */
        x = ctx.MkConst("x", int_ty);
        y = ctx.MkConst("y", int_ty);
        l1 = ctx.MkApp(int_list.ConsDecl(), new Expr[] { x, nil });
        l2 = ctx.MkApp(int_list.ConsDecl(), new Expr[] { y, nil });
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

        /* cons(x,u) = cons(x, v) => u = v */
        u = ctx.MkConst("u", int_list);
        v = ctx.MkConst("v", int_list);
        l1 = ctx.MkApp(int_list.ConsDecl(), new Expr[] { x, u });
        l2 = ctx.MkApp(int_list.ConsDecl(), new Expr[] { y, v });
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(u, v)));
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

        /* is_nil(u) or is_cons(u) */
        Prove(ctx,
                ctx.MkOr(new BoolExpr[] {
                        (BoolExpr) ctx.MkApp(int_list.IsNilDecl(),
                                new Expr[] { u }),
                        (BoolExpr) ctx.MkApp(int_list.IsConsDecl(),
                                new Expr[] { u }) }));

        /* occurs check u != cons(x,u) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(u, l1)));

        /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
        fml1 = ctx.MkEq(u, ctx.MkApp(int_list.ConsDecl(),
                new Expr[] { ctx.MkApp(int_list.HeadDecl(), new Expr[] { u }),
                        ctx.MkApp(int_list.TailDecl(), new Expr[] { u }) }));
        fml = ctx.MkImplies(
                (BoolExpr) ctx.MkApp(int_list.IsConsDecl(), new Expr[] { u }),
                fml1);
        System.out.println("Formula " + fml);

        Prove(ctx, fml);

        Disprove(ctx, fml1);
    }

    // / Create a binary tree datatype.

    public void TreeExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("TreeExample");

        Sort cell;
        FuncDecl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
        Expr nil, l1, l2, x, y, u, v;
        BoolExpr fml, fml1;
        String[] head_tail = new String[] { "car", "cdr" };
        Sort[] sorts = new Sort[] { null, null };
        int[] sort_refs = new int[] { 0, 0 };
        Constructor nil_con, cons_con;

        nil_con = ctx.MkConstructor("nil", "is_nil", null, null, null);
        cons_con = ctx.MkConstructor("cons", "is_cons", head_tail, sorts,
                sort_refs);
        Constructor[] constructors = new Constructor[] { nil_con, cons_con };

        cell = ctx.MkDatatypeSort("cell", constructors);

        nil_decl = nil_con.ConstructorDecl();
        is_nil_decl = nil_con.TesterDecl();
        cons_decl = cons_con.ConstructorDecl();
        is_cons_decl = cons_con.TesterDecl();
        FuncDecl[] cons_accessors = cons_con.AccessorDecls();
        car_decl = cons_accessors[0];
        cdr_decl = cons_accessors[1];

        nil = ctx.MkConst(nil_decl);
        l1 = ctx.MkApp(cons_decl, new Expr[] { nil, nil });
        l2 = ctx.MkApp(cons_decl, new Expr[] { l1, nil });

        /* nil != cons(nil, nil) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(nil, l1)));

        /* cons(x,u) = cons(x, v) => u = v */
        u = ctx.MkConst("u", cell);
        v = ctx.MkConst("v", cell);
        x = ctx.MkConst("x", cell);
        y = ctx.MkConst("y", cell);
        l1 = ctx.MkApp(cons_decl, new Expr[] { x, u });
        l2 = ctx.MkApp(cons_decl, new Expr[] { y, v });
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(u, v)));
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

        /* is_nil(u) or is_cons(u) */
        Prove(ctx,
                ctx.MkOr(new BoolExpr[] {
                        (BoolExpr) ctx.MkApp(is_nil_decl, new Expr[] { u }),
                        (BoolExpr) ctx.MkApp(is_cons_decl, new Expr[] { u }) }));

        /* occurs check u != cons(x,u) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(u, l1)));

        /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
        fml1 = ctx.MkEq(
                u,
                ctx.MkApp(
                        cons_decl,
                        new Expr[] { ctx.MkApp(car_decl, u),
                                ctx.MkApp(cdr_decl, u) }));
        fml = ctx.MkImplies((BoolExpr) ctx.MkApp(is_cons_decl, u), fml1);
        System.out.println("Formula " + fml);
        Prove(ctx, fml);

        Disprove(ctx, fml1);
    }

    // / Create a forest of trees.

    // / <remarks>
    // / forest ::= nil | cons(tree, forest)
    // / tree ::= nil | cons(forest, forest)
    // / </remarks>
    public void ForestExample(Context ctx) throws Z3Exception,
            TestFailedException
    {
        System.out.println("ForestExample");

        Sort tree, forest;
        FuncDecl nil1_decl, is_nil1_decl, cons1_decl, is_cons1_decl, car1_decl, cdr1_decl;
        FuncDecl nil2_decl, is_nil2_decl, cons2_decl, is_cons2_decl, car2_decl, cdr2_decl;
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
        Symbol[] head_tail1 = new Symbol[] { ctx.MkSymbol("head"),
                ctx.MkSymbol("tail") };
        Sort[] sorts1 = new Sort[] { null, null };
        int[] sort1_refs = new int[] { 1, 0 }; // the first item points to a
                                               // tree, the second to a forest

        Symbol[] head_tail2 = new Symbol[] { ctx.MkSymbol("car"),
                ctx.MkSymbol("cdr") };
        Sort[] sorts2 = new Sort[] { null, null };
        int[] sort2_refs = new int[] { 0, 0 }; // both items point to the forest
                                               // datatype.
        Constructor nil1_con, cons1_con, nil2_con, cons2_con;
        Constructor[] constructors1 = new Constructor[2], constructors2 = new Constructor[2];
        Symbol[] sort_names = { ctx.MkSymbol("forest"), ctx.MkSymbol("tree") };

        /* build a forest */
        nil1_con = ctx.MkConstructor(ctx.MkSymbol("nil"),
                ctx.MkSymbol("is_nil"), null, null, null);
        cons1_con = ctx.MkConstructor(ctx.MkSymbol("cons1"),
                ctx.MkSymbol("is_cons1"), head_tail1, sorts1, sort1_refs);
        constructors1[0] = nil1_con;
        constructors1[1] = cons1_con;

        /* build a tree */
        nil2_con = ctx.MkConstructor(ctx.MkSymbol("nil2"),
                ctx.MkSymbol("is_nil2"), null, null, null);
        cons2_con = ctx.MkConstructor(ctx.MkSymbol("cons2"),
                ctx.MkSymbol("is_cons2"), head_tail2, sorts2, sort2_refs);
        constructors2[0] = nil2_con;
        constructors2[1] = cons2_con;

        Constructor[][] clists = new Constructor[][] { constructors1,
                constructors2 };

        Sort[] sorts = ctx.MkDatatypeSorts(sort_names, clists);
        forest = sorts[0];
        tree = sorts[1];

        //
        // Now that the datatype has been created.
        // Query the constructors for the constructor
        // functions, testers, and field accessors.
        //
        nil1_decl = nil1_con.ConstructorDecl();
        is_nil1_decl = nil1_con.TesterDecl();
        cons1_decl = cons1_con.ConstructorDecl();
        is_cons1_decl = cons1_con.TesterDecl();
        FuncDecl[] cons1_accessors = cons1_con.AccessorDecls();
        car1_decl = cons1_accessors[0];
        cdr1_decl = cons1_accessors[1];

        nil2_decl = nil2_con.ConstructorDecl();
        is_nil2_decl = nil2_con.TesterDecl();
        cons2_decl = cons2_con.ConstructorDecl();
        is_cons2_decl = cons2_con.TesterDecl();
        FuncDecl[] cons2_accessors = cons2_con.AccessorDecls();
        car2_decl = cons2_accessors[0];
        cdr2_decl = cons2_accessors[1];

        nil1 = ctx.MkConst(nil1_decl);
        nil2 = ctx.MkConst(nil2_decl);
        f1 = ctx.MkApp(cons1_decl, new Expr[] { nil2, nil1 });
        t1 = ctx.MkApp(cons2_decl, new Expr[] { nil1, nil1 });
        t2 = ctx.MkApp(cons2_decl, new Expr[] { f1, nil1 });
        t3 = ctx.MkApp(cons2_decl, new Expr[] { f1, f1 });
        t4 = ctx.MkApp(cons2_decl, new Expr[] { nil1, f1 });
        f2 = ctx.MkApp(cons1_decl, new Expr[] { t1, nil1 });
        f3 = ctx.MkApp(cons1_decl, new Expr[] { t1, f1 });

        /* nil != cons(nil,nil) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(nil1, f1)));
        Prove(ctx, ctx.MkNot(ctx.MkEq(nil2, t1)));

        /* cons(x,u) = cons(x, v) => u = v */
        u = ctx.MkConst("u", forest);
        v = ctx.MkConst("v", forest);
        x = ctx.MkConst("x", tree);
        y = ctx.MkConst("y", tree);
        l1 = ctx.MkApp(cons1_decl, new Expr[] { x, u });
        l2 = ctx.MkApp(cons1_decl, new Expr[] { y, v });
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(u, v)));
        Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

        /* is_nil(u) or is_cons(u) */
        Prove(ctx, ctx.MkOr(new BoolExpr[] {
                (BoolExpr) ctx.MkApp(is_nil1_decl, new Expr[] { u }),
                (BoolExpr) ctx.MkApp(is_cons1_decl, new Expr[] { u }) }));

        /* occurs check u != cons(x,u) */
        Prove(ctx, ctx.MkNot(ctx.MkEq(u, l1)));
    }

    // / Demonstrate how to use #Eval.

    public void EvalExample1(Context ctx) throws Z3Exception
    {
        System.out.println("EvalExample1");

        IntExpr x = ctx.MkIntConst("x");
        IntExpr y = ctx.MkIntConst("y");
        IntExpr two = ctx.MkInt(2);

        Solver solver = ctx.MkSolver();

        /* assert x < y */
        solver.Assert(ctx.MkLt(x, y));

        /* assert x > 2 */
        solver.Assert(ctx.MkGt(x, two));

        /* find model for the constraints above */
        Model model = null;
        if (Status.SATISFIABLE == solver.Check())
        {
            model = solver.Model();
            System.out.println(model);
            System.out.println("\nevaluating x+y");
            Expr v = model.Evaluate(ctx.MkAdd(new ArithExpr[] { x, y }), false);
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

    public void EvalExample2(Context ctx) throws Z3Exception
    {
        System.out.println("EvalExample2");

        Sort int_type = ctx.IntSort();
        TupleSort tuple = ctx.MkTupleSort(ctx.MkSymbol("mk_tuple"), // name of
                                                                    // tuple
                                                                    // constructor
                new Symbol[] { ctx.MkSymbol("first"), ctx.MkSymbol("second") }, // names
                                                                                // of
                                                                                // projection
                                                                                // operators
                new Sort[] { int_type, int_type } // types of projection
                                                  // operators
                );
        FuncDecl first = tuple.FieldDecls()[0]; // declarations are for
                                                // projections
        FuncDecl second = tuple.FieldDecls()[1];
        Expr tup1 = ctx.MkConst("t1", tuple);
        Expr tup2 = ctx.MkConst("t2", tuple);

        Solver solver = ctx.MkSolver();

        /* assert tup1 != tup2 */
        solver.Assert(ctx.MkNot(ctx.MkEq(tup1, tup2)));
        /* assert first tup1 = first tup2 */
        solver.Assert(ctx.MkEq(ctx.MkApp(first, tup1), ctx.MkApp(first, tup2)));

        /* find model for the constraints above */
        Model model = null;
        if (Status.SATISFIABLE == solver.Check())
        {
            model = solver.Model();
            System.out.println(model);
            System.out.println("evaluating tup1 "
                    + (model.Evaluate(tup1, false)));
            System.out.println("evaluating tup2 "
                    + (model.Evaluate(tup2, false)));
            System.out.println("evaluating second(tup2) "
                    + (model.Evaluate(ctx.MkApp(second, tup2), false)));
        } else
        {
            System.out.println("BUG, the constraints are satisfiable.");
        }
    }

    // / Demonstrate how to use <code>Push</code>and <code>Pop</code>to
    // / control the size of models.

    // / <remarks>Note: this test is specialized to 32-bit bitvectors.</remarks>
    public void CheckSmall(Context ctx, Solver solver, BitVecExpr[] to_minimize)
            throws Z3Exception
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
            solver.Push();

            boolean check_is_sat = true;
            while (check_is_sat && some_work)
            {
                // Assert all feasible bounds.
                for (int i = 0; i < num_Exprs; ++i)
                {
                    solver.Assert(ctx.MkBVULE(to_minimize[i],
                            ctx.MkBV(upper[i], 32)));
                }

                check_is_sat = Status.SATISFIABLE == solver.Check();
                if (!check_is_sat)
                {
                    if (last_index != -1)
                    {
                        lower[last_index] = last_upper + 1;
                    }
                    break;
                }
                System.out.println(solver.Model());

                // narrow the bounds based on the current model.
                for (int i = 0; i < num_Exprs; ++i)
                {
                    Expr v = solver.Model().Evaluate(to_minimize[i], false);
                    int ui = ((BitVecNum) v).Int();
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
                        solver.Assert(ctx.MkBVULE(to_minimize[i],
                                ctx.MkBV(last_upper, 32)));
                        some_work = true;
                        break;
                    }
                }
            }
            solver.Pop();
        }
    }

    // / Reduced-size model generation example.

    public void FindSmallModelExample(Context ctx) throws Z3Exception
    {
        System.out.println("FindSmallModelExample");

        BitVecExpr x = ctx.MkBVConst("x", 32);
        BitVecExpr y = ctx.MkBVConst("y", 32);
        BitVecExpr z = ctx.MkBVConst("z", 32);

        Solver solver = ctx.MkSolver();

        solver.Assert(ctx.MkBVULE(x, ctx.MkBVAdd(y, z)));
        CheckSmall(ctx, solver, new BitVecExpr[] { x, y, z });
    }

    // / Simplifier example.

    public void SimplifierExample(Context ctx) throws Z3Exception
    {
        System.out.println("SimplifierExample");

        IntExpr x = ctx.MkIntConst("x");
        IntExpr y = ctx.MkIntConst("y");
        IntExpr z = ctx.MkIntConst("z");
        IntExpr u = ctx.MkIntConst("u");

        Expr t1 = ctx.MkAdd(new ArithExpr[] {
                x,
                ctx.MkSub(new ArithExpr[] { y,
                        ctx.MkAdd(new ArithExpr[] { x, z }) }) });
        Expr t2 = t1.Simplify();
        System.out.println((t1) + " -> " + (t2));
    }

    // / Extract unsatisfiable core example

    public void UnsatCoreAndProofExample() throws Z3Exception
    {
        System.out.println("UnsatCoreAndProofExample");

        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("PROOF_MODE", "2");

        {
            Context ctx = new Context(cfg);
            Solver solver = ctx.MkSolver();

            BoolExpr pa = ctx.MkBoolConst("PredA");
            BoolExpr pb = ctx.MkBoolConst("PredB");
            BoolExpr pc = ctx.MkBoolConst("PredC");
            BoolExpr pd = ctx.MkBoolConst("PredD");
            BoolExpr p1 = ctx.MkBoolConst("P1");
            BoolExpr p2 = ctx.MkBoolConst("P2");
            BoolExpr p3 = ctx.MkBoolConst("P3");
            BoolExpr p4 = ctx.MkBoolConst("P4");
            BoolExpr[] assumptions = new BoolExpr[] { ctx.MkNot(p1),
                    ctx.MkNot(p2), ctx.MkNot(p3), ctx.MkNot(p4) };
            BoolExpr f1 = ctx.MkAnd(new BoolExpr[] { pa, pb, pc });
            BoolExpr f2 = ctx.MkAnd(new BoolExpr[] { pa, ctx.MkNot(pb), pc });
            BoolExpr f3 = ctx.MkOr(new BoolExpr[] { ctx.MkNot(pa),
                    ctx.MkNot(pc) });
            BoolExpr f4 = pd;

            solver.Assert(ctx.MkOr(new BoolExpr[] { f1, p1 }));
            solver.Assert(ctx.MkOr(new BoolExpr[] { f2, p2 }));
            solver.Assert(ctx.MkOr(new BoolExpr[] { f3, p3 }));
            solver.Assert(ctx.MkOr(new BoolExpr[] { f4, p4 }));
            Status result = solver.Check(assumptions);

            if (result == Status.UNSATISFIABLE)
            {
                System.out.println("unsat");
                System.out.println("proof: " + solver.Proof());
                System.out.println("core: ");
                for (Expr c : solver.UnsatCore())
                {
                    System.out.println(c);
                }
            }
        }
    }

    public void FiniteDomainExample(Context ctx) throws Z3Exception
    {
        System.out.println("FiniteDomainExample");

        FiniteDomainSort s = ctx.MkFiniteDomainSort("S", 10);
        FiniteDomainSort t = ctx.MkFiniteDomainSort("T", 10);
        Expr s1 = ctx.MkNumeral(1, s);
        Expr t1 = ctx.MkNumeral(1, t);
        System.out.println(s);
        System.out.println(t);
        System.out.println(s1);
        System.out.println(ctx.MkNumeral(2, s));
        System.out.println(t1);
        // But you cannot mix numerals of different sorts
        // even if the size of their domains are the same:
        // System.out.println(ctx.MkEq(s1, t1));
    }

    public static void main(String[] args)
    {
        JavaExample p = new JavaExample();
        try
        {
            Context.ToggleWarningMessages(true);
            Log.Open("test.log");

            System.out.print("Z3 Major Version: ");
            System.out.println(Version.Major());
            System.out.print("Z3 Full Version: ");
            System.out.println(Version.getString());

            p.SimpleExample();

            {
                HashMap<String, String> cfg = new HashMap<String, String>();
                cfg.put("MODEL", "true");
                cfg.put("PROOF_MODE", "2");
                Context ctx = new Context(cfg);
                p.BasicTests(ctx);
                p.CastingTest(ctx);
                p.SudokuExample(ctx);
                p.QuantifierExample1(ctx);
                p.QuantifierExample2(ctx);
                p.LogicExample(ctx);
                p.ParOrExample(ctx);
                p.FindModelExample1(ctx);
                p.FindModelExample2(ctx);
                p.ProveExample1(ctx);
                p.ProveExample2(ctx);
                p.PushPopExample1(ctx);
                p.ArrayExample1(ctx);
                p.ArrayExample2(ctx);
                p.ArrayExample3(ctx);
                p.TupleExample(ctx);
                p.BitvectorExample1(ctx);
                p.BitvectorExample2(ctx);
                p.ParserExample1(ctx);
                p.ParserExample2(ctx);
                p.ParserExample3(ctx);
                p.ParserExample4(ctx);
                p.ParserExample5(ctx);
                p.ITEExample(ctx);
                p.EnumExample(ctx);
                p.ListExample(ctx);
                p.TreeExample(ctx);
                p.ForestExample(ctx);
                p.EvalExample1(ctx);
                p.EvalExample2(ctx);
                p.FindSmallModelExample(ctx);
                p.SimplifierExample(ctx);
                p.FiniteDomainExample(ctx);
            }

            p.QuantifierExample3();
            p.QuantifierExample4();
            p.UnsatCoreAndProofExample();

            Log.Close();
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
