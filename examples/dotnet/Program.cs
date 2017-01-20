/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Program.cs

Abstract:

    Z3 Managed API: Example program

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:

--*/

using System;
using System.Collections;
using System.Collections.Generic;

using Microsoft.Z3;

namespace test_mapi
{
    class Program
    {
        class TestFailedException : Exception
        {
            public TestFailedException() : base("Check FAILED") { }
        };

        /// <summary>
        /// Create axiom: function f is injective in the i-th argument.
        /// </summary>
        /// <remarks>
        /// The following axiom is produced:
        /// <c>
        /// forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
        /// </c>
        /// Where, <code>finv</code>is a fresh function declaration.
        /// </summary>
        public static BoolExpr InjAxiom(Context ctx, FuncDecl f, int i)
        {
            Sort[] domain = f.Domain;
            uint sz = f.DomainSize;

            if (i >= sz)
            {
                Console.WriteLine("failed to create inj axiom");
                return null;
            }

            /* declare the i-th inverse of f: finv */
            Sort finv_domain = f.Range;
            Sort finv_range = domain[i];
            FuncDecl finv = ctx.MkFuncDecl("f_fresh", finv_domain, finv_range);

            /* allocate temporary arrays */
            Expr[] xs = new Expr[sz];
            Symbol[] names = new Symbol[sz];
            Sort[] types = new Sort[sz];

            /* fill types, names and xs */

            for (uint j = 0; j < sz; j++)
            {
                types[j] = domain[j];
                names[j] = ctx.MkSymbol(String.Format("x_{0}", j));
                xs[j] = ctx.MkBound(j, types[j]);
            }
            Expr x_i = xs[i];

            /* create f(x_0, ..., x_i, ..., x_{n-1}) */
            Expr fxs = f[xs];

            /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
            Expr finv_fxs = finv[fxs];

            /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
            Expr eq = ctx.MkEq(finv_fxs, x_i);

            /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
            Pattern p = ctx.MkPattern(new Expr[] { fxs });

            /* create & assert quantifier */
            BoolExpr q = ctx.MkForall(
                types, /* types of quantified variables */
                names, /* names of quantified variables */
                eq,
                1,
                new Pattern[] { p } /* patterns */);

            return q;
        }

        /// <summary>
        /// Create axiom: function f is injective in the i-th argument.
        /// </summary>
        /// <remarks>
        /// The following axiom is produced:
        /// <c>
        /// forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
        /// </c>
        /// Where, <code>finv</code>is a fresh function declaration.
        /// </summary>
        public static BoolExpr InjAxiomAbs(Context ctx, FuncDecl f, int i)
        {
            Sort[] domain = f.Domain;
            uint sz = f.DomainSize;

            if (i >= sz)
            {
                Console.WriteLine("failed to create inj axiom");
                return null;
            }

            /* declare the i-th inverse of f: finv */
            Sort finv_domain = f.Range;
            Sort finv_range = domain[i];
            FuncDecl finv = ctx.MkFuncDecl("f_fresh", finv_domain, finv_range);

            /* allocate temporary arrays */
            Expr[] xs = new Expr[sz];

            /* fill types, names and xs */
            for (uint j = 0; j < sz; j++)
            {
                xs[j] = ctx.MkConst(String.Format("x_{0}", j), domain[j]);
            }
            Expr x_i = xs[i];

            /* create f(x_0, ..., x_i, ..., x_{n-1}) */
            Expr fxs = f[xs];

            /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
            Expr finv_fxs = finv[fxs];

            /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
            Expr eq = ctx.MkEq(finv_fxs, x_i);

            /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
            Pattern p = ctx.MkPattern(new Expr[] { fxs });

            /* create & assert quantifier */
            BoolExpr q = ctx.MkForall(
                xs, /* types of quantified variables */
                eq, /* names of quantified variables */
                1,
                new Pattern[] { p } /* patterns */);

            return q;
        }

        /// <summary>
        /// Assert the axiom: function f is commutative.
        /// </summary>
        /// <remarks>
        /// This example uses the SMT-LIB parser to simplify the axiom construction.
        /// </remarks>
        private static BoolExpr CommAxiom(Context ctx, FuncDecl f)
        {
            Sort t = f.Range;
            Sort[] dom = f.Domain;

            if (dom.Length != 2 ||
                !t.Equals(dom[0]) ||
                !t.Equals(dom[1]))
            {
                Console.WriteLine("{0} {1} {2} {3}", dom.Length, dom[0], dom[1], t);
                throw new Exception("function must be binary, and argument types must be equal to return type");
            }

            string bench = string.Format("(benchmark comm :formula (forall (x {0}) (y {1}) (= ({2} x y) ({3} y x))))",
                             t.Name, t.Name, f.Name, f.Name);
            ctx.ParseSMTLIBString(bench, new Symbol[] { t.Name }, new Sort[] { t }, new Symbol[] { f.Name }, new FuncDecl[] { f });
            return ctx.SMTLIBFormulas[0];
        }

        /// <summary>
        /// "Hello world" example: create a Z3 logical context, and delete it.
        /// </summary>
        public static void SimpleExample()
        {
            Console.WriteLine("SimpleExample");

            using (Context ctx = new Context())
            {
                /* do something with the context */

                /* be kind to dispose manually and not wait for the GC. */
                ctx.Dispose();
            }
        }

        static Model Check(Context ctx, BoolExpr f, Status sat)
        {
            Solver s = ctx.MkSolver();
            s.Assert(f);
            if (s.Check() != sat)
                throw new TestFailedException();
            if (sat == Status.SATISFIABLE)
                return s.Model;
            else
                return null;
        }

        static void SolveTactical(Context ctx, Tactic t, Goal g, Status sat)
        {
            Solver s = ctx.MkSolver(t);
            Console.WriteLine("\nTactical solver: " + s);

            foreach (BoolExpr a in g.Formulas)
                s.Assert(a);
            Console.WriteLine("Solver: " + s);

            if (s.Check() != sat)
                throw new TestFailedException();
        }

        static ApplyResult ApplyTactic(Context ctx, Tactic t, Goal g)
        {
            Console.WriteLine("\nGoal: " + g);

            ApplyResult res = t.Apply(g);
            Console.WriteLine("Application result: " + res);

            Status q = Status.UNKNOWN;
            foreach (Goal sg in res.Subgoals)
                if (sg.IsDecidedSat) q = Status.SATISFIABLE;
                else if (sg.IsDecidedUnsat) q = Status.UNSATISFIABLE;

            switch (q)
            {
                case Status.UNKNOWN:
                    Console.WriteLine("Tactic result: Undecided");
                    break;
                case Status.SATISFIABLE:
                    Console.WriteLine("Tactic result: SAT");
                    break;
                case Status.UNSATISFIABLE:
                    Console.WriteLine("Tactic result: UNSAT");
                    break;
            }

            return res;
        }

        static void Prove(Context ctx, BoolExpr f, bool useMBQI = false, params BoolExpr[] assumptions)
        {
            Console.WriteLine("Proving: " + f);
            Solver s = ctx.MkSolver();
            Params p = ctx.MkParams();
            p.Add("mbqi", useMBQI);
            s.Parameters = p;
            foreach (BoolExpr a in assumptions)
                s.Assert(a);
            s.Assert(ctx.MkNot(f));
            Status q = s.Check();

            switch (q)
            {
                case Status.UNKNOWN:
                    Console.WriteLine("Unknown because: " + s.ReasonUnknown);
                    break;
                case Status.SATISFIABLE:
                    throw new TestFailedException();
                case Status.UNSATISFIABLE:
                    Console.WriteLine("OK, proof: " + s.Proof);
                    break;
            }
        }

        static void Disprove(Context ctx, BoolExpr f, bool useMBQI = false, params BoolExpr[] assumptions)
        {
            Console.WriteLine("Disproving: " + f);
            Solver s = ctx.MkSolver();
            Params p = ctx.MkParams();
            p.Add("mbqi", useMBQI);
            s.Parameters = p;
            foreach (BoolExpr a in assumptions)
                s.Assert(a);
            s.Assert(ctx.MkNot(f));
            Status q = s.Check();

            switch (q)
            {
                case Status.UNKNOWN:
                    Console.WriteLine("Unknown because: " + s.ReasonUnknown);
                    break;
                case Status.SATISFIABLE:
                    Console.WriteLine("OK, model: " + s.Model);
                    break;
                case Status.UNSATISFIABLE:
                    throw new TestFailedException();
            }
        }

        static void ModelConverterTest(Context ctx)
        {
            Console.WriteLine("ModelConverterTest");

            ArithExpr xr = (ArithExpr)ctx.MkConst(ctx.MkSymbol("x"), ctx.MkRealSort());
            ArithExpr yr = (ArithExpr)ctx.MkConst(ctx.MkSymbol("y"), ctx.MkRealSort());
            Goal g4 = ctx.MkGoal(true);
            g4.Assert(ctx.MkGt(xr, ctx.MkReal(10, 1)));
            g4.Assert(ctx.MkEq(yr, ctx.MkAdd(xr, ctx.MkReal(1, 1))));
            g4.Assert(ctx.MkGt(yr, ctx.MkReal(1, 1)));

            ApplyResult ar = ApplyTactic(ctx, ctx.MkTactic("simplify"), g4);
            if (ar.NumSubgoals == 1 && (ar.Subgoals[0].IsDecidedSat || ar.Subgoals[0].IsDecidedUnsat))
                throw new TestFailedException();

            ar = ApplyTactic(ctx, ctx.AndThen(ctx.MkTactic("simplify"), ctx.MkTactic("solve-eqs")), g4);
            if (ar.NumSubgoals == 1 && (ar.Subgoals[0].IsDecidedSat || ar.Subgoals[0].IsDecidedUnsat))
                throw new TestFailedException();

            Solver s = ctx.MkSolver();
            foreach (BoolExpr e in ar.Subgoals[0].Formulas)
                s.Assert(e);
            Status q = s.Check();
            Console.WriteLine("Solver says: " + q);
            Console.WriteLine("Model: \n" + s.Model);
            Console.WriteLine("Converted Model: \n" + ar.ConvertModel(0, s.Model));
            if (q != Status.SATISFIABLE)
                throw new TestFailedException();
        }

        /// <summary>
        /// A simple array example.
        /// </summary>
        /// <param name="ctx"></param>
        static void ArrayExample1(Context ctx)
        {
            Console.WriteLine("ArrayExample1");

            Goal g = ctx.MkGoal(true);
            ArraySort asort = ctx.MkArraySort(ctx.IntSort, ctx.MkBitVecSort(32));
            ArrayExpr aex = (ArrayExpr)ctx.MkConst(ctx.MkSymbol("MyArray"), asort);
            Expr sel = ctx.MkSelect(aex, ctx.MkInt(0));
            g.Assert(ctx.MkEq(sel, ctx.MkBV(42, 32)));
            Symbol xs = ctx.MkSymbol("x");
            IntExpr xc = (IntExpr)ctx.MkConst(xs, ctx.IntSort);

            Symbol fname = ctx.MkSymbol("f");
            Sort[] domain = { ctx.IntSort };
            FuncDecl fd = ctx.MkFuncDecl(fname, domain, ctx.IntSort);
            Expr[] fargs = { ctx.MkConst(xs, ctx.IntSort) };
            IntExpr fapp = (IntExpr)ctx.MkApp(fd, fargs);

            g.Assert(ctx.MkEq(ctx.MkAdd(xc, fapp), ctx.MkInt(123)));

            Solver s = ctx.MkSolver();
            foreach (BoolExpr a in g.Formulas)
                s.Assert(a);
            Console.WriteLine("Solver: " + s);

            Status q = s.Check();
            Console.WriteLine("Status: " + q);

            if (q != Status.SATISFIABLE)
                throw new TestFailedException();

            Console.WriteLine("Model = " + s.Model);

            Console.WriteLine("Interpretation of MyArray:\n" + s.Model.FuncInterp(aex.FuncDecl));
            Console.WriteLine("Interpretation of x:\n" + s.Model.ConstInterp(xc));
            Console.WriteLine("Interpretation of f:\n" + s.Model.FuncInterp(fd));
            Console.WriteLine("Interpretation of MyArray as Term:\n" + s.Model.FuncInterp(aex.FuncDecl));
        }

        /// <summary>
        /// Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))</tt>.
        /// </summary>
        /// <remarks>This example demonstrates how to use the array theory.</remarks>
        public static void ArrayExample2(Context ctx)
        {
            Console.WriteLine("ArrayExample2");

            Sort int_type = ctx.IntSort;
            Sort array_type = ctx.MkArraySort(int_type, int_type);

            ArrayExpr a1 = (ArrayExpr)ctx.MkConst("a1", array_type);
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

            /* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) */
            BoolExpr consequent = ctx.MkOr(new BoolExpr[] { ctx.MkEq(i1, i3), ctx.MkEq(i2, i3), ctx.MkEq(sel1, sel2) });

            /* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) */
            BoolExpr thm = ctx.MkImplies(antecedent, consequent);
            Console.WriteLine("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))");
            Console.WriteLine("{0}", (thm));
            Prove(ctx, thm);
        }

        /// <summary>
        /// Show that <code>distinct(a_0, ... , a_n)</code> is
        /// unsatisfiable when <code>a_i</code>'s are arrays from boolean to
        /// boolean and n > 4.
        /// </summary>
        /// <remarks>This example also shows how to use the <code>distinct</code> construct.</remarks>
        public static void ArrayExample3(Context ctx)
        {
            Console.WriteLine("ArrayExample3");

            for (int n = 2; n <= 5; n++)
            {
                Console.WriteLine("n = {0}", n);

                Sort bool_type = ctx.MkBoolSort();
                Sort array_type = ctx.MkArraySort(bool_type, bool_type);
                Expr[] a = new Expr[n];

                /* create arrays */
                for (int i = 0; i < n; i++)
                {
                    a[i] = ctx.MkConst(String.Format("array_{0}", i), array_type);
                }

                /* assert distinct(a[0], ..., a[n]) */
                BoolExpr d = ctx.MkDistinct(a);
                Console.WriteLine("{0}", (d));

                /* context is satisfiable if n < 5 */
                Model model = Check(ctx, d, n < 5 ? Status.SATISFIABLE : Status.UNSATISFIABLE);
                if (n < 5)
                {
                    for (int i = 0; i < n; i++)
                    {
                        Console.WriteLine("{0} = {1}",
                                          a[i],
                                          model.Evaluate(a[i]));
                    }
                }
            }
        }

        /// <summary>
        /// Sudoku solving example.
        /// </summary>
        static void SudokuExample(Context ctx)
        {
            Console.WriteLine("SudokuExample");

            // 9x9 matrix of integer variables
            IntExpr[][] X = new IntExpr[9][];
            for (uint i = 0; i < 9; i++)
            {
                X[i] = new IntExpr[9];
                for (uint j = 0; j < 9; j++)
                    X[i][j] = (IntExpr)ctx.MkConst(ctx.MkSymbol("x_" + (i + 1) + "_" + (j + 1)), ctx.IntSort);
            }

            // each cell contains a value in {1, ..., 9}
            Expr[][] cells_c = new Expr[9][];
            for (uint i = 0; i < 9; i++)
            {
                cells_c[i] = new BoolExpr[9];
                for (uint j = 0; j < 9; j++)
                    cells_c[i][j] = ctx.MkAnd(ctx.MkLe(ctx.MkInt(1), X[i][j]),
                                              ctx.MkLe(X[i][j], ctx.MkInt(9)));
            }

            // each row contains a digit at most once
            BoolExpr[] rows_c = new BoolExpr[9];
            for (uint i = 0; i < 9; i++)
                rows_c[i] = ctx.MkDistinct(X[i]);

            // each column contains a digit at most once
            BoolExpr[] cols_c = new BoolExpr[9];
            for (uint j = 0; j < 9; j++)
            {
                IntExpr[] column = new IntExpr[9];
                for (uint i = 0; i < 9; i++)
                    column[i] = X[i][j];

                cols_c[j] = ctx.MkDistinct(column);
            }

            // each 3x3 square contains a digit at most once
            BoolExpr[][] sq_c = new BoolExpr[3][];
            for (uint i0 = 0; i0 < 3; i0++)
            {
                sq_c[i0] = new BoolExpr[3];
                for (uint j0 = 0; j0 < 3; j0++)
                {
                    IntExpr[] square = new IntExpr[9];
                    for (uint i = 0; i < 3; i++)
                        for (uint j = 0; j < 3; j++)
                            square[3 * i + j] = X[3 * i0 + i][3 * j0 + j];
                    sq_c[i0][j0] = ctx.MkDistinct(square);
                }
            }

            BoolExpr sudoku_c = ctx.MkTrue();
            foreach (BoolExpr[] t in cells_c)
                sudoku_c = ctx.MkAnd(ctx.MkAnd(t), sudoku_c);
            sudoku_c = ctx.MkAnd(ctx.MkAnd(rows_c), sudoku_c);
            sudoku_c = ctx.MkAnd(ctx.MkAnd(cols_c), sudoku_c);
            foreach (BoolExpr[] t in sq_c)
                sudoku_c = ctx.MkAnd(ctx.MkAnd(t), sudoku_c);

            // sudoku instance, we use '0' for empty cells
            int[,] instance = {{0,0,0,0,9,4,0,3,0},
                               {0,0,0,5,1,0,0,0,7},
                               {0,8,9,0,0,0,0,4,0},
                               {0,0,0,0,0,0,2,0,8},
                               {0,6,0,2,0,1,0,5,0},
                               {1,0,2,0,0,0,0,0,0},
                               {0,7,0,0,0,0,5,2,0},
                               {9,0,0,0,6,5,0,0,0},
                               {0,4,0,9,7,0,0,0,0}};

            BoolExpr instance_c = ctx.MkTrue();
            for (uint i = 0; i < 9; i++)
                for (uint j = 0; j < 9; j++)
                    instance_c = ctx.MkAnd(instance_c,
                        (BoolExpr)
                        ctx.MkITE(ctx.MkEq(ctx.MkInt(instance[i, j]), ctx.MkInt(0)),
                                    ctx.MkTrue(),
                                    ctx.MkEq(X[i][j], ctx.MkInt(instance[i, j]))));

            Solver s = ctx.MkSolver();
            s.Assert(sudoku_c);
            s.Assert(instance_c);

            if (s.Check() == Status.SATISFIABLE)
            {
                Model m = s.Model;
                Expr[,] R = new Expr[9, 9];
                for (uint i = 0; i < 9; i++)
                    for (uint j = 0; j < 9; j++)
                        R[i, j] = m.Evaluate(X[i][j]);
                Console.WriteLine("Sudoku solution:");
                for (uint i = 0; i < 9; i++)
                {
                    for (uint j = 0; j < 9; j++)
                        Console.Write(" " + R[i, j]);
                    Console.WriteLine();
                }
            }
            else
            {
                Console.WriteLine("Failed to solve sudoku");
                throw new TestFailedException();
            }
        }

        /// <summary>
        /// A basic example of how to use quantifiers.
        /// </summary>
        static void QuantifierExample1(Context ctx)
        {
            Console.WriteLine("QuantifierExample");

            Sort[] types = new Sort[3];
            IntExpr[] xs = new IntExpr[3];
            Symbol[] names = new Symbol[3];
            IntExpr[] vars = new IntExpr[3];

            for (uint j = 0; j < 3; j++)
            {
                types[j] = ctx.IntSort;
                names[j] = ctx.MkSymbol(String.Format("x_{0}", j));
                xs[j] = (IntExpr)ctx.MkConst(names[j], types[j]);
                vars[j] = (IntExpr)ctx.MkBound(2 - j, types[j]); // <-- vars reversed!
            }

            Expr body_vars = ctx.MkAnd(ctx.MkEq(ctx.MkAdd(vars[0], ctx.MkInt(1)), ctx.MkInt(2)),
                                        ctx.MkEq(ctx.MkAdd(vars[1], ctx.MkInt(2)),
                                                       ctx.MkAdd(vars[2], ctx.MkInt(3))));

            Expr body_const = ctx.MkAnd(ctx.MkEq(ctx.MkAdd(xs[0], ctx.MkInt(1)), ctx.MkInt(2)),
                                        ctx.MkEq(ctx.MkAdd(xs[1], ctx.MkInt(2)),
                                                       ctx.MkAdd(xs[2], ctx.MkInt(3))));

            Expr x = ctx.MkForall(types, names, body_vars, 1, null, null, ctx.MkSymbol("Q1"), ctx.MkSymbol("skid1"));
            Console.WriteLine("Quantifier X: " + x.ToString());

            Expr y = ctx.MkForall(xs, body_const, 1, null, null, ctx.MkSymbol("Q2"), ctx.MkSymbol("skid2"));
            Console.WriteLine("Quantifier Y: " + y.ToString());
        }

        static void QuantifierExample2(Context ctx)
        {

            Console.WriteLine("QuantifierExample2");

            Expr q1, q2;
            FuncDecl f = ctx.MkFuncDecl("f", ctx.IntSort, ctx.IntSort);
            FuncDecl g = ctx.MkFuncDecl("g", ctx.IntSort, ctx.IntSort);

            // Quantifier with Exprs as the bound variables.
            {
                Expr x = ctx.MkConst("x", ctx.IntSort);
                Expr y = ctx.MkConst("y", ctx.IntSort);
                Expr f_x = ctx.MkApp(f, x);
                Expr f_y = ctx.MkApp(f, y);
                Expr g_y = ctx.MkApp(g, y);
                Pattern[] pats = new Pattern[] { ctx.MkPattern(new Expr[] { f_x, g_y }) };
                Expr[] no_pats = new Expr[] { f_y };
                Expr[] bound = new Expr[2] { x, y };
                Expr body = ctx.MkAnd(ctx.MkEq(f_x, f_y), ctx.MkEq(f_y, g_y));

                q1 = ctx.MkForall(bound, body, 1, null, no_pats, ctx.MkSymbol("q"), ctx.MkSymbol("sk"));

                Console.WriteLine("{0}", q1);
            }

            // Quantifier with de-Brujin indices.
            {
                Expr x = ctx.MkBound(1, ctx.IntSort);
                Expr y = ctx.MkBound(0, ctx.IntSort);
                Expr f_x = ctx.MkApp(f, x);
                Expr f_y = ctx.MkApp(f, y);
                Expr g_y = ctx.MkApp(g, y);
                Pattern[] pats = new Pattern[] { ctx.MkPattern(new Expr[] { f_x, g_y }) };
                Expr[] no_pats = new Expr[] { f_y };
                Symbol[] names = new Symbol[] { ctx.MkSymbol("x"), ctx.MkSymbol("y") };
                Sort[] sorts = new Sort[] { ctx.IntSort, ctx.IntSort };
                Expr body = ctx.MkAnd(ctx.MkEq(f_x, f_y), ctx.MkEq(f_y, g_y));

                q2 = ctx.MkForall(sorts, names, body, 1,
                                         null, // pats,
                                         no_pats,
                                         ctx.MkSymbol("q"),
                                         ctx.MkSymbol("sk")
                                        );
                Console.WriteLine("{0}", q2);
            }

            Console.WriteLine("{0}", (q1.Equals(q2)));
        }

        /// <summary>
        /// Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
        /// <code>f</code> is injective in the second argument. <seealso cref="inj_axiom"/>
        /// </summary>
        public static void QuantifierExample3(Context ctx)
        {
            Console.WriteLine("QuantifierExample3");

            /* If quantified formulas are asserted in a logical context, then
               the model produced by Z3 should be viewed as a potential model. */

            /* declare function f */
            Sort I = ctx.IntSort;
            FuncDecl f = ctx.MkFuncDecl("f", new Sort[] { I, I }, I);

            /* f is injective in the second argument. */
            BoolExpr inj = InjAxiom(ctx, f, 1);

            /* create x, y, v, w, fxy, fwv */
            Expr x = ctx.MkIntConst("x");
            Expr y = ctx.MkIntConst("y");
            Expr v = ctx.MkIntConst("v");
            Expr w = ctx.MkIntConst("w");
            Expr fxy = ctx.MkApp(f, x, y);
            Expr fwv = ctx.MkApp(f, w, v);

            /* f(x, y) = f(w, v) */
            BoolExpr p1 = ctx.MkEq(fxy, fwv);

            /* prove f(x, y) = f(w, v) implies y = v */
            BoolExpr p2 = ctx.MkEq(y, v);
            Prove(ctx, p2, false, inj, p1);

            /* disprove f(x, y) = f(w, v) implies x = w */
            BoolExpr p3 = ctx.MkEq(x, w);
            Disprove(ctx, p3, false, inj, p1);
        }

        /// <summary>
        /// Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
        /// <code>f</code> is injective in the second argument. <seealso cref="inj_axiom"/>
        /// </summary>
        public static void QuantifierExample4(Context ctx)
        {
            Console.WriteLine("QuantifierExample4");

            /* If quantified formulas are asserted in a logical context, then
               the model produced by Z3 should be viewed as a potential model. */

            /* declare function f */
            Sort I = ctx.IntSort;
            FuncDecl f = ctx.MkFuncDecl("f", new Sort[] { I, I }, I);

            /* f is injective in the second argument. */
            BoolExpr inj = InjAxiomAbs(ctx, f, 1);

            /* create x, y, v, w, fxy, fwv */
            Expr x = ctx.MkIntConst("x");
            Expr y = ctx.MkIntConst("y");
            Expr v = ctx.MkIntConst("v");
            Expr w = ctx.MkIntConst("w");
            Expr fxy = ctx.MkApp(f, x, y);
            Expr fwv = ctx.MkApp(f, w, v);

            /* f(x, y) = f(w, v) */
            BoolExpr p1 = ctx.MkEq(fxy, fwv);

            /* prove f(x, y) = f(w, v) implies y = v */
            BoolExpr p2 = ctx.MkEq(y, v);
            Prove(ctx, p2, false, inj, p1);

            /* disprove f(x, y) = f(w, v) implies x = w */
            BoolExpr p3 = ctx.MkEq(x, w);
            Disprove(ctx, p3, false, inj, p1);
        }

        /// <summary>
        /// Some basic tests.
        /// </summary>
        static void BasicTests(Context ctx)
        {
            Console.WriteLine("BasicTests");

            Symbol qi = ctx.MkSymbol(1);
            Symbol fname = ctx.MkSymbol("f");
            Symbol x = ctx.MkSymbol("x");
            Symbol y = ctx.MkSymbol("y");

            Sort bs = ctx.MkBoolSort();

            Sort[] domain = { bs, bs };
            FuncDecl f = ctx.MkFuncDecl(fname, domain, bs);
            Expr fapp = ctx.MkApp(f, ctx.MkConst(x, bs), ctx.MkConst(y, bs));

            Expr[] fargs2 = { ctx.MkFreshConst("cp", bs) };
            Sort[] domain2 = { bs };
            Expr fapp2 = ctx.MkApp(ctx.MkFreshFuncDecl("fp", domain2, bs), fargs2);

            BoolExpr trivial_eq = ctx.MkEq(fapp, fapp);
            BoolExpr nontrivial_eq = ctx.MkEq(fapp, fapp2);

            Goal g = ctx.MkGoal(true);
            g.Assert(trivial_eq);
            g.Assert(nontrivial_eq);
            Console.WriteLine("Goal: " + g);

            Solver solver = ctx.MkSolver();

            foreach (BoolExpr a in g.Formulas)
                solver.Assert(a);

            if (solver.Check() != Status.SATISFIABLE)
                throw new TestFailedException();

            ApplyResult ar = ApplyTactic(ctx, ctx.MkTactic("simplify"), g);
            if (ar.NumSubgoals == 1 && (ar.Subgoals[0].IsDecidedSat || ar.Subgoals[0].IsDecidedUnsat))
                throw new TestFailedException();

            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedSat)
                throw new TestFailedException();

            g.Assert(ctx.MkEq(ctx.MkNumeral(1, ctx.MkBitVecSort(32)),
                                      ctx.MkNumeral(2, ctx.MkBitVecSort(32))));
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedUnsat)
                throw new TestFailedException();


            Goal g2 = ctx.MkGoal(true, true);
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g2);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedSat)
                throw new TestFailedException();

            g2 = ctx.MkGoal(true, true);
            g2.Assert(ctx.MkFalse());
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g2);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedUnsat)
                throw new TestFailedException();

            Goal g3 = ctx.MkGoal(true, true);
            Expr xc = ctx.MkConst(ctx.MkSymbol("x"), ctx.IntSort);
            Expr yc = ctx.MkConst(ctx.MkSymbol("y"), ctx.IntSort);
            g3.Assert(ctx.MkEq(xc, ctx.MkNumeral(1, ctx.IntSort)));
            g3.Assert(ctx.MkEq(yc, ctx.MkNumeral(2, ctx.IntSort)));
            BoolExpr constr = ctx.MkEq(xc, yc);
            g3.Assert(constr);
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g3);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedUnsat)
                throw new TestFailedException();

            ModelConverterTest(ctx);

            // Real num/den test.
            RatNum rn = ctx.MkReal(42, 43);
            Expr inum = rn.Numerator;
            Expr iden = rn.Denominator;
            Console.WriteLine("Numerator: " + inum + " Denominator: " + iden);
            if (inum.ToString() != "42" || iden.ToString() != "43")
                throw new TestFailedException();

            if (rn.ToDecimalString(3) != "0.976?")
                throw new TestFailedException();

            BigIntCheck(ctx, ctx.MkReal("-1231231232/234234333"));
            BigIntCheck(ctx, ctx.MkReal("-123123234234234234231232/234234333"));
            BigIntCheck(ctx, ctx.MkReal("-234234333"));
            BigIntCheck(ctx, ctx.MkReal("234234333/2"));


#if !FRAMEWORK_LT_4
            string bn = "1234567890987654321";

            if (ctx.MkInt(bn).BigInteger.ToString() != bn)
                throw new TestFailedException();

            if (ctx.MkBV(bn, 128).BigInteger.ToString() != bn)
                throw new TestFailedException();

            if (ctx.MkBV(bn, 32).BigInteger.ToString() == bn)
                throw new TestFailedException();
#endif

            // Error handling test.
            try
            {
                IntExpr i = ctx.MkInt("1/2");
                throw new TestFailedException(); // unreachable
            }
            catch (Z3Exception)
            {
            }
        }

        /// <summary>
        /// Some basic expression casting tests.
        /// </summary>
        static void CastingTest(Context ctx)
        {
            Console.WriteLine("CastingTest");

            Sort[] domain = { ctx.BoolSort, ctx.BoolSort };
            FuncDecl f = ctx.MkFuncDecl("f", domain, ctx.BoolSort);

            AST upcast = ctx.MkFuncDecl(ctx.MkSymbol("q"), domain, ctx.BoolSort);

            try
            {
                FuncDecl downcast = (FuncDecl)f; // OK
            }
            catch (InvalidCastException)
            {
                throw new TestFailedException();
            }

            try
            {
                Expr uc = (Expr)upcast;
                throw new TestFailedException(); // should not be reachable!
            }
            catch (InvalidCastException)
            {
            }

            Symbol s = ctx.MkSymbol(42);
            IntSymbol si = s as IntSymbol;
            if (si == null) throw new TestFailedException();
            try
            {
                IntSymbol si2 = (IntSymbol)s;
            }
            catch (InvalidCastException)
            {
                throw new TestFailedException();
            }

            s = ctx.MkSymbol("abc");
            StringSymbol ss = s as StringSymbol;
            if (ss == null) throw new TestFailedException();
            try
            {
                StringSymbol ss2 = (StringSymbol)s;
            }
            catch (InvalidCastException)
            {
                throw new TestFailedException();
            }
            try
            {
                IntSymbol si2 = (IntSymbol)s;
                throw new TestFailedException(); // unreachable
            }
            catch
            {
            }

            Sort srt = ctx.MkBitVecSort(32);
            BitVecSort bvs = null;
            try
            {
                bvs = (BitVecSort)srt;
            }
            catch (InvalidCastException)
            {
                throw new TestFailedException();
            }

            if (bvs.Size != 32)
                throw new TestFailedException();

            Expr q = ctx.MkAdd(ctx.MkInt(1), ctx.MkInt(2));
            Expr q2 = q.Args[1];
            Sort qs = q2.Sort;
            if (qs as IntSort == null)
                throw new TestFailedException();
            try
            {
                IntSort isrt = (IntSort)qs;
            }
            catch (InvalidCastException)
            {
                throw new TestFailedException();
            }

            AST a = ctx.MkInt(42);
            Expr ae = a as Expr;
            if (ae == null) throw new TestFailedException();
            ArithExpr aae = a as ArithExpr;
            if (aae == null) throw new TestFailedException();
            IntExpr aie = a as IntExpr;
            if (aie == null) throw new TestFailedException();
            IntNum ain = a as IntNum;
            if (ain == null) throw new TestFailedException();


            Expr[][] earr = new Expr[2][];
            earr[0] = new Expr[2];
            earr[1] = new Expr[2];
            earr[0][0] = ctx.MkTrue();
            earr[0][1] = ctx.MkTrue();
            earr[1][0] = ctx.MkFalse();
            earr[1][1] = ctx.MkFalse();
            foreach (Expr[] ea in earr)
                foreach (Expr e in ea)
                {
                    try
                    {
                        Expr ns = ctx.MkNot((BoolExpr)e);
                        BoolExpr ens = (BoolExpr)ns;
                    }
                    catch (InvalidCastException)
                    {
                        throw new TestFailedException();
                    }
                }
        }

        /// <summary>
        /// Shows how to read an SMT1 file.
        /// </summary>
        static void SMT1FileTest(string filename)
        {
            Console.Write("SMT File test ");

            using (Context ctx = new Context(new Dictionary<string, string>() { { "MODEL", "true" } }))
            {
                ctx.ParseSMTLIBFile(filename);

                BoolExpr a = ctx.MkAnd(ctx.SMTLIBFormulas);
                Console.WriteLine("read formula: " + a);
            }
        }

        /// <summary>
        /// Shows how to read an SMT2 file.
        /// </summary>
        static void SMT2FileTest(string filename)
        {
            System.DateTime before = System.DateTime.Now;

            Console.WriteLine("SMT2 File test ");
            System.GC.Collect();

            using (Context ctx = new Context(new Dictionary<string, string>() { { "MODEL", "true" } }))
            {
                Expr a = ctx.ParseSMTLIB2File(filename);

                Console.WriteLine("SMT2 file read time: " + (System.DateTime.Now - before).TotalSeconds + " sec");

                // Iterate over the formula.

                Queue q = new Queue();
                q.Enqueue(a);
                uint cnt = 0;
                while (q.Count > 0)
                {
                    AST cur = (AST)q.Dequeue();
                    cnt++;

                    // This here ...
                    if (cur is Expr)
                        if (!(cur.IsVar))
                            foreach (Expr c in ((Expr)cur).Args)
                                q.Enqueue(c);

                    // Takes the same time as this:
                    //switch ((cur).ASTKind)
                    //{
                    //    case Z3_ast_kind.Z3_APP_AST:
                    //        foreach (Expr e in ((Expr)cur).Args)
                    //            q.Enqueue(e);
                    //        break;
                    //    case Z3_ast_kind.Z3_QUANTIFIER_AST:
                    //        q.Enqueue(((Quantifier)cur).Args[0]);
                    //        break;
                    //    case Z3_ast_kind.Z3_VAR_AST: break;
                    //    case Z3_ast_kind.Z3_NUMERAL_AST: break;
                    //    case Z3_ast_kind.Z3_FUNC_DECL_AST: break;
                    //    case Z3_ast_kind.Z3_SORT_AST: break;
                    //}
                }
                Console.WriteLine(cnt + " ASTs");
            }

            Console.WriteLine("SMT2 file test took " + (System.DateTime.Now - before).TotalSeconds + " sec");
        }

        /// <summary>
        /// Shows how to use Solver(logic)
        /// </summary>
        /// <param name="ctx"></param>
        static void LogicExample(Context ctx)
        {
            Console.WriteLine("LogicTest");

            Microsoft.Z3.Global.ToggleWarningMessages(true);

            BitVecSort bvs = ctx.MkBitVecSort(32);
            Expr x = ctx.MkConst("x", bvs);
            Expr y = ctx.MkConst("y", bvs);
            BoolExpr eq = ctx.MkEq(x, y);

            // Use a solver for QF_BV
            Solver s = ctx.MkSolver("QF_BV");
            s.Assert(eq);
            Status res = s.Check();
            Console.WriteLine("solver result: " + res);


            // Or perhaps a tactic for QF_BV
            Goal g = ctx.MkGoal(true);
            g.Assert(eq);

            Tactic t = ctx.MkTactic("qfbv");
            ApplyResult ar = t.Apply(g);
            Console.WriteLine("tactic result: " + ar);

            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedSat)
                throw new TestFailedException();
        }

        /// <summary>
        /// Demonstrates how to use the ParOr tactic.
        /// </summary>
        static void ParOrExample(Context ctx)
        {
            Console.WriteLine("ParOrExample");

            BitVecSort bvs = ctx.MkBitVecSort(32);
            Expr x = ctx.MkConst("x", bvs);
            Expr y = ctx.MkConst("y", bvs);
            BoolExpr q = ctx.MkEq(x, y);

            Goal g = ctx.MkGoal(true);
            g.Assert(q);

            Tactic t1 = ctx.MkTactic("qfbv");
            Tactic t2 = ctx.MkTactic("qfbv");
            Tactic p = ctx.ParOr(t1, t2);

            ApplyResult ar = p.Apply(g);

            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedSat)
                throw new TestFailedException();
        }

        static void BigIntCheck(Context ctx, RatNum r)
        {
#if !FRAMEWORK_LT_4
            Console.WriteLine("Num: " + r.BigIntNumerator);
            Console.WriteLine("Den: " + r.BigIntDenominator);
#endif
        }

        /// <summary>
        /// Find a model for <code>x xor y</code>.
        /// </summary>
        public static void FindModelExample1(Context ctx)
        {
            Console.WriteLine("FindModelExample1");

            BoolExpr x = ctx.MkBoolConst("x");
            BoolExpr y = ctx.MkBoolConst("y");
            BoolExpr x_xor_y = ctx.MkXor(x, y);

            Model model = Check(ctx, x_xor_y, Status.SATISFIABLE);
            Console.WriteLine("x = {0}, y = {1}",
                              model.Evaluate(x),
                              model.Evaluate(y));
        }

        /// <summary>
        /// Find a model for <tt>x < y + 1, x > 2</tt>.
        /// Then, assert <tt>not(x = y)</tt>, and find another model.
        /// </summary>
        public static void FindModelExample2(Context ctx)
        {
            Console.WriteLine("FindModelExample2");

            IntExpr x = ctx.MkIntConst("x");
            IntExpr y = ctx.MkIntConst("y");
            IntExpr one = ctx.MkInt(1);
            IntExpr two = ctx.MkInt(2);

            ArithExpr y_plus_one = ctx.MkAdd(y, one);

            BoolExpr c1 = ctx.MkLt(x, y_plus_one);
            BoolExpr c2 = ctx.MkGt(x, two);

            BoolExpr q = ctx.MkAnd(c1, c2);

            Console.WriteLine("model for: x < y + 1, x > 2");
            Model model = Check(ctx, q, Status.SATISFIABLE);
            Console.WriteLine("x = {0}, y = {1}",
                              (model.Evaluate(x)),
                              (model.Evaluate(y)));

            /* assert not(x = y) */
            BoolExpr x_eq_y = ctx.MkEq(x, y);
            BoolExpr c3 = ctx.MkNot(x_eq_y);

            q = ctx.MkAnd(q, c3);

            Console.WriteLine("model for: x < y + 1, x > 2, not(x = y)");
            model = Check(ctx, q, Status.SATISFIABLE);
            Console.WriteLine("x = {0}, y = {1}",
                              (model.Evaluate(x)),
                              (model.Evaluate(y)));
        }

        /// <summary>
        /// Prove <tt>x = y implies g(x) = g(y)</tt>, and
        /// disprove <tt>x = y implies g(g(x)) = g(y)</tt>.
        /// </summary>
        /// <remarks>This function demonstrates how to create uninterpreted
        /// types and functions.</remarks>
        public static void ProveExample1(Context ctx)
        {
            Console.WriteLine("ProveExample1");

            /* create uninterpreted type. */
            Sort U = ctx.MkUninterpretedSort(ctx.MkSymbol("U"));

            /* declare function g */
            FuncDecl g = ctx.MkFuncDecl("g", U, U);

            /* create x and y */
            Expr x = ctx.MkConst("x", U);
            Expr y = ctx.MkConst("y", U);
            /* create g(x), g(y) */
            Expr gx = g[x];
            Expr gy = g[y];

            /* assert x = y */
            BoolExpr eq = ctx.MkEq(x, y);

            /* prove g(x) = g(y) */
            BoolExpr f = ctx.MkEq(gx, gy);
            Console.WriteLine("prove: x = y implies g(x) = g(y)");
            Prove(ctx, ctx.MkImplies(eq, f));

            /* create g(g(x)) */
            Expr ggx = g[gx];

            /* disprove g(g(x)) = g(y) */
            f = ctx.MkEq(ggx, gy);
            Console.WriteLine("disprove: x = y implies g(g(x)) = g(y)");
            Disprove(ctx, ctx.MkImplies(eq, f));


            /* Print the model using the custom model printer */
            Model m = Check(ctx, ctx.MkNot(f), Status.SATISFIABLE);
            Console.WriteLine(m);
        }

        /// <summary>
        /// Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0 </tt>.
        /// Then, show that <tt>z < -1</tt> is not implied.
        /// </summary>
        /// <remarks>This example demonstrates how to combine uninterpreted functions
        /// and arithmetic.</remarks>
        public static void ProveExample2(Context ctx)
        {
            Console.WriteLine("ProveExample2");

            /* declare function g */
            Sort I = ctx.IntSort;

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
            ArithExpr gx_gy = ctx.MkSub((IntExpr)gx, (IntExpr)gy);
            Expr ggx_gy = ctx.MkApp(g, gx_gy);
            BoolExpr eq = ctx.MkEq(ggx_gy, gz);
            BoolExpr c1 = ctx.MkNot(eq);

            /* assert x + z <= y */
            ArithExpr x_plus_z = ctx.MkAdd(x, z);
            BoolExpr c2 = ctx.MkLe(x_plus_z, y);

            /* assert y <= x */
            BoolExpr c3 = ctx.MkLe(y, x);

            /* prove z < 0 */
            BoolExpr f = ctx.MkLt(z, zero);
            Console.WriteLine("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0");
            Prove(ctx, f, false, c1, c2, c3);

            /* disprove z < -1 */
            IntExpr minus_one = ctx.MkInt(-1);
            f = ctx.MkLt(z, minus_one);
            Console.WriteLine("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1");
            Disprove(ctx, f, false, c1, c2, c3);
        }

        /// <summary>
        /// Show how push & pop can be used to create "backtracking" points.
        /// </summary>
        /// <remarks>This example also demonstrates how big numbers can be
        /// created in ctx.</remarks>
        public static void PushPopExample1(Context ctx)
        {
            Console.WriteLine("PushPopExample1");

            /* create a big number */
            IntSort int_type = ctx.IntSort;
            IntExpr big_number = ctx.MkInt("1000000000000000000000000000000000000000000000000000000");

            /* create number 3 */
            IntExpr three = (IntExpr)ctx.MkNumeral("3", int_type);

            /* create x */
            IntExpr x = ctx.MkIntConst("x");

            Solver solver = ctx.MkSolver();

            /* assert x >= "big number" */
            BoolExpr c1 = ctx.MkGe(x, big_number);
            Console.WriteLine("assert: x >= 'big number'");
            solver.Assert(c1);

            /* create a backtracking point */
            Console.WriteLine("push");
            solver.Push();

            /* assert x <= 3 */
            BoolExpr c2 = ctx.MkLe(x, three);
            Console.WriteLine("assert: x <= 3");
            solver.Assert(c2);

            /* context is inconsistent at this point */
            if (solver.Check() != Status.UNSATISFIABLE)
                throw new TestFailedException();

            /* backtrack: the constraint x <= 3 will be removed, since it was
               asserted after the last ctx.Push. */
            Console.WriteLine("pop");
            solver.Pop(1);

            /* the context is consistent again. */
            if (solver.Check() != Status.SATISFIABLE)
                throw new TestFailedException();

            /* new constraints can be asserted... */

            /* create y */
            IntExpr y = ctx.MkIntConst("y");

            /* assert y > x */
            BoolExpr c3 = ctx.MkGt(y, x);
            Console.WriteLine("assert: y > x");
            solver.Assert(c3);

            /* the context is still consistent. */
            if (solver.Check() != Status.SATISFIABLE)
                throw new TestFailedException();
        }

        /// <summary>
        /// Tuples.
        /// </summary>
        /// <remarks>Check that the projection of a tuple
        /// returns the corresponding element.</remarks>
        public static void TupleExample(Context ctx)
        {
            Console.WriteLine("TupleExample");

            Sort int_type = ctx.IntSort;
            TupleSort tuple = ctx.MkTupleSort(
             ctx.MkSymbol("mk_tuple"),         // name of tuple constructor
             new Symbol[] { ctx.MkSymbol("first"), ctx.MkSymbol("second") },  // names of projection operators
             new Sort[] { int_type, int_type } // types of projection operators
                );
            FuncDecl first = tuple.FieldDecls[0];  // declarations are for projections
            FuncDecl second = tuple.FieldDecls[1];
            Expr x = ctx.MkConst("x", int_type);
            Expr y = ctx.MkConst("y", int_type);
            Expr n1 = tuple.MkDecl[x, y];
            Expr n2 = first[n1];
            BoolExpr n3 = ctx.MkEq(x, n2);
            Console.WriteLine("Tuple example: {0}", n3);
            Prove(ctx, n3);
        }

        /// <summary>
        /// Simple bit-vector example.
        /// </summary>
        /// <remarks>
        /// This example disproves that x - 10 &lt;= 0 IFF x &lt;= 10 for (32-bit) machine integers
        /// </remarks>
        public static void BitvectorExample1(Context ctx)
        {
            Console.WriteLine("BitvectorExample1");

            Sort bv_type = ctx.MkBitVecSort(32);
            BitVecExpr x = (BitVecExpr)ctx.MkConst("x", bv_type);
            BitVecNum zero = (BitVecNum)ctx.MkNumeral("0", bv_type);
            BitVecNum ten = ctx.MkBV(10, 32);
            BitVecExpr x_minus_ten = ctx.MkBVSub(x, ten);
            /* bvsle is signed less than or equal to */
            BoolExpr c1 = ctx.MkBVSLE(x, ten);
            BoolExpr c2 = ctx.MkBVSLE(x_minus_ten, zero);
            BoolExpr thm = ctx.MkIff(c1, c2);
            Console.WriteLine("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers");
            Disprove(ctx, thm);
        }

        /// <summary>
        /// Find x and y such that: x ^ y - 103 == x * y
        /// </summary>
        public static void BitvectorExample2(Context ctx)
        {
            Console.WriteLine("BitvectorExample2");

            /* construct x ^ y - 103 == x * y */
            Sort bv_type = ctx.MkBitVecSort(32);
            BitVecExpr x = ctx.MkBVConst("x", 32);
            BitVecExpr y = ctx.MkBVConst("y", 32);
            BitVecExpr x_xor_y = ctx.MkBVXOR(x, y);
            BitVecExpr c103 = (BitVecNum)ctx.MkNumeral("103", bv_type);
            BitVecExpr lhs = ctx.MkBVSub(x_xor_y, c103);
            BitVecExpr rhs = ctx.MkBVMul(x, y);
            BoolExpr ctr = ctx.MkEq(lhs, rhs);

            Console.WriteLine("find values of x and y, such that x ^ y - 103 == x * y");

            /* find a model (i.e., values for x an y that satisfy the constraint */
            Model m = Check(ctx, ctr, Status.SATISFIABLE);
            Console.WriteLine(m);
        }

        /// <summary>
        /// Demonstrates how to use the SMTLIB parser.
        /// </summary>
        public static void ParserExample1(Context ctx)
        {
            Console.WriteLine("ParserExample1");

            ctx.ParseSMTLIBString("(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))");
            foreach (BoolExpr f in ctx.SMTLIBFormulas)
                Console.WriteLine("formula {0}", f);

            Model m = Check(ctx, ctx.MkAnd(ctx.SMTLIBFormulas), Status.SATISFIABLE);
        }

        /// <summary>
        /// Demonstrates how to initialize the parser symbol table.
        /// </summary>
        public static void ParserExample2(Context ctx)
        {
            Console.WriteLine("ParserExample2");

            Symbol[] declNames = { ctx.MkSymbol("a"), ctx.MkSymbol("b") };
            FuncDecl a = ctx.MkConstDecl(declNames[0], ctx.MkIntSort());
            FuncDecl b = ctx.MkConstDecl(declNames[1], ctx.MkIntSort());
            FuncDecl[] decls = new FuncDecl[] { a, b };

            ctx.ParseSMTLIBString("(benchmark tst :formula (> a b))",
                                 null, null, declNames, decls);
            BoolExpr f = ctx.SMTLIBFormulas[0];
            Console.WriteLine("formula: {0}", f);
            Check(ctx, f, Status.SATISFIABLE);
        }

        /// <summary>
        /// Demonstrates how to initialize the parser symbol table.
        /// </summary>
        public static void ParserExample3(Context ctx)
        {
            Console.WriteLine("ParserExample3");

            /* declare function g */
            Sort I = ctx.MkIntSort();
            FuncDecl g = ctx.MkFuncDecl("g", new Sort[] { I, I }, I);

            BoolExpr ca = CommAxiom(ctx, g);

            ctx.ParseSMTLIBString("(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (gg x 0) (gg 0 y)))))",
             null, null,
             new Symbol[] { ctx.MkSymbol("gg") },
             new FuncDecl[] { g });

            BoolExpr thm = ctx.SMTLIBFormulas[0];
            Console.WriteLine("formula: {0}", thm);
            Prove(ctx, thm, false, ca);
        }

        /// <summary>
        /// Display the declarations, assumptions and formulas in a SMT-LIB string.
        /// </summary>
        public static void ParserExample4(Context ctx)
        {
            Console.WriteLine("ParserExample4");

            ctx.ParseSMTLIBString
            ("(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))");
            foreach (var decl in ctx.SMTLIBDecls)
            {
                Console.WriteLine("Declaration: {0}", decl);
            }
            foreach (var f in ctx.SMTLIBAssumptions)
            {
                Console.WriteLine("Assumption: {0}", f);
            }
            foreach (var f in ctx.SMTLIBFormulas)
            {
                Console.WriteLine("Formula: {0}", f);
            }
        }

        /// <summary>
        /// Demonstrates how to handle parser errors using Z3 error handling support.
        /// </summary>
        /// <remarks></remarks>
        public static void ParserExample5(Context ctx)
        {
            Console.WriteLine("ParserExample5");

            try
            {
                ctx.ParseSMTLIBString(
                    /* the following string has a parsing error: missing parenthesis */
                         "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))");
            }
            catch (Z3Exception e)
            {
                Console.WriteLine("Z3 error: {0}", e);
            }
        }

        /// <summary>
        /// Create an ite-Expr (if-then-else Exprs).
        /// </summary>
        public static void ITEExample(Context ctx)
        {
            Console.WriteLine("ITEExample");

            BoolExpr f = ctx.MkFalse();
            Expr one = ctx.MkInt(1);
            Expr zero = ctx.MkInt(0);
            Expr ite = ctx.MkITE(f, one, zero);

            Console.WriteLine("Expr: {0}", ite);
        }

        /// <summary>
        /// Create an enumeration data type.
        /// </summary>
        public static void EnumExample(Context ctx)
        {
            Console.WriteLine("EnumExample");

            Symbol name = ctx.MkSymbol("fruit");

            EnumSort fruit = ctx.MkEnumSort(ctx.MkSymbol("fruit"), new Symbol[] { ctx.MkSymbol("apple"), ctx.MkSymbol("banana"), ctx.MkSymbol("orange") });

            Console.WriteLine("{0}", (fruit.Consts[0]));
            Console.WriteLine("{0}", (fruit.Consts[1]));
            Console.WriteLine("{0}", (fruit.Consts[2]));

            Console.WriteLine("{0}", (fruit.TesterDecls[0]));
            Console.WriteLine("{0}", (fruit.TesterDecls[1]));
            Console.WriteLine("{0}", (fruit.TesterDecls[2]));

            Expr apple = fruit.Consts[0];
            Expr banana = fruit.Consts[1];
            Expr orange = fruit.Consts[2];

            /* Apples are different from oranges */
            Prove(ctx, ctx.MkNot(ctx.MkEq(apple, orange)));

            /* Apples pass the apple test */
            Prove(ctx, (BoolExpr)ctx.MkApp(fruit.TesterDecls[0], apple));

            /* Oranges fail the apple test */
            Disprove(ctx, (BoolExpr)ctx.MkApp(fruit.TesterDecls[0], orange));
            Prove(ctx, (BoolExpr)ctx.MkNot((BoolExpr)ctx.MkApp(fruit.TesterDecls[0], orange)));

            Expr fruity = ctx.MkConst("fruity", fruit);

            /* If something is fruity, then it is an apple, banana, or orange */

            Prove(ctx, ctx.MkOr(new BoolExpr[] { ctx.MkEq(fruity, apple), ctx.MkEq(fruity, banana), ctx.MkEq(fruity, orange) }));
        }

        /// <summary>
        /// Create a list datatype.
        /// </summary>
        public static void ListExample(Context ctx)
        {
            Console.WriteLine("ListExample");

            Sort int_ty;
            ListSort int_list;
            Expr nil, l1, l2, x, y, u, v;
            BoolExpr fml, fml1;

            int_ty = ctx.MkIntSort();

            int_list = ctx.MkListSort(ctx.MkSymbol("int_list"), int_ty);

            nil = ctx.MkConst(int_list.NilDecl);
            l1 = ctx.MkApp(int_list.ConsDecl, ctx.MkInt(1), nil);
            l2 = ctx.MkApp(int_list.ConsDecl, ctx.MkInt(2), nil);

            /* nil != cons(1, nil) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(nil, l1)));

            /* cons(2,nil) != cons(1, nil) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(l1, l2)));

            /* cons(x,nil) = cons(y, nil) => x = y */
            x = ctx.MkConst("x", int_ty);
            y = ctx.MkConst("y", int_ty);
            l1 = ctx.MkApp(int_list.ConsDecl, x, nil);
            l2 = ctx.MkApp(int_list.ConsDecl, y, nil);
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

            /* cons(x,u) = cons(x, v) => u = v */
            u = ctx.MkConst("u", int_list);
            v = ctx.MkConst("v", int_list);
            l1 = ctx.MkApp(int_list.ConsDecl, x, u);
            l2 = ctx.MkApp(int_list.ConsDecl, y, v);
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(u, v)));
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

            /* is_nil(u) or is_cons(u) */
            Prove(ctx, ctx.MkOr((BoolExpr)ctx.MkApp(int_list.IsNilDecl, u),
                           (BoolExpr)ctx.MkApp(int_list.IsConsDecl, u)));

            /* occurs check u != cons(x,u) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(u, l1)));

            /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
            fml1 = ctx.MkEq(u, ctx.MkApp(int_list.ConsDecl, ctx.MkApp(int_list.HeadDecl, u),
                              ctx.MkApp(int_list.TailDecl, u)));
            fml = ctx.MkImplies((BoolExpr)ctx.MkApp(int_list.IsConsDecl, u), fml1);
            Console.WriteLine("Formula {0}", fml);

            Prove(ctx, fml);

            Disprove(ctx, fml1);
        }

        /// <summary>
        /// Create a binary tree datatype.
        /// </summary>
        public static void TreeExample(Context ctx)
        {
            Console.WriteLine("TreeExample");

            Sort cell;
            FuncDecl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
            Expr nil, l1, l2, x, y, u, v;
            BoolExpr fml, fml1;
            string[] head_tail = new string[] { "car", "cdr" };
            Sort[] sorts = new Sort[] { null, null };
            uint[] sort_refs = new uint[] { 0, 0 };
            Constructor nil_con, cons_con;

            nil_con = ctx.MkConstructor("nil", "is_nil", null, null, null);
            cons_con = ctx.MkConstructor("cons", "is_cons", head_tail, sorts, sort_refs);
            Constructor[] constructors = new Constructor[] { nil_con, cons_con };

            cell = ctx.MkDatatypeSort("cell", constructors);

            nil_decl = nil_con.ConstructorDecl;
            is_nil_decl = nil_con.TesterDecl;
            cons_decl = cons_con.ConstructorDecl;
            is_cons_decl = cons_con.TesterDecl;
            FuncDecl[] cons_accessors = cons_con.AccessorDecls;
            car_decl = cons_accessors[0];
            cdr_decl = cons_accessors[1];

            nil = ctx.MkConst(nil_decl);
            l1 = ctx.MkApp(cons_decl, nil, nil);
            l2 = ctx.MkApp(cons_decl, l1, nil);

            /* nil != cons(nil, nil) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(nil, l1)));

            /* cons(x,u) = cons(x, v) => u = v */
            u = ctx.MkConst("u", cell);
            v = ctx.MkConst("v", cell);
            x = ctx.MkConst("x", cell);
            y = ctx.MkConst("y", cell);
            l1 = ctx.MkApp(cons_decl, x, u);
            l2 = ctx.MkApp(cons_decl, y, v);
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(u, v)));
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

            /* is_nil(u) or is_cons(u) */
            Prove(ctx, ctx.MkOr((BoolExpr)ctx.MkApp(is_nil_decl, u), (BoolExpr)ctx.MkApp(is_cons_decl, u)));

            /* occurs check u != cons(x,u) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(u, l1)));

            /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
            fml1 = ctx.MkEq(u, ctx.MkApp(cons_decl, ctx.MkApp(car_decl, u), ctx.MkApp(cdr_decl, u)));
            fml = ctx.MkImplies((BoolExpr)ctx.MkApp(is_cons_decl, u), fml1);
            Console.WriteLine("Formula {0}", fml);
            Prove(ctx, fml);

            Disprove(ctx, fml1);
        }

        /// <summary>
        /// Create a forest of trees.
        /// </summary>
        /// <remarks>
        /// forest ::= nil | cons(tree, forest)
        /// tree   ::= nil | cons(forest, forest)
        /// </remarks>
        public static void ForestExample(Context ctx)
        {
            Console.WriteLine("ForestExample");

            Sort tree, forest;
            FuncDecl nil1_decl, is_nil1_decl, cons1_decl, is_cons1_decl, car1_decl, cdr1_decl;
            FuncDecl nil2_decl, is_nil2_decl, cons2_decl, is_cons2_decl, car2_decl, cdr2_decl;
            Expr nil1, nil2, t1, t2, t3, t4, f1, f2, f3, l1, l2, x, y, u, v;

            //
            // Declare the names of the accessors for cons.
            // Then declare the sorts of the accessors.
            // For this example, all sorts refer to the new types 'forest' and 'tree'
            // being declared, so we pass in null for both sorts1 and sorts2.
            // On the other hand, the sort_refs arrays contain the indices of the
            // two new sorts being declared. The first element in sort1_refs
            // points to 'tree', which has index 1, the second element in sort1_refs array
            // points to 'forest', which has index 0.
            //
            Symbol[] head_tail1 = new Symbol[] { ctx.MkSymbol("head"), ctx.MkSymbol("tail") };
            Sort[] sorts1 = new Sort[] { null, null };
            uint[] sort1_refs = new uint[] { 1, 0 }; // the first item points to a tree, the second to a forest

            Symbol[] head_tail2 = new Symbol[] { ctx.MkSymbol("car"), ctx.MkSymbol("cdr") };
            Sort[] sorts2 = new Sort[] { null, null };
            uint[] sort2_refs = new uint[] { 0, 0 }; // both items point to the forest datatype.
            Constructor nil1_con, cons1_con, nil2_con, cons2_con;
            Constructor[] constructors1 = new Constructor[2], constructors2 = new Constructor[2];
            Symbol[] sort_names = { ctx.MkSymbol("forest"), ctx.MkSymbol("tree") };

            /* build a forest */
            nil1_con = ctx.MkConstructor(ctx.MkSymbol("nil"), ctx.MkSymbol("is_nil"), null, null, null);
            cons1_con = ctx.MkConstructor(ctx.MkSymbol("cons1"), ctx.MkSymbol("is_cons1"), head_tail1, sorts1, sort1_refs);
            constructors1[0] = nil1_con;
            constructors1[1] = cons1_con;

            /* build a tree */
            nil2_con = ctx.MkConstructor(ctx.MkSymbol("nil2"), ctx.MkSymbol("is_nil2"), null, null, null);
            cons2_con = ctx.MkConstructor(ctx.MkSymbol("cons2"), ctx.MkSymbol("is_cons2"), head_tail2, sorts2, sort2_refs);
            constructors2[0] = nil2_con;
            constructors2[1] = cons2_con;


            Constructor[][] clists = new Constructor[][] { constructors1, constructors2 };

            Sort[] sorts = ctx.MkDatatypeSorts(sort_names, clists);
            forest = sorts[0];
            tree = sorts[1];

            //
            // Now that the datatype has been created.
            // Query the constructors for the constructor
            // functions, testers, and field accessors.
            //
            nil1_decl = nil1_con.ConstructorDecl;
            is_nil1_decl = nil1_con.TesterDecl;
            cons1_decl = cons1_con.ConstructorDecl;
            is_cons1_decl = cons1_con.TesterDecl;
            FuncDecl[] cons1_accessors = cons1_con.AccessorDecls;
            car1_decl = cons1_accessors[0];
            cdr1_decl = cons1_accessors[1];

            nil2_decl = nil2_con.ConstructorDecl;
            is_nil2_decl = nil2_con.TesterDecl;
            cons2_decl = cons2_con.ConstructorDecl;
            is_cons2_decl = cons2_con.TesterDecl;
            FuncDecl[] cons2_accessors = cons2_con.AccessorDecls;
            car2_decl = cons2_accessors[0];
            cdr2_decl = cons2_accessors[1];


            nil1 = ctx.MkConst(nil1_decl);
            nil2 = ctx.MkConst(nil2_decl);
            f1 = ctx.MkApp(cons1_decl, nil2, nil1);
            t1 = ctx.MkApp(cons2_decl, nil1, nil1);
            t2 = ctx.MkApp(cons2_decl, f1, nil1);
            t3 = ctx.MkApp(cons2_decl, f1, f1);
            t4 = ctx.MkApp(cons2_decl, nil1, f1);
            f2 = ctx.MkApp(cons1_decl, t1, nil1);
            f3 = ctx.MkApp(cons1_decl, t1, f1);


            /* nil != cons(nil,nil) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(nil1, f1)));
            Prove(ctx, ctx.MkNot(ctx.MkEq(nil2, t1)));


            /* cons(x,u) = cons(x, v) => u = v */
            u = ctx.MkConst("u", forest);
            v = ctx.MkConst("v", forest);
            x = ctx.MkConst("x", tree);
            y = ctx.MkConst("y", tree);
            l1 = ctx.MkApp(cons1_decl, x, u);
            l2 = ctx.MkApp(cons1_decl, y, v);
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(u, v)));
            Prove(ctx, ctx.MkImplies(ctx.MkEq(l1, l2), ctx.MkEq(x, y)));

            /* is_nil(u) or is_cons(u) */
            Prove(ctx, ctx.MkOr((BoolExpr)ctx.MkApp(is_nil1_decl, u),
                                (BoolExpr)ctx.MkApp(is_cons1_decl, u)));

            /* occurs check u != cons(x,u) */
            Prove(ctx, ctx.MkNot(ctx.MkEq(u, l1)));
        }

        /// <summary>
        /// Demonstrate how to use #Eval.
        /// </summary>
        public static void EvalExample1(Context ctx)
        {
            Console.WriteLine("EvalExample1");

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
                model = solver.Model;
                Console.WriteLine("{0}", model);
                Console.WriteLine("\nevaluating x+y");
                Expr v = model.Evaluate(ctx.MkAdd(x, y));
                if (v != null)
                {
                    Console.WriteLine("result = {0}", (v));
                }
                else
                {
                    Console.WriteLine("Failed to evaluate: x+y");
                }
            }
            else
            {
                Console.WriteLine("BUG, the constraints are satisfiable.");
            }
        }

        /// <summary>
        /// Demonstrate how to use #Eval on tuples.
        /// </summary>
        public static void EvalExample2(Context ctx)
        {
            Console.WriteLine("EvalExample2");

            Sort int_type = ctx.IntSort;
            TupleSort tuple = ctx.MkTupleSort(
             ctx.MkSymbol("mk_tuple"),                        // name of tuple constructor
             new Symbol[] { ctx.MkSymbol("first"), ctx.MkSymbol("second") },    // names of projection operators
             new Sort[] { int_type, int_type } // types of projection operators
             );
            FuncDecl first = tuple.FieldDecls[0];     // declarations are for projections
            FuncDecl second = tuple.FieldDecls[1];
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
                model = solver.Model;
                Console.WriteLine("{0}", model);
                Console.WriteLine("evaluating tup1 {0}", (model.Evaluate(tup1)));
                Console.WriteLine("evaluating tup2 {0}", (model.Evaluate(tup2)));
                Console.WriteLine("evaluating second(tup2) {0}",
                          (model.Evaluate(ctx.MkApp(second, tup2))));
            }
            else
            {
                Console.WriteLine("BUG, the constraints are satisfiable.");
            }
        }

        /// <summary>
        /// Demonstrate how to use <code>Push</code>and <code>Pop</code>to
        /// control the size of models.
        /// </summary>
        /// <remarks>Note: this test is specialized to 32-bit bitvectors.</remarks>
        public static void CheckSmall(Context ctx, Solver solver, BitVecExpr[] to_minimize)
        {
            Sort bv32 = ctx.MkBitVecSort(32);

            int num_Exprs = to_minimize.Length;
            UInt32[] upper = new UInt32[num_Exprs];
            UInt32[] lower = new UInt32[num_Exprs];
            BitVecExpr[] values = new BitVecExpr[num_Exprs];
            for (int i = 0; i < upper.Length; ++i)
            {
                upper[i] = UInt32.MaxValue;
                lower[i] = 0;
            }
            bool some_work = true;
            int last_index = -1;
            UInt32 last_upper = 0;
            while (some_work)
            {
                solver.Push();

                bool check_is_sat = true;
                while (check_is_sat && some_work)
                {
                    // Assert all feasible bounds.
                    for (int i = 0; i < num_Exprs; ++i)
                    {
                        solver.Assert(ctx.MkBVULE(to_minimize[i], ctx.MkBV(upper[i], 32)));
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
                    Console.WriteLine("{0}", solver.Model);

                    // narrow the bounds based on the current model.
                    for (int i = 0; i < num_Exprs; ++i)
                    {
                        Expr v = solver.Model.Evaluate(to_minimize[i]);
                        UInt64 ui = ((BitVecNum)v).UInt64;
                        if (ui < upper[i])
                        {
                            upper[i] = (UInt32)ui;
                        }
                        Console.WriteLine("{0} {1} {2}", i, lower[i], upper[i]);
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
                            solver.Assert(ctx.MkBVULE(to_minimize[i], ctx.MkBV(last_upper, 32)));
                            some_work = true;
                            break;
                        }
                    }
                }
                solver.Pop();
            }
        }

        /// <summary>
        /// Reduced-size model generation example.
        /// </summary>
        public static void FindSmallModelExample(Context ctx)
        {
            Console.WriteLine("FindSmallModelExample");

            BitVecExpr x = ctx.MkBVConst("x", 32);
            BitVecExpr y = ctx.MkBVConst("y", 32);
            BitVecExpr z = ctx.MkBVConst("z", 32);

            Solver solver = ctx.MkSolver();

            solver.Assert(ctx.MkBVULE(x, ctx.MkBVAdd(y, z)));
            CheckSmall(ctx, solver, new BitVecExpr[] { x, y, z });
        }

        /// <summary>
        /// Simplifier example.
        /// </summary>
        public static void SimplifierExample(Context ctx)
        {
            Console.WriteLine("SimplifierExample");

            IntExpr x = ctx.MkIntConst("x");
            IntExpr y = ctx.MkIntConst("y");
            IntExpr z = ctx.MkIntConst("z");
            IntExpr u = ctx.MkIntConst("u");

            Expr t1 = ctx.MkAdd(x, ctx.MkSub(y, ctx.MkAdd(x, z)));
            Expr t2 = t1.Simplify();
            Console.WriteLine("{0} -> {1}", (t1), (t2));
        }

        /// <summary>
        /// Extract unsatisfiable core example
        /// </summary>
        public static void UnsatCoreAndProofExample(Context ctx)
        {
            Console.WriteLine("UnsatCoreAndProofExample");

            Solver solver = ctx.MkSolver();

            BoolExpr pa = ctx.MkBoolConst("PredA");
            BoolExpr pb = ctx.MkBoolConst("PredB");
            BoolExpr pc = ctx.MkBoolConst("PredC");
            BoolExpr pd = ctx.MkBoolConst("PredD");
            BoolExpr p1 = ctx.MkBoolConst("P1");
            BoolExpr p2 = ctx.MkBoolConst("P2");
            BoolExpr p3 = ctx.MkBoolConst("P3");
            BoolExpr p4 = ctx.MkBoolConst("P4");
            BoolExpr[] assumptions = new BoolExpr[] { ctx.MkNot(p1), ctx.MkNot(p2), ctx.MkNot(p3), ctx.MkNot(p4) };
            BoolExpr f1 = ctx.MkAnd(new BoolExpr[] { pa, pb, pc });
            BoolExpr f2 = ctx.MkAnd(new BoolExpr[] { pa, ctx.MkNot(pb), pc });
            BoolExpr f3 = ctx.MkOr(ctx.MkNot(pa), ctx.MkNot(pc));
            BoolExpr f4 = pd;

            solver.Assert(ctx.MkOr(f1, p1));
            solver.Assert(ctx.MkOr(f2, p2));
            solver.Assert(ctx.MkOr(f3, p3));
            solver.Assert(ctx.MkOr(f4, p4));
            Status result = solver.Check(assumptions);

            if (result == Status.UNSATISFIABLE)
            {
                Console.WriteLine("unsat");
                Console.WriteLine("proof: {0}", solver.Proof);
                Console.WriteLine("core: ");
                foreach (Expr c in solver.UnsatCore)
                {
                    Console.WriteLine("{0}", c);
                }
            }
        }

        /// <summary>
        /// Extract unsatisfiable core example with AssertAndTrack
        /// </summary>
        public static void UnsatCoreAndProofExample2(Context ctx)
        {
            Console.WriteLine("UnsatCoreAndProofExample2");

            Solver solver = ctx.MkSolver();

            BoolExpr pa = ctx.MkBoolConst("PredA");
            BoolExpr pb = ctx.MkBoolConst("PredB");
            BoolExpr pc = ctx.MkBoolConst("PredC");
            BoolExpr pd = ctx.MkBoolConst("PredD");

            BoolExpr f1 = ctx.MkAnd(new BoolExpr[] { pa, pb, pc });
            BoolExpr f2 = ctx.MkAnd(new BoolExpr[] { pa, ctx.MkNot(pb), pc });
            BoolExpr f3 = ctx.MkOr(ctx.MkNot(pa), ctx.MkNot(pc));
            BoolExpr f4 = pd;

            BoolExpr p1 = ctx.MkBoolConst("P1");
            BoolExpr p2 = ctx.MkBoolConst("P2");
            BoolExpr p3 = ctx.MkBoolConst("P3");
            BoolExpr p4 = ctx.MkBoolConst("P4");

            solver.AssertAndTrack(f1, p1);
            solver.AssertAndTrack(f2, p2);
            solver.AssertAndTrack(f3, p3);
            solver.AssertAndTrack(f4, p4);
            Status result = solver.Check();

            if (result == Status.UNSATISFIABLE)
            {
                Console.WriteLine("unsat");
                Console.WriteLine("core: ");
                foreach (Expr c in solver.UnsatCore)
                {
                    Console.WriteLine("{0}", c);
                }
            }
        }

        public static void FiniteDomainExample(Context ctx)
        {
            Console.WriteLine("FiniteDomainExample");

            FiniteDomainSort s = ctx.MkFiniteDomainSort("S", 10);
            FiniteDomainSort t = ctx.MkFiniteDomainSort("T", 10);
            FiniteDomainNum s1 = (FiniteDomainNum)ctx.MkNumeral(1, s);
            FiniteDomainNum t1 = (FiniteDomainNum)ctx.MkNumeral(1, t);
            Console.WriteLine("{0} of size {1}", s, s.Size);
            Console.WriteLine("{0} of size {1}", t, t.Size);
            Console.WriteLine("{0}", s1);
            Console.WriteLine("{0}", t1);
            Console.WriteLine("{0}", s1.Int);
            Console.WriteLine("{0}", t1.Int);
            // But you cannot mix numerals of different sorts
            // even if the size of their domains are the same:
            // Console.WriteLine("{0}", ctx.MkEq(s1, t1));
        }

        public static void FloatingPointExample1(Context ctx)
        {
            Console.WriteLine("FloatingPointExample1");

            FPSort s = ctx.MkFPSort(11, 53);
            Console.WriteLine("Sort: {0}", s);

            FPNum x = (FPNum)ctx.MkNumeral("-1e1", s); /* -1 * 10^1 = -10 */
            FPNum y = (FPNum)ctx.MkNumeral("-10", s); /* -10 */
            FPNum z = (FPNum)ctx.MkNumeral("-1.25p3", s); /* -1.25 * 2^3 = -1.25 * 8 = -10 */
            Console.WriteLine("x={0}; y={1}; z={2}", x.ToString(), y.ToString(), z.ToString());

            BoolExpr a = ctx.MkAnd(ctx.MkFPEq(x, y), ctx.MkFPEq(y, z));
            Check(ctx, ctx.MkNot(a), Status.UNSATISFIABLE);

            /* nothing is equal to NaN according to floating-point
             * equality, so NaN == k should be unsatisfiable. */
            FPExpr k = (FPExpr)ctx.MkConst("x", s);
            FPExpr nan = ctx.MkFPNaN(s);

            /* solver that runs the default tactic for QF_FP. */
            Solver slvr = ctx.MkSolver("QF_FP");
            slvr.Add(ctx.MkFPEq(nan, k));
            if (slvr.Check() != Status.UNSATISFIABLE)
                throw new TestFailedException();
            Console.WriteLine("OK, unsat:" + Environment.NewLine + slvr);

            /* NaN is equal to NaN according to normal equality. */
            slvr = ctx.MkSolver("QF_FP");
            slvr.Add(ctx.MkEq(nan, nan));
            if (slvr.Check() != Status.SATISFIABLE)
                throw new TestFailedException();
            Console.WriteLine("OK, sat:" + Environment.NewLine + slvr);

            /* Let's prove -1e1 * -1.25e3 == +100 */
            x = (FPNum)ctx.MkNumeral("-1e1", s);
            y = (FPNum)ctx.MkNumeral("-1.25p3", s);
            FPExpr x_plus_y = (FPExpr)ctx.MkConst("x_plus_y", s);
            FPNum r = (FPNum)ctx.MkNumeral("100", s);
            slvr = ctx.MkSolver("QF_FP");

            slvr.Add(ctx.MkEq(x_plus_y, ctx.MkFPMul(ctx.MkFPRoundNearestTiesToAway(), x, y)));
            slvr.Add(ctx.MkNot(ctx.MkFPEq(x_plus_y, r)));
            if (slvr.Check() != Status.UNSATISFIABLE)
                throw new TestFailedException();
            Console.WriteLine("OK, unsat:" + Environment.NewLine + slvr);
        }

        public static void FloatingPointExample2(Context ctx)
        {
            Console.WriteLine("FloatingPointExample2");
            FPSort double_sort = ctx.MkFPSort(11, 53);
            FPRMSort rm_sort = ctx.MkFPRoundingModeSort();

            FPRMExpr rm = (FPRMExpr)ctx.MkConst(ctx.MkSymbol("rm"), rm_sort);
            BitVecExpr x = (BitVecExpr)ctx.MkConst(ctx.MkSymbol("x"), ctx.MkBitVecSort(64));
            FPExpr y = (FPExpr)ctx.MkConst(ctx.MkSymbol("y"), double_sort);
            FPExpr fp_val = ctx.MkFP(42, double_sort);

            BoolExpr c1 = ctx.MkEq(y, fp_val);
            BoolExpr c2 = ctx.MkEq(x, ctx.MkFPToBV(rm, y, 64, false));
            BoolExpr c3 = ctx.MkEq(x, ctx.MkBV(42, 64));
            BoolExpr c4 = ctx.MkEq(ctx.MkNumeral(42, ctx.RealSort), ctx.MkFPToReal(fp_val));
            BoolExpr c5 = ctx.MkAnd(c1, c2, c3, c4);
            Console.WriteLine("c5 = " + c5);

            /* Generic solver */
            Solver s = ctx.MkSolver();
            s.Assert(c5);

            Console.WriteLine(s);

            if (s.Check() != Status.SATISFIABLE)
                throw new TestFailedException();

            Console.WriteLine("OK, model: {0}", s.Model.ToString());
        }

        static void Main(string[] args)
        {
            try
            {
                Microsoft.Z3.Global.ToggleWarningMessages(true);
                Log.Open("test.log");

                Console.Write("Z3 Major Version: ");
                Console.WriteLine(Microsoft.Z3.Version.Major.ToString());
                Console.Write("Z3 Full Version: ");
                Console.WriteLine(Microsoft.Z3.Version.ToString());
                Console.Write("Z3 Full Version String: ");
                Console.WriteLine(Microsoft.Z3.Version.FullVersion);


                SimpleExample();

                // These examples need model generation turned on.
                using (Context ctx = new Context(new Dictionary<string, string>() { { "model", "true" } }))
                {
                    BasicTests(ctx);
                    CastingTest(ctx);
                    SudokuExample(ctx);
                    QuantifierExample1(ctx);
                    QuantifierExample2(ctx);
                    LogicExample(ctx);
                    ParOrExample(ctx);
                    FindModelExample1(ctx);
                    FindModelExample2(ctx);
                    PushPopExample1(ctx);
                    ArrayExample1(ctx);
                    ArrayExample3(ctx);
                    BitvectorExample1(ctx);
                    BitvectorExample2(ctx);
                    ParserExample1(ctx);
                    ParserExample2(ctx);
                    ParserExample4(ctx);
                    ParserExample5(ctx);
                    ITEExample(ctx);
                    EvalExample1(ctx);
                    EvalExample2(ctx);
                    FindSmallModelExample(ctx);
                    SimplifierExample(ctx);
                    FiniteDomainExample(ctx);
                    FloatingPointExample1(ctx);
                    FloatingPointExample2(ctx);
                }

                // These examples need proof generation turned on.
                using (Context ctx = new Context(new Dictionary<string, string>() { { "proof", "true" } }))
                {
                    ProveExample1(ctx);
                    ProveExample2(ctx);
                    ArrayExample2(ctx);
                    TupleExample(ctx);
                    ParserExample3(ctx);
                    EnumExample(ctx);
                    ListExample(ctx);
                    TreeExample(ctx);
                    ForestExample(ctx);
                    UnsatCoreAndProofExample(ctx);
                    UnsatCoreAndProofExample2(ctx);
                }

                // These examples need proof generation turned on and auto-config set to false.
                using (Context ctx = new Context(new Dictionary<string, string>()
                    { {"proof", "true" },
                      {"auto-config", "false" } }))
                {
                    QuantifierExample3(ctx);
                    QuantifierExample4(ctx);
                }

                Log.Close();
                if (Log.isOpen())
                    Console.WriteLine("Log is still open!");
            }
            catch (Z3Exception ex)
            {
                Console.WriteLine("Z3 Managed Exception: " + ex.Message);
                Console.WriteLine("Stack trace: " + ex.StackTrace);
            }
            catch (TestFailedException ex)
            {
                Console.WriteLine("TEST CASE FAILED: " + ex.Message);
            }
        }
    }
}
