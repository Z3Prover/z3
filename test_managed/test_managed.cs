
/** 
   \defgroup mapi_ex Managed (.NET) API examples
*/
/*@{*/

using Microsoft.Z3;
using System;
using System.Collections.Generic;
///
/// \brief Class encapsulating Z3 tests.
///

class TestManaged
{
    ///
    /// \brief local reference to the Z3 Api.
    ///
    Context z3;
    Solver solver;


    /*! \brief Create a logical context with model construction enabled.
    */
    public void mk_context()
    {
        if (this.z3 != null)
        {
            this.z3.Dispose();
        }
        Dictionary<string, string> cfg = new Dictionary<string, string>() { 
                { "MODEL", "true" },
                { "MBQI_MAX_ITERATIONS", "10" },
                { "PROOF_MODE", "2" } };
        this.z3 = new Context(cfg);
        this.solver = z3.MkSolver();
    }


    /*! \brief Create an integer type.
    */
    public IntSort mk_int_type()
    {
        return z3.MkIntSort();
    }

    /*! \brief Create a bit-vector type.
    */
    public BitVecSort mk_bv_type(uint num_bytes)
    {
        return z3.MkBitVecSort(num_bytes);
    }

    /*! \brief Create a variable using the given name and type.
    */
    public Expr mk_var(string name, Sort ty)
    {
        return z3.MkConst(name, ty);
    }

    /*! \brief Create a boolean variable using the given name.
    */
    public BoolExpr mk_bool_var(string name)
    {
        return (BoolExpr) mk_var(name, z3.MkBoolSort());
    }

    /*! \brief Create an integer variable using the given name.
    */
    public IntExpr mk_int_var(string name)
    {
        return (IntExpr)mk_var(name, mk_int_type());
    }

    /*! \brief Create a bit-vector variable using the given name.
    */
    public BitVecExpr mk_bv_var(string name, uint num_bytes)
    {
        return (BitVecExpr)mk_var(name, mk_bv_type(num_bytes));
    }

    /*! \brief Create a Z3 integer node using an int. 
    */
    IntExpr mk_int(int v)
    {
        return (IntExpr)z3.MkNumeral(v, mk_int_type());
    }

    /*! \brief Create a Z3 32-bit integer.
    */
    BitVecExpr mk_bv32(UInt32 b)
    {
        return (BitVecExpr)z3.MkNumeral(String.Format("{0}", b), mk_bv_type(32));
    }

    /*! \brief Create the unary function application: <tt>(f x)</tt>.
    */
    Expr mk_unary_app(FuncDecl f, Expr x)
    {
        return f[x];
    }

    /*! \brief Create the binary function application: <tt>(f x y)</tt>.
    */
    Expr mk_binary_app(FuncDecl f, Expr x, Expr y)
    {
        return f[x, y];
    }

    void exitf(string message)
    {
        Console.WriteLine("{0}", message);
        throw new Exception("Fatal Error");
    }

    /*!
       \brief Check whether the logical context is satisfiable, 
       and compare the result with the expected result.
       If the context is satisfiable, then display the model.
    */
    public void check(Status expected_result, out Model model)
    {        
        Status result = solver.Check();
        model = null;
        Console.WriteLine("{0}", result);
        switch (result)
        {
            case Status.UNSATISFIABLE:
                break;
            case Status.UNKNOWN:
                break;
            case Status.SATISFIABLE:
                model = solver.Model;
                Console.WriteLine("{0}", model.ToString());
                break;
        }
        if (result != expected_result)
        {
            Console.WriteLine("BUG: unexpected result");
        }
    }

    /**
       \brief Similar to #check, but uses #display_model instead of Z3's native display method.
    */
    public void check2(Status expected_result)
    {        
        Status result = solver.Check();
        Console.WriteLine("{0}", result);
        switch (result)
        {
            case Status.UNSATISFIABLE:
            case Status.UNKNOWN:
                break;
            case Status.SATISFIABLE:
                display_model(Console.Out, solver.Model);
                break;
        }
        if (result != expected_result)
        {
            Console.WriteLine("BUG: unexpected result");
        }
    }



    /*!
       \brief Prove that the constraints already asserted into the logical
       context implies the given formula.  The result of the proof is
       displayed.
   
       Z3 is a satisfiability checker. So, one can prove \c f by showing
       that <tt>(not f)</tt> is unsatisfiable.

    */
    public void prove(BoolExpr f)
    {
        /* save the current state of the context */
        solver.Push();        

        BoolExpr not_f = z3.MkNot(f);
        solver.Assert(not_f);
        Status result = solver.Check();

        switch (result)
        {
            case Status.UNSATISFIABLE:
                /* proved */                
                Console.WriteLine("valid");
                Console.WriteLine("Proof: " + solver.Proof);
                break;
            case Status.UNKNOWN:
                /* Z3 failed to prove/disprove f. */
                Console.WriteLine("unknown");
                break;
            case Status.SATISFIABLE:
                /* disproved */
                Console.WriteLine("invalid");
                display_model(Console.Out, solver.Model); 
                break;
        }

        /* restore context */
        solver.Pop();
    }

    /*!
       \brief Prove that the constraints already asserted into the logical
       context implies the given formula.  The result of the proof is
       displayed.
   
       Z3 is a satisfiability checker. So, one can prove \c f by showing
       that <tt>(not f)</tt> is unsatisfiable.

    */
    public void prove2(BoolExpr f, bool is_valid)
    {
        /* save the current state of the context */
        solver.Push();

        BoolExpr not_f = z3.MkNot(f);
        solver.Assert(not_f);

        switch (solver.Check())
        {
            case Status.UNSATISFIABLE:
                /* proved */
                Console.WriteLine("valid");
                if (!is_valid)
                {
                    exitf("Did not expecte valid");
                }
                break;
            case Status.UNKNOWN:
                /* Z3 failed to prove/disprove f. */
                Console.WriteLine("unknown");
                if (is_valid)
                {
                    exitf("Expected valid");
                }
                break;
            case Status.SATISFIABLE:
                /* disproved */
                Console.WriteLine("invalid");
                display_model(Console.Out, solver.Model);
                if (is_valid)
                {
                    exitf("Expected valid");
                }
                break;
        }

        /* restore context */
        solver.Pop();

    }

    /**
       \brief Custom model pretty printer.
    */
    void display_model(System.IO.TextWriter w, Model model)
    {
        w.WriteLine("Custom model display:");
        FuncDecl[] consts = model.ConstDecls; 
        for (int i = 0; i < consts.Length; i++)
        {
            w.WriteLine("{0} |-> {1}", consts[i], model.Evaluate(consts[i].Apply()));
        }
        w.WriteLine("num consts: {0}", consts.Length);
        FuncDecl[] funcs = model.FuncDecls;
        foreach (FuncDecl f in funcs)
        {
            FuncInterp g = model.FuncInterp(f);
            
            w.WriteLine("function {0}:", f);
            for (int j = 0; j < g.Entries.Length; ++j)
            {
                for (int k = 0; k < g.Entries[j].Args.Length; ++k)
                {
                    w.Write("  {0} ", g.Entries[j].Args[k]);
                }
                w.WriteLine(" |-> {0}", g.Entries[j].Value);
            }
            w.WriteLine("  else |-> {0}", g.Else);
        }
    }

    /*!
       \brief Assert the axiom: function f is injective in the i-th argument.
       
       The following axiom is asserted into the logical context:
       \code
       forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
       \endcode
       
       Where, \c finv is a fresh function declaration.
    */
    public void assert_inj_axiom(FuncDecl f, int i)
    {
        Sort[] domain = f.Domain;
        uint sz = f.DomainSize;

        if (i >= sz)
        {
            Console.WriteLine("failed to create inj axiom");
            return;
        }

        /* declare the i-th inverse of f: finv */
        Sort finv_domain = f.Range;
        Sort finv_range = domain[i];
        FuncDecl finv = z3.MkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        Expr[] xs = new Expr[sz];
        Symbol[] names = new Symbol[sz];
        Sort[] types = new Sort[sz];

        /* fill types, names and xs */

        for (uint j = 0; j < sz; j++)
        {
            types[j] = domain[j];
            names[j] = z3.MkSymbol(String.Format("x_{0}", j));
            xs[j] = z3.MkBound(j, types[j]);
        }
        Expr x_i = xs[i];

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr fxs = f[xs]; 

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr finv_fxs = mk_unary_app(finv, fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Expr eq = z3.MkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = z3.MkPattern(new Expr[] { fxs });
        Console.WriteLine("pattern {0}", p);

        /* create & assert quantifier */
        BoolExpr q = z3.MkForall(
            types, /* types of quantified variables */
            names, /* names of quantified variables */
            eq,
            1,
            new Pattern[] { p } /* patterns */);

        Console.WriteLine("assert axiom {0}", q);
        solver.Assert(q);

    }

    /*!
       \brief Assert the axiom: function f is injective in the i-th argument.
       
       The following axiom is asserted into the logical context:
       \code
       forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
       \endcode
       
       Where, \c finv is a fresh function declaration.
    */
    public void assert_inj_axiom_abs(FuncDecl f, int i)
    {
        Sort[] domain = f.Domain;
        uint sz = f.DomainSize;

        if (i >= sz)
        {
            Console.WriteLine("failed to create inj axiom");
            return;
        }

        /* declare the i-th inverse of f: finv */
        Sort finv_domain = f.Range;
        Sort finv_range = domain[i];
        FuncDecl finv = z3.MkFuncDecl("f_fresh", finv_domain, finv_range);

        /* allocate temporary arrays */
        Expr[] xs = new Expr[sz];

        /* fill types, names and xs */

        for (uint j = 0; j < sz; j++)
        {
            xs[j] = z3.MkConst(String.Format("x_{0}", j), domain[j]);
        }
        Expr x_i = xs[i];

        /* create f(x_0, ..., x_i, ..., x_{n-1}) */
        Expr fxs = f[xs];

        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Expr finv_fxs = mk_unary_app(finv, fxs);

        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Expr eq = z3.MkEq(finv_fxs, x_i);

        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p = z3.MkPattern(new Expr[] { fxs });
        Console.WriteLine("pattern {0}", p);

        /* create & assert quantifier */
        Quantifier q = z3.MkForall(
            xs,    /* the list of bound variables */            
            eq,
            1, 
            new Pattern[] { p } /* patterns */);

        Console.WriteLine("assert axiom {0}", q);
        solver.Assert(q);

    }

    /**
       \brief Assert the axiom: function f is commutative. 
   
       This example uses the SMT-LIB parser to simplify the axiom construction.
    */
    private void assert_comm_axiom(FuncDecl f)
    {
        Sort t = f.Range;
        Sort[] dom = f.Domain;

        if (dom.Length != 2 ||
            !t.Equals(dom[0]) ||
            !t.Equals(dom[1]))
        {
            Console.WriteLine("{0} {1} {2} {3}", dom.Length, dom[0], dom[1], t);
            exitf("function must be binary, and argument types must be equal to return type");
        }
        string bench = string.Format("(benchmark comm :formula (forall (x {0}) (y {1}) (= ({2} x y) ({3} y x))))",
                         t.Name, t.Name, f.Name, f.Name);
        z3.ParseSMTLIBString(bench, new Symbol[] { t.Name }, new Sort[] { t }, new Symbol[] { f.Name }, new FuncDecl[] { f });
        BoolExpr q = z3.SMTLIBFormulas[0];
        Console.WriteLine("assert axiom:\n{0}", q);
        solver.Assert(q);
    }



    /* @name Examples
    */

    /*!
       \brief "Hello world" example: create a Z3 logical context, and delete it.
    */
    public void simple_example()
    {
        Console.WriteLine("simple_example");
        Dictionary<string, string> cfg = new Dictionary<string, string>();
        Context z3 = new Context(cfg);

        /* do something with the context */

        /* be kind to dispose manually and not wait for the GC. */
        z3.Dispose();
    }

    /*!
       \brief Find a model for <tt>x xor y</tt>.
    */
    public void find_model_example1()
    {
        Console.WriteLine("find_model_example1");

        mk_context();

        BoolExpr x = mk_bool_var("x");
        BoolExpr y = mk_bool_var("y");
        BoolExpr x_xor_y = z3.MkXor(x, y);

        solver.Assert(x_xor_y);

        Console.WriteLine("model for: x xor y");
        Model model = null;
        check(Status.SATISFIABLE, out model);
        Console.WriteLine("x = {0}, y = {1}",
                          model.Evaluate(x),
                          model.Evaluate(y));
    }

    /*!
       \brief Find a model for <tt>x < y + 1, x > 2</tt>.
       Then, assert <tt>not(x = y)</tt>, and find another model.
    */
    public void find_model_example2()
    {
        Console.WriteLine("find_model_example2");

        mk_context();
        IntExpr x = mk_int_var("x");
        IntExpr y = mk_int_var("y");
        IntExpr one = mk_int(1);
        IntExpr two = mk_int(2);

        ArithExpr y_plus_one = z3.MkAdd(y, one);

        BoolExpr c1 = z3.MkLt(x, y_plus_one);
        BoolExpr c2 = z3.MkGt(x, two);

        solver.Assert(c1);
        solver.Assert(c2);

        Console.WriteLine("model for: x < y + 1, x > 2");
        Model model = null;
        check(Status.SATISFIABLE, out model);
        Console.WriteLine("x = {0}, y = {1}",
                          (model.Evaluate(x)),
                          (model.Evaluate(y)));

        /* assert not(x = y) */
        BoolExpr x_eq_y = z3.MkEq(x, y);
        BoolExpr c3 = z3.MkNot(x_eq_y);
        solver.Assert(c3);

        Console.WriteLine("model for: x < y + 1, x > 2, not(x = y)");
        check(Status.SATISFIABLE, out model);
        Console.WriteLine("x = {0}, y = {1}",
                          (model.Evaluate(x)),
                          (model.Evaluate(y)));
    }

    /*!
       \brief Prove <tt>x = y implies g(x) = g(y)</tt>, and
       disprove <tt>x = y implies g(g(x)) = g(y)</tt>.
       
       This function demonstrates how to create uninterpreted types and
       functions.
    */
    public void prove_example1()
    {
        Console.WriteLine("prove_example1");

        mk_context();

        /* create uninterpreted type. */
        Sort U = z3.MkUninterpretedSort(z3.MkSymbol("U"));

        /* declare function g */
        FuncDecl g = z3.MkFuncDecl("g", U, U);

        /* create x and y */
        Expr x = z3.MkConst("x", U);
        Expr y = z3.MkConst("y", U);
        /* create g(x), g(y) */
        Expr gx = mk_unary_app(g, x);
        Expr gy = mk_unary_app(g, y);

        /* assert x = y */
        BoolExpr eq = z3.MkEq(x, y);        

        /* prove g(x) = g(y) */
        BoolExpr f = z3.MkEq(gx, gy);
        Console.WriteLine("prove: x = y implies g(x) = g(y)");
        prove(z3.MkImplies(eq, f));

        /* create g(g(x)) */
        Expr ggx = mk_unary_app(g, gx);

        /* disprove g(g(x)) = g(y) */
        f = z3.MkEq(ggx, gy);
        Console.WriteLine("disprove: x = y implies g(g(x)) = g(y)");
        prove(z3.MkImplies(eq, f));


        /* Print the model using the custom model printer */
        solver.Assert(z3.MkNot(f));
        check2(Status.SATISFIABLE);
    }


    /*! \brief Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0 </tt>.
        Then, show that <tt>z < -1</tt> is not implied.
       
        This example demonstrates how to combine uninterpreted functions and arithmetic.
    */
    public void prove_example2()
    {
        Console.WriteLine("prove_example2");

        mk_context();

        /* declare function g */
        Sort int_type = mk_int_type();

        FuncDecl g = z3.MkFuncDecl("g", int_type, int_type);

        /* create x, y, and z */
        IntExpr x = mk_int_var("x");
        IntExpr y = mk_int_var("y");
        IntExpr z = mk_int_var("z");

        /* create gx, gy, gz */
        Expr gx = mk_unary_app(g, x);
        Expr gy = mk_unary_app(g, y);
        Expr gz = mk_unary_app(g, z);

        /* create zero */
        IntExpr zero = mk_int(0);

        /* assert not(g(g(x) - g(y)) = g(z)) */
        ArithExpr gx_gy = z3.MkSub((IntExpr)gx, (IntExpr)gy);
        Expr ggx_gy = mk_unary_app(g, gx_gy);
        BoolExpr eq = z3.MkEq(ggx_gy, gz);
        BoolExpr c1 = z3.MkNot(eq);
        solver.Assert(c1);

        /* assert x + z <= y */
        ArithExpr x_plus_z = z3.MkAdd(x, z);
        BoolExpr c2 = z3.MkLe(x_plus_z, y);
        solver.Assert(c2);

        /* assert y <= x */
        BoolExpr c3 = z3.MkLe(y, x);
        solver.Assert(c3);

        /* prove z < 0 */
        BoolExpr f = z3.MkLt(z, zero);
        Console.WriteLine("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0");
        prove(f);

        /* disprove z < -1 */
        IntExpr minus_one = mk_int(-1);
        f = z3.MkLt(z, minus_one);
        Console.WriteLine("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1");
        prove(f);
    }

    /*! \brief Show how push & pop can be used to create "backtracking"
         points.
       
         This example also demonstrates how big numbers can be created in Z3.
    */
    public void push_pop_example1()
    {
        Console.WriteLine("push_pop_example1");

        mk_context();

        /* create a big number */
        IntSort int_type = mk_int_type();
        IntExpr big_number = (IntExpr)z3.MkNumeral("1000000000000000000000000000000000000000000000000000000", int_type);

        /* create number 3 */
        IntExpr three = (IntExpr)z3.MkNumeral("3", int_type);

        /* create x */
        IntExpr x = mk_int_var("x");  


        /* assert x >= "big number" */
        BoolExpr c1 = z3.MkGe(x, big_number);
        Console.WriteLine("assert: x >= 'big number'");
        solver.Assert(c1);

        /* create a backtracking point */
        Console.WriteLine("push");
        solver.Push();

        /* assert x <= 3 */
        BoolExpr c2 = z3.MkLe(x, three);
        Console.WriteLine("assert: x <= 3");
        solver.Assert(c2);

        /* context is inconsistent at this point */
        Model model = null;
        check(Status.UNSATISFIABLE, out model);

        /* backtrack: the constraint x <= 3 will be removed, since it was
           asserted after the last z3.Push. */
        Console.WriteLine("pop");
        solver.Pop(1);

        /* the context is consistent again. */
        check2(Status.SATISFIABLE);

        /* new constraints can be asserted... */

        /* create y */
        IntExpr y = mk_int_var("y"); 

        /* assert y > x */
        BoolExpr c3 = z3.MkGt(y, x);
        Console.WriteLine("assert: y > x");
        solver.Assert(c3);

        /* the context is still consistent. */
        check(Status.SATISFIABLE, out model);
    }

   public void mk_quantifier()
   {
        Console.WriteLine("quantifier_example1");
        mk_context();
        Expr q1, q2;
        FuncDecl f = z3.MkFuncDecl("f", z3.MkIntSort(), z3.MkIntSort());
        FuncDecl g = z3.MkFuncDecl("g", z3.MkIntSort(), z3.MkIntSort());

        // Quantifier with Exprs as the bound variables.
	{
        Expr x = z3.MkConst("x", z3.MkIntSort());
        Expr y = z3.MkConst("y", z3.MkIntSort());
        Expr f_x = z3.MkApp(f,x);
        Expr f_y = z3.MkApp(f,y);
        Expr g_y = z3.MkApp(g,y);
        Pattern[] pats = new Pattern[] { z3.MkPattern(new Expr[]{ f_x, g_y }) };
        Expr[] no_pats = new Expr[]{f_y};
        Expr[] bound = new Expr[2]{ x, y };
        Expr body = z3.MkAnd(z3.MkEq(f_x,f_y),z3.MkEq(f_y,g_y));

        q1 = z3.MkForall(bound, body, 1, null, no_pats, z3.MkSymbol("q"), z3.MkSymbol("sk"));

        Console.WriteLine("{0}", q1);
        }
        // Quantifier with de-Brujin indices.
	{
        Expr x = z3.MkBound(1, z3.MkIntSort());
        Expr y = z3.MkBound(0, z3.MkIntSort());
        Expr f_x = z3.MkApp(f,x);
        Expr f_y = z3.MkApp(f,y);
        Expr g_y = z3.MkApp(g,y);
        Pattern[] pats = new Pattern[] { z3.MkPattern(new Expr[]{ f_x, g_y }) };
        Expr[] no_pats = new Expr[]{f_y};
        Symbol[] names = new Symbol[] { z3.MkSymbol("x"), z3.MkSymbol("y") };
        Sort[] sorts = new Sort[] { z3.MkIntSort(), z3.MkIntSort() };
        Expr body = z3.MkAnd(z3.MkEq(f_x,f_y),z3.MkEq(f_y,g_y));

        q2 = z3.MkForall( sorts, names, body, 1,
                                 null, // pats,
                                 no_pats,
                                 z3.MkSymbol("q"),
                                 z3.MkSymbol("sk")
                                );
        Console.WriteLine("{0}", q2);
	}
        Console.WriteLine("{0}", (q1.Equals(q2)));

   }

    /*! \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when 
        \c f is injective in the second argument.
       
        \sa assert_inj_axiom.
    */
    public void quantifier_example1()
    {
        Console.WriteLine("quantifier_example1");

        Dictionary<string, string> cfg = new Dictionary<string, string>() { 
            { "MBQI", "false" },
            { "PROOF_MODE", "2" } };
        /* If quantified formulas are asserted in a logical context, then
           the model produced by Z3 should be viewed as a potential model.
           
        */
        if (this.z3 != null)
        {
            this.z3.Dispose();
        }
        this.z3 = new Context(cfg);
        this.solver = z3.MkSolver();

        /* declare function f */
        Sort int_type = mk_int_type();
        FuncDecl f = z3.MkFuncDecl("f", new Sort[] { int_type, int_type }, int_type);

        /* assert that f is injective in the second argument. */
        assert_inj_axiom(f, 1);

        /* create x, y, v, w, fxy, fwv */
        Expr x = mk_int_var("x");
        Expr y = mk_int_var("y");
        Expr v = mk_int_var("v");
        Expr w = mk_int_var("w");
        Expr fxy = mk_binary_app(f, x, y);
        Expr fwv = mk_binary_app(f, w, v);

        /* assert f(x, y) = f(w, v) */
        BoolExpr p1 = z3.MkEq(fxy, fwv);
        solver.Assert(p1);

        /* prove f(x, y) = f(w, v) implies y = v */
        BoolExpr p2 = z3.MkEq(y, v);
        Console.WriteLine("prove: f(x, y) = f(w, v) implies y = v");
        prove(p2);

        /* disprove f(x, y) = f(w, v) implies x = w */
        BoolExpr p3 = z3.MkEq(x, w);
        Console.WriteLine("disprove: f(x, y) = f(w, v) implies x = w");
        prove(p3);
    }

    /*! \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when 
        \c f is injective in the second argument.
       
        \sa assert_inj_axiom.
    */
    public void quantifier_example1_abs()
    {
        Console.WriteLine("quantifier_example1_abs");

        Dictionary<string, string> cfg = new Dictionary<string, string>() { { "MBQI", "false" }, { "PROOF_MODE", "2" } };

        /* If quantified formulas are asserted in a logical context, then
           the model produced by Z3 should be viewed as a potential model.
           
        */
        if (this.z3 != null)
        {
            this.z3.Dispose();
        }
        this.z3 = new Context(cfg);
        this.solver = z3.MkSolver();

        /* declare function f */
        Sort int_type = mk_int_type();
        FuncDecl f = z3.MkFuncDecl("f", new Sort[] { int_type, int_type }, int_type);

        /* assert that f is injective in the second argument. */
        assert_inj_axiom_abs(f, 1);

        /* create x, y, v, w, fxy, fwv */
        Expr x = mk_int_var("x");
        Expr y = mk_int_var("y");
        Expr v = mk_int_var("v");
        Expr w = mk_int_var("w");
        Expr fxy = mk_binary_app(f, x, y);
        Expr fwv = mk_binary_app(f, w, v);

        /* assert f(x, y) = f(w, v) */
        BoolExpr p1 = z3.MkEq(fxy, fwv);
        solver.Assert(p1);

        /* prove f(x, y) = f(w, v) implies y = v */
        BoolExpr p2 = z3.MkEq(y, v);
        Console.WriteLine("prove: f(x, y) = f(w, v) implies y = v");
        prove(p2);

        /* disprove f(x, y) = f(w, v) implies x = w */
        BoolExpr p3 = z3.MkEq(x, w);
        Console.WriteLine("disprove: f(x, y) = f(w, v) implies x = w");
        prove(p3);
    }


    /*! \brief Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))</tt>.
       
       This example demonstrates how to use the array theory.
    */
    public void array_example1()
    {

        Console.WriteLine("array_example1");

        mk_context();

        Sort int_type = mk_int_type();
        Sort array_type = z3.MkArraySort(int_type, int_type);

        ArrayExpr a1 = (ArrayExpr)mk_var("a1", array_type);
        ArrayExpr a2 = (ArrayExpr)mk_var("a2", array_type);
        Expr i1 = mk_var("i1", int_type);
        Expr i2 = mk_var("i2", int_type);
        Expr i3 = mk_var("i3", int_type);
        Expr v1 = mk_var("v1", int_type);
        Expr v2 = mk_var("v2", int_type);

        Expr st1 = z3.MkStore(a1, i1, v1);
        Expr st2 = z3.MkStore(a2, i2, v2);

        Expr sel1 = z3.MkSelect(a1, i3);
        Expr sel2 = z3.MkSelect(a2, i3);

        /* create antecedent */
        BoolExpr antecedent = z3.MkEq(st1, st2);

        /* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) */
        BoolExpr consequent = z3.MkOr(new BoolExpr[] { z3.MkEq(i1, i3), z3.MkEq(i2, i3), z3.MkEq(sel1, sel2) });

        /* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) */
        BoolExpr thm = z3.MkImplies(antecedent, consequent);
        Console.WriteLine("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))");
        Console.WriteLine("{0}", (thm));
        prove(thm);
    }

    /*! \brief Show that <tt>distinct(a_0, ... , a_n)</tt> is
       unsatisfiable when \c a_i's are arrays from boolean to
       boolean and n > 4.
       
       This example also shows how to use the \c distinct construct.
    */
    public void array_example2()
    {
        Console.WriteLine("array_example2");

        for (int n = 2; n <= 5; n++)
        {
            Console.WriteLine("n = {0}", n);
            mk_context();

            Sort bool_type = z3.MkBoolSort();
            Sort array_type = z3.MkArraySort(bool_type, bool_type);
            Expr[] a = new Expr[n];

            /* create arrays */
            for (int i = 0; i < n; i++)
            {
                a[i] = z3.MkConst(String.Format("array_{0}", i), array_type);
            }

            /* assert distinct(a[0], ..., a[n]) */
            BoolExpr d = z3.MkDistinct(a);
            Console.WriteLine("{0}", (d));
            solver.Assert(d);

            /* context is satisfiable if n < 5 */
            Model model = null;
            check(n < 5 ? Status.SATISFIABLE : Status.UNSATISFIABLE, out model);
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

    /*! \brief Tuples.

        Check that the projection of a tuple returns the corresponding element.
    */
    public void tuple_example()
    {
        mk_context();
        Sort int_type = mk_int_type();
        TupleSort tuple = z3.MkTupleSort(
         z3.MkSymbol("mk_tuple"),                        // name of tuple constructor
         new Symbol[] { z3.MkSymbol("first"), z3.MkSymbol("second") },    // names of projection operators
         new Sort[] { int_type, int_type } // types of projection operators         
            );
        FuncDecl first = tuple.FieldDecls[0];         // declarations are for projections
        FuncDecl second = tuple.FieldDecls[1];
        Expr x = z3.MkConst("x", int_type);
        Expr y = z3.MkConst("y", int_type);
        Expr n1 = tuple.MkDecl[x, y];
        Expr n2 = first[n1];
        BoolExpr n3 = z3.MkEq(x, n2);
        Console.WriteLine("Tuple example: {0}", n3);
        prove(n3);
    }

    /*!
       \brief Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
    */
    public void bitvector_example1()
    {
        Console.WriteLine("\nbitvector_example1");

        mk_context();

        Sort bv_type = z3.MkBitVecSort(32);
        BitVecExpr x = (BitVecExpr)mk_var("x", bv_type);
        BitVecNum zero = (BitVecNum)z3.MkNumeral("0", bv_type);
        BitVecNum ten = (BitVecNum)z3.MkNumeral("10", bv_type);
        BitVecExpr x_minus_ten = z3.MkBVSub(x, ten);
        /* bvsle is signed less than or equal to */
        BoolExpr c1 = z3.MkBVSLE(x, ten);
        BoolExpr c2 = z3.MkBVSLE(x_minus_ten, zero);
        BoolExpr thm = z3.MkIff(c1, c2);
        Console.WriteLine("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers");
        prove(thm);
    }

    /*!
       \brief Find x and y such that: x ^ y - 103 == x * y
    */
    public void bitvector_example2()
    {
        mk_context();

        /* construct x ^ y - 103 == x * y */
        Sort bv_type = z3.MkBitVecSort(32);
        BitVecExpr x = (BitVecExpr)mk_var("x", bv_type);
        BitVecExpr y = (BitVecExpr)mk_var("y", bv_type);
        BitVecExpr x_xor_y = z3.MkBVXOR(x, y);
        BitVecExpr c103 = (BitVecNum)z3.MkNumeral("103", bv_type);
        BitVecExpr lhs = z3.MkBVSub(x_xor_y, c103);
        BitVecExpr rhs = z3.MkBVMul(x, y);
        BoolExpr ctr = z3.MkEq(lhs, rhs);

        Console.WriteLine("\nbitvector_example2");
        Console.WriteLine("find values of x and y, such that x ^ y - 103 == x * y");

        /* add the constraint <tt>x ^ y - 103 == x * y<\tt> to the logical context */
        solver.Assert(ctr);

        /* find a model (i.e., values for x an y that satisfy the constraint */
        check2(Status.SATISFIABLE);
    }



    /*!
       \brief Demonstrates how to use the SMTLIB parser.
    */
    public void parser_example1()
    {
        mk_context();

        Console.WriteLine("\nparser_example1");

        z3.ParseSMTLIBString("(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))");
        foreach (BoolExpr f in z3.SMTLIBFormulas)
        {
            Console.WriteLine("formula {0}", f);
            solver.Assert(f);
        }
        check2(Status.SATISFIABLE);
    }

    /*!
       \brief Demonstrates how to initialize the parser symbol table.
    */
    public void parser_example2()
    {
        mk_context();
        Console.WriteLine("\nparser_example2");

        /* 
           Z3_enable_arithmetic doesn't need to be invoked in this example
           because it will be implicitly invoked by mk_int_var.
        */

        Symbol[] declNames = { z3.MkSymbol("a"), z3.MkSymbol("b") };
        FuncDecl a = z3.MkConstDecl(declNames[0], z3.MkIntSort());
        FuncDecl b = z3.MkConstDecl(declNames[1], z3.MkIntSort());
        FuncDecl[] decls = new FuncDecl[] { a, b };        

        z3.ParseSMTLIBString("(benchmark tst :formula (> a b))",
			                 null, null, declNames, decls);
        BoolExpr f = z3.SMTLIBFormulas[0];
        Console.WriteLine("formula: {0}", f);
        solver.Assert(f);
        check2(Status.SATISFIABLE);
    }

    /*!
       \brief Demonstrates how to initialize the parser symbol table.
    */
    public void parser_example3()
    {
        Console.WriteLine("\nparser_example3");

        mk_context();

        /* declare function g */
        Sort int_type = z3.MkIntSort();
        FuncDecl g = z3.MkFuncDecl("g", new Sort[] { int_type, int_type }, int_type);        

        assert_comm_axiom(g);

        z3.ParseSMTLIBString("(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (gg x 0) (gg 0 y)))))",
	     null, null, 
         new Symbol[] { z3.MkSymbol("gg") },
	     new FuncDecl[] { g });

        BoolExpr thm = z3.SMTLIBFormulas[0];
        Console.WriteLine("formula: {0}", thm);
        prove(thm);
    }

    /*!
       \brief Display the declarations, assumptions and formulas in a SMT-LIB string.
    */
    public void parser_example4()
    {
        mk_context();

        Console.WriteLine("\nparser_example4");

        z3.ParseSMTLIBString
	    ("(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))");
        foreach (var decl in z3.SMTLIBDecls)
        {
            Console.WriteLine("Declaration: {0}", decl);
        }
        foreach (var f in z3.SMTLIBAssumptions)
        {
            Console.WriteLine("Assumption: {0}", f);
        }
        foreach (var f in z3.SMTLIBFormulas)
        {
            Console.WriteLine("Formula: {0}", f);
        }
    }

    /*!
       \brief Demonstrates how to handle parser errors using Z3 error handling support.
    */
    public void parser_example5()
    {
        Console.WriteLine("\nparser_example5");
        
        try
        {
            z3.ParseSMTLIBString(
                /* the following string has a parsing error: missing parenthesis */
                     "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))");
        }
        catch (Z3Exception e)
        {
            Console.WriteLine("Z3 error: {0}", e);
        }
    }

    /*!
       \brief Create an ite-Expr (if-then-else Exprs).
    */
    public void ite_example()
    {
        Console.WriteLine("\nite_example");
        mk_context();

        BoolExpr f = z3.MkFalse();
        Expr one = mk_int(1);
        Expr zero = mk_int(0);
        Expr ite = z3.MkITE(f, one, zero);

        Console.WriteLine("Expr: {0}", ite);
    }

    /*!
       \brief Create an enumeration data type.
    */
    public void enum_example()
    {
        mk_context();
        Symbol name = z3.MkSymbol("fruit");        

        Console.WriteLine("\nenum_example");

        EnumSort fruit = z3.MkEnumSort(z3.MkSymbol("fruit"), new Symbol[] { z3.MkSymbol("apple"), z3.MkSymbol("banana"), z3.MkSymbol("orange") });

        Console.WriteLine("{0}", (fruit.Consts[0]));
        Console.WriteLine("{0}", (fruit.Consts[1]));
        Console.WriteLine("{0}", (fruit.Consts[2]));

        Console.WriteLine("{0}", (fruit.TesterDecls[0]));
        Console.WriteLine("{0}", (fruit.TesterDecls[1]));
        Console.WriteLine("{0}", (fruit.TesterDecls[2]));

        Expr apple = z3.MkConst(fruit.ConstDecls[0]);
        Expr banana = z3.MkConst(fruit.ConstDecls[1]);
        Expr orange = z3.MkConst(fruit.ConstDecls[2]);

        /* Apples are different from oranges */
        prove2(z3.MkNot(z3.MkEq(apple, orange)), true);

        /* Apples pass the apple test */
        prove2((BoolExpr)z3.MkApp(fruit.TesterDecls[0], apple), true);

        /* Oranges fail the apple test */
        prove2((BoolExpr)z3.MkApp(fruit.TesterDecls[0], orange), false);
        prove2((BoolExpr)z3.MkNot((BoolExpr)z3.MkApp(fruit.TesterDecls[0], orange)), true);

        Expr fruity = mk_var("fruity", fruit);

        /* If something is fruity, then it is an apple, banana, or orange */

        prove2(z3.MkOr(new BoolExpr[] { z3.MkEq(fruity, apple), z3.MkEq(fruity, banana), z3.MkEq(fruity, orange) }), true);
    }


    /*!
       \brief Create a list datatype.
    */
    public void list_example()
    {
        mk_context();

        Sort int_ty;
        ListSort int_list;        
        Expr nil, l1, l2, x, y, u, v;
        BoolExpr fml, fml1;

        Console.WriteLine("\nlist_example");

        int_ty = z3.MkIntSort();

        int_list = z3.MkListSort(z3.MkSymbol("int_list"), int_ty);
        
        nil = z3.MkConst(int_list.NilDecl);
        l1 = mk_binary_app(int_list.ConsDecl, mk_int(1), nil);
        l2 = mk_binary_app(int_list.ConsDecl, mk_int(2), nil);

        /* nil != cons(1, nil) */
        prove2(z3.MkNot(z3.MkEq(nil, l1)), true);

        /* cons(2,nil) != cons(1, nil) */
        prove2(z3.MkNot(z3.MkEq(l1, l2)), true);

        /* cons(x,nil) = cons(y, nil) => x = y */
        x = mk_var("x", int_ty);
        y = mk_var("y", int_ty);
        l1 = mk_binary_app(int_list.ConsDecl, x, nil);
        l2 = mk_binary_app(int_list.ConsDecl, y, nil);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(x, y)), true);

        /* cons(x,u) = cons(x, v) => u = v */
        u = mk_var("u", int_list);
        v = mk_var("v", int_list);
        l1 = mk_binary_app(int_list.ConsDecl, x, u);
        l2 = mk_binary_app(int_list.ConsDecl, y, v);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(u, v)), true);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(x, y)), true);

        /* is_nil(u) or is_cons(u) */
        prove2(z3.MkOr((BoolExpr) z3.MkApp(int_list.IsNilDecl, u), 
                       (BoolExpr)z3.MkApp(int_list.IsConsDecl, u)), true);

        /* occurs check u != cons(x,u) */
        prove2(z3.MkNot(z3.MkEq(u, l1)), true);

        /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
        fml1 = z3.MkEq(u, mk_binary_app(int_list.ConsDecl, mk_unary_app(int_list.HeadDecl, u), 
                          mk_unary_app(int_list.TailDecl, u)));
        fml = z3.MkImplies((BoolExpr) z3.MkApp(int_list.IsConsDecl, u), fml1);
        Console.WriteLine("Formula {0}", fml);

        prove2(fml, true);

        prove2(fml1, false);
    }



    /*!
       \brief Create a binary tree datatype.
    */
    public void tree_example()
    {
        mk_context();
        Sort cell;
        FuncDecl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
        Expr nil, l1, l2, x, y, u, v;
        BoolExpr fml, fml1;
        string[] head_tail = new string[] {"car", "cdr" };
        Sort[] sorts = new Sort[] { null, null };
        uint[] sort_refs = new uint[] { 0, 0 };
        Constructor nil_con, cons_con;

        Console.WriteLine("\ntree_example");

        nil_con = z3.MkConstructor("nil", "is_nil", null, null, null);
        cons_con = z3.MkConstructor("cons", "is_cons", head_tail, sorts, sort_refs);
        Constructor[] constructors = new Constructor[] { nil_con, cons_con };

        cell = z3.MkDatatypeSort("cell", constructors);

        nil_decl = nil_con.ConstructorDecl;
        is_nil_decl = nil_con.TesterDecl;
        cons_decl = cons_con.ConstructorDecl;
        is_cons_decl = cons_con.TesterDecl;
        FuncDecl[] cons_accessors = cons_con.AccessorDecls;
        car_decl = cons_accessors[0];
        cdr_decl = cons_accessors[1];

        nil = z3.MkConst(nil_decl);
        l1 = mk_binary_app(cons_decl, nil, nil);
        l2 = mk_binary_app(cons_decl, l1, nil);

        /* nil != cons(nil, nil) */
        prove2(z3.MkNot(z3.MkEq(nil, l1)), true);

        /* cons(x,u) = cons(x, v) => u = v */
        u = mk_var("u", cell);
        v = mk_var("v", cell);
        x = mk_var("x", cell);
        y = mk_var("y", cell);
        l1 = mk_binary_app(cons_decl, x, u);
        l2 = mk_binary_app(cons_decl, y, v);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(u, v)), true);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(x, y)), true);

        /* is_nil(u) or is_cons(u) */
        prove2(z3.MkOr((BoolExpr)z3.MkApp(is_nil_decl, u), (BoolExpr)z3.MkApp(is_cons_decl, u)), true);

        /* occurs check u != cons(x,u) */
        prove2(z3.MkNot(z3.MkEq(u, l1)), true);

        /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
        fml1 = z3.MkEq(u, mk_binary_app(cons_decl, mk_unary_app(car_decl, u), mk_unary_app(cdr_decl, u)));
        fml = z3.MkImplies((BoolExpr)z3.MkApp(is_cons_decl, u), fml1);
        Console.WriteLine("Formula {0}", fml);
        prove2(fml, true);

        prove2(fml1, false);

    }


    /*!
       \brief Create a forest of trees.
       
       forest ::= nil | cons(tree, forest)
       tree   ::= nil | cons(forest, forest)
    */

    public void forest_example()
    {
        mk_context();
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
        Symbol[] head_tail1 = new Symbol[] { z3.MkSymbol("head"), z3.MkSymbol("tail") };
        Sort[] sorts1 = new Sort[] { null, null };
        uint[] sort1_refs = new uint[] { 1, 0 }; // the first item points to a tree, the second to a forest

        Symbol[] head_tail2 = new Symbol[] { z3.MkSymbol("car"), z3.MkSymbol("cdr") };
        Sort[] sorts2 = new Sort[] { null, null };
        uint[] sort2_refs = new uint[] { 0, 0 }; // both items point to the forest datatype.
        Constructor nil1_con, cons1_con, nil2_con, cons2_con;
        Constructor[] constructors1 = new Constructor[2], constructors2 = new Constructor[2];
        Symbol[] sort_names = { z3.MkSymbol("forest"), z3.MkSymbol("tree") };

        Console.WriteLine("\nforest_example");

        /* build a forest */
        nil1_con = z3.MkConstructor(z3.MkSymbol("nil"), z3.MkSymbol("is_nil"), null, null, null);
        cons1_con = z3.MkConstructor(z3.MkSymbol("cons1"), z3.MkSymbol("is_cons1"), head_tail1, sorts1, sort1_refs);
        constructors1[0] = nil1_con;
        constructors1[1] = cons1_con;

        /* build a tree */
        nil2_con = z3.MkConstructor(z3.MkSymbol("nil2"), z3.MkSymbol("is_nil2"), null, null, null);
        cons2_con = z3.MkConstructor(z3.MkSymbol("cons2"), z3.MkSymbol("is_cons2"), head_tail2, sorts2, sort2_refs);
        constructors2[0] = nil2_con;
        constructors2[1] = cons2_con;


        Constructor[][] clists = new Constructor[][] { constructors1, constructors2 };

        Sort[] sorts = z3.MkDatatypeSorts(sort_names, clists);
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


        nil1 = z3.MkConst(nil1_decl);
        nil2 = z3.MkConst(nil2_decl);
        f1 = mk_binary_app(cons1_decl, nil2, nil1);
        t1 = mk_binary_app(cons2_decl, nil1, nil1);
        t2 = mk_binary_app(cons2_decl, f1, nil1);
        t3 = mk_binary_app(cons2_decl, f1, f1);
        t4 = mk_binary_app(cons2_decl, nil1, f1);
        f2 = mk_binary_app(cons1_decl, t1, nil1);
        f3 = mk_binary_app(cons1_decl, t1, f1);


        /* nil != cons(nil,nil) */
        prove2(z3.MkNot(z3.MkEq(nil1, f1)), true);
        prove2(z3.MkNot(z3.MkEq(nil2, t1)), true);


        /* cons(x,u) = cons(x, v) => u = v */
        u = mk_var("u", forest);
        v = mk_var("v", forest);
        x = mk_var("x", tree);
        y = mk_var("y", tree);
        l1 = mk_binary_app(cons1_decl, x, u);
        l2 = mk_binary_app(cons1_decl, y, v);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(u, v)), true);
        prove2(z3.MkImplies(z3.MkEq(l1, l2), z3.MkEq(x, y)), true);

        /* is_nil(u) or is_cons(u) */
        prove2(z3.MkOr((BoolExpr)z3.MkApp(is_nil1_decl, u), 
                       (BoolExpr)z3.MkApp(is_cons1_decl, u)), true);

        /* occurs check u != cons(x,u) */
        prove2(z3.MkNot(z3.MkEq(u, l1)), true);
    }


    /*!
       \brief Demonstrate how to use #Eval.
    */
    public void eval_example1()
    {
        Console.WriteLine("\neval_example1");
        mk_context();
        IntExpr x = mk_int_var("x");
        IntExpr y = mk_int_var("y");
        IntExpr two = mk_int(2);

        /* assert x < y */
        solver.Assert(z3.MkLt(x, y));

        /* assert x > 2 */
        solver.Assert(z3.MkGt(x, two));

        /* find model for the constraints above */
        Model model = null;
        if (Status.SATISFIABLE == solver.Check())
        {
            model = solver.Model;
            Console.WriteLine("{0}", model);
            Console.WriteLine("\nevaluating x+y");
            Expr v = model.Evaluate(z3.MkAdd(x, y));
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

    /*!
       \brief Demonstrate how to use #Eval on tuples.
    */
    public void eval_example2()
    {
        Console.WriteLine("\neval_example2");
        mk_context();
        Sort int_type = mk_int_type();        
        TupleSort tuple = z3.MkTupleSort(
         z3.MkSymbol("mk_tuple"),                        // name of tuple constructor
         new Symbol[] { z3.MkSymbol("first"), z3.MkSymbol("second") },    // names of projection operators
         new Sort[] { int_type, int_type } // types of projection operators
         );
        FuncDecl first = tuple.FieldDecls[0];     // declarations are for projections
        FuncDecl second = tuple.FieldDecls[1];
        Expr tup1 = z3.MkConst("t1", tuple);
        Expr tup2 = z3.MkConst("t2", tuple);
        /* assert tup1 != tup2 */
        solver.Assert(z3.MkNot(z3.MkEq(tup1, tup2)));
        /* assert first tup1 = first tup2 */
        solver.Assert(z3.MkEq(z3.MkApp(first, tup1), z3.MkApp(first, tup2)));

        /* find model for the constraints above */
        Model model = null;
        if (Status.SATISFIABLE == solver.Check())
        {
            model = solver.Model;
            Console.WriteLine("{0}",model);
            Console.WriteLine("evaluating tup1 {0}", (model.Evaluate(tup1)));
            Console.WriteLine("evaluating tup2 {0}", (model.Evaluate(tup2)));
            Console.WriteLine("evaluating second(tup2) {0}",
                      (model.Evaluate(z3.MkApp(second, tup2))));
        }
        else
        {
            Console.WriteLine("BUG, the constraints are satisfiable.");
        }
    }

    /*!
       \brief Demonstrate how to use #Push and #Pop to control 
       the size of models.

       Note: this test is specialized to 32-bit bitvectors.
    */
    public void check_small(BitVecExpr[] to_minimize)
    {

        Sort bv32 = mk_bv_type(32);

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
                    solver.Assert(z3.MkBVULE(to_minimize[i], mk_bv32(upper[i])));
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
                Console.WriteLine("{0}",solver.Model);

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
                        solver.Assert(z3.MkBVULE(to_minimize[i], mk_bv32(last_upper)));
                        some_work = true;
                        break;
                    }
                }
            }
            solver.Pop();
        }
    }

    /*!
       \brief Reduced-size model generation example.
    */
    public void find_small_model_example()
    {
        mk_context();
        BitVecExpr x = mk_bv_var("x", 32);
        BitVecExpr y = mk_bv_var("y", 32);
        BitVecExpr z = mk_bv_var("z", 32);
        solver.Assert(z3.MkBVULE(x, z3.MkBVAdd(y, z)));
        check_small(new BitVecExpr[] { x, y, z });
    }

    /*!
       \brief Simplifier example.
    */
    public void simplifier_example()
    {
        mk_context();
        IntExpr x = mk_int_var("x");
        IntExpr y = mk_int_var("y");
        IntExpr z = mk_int_var("z");
        IntExpr u = mk_int_var("u");

        Expr t1 = z3.MkAdd(x, z3.MkSub(y, z3.MkAdd(x, z)));
        Expr t2 = t1.Simplify(); 
        Console.WriteLine("{0} -> {1}", (t1), (t2));
    }

    /*!
       \brief Extract unsatisfiable core example
    */
    public void unsat_core_and_proof_example()
    {
        if (this.z3 != null)
        {
            this.z3.Dispose();
        }
        Dictionary<string, string> cfg = new Dictionary<string, string>() {
            { "PROOF_MODE", "2" } };
        this.z3 = new Context(cfg);
        this.solver = z3.MkSolver();

        BoolExpr pa = mk_bool_var("PredA");
        BoolExpr pb = mk_bool_var("PredB");
        BoolExpr pc = mk_bool_var("PredC");
        BoolExpr pd = mk_bool_var("PredD");
        BoolExpr p1 = mk_bool_var("P1");
        BoolExpr p2 = mk_bool_var("P2");
        BoolExpr p3 = mk_bool_var("P3");
        BoolExpr p4 = mk_bool_var("P4");
        BoolExpr[] assumptions = new BoolExpr[] { z3.MkNot(p1), z3.MkNot(p2), z3.MkNot(p3), z3.MkNot(p4) };
        BoolExpr f1 = z3.MkAnd(new BoolExpr[] { pa, pb, pc });
        BoolExpr f2 = z3.MkAnd(new BoolExpr[] { pa, z3.MkNot(pb), pc });
        BoolExpr f3 = z3.MkOr(z3.MkNot(pa), z3.MkNot(pc));
        BoolExpr f4 = pd;

        solver.Assert(z3.MkOr(f1, p1));
        solver.Assert(z3.MkOr(f2, p2));
        solver.Assert(z3.MkOr(f3, p3));
        solver.Assert(z3.MkOr(f4, p4));
        Status result = solver.Check(assumptions);

        if (result == Status.UNSATISFIABLE)
        {
            Console.WriteLine("unsat");
            Console.WriteLine("proof: {0}", solver.Proof);
            foreach (Expr c in solver.UnsatCore)
            {
                Console.WriteLine("{0}", c);
            }
        }
    }


    // CMW: get_implied_equalities is deprecated.

    ///*!
    //   \brief Extract implied equalities.
    //*/
#if false
    public void get_implied_equalities_example() {
       if (this.z3 != null)
        {
            this.z3.Dispose();
        }
        Config p = new Config();
        p.SetParam("ARITH_EQ_BOUNDS","true");
        this.z3 = new Context(p);

        Sort int_sort = z3.MkIntSort();
        Expr a = mk_int_var("a");
        Expr b = mk_int_var("b");
        Expr c = mk_int_var("c");
        Expr d = mk_int_var("d");
        FuncDecl f = z3.MkFuncDecl("f", int_sort, int_sort);
        Expr fa = z3.MkApp(f,a);
        Expr fb = z3.MkApp(f,b);
        Expr fc = z3.MkApp(f,c);
        Expr[] Exprs = new Expr[]{ a, b, c, d, fa, fb, fc };
        uint[] class_ids;

        solver.Assert(z3.MkEq(a, b));
        solver.Assert(z3.MkEq(b, c));
        solver.Assert(z3.MkLe((ArithExpr)fc, (ArithExpr)a));
        solver.Assert(z3.MkLe((ArithExpr)b, (ArithExpr)fb));
        int num_Exprs = Exprs.Length;

        z3.GetImpliedEqualities(Exprs, out class_ids);
        for (int i = 0; i < num_Exprs; ++i) {
            Console.WriteLine("Class {0} |-> {1}", Exprs[i], class_ids[i]);
        }
    }
#endif

    static void Main()
    {
        Log.Open("z3.log");
        TestManaged test = new TestManaged();
        Log.Append("mk_quantifier");
	    test.mk_quantifier();
        Log.Append("simple_example");
        test.simple_example();
        Log.Append("find_model_example1");
        test.find_model_example1();
        Log.Append("find_model_example2");
        test.find_model_example2();
        Log.Append("prove_example1");
        test.prove_example1();
        Log.Append("prove_example2");
        test.prove_example2();
        Log.Append("push_pop_example1");
        test.push_pop_example1();
        Log.Append("quantifier_example1");
        test.quantifier_example1();
        Log.Append("quantifier_example1_abs");
        test.quantifier_example1_abs();
        Log.Append("array_example1");
        test.array_example1();
        Log.Append("array_example2");
        test.array_example2();
        Log.Append("tuple_example");
        test.tuple_example();
        Log.Append("bitvector_example1");
        test.bitvector_example1();
        Log.Append("bitvector_example2");
        test.bitvector_example2();
        Log.Append("parser_example1");
        test.parser_example1();
        Log.Append("parser_example2");
        test.parser_example2();
        Log.Append("parser_example3");
        test.parser_example3();
        Log.Append("parser_example4");
        test.parser_example4();
        Log.Append("parser_example5");
        test.parser_example5();
        Log.Append("ite_example");
        test.ite_example();
        Log.Append("enum_example");
        test.enum_example();
        Log.Append("list_example");
        test.list_example();
        Log.Append("tree_example");
        test.tree_example();
        Log.Append("forest_example");
        test.forest_example();        
        Log.Append("eval_example1");
        test.eval_example1();
        Log.Append("eval_example2");
        test.eval_example2();
        Log.Append("find_small_model_example");
        test.find_small_model_example();
        Log.Append("simplifier_example");
        test.simplifier_example();
        Log.Append("unsat_core_and_proof_example");
        test.unsat_core_and_proof_example();

        // CMW: these are deprecated.
        //Log.Append("get_implied_equalities_example");
        //test.get_implied_equalities_example();
        
        test.z3.Dispose();
    }
}

/*@}*/






