#include "model_based_opt.h"
#include "util.h"
#include "uint_set.h"

typedef opt::model_based_opt::var var;

static void add_ineq(opt::model_based_opt& mbo, unsigned x, int a, int k, opt::ineq_type rel) {
    vector<var> vars;
    vars.push_back(var(x, rational(a)));
    mbo.add_constraint(vars, rational(k), rel);
}

static void add_ineq(opt::model_based_opt& mbo, 
                     unsigned x, int a, 
                     unsigned y, int b, int k, 
                     opt::ineq_type rel) {
    vector<var> vars;
    vars.push_back(var(x, rational(a)));
    vars.push_back(var(y, rational(b)));
    mbo.add_constraint(vars, rational(k), rel);
}

static void add_ineq(opt::model_based_opt& mbo, 
                     unsigned x, int a, 
                     unsigned y, int b, 
                     unsigned z, int c, int k, 
                     opt::ineq_type rel) {
    vector<var> vars;
    vars.push_back(var(x, rational(a)));
    vars.push_back(var(y, rational(b)));
    vars.push_back(var(z, rational(c)));
    mbo.add_constraint(vars, rational(k), rel);
}

static void add_random_ineq(opt::model_based_opt& mbo,
                            random_gen& r,
                            svector<int>  const& values,
                            unsigned max_vars,
                            unsigned max_coeff) {
    unsigned num_vars = values.size();
    uint_set used_vars;
    vector<var> vars;
    int value = 0;
    for (unsigned i = 0; i < max_vars; ++i) {
        unsigned x = r(num_vars);
        if (used_vars.contains(x)) {
            continue;
        }
        used_vars.insert(x);
        int coeff = r(max_coeff + 1);
        if (coeff == 0) {
            continue;
        }
        unsigned sign = r(2);
		coeff = sign == 0 ? coeff : -coeff;
        vars.push_back(var(x, rational(coeff)));
        value += coeff*values[x];
    }
    unsigned abs_value = value < 0 ? - value : value;
    // value + k <= 0
    // k <= - value
    // range for k is 2*|value|
    // k <= - value - range
    opt::ineq_type rel = opt::t_le;

    int coeff = 0;
    if (r(4) == 0) {
        rel = opt::t_eq;
        coeff = -value;
    }
    else {
        if (abs_value > 0) {
            coeff = -value - r(2*abs_value);
        }
        else {
            coeff = 0;
        }
        if (coeff != -value && r(3) == 0) {
            rel = opt::t_lt;
        }   
    }
    mbo.add_constraint(vars, rational(coeff), rel);
}
                        
static void check_random_ineqs(random_gen& r, unsigned num_vars, unsigned max_value, unsigned num_ineqs, unsigned max_vars, unsigned max_coeff) {
    opt::model_based_opt mbo;
    svector<int> values;
    for (unsigned i = 0; i < num_vars; ++i) {
        values.push_back(r(max_value + 1));
        mbo.add_var(rational(values.back()));
    }
    for (unsigned i = 0; i < num_ineqs; ++i) {
        add_random_ineq(mbo, r, values, max_vars, max_coeff);
    }

    vector<var> vars;
    vars.reset();
    vars.push_back(var(0, rational(2)));
    vars.push_back(var(1, rational(-2)));
    mbo.set_objective(vars, rational(0));

    mbo.display(std::cout);
    opt::inf_eps value = mbo.maximize();    
    std::cout << "optimal: " << value << "\n";
    mbo.display(std::cout);
    for (unsigned i = 0; i < values.size(); ++i) {
        std::cout << i << ": " << values[i] << " -> " << mbo.get_value(i) << "\n";
    }
}

static void check_random_ineqs() {
    random_gen r(1);

    for (unsigned i = 0; i < 1009; ++i) {
        check_random_ineqs(r, 4, 5, 5, 3, 6);
    }
}

// test with upper bounds
static void test1() {
    opt::model_based_opt mbo;
    vector<var> vars;
    unsigned x = mbo.add_var(rational(2));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));

    add_ineq(mbo, x, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, z, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, z, 1, u, -1, 1, opt::t_le);
    add_ineq(mbo, u, 1, -6, opt::t_le);

    vars.reset();
    vars.push_back(var(x, rational(2)));
    mbo.set_objective(vars, rational(0));

    opt::inf_eps value = mbo.maximize();    
    std::cout << value << "\n";
    std::cout << "x: " << mbo.get_value(x) << "\n";
    std::cout << "y: " << mbo.get_value(y) << "\n";
    std::cout << "z: " << mbo.get_value(z) << "\n";
    std::cout << "u: " << mbo.get_value(u) << "\n";
}

// test with lower bounds
static void test2() {
    opt::model_based_opt mbo;
    vector<var> vars;
    unsigned x = mbo.add_var(rational(5));
    unsigned y = mbo.add_var(rational(4));
    unsigned z = mbo.add_var(rational(3));
    unsigned u = mbo.add_var(rational(2));

    add_ineq(mbo, x, -1, y, 1, 0, opt::t_le);
    add_ineq(mbo, x, -1, z, 1, 0, opt::t_le);
    add_ineq(mbo, y, -1, u, 1, 0, opt::t_le);
    add_ineq(mbo, z, -1, u, 1, 1, opt::t_le);
    add_ineq(mbo, u, -1, -6, opt::t_le);

    vars.reset();
    vars.push_back(var(x, rational(-2)));
    mbo.set_objective(vars, rational(0));

    opt::inf_eps value = mbo.maximize();    
    std::cout << value << "\n";
}

// test unbounded
static void test3() {
    opt::model_based_opt mbo;
    vector<var> vars;
    unsigned x = mbo.add_var(rational(2));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));

    add_ineq(mbo, x, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, z, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, z, 1, u, -1, 1, opt::t_le);

    vars.reset();
    vars.push_back(var(x, rational(2)));
    mbo.set_objective(vars, rational(0));

    opt::inf_eps value = mbo.maximize();    
    std::cout << value << "\n";

}

// test strict
static void test4() {
    opt::model_based_opt mbo;
    vector<var> vars;
    unsigned x = mbo.add_var(rational(2));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));

    add_ineq(mbo, x, 1, y, -1, 0, opt::t_lt);
    add_ineq(mbo, x, 1, z, -1, 0, opt::t_lt);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, z, 1, u, -1, 1, opt::t_le);
    add_ineq(mbo, u, 1, -6, opt::t_le);

    vars.reset();
    vars.push_back(var(x, rational(2)));
    mbo.set_objective(vars, rational(0));

    opt::inf_eps value = mbo.maximize();    
    std::cout << value << "\n";
    std::cout << "x: " << mbo.get_value(x) << "\n";
    std::cout << "y: " << mbo.get_value(y) << "\n";
    std::cout << "z: " << mbo.get_value(z) << "\n";
    std::cout << "u: " << mbo.get_value(u) << "\n";
}

static void test5() {
    opt::model_based_opt mbo;
    unsigned x = mbo.add_var(rational(2));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));

    add_ineq(mbo, x, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, z, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, z, 1, u, -1, 1, opt::t_le);

    unsigned vars[2] = { y, z };
    mbo.project(1, vars);    
    mbo.display(std::cout);

    mbo.project(1, vars);    
    mbo.display(std::cout);

    mbo.project(1, vars+1);
    mbo.display(std::cout);

    vector<opt::model_based_opt::row> rows;
    mbo.get_live_rows(rows);
}


static void test6() {
    opt::model_based_opt mbo;
    unsigned x0 = mbo.add_var(rational(1));
    unsigned x = mbo.add_var(rational(2));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));
    unsigned v = mbo.add_var(rational(6));
    unsigned w = mbo.add_var(rational(6));

    add_ineq(mbo, x0, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, z, -1, 1, opt::t_le);
    add_ineq(mbo, y, 1, v, -1, 1, opt::t_le);
    add_ineq(mbo, y, 1, w, -1, 1, opt::t_le);

    mbo.display(std::cout);
    mbo.project(1, &y);
    mbo.display(std::cout);
}

static void test7() {
    opt::model_based_opt mbo;
    unsigned x0 = mbo.add_var(rational(2));
    unsigned x = mbo.add_var(rational(1));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));
    unsigned v = mbo.add_var(rational(6));
    unsigned w = mbo.add_var(rational(6));

    add_ineq(mbo, x0, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, y, -1, 0, opt::t_lt);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, z, -1, 1, opt::t_le);
    add_ineq(mbo, y, 1, v, -1, 1, opt::t_le);
    add_ineq(mbo, y, 1, w, -1, 1, opt::t_lt);

    mbo.display(std::cout);
    mbo.project(1, &y);
    mbo.display(std::cout);
}

static void test8() {
    opt::model_based_opt mbo;
    unsigned x0 = mbo.add_var(rational(2));
    unsigned x = mbo.add_var(rational(1));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));
    unsigned v = mbo.add_var(rational(6));
    unsigned w = mbo.add_var(rational(6));

    add_ineq(mbo, x0, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, y, -1, 0, opt::t_lt);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, z, -1, 1, opt::t_le);
    add_ineq(mbo, y, 1, v, -1, 1, opt::t_le);

    mbo.display(std::cout);
    mbo.project(1, &y);
    mbo.display(std::cout);
}


static void test9() {
    opt::model_based_opt mbo;
    unsigned x0 = mbo.add_var(rational(2), true);
    unsigned x = mbo.add_var(rational(1), true);
    unsigned y = mbo.add_var(rational(3), true);
    unsigned z = mbo.add_var(rational(4), true);
    unsigned u = mbo.add_var(rational(5), true);
    unsigned v = mbo.add_var(rational(6), true);

    add_ineq(mbo, x0, 1, y, -1, 0, opt::t_le);
    add_ineq(mbo, x, 1, y, -1, 0, opt::t_lt);
    add_ineq(mbo, y, 1, u, -1, 0, opt::t_le);
    add_ineq(mbo, y, 1, z, -1, 1, opt::t_le);
    add_ineq(mbo, y, 1, v, -1, 1, opt::t_le);

    mbo.display(std::cout);
    mbo.project(1, &y);
    mbo.display(std::cout);
}


static void test10() {
    opt::model_based_opt mbo;
    unsigned x0 = mbo.add_var(rational(2), true);
    unsigned x = mbo.add_var(rational(1), true);
    unsigned y = mbo.add_var(rational(3), true);
    unsigned z = mbo.add_var(rational(4), true);
    unsigned u = mbo.add_var(rational(5), true);
    unsigned v = mbo.add_var(rational(6), true);

    add_ineq(mbo, x0, 1, y, -2, 0, opt::t_le);
    add_ineq(mbo, x, 1, y, -2, 0, opt::t_lt);
    add_ineq(mbo, y, 3, u, -4, 0, opt::t_le);
    add_ineq(mbo, y, 3, z, -5, 1, opt::t_le);
    add_ineq(mbo, y, 3, v, -6, 1, opt::t_le);

    mbo.display(std::cout);
    mbo.project(1, &y);
    mbo.display(std::cout);
    mbo.project(1, &x0);
    mbo.display(std::cout);
}

// test with mix of upper and lower bounds

void tst_model_based_opt() {
    test10();
    return;
    check_random_ineqs();
    test1();
    test2();
    test3();
    test4();
    test5();
    test6();
    test7();
    test8();
    test9();
}
