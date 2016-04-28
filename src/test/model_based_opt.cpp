#include "model_based_opt.h"

typedef opt::model_based_opt::var var;

static void add_ineq(opt::model_based_opt& mbo, unsigned x, int a, unsigned y, int b, int k, opt::ineq_type rel) {
    vector<var> vars;
    vars.push_back(var(x, rational(a)));
    vars.push_back(var(y, rational(b)));
    mbo.add_constraint(vars, rational(k), rel);
}

static void add_ineq(opt::model_based_opt& mbo, unsigned x, int a, int k, opt::ineq_type rel) {
    vector<var> vars;
    vars.push_back(var(x, rational(a)));
    mbo.add_constraint(vars, rational(k), rel);
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

    rational value;
    opt::bound_type bound = mbo.maximize(value);    
    std::cout << bound << ": " << value << "\n";
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

    rational value;
    opt::bound_type bound = mbo.maximize(value);    
    std::cout << bound << ": " << value << "\n";
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

    rational value;
    opt::bound_type bound = mbo.maximize(value);    
    std::cout << bound << ": " << value << "\n";
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

    rational value;
    opt::bound_type bound = mbo.maximize(value);    
    std::cout << bound << ": " << value << "\n";
}

// test with mix of upper and lower bounds

void tst_model_based_opt() {
    test1();
    test2();
    test3();
    test4();
}
