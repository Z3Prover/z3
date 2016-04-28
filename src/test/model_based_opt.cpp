#include "model_based_opt.h"

static void test1() {
    opt::model_based_opt mbo;
    typedef opt::model_based_opt::var var;
    vector<var> vars;
    unsigned x = mbo.add_var(rational(2));
    unsigned y = mbo.add_var(rational(3));
    unsigned z = mbo.add_var(rational(4));
    unsigned u = mbo.add_var(rational(5));

    vars.reset();
    vars.push_back(var(x, rational(1)));
    vars.push_back(var(y, rational(-1)));
    mbo.add_constraint(vars, rational(0), opt::t_le);

    vars.reset();
    vars.push_back(var(x, rational(1)));
    vars.push_back(var(z, rational(-1)));
    mbo.add_constraint(vars, rational(0), opt::t_le);

    vars.reset();
    vars.push_back(var(y, rational(1)));
    vars.push_back(var(u, rational(-1)));
    mbo.add_constraint(vars, rational(0), opt::t_le);

    vars.reset();
    vars.push_back(var(z, rational(1)));
    vars.push_back(var(u, rational(-1)));
    mbo.add_constraint(vars, rational(-1), opt::t_le);

    vars.reset();
    vars.push_back(var(u, rational(1)));
    mbo.add_constraint(vars, rational(4), opt::t_le);

    vars.reset();
    vars.push_back(var(x, rational(2)));
    mbo.set_objective(vars, rational(0));

    rational value;
    opt::bound_type bound = mbo.maximize(value);
    
    std::cout << bound << ": " << value << "\n";
    
}

void tst_model_based_opt() {
    test1();
}
