#include "hilbert_basis.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"
#include "arith_decl_plugin.h"
#include "quant_tactics.h"
#include "tactic.h"
#include "tactic2solver.h"
#include "solver.h"
#include <signal.h>
#include <time.h>
#include <sstream>

static bool g_use_ordered_support = false;
static bool g_use_ordered_subsumption = false;
static bool g_use_support = false;

class hilbert_basis_validate {
    ast_manager& m;

    void validate_solution(hilbert_basis& hb, vector<rational> const& v, bool is_initial);

    rational eval_ineq(hilbert_basis& hb, unsigned idx, vector<rational> const& v, bool& is_eq) {
        vector<rational> w;
        rational bound;
        hb.get_ge(idx, w, bound, is_eq);
        rational sum(0);
        for (unsigned j = 0; j < v.size(); ++j) {
            sum += w[j]*v[j];
        }
        sum -= bound;
        return sum;
    }

public:
        
    hilbert_basis_validate(ast_manager& m);

    expr_ref mk_validate(hilbert_basis& hb);

};


hilbert_basis_validate::hilbert_basis_validate(ast_manager& m): 
    m(m) {
}

void hilbert_basis_validate::validate_solution(hilbert_basis& hb, vector<rational> const& v, bool is_initial) {
    unsigned sz = hb.get_num_ineqs();
    rational bound;
    for (unsigned i = 0; i < sz; ++i) {
        bool is_eq;
        vector<rational> w;
        rational bound;
        hb.get_ge(i, w, bound, is_eq);
        rational sum(0);
        for (unsigned j = 0; j < v.size(); ++j) {
            sum += w[j]*v[j];
        }
        if (sum >= bound && !is_eq) {
            continue;
        }
        if (sum == bound && is_eq) {
            continue;
        }
        // homogeneous solutions should be non-negative.
        if (!is_initial && sum.is_nonneg()) {
            continue;
        }

        // validation failed.
        std::cout << "validation failed\n";
        std::cout << "constraint: ";
        for (unsigned j = 0; j < v.size(); ++j) {
            std::cout << v[j] << " ";
        }
        std::cout << (is_eq?" = ":" >= ") << bound << "\n";
        std::cout << "vector:     ";
        for (unsigned j = 0; j < w.size(); ++j) {
            std::cout << w[j] << " ";
        }
        std::cout << "\n";
        std::cout << "sum: " << sum << "\n";
    }        
}

expr_ref hilbert_basis_validate::mk_validate(hilbert_basis& hb) {
    arith_util a(m);
    unsigned sz = hb.get_basis_size();
    vector<rational> v;

    // check that claimed solution really satisfies inequalities:        
    for (unsigned i = 0; i < sz; ++i) {
        bool is_initial;
        hb.get_basis_solution(i, v, is_initial);
        validate_solution(hb, v, is_initial);
    }

    // check that solutions satisfying inequalities are in solution.
    // build a formula that says solutions to linear inequalities
    // coincide with linear combinations of basis.
    vector<expr_ref_vector> offsets, increments;
    expr_ref_vector xs(m), vars(m);
    expr_ref var(m);
    svector<symbol> names;
    sort_ref_vector sorts(m);

#define mk_mul(_r,_x) (_r.is_one()?((expr*)_x):((expr*)a.mk_mul(a.mk_numeral(_r,true),_x)))
    

    for (unsigned i = 0; i < sz; ++i) {
        bool is_initial;
        hb.get_basis_solution(i, v, is_initial);

        for (unsigned j = 0; xs.size() < v.size(); ++j) {
            xs.push_back(m.mk_fresh_const("x", a.mk_int()));
        }


        if (is_initial) {
            expr_ref_vector tmp(m);
            for (unsigned j = 0; j < v.size(); ++j) {
                tmp.push_back(a.mk_numeral(v[j], true));
            }
            offsets.push_back(tmp);
        }
        else {
            var = m.mk_var(vars.size(), a.mk_int());
            expr_ref_vector tmp(m);
            for (unsigned j = 0; j < v.size(); ++j) {
                tmp.push_back(mk_mul(v[j], var));
            }
            std::stringstream name;
            name << "u" << i;
            increments.push_back(tmp);
            vars.push_back(var);
            names.push_back(symbol(name.str().c_str()));
            sorts.push_back(a.mk_int());
        }
    }

    expr_ref_vector bounds(m);
    for (unsigned i = 0; i < vars.size(); ++i) {
        bounds.push_back(a.mk_ge(vars[i].get(), a.mk_numeral(rational(0), true)));
    }
    expr_ref_vector fmls(m);
    expr_ref fml(m), fml1(m), fml2(m);
    for (unsigned i = 0; i < offsets.size(); ++i) {
        expr_ref_vector eqs(m);
        eqs.append(bounds);
        for (unsigned j = 0; j < xs.size(); ++j) {
            expr_ref_vector sum(m);
            sum.push_back(offsets[i][j].get());
            for (unsigned k = 0; k < increments.size(); ++k) {
                sum.push_back(increments[k][j].get());
            }
            eqs.push_back(m.mk_eq(xs[j].get(), a.mk_add(sum.size(), sum.c_ptr())));
        }
        fml = m.mk_and(eqs.size(), eqs.c_ptr());
        if (!names.empty()) {
            fml = m.mk_exists(names.size(), sorts.c_ptr(), names.c_ptr(), fml);
        }
        fmls.push_back(fml);
    }
    fml1 = m.mk_or(fmls.size(), fmls.c_ptr());
    fmls.reset();
    
    sz = hb.get_num_ineqs();
    for (unsigned i = 0; i < sz; ++i) {
        bool is_eq;
        vector<rational> w;
        rational bound;
        hb.get_ge(i, w, bound, is_eq);
        expr_ref_vector sum(m);
        for (unsigned j = 0; j < w.size(); ++j) {
            if (!w[j].is_zero()) {
                sum.push_back(mk_mul(w[j], xs[j].get()));
            }
        }
        expr_ref lhs(m), rhs(m);
        lhs = a.mk_add(sum.size(), sum.c_ptr());
        rhs = a.mk_numeral(bound, true);
        if (is_eq) {
            fmls.push_back(a.mk_eq(lhs, rhs));
        }
        else {
            fmls.push_back(a.mk_ge(lhs, rhs));
        }
    }
    fml2 = m.mk_and(fmls.size(), fmls.c_ptr());
    fml = m.mk_eq(fml1, fml2);
    
    bounds.reset();
    for (unsigned i = 0; i < xs.size(); ++i) {
        if (!hb.get_is_int(i)) {
            bounds.push_back(a.mk_ge(xs[i].get(), a.mk_numeral(rational(0), true)));
        }
    }
    if (!bounds.empty()) {
        fml = m.mk_implies(m.mk_and(bounds.size(), bounds.c_ptr()), fml);
    }
    return fml;

}


hilbert_basis* g_hb = 0;
static double  g_start_time;

static void display_statistics(hilbert_basis& hb) {
    double time = static_cast<double>(clock()) - g_start_time;
    statistics st;
    hb.collect_statistics(st);
    st.display(std::cout);
    std::cout << "time: " << (time / CLOCKS_PER_SEC) << " secs\n";
}

static void on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);    
    display_statistics(*g_hb);
    raise(SIGINT);
}

#if 0
static void validate_sat(hilbert_basis& hb) {
    ast_manager m;
    reg_decl_plugins(m);
    hilbert_basis_validate val(m);

    expr_ref fml = val.mk_validate(hb);

    return;

    std::cout << mk_pp(fml, m) << "\n";

    fml = m.mk_not(fml);
    params_ref p;
    tactic_ref tac = mk_lra_tactic(m, p);
    ref<solver> sol = mk_tactic2solver(m, tac.get(), p);
    sol->assert_expr(fml);
    lbool r = sol->check_sat(0,0);
    std::cout << r << "\n";
}
#endif

static void saturate_basis(hilbert_basis& hb) {
    signal(SIGINT, on_ctrl_c);
    g_hb = &hb;
    g_start_time = static_cast<double>(clock());
    hb.set_use_ordered_support(g_use_ordered_support);
    hb.set_use_support(g_use_support);
    hb.set_use_ordered_subsumption(g_use_ordered_subsumption);
    lbool is_sat = hb.saturate();

    switch(is_sat) {
    case l_true:  
        std::cout << "sat\n"; 
        hb.display(std::cout);
        //validate_sat(hb);
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        break;
    case l_undef: 
        std::cout << "undef\n"; 
        break;       
    }
    display_statistics(hb);
}


/**
   n         - number of variables.
   k         - subset of variables to be non-zero
   bound     - numeric value of upper and lower bound
   num_ineqs - number of inequalities to create
*/
static void gorrila_test(unsigned seed, unsigned n, unsigned k, unsigned bound, unsigned num_ineqs) {
    std::cout << "Gorrila test\n";
    random_gen rand(seed);
    hilbert_basis hb;
    SASSERT(0 < bound);
    SASSERT(k <= n);
    int ibound = static_cast<int>(bound);
    for (unsigned i = 0; i < num_ineqs; ++i) {
        vector<rational> nv;
        nv.resize(n);
        rational a0;
        unsigned num_selected = 0;
        while (num_selected < k) {
            unsigned s = rand(n);
            if (nv[s].is_zero()) {
                nv[s] = rational(ibound - static_cast<int>(rand(2*bound+1)));
                if (!nv[s].is_zero()) {
                    ++num_selected;
                }
            }
        }
        a0 = rational(ibound - static_cast<int>(rand(2*bound+1)));
        hb.add_ge(nv, a0);
    }    
    hb.display(std::cout << "Saturate\n");
    saturate_basis(hb);
}

static vector<rational> vec(int i, int j) {
    vector<rational> nv;
    nv.resize(2);
    nv[0] = rational(i);
    nv[1] = rational(j);
    return nv;
}

static vector<rational> vec(int i, int j, int k) {
    vector<rational> nv;
    nv.resize(3);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    return nv;
}

static vector<rational> vec(int i, int j, int k, int l) {
    vector<rational> nv;
    nv.resize(4);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    nv[3] = rational(l);
    return nv;
}

static vector<rational> vec(int i, int j, int k, int l, int m) {
    vector<rational> nv;
    nv.resize(5);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    nv[3] = rational(l);
    nv[4] = rational(m);
    return nv;
}

static vector<rational> vec(int i, int j, int k, int l, int x, int y, int z) {
    vector<rational> nv;
    nv.resize(7);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    nv[3] = rational(l);
    nv[4] = rational(x);
    nv[5] = rational(y);
    nv[6] = rational(z);
    return nv;
}




// example 9, Ajili, Contenjean
// x + y - 2z = 0
// x - z = 0
// -y + z <= 0

static void tst1() {
    hilbert_basis hb;
    hb.add_eq(vec(1,1,-2));
    hb.add_eq(vec(1,0,-1));
    hb.add_le(vec(0,1,-1));
    saturate_basis(hb);
}


// example 10, Ajili, Contenjean
// 23x - 12y - 9z <= 0
// x   - 8y  - 8z <= 0
void tst2() {
    hilbert_basis hb;

    hb.add_eq(vec(-23,12,9));
    hb.add_eq(vec(-1,8,8));

    saturate_basis(hb);
}

// example 6, Ajili, Contenjean
// 3x + 2y - z - 2u <= 0
static void tst3() {
    hilbert_basis hb;
    hb.add_le(vec(3,2,-1,-2));
    saturate_basis(hb);
}

#define R rational

// Sigma_1, table 1, Ajili, Contejean
static void tst4() {
    hilbert_basis hb;
    hb.add_le(vec( 0,-2, 1, 3, 2,-2, 3), R(3));
    hb.add_le(vec(-1, 7, 0, 1, 3, 5,-4), R(2));
    hb.add_le(vec( 0,-1, 1,-1,-1, 0, 0), R(2));
    hb.add_le(vec(-2, 0, 1, 4, 0, 0,-2), R(1));
    hb.add_le(vec(-3, 2,-2, 2,-4,-1, 0), R(8));
    hb.add_le(vec( 3,-2, 2,-2, 4, 1, 0), R(3));
    hb.add_le(vec( 1, 0, 0,-1, 0, 1, 0), R(4));
    hb.add_le(vec( 1,-2, 0, 0, 0, 0, 0), R(2));
    hb.add_le(vec( 1, 1, 0, 0,-1, 0, 1), R(4));
    hb.add_le(vec( 1, 0, 0, 0,-1, 0, 0), R(9));
    saturate_basis(hb);
}

// Sigma_2 table 1,  Ajili, Contejean
static void tst5() {
    hilbert_basis hb;
    hb.add_le(vec( 1, 2,-1, 1), R(3));
    hb.add_le(vec( 2, 4, 1, 2), R(12));
    hb.add_le(vec( 1, 4, 2, 1), R(9));
    hb.add_le(vec( 1, 1, 0,-1), R(10));
    hb.add_le(vec( 1, 1,-1, 0), R(6));
    hb.add_le(vec( 1,-1, 0, 0), R(0));
    hb.add_le(vec( 0, 0, 1,-1), R(2));
    saturate_basis(hb);
}

// Sigma_3 table 1,  Ajili, Contejean
static void tst6() {
    hilbert_basis hb;
    hb.add_le(vec( 4, 3, 0), R(6));
    hb.add_le(vec(-3,-4, 0), R(-1));
    hb.add_le(vec( 4, 0,-3), R(3));
    hb.add_le(vec(-3, 0, 4), R(7));
    hb.add_le(vec( 4, 0,-3), R(23));
    hb.add_le(vec( 0,-3, 4), R(11));
    saturate_basis(hb);
}

// Sigma_4 table 1,  Ajili, Contejean
static void tst7() {
    hilbert_basis hb;
    hb.add_eq(vec( 1, 1, 1, 0),  R(5));
    hb.add_le(vec( 2, 1, 0, 1),  R(6));
    hb.add_le(vec( 1, 2, 1, 1),  R(7));
    hb.add_le(vec( 1, 3,-1, 2),  R(8));
    hb.add_le(vec( 1, 2,-9,-12), R(-11));
    hb.add_le(vec( 0, 0,-1, 3),  R(10));
    saturate_basis(hb);
}


// Sigma_5 table 1,  Ajili, Contejean
static void tst8() {
    hilbert_basis hb;
    hb.add_le(vec( 2, 1, 1), R(2));
    hb.add_le(vec( 1, 2, 3), R(5));
    hb.add_le(vec( 2, 2, 3), R(6));
    hb.add_le(vec( 1,-1,-3), R(-2));
    saturate_basis(hb);
}

// Sigma_6 table 1,  Ajili, Contejean
static void tst9() {
    hilbert_basis hb;
    hb.add_le(vec( 1, 2, 3), R(11));
    hb.add_le(vec( 2, 2, 5), R(13));
    hb.add_le(vec( 1,-1,-11), R(3));
    saturate_basis(hb);
}

// Sigma_7 table 1,  Ajili, Contejean
static void tst10() {
    hilbert_basis hb;
    hb.add_le(vec( 1,-1,-1,-3), R(2));
    hb.add_le(vec(-2, 3, 3,-5), R(3));
    saturate_basis(hb);
}

// Sigma_8 table 1,  Ajili, Contejean
static void tst11() {
    hilbert_basis hb;
    hb.add_le(vec( 7,-2,11, 3, -5), R(5));
    saturate_basis(hb);
}

// Sigma_9 table 1,  Ajili, Contejean
static void tst12() {
    hilbert_basis hb;
    hb.add_eq(vec( 1,-2,-3,4), R(0));
    hb.add_le(vec(100,45,-78,-67), R(0));
    saturate_basis(hb);
}

// Sigma_10 table 1,  Ajili, Contejean
static void tst13() {
    hilbert_basis hb;
    hb.add_le(vec( 23, -56, -34, 12, 11), R(0));
    saturate_basis(hb);
}

// Sigma_11 table 1,  Ajili, Contejean
static void tst14() {
    hilbert_basis hb;
    hb.add_eq(vec(1, 0, -4, 8), R(2));
    hb.add_le(vec(12,19,-11,-7), R(-7));
    saturate_basis(hb);
}

static void tst15() {
    hilbert_basis hb;
    hb.add_le(vec(1, 0), R(1));
    hb.add_le(vec(0, 1), R(1));
    saturate_basis(hb);
}

static void tst16() {
    hilbert_basis hb;
    hb.add_le(vec(1, 0), R(100));
    saturate_basis(hb);
}

static void tst17() {
    hilbert_basis hb;
    hb.add_eq(vec(1,  0), R(0));
    hb.add_eq(vec(-1, 0), R(0));
    hb.add_eq(vec(0,  2), R(0));
    hb.add_eq(vec(0, -2), R(0));
    saturate_basis(hb);

}

static void tst18() {
    hilbert_basis hb;
    hb.add_eq(vec(0, 1), R(0));
    hb.add_eq(vec(1, -1), R(2));
    saturate_basis(hb);    
}

static void tst19() {
    hilbert_basis hb;
    hb.add_eq(vec(0,  1, 0), R(0));
    hb.add_eq(vec(1, -1, 0), R(2));
    saturate_basis(hb);    
}

static void test_A_5_5_3() {
    hilbert_basis hb;
    for (unsigned i = 0; i < 15; ++i) {
        vector<rational> v;
        for (unsigned j = 0; j < 5; ++j) {
            for (unsigned k = 0; k < 15; ++k) {
                v.push_back(rational(k == i));                
            }
        }
        hb.add_ge(v, R(0));
    }
    for (unsigned i = 1; i <= 15; ++i) {
        vector<rational> v;
        for (unsigned k = 1; k <= 5; ++k) {
            for (unsigned l = 1; l <= 5; ++l) {
                for (unsigned j = 1; j <= 3; ++j) {
                    bool one = ((j*k <= i) && (((i - j) % 3) == 0)); // fixme
                    v.push_back(rational(one));
                }
            }
        }
        hb.add_ge(v, R(0));
    }
    // etc.
    saturate_basis(hb);
}

void tst_hilbert_basis() {
    std::cout << "hilbert basis test\n";
//    tst3();
//    return;

    g_use_ordered_support = true;

    test_A_5_5_3();
    return;

    tst18();
    return;

    tst19();
    return;
    tst17();

    if (true) {
        tst1();
        tst2();
        tst3();
        tst4();
        tst4();
        tst4();
       tst4();
       tst4();
       tst4();
        tst5();
        tst6();
        tst7();
        tst8();
        tst9();
        tst10();
        tst11();
        tst12();
        tst13();
        tst14();
        tst15();
        tst16();
        gorrila_test(0, 4, 3, 20, 5);
        gorrila_test(1, 4, 3, 20, 5);
        //gorrila_test(2, 4, 3, 20, 5);
        //gorrila_test(0, 4, 2, 20, 5);
        //gorrila_test(0, 4, 2, 20, 5);
    }
    else {
        gorrila_test(0, 10, 7, 20, 11);
    }

    return;
    std::cout << "ordered support\n";
    g_use_ordered_support = true;
    tst4();

    std::cout << "non-ordered support\n";
    g_use_ordered_support = false;
    tst4();

}
