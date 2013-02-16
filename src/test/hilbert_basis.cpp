#include "hilbert_basis.h"
#include "hilbert_basis_validate.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"
#include "quant_tactics.h"
#include "tactic.h"
#include "tactic2solver.h"
#include "solver.h"

#include<signal.h>
#include<time.h>

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

static void validate_sat(hilbert_basis& hb) {
    ast_manager m;
    reg_decl_plugins(m);
    hilbert_basis_validate val(m);

    expr_ref fml = val.mk_validate(hb);

    std::cout << mk_pp(fml, m) << "\n";

    fml = m.mk_not(fml);
    params_ref p;
    tactic_ref tac = mk_lra_tactic(m, p);
    ref<solver> sol = mk_tactic2solver(m, tac.get(), p);
    sol->assert_expr(fml);
    lbool r = sol->check_sat(0,0);
    std::cout << r << "\n";
}

static void saturate_basis(hilbert_basis& hb) {
    signal(SIGINT, on_ctrl_c);
    g_hb = &hb;
    g_start_time = static_cast<double>(clock());
    lbool is_sat = hb.saturate();

    switch(is_sat) {
    case l_true:  
        std::cout << "sat\n"; 
        hb.display(std::cout);
        // validate_sat(hb);
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
    hb.add_le(vec(-2, 3, 3, 5), R(3));
    saturate_basis(hb);
}

// Sigma_8 table 1,  Ajili, Contejean
static void tst11() {
    hilbert_basis hb;
    hb.add_le(vec( 7,-2,11, 3, -5), R(5));
    saturate_basis(hb);
}

static void tst12() {
    hilbert_basis hb;
    hb.add_le(vec(1, 0), R(1));
    hb.add_le(vec(0, 1), R(1));
    saturate_basis(hb);
}

// Sigma_9 table 1,  Ajili, Contejean
static void tst13() {
    hilbert_basis hb;
    hb.add_eq(vec( 1,-2,-4,4), R(0));
    hb.add_le(vec(100,45,-78,-67), R(0));
    saturate_basis(hb);
}

// Sigma_10 table 1,  Ajili, Contejean
static void tst14() {
    hilbert_basis hb;
    hb.add_le(vec( 23, -56, -34, 12, 11), R(0));
    saturate_basis(hb);
}

// Sigma_11 table 1,  Ajili, Contejean
static void tst15() {
//    hilbert_basis hb;
//    hb.add_le(vec( 23, -56, -34, 12, 11), R(0));
//    saturate_basis(hb);
}


void tst_hilbert_basis() {
    std::cout << "hilbert basis test\n";

    if (true) {
        tst1();
        tst2();
        tst3();
        // tst4();
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
        gorrila_test(0, 4, 3, 20, 5);
        gorrila_test(1, 4, 3, 20, 5);
        //gorrila_test(2, 4, 3, 20, 5);
        //gorrila_test(0, 4, 2, 20, 5);
        //gorrila_test(0, 4, 2, 20, 5);
    }
    else {
        gorrila_test(0, 10, 7, 20, 11);
    }
}
