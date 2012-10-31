/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    interval.h

Abstract:

    Goodies/Templates for interval arithmetic

Author:

    Leonardo de Moura (leonardo) 2012-07-19.

Revision History:

--*/
#include<cstdlib>
#include"interval_def.h"
#include"dependency.h"
#include"mpq.h"
#include"ast.h"
#include"debug.h"

template class interval_manager<im_default_config>;
typedef im_default_config::interval interval;

static void display_preamble(std::ostream & out) {
    out << "(set-info :status unsat)\n";
    out << "(set-option :auto-config true)\n";
    out << "(set-option :numeral-as-real true)\n";
    out << "(declare-const a Real)\n";
    out << "(declare-const b Real)\n";
}

static void display_smt2_pos_numeral(std::ostream & out, unsynch_mpq_manager & m, mpq const & n) {
    if (m.is_int(n)) {
        m.display(out, n);
    }
    else {
        out << "(/ ";
        m.display(out, n.numerator());
        out << " ";
        m.display(out, n.denominator());
        out << ")";
    }
}

static void display_smt2_numeral(std::ostream & out, unsynch_mpq_manager & m, mpq const & n) {
    if (m.is_neg(n)) {
        scoped_mpq n_copy(m);
        n_copy = n;
        out << "(- ";
        n_copy.neg();
        display_smt2_pos_numeral(out, m, n_copy);
        out << ")";
    }
    else {
        display_smt2_pos_numeral(out, m, n);
    }
}

static void display_constraint(std::ostream & out, unsynch_mpq_manager & m, char const * a, interval const & i, 
                               bool include_lower = true, bool include_upper = true) {
    out << "(and true";
    if (!i.m_lower_inf && include_lower) {
        out << " (" << (i.m_lower_open ? "<" : "<=") << " ";
        display_smt2_numeral(out, m, i.m_lower);
        out << " " << a << ")";
    }
    if (!i.m_upper_inf && include_upper) {
        out << " (" << (i.m_upper_open ? "<" : "<=") << " " << a << " ";
        display_smt2_numeral(out, m, i.m_upper);
        out << ")";
    }
    out << ")";
}

static void assert_hyp(std::ostream & out, unsynch_mpq_manager & m, char const * a, interval const & i, 
                       bool include_lower = true, bool include_upper = true) {
    out << "(assert ";
    display_constraint(out, m, a, i, include_lower, include_upper);
    out << ")\n";
}

static void assert_conj(std::ostream & out, unsynch_mpq_manager & m, char const * a, interval const & i,
                       bool include_lower = true, bool include_upper = true) {
    out << "(assert (not ";
    display_constraint(out, m, a, i, include_lower, include_upper);
    out << "))\n";
}

#if 0
static bool mk_interval(im_default_config & cfg, interval & a, bool l_inf, bool l_open, int l_val, bool u_inf, bool u_open, int u_val) {
    if (!l_inf && !u_inf) {
        if (l_val > u_val)
            return false;
        if (l_val == u_val && (l_open || u_open))
            return false;
    }
    
    if (l_inf) {
        a.m_lower_open = true;
        a.m_lower_inf  = true;
    }
    else {
        a.m_lower_open = l_open;
        a.m_lower_inf  = false;
        cfg.m().set(a.m_lower, l_val);
    }

    if (u_inf) {
        a.m_upper_open = true;
        a.m_upper_inf  = true;
    }
    else {
        a.m_upper_open = u_open;
        a.m_upper_inf  = false;
        cfg.m().set(a.m_upper, u_val);
    }
    
    return true;
}
#endif

static void mk_random_interval(im_default_config & cfg, interval & a, unsigned magnitude) {
    switch (rand()%3) {
    case 0:
        // Neg, Neg
        if (rand()%4 == 0) {
            a.m_lower_open = true;
            a.m_lower_inf  = true;
            
            a.m_upper_open = (rand()%2 == 0);
            a.m_upper_inf  = false;
            cfg.m().set(a.m_upper, -static_cast<int>((rand()%magnitude)));
        }
        else {
            a.m_upper_open = (rand()%2 == 0);
            a.m_upper_inf  = false;
            int upper = -static_cast<int>((rand()%magnitude));
            cfg.m().set(a.m_upper, upper);
            
            a.m_lower_open = (rand()%2 == 0);
            a.m_lower_inf  = false;
            cfg.m().set(a.m_lower, upper - static_cast<int>(rand()%magnitude) - (a.m_lower_open || a.m_upper_open ? 1 : 0));
        }
        break;
    case 1:
        // Neg, Pos
        
        if (rand()%4 == 0) {
            a.m_lower_open = true;
            a.m_lower_inf  = true;
        }
        else {
            a.m_lower_open = (rand()%2 == 0);
            a.m_lower_inf  = false;
            cfg.m().set(a.m_lower, -static_cast<int>((rand()%magnitude)) - 1);
        }
        
        if (rand()%4 == 0) {
            a.m_upper_open = true;
            a.m_upper_inf  = true;
        }
        else {
            a.m_upper_open = (rand()%2 == 0);
            a.m_upper_inf  = false;
            cfg.m().set(a.m_upper, rand()%magnitude + 1);
        }
        break;
    default:
        // Neg, Neg
        if (rand()%4 == 0) {
            a.m_upper_open = true;
            a.m_upper_inf  = true;
            
            a.m_lower_open = (rand()%2 == 0);
            a.m_lower_inf  = false;
            cfg.m().set(a.m_lower, (rand()%magnitude));
        }
        else {
            a.m_lower_open = (rand()%2 == 0);
            a.m_lower_inf  = false;
            int lower = (rand()%magnitude);
            cfg.m().set(a.m_lower, lower);
            
            a.m_upper_open = (rand()%2 == 0);
            a.m_upper_inf  = false;
            cfg.m().set(a.m_upper, lower + rand()%magnitude + (a.m_lower_open || a.m_upper_open ? 1 : 0));
        }
        break;
    }
}

static void del_interval(im_default_config & cfg, interval & a) {
    cfg.m().del(a.m_lower);
    cfg.m().del(a.m_upper);
}

#define BUFFER_SZ 256
static int g_problem_id = 0;
static char g_buffer[BUFFER_SZ];

char const * get_next_file_name() {
#ifdef _WINDOWS
    sprintf_s(g_buffer, BUFFER_SZ, "interval_lemma_%d.smt2", g_problem_id);
#else
    sprintf(g_buffer, "interval_lemma_%d.smt2", g_problem_id);
#endif
    g_problem_id++;
    return g_buffer;
}

static void display_lemmas(unsynch_mpq_manager & nm, char const * result_term,
                           interval const & a, interval const & b, interval const & r, interval_deps const & deps) {
    {
        std::ofstream out(get_next_file_name());
        display_preamble(out);
        assert_hyp(out, nm, "a", a, dep_in_lower1(deps.m_lower_deps), dep_in_upper1(deps.m_lower_deps));
        assert_hyp(out, nm, "b", b, dep_in_lower2(deps.m_lower_deps), dep_in_upper2(deps.m_lower_deps));
        assert_conj(out, nm, result_term, r, true, false);
        out << "(check-sat)\n";
    }
    {
        std::ofstream out(get_next_file_name());
        display_preamble(out);
        assert_hyp(out, nm, "a", a, dep_in_lower1(deps.m_upper_deps), dep_in_upper1(deps.m_upper_deps));
        assert_hyp(out, nm, "b", b, dep_in_lower2(deps.m_upper_deps), dep_in_upper2(deps.m_upper_deps));
        assert_conj(out, nm, result_term, r, false, true);
        out << "(check-sat)\n";
    }
}

#define MK_BINARY(NAME, RES_TERM)                                       \
static void tst_ ## NAME(unsigned N, unsigned magnitude) {              \
    unsynch_mpq_manager                 nm;                             \
    im_default_config                   imc(nm);                        \
    interval_manager<im_default_config> im(imc);                        \
    interval a, b, r;                                                   \
                                                                        \
    for (unsigned i = 0; i < N; i++) {                                  \
        mk_random_interval(imc, a, magnitude);                          \
        mk_random_interval(imc, b, magnitude);                          \
        interval_deps deps;                                             \
        im.NAME(a, b, r, deps);                                         \
                                                                        \
        display_lemmas(nm, RES_TERM, a, b, r, deps);                    \
    }                                                                   \
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r);   \
}

MK_BINARY(mul, "(* a b)");
MK_BINARY(add, "(+ a b)");
MK_BINARY(sub, "(- a b)");

static void tst_neg(unsigned N, unsigned magnitude) { 
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval a, b, r;                           
                                                
    for (unsigned i = 0; i < N; i++) {          
        mk_random_interval(imc, a, magnitude);  
        interval_deps deps;                     
        im.neg(a, r, deps);                 
        display_lemmas(nm, "(- a)", a, b, r, deps); 
    }  
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r); 
}

static void tst_pw_2(unsigned N, unsigned magnitude) { 
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval a, b, r;                           
                                                
    for (unsigned i = 0; i < N; i++) {          
        mk_random_interval(imc, a, magnitude);  
        interval_deps deps;                     
        im.power(a, 2, r, deps);                 
        display_lemmas(nm, "(* a a)", a, b, r, deps); 
    }  
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r); 
}

static void tst_pw_3(unsigned N, unsigned magnitude) { 
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval a, b, r;                           
                                                
    for (unsigned i = 0; i < N; i++) {          
        mk_random_interval(imc, a, magnitude);  
        interval_deps deps;                     
        im.power(a, 3, r, deps);                 
        display_lemmas(nm, "(* a a a)", a, b, r, deps); 
    }
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r); 
}

static void tst_root_2(unsigned N, unsigned magnitude, unsigned precision) { 
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval a, b, r;                           
    scoped_mpq                          p(nm);
    p = precision;
    nm.inv(p);

    unsigned i = 0;
    while (i < N) {
        mk_random_interval(imc, a, magnitude);  
        if (!im.lower_is_neg(a)) {
            i++;
            interval_deps deps;                     
            im.nth_root(a, 2, p, r, deps);                 
            display_lemmas(nm, "(^ a (/ 1.0 2.0))", a, b, r, deps); 
        } 
    } 
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r); 
}

static void tst_root_3(unsigned N, unsigned magnitude, unsigned precision) { 
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval a, b, r;                           
    scoped_mpq                          p(nm);
    p = precision;
    nm.inv(p);

    unsigned i = 0;
    while (i < N) {
        mk_random_interval(imc, a, magnitude);  
        i++;
        interval_deps deps;                     
        im.nth_root(a, 3, p, r, deps);                 
        display_lemmas(nm, "(^ a (/ 1.0 3.0))", a, b, r, deps); 
    } 
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r); 
}

static void tst_inv(unsigned N, unsigned magnitude) { 
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval a, b, r;                           
            
    for (unsigned i = 0; i < N; i++) {          
        while (true) {
            mk_random_interval(imc, a, magnitude);  
            if (!im.contains_zero(a))
                break;
        }
        interval_deps deps;                     
        im.inv(a, r, deps);                 
        display_lemmas(nm, "(/ 1 a)", a, b, r, deps); 
    }  
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r); 
}

static void tst_div(unsigned N, unsigned magnitude) {                    
    unsynch_mpq_manager                 nm;                       
    im_default_config                   imc(nm);                  
    interval_manager<im_default_config> im(imc);                  
    interval a, b, r;                                                  

    for (unsigned i = 0; i < N; i++) {                                 
        mk_random_interval(imc, a, magnitude);                         
        while (true) {
            mk_random_interval(imc, b, magnitude);                         
            if (!im.contains_zero(b))
                break;
        }
        interval_deps deps;                                             
        im.div(a, b, r, deps);                                         
        display_lemmas(nm, "(/ a b)", a, b, r, deps);  
    }                                                 
    del_interval(imc, a); del_interval(imc, b); del_interval(imc, r);   
}

#include"im_float_config.h"

#if 0
static void tst_float() {
    unsynch_mpq_manager   qm;
    mpf_manager           fm;
    im_float_config<mpf_manager>                    ifc(fm);
    interval_manager<im_float_config<mpf_manager> > im(ifc);
    im_float_config<mpf_manager>::interval          a, b, c;
    scoped_mpq minus_one_third(qm), one_third(qm), two_third(qm), minus_two_third(qm);
    qm.set(minus_one_third, -1, 3);
    qm.set(one_third, 1, 3);
    qm.set(two_third, 2, 3);
    qm.set(minus_two_third, -2, 3);
    
    ifc.round_to_minus_inf();
    ifc.m().set(a.m_lower, minus_one_third);
    ifc.round_to_plus_inf();
    ifc.m().set(a.m_upper, two_third);

    ifc.round_to_minus_inf();
    ifc.m().set(b.m_lower, minus_two_third);
    ifc.round_to_plus_inf();
    ifc.m().set(b.m_upper, one_third);
    
    im.display(std::cout, a);
    std::cout << "\n";
    im.display(std::cout, b);
    std::cout << "\n";
    interval_deps deps;
    im.add(a, b, c, deps);
    im.display(std::cout, c);
    std::cout << "\n";

    del_f_interval(ifc, a); del_f_interval(ifc, b); del_f_interval(ifc, c);
}
#endif

void tst_pi() {
    unsynch_mpq_manager                 nm;     
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(imc);
    interval r;
    for (unsigned i = 0; i < 8; i++) {
        im.pi(i, r);
        nm.display_decimal(std::cout, im.lower(r), 32); std::cout << "   "; 
        nm.display_decimal(std::cout, im.upper(r), 32); std::cout << "\n";
        SASSERT(nm.lt(im.lower(r), im.upper(r)));
    }
    del_interval(imc, r);
}

#if 0
static void tst_pi_float() {
    std::cout << "pi float...\n";
    unsynch_mpq_manager   qm;
    mpf_manager           fm;
    im_float_config<mpf_manager>                    ifc(fm, 22, 106);
    interval_manager<im_float_config<mpf_manager> > im(ifc);
    scoped_mpq q(qm);
    im_float_config<mpf_manager>::interval r;
    for (unsigned i = 0; i < 8; i++) {
        im.pi(i, r);
        fm.to_rational(im.lower(r), q);
        qm.display_decimal(std::cout, q, 32); std::cout << " ";
        fm.to_rational(im.upper(r), q);
        qm.display_decimal(std::cout, q, 32); std::cout << "\n";
    }
    del_f_interval(ifc, r);
}
#endif 

#define NUM_TESTS 1000
#define SMALL_MAG 3
#define MID_MAG   10

void tst_interval() {
    // enable_trace("interval_bug");
    // tst_float();
    // return;
    // enable_trace("interval_nth_root");
    // tst_pi();
    // tst_pi_float();
    tst_root_2(NUM_TESTS, MID_MAG, 100);
    tst_root_3(NUM_TESTS, MID_MAG, 100);
    tst_div(NUM_TESTS, SMALL_MAG);
    tst_inv(NUM_TESTS, SMALL_MAG);
    tst_pw_2(NUM_TESTS, SMALL_MAG);
    tst_pw_3(NUM_TESTS, SMALL_MAG);
    tst_neg(NUM_TESTS, SMALL_MAG);
    tst_sub(NUM_TESTS, SMALL_MAG);
    tst_mul(NUM_TESTS, SMALL_MAG);
    tst_add(NUM_TESTS, SMALL_MAG);
}
