/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat.cpp

Abstract:

    nlsat procedure

Author:

    Leonardo (leonardo) 2012-01-09

Notes:

--*/
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_interval_set.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/levelwise.h"
#include "util/util.h"
#include "nlsat/nlsat_explain.h"
#include "math/polynomial/polynomial_cache.h"
#include "util/rlimit.h"
#include <iostream>
#include <vector>

// Helper function to check if a point (given by counter_as) is inside a levelwise cell.
// Returns true if the point is inside ALL cell intervals, false otherwise.
// Prints diagnostic info about which constraint was violated (if any).
static bool is_point_inside_cell(
    anum_manager& am,
    polynomial::manager& pm,
    std_vector<nlsat::levelwise::root_function_interval> const& cell,
    nlsat::assignment const& counter_as,
    bool verbose = true) 
{
    for (unsigned level = 0; level < cell.size(); ++level) {
        auto const& interval = cell[level];
        
        // Skip whole-line sectors - no constraint
        if (!interval.is_section() && interval.l_inf() && interval.u_inf())
            continue;
            
        // Get the value at this level from counter_as
        if (!counter_as.is_assigned(level))
            continue;  // Variable not assigned in counterexample
            
        scoped_anum counter_val(am);
        am.set(counter_val, counter_as.value(level));
        
        // Build partial assignment up to this level (exclusive) for root isolation
        nlsat::assignment partial_as(am);
        for (unsigned j = 0; j < level; ++j) {
            if (counter_as.is_assigned(j)) {
                scoped_anum v(am);
                am.set(v, counter_as.value(j));
                partial_as.set(j, v);
            }
        }
        
        if (interval.is_section()) {
            // Section: counter must equal the root
            polynomial_ref section_p(interval.l, pm);
            scoped_anum_vector roots(am);
            am.isolate_roots(section_p, nlsat::undef_var_assignment(partial_as, level), roots);
            
            if (roots.size() >= interval.l_index) {
                bool at_root = am.eq(counter_val, roots[interval.l_index - 1]);
                if (!at_root) {
                    if (verbose) {
                        std::cout << "  Level " << level << ": OUTSIDE (not at section root)\n";
                        std::cout << "    Section root = ";
                        am.display_decimal(std::cout, roots[interval.l_index - 1], 6);
                        std::cout << ", counter = ";
                        am.display_decimal(std::cout, counter_val, 6);
                        std::cout << "\n";
                    }
                    return false;
                }
            }
        } else {
            // Sector: check lower and upper bounds
            if (!interval.l_inf()) {
                polynomial_ref lower_p(interval.l, pm);
                scoped_anum_vector lower_roots(am);
                am.isolate_roots(lower_p, nlsat::undef_var_assignment(partial_as, level), lower_roots);
                
                if (lower_roots.size() >= interval.l_index) {
                    int cmp = am.compare(counter_val, lower_roots[interval.l_index - 1]);
                    if (cmp <= 0) {  // counter <= lower bound, violates (lower, ...)
                        if (verbose) {
                            std::cout << "  Level " << level << ": OUTSIDE (at or below lower bound)\n";
                            std::cout << "    Lower bound = ";
                            am.display_decimal(std::cout, lower_roots[interval.l_index - 1], 6);
                            std::cout << ", counter = ";
                            am.display_decimal(std::cout, counter_val, 6);
                            std::cout << "\n";
                        }
                        return false;
                    }
                }
            }
            
            if (!interval.u_inf()) {
                polynomial_ref upper_p(interval.u, pm);
                scoped_anum_vector upper_roots(am);
                am.isolate_roots(upper_p, nlsat::undef_var_assignment(partial_as, level), upper_roots);
                
                if (upper_roots.size() >= interval.u_index) {
                    int cmp = am.compare(counter_val, upper_roots[interval.u_index - 1]);
                    if (cmp >= 0) {  // counter >= upper bound, violates (..., upper)
                        if (verbose) {
                            std::cout << "  Level " << level << ": OUTSIDE (at or above upper bound)\n";
                            std::cout << "    Upper bound = ";
                            am.display_decimal(std::cout, upper_roots[interval.u_index - 1], 6);
                            std::cout << ", counter = ";
                            am.display_decimal(std::cout, counter_val, 6);
                            std::cout << "\n";
                        }
                        return false;
                    }
                }
            }
        }
    }
    
    if (verbose) {
        std::cout << "  Point is INSIDE the cell (all constraints satisfied)\n";
    }
    return true;
}

// Helper: verify that counter_as has a different sign than sample_as on at least
// one polynomial in polys.  Only polynomials whose max_var is assigned in BOTH
// assignments are checked.  Returns true when at least one sign differs.
static bool has_different_sign(
    anum_manager& am,
    polynomial::manager& pm,
    polynomial_ref_vector const& polys,
    nlsat::assignment const& sample_as,
    nlsat::assignment const& counter_as)
{
    for (unsigned i = 0; i < polys.size(); ++i) {
        polynomial_ref p(polys.get(i), pm);
        polynomial::var mv = pm.max_var(p);
        if (mv == polynomial::null_var)          // constant polynomial
            continue;
        if (!sample_as.is_assigned(mv) || !counter_as.is_assigned(mv))
            continue;
        sign s_sign = am.eval_sign_at(p, sample_as);
        sign c_sign = am.eval_sign_at(p, counter_as);
        if (s_sign != c_sign) {
            std::cout << "  p" << i << " has different sign: sample=" << s_sign
                      << ", counter=" << c_sign << "\n";
            return true;
        }
    }
    return false;
}

nlsat::interval_set_ref tst_interval(nlsat::interval_set_ref const & s1,
                                     nlsat::interval_set_ref const & s2,
                                     unsigned expected_num_intervals,
                                     bool check_num_intervals = true) {
    nlsat::interval_set_manager & ism = s1.m();
    nlsat::interval_set_ref r(ism);
    std::cout << "s1:            " << s1 << "\n";
    std::cout << "s2:            " << s2 << "\n";
    r = ism.mk_union(s1, s2);
    std::cout << "union(s1, s2): " << r <<  std::endl;
    ENSURE(!check_num_intervals || ism.num_intervals(r) == expected_num_intervals);
    ENSURE(ism.subset(s1, r));
    ENSURE(ism.subset(s2, r));
    if (ism.set_eq(s1, s2)) {
        ENSURE(ism.set_eq(s1, r));
        ENSURE(ism.set_eq(s2, r));
    }
    else {
        ENSURE(ism.subset(s1, s2) || !ism.subset(r, s2));
        ENSURE(ism.subset(s2, s1) || !ism.subset(r, s1));
    }
    nlsat::interval_set_ref r2(ism);
    r2 = ism.mk_union(s2, s1);
    ENSURE(ism.set_eq(r, r2));
    anum zero;
    nlsat::interval_set_ref full(ism);
    nlsat::literal dummy(131, false);
    full = ism.mk(true, true, zero, true, true, zero, dummy, nullptr);
    ENSURE(ism.set_eq(r, full) == ism.is_full(r));
    return r;
}

static void tst3() {
    // enable_trace("nlsat_interval");
    reslimit rl;
    unsynch_mpq_manager         qm;
    anum_manager                am(rl, qm);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);

    scoped_anum               sqrt2(am), m_sqrt2(am), two(am), m_two(am), three(am), one(am), zero(am);
    am.set(two, 2);
    am.set(m_two, -2);
    am.set(one, 1);
    am.root(two, 2, sqrt2);
    am.set(m_sqrt2, sqrt2);
    am.neg(m_sqrt2);
    am.set(three, 3);

    nlsat::literal p1(1, false);
    nlsat::literal p2(2, false);
    nlsat::literal p3(3, false);
    nlsat::literal p4(4, false);
    nlsat::literal np2(2, true);

    nlsat::interval_set_ref s1(ism), s2(ism), s3(ism), s4(ism);
    s1 = ism.mk_empty();
    std::cout << "s1: " << s1 << "\n";
    s2 = ism.mk(true, true, zero, false, false, sqrt2, np2, nullptr);
    std::cout << "s2: " << s2 << "\n";
    s3 = ism.mk(false, false, zero, false, false, two, p1, nullptr);
    std::cout << "s3: " << s3 << "\n";
    s4 = ism.mk_union(s2, s3);
    std::cout << "s4: " << s4 << "\n";

    // Case
    //  s1:   [ ... ]
    //  s2:   [ ... ]
    s1 = ism.mk(false, false, zero, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, zero, false, false, two, p2, nullptr);
    tst_interval(s1, s2, 1);

    // Case
    // s1:   [ ... ]
    // s2: [ ... ]
    s1 = ism.mk(false, false, zero, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, m_sqrt2, false, false, one, p2, nullptr);
    s3 = ism.mk_union(s1, s2);
    tst_interval(s1, s2, 2);

    // Case
    // s1:   [ ... ]
    // s2:      [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, one, p1, nullptr);
    s2 = ism.mk(false, false, zero, false, false, two, p2, nullptr);
    tst_interval(s1, s2, 2);

    // Case
    // s1:   [ ... ]
    // s2:            [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, one, p1, nullptr);
    s2 = ism.mk(false, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 2);

    // Case
    // s1:   [    ...    ]
    // s2:      [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, three, p1, nullptr);
    s2 = ism.mk(false, false, zero, false, false, two, p2, nullptr);
    tst_interval(s1, s2, 1);

    // Case
    // s1:   [    ...      ]
    // s2:      [ ... ] [  ...  ]
    s1 = ism.mk(false, false, m_two, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, m_sqrt2, false, false, zero, p2, nullptr);
    s3 = ism.mk(false, false, one, false, false, three, p2, nullptr);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 2);

    // Case
    // s1:  [ ... ]
    // s2:        [ ... ]
    s1 = ism.mk(false, false, m_two, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, two, false, false, three, p1, nullptr);
    tst_interval(s1, s2, 1);
    s1 = ism.mk(false, false, m_two, true, false, two, p1, nullptr);
    tst_interval(s1, s2, 2);
    s1 = ism.mk(false, false, two, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 1);

    // Case
    // s1:  [ ... ]    [ ...  ]
    // s2: [ .. ]   [ ... ] [ ... ]
    s1 = ism.mk(false, false, m_two, false, false, zero, p1, nullptr);
    s3 = ism.mk(false, false, one, false, false,   three, p1, nullptr);
    s1 = ism.mk_union(s1, s3);
    s2 = ism.mk(true, true, zero,  false, false, m_sqrt2, p2, nullptr);
    tst_interval(s1, s2, 3);
    s3 = ism.mk(false, false, one, false, false, sqrt2, p2, nullptr);
    s2 = ism.mk_union(s2, s3);
    s3 = ism.mk(false, false, two, true, true, zero, p2, nullptr);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 4);

    // Case
    s1 = ism.mk(true, true, zero, false, false, one, p1, nullptr);
    s2 = ism.mk(true, false, one, true, true, zero, p2, nullptr);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, one, false, false, two, p2, nullptr);
    s3 = ism.mk(false, false, two, true, true, zero, p1, nullptr);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 3);
}

static nlsat::interval_set_ref mk_random(nlsat::interval_set_manager & ism, anum_manager & am, int range, int space, int tries, bool minus_inf, bool plus_inf,
                                       nlsat::literal lit) {
    static random_gen gen;
    ENSURE(range > 0);
    ENSURE(space > 0);
    nlsat::interval_set_ref r(ism), curr(ism);
    scoped_anum lower(am);
    scoped_anum upper(am);
    int prev = -range + (gen() % (space*4));

    if (gen() % 3 == 0 && minus_inf) {
        int  next = prev + (gen() % space);
        bool open = gen() % 2 == 0;
        am.set(upper, next);
        r = ism.mk(true, true, lower, open, false, upper, lit, nullptr);
        prev = next;
    }

    for (int i = 0; i < tries; ++i) {
        int l = prev  + (gen() % space);
        int u = l + (gen() % space);
        bool lower_open = gen() % 2 == 0;
        bool upper_open = gen() % 2 == 0;
        if ((lower_open || upper_open) && l == u)
            u++;
        am.set(lower, l);
        am.set(upper, u);
        curr = ism.mk(lower_open, false, lower, upper_open, false, upper, lit, nullptr);
        r = ism.mk_union(r, curr);
        prev = u;
    }

    if (gen() % 3 == 0 && plus_inf) {
        int  next = prev + (gen() % space);
        bool open = gen() % 2 == 0;
        am.set(lower, next);
        curr = ism.mk(open, false, lower, true, true, upper, lit, nullptr);
        r = ism.mk_union(r, curr);
    }
    return r;
}

static void check_subset_result(nlsat::interval_set_ref const & s1,
                                nlsat::interval_set_ref const & s2,
                                nlsat::interval_set_ref const & r,
                                nlsat::literal l1,
                                nlsat::literal l2) {
    nlsat::interval_set_manager ism(s1.m());
    nlsat::interval_set_ref tmp(ism);
    unsigned num = ism.num_intervals(r);
    nlsat::literal_vector lits;
    ptr_vector<nlsat::clause> clauses;
    ism.get_justifications(r, lits, clauses);
    ENSURE(lits.size() <= 2);
    for (unsigned i = 0; i < num; ++i) {
        tmp = ism.get_interval(r, i);
        ism.get_justifications(tmp, lits, clauses);
        ENSURE(lits.size() == 1);
        if (lits[0] == l1) {
            ENSURE(ism.subset(tmp, s1));
        }
        else {
            ENSURE(lits[0] == l2);
            ENSURE(ism.subset(tmp, s2));
        }
    }
}

static void tst4() {
    // enable_trace("nlsat_interval");
    reslimit rl;
    unsynch_mpq_manager         qm;
    anum_manager                am(rl, qm);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);
    nlsat::interval_set_ref     s1(ism), s2(ism), r(ism);

    nlsat::literal l1(1, false);
    nlsat::literal l2(2, false);

    for (unsigned i = 0; i < 100; ++i) {
        s1 = mk_random(ism, am, 20, 3, 10, true, true, l1);
        s2 = mk_random(ism, am, 20, 3, 10, true, true, l2);
        r = tst_interval(s1, s2, 0, false);
        check_subset_result(s1, s2, r, l1, l2);
    }

    for (unsigned i = 0; i < 100; ++i) {
        s1 = mk_random(ism, am, 200, 100, 20, true, true, l1);
        s2 = mk_random(ism, am, 200, 100, 20, true, true, l2);
        r = tst_interval(s1, s2, 0, false);
        check_subset_result(s1, s2, r, l1, l2);
    }
}

static void tst5() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am = s.am();
    nlsat::pmanager & pm = s.pm();
    nlsat::assignment           as(am);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);
    nlsat::evaluator            ev(s, as, pm, allocator);
    nlsat::var                  x0, x1;
    x0 = pm.mk_var();
    x1 = pm.mk_var();

    polynomial_ref p(pm);
    polynomial_ref _x0(pm), _x1(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    p = (_x0^2) + (_x1^2) - 2;
    nlsat::poly * _p[1] = { p.get() };
    bool is_even[1] = { false };
    nlsat::bool_var b = s.mk_ineq_atom(nlsat::atom::GT, 1, _p, is_even);
    nlsat::atom * a = s.bool_var2atom(b);
    ENSURE(a != nullptr);
    scoped_anum zero(am);
    am.set(zero, 0);
    as.set(0, zero);
    auto i = ev.infeasible_intervals(a, true, nullptr);
    std::cout << "1) " << i << "\n";
    as.set(1, zero);
    auto i2 = ev.infeasible_intervals(a, true, nullptr);
    std::cout << "2) " << i2 << "\n";
}



static void project(nlsat::solver& s, nlsat::explain& ex, nlsat::var x, unsigned num, nlsat::literal const* lits) {
    std::cout << "Project ";
    s.display(std::cout, num, lits);
    nlsat::scoped_literal_vector result(s);
    ex.project(x, num, lits, result);
    s.display(std::cout << "\n==>\n", result.size(), result.data());
    std::cout << "\n";
}

static void project_fa(nlsat::solver& s, nlsat::explain& ex, nlsat::var x, unsigned num, nlsat::literal const* lits) {
    std::cout << "Project ";
    nlsat::scoped_literal_vector result(s);
    ex.compute_conflict_explanation(num, lits, result);
    std::cout << "(or";
    for (auto l : result) {
        s.display(std::cout << " ", l);
    }
    for (unsigned i = 0; i < num; ++i) {
        s.display(std::cout << " ", ~lits[i]);
    }
    std::cout << ")\n";
}

static nlsat::literal mk_gt(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::GT, 1, _p, is_even);
}


static nlsat::literal mk_lt(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::LT, 1, _p, is_even);
}

static nlsat::literal mk_eq(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::EQ, 1, _p, is_even);
}

static nlsat::literal mk_root_eq(nlsat::solver& s, nlsat::poly* p, nlsat::var x, unsigned i) {
    nlsat::bool_var b = s.mk_root_atom(nlsat::atom::ROOT_EQ, x, i, p);
    return nlsat::literal(b, false);
}

static void set_assignment_value(nlsat::assignment& as, anum_manager& am, nlsat::var v, rational const& val) {
    scoped_anum tmp(am);
    am.set(tmp, val.to_mpq());
    as.set(v, tmp);
}

static void tst_12() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver   s(rlim, ps, false);
    nlsat::pmanager& pm = s.pm();
    anum_manager & am     = s.am();
    nlsat::assignment as(am);
    scoped_anum zero(am), one(am), two(am), three(am);
    nlsat::explain& ex    = s.get_explain();
    
    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    am.set(one, 1);
    am.set(two, 2);
    as.set(x0, one);
    as.set(x1, two);
    as.set(x2, three);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);

    polynomial_ref x0_sq(pm), x1_sq(pm), x2_sq(pm);
    x0_sq = _x0 * _x0;
    x1_sq = _x1 * _x1;
    x2_sq = _x2 * _x2;

    polynomial_ref vandermonde_flat(pm);
    vandermonde_flat =
        (_x1 * x2_sq) -
        (x1_sq * _x2) +
        (_x0 * x1_sq) -
        (x0_sq * _x1) +
        (x0_sq * _x2) -
        (_x0 * x2_sq);

    polynomial_ref vandermonde_factored(pm);
    vandermonde_factored = (_x1 - _x0) * (_x2 - _x0) * (_x2 - _x1);
    std::cout << "vandermonde_factored:" << vandermonde_factored << "\n";
    polynomial_ref diff(pm);
    diff = vandermonde_flat - vandermonde_factored;
    ENSURE(pm.is_zero(diff.get()));

    pm.display(std::cout << "vandermonde(flat): ", vandermonde_flat);
    std::cout << "\n";
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, vandermonde_flat));
    s.set_rvalues(as);
    project(s, ex, x2, lits.size(), lits.data());
    as.set(x2, (one + two)/2);
    std::cout << am.eval_sign_at(vandermonde_flat, as) << "\n";
;}

static void tst6() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);

    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);

    p1 = (_a*(_x0^2)) + _x2 + 2;
    p2 = (_b*_x1) - (2*_x2) - _x0 + 8;
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_gt(s, p2));
    lits.push_back(mk_gt(s, (_c*_x0) + _x2 + 1));
    lits.push_back(mk_gt(s, (_d*_x0) - _x1 + 5*_x2));

    scoped_anum zero(am), one(am), two(am);
    am.set(zero, 0);
    am.set(one,  1);
    am.set(two,  2);
    as.set(0, one);
    as.set(1, one);
    as.set(2, two);
    as.set(3, two);
    as.set(4, two);
    as.set(5, one);
    as.set(6, one); 
    s.set_rvalues(as);


    project(s, ex, x0, 2, lits.data());
    project(s, ex, x1, 3, lits.data());
    project(s, ex, x2, 3, lits.data());
    project(s, ex, x2, 2, lits.data());
    project(s, ex, x2, 4, lits.data());
    project(s, ex, x2, 3, lits.data()+1);
    
    
}

static void tst7() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    nlsat::pmanager & pm  = s.pm();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);
    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);

    p1 = _x0 + _x1;
    p2 = _x2 - _x0;
    p3 = (-1*_x0) - _x1;
    
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_gt(s, p2));
    lits.push_back(mk_gt(s, p3));

    nlsat::literal_vector litsv(lits.size(), lits.data());
    lbool res = s.check(litsv);
    VERIFY(res == l_false);
    for (unsigned i = 0; i < litsv.size(); ++i) {
        s.display(std::cout, litsv[i]);
        std::cout << " ";
    }
    std::cout << "\n";

    litsv.reset();
    litsv.append(2, lits.data());
    res = s.check(litsv);
    ENSURE(res == l_true);
    s.display(std::cout);
    s.am().display(std::cout, s.value(x0)); std::cout << "\n";
    s.am().display(std::cout, s.value(x1)); std::cout << "\n";
    s.am().display(std::cout, s.value(x2)); std::cout << "\n";

}

static void tst8() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);

    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);
    
    scoped_anum zero(am), one(am), two(am), six(am);
    am.set(zero, 0);
    am.set(one,  1);
    am.set(two,  2);
    am.set(six,  6);
    as.set(0, two); // a
    as.set(1, one); // b
    as.set(2, six); // c
    as.set(3, zero); // d
    as.set(4, zero); // x0
    as.set(5, zero); // x1
    as.set(6, two); // x2
    s.set_rvalues(as);

    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_eq(s, (_a*_x2*_x2) - (_b*_x2) - _c));
    project(s, ex, x2, 1, lits.data());
}



static void tst9() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    int num_lo = 4;
    int num_hi = 5;
    svector<nlsat::var> los, his;
    for (int i = 0; i < num_lo; ++i) {
        los.push_back(s.mk_var(false));
        scoped_anum num(am);
        am.set(num, - i - 1);
        as.set(i, num);
    }
    for (int i = 0; i < num_hi; ++i) {
        his.push_back(s.mk_var(false));
        scoped_anum num(am);
        am.set(num, i + 1);
        as.set(num_lo + i, num);
    }
    nlsat::var _z = s.mk_var(false);
    nlsat::var _x = s.mk_var(false);
    polynomial_ref x(pm), z(pm);
    x = pm.mk_polynomial(_x);
    scoped_anum val(am);
    am.set(val, 0);
    as.set(num_lo + num_hi, val);
    as.set(num_lo + num_hi + 1, val);
    s.set_rvalues(as);
    nlsat::scoped_literal_vector lits(s);

    for (int i = 0; i < num_lo; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(los[i]);
        lits.push_back(mk_gt(s, x - y));
    }
    for (int i = 0; i < num_hi; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(his[i]);
        lits.push_back(mk_gt(s, y - x));
    }
    z = pm.mk_polynomial(_z);
    lits.push_back(mk_eq(s, x - z));

#define TEST_ON_OFF()                                   \
    std::cout << "Off ";                                \
    project(s, ex, _x, lits.size()-1, lits.data());    \
    std::cout << "On ";                                 \
    project(s, ex, _x, lits.size()-1, lits.data());    \
    std::cout << "Off ";                                \
    project(s, ex, _x, lits.size(), lits.data());      \
    std::cout << "On ";                                 \
    project(s, ex, _x, lits.size(), lits.data())       \

    TEST_ON_OFF();

    lits.reset();
    polynomial_ref u(pm);
    u = pm.mk_polynomial(his[1]);
    for (int i = 0; i < num_lo; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(los[i]);
        lits.push_back(mk_gt(s, u*x - y));
    }
    for (int i = 0; i < num_hi; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(his[i]);
        lits.push_back(mk_gt(s, y - u*x));
    }
    z = pm.mk_polynomial(_z);
    lits.push_back(mk_eq(s, u*x - z));

    TEST_ON_OFF();

    lits.reset();
    u = pm.mk_polynomial(los[1]);
    for (int i = 0; i < num_lo; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(los[i]);
        lits.push_back(mk_gt(s, u*x - y));
    }
    for (int i = 0; i < num_hi; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(his[i]);
        lits.push_back(mk_gt(s, y - u*x));
    }
    z = pm.mk_polynomial(_z);
    lits.push_back(mk_eq(s, x - z));

    TEST_ON_OFF();
}


#if 0


#endif

static void test_root_literal(nlsat::solver& s, nlsat::explain& ex, nlsat::var x, nlsat::atom::kind k, unsigned i, nlsat::poly* p) {
    nlsat::scoped_literal_vector result(s);
    ex.test_root_literal(k, x, 1, p, result);
    nlsat::bool_var b = s.mk_root_atom(k, x, i, p);
    s.display(std::cout, nlsat::literal(b, false));
    s.display(std::cout << " ==> ", result.size(), result.data());
    std::cout << "\n";
}

static bool satisfies_root(nlsat::solver& s, nlsat::atom::kind k, nlsat::poly* p) {
    nlsat::pmanager & pm  = s.pm();
    anum_manager & am     = s.am();
    nlsat::assignment as(am);
    s.get_rvalues(as);
    polynomial_ref pr(p, pm);
    switch (k) {
    case nlsat::atom::ROOT_EQ: return am.eval_sign_at(pr, as) == 0; 
    case nlsat::atom::ROOT_LE: return am.eval_sign_at(pr, as) <= 0;
    case nlsat::atom::ROOT_LT: return am.eval_sign_at(pr, as) <  0;
    case nlsat::atom::ROOT_GE: return am.eval_sign_at(pr, as) >= 0;
    case nlsat::atom::ROOT_GT: return am.eval_sign_at(pr, as) >  0;
    default:
        UNREACHABLE();
        return false;
    }
}

static void tst10() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var _a = s.mk_var(false);
    nlsat::var _b = s.mk_var(false);
    nlsat::var _c = s.mk_var(false);
    nlsat::var _x = s.mk_var(false);

    polynomial_ref x(pm), a(pm), b(pm), c(pm), p(pm);
    x = pm.mk_polynomial(_x);
    a = pm.mk_polynomial(_a);
    b = pm.mk_polynomial(_b);
    c = pm.mk_polynomial(_c);
    p = a*x*x + b*x + c;
    scoped_anum one(am), two(am), three(am), mone(am), mtwo(am), mthree(am), zero(am), one_a_half(am);
    am.set(zero, 0);
    am.set(one, 1);
    am.set(two, 2);
    am.set(three, 3);
    am.set(mone, -1);
    am.set(mtwo, -2);
    am.set(mthree, -3);
    rational oah(1,2);
    am.set(one_a_half, oah.to_mpq());
    
 
    scoped_anum_vector nums(am);
    nums.push_back(one);
    nums.push_back(two);
    nums.push_back(one_a_half);
    nums.push_back(mone);
    nums.push_back(three);

    // a = 1, b = -3, c = 2: 
    // has roots x = 2, x = 1:
    //  2^2 - 3*2 + 2 = 0
    //  1 - 3 + 2 = 0
    as.set(_a, one);
    as.set(_b, mthree);
    as.set(_c, two);

    for (unsigned i = 0; i < nums.size(); ++i) {
        as.set(_x, nums[i]);
        s.set_rvalues(as);
        std::cout << p << "\n";
        as.display(std::cout);
        for (unsigned k = nlsat::atom::ROOT_EQ; k <= nlsat::atom::ROOT_GE; ++k) {
            if (satisfies_root(s, (nlsat::atom::kind) k, p)) {
                test_root_literal(s, ex, _x, (nlsat::atom::kind) k, 1, p);
            }
        }
    }
    as.set(_a, mone);
    as.set(_b, three);
    as.set(_c, mtwo);
    for (unsigned i = 0; i < nums.size(); ++i) {
        as.set(_x, nums[i]);
        s.set_rvalues(as);
        std::cout << p << "\n";
        as.display(std::cout);
        for (unsigned k = nlsat::atom::ROOT_EQ; k <= nlsat::atom::ROOT_GE; ++k) {
            if (satisfies_root(s, (nlsat::atom::kind) k, p)) {
                test_root_literal(s, ex, _x, (nlsat::atom::kind) k, 1, p);
            }
        }
    }
    std::cout << "\n";
}

void tst_13() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment assignment(am);
    nlsat::explain& ex    = s.get_explain();

    tst_12();
    return;

    // Regression: reproduce lemma 114 where main_operator adds spurious bounds.
    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);

    polynomial_ref _x0(pm), _x1(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);

    polynomial_ref x0_sq(pm), x0_cu(pm), x0_4(pm), x0_5(pm);
    x0_sq = _x0 * _x0;
    x0_cu = x0_sq * _x0;
    x0_4 = x0_cu * _x0;
    x0_5 = x0_4 * _x0;

    polynomial_ref x1_sq(pm), x1_cu(pm), x1_4(pm), x1_5(pm);
    x1_sq = _x1 * _x1;
    x1_cu = x1_sq * _x1;
    x1_4 = x1_cu * _x1;
    x1_5 = x1_4 * _x1;

    polynomial_ref root_arg(pm);
    root_arg =
        x1_5 +
        (_x0 * x1_4) -
        (18 * x1_4) -
        (2 * x0_sq * x1_cu) -
        (2 * x0_cu * x1_sq) +
        (36 * x0_sq * x1_sq) +
        (1296 * _x0 * x1_sq) +
        (864 * x1_sq) +
        (x0_4 * _x1) +
        (1296 * x0_sq * _x1) +
        (6048 * _x0 * _x1) +
        x0_5 -
        (18 * x0_4) +
        (864 * x0_sq);
    // should be (x1^5 + x0 x1^4 - 18 x1^4 - 2 x0^2 x1^3 - 2 x0^3 x1^2 + 36 x0^2 x1^2 + 1296 x0 x1^2 + 864 x1^2 + x0^4 x1 + 1296 x0^2 x1 + 6048 x0 x1 + x0^5 - 18 x0^4 + 864 x0^2)
    std::cout << "big poly:" <<  root_arg << std::endl;
    nlsat::literal x1_gt_0 = mk_gt(s, _x1);
    nlsat::bool_var root_gt = s.mk_root_atom(nlsat::atom::ROOT_GT, x1, 3, root_arg.get());
    nlsat::literal x1_gt_root(root_gt, false);

    nlsat::scoped_literal_vector lits(s);
    lits.push_back(x1_gt_0);
    lits.push_back(~x1_gt_root); // !(x1 > root[3](root_arg))

    scoped_anum one(am), one_dup(am);
    am.set(one, 1);
    assignment.set(x0, one);
    s.set_rvalues(assignment);

    nlsat::scoped_literal_vector result(s);
    ex.compute_conflict_explanation(lits.size(), lits.data(), result);

    std::cout << "main_operator root regression core:\n";
    s.display(std::cout, lits.size(), lits.data());
    s.display(std::cout << "\n==>\n", result.size(), result.data());
    std::cout << "\n";

    // Assign x1 only after the lemma is produced.
    am.set(one_dup, 1);
    assignment.set(x1, one_dup);
    s.set_rvalues(assignment);

    small_object_allocator allocator;
    nlsat::evaluator eval(s, assignment, pm, allocator);
    std::cout << "input literal values at x0 = 1, x1 = 1:\n";
    for (nlsat::literal l : lits) {
        nlsat::atom* a = s.bool_var2atom(l.var());
        if (!a) {
            std::cout << "conversion bug\n";
        }
        bool value = a ? eval.eval(a, l.sign()) : false;
        s.display(std::cout << "  ", l);
        std::cout << " -> " << (value ? "true" : "false") << "\n";
    }
    std::cout << "new literal values at x0 = 1, x1 = 1:\n";
    for (nlsat::literal l : result) {
        nlsat::atom* a = s.bool_var2atom(l.var());
        bool value = a ? eval.eval(a, l.sign()) : false;
        if (!a) {
            std::cout << "conversion bug\n";
        }
        s.display(std::cout << "  ", l);
        std::cout << " -> " << (value ? "true" : "false") << "\n";
    }
    std::cout << "\n";
}

static void tst11() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x, y, z;
    y = s.mk_var(false);
    z = s.mk_var(false);
    x = s.mk_var(false);
    polynomial_ref p1(pm), p2(pm), _x(pm), _y(pm), _z(pm);
    _x = pm.mk_polynomial(x);
    _y = pm.mk_polynomial(y);
    _z = pm.mk_polynomial(z);

    nlsat::scoped_literal_vector lits(s);
    scoped_anum zero(am), one(am), five(am);
    am.set(zero, 0);
    am.set(one, 1);
    am.set(five, 5);
    as.set(z, zero);
    as.set(y, five);
    as.set(x, five);
    s.set_rvalues(as);

    p1 = (_x - _y);
    p2 = ((_x*_x) - (_x*_y) - _z);
    lits.reset();
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_eq(s, p2));
    project_fa(s, ex, x, 2, lits.data());
//    return;

    p1 = ((_x * _x) - (2 * _y * _x)  - _z + (_y *_y));
    p2 = _x + _y;
    as.set(_x, one);
    as.set(_y, zero);
    as.set(_z, one);
    lits.reset();
    lits.push_back(mk_lt(s, p1));
    lits.push_back(mk_eq(s, p2));
    project_fa(s, ex, x, 2, lits.data());
    return;

    as.set(z, zero);
    as.set(y, five);
    as.set(x, five);    
    p1 = (_x - _y);
    p2 = ((_x*_x) - (_x*_y));
    lits.reset();
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_eq(s, p2));
    project_fa(s, ex, x, 2, lits.data());

#if 0

!(x5^4 - 2 x3^2 x5^2 - 2 x1^2 x5^2 + 4 x0 x1 x5^2 - 2 x0^2 x5^2 + x3^4 - 2 x1^2 x3^2 + 4 x0 x1 x3^2 - 2 x0^2 x3^2 + x1^4 - 4 x0 x1^3 + 6 x0^2 x1^2 - 4 x0^3 x1 + x0^4 = 0) or !(x5 < 0) or !(x4 > root[1](x1 x4 - x0 x4 + x3)) or !(x3 + x1 - x0 > 0) or !(x1 - x0 < 0) or !(x7 > root[1](x1^2 x7 - 2 x0 x1 x7 + x0^2 x7 + x1 x3 - x0 x3)) or x7 - x4 = 0 or !(x1 x3 x7^2 - x0 x3 x7^2 - x5^2 x7 + x3^2 x7 + x1^2 x7 - 2 x0 x1 x7 + x0^2 x7 + x1 x3 - x0 x3 = 0)

x0 := -1
x1 := -21.25
x2 := 0.0470588235?
x3 := 2
x4 := -0.03125
x5 := -18.25
x6 := -0.5
x7 := 1

#endif

}

static void tst_14() {
    params_ref ps;
    reslimit rlim;
    nlsat::solver s(rlim, ps, false);
    nlsat::pmanager& pm = s.pm();
    polynomial::cache cache(pm);
    nlsat::var x = s.mk_var(false);
    polynomial_ref x_poly(pm);
    x_poly = pm.mk_polynomial(x);

    polynomial_ref p(pm);
    p = 2 * x_poly;
    pm.display(std::cout, p);
    std::cout << "\n";

    ENSURE(!cache.contains(p.get()));
    polynomial::polynomial* unique_p = cache.mk_unique(p.get());
    ENSURE(unique_p != nullptr);
    ENSURE(cache.contains(unique_p));
    pm.display(std::cout, unique_p);
    std::cout << "\n";

    polynomial_ref p_again(pm);
    p_again = 2 * x_poly;
    ENSURE(cache.mk_unique(p_again.get()) == unique_p);

    polynomial_ref p_neg(pm);
    p_neg = -2 * x_poly;
    ENSURE(!cache.contains(p_neg.get()));
    polynomial::polynomial* unique_p_neg = cache.mk_unique(p_neg.get());
    ENSURE(unique_p_neg != nullptr);
    ENSURE(unique_p_neg != unique_p);
    ENSURE(cache.contains(unique_p_neg));

    polynomial_ref p_neg_again(pm);
    p_neg_again = -2 * x_poly;
    ENSURE(cache.mk_unique(p_neg_again.get()) == unique_p_neg);

    polynomial_ref ca(p, pm), cb(p_neg, pm);
    pm.primitive(ca, x, ca);
    pm.primitive(cb, x, cb);
    pm.display(std::cout << "ca:", ca) << "\n";
    pm.display(std::cout << "cb:", cb) << "\n";
           
}

static void tst_15() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    nlsat::pmanager & pm  = s.pm();
    anum_manager & am     = s.am();
    polynomial::cache cache(pm);

    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);
    ENSURE(x0 < x1 && x1 < x2);

    polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);

    polynomial_ref p1(pm), p2(pm);
    p1 = _x2 * _x1;
    p2 = _x0;
    p1 = p1 + p2;
    p2 = _x3;
    polynomial_ref_vector polys(pm);
    polys.push_back(p1);
    polys.push_back(p2);
    nlsat::assignment as(am);
    scoped_anum zero(am);
    am.set(zero, 0);
    as.set(x0, zero);
    as.set(x1, zero);
    as.set(x2, zero);
    as.set(x3, zero);
    s.set_rvalues(as);

    unsigned max_x = 0;
    for (unsigned i = 0; i < polys.size(); ++i) {
        unsigned lvl = pm.max_var(polys.get(i));
        if (lvl > max_x)
            max_x = lvl;
    }
    ENSURE(max_x == x3);

    nlsat::levelwise lws(s, polys, max_x, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();
}

// Test case for unsound lemma lws2380 - comparing standard projection vs levelwise
// The issue: x7 is unconstrained in levelwise output but affects the section polynomial
static void tst_16() {
    // enable_trace("nlsat_explain");
    
    auto run_test = [](bool use_lws) {
        std::cout << "=== tst_16: " << (use_lws ? "Levelwise" : "Standard") << " projection (lws=" << use_lws << ") ===\n";
        params_ref      ps;
        ps.set_bool("lws", use_lws);
        reslimit        rlim;
        nlsat::solver s(rlim, ps, false);
        anum_manager & am     = s.am();
        nlsat::pmanager & pm  = s.pm();
        nlsat::assignment as(am);
        nlsat::explain& ex    = s.get_explain();

        // Create 14 variables x0-x13
        nlsat::var x0 = s.mk_var(false);
        nlsat::var x1 = s.mk_var(false);
        nlsat::var x2 = s.mk_var(false);
        nlsat::var x3 = s.mk_var(false);
        nlsat::var x4 = s.mk_var(false);
        nlsat::var x5 = s.mk_var(false);
        nlsat::var x6 = s.mk_var(false);
        nlsat::var x7 = s.mk_var(false);
        nlsat::var x8 = s.mk_var(false);
        nlsat::var x9 = s.mk_var(false);
        nlsat::var x10 = s.mk_var(false);
        nlsat::var x11 = s.mk_var(false);
        nlsat::var x12 = s.mk_var(false);
        nlsat::var x13 = s.mk_var(false);

        polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm), _x4(pm), _x5(pm), _x6(pm);
        polynomial_ref _x7(pm), _x8(pm), _x9(pm), _x10(pm), _x11(pm), _x12(pm), _x13(pm);
        _x0 = pm.mk_polynomial(x0);
        _x1 = pm.mk_polynomial(x1);
        _x2 = pm.mk_polynomial(x2);
        _x3 = pm.mk_polynomial(x3);
        _x4 = pm.mk_polynomial(x4);
        _x5 = pm.mk_polynomial(x5);
        _x6 = pm.mk_polynomial(x6);
        _x7 = pm.mk_polynomial(x7);
        _x8 = pm.mk_polynomial(x8);
        _x9 = pm.mk_polynomial(x9);
        _x10 = pm.mk_polynomial(x10);
        _x11 = pm.mk_polynomial(x11);
        _x12 = pm.mk_polynomial(x12);
        _x13 = pm.mk_polynomial(x13);

        // p[0]: x13
        polynomial_ref p0(pm);
        p0 = _x13;

        // p[1]: 170*x8*x13 + x10*x11*x12 - x11*x12 - x7*x8*x12 + x5*x10*x11 + 184*x1*x10*x11
        //       - x0*x10*x11 - x5*x11 - 184*x1*x11 + x0*x11 - x3*x8*x10 + x2*x8*x10
        //       - 2*x10 - 184*x1*x7*x8 - x2*x8 + 2
        polynomial_ref p1(pm);
        p1 = (170 * _x8 * _x13) +
             (_x10 * _x11 * _x12) -
             (_x11 * _x12) -
             (_x7 * _x8 * _x12) +
             (_x5 * _x10 * _x11) +
             (184 * _x1 * _x10 * _x11) -
             (_x0 * _x10 * _x11) -
             (_x5 * _x11) -
             (184 * _x1 * _x11) +
             (_x0 * _x11) -
             (_x3 * _x8 * _x10) +
             (_x2 * _x8 * _x10) -
             (2 * _x10) -
             (184 * _x1 * _x7 * _x8) -
             (_x2 * _x8) +
             2;

        std::cout << "p0: " << p0 << "\n";
        std::cout << "p1: " << p1 << "\n";

        // Set sample: x0=-1, x1=-1, x2=0, x3=-1, x5=0, x7=0, x8=2, x10=0, x11=0, x12=2
        scoped_anum val(am);
        am.set(val, -1); as.set(x0, val);
        am.set(val, -1); as.set(x1, val);
        am.set(val, 0);  as.set(x2, val);
        am.set(val, -1); as.set(x3, val);
        am.set(val, 0);  as.set(x4, val);
        am.set(val, 0);  as.set(x5, val);
        am.set(val, 0);  as.set(x6, val);
        am.set(val, 0);  as.set(x7, val);
        am.set(val, 2);  as.set(x8, val);
        am.set(val, 0);  as.set(x9, val);
        am.set(val, 0);  as.set(x10, val);
        am.set(val, 0);  as.set(x11, val);
        am.set(val, 2);  as.set(x12, val);
        am.set(val, 1);  as.set(x13, val);
        s.set_rvalues(as);

        // Create literals for the two polynomials
        nlsat::scoped_literal_vector lits(s);
        lits.push_back(mk_gt(s, p0.get()));  // x13 > 0
        lits.push_back(mk_gt(s, p1.get()));  // p1 > 0

        project_fa(s, ex, x13, lits.size(), lits.data());
        std::cout << "\n";
    };

    run_test(false);  // Standard projection
    run_test(true);   // Levelwise projection
}

// Test case for unsound lemma - levelwise produces cell that's too large
// Input: 5 polynomials with max_var=x3, sample x0=-7, x1=-1, x2=1
// Counterexample: x0=-4, x1=-8, x2=5, x3=6
static void tst_17() {
    std::cout << "=== tst_17 ===\n";
    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);
    polynomial::cache cache(pm);

    // Create 4 variables x0, x1, x2, x3
    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);

    polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);

    // p[0]: x3 + x0
    polynomial_ref p0(pm);
    p0 = _x3 + _x0;

    // p[1]: x1
    polynomial_ref p1(pm);
    p1 = _x1;

    // p[2]: 9 x1^2 x3^2 - 6 x0 x1 x2 x3 + 3 x0 x1^2 x3 - 12 x1^2 x3 + x0^2 x2^2 - x0^2 x1 x2 - 4 x0 x1 x2 + 2 x0 x1^2 + 4 x1^2
    polynomial_ref p2(pm);
    p2 = 9 * (_x1^2) * (_x3^2) 
       - 6 * _x0 * _x1 * _x2 * _x3 
       + 3 * _x0 * (_x1^2) * _x3 
       - 12 * (_x1^2) * _x3 
       + (_x0^2) * (_x2^2) 
       - (_x0^2) * _x1 * _x2 
       - 4 * _x0 * _x1 * _x2 
       + 2 * _x0 * (_x1^2) 
       + 4 * (_x1^2);

    // p[3]: 9 x1^2 x3^2 - 6 x0 x1 x2 x3 + 6 x0 x1^2 x3 - 12 x1^2 x3 + x0^2 x2^2 - 2 x0^2 x1 x2 - 4 x0 x1 x2 + x0^2 x1^2 + 4 x0 x1^2 + 4 x1^2
    polynomial_ref p3(pm);
    p3 = 9 * (_x1^2) * (_x3^2) 
       - 6 * _x0 * _x1 * _x2 * _x3 
       + 6 * _x0 * (_x1^2) * _x3 
       - 12 * (_x1^2) * _x3 
       + (_x0^2) * (_x2^2) 
       - 2 * (_x0^2) * _x1 * _x2 
       - 4 * _x0 * _x1 * _x2 
       + (_x0^2) * (_x1^2) 
       + 4 * _x0 * (_x1^2) 
       + 4 * (_x1^2);

    // p[4]: x3 + x1 + x0
    polynomial_ref p4(pm);
    p4 = _x3 + _x1 + _x0;

    // Set sample: x0=-7, x1=-1, x2=1, x3=8
    scoped_anum val(am);
    am.set(val, -7); sample_as.set(x0, val);
    am.set(val, -1); sample_as.set(x1, val);
    am.set(val, 1);  sample_as.set(x2, val);
    am.set(val, 8);  sample_as.set(x3, val);
    
    // Counterexample: x0=-4, x1=-8, x2=5, x3=6
    am.set(val, -4); counter_as.set(x0, val);
    am.set(val, -8); counter_as.set(x1, val);
    am.set(val, 5);  counter_as.set(x2, val);
    am.set(val, 6);  counter_as.set(x3, val);

    // Set solver assignment for levelwise
    s.set_rvalues(sample_as);

    // Build polynomial vector
    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);
    polys.push_back(p3);
    polys.push_back(p4);

    unsigned max_x = x3;

    // Run levelwise
    nlsat::levelwise lws(s, polys, max_x, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();

    // Sanity-check: the counterexample must truly be a counterexample
    ENSURE(has_different_sign(am, pm, polys, sample_as, counter_as));

    // Counterexample must be OUTSIDE the cell
    ENSURE(!is_point_inside_cell(am, pm, cell, counter_as));
    
    std::cout << "=== END tst_17 ===\n\n";
}

// Test case for unsound lemma from From_T2__n-46.t2__p4432_terminationG_0.smt2
// This test calls levelwise with the input polynomials and analyzes what was missed.
//
// Input polynomials passed to levelwise:
//   p[0]: x2
//   p[1]: x2 x6^2 + x0 x5 x6 + x2 x4 x6 + x2 x3 x6 - x0 x6 - x0 x4
//   p[2]: x2 x6^2 x7 + x0 x5 x6 x7 + x2 x4 x6 x7 + x2 x3 x6 x7 - x0 x6 x7 - x0 x4 x7 + 2 x6 + 2 x4
//   p[3]: x6
//   p[4]: x2 x6 x7 - 2
//
// Sample: x0=1, x1=2, x2=1, x3=-1, x4=-1, x5=1, x6=7/8
// Counterexample: x0=1, x2=1, x3=0, x4=-9, x5=0, x6=5, x7=0
//
// Unsound lemma produced:
//   !(x0 > 0) or !(x2 > 0) or !(x4 < root[1](2 x2 x4 + x0)) or 
//   !(x5 = root[1](x0 x5 + x2 x3)) or 
//   !(x0^2 x5^2 + ... > 0) or !(2 x2 > 0) or 
//   !(4 x2 x6 + x0 x5 + 2 x2 x4 + x2 x3 - x0 > 0) or
//   !(2 x2 x6^2 + x0 x5 x6 + 2 x2 x4 x6 + x2 x3 x6 - x0 x6 - x0 x4 < 0) or
//   x7 < root[1](x2 x6^2 x7 + ... + 2 x6 + 2 x4) or 
//   !(x7 < root[1](x2 x6 x7 - 2))
static void tst_18() {
    std::cout << "=== tst_18 ===\n";
    
    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);
    polynomial::cache cache(pm);

    // Create 8 variables x0-x7
    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);
    nlsat::var x4 = s.mk_var(false);
    nlsat::var x5 = s.mk_var(false);
    nlsat::var x6 = s.mk_var(false);
    nlsat::var x7 = s.mk_var(false);

    polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm), _x4(pm), _x5(pm), _x6(pm), _x7(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);
    _x4 = pm.mk_polynomial(x4);
    _x5 = pm.mk_polynomial(x5);
    _x6 = pm.mk_polynomial(x6);
    _x7 = pm.mk_polynomial(x7);
    (void)_x1; // unused

    // Input polynomials passed to levelwise (from unsound_log)
    // p[0]: x2
    polynomial_ref p0(pm);
    p0 = _x2;

    // p[1]: x2 x6^2 + x0 x5 x6 + x2 x4 x6 + x2 x3 x6 - x0 x6 - x0 x4
    polynomial_ref p1(pm);
    p1 = _x2 * (_x6^2) + _x0 * _x5 * _x6 + _x2 * _x4 * _x6 + _x2 * _x3 * _x6 - _x0 * _x6 - _x0 * _x4;

    // p[2]: x2 x6^2 x7 + x0 x5 x6 x7 + x2 x4 x6 x7 + x2 x3 x6 x7 - x0 x6 x7 - x0 x4 x7 + 2 x6 + 2 x4
    polynomial_ref p2(pm);
    p2 = _x2 * (_x6^2) * _x7 + _x0 * _x5 * _x6 * _x7 + _x2 * _x4 * _x6 * _x7 
       + _x2 * _x3 * _x6 * _x7 - _x0 * _x6 * _x7 - _x0 * _x4 * _x7 
       + 2 * _x6 + 2 * _x4;

    // p[3]: x6
    polynomial_ref p3(pm);
    p3 = _x6;

    // p[4]: x2 x6 x7 - 2
    polynomial_ref p4(pm);
    p4 = _x2 * _x6 * _x7 - 2;

    // Set sample point: x0=1, x1=2, x2=1, x3=-1, x4=-1, x5=1, x6=7/8
    scoped_anum val(am);
    rational q(7, 8);
    am.set(val, 1);  sample_as.set(x0, val);
    am.set(val, 2);  sample_as.set(x1, val);
    am.set(val, 1);  sample_as.set(x2, val);
    am.set(val, -1); sample_as.set(x3, val);
    am.set(val, -1); sample_as.set(x4, val);
    am.set(val, 1);  sample_as.set(x5, val);
    am.set(val, q.to_mpq()); sample_as.set(x6, val);

    // Set counterexample: x0=1, x2=1, x3=0, x4=-9, x5=0, x6=5, x7=0
    am.set(val, 1);  counter_as.set(x0, val);
    am.set(val, 0);  counter_as.set(x1, val);
    am.set(val, 1);  counter_as.set(x2, val);
    am.set(val, 0);  counter_as.set(x3, val);
    am.set(val, -9); counter_as.set(x4, val);
    am.set(val, 0);  counter_as.set(x5, val);
    am.set(val, 5);  counter_as.set(x6, val);
    am.set(val, 0);  counter_as.set(x7, val);

    // Set solver assignment for levelwise
    s.set_rvalues(sample_as);

    // Build polynomial vector
    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);
    polys.push_back(p3);
    polys.push_back(p4);

    nlsat::var max_x = x7;

    // Run levelwise
    nlsat::levelwise lws(s, polys, max_x, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();

    // Verify discriminant projection fix:
    // Level 4 should be a SECTION (disc of p1 w.r.t. x6 has factor x2*x4+x0)
    ENSURE(cell.size() > 4);
    ENSURE(cell[4].section);

    // Sanity-check: the counterexample must truly be a counterexample
    ENSURE(has_different_sign(am, pm, polys, sample_as, counter_as));

    // Counterexample must be OUTSIDE the cell
    ENSURE(!is_point_inside_cell(am, pm, cell, counter_as));
    
    std::cout << "=== END tst_18 ===\n\n";
}

// Test case for unsound lemma from From_AProVE_2014__Et4-rec.jar-obl-8__p28996_terminationG_0.smt2
// Sample: x0=4, x1=5, x2=3.5, x3=-8, x4=5
// Counterexample: x0=5, x3=3, x4=0, x5=0
// Polynomials:
//   p[0]: x0
//   p[1]: 2 x0 x4^2 + 2 x3 x4 - x0 x4 - 2 x3
//   p[2]: 2 x0 x4^2 x5 + 2 x3 x4 x5 - x0 x4 x5 - 2 x3 x5 + 4 x3 x4^2 + 9 x0 x3 x4 - 26 x3 x4 - 3 x0 x4
//   p[3]: x5 - 9
static void tst_19() {
    std::cout << "=== tst_19 ===\n";
    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);
    polynomial::cache cache(pm);

    // Create 6 variables x0, x1, x2, x3, x4, x5
    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);
    nlsat::var x4 = s.mk_var(false);
    nlsat::var x5 = s.mk_var(false);

    polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm), _x4(pm), _x5(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);
    _x4 = pm.mk_polynomial(x4);
    _x5 = pm.mk_polynomial(x5);

    // p[0]: x0
    polynomial_ref p0(pm);
    p0 = _x0;

    // p[1]: 2 x0 x4^2 + 2 x3 x4 - x0 x4 - 2 x3
    polynomial_ref p1(pm);
    p1 = 2 * _x0 * (_x4^2) + 2 * _x3 * _x4 - _x0 * _x4 - 2 * _x3;

    // p[2]: 2 x0 x4^2 x5 + 2 x3 x4 x5 - x0 x4 x5 - 2 x3 x5 + 4 x3 x4^2 + 9 x0 x3 x4 - 26 x3 x4 - 3 x0 x4
    polynomial_ref p2(pm);
    p2 = 2 * _x0 * (_x4^2) * _x5 
       + 2 * _x3 * _x4 * _x5 
       - _x0 * _x4 * _x5 
       - 2 * _x3 * _x5 
       + 4 * _x3 * (_x4^2) 
       + 9 * _x0 * _x3 * _x4 
       - 26 * _x3 * _x4 
       - 3 * _x0 * _x4;

    // p[3]: x5 - 9
    polynomial_ref p3(pm);
    p3 = _x5 - 9;

    // Sample: x0=4, x1=5, x2=3.5, x3=-8, x4=5
    scoped_anum val(am);
    am.set(val, 4);  sample_as.set(x0, val);
    am.set(val, 5);  sample_as.set(x1, val);
    rational q(7, 2);  // 3.5
    am.set(val, q.to_mpq());  sample_as.set(x2, val);
    am.set(val, -8); sample_as.set(x3, val);
    am.set(val, 5);  sample_as.set(x4, val);
    // x5 not assigned (top level)
    
    // Counterexample: x0=5, x3=3, x4=0, x5=0
    am.set(val, 5);  counter_as.set(x0, val);
    am.set(val, 5);  counter_as.set(x1, val);
    am.set(val, q.to_mpq());  counter_as.set(x2, val);
    am.set(val, 3);  counter_as.set(x3, val);
    am.set(val, 0);  counter_as.set(x4, val);
    am.set(val, 0);  counter_as.set(x5, val);

    // sample_full includes x5=0 for sign evaluation
    nlsat::assignment sample_full(am);
    am.set(val, 4);  sample_full.set(x0, val);
    am.set(val, 5);  sample_full.set(x1, val);
    am.set(val, q.to_mpq());  sample_full.set(x2, val);
    am.set(val, -8); sample_full.set(x3, val);
    am.set(val, 5);  sample_full.set(x4, val);
    am.set(val, 0);  sample_full.set(x5, val);

    // Set solver assignment for levelwise (without x5)
    s.set_rvalues(sample_as);

    // Build polynomial vector
    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);
    polys.push_back(p3);

    unsigned max_x = x5;

    // Run levelwise
    nlsat::levelwise lws(s, polys, max_x, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();

    // Sanity-check: the counterexample must truly be a counterexample
    ENSURE(has_different_sign(am, pm, polys, sample_full, counter_as));

    // Counterexample must be OUTSIDE the cell
    ENSURE(!is_point_inside_cell(am, pm, cell, counter_as));
    
    std::cout << "=== END tst_19 ===\n\n";
}

// Test case for unsound lemma with disc=0 at sample for same_boundary_poly sector case
// Polynomials:
//   p[0]: - x2^3 + x1^3 x2 - x1^4
//   p[1]: - x2^3 x3 + x1^3 x2 x3 - x1^4 x3 - x2^3 + x1^3 x2^2 + 4 x1^4 x2 - x1^3 x2 - x1^5 - x1^4
//   p[2]: x3
// Sample: x0=1, x1=1, x2=1
// Counterexample: x1=12, x2=16, x3=0
static void tst_20() {
    std::cout << "=== tst_20 ===\n";

    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);
    polynomial::cache cache(pm);

    // Create 4 variables x0-x3
    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);

    polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);
    (void)_x0; // unused

    // p[0]: - x2^3 + x1^3 x2 - x1^4
    polynomial_ref p0(pm);
    p0 = -(_x2^3) + (_x1^3) * _x2 - (_x1^4);

    // p[1]: - x2^3 x3 + x1^3 x2 x3 - x1^4 x3 - x2^3 + x1^3 x2^2 + 4 x1^4 x2 - x1^3 x2 - x1^5 - x1^4
    polynomial_ref p1(pm);
    p1 = -(_x2^3) * _x3 + (_x1^3) * _x2 * _x3 - (_x1^4) * _x3
       - (_x2^3) + (_x1^3) * (_x2^2) + 4 * (_x1^4) * _x2 - (_x1^3) * _x2 - (_x1^5) - (_x1^4);

    // p[2]: x3
    polynomial_ref p2(pm);
    p2 = _x3;

    std::cout << "Input polynomials:\n";
    std::cout << "  p0: " << p0 << "\n";
    std::cout << "  p1: " << p1 << "\n";
    std::cout << "  p2: " << p2 << "\n\n";

    // Set sample point: x0=1, x1=1, x2=1
    scoped_anum val(am);
    am.set(val, 1);  sample_as.set(x0, val);
    am.set(val, 1);  sample_as.set(x1, val);
    am.set(val, 1);  sample_as.set(x2, val);

    std::cout << "Sample point: x0=1, x1=1, x2=1\n";

    // Set counterexample: x1=12, x2=16, x3=0
    am.set(val, 1);  counter_as.set(x0, val);
    am.set(val, 12); counter_as.set(x1, val);
    am.set(val, 16); counter_as.set(x2, val);
    am.set(val, 0);  counter_as.set(x3, val);

    std::cout << "Counterexample: x1=12, x2=16, x3=0\n\n";

    // Set solver assignment for levelwise
    s.set_rvalues(sample_as);

    // Build polynomial vector
    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);

    nlsat::var max_x = x3;

    // Run levelwise
    std::cout << "Running levelwise with max_x = x3...\n";
    nlsat::levelwise lws(s, polys, max_x, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();

    std::cout << "Cell intervals:\n";
    for (unsigned i = 0; i < cell.size(); ++i) {
        std::cout << "  Level " << i << ": ";
        nlsat::display(std::cout, s, cell[i]) << "\n";
    }

    // Print the lemma produced by levelwise
    std::cout << "\n--- LEMMA from levelwise ---\n";
    for (unsigned i = 0; i < cell.size(); ++i) {
        auto const& interval = cell[i];
        if (interval.section) {
            std::cout << "!(x" << i << " = root[" << interval.l_index << "](";
            pm.display(std::cout, interval.l) << "))\n";
        } else {
            if (!interval.l_inf()) {
                std::cout << "!(x" << i << " > root[" << interval.l_index << "](";
                pm.display(std::cout, interval.l) << "))\n";
            }
            if (!interval.u_inf()) {
                std::cout << "!(x" << i << " < root[" << interval.u_index << "](";
                pm.display(std::cout, interval.u) << "))\n";
            }
        }
    }
    std::cout << "--- END LEMMA ---\n\n";

    // Check sign of p0 at sample vs counterexample
    std::cout << "=== Checking sign of p0 (projection poly) ===\n";
    sign p0_sample = am.eval_sign_at(p0, sample_as);
    sign p0_counter = am.eval_sign_at(p0, counter_as);
    std::cout << "  p0 at sample (x1=1, x2=1): " << p0_sample << "\n";
    std::cout << "  p0 at counter (x1=12, x2=16): " << p0_counter << "\n";
    std::cout << "  Signs " << (p0_sample == p0_counter ? "match" : "DIFFER") << "\n";

    // Check if counterexample is inside the cell at each level
    // For soundness: if counter has different poly sign, it MUST be outside the cell
    std::cout << "\n=== Checking if counterexample is in the cell ===\n";
    bool counter_outside = false;

    // Level 0: (-oo, +oo) - always inside
    std::cout << "Level 0: (-oo, +oo) -> counter inside\n";

    // Level 1: check if x1=12 is in the cell
    {
        auto const& interval = cell[1];
        if (!interval.l_inf()) {
            polynomial_ref lower_p(interval.l, pm);
            scoped_anum_vector lower_roots(am);
            // Partial assignment for level 1 (just x0)
            nlsat::assignment partial_as(am);
            scoped_anum val0(am);
            am.set(val0, 1);  // counter x0 = 1
            partial_as.set(x0, val0);
            am.isolate_roots(lower_p, nlsat::undef_var_assignment(partial_as, 1), lower_roots);
            if (lower_roots.size() >= interval.l_index) {
                scoped_anum counter_x1(am);
                am.set(counter_x1, 12);
                int cmp = am.compare(counter_x1, lower_roots[interval.l_index - 1]);
                std::cout << "Level 1 lower bound: root[" << interval.l_index << "] of poly, counter x1=12 is "
                          << (cmp > 0 ? "ABOVE" : (cmp < 0 ? "BELOW" : "AT")) << " lower bound\n";
                if (cmp <= 0) counter_outside = true;
            }
        }
        if (!interval.u_inf()) {
            polynomial_ref upper_p(interval.u, pm);
            scoped_anum_vector upper_roots(am);
            // Partial assignment for level 1 (just x0)
            nlsat::assignment partial_as(am);
            scoped_anum val0(am);
            am.set(val0, 1);  // counter x0 = 1
            partial_as.set(x0, val0);
            am.isolate_roots(upper_p, nlsat::undef_var_assignment(partial_as, 1), upper_roots);
            if (upper_roots.size() >= interval.u_index) {
                scoped_anum counter_x1(am);
                am.set(counter_x1, 12);
                int cmp = am.compare(counter_x1, upper_roots[interval.u_index - 1]);
                std::cout << "Level 1 upper bound: root[" << interval.u_index << "] of poly, counter x1=12 is "
                          << (cmp > 0 ? "ABOVE" : (cmp < 0 ? "BELOW" : "AT")) << " upper bound\n";
                if (cmp >= 0) counter_outside = true;
            }
        }
    }

    // For a sound cell, if polynomial signs differ, counter MUST be outside the cell
    // The fix (projecting p0's discriminant) should create bounds that exclude the counterexample
    // Sanity-check: the counterexample must truly be a counterexample,
    // i.e. at least one input polynomial has a different sign.
    ENSURE(has_different_sign(am, pm, polys, sample_as, counter_as));

    if (p0_sample != p0_counter) {
        std::cout << "\nPoly signs differ between sample and counter.\n";
        std::cout << "For cell to be sound, counter must be OUTSIDE the cell.\n";
        std::cout << "Counter is " << (counter_outside ? "OUTSIDE" : "INSIDE") << " the cell.\n";
        ENSURE(counter_outside);  // Cell is sound if counter is outside
    } else {
        std::cout << "\nPoly signs match - cell is trivially sound.\n";
    }

    std::cout << "\n=== END tst_20 ===\n\n";
}

// Test case for unsound lemma from ppblockterm.t2__p7867_terminationG_0.smt2
// Issue z3-76w: levelwise produces unsound cell
static void tst_21() {
    std::cout << "=== tst_21 ===\n";
    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    polynomial::cache cache(pm);

    // Create 25 variables x0 to x24
    nlsat::var vars[25];
    polynomial_ref xvars[25] = {
        polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm),
        polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm),
        polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm),
        polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm),
        polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm), polynomial_ref(pm)
    };
    
    for (unsigned i = 0; i < 25; i++) {
        vars[i] = s.mk_var(false);
        xvars[i] = pm.mk_polynomial(vars[i]);
    }

    // Aliases for readability
    polynomial_ref &x2 = xvars[2], &x4 = xvars[4], &x5 = xvars[5];
    polynomial_ref &x9 = xvars[9], &x10 = xvars[10], &x11 = xvars[11];
    polynomial_ref &x12 = xvars[12], &x13 = xvars[13], &x15 = xvars[15];
    polynomial_ref &x16 = xvars[16], &x19 = xvars[19], &x24 = xvars[24];

    // p[0]: x16 + x9
    polynomial_ref p0(pm);
    p0 = x16 + x9;

    // p[1]: x16 x24 + x9 x24 + x13 x19 + x5 x19 + x12 x15 + x10 x15 - 2
    polynomial_ref p1(pm);
    p1 = x16 * x24 + x9 * x24 + x13 * x19 + x5 * x19 + x12 * x15 + x10 * x15 - 2;

    // p[2]: x4
    polynomial_ref p2(pm);
    p2 = x4;

    // p[3]: x4 x24 + x2 x19 + x11 x15
    polynomial_ref p3(pm);
    p3 = x4 * x24 + x2 * x19 + x11 * x15;

    std::cout << "Input polynomials:\n";
    std::cout << "  p0: " << p0 << "\n";
    std::cout << "  p1: " << p1 << "\n";
    std::cout << "  p2: " << p2 << "\n";
    std::cout << "  p3: " << p3 << "\n\n";

    // Set sample point values
    // x0->1, x1->1, x2->-1, x3->-1, x4->1, x5->-1, x6->1, x7->2, x8->1
    // x9->1, x10->-1, x11->1, x12->-2, x13->-2, x14->-2, x15->0, x16->2
    // x17->0, x18->0, x19->0, x20->0, x21->0, x22->0, x23->0
    int sample_vals[24] = {1, 1, -1, -1, 1, -1, 1, 2, 1, 1, -1, 1, -2, -2, -2, 0, 2, 0, 0, 0, 0, 0, 0, 0};
    
    scoped_anum val(am);
    nlsat::assignment sample_as(am);
    for (unsigned i = 0; i < 24; i++) {
        am.set(val, sample_vals[i]);
        sample_as.set(vars[i], val);
    }
    s.set_rvalues(sample_as);

    std::cout << "Sample point (x0..x23):\n";
    for (unsigned i = 0; i < 24; i++) {
        std::cout << "  x" << i << " -> " << sample_vals[i] << "\n";
    }
    std::cout << "\n";

    // Evaluate polynomials at sample (with x24 = 0 for checking)
    am.set(val, 0);
    sample_as.set(vars[24], val);
    std::cout << "Polynomial signs at sample (x24=0):\n";
    std::cout << "  p0 sign: " << am.eval_sign_at(p0, sample_as) << "\n";
    std::cout << "  p1 sign: " << am.eval_sign_at(p1, sample_as) << "\n";
    std::cout << "  p2 sign: " << am.eval_sign_at(p2, sample_as) << "\n";
    std::cout << "  p3 sign: " << am.eval_sign_at(p3, sample_as) << "\n\n";

    // Counterexample from the unsound lemma:
    // x2=-1, x4=1, x5=0, x9=0, x10=0, x11=-1, x12=-1, x13=-2, x15=3, x16=2, x19=0, x24=3
    nlsat::assignment counter_as(am);
    am.set(val, -1); counter_as.set(vars[2], val);
    am.set(val, 1);  counter_as.set(vars[4], val);
    am.set(val, 0);  counter_as.set(vars[5], val);
    am.set(val, 0);  counter_as.set(vars[9], val);
    am.set(val, 0);  counter_as.set(vars[10], val);
    am.set(val, -1); counter_as.set(vars[11], val);
    am.set(val, -1); counter_as.set(vars[12], val);
    am.set(val, -2); counter_as.set(vars[13], val);
    am.set(val, 3);  counter_as.set(vars[15], val);
    am.set(val, 2);  counter_as.set(vars[16], val);
    am.set(val, 0);  counter_as.set(vars[19], val);
    am.set(val, 3);  counter_as.set(vars[24], val);

    std::cout << "Counterexample point:\n";
    std::cout << "  x2=-1, x4=1, x5=0, x9=0, x10=0, x11=-1, x12=-1, x13=-2, x15=3, x16=2, x19=0, x24=3\n\n";

    std::cout << "Polynomial signs at counterexample:\n";
    std::cout << "  p0 sign: " << am.eval_sign_at(p0, counter_as) << "\n";
    std::cout << "  p1 sign: " << am.eval_sign_at(p1, counter_as) << "\n";
    std::cout << "  p2 sign: " << am.eval_sign_at(p2, counter_as) << "\n";
    std::cout << "  p3 sign: " << am.eval_sign_at(p3, counter_as) << "\n\n";

    // Build polynomial vector
    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);
    polys.push_back(p3);

    unsigned max_x = vars[24];  // x24 is the highest variable

    std::cout << "Running levelwise with max_x = x24...\n";
    nlsat::levelwise lws(s, polys, max_x, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();
    
    std::cout << "Levelwise succeeded\n";
    std::cout << "--- LEMMA from levelwise ---\n";
    for (unsigned i = 0; i < cell.size(); i++) {
        auto const& interval = cell[i];
        std::cout << "Level x" << i << ": ";
        if (interval.is_section()) {
            std::cout << "section at root[" << interval.l_index << "] of " << interval.l << "\n";
        } else {
            if (interval.l_inf())
                std::cout << "(-oo, ";
            else
                std::cout << "(root[" << interval.l_index << "] of " << interval.l << ", ";
            if (interval.u_inf())
                std::cout << "+oo)";
            else
                std::cout << "root[" << interval.u_index << "] of " << interval.u << ")";
            std::cout << "\n";
        }

        std::cout << "--- END LEMMA ---\n\n";
        
        // Sanity-check: the counterexample must truly be a counterexample,
        // i.e. at least one input polynomial has a different sign.
        ENSURE(has_different_sign(am, pm, polys, sample_as, counter_as));
        
        // Verify that the counterexample is OUTSIDE the cell (cell is sound)
        std::cout << "\nChecking if counterexample is inside cell:\n";
        bool inside = is_point_inside_cell(am, pm, cell, counter_as);
        
        // For a sound cell with differing signs, counterexample must be OUTSIDE
        ENSURE(!inside);
        std::cout << "SUCCESS: Counterexample is OUTSIDE the cell (cell is sound)\n";
    }

    std::cout << "=== END tst_21 ===\n\n";
}

// Test case for gh-8397: unsound lemma with lws=false
// Unsound lemma detected by nlsat.check_lemmas=true:
// !(1024 x1 = 0) or !(x1 + 1 > 0) or !(2048 x1^2 + 4096 x1 = 0) or 
// !(x1 = root[3](1024 x1^3 + 6144 x1^2 + 6144 x1)) or 
// !(x1 = root[3](2048 x1^3 + 6144 x1^2 + 4096 x1)) or !(x1 = 0) or 
// 4 x6^3 + 4 x5 x6^2 - 4 x1 x6^2 + 4 x6^2 - 4 x1 x5 x6 - 4 x1 x6 < 0 or 
// x6 - x1 = 0 or x6 > 0
// Counterexample: x1 = 0, x5 = 0, x6 = -0.5
static void tst_22() {
    // Reproduce exact unsound lemma from gh-8397
    // Unsound lemma: !(1024 x1 = 0) or !(x1 + 1 > 0) or !(2048 x1^2 + 4096 x1 = 0) or 
    //   !(x1 = root[3](1024 x1^3 + 6144 x1^2 + 6144 x1)) or 
    //   !(x1 = root[3](2048 x1^3 + 6144 x1^2 + 4096 x1)) or !(x1 = 0) or 
    //   4 x6^3 + 4 x5 x6^2 - 4 x1 x6^2 + 4 x6^2 - 4 x1 x5 x6 - 4 x1 x6 < 0 or x6 - x1 = 0 or x6 > 0
    // Counterexample: x1=0, x5=0, x6=-0.5 makes ALL literals FALSE
    // Sample point: x0=-1, x1=0, x2=0, x3=-1, x4=0, x5=-1 (x6 is conflict var)
    std::cout << "=== tst_22 ===\n";
    
    auto run_test = [](bool use_lws) {
        std::cout << "\n--- Running with lws=" << (use_lws ? "true" : "false") << " ---\n";
        
        params_ref ps;
        ps.set_bool("lws", use_lws);
        reslimit rlim;
        nlsat::solver s(rlim, ps, false);
        anum_manager& am = s.am();
        nlsat::pmanager& pm = s.pm();
        nlsat::explain& ex = s.get_explain();
        
        // Create variables in order: x0, x1, x2, x3, x4, x5, x6
        nlsat::var x0 = s.mk_var(false);
        nlsat::var x1 = s.mk_var(false);
        nlsat::var x2 = s.mk_var(false);
        nlsat::var x3 = s.mk_var(false);
        nlsat::var x4 = s.mk_var(false);
        nlsat::var x5 = s.mk_var(false);
        nlsat::var x6 = s.mk_var(false);
        (void)x0; (void)x2; (void)x3; (void)x4;  // suppress unused warnings
        
        polynomial_ref _x1(pm), _x5(pm), _x6(pm);
        _x1 = pm.mk_polynomial(x1);
        _x5 = pm.mk_polynomial(x5);
        _x6 = pm.mk_polynomial(x6);
        
        // Polynomials from the unsound lemma
        // p_main: 4 x6^3 + 4 x5 x6^2 - 4 x1 x6^2 + 4 x6^2 - 4 x1 x5 x6 - 4 x1 x6
        polynomial_ref p_main(pm);
        p_main = 4*_x6*_x6*_x6 + 4*_x5*_x6*_x6 - 4*_x1*_x6*_x6 + 4*_x6*_x6 - 4*_x1*_x5*_x6 - 4*_x1*_x6;
        
        // p_diff: x6 - x1
        polynomial_ref p_diff(pm);
        p_diff = _x6 - _x1;
        
        // Additional polynomials for x1 constraints (from root literals)
        // 1024 x1^3 + 6144 x1^2 + 6144 x1 = 1024*x1*(x1^2 + 6*x1 + 6)
        polynomial_ref p_root1(pm);
        p_root1 = 1024*_x1*_x1*_x1 + 6144*_x1*_x1 + 6144*_x1;
        
        // 2048 x1^3 + 6144 x1^2 + 4096 x1 = 1024*x1*(2*x1^2 + 6*x1 + 4)
        polynomial_ref p_root2(pm);
        p_root2 = 2048*_x1*_x1*_x1 + 6144*_x1*_x1 + 4096*_x1;
        
        // 1024 x1
        polynomial_ref p_x1_eq(pm);
        p_x1_eq = 1024*_x1;
        
        // x1 + 1
        polynomial_ref p_x1_gt(pm);
        p_x1_gt = _x1 + 1;
        
        // 2048 x1^2 + 4096 x1
        polynomial_ref p_x1_eq2(pm);
        p_x1_eq2 = 2048*_x1*_x1 + 4096*_x1;
        
        std::cout << "p_main: " << p_main << "\n";
        std::cout << "p_diff: " << p_diff << "\n";
        std::cout << "p_root1: " << p_root1 << "\n";
        std::cout << "p_root2: " << p_root2 << "\n";
        
        // Set sample point: x0=-1, x1=0, x2=0, x3=-1, x4=0, x5=-1
        nlsat::assignment sample_as(am);
        scoped_anum val(am);
        am.set(val, -1); sample_as.set(x0, val);
        am.set(val, 0);  sample_as.set(x1, val);
        am.set(val, 0);  sample_as.set(x2, val);
        am.set(val, -1); sample_as.set(x3, val);
        am.set(val, 0);  sample_as.set(x4, val);
        am.set(val, -1); sample_as.set(x5, val);
        // x6 is the conflict variable, set to 0 for sample
        am.set(val, 0);  sample_as.set(x6, val);
        s.set_rvalues(sample_as);
        
        // Input literals for the conflict (constraints on x6):
        // The conflict is that x6 > x1 (i.e. x6 > 0) AND p_main < 0 
        // But at sample point x1=0, x5=-1, these are infeasible at x6=0
        nlsat::scoped_literal_vector lits(s);
        lits.push_back(mk_gt(s, p_diff.get()));  // x6 - x1 > 0 (i.e. x6 > 0 since x1=0)
        lits.push_back(mk_lt(s, p_main.get()));  // p_main < 0
        
        // Also add x1 constraints that were part of the conflict core
        lits.push_back(mk_eq(s, p_x1_eq.get()));   // 1024 x1 = 0
        lits.push_back(mk_gt(s, p_x1_gt.get()));   // x1 + 1 > 0
        lits.push_back(mk_eq(s, p_x1_eq2.get()));  // 2048 x1^2 + 4096 x1 = 0
        // Root literals: x1 = root[3](p_root1), x1 = root[3](p_root2)
        lits.push_back(mk_root_eq(s, p_root1.get(), x1, 3));  // x1 = root[3](p_root1)
        lits.push_back(mk_root_eq(s, p_root2.get(), x1, 3));  // x1 = root[3](p_root2)
        lits.push_back(mk_eq(s, _x1.get()));       // x1 = 0
        
        std::cout << "Input literals:\n";
        s.display(std::cout, lits.size(), lits.data());
        std::cout << "\n";
        
        // Call compute_conflict_explanation
        nlsat::scoped_literal_vector result(s);
        ex.compute_conflict_explanation(lits.size(), lits.data(), result);
        
        std::cout << "Result lemma (lws=" << (use_lws ? "true" : "false") << "):\n";
        std::cout << "(or";
        for (auto l : result) {
            s.display(std::cout << "\n  ", l);
        }
        for (unsigned i = 0; i < lits.size(); ++i) {
            s.display(std::cout << "\n  ", ~lits[i]);
        }
        std::cout << "\n)\n";
        
        // Counterexample from checker: x1=0, x5=0, x6=-0.5
        nlsat::assignment counter_as(am);
        am.set(val, -1); counter_as.set(x0, val);
        am.set(val, 0);  counter_as.set(x1, val);
        am.set(val, 0);  counter_as.set(x2, val);
        am.set(val, -1); counter_as.set(x3, val);
        am.set(val, 0);  counter_as.set(x4, val);
        am.set(val, 0);  counter_as.set(x5, val);  // changed from -1 to 0
        mpq half; am.qm().set(half, -1, 2);  // -1/2
        am.set(val, half); counter_as.set(x6, val);
        
        std::cout << "\nEvaluating at counterexample (x1=0, x5=0, x6=-0.5):\n";
        
        // Evaluate each result literal at counterexample
        small_object_allocator allocator;
        nlsat::evaluator eval(s, counter_as, pm, allocator);
        
        bool all_false = true;
        for (auto l : result) {
            nlsat::atom* a = s.bool_var2atom(l.var());
            if (a) {
                bool value = eval.eval(a, l.sign());
                s.display(std::cout << "  ", l);
                std::cout << " -> " << (value ? "TRUE" : "FALSE") << "\n";
                if (value) all_false = false;
            }
        }
        
        // Also check negated input literals
        for (unsigned i = 0; i < lits.size(); ++i) {
            nlsat::literal nl = ~lits[i];
            nlsat::atom* a = s.bool_var2atom(nl.var());
            if (a) {
                bool value = eval.eval(a, nl.sign());
                s.display(std::cout << "  ", nl);
                std::cout << " -> " << (value ? "TRUE" : "FALSE") << "\n";
                if (value) all_false = false;
            }
        }
        
        if (all_false) {
            std::cout << "*** ALL literals FALSE at counterexample - LEMMA IS UNSOUND! ***\n";
        } else {
            std::cout << "At least one literal is TRUE - lemma is sound at this point\n";
        }
    };
    
    run_test(false);  // lws=false (buggy)
    run_test(true);   // lws=true (should be correct)
    
    std::cout << "\n=== END tst_22 ===\n\n";
}


// Test case for unsound lemma - nullified polynomial in levelwise
// Polynomials:
//   p[0]: - x6 + x3 x5 + 1
//   p[1]: - x2
//   p[2]: - 2 x2 x6^2 + 2 x3 x5 x6 - 2 x2 x5 x6 + x4 x5^3 + 2 x3 x5^2
// Sample: x0=4, x1=1, x2=1, x3=5/2, x4=0, x5=1
// Counterexample: x2=4, x3=-3, x4=0, x5=1, x6=-1
static void tst_23() {
    std::cout << "=== tst_23 ===\n";

    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);
    polynomial::cache cache(pm);

    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);
    nlsat::var x4 = s.mk_var(false);
    nlsat::var x5 = s.mk_var(false);
    nlsat::var x6 = s.mk_var(false);

    polynomial_ref _x2(pm), _x3(pm), _x4(pm), _x5(pm), _x6(pm);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);
    _x4 = pm.mk_polynomial(x4);
    _x5 = pm.mk_polynomial(x5);
    _x6 = pm.mk_polynomial(x6);

    polynomial_ref p0(pm), p1(pm), p2(pm);
    p0 = -_x6 + _x3 * _x5 + 1;
    p1 = -_x2;
    p2 = -2 * _x2 * (_x6^2) + 2 * _x3 * _x5 * _x6 - 2 * _x2 * _x5 * _x6
       + _x4 * (_x5^3) + 2 * _x3 * (_x5^2);

    std::cout << "  p0: " << p0 << "\n  p1: " << p1 << "\n  p2: " << p2 << "\n";

    // Sample: x0=4, x1=1, x2=1, x3=5/2, x4=0, x5=1
    scoped_anum val(am);
    rational five_half(5, 2);
    am.set(val, 4);  sample_as.set(x0, val);
    am.set(val, 1);  sample_as.set(x1, val);
    am.set(val, 1);  sample_as.set(x2, val);
    am.set(val, five_half.to_mpq()); sample_as.set(x3, val);
    am.set(val, 0);  sample_as.set(x4, val);
    am.set(val, 1);  sample_as.set(x5, val);

    // Counterexample: x0=4, x1=1, x2=4, x3=-3, x4=0, x5=1, x6=-1
    am.set(val, 4);  counter_as.set(x0, val);
    am.set(val, 1);  counter_as.set(x1, val);
    am.set(val, 4);  counter_as.set(x2, val);
    am.set(val, -3); counter_as.set(x3, val);
    am.set(val, 0);  counter_as.set(x4, val);
    am.set(val, 1);  counter_as.set(x5, val);
    am.set(val, -1); counter_as.set(x6, val);

    s.set_rvalues(sample_as);

    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);

    nlsat::levelwise lws(s, polys, x6, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();

    std::cout << "Cell intervals:\n";
    for (unsigned i = 0; i < cell.size(); ++i)
        nlsat::display(std::cout << "  Level " << i << ": ", s, cell[i]) << "\n";

    bool inside = is_point_inside_cell(am, pm, cell, counter_as);
    // The counterexample should be OUTSIDE the cell for soundness.
    ENSURE(!inside);
    std::cout << "=== END tst_23 ===\n\n";
}

// Test case for unsound lemma - nullified polynomial with x4=3/4
// Polynomials:
//   p[0]: x2
//   p[1]: x5 + x4
//   p[2]: x2^2 x5 x6 + x2^2 x4 x6 + 2 x2^2 x3 x5 + x0 x2^2 x5 - 3 x0 x1 x2 x5 - 2 x0 x1^2 x5 + 2 x2^2 x3 x4 + 2 x0 x2^2 x4
//   p[3]: x5
//   p[4]: x2 x5 x6 - x0 x1 x5 - x0 x5 + x0 x2 x4
// Sample: x0=1, x1=0, x2=-1, x3=0, x4=3/4, x5=1
// Counterexample: x0=1, x1=-1, x2=-1, x3=2, x4=1, x5=1, x6=-2
static void tst_24() {
    std::cout << "=== tst_24 ===\n";

    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);
    polynomial::cache cache(pm);

    nlsat::var x0 = s.mk_var(false);
    nlsat::var x1 = s.mk_var(false);
    nlsat::var x2 = s.mk_var(false);
    nlsat::var x3 = s.mk_var(false);
    nlsat::var x4 = s.mk_var(false);
    nlsat::var x5 = s.mk_var(false);
    nlsat::var x6 = s.mk_var(false);

    polynomial_ref _x0(pm), _x1(pm), _x2(pm), _x3(pm), _x4(pm), _x5(pm), _x6(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _x3 = pm.mk_polynomial(x3);
    _x4 = pm.mk_polynomial(x4);
    _x5 = pm.mk_polynomial(x5);
    _x6 = pm.mk_polynomial(x6);

    polynomial_ref p0(pm), p1(pm), p2(pm), p3(pm), p4(pm);
    p0 = _x2;
    p1 = _x5 + _x4;
    p2 = (_x2^2) * _x5 * _x6 + (_x2^2) * _x4 * _x6
       + 2 * (_x2^2) * _x3 * _x5 + _x0 * (_x2^2) * _x5
       - 3 * _x0 * _x1 * _x2 * _x5 - 2 * _x0 * (_x1^2) * _x5
       + 2 * (_x2^2) * _x3 * _x4 + 2 * _x0 * (_x2^2) * _x4;
    p3 = _x5;
    p4 = _x2 * _x5 * _x6 - _x0 * _x1 * _x5 - _x0 * _x5 + _x0 * _x2 * _x4;

    std::cout << "  p0: " << p0 << "\n  p1: " << p1 << "\n  p2: " << p2
              << "\n  p3: " << p3 << "\n  p4: " << p4 << "\n";

    // Sample: x0=1, x1=0, x2=-1, x3=0, x4=3/4, x5=1
    scoped_anum val(am);
    rational three_quarter(3, 4);
    am.set(val, 1);  sample_as.set(x0, val);
    am.set(val, 0);  sample_as.set(x1, val);
    am.set(val, -1); sample_as.set(x2, val);
    am.set(val, 0);  sample_as.set(x3, val);
    am.set(val, three_quarter.to_mpq()); sample_as.set(x4, val);
    am.set(val, 1);  sample_as.set(x5, val);

    // Counterexample: x0=1, x1=-1, x2=-1, x3=2, x4=1, x5=1, x6=-2
    am.set(val, 1);  counter_as.set(x0, val);
    am.set(val, -1); counter_as.set(x1, val);
    am.set(val, -1); counter_as.set(x2, val);
    am.set(val, 2);  counter_as.set(x3, val);
    am.set(val, 1);  counter_as.set(x4, val);
    am.set(val, 1);  counter_as.set(x5, val);
    am.set(val, -2); counter_as.set(x6, val);

    s.set_rvalues(sample_as);

    polynomial_ref_vector polys(pm);
    polys.push_back(p0);
    polys.push_back(p1);
    polys.push_back(p2);
    polys.push_back(p3);
    polys.push_back(p4);

    nlsat::levelwise lws(s, polys, x6, s.sample(), pm, am, cache);
    auto cell = lws.single_cell();

    std::cout << "Cell intervals:\n";
    for (unsigned i = 0; i < cell.size(); ++i)
        nlsat::display(std::cout << "  Level " << i << ": ", s, cell[i]) << "\n";

    bool inside = is_point_inside_cell(am, pm, cell, counter_as);
    // The counterexample should be OUTSIDE the cell for soundness.
    ENSURE(!inside);
    std::cout << "=== END tst_24 ===\n\n";
}

// Test that compute_conflict_explanation produces a lemma where the counterexample
// falsifies at least one literal. Reproducer from p6236_terminationG_0.smt2.
static void tst_25() {
    std::cout << "=== tst_25 ===\n";

    params_ref      ps;
    ps.set_bool("lws", true);
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment sample_as(am);
    nlsat::assignment counter_as(am);

    // Create 16 variables x0-x15
    nlsat::var x0  = s.mk_var(false);
    nlsat::var x1  = s.mk_var(false);
    nlsat::var x2  = s.mk_var(false);
    nlsat::var x3  = s.mk_var(false);
    nlsat::var x4  = s.mk_var(false);
    nlsat::var x5  = s.mk_var(false);
    nlsat::var x6  = s.mk_var(false);
    nlsat::var x7  = s.mk_var(false);
    nlsat::var x8  = s.mk_var(false);
    nlsat::var x9  = s.mk_var(false);
    nlsat::var x10 = s.mk_var(false);
    nlsat::var x11 = s.mk_var(false);
    nlsat::var x12 = s.mk_var(false);
    nlsat::var x13 = s.mk_var(false);
    nlsat::var x14 = s.mk_var(false);
    nlsat::var x15 = s.mk_var(false);

    polynomial_ref _x0(pm), _x3(pm), _x4(pm), _x5(pm), _x6(pm);
    polynomial_ref _x9(pm), _x10(pm), _x11(pm), _x13(pm), _x14(pm), _x15(pm);
    _x0  = pm.mk_polynomial(x0);
    _x3  = pm.mk_polynomial(x3);
    _x4  = pm.mk_polynomial(x4);
    _x5  = pm.mk_polynomial(x5);
    _x6  = pm.mk_polynomial(x6);
    _x9  = pm.mk_polynomial(x9);
    _x10 = pm.mk_polynomial(x10);
    _x11 = pm.mk_polynomial(x11);
    _x13 = pm.mk_polynomial(x13);
    _x14 = pm.mk_polynomial(x14);
    _x15 = pm.mk_polynomial(x15);

    // p1: -x9*x15 - x10*x14 + x5*x11*x13 + x3*x4*x11 + 2
    polynomial_ref p1(pm);
    p1 = -_x9 * _x15 - _x10 * _x14 + _x5 * _x11 * _x13 + _x3 * _x4 * _x11 + 2;

    // p2: x15 + x6*x13 + x0*x4
    polynomial_ref p2(pm);
    p2 = _x15 + _x6 * _x13 + _x0 * _x4;

    // Build justification literals:
    //   jst lit[0]: !(x15 < root[1](p1))  =>  literal(root_lt_bvar, true)
    //   jst lit[1]: !(p2 > 0)             =>  literal(gt_bvar, true)
    nlsat::bool_var root_lt_bvar = s.mk_root_atom(nlsat::atom::ROOT_LT, x15, 1, p1.get());
    s.inc_ref(root_lt_bvar);
    nlsat::literal jst_lit0(root_lt_bvar, true);  // negated: !(x15 < root[1](p1))

    nlsat::literal gt_lit = mk_gt(s, p2.get());
    s.inc_ref(gt_lit);
    nlsat::literal jst_lit1 = ~gt_lit;            // negated: !(p2 > 0)

    nlsat::literal jst_lits[2] = { jst_lit0, jst_lit1 };

    // Sample: x0=1,x1=-1,x2=1,x3=-1,x4=2,x5=0,x6=0,x7=0,x8=0,x9=1,x10=0,x11=1/2,x12=1,x13=-4,x14=2
    scoped_anum val(am);
    rational half(1, 2);
    set_assignment_value(sample_as, am, x0, rational(1));
    set_assignment_value(sample_as, am, x1, rational(-1));
    set_assignment_value(sample_as, am, x2, rational(1));
    set_assignment_value(sample_as, am, x3, rational(-1));
    set_assignment_value(sample_as, am, x4, rational(2));
    set_assignment_value(sample_as, am, x5, rational(0));
    set_assignment_value(sample_as, am, x6, rational(0));
    set_assignment_value(sample_as, am, x7, rational(0));
    set_assignment_value(sample_as, am, x8, rational(0));
    set_assignment_value(sample_as, am, x9, rational(1));
    set_assignment_value(sample_as, am, x10, rational(0));
    set_assignment_value(sample_as, am, x11, half);
    set_assignment_value(sample_as, am, x12, rational(1));
    set_assignment_value(sample_as, am, x13, rational(-4));
    set_assignment_value(sample_as, am, x14, rational(2));

    s.set_rvalues(sample_as);

    // Compute conflict explanation
    nlsat::explain& ex = s.get_explain();
    nlsat::scoped_literal_vector result(s);
    ex.compute_conflict_explanation(2, jst_lits, result);

    // Build the full lemma: result literals + ~jst_lits
    nlsat::literal_vector lemma;
    for (unsigned i = 0; i < result.size(); ++i)
        lemma.push_back(result[i]);
    lemma.push_back(~jst_lits[0]);  // x15 < root[1](p1)
    lemma.push_back(~jst_lits[1]);  // p2 > 0

    std::cout << "Lemma (" << lemma.size() << " literals):\n";
    s.display(std::cout << "  ", lemma.size(), lemma.data()) << "\n";

    // Counterexample: x0=0,x3=-1,x4=1,x5=0,x6=0,x9=1,x10=0,x11=3,x13=0,x14=0,x15=0
    set_assignment_value(counter_as, am, x0, rational(0));
    set_assignment_value(counter_as, am, x1, rational(-1));
    set_assignment_value(counter_as, am, x2, rational(1));
    set_assignment_value(counter_as, am, x3, rational(-1));
    set_assignment_value(counter_as, am, x4, rational(1));
    set_assignment_value(counter_as, am, x5, rational(0));
    set_assignment_value(counter_as, am, x6, rational(0));
    set_assignment_value(counter_as, am, x7, rational(0));
    set_assignment_value(counter_as, am, x8, rational(0));
    set_assignment_value(counter_as, am, x9, rational(1));
    set_assignment_value(counter_as, am, x10, rational(0));
    set_assignment_value(counter_as, am, x11, rational(3));
    set_assignment_value(counter_as, am, x12, rational(1));
    set_assignment_value(counter_as, am, x13, rational(0));
    set_assignment_value(counter_as, am, x14, rational(0));
    set_assignment_value(counter_as, am, x15, rational(0));

    // Set counterexample as the solver's assignment for evaluation
    s.set_rvalues(counter_as);
    nlsat::evaluator& ev = s.get_evaluator();

    // At least one lemma literal must be true at the counterexample for soundness
    bool some_true = false;
    for (unsigned i = 0; i < lemma.size(); ++i) {
        nlsat::literal lit = lemma[i];
        nlsat::atom* a = s.bool_var2atom(lit.var());
        if (a == nullptr)
            continue;
        bool v = ev.eval(a, lit.sign());
        std::cout << "  lit[" << i << "]: ";
        s.display(std::cout, lit) << " = " << (v ? "true" : "false") << "\n";
        if (v)
            some_true = true;
    }

    ENSURE(some_true);

    s.dec_ref(root_lt_bvar);
    s.dec_ref(gt_lit);
    std::cout << "=== END tst_25 ===\n\n";
}

void tst_nlsat() {
    tst_22();
    std::cout << "------------------\n";    
    tst_25();
    std::cout << "------------------\n";
    tst_20();
    std::cout << "------------------\n";    
    tst_24();
    std::cout << "------------------\n";
    tst_23();
    std::cout << "------------------\n";
    tst_21();
    std::cout << "------------------\n";
    tst_18();
    std::cout << "------------------\n";
    tst_19();
    std::cout << "------------------\n";
    tst_17();
    std::cout << "------------------\n";
    tst_16();
    std::cout << "------------------\n";
    tst_14();
    std::cout << "------------------\n";
    tst_15();
    std::cout << "------------------\n";
    tst11();
    std::cout << "------------------\n";
    tst10();
    std::cout << "------------------\n";
    tst9();
    std::cout << "------------------\n";
    tst8();
    std::cout << "------------------\n";
    tst7();
    std::cout << "------------------\n";
    tst6();
    std::cout << "------------------\n";
    tst5();
    std::cout << "------------------\n";
    tst4();
    std::cout << "------------------\n";
    tst3();
}
