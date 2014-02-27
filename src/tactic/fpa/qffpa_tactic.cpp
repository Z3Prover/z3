/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffpa_tactic.cpp

Abstract:

    Tactic for QF_FPA benchmarks.

Author:

    Christoph (cwinter) 2012-01-16

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"bit_blaster_tactic.h"
#include"sat_tactic.h"
#include"fpa2bv_tactic.h"

#include"qffpa_tactic.h"

tactic * mk_qffpa_tactic(ast_manager & m, params_ref const & p) {
    params_ref sat_simp_p = p;
    sat_simp_p .set_bool("elim_and", true);

    return and_then(mk_simplify_tactic(m, p),
                    mk_fpa2bv_tactic(m, p),
                    using_params(mk_simplify_tactic(m, p), sat_simp_p),
                    mk_bit_blaster_tactic(m, p),
                    using_params(mk_simplify_tactic(m, p), sat_simp_p),
                    mk_sat_tactic(m, p),
                    mk_fail_if_undecided_tactic());
}

struct is_non_qffpa_predicate {
    struct found {};
    ast_manager & m;
    float_util    u;

    is_non_qffpa_predicate(ast_manager & _m) : m(_m), u(m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        sort * s = get_sort(n);
        if (!m.is_bool(s) && !u.is_float(s) && !u.is_rm(s))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return;
        if (fid == u.get_family_id())
            return;
        if (is_uninterp_const(n))
            return;

        throw found();
    }
};

struct is_non_qffpabv_predicate {
    struct found {};
    ast_manager & m;
    bv_util       bu;
    float_util    fu;

    is_non_qffpabv_predicate(ast_manager & _m) : m(_m), bu(m), fu(m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        sort * s = get_sort(n);
        if (!m.is_bool(s) && !fu.is_float(s) && !fu.is_rm(s) && !bu.is_bv_sort(s))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return;
        if (fid == fu.get_family_id() || fid == bu.get_family_id())
            return;
        if (is_uninterp_const(n))
            return;

        throw found();
    }
};

class is_qffpa_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return !test<is_non_qffpa_predicate>(g);
    }
};

class is_qffpabv_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return !test<is_non_qffpabv_predicate>(g);
    }
};

probe * mk_is_qffpa_probe() {
    return alloc(is_qffpa_probe);
}

probe * mk_is_qffpabv_probe() {
    return alloc(is_qffpabv_probe);
}
    