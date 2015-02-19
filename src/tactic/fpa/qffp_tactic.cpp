/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffpa_tactic.cpp

Abstract:

    Tactic for QF_FP benchmarks.

Author:

    Christoph (cwinter) 2012-01-16

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"bit_blaster_tactic.h"
#include"sat_tactic.h"
#include"fpa2bv_tactic.h"
#include"smt_tactic.h"
#include"propagate_values_tactic.h"

#include"qffp_tactic.h"

tactic * mk_qffp_tactic(ast_manager & m, params_ref const & p) {
    params_ref simp_p = p;
    simp_p.set_bool("arith_lhs", true);
    simp_p.set_bool("elim_and", true);

    tactic * st = and_then(mk_simplify_tactic(m, simp_p),
                           mk_propagate_values_tactic(m, p),
                           cond(mk_or(mk_produce_proofs_probe(), mk_produce_unsat_cores_probe()),
                                mk_smt_tactic(),
                                and_then(
                                     mk_fpa2bv_tactic(m, p),
                                     using_params(mk_simplify_tactic(m, p), simp_p),                                 
                                     mk_bit_blaster_tactic(m, p),
                                     using_params(mk_simplify_tactic(m, p), simp_p),                                 
                                     cond(mk_is_propositional_probe(),
                                        mk_sat_tactic(m, p),
                                        mk_smt_tactic(p)),
                                     mk_fail_if_undecided_tactic())));

    st->updt_params(p);
    return st;
}

tactic * mk_qffpbv_tactic(ast_manager & m, params_ref const & p) {
    return mk_qffp_tactic(m, p);
}

struct is_non_qffp_predicate {
    struct found {};
    ast_manager & m;
    bv_util       bu;
    fpa_util      fu;
    arith_util    au;

    is_non_qffp_predicate(ast_manager & _m) : m(_m), bu(m), fu(m), au(m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        sort * s = get_sort(n);
        if (!m.is_bool(s) && !fu.is_float(s) && !fu.is_rm(s) && !bu.is_bv_sort(s) && !au.is_real(s))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return;
        if (fid == fu.get_family_id() || fid == bu.get_family_id())
            return;
        if (is_uninterp_const(n))
            return;
        if (au.is_real(s) && au.is_numeral(n))
            return;

        throw found();
    }
};

class is_qffp_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return !test<is_non_qffp_predicate>(g);
    }

    virtual ~is_qffp_probe() {}
};

probe * mk_is_qffp_probe() {
    return alloc(is_qffp_probe);
}
    
probe * mk_is_qffpbv_probe() {
    return alloc(is_qffp_probe);
}
