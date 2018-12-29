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
#include "tactic/tactical.h"
#include "tactic/fpa/fpa2bv_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/smtlogics/qfnra_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "smt/tactic/smt_tactic.h"
#include "ackermannization/ackermannize_bv_tactic.h"

#include "tactic/fpa/qffp_tactic.h"


struct is_non_fp_qfnra_predicate {
    struct found {};
    ast_manager & m;
    bv_util       bu;
    fpa_util      fu;
    arith_util    au;

    is_non_fp_qfnra_predicate(ast_manager & _m) : m(_m), bu(m), fu(m), au(m) {}

    void operator()(var *) { throw found(); }
    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        family_id fid = n->get_family_id();
        if (fid != null_family_id && fid != fu.get_family_id())
            throw found();

        sort * s = get_sort(n);
        if (fid == fu.get_family_id()) {
            if (!fu.is_float(s) && !fu.is_rm(s) &&
                to_app(n)->get_decl_kind() != OP_FPA_TO_REAL)
                throw found();
        }
        else if (fid == null_family_id) {
            if (!fu.is_float(s) && !fu.is_rm(s) && !m.is_bool(s))
                throw found();
        }
        else if (fid == m.get_basic_family_id())
            return;
        else
            throw found();
    }
};

class is_fp_qfnra_probe : public probe {
public:
    result operator()(goal const & g) override {
        return !test<is_non_fp_qfnra_predicate>(g);
    }
    ~is_fp_qfnra_probe() override {}
};

probe * mk_is_fp_qfnra_probe() {
    return alloc(is_fp_qfnra_probe);
}


tactic * mk_qffp_tactic(ast_manager & m, params_ref const & p) {
    params_ref simp_p = p;
    simp_p.set_bool("arith_lhs", true);
    simp_p.set_bool("elim_and", true);

    tactic * preamble = and_then(mk_simplify_tactic(m, simp_p),
                                 mk_propagate_values_tactic(m, p),
                                 mk_fpa2bv_tactic(m, p),
                                 mk_propagate_values_tactic(m, p),
                                 using_params(mk_simplify_tactic(m, p), simp_p),
                                 if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m, p))));

    tactic * st = and_then(preamble,
                           mk_bit_blaster_tactic(m, p),
                           using_params(mk_simplify_tactic(m, p), simp_p),
                           cond(mk_is_propositional_probe(),
                                cond(mk_produce_proofs_probe(),
                                     mk_smt_tactic(m, p), // `sat' does not support proofs.
                                     mk_psat_tactic(m, p)),
                                cond(mk_is_fp_qfnra_probe(),
                                     mk_qfnra_tactic(m, p),
                                     mk_smt_tactic(m, p))));

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
    result operator()(goal const & g) override {
        return !test<is_non_qffp_predicate>(g);
    }

    ~is_qffp_probe() override {}
};

probe * mk_is_qffp_probe() {
    return alloc(is_qffp_probe);
}

probe * mk_is_qffpbv_probe() {
    return alloc(is_qffp_probe);
}
