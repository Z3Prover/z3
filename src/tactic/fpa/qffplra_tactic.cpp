/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffpalra_tactic.cpp

Abstract:

    Tactic for QF_FPLRA benchmarks.

Author:

    Christoph (cwinter) 2018-04-24

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/fpa/qffp_tactic.h"
#include "tactic/fpa/qffplra_tactic.h"

tactic * mk_qffplra_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = mk_qffp_tactic(m, p);
    st->updt_params(p);
    return st;
}

struct is_fpa_function {
    struct found {};
    ast_manager & m;
    fpa_util      fu;
    
    is_fpa_function(ast_manager & _m) : m(_m), fu(m) {}

    void operator()(var *) { }

    void operator()(quantifier *) { }

    void operator()(app * n) {
        if (n->get_family_id() == fu.get_family_id()) 
            throw found();
    }
};

struct is_non_qffplra_predicate {
    struct found {};
    ast_manager & m;
    bv_util       bu;
    fpa_util      fu;
    arith_util    au;

    is_non_qffplra_predicate(ast_manager & _m) : m(_m), bu(m), fu(m), au(m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        sort * s = n->get_sort();
        if (!m.is_bool(s) && !fu.is_float(s) && !fu.is_rm(s) && !bu.is_bv_sort(s) && !au.is_real(s))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id() ||
            fid == fu.get_family_id() ||
            fid == bu.get_family_id() ||
            fid == au.get_family_id())
            return;
        if (is_uninterp_const(n))
            return;
        if (au.is_real(s))
            return;

        throw found();
    }
};

class is_qffplra_probe : public probe {
public:
    result operator()(goal const & g) override {
        return 
            test<is_fpa_function>(g) && 
            !test<is_non_qffplra_predicate>(g);
    }

    ~is_qffplra_probe() override {}
};

probe * mk_is_qffplra_probe() {
    return alloc(is_qffplra_probe);
}
