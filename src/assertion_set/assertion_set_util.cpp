/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set_util.cpp

Abstract:

    Assertion set goodies

Author:

    Leonardo de Moura (leonardo) 2011-04-28

Revision History:

--*/
#include"assertion_set_util.h"
#include"well_sorted.h"
#include"for_each_expr.h"
#include"bv_decl_plugin.h"
#include"arith_decl_plugin.h"

void as_shared_occs::operator()(assertion_set const & s) {
    m_occs.reset();
    shared_occs_mark visited;
    unsigned sz = s.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * t = s.form(i);
        m_occs(t, visited);
    }
}

bool is_well_sorted(assertion_set const & s) {
    unsigned sz = s.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * t = s.form(i);
        if (!is_well_sorted(s.m(), t))
            return false;
    }
    return true;
}

struct is_non_propositional {
    struct found {};
    ast_manager & m;

    is_non_propositional(ast_manager & _m):m(_m) {}
    void operator()(var *) { throw found();  }
    void operator()(quantifier *) { throw found(); }
    void operator()(app * n) {
        if (!m.is_bool(n))
            throw found();
        
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return; 
        
        if (is_uninterp_const(n))
            return;

        throw found();
    }
};

struct is_non_qfbv {
    struct found {};
    ast_manager & m;
    bv_util       u;

    is_non_qfbv(ast_manager & _m):m(_m), u(m) {}

    void operator()(var *) { throw found();  }
    
    void operator()(quantifier *) { throw found(); }
    
    void operator()(app * n) {
        if (!m.is_bool(n) && !u.is_bv(n))
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

bool is_propositional(assertion_set const & s) {
    return !test<is_non_propositional>(s);
}

bool is_qfbv(assertion_set const & s) {
    return !test<is_non_qfbv>(s);
}

struct is_non_qflira {
    struct found {};
    ast_manager & m;
    arith_util    u;
    bool          m_int;
    bool          m_real;

    is_non_qflira(ast_manager & _m, bool _int, bool _real):m(_m), u(m), m_int(_int), m_real(_real) {}

    void operator()(var *) { throw found();  }
    
    void operator()(quantifier *) { throw found(); }
    
    bool compatible_sort(app * n) const {
        if (m.is_bool(n))
            return true;
        if (m_int && u.is_int(n))
            return true;
        if (m_real && u.is_real(n))
            return true;
        return false;
    }

    void operator()(app * n) {
        if (!compatible_sort(n))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return; 
        if (fid == u.get_family_id()) {
            switch (n->get_decl_kind()) {
            case OP_LE:  case OP_GE: case OP_LT: case OP_GT:
            case OP_ADD: case OP_NUM:
                return;
            case OP_MUL:
                if (n->get_num_args() != 2)
                    throw found();
                if (!u.is_numeral(n->get_arg(0)))
                    throw found();
                return;
            case OP_TO_REAL:
                if (!m_real)
                    throw found();
                break;
            default:
                throw found();
            }
            return;
        }
        if (is_uninterp_const(n))
            return;
        throw found();
    }
};

bool is_qflia(assertion_set const & s) {
    is_non_qflira proc(s.m(), true, false);
    return !test(s, proc);
}

bool is_qflra(assertion_set const & s) {
    is_non_qflira proc(s.m(), false, true);
    return !test(s, proc);
}

bool is_qflira(assertion_set const & s) {
    is_non_qflira proc(s.m(), true, true);
    return !test(s, proc);
}

bool is_lp(assertion_set const & s) {
    ast_manager & m = s.m();
    arith_util u(m);
    unsigned sz = s.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f  = s.form(i);
        bool sign = false;
        while (m.is_not(f, f))
            sign = !sign;
        if (m.is_eq(f) && !sign) {
            if (m.get_sort(to_app(f)->get_arg(0))->get_family_id() != u.get_family_id())
                return false;
            continue;
        }
        if (u.is_le(f) || u.is_ge(f) || u.is_lt(f) || u.is_gt(f))
            continue;
        return false;
    }
    return true;
}

bool is_ilp(assertion_set const & s) {
    if (!is_qflia(s))
        return false;
    if (has_term_ite(s))
        return false;
    return is_lp(s);
}

bool is_mip(assertion_set const & s) {
    if (!is_qflira(s))
        return false;
    if (has_term_ite(s))
        return false;
    return is_lp(s);
}

struct has_term_ite_proc {
    struct found {};
    ast_manager & m;
    has_term_ite_proc(ast_manager & _m):m(_m) {}
    void operator()(var *) {}
    void operator()(quantifier *) {}
    void operator()(app * n) { if (m.is_term_ite(n)) throw found(); }
};

bool has_term_ite(assertion_set const & s) {
    return test<has_term_ite_proc>(s);
}

