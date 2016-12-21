/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver.h

Abstract:

    abstract solver interface

Author:

    Leonardo (leonardo) 2011-03-19

Notes:

--*/
#include"solver.h"
#include"model_evaluator.h"
#include"ast_util.h"
#include"ast_pp.h"
#include"ast_pp_util.h"
#include "common_msgs.h"


unsigned solver::get_num_assertions() const {
    NOT_IMPLEMENTED_YET();
    return 0;
}

expr * solver::get_assertion(unsigned idx) const {
    NOT_IMPLEMENTED_YET();
    return 0;
}

std::ostream& solver::display(std::ostream & out) const {
    expr_ref_vector fmls(get_manager());
    get_assertions(fmls);
    ast_pp_util visitor(get_manager());
    visitor.collect(fmls);
    visitor.display_decls(out);
    visitor.display_asserts(out, fmls, true);
    return out;
}

void solver::get_assertions(expr_ref_vector& fmls) const {
    unsigned sz = get_num_assertions();
    for (unsigned i = 0; i < sz; ++i) {
        fmls.push_back(get_assertion(i));
    }
}

struct scoped_assumption_push {
    expr_ref_vector& m_vec;
    scoped_assumption_push(expr_ref_vector& v, expr* e): m_vec(v) { v.push_back(e); }
    ~scoped_assumption_push() { m_vec.pop_back(); }
};

lbool solver::get_consequences(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) {
    try {
        return get_consequences_core(asms, vars, consequences);
    }
    catch (z3_exception& ex) {
        if (asms.get_manager().canceled()) {
            set_reason_unknown(Z3_CANCELED_MSG);
            return l_undef;
        }
        else {
            set_reason_unknown(ex.msg());
        }
        throw;
    }
}

lbool solver::get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) {
    ast_manager& m = asms.get_manager();
    lbool is_sat = check_sat(asms);
    if (is_sat != l_true) {
        return is_sat;
    }
    model_ref model;
    get_model(model);
    expr_ref tmp(m), nlit(m), lit(m), val(m);
    expr_ref_vector asms1(asms);
    model_evaluator eval(*model.get());
    unsigned k = 0;
    for (unsigned i = 0; i < vars.size(); ++i) {
        expr_ref_vector core(m);
        tmp = vars[i];
        val = eval(tmp);
        if (!m.is_value(val)) {
            // vars[i] is unfixed
            continue;
        }
        if (m.is_bool(tmp) && is_uninterp_const(tmp)) {
            if (m.is_true(val)) {
                nlit = m.mk_not(tmp);
                lit = tmp;
            }
            else if (m.is_false(val)) {
                nlit = tmp;
                lit = m.mk_not(tmp);
            }
            else {
                // vars[i] is unfixed
                continue;
            }
            scoped_assumption_push _scoped_push(asms1, nlit);
            is_sat = check_sat(asms1);
            switch (is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                // vars[i] is unfixed
                break;
            case l_false:
                get_unsat_core(core);
                k = 0;
                for (unsigned j = 0; j < core.size(); ++j) {
                    if (core[j].get() != nlit) {
                        core[k] = core[j].get();
                        ++k;
                    }
                }
                core.resize(k);
                consequences.push_back(m.mk_implies(mk_and(core), lit));
                break;
            }
        }
        else {
            lit = m.mk_eq(tmp, val);
            nlit = m.mk_not(lit);
            scoped_push _scoped_push(*this);
            assert_expr(nlit);
            is_sat = check_sat(asms);            
            switch (is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                // vars[i] is unfixed
                break;
            case l_false:
                get_unsat_core(core);
                consequences.push_back(m.mk_implies(mk_and(core), lit));
                break;
            }            
        }
    }
    return l_true;
}

lbool solver::find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
    return l_true;
}

lbool solver::preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) {
    return check_sat(0, 0);
}

bool solver::is_literal(ast_manager& m, expr* e) {
    return is_uninterp_const(e) || (m.is_not(e, e) && is_uninterp_const(e));
}

