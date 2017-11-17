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
#include "util/common_msgs.h"
#include "util/stopwatch.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_pp_util.h"
#include "tactic/model_converter.h"
#include "solver/solver.h"
#include "model/model_evaluator.h"


unsigned solver::get_num_assertions() const {
    NOT_IMPLEMENTED_YET();
    return 0;
}

expr * solver::get_assertion(unsigned idx) const {
    NOT_IMPLEMENTED_YET();
    return 0;
}

std::ostream& solver::display(std::ostream & out, unsigned n, expr* const* assumptions) const {
    expr_ref_vector fmls(get_manager());
    stopwatch sw;
    sw.start();
    // std::cout << "display 1\n";
    get_assertions(fmls);
    // std::cout << "display 2 " << sw.get_current_seconds() << "\n";
    ast_pp_util visitor(get_manager());
    model_converter_ref mc = get_model_converter();
    // std::cout << "display 3 " << sw.get_current_seconds() << "\n";
    if (mc.get()) { 
        mc->collect(visitor); 
    }
    // std::cout << "display 4 " << sw.get_current_seconds() << "\n";
    visitor.collect(fmls);
    // std::cout << "display 5 " << sw.get_current_seconds() << "\n";
    visitor.collect(n, assumptions);
    visitor.display_decls(out);
    // std::cout << "display 6 " << sw.get_current_seconds() << "\n";
    visitor.display_asserts(out, fmls, true);
    // std::cout << "display 7 " << sw.get_current_seconds() << "\n";
    if (mc.get()) {
        mc->display(out);
    }
    // std::cout << "display 8 " << sw.get_current_seconds() << "\n";
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


void solver::assert_expr(expr* f) {
    expr_ref fml(f, get_manager());
    if (mc0()) {
        (*mc0())(fml);        
    }
    assert_expr_core(fml);    
}

void solver::assert_expr(expr* f, expr* t) {
    // let mc0 be the model converter associated with the solver
    // that converts models to their "real state".
    ast_manager& m = get_manager();
    expr_ref fml(f, m);
    expr_ref a(t, m);

    if (mc0()) {
        (*mc0())(fml);        
        // (*mc0())(a);        
    }
    assert_expr_core(fml, a);    
}

