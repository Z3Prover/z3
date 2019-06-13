/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver.cpp

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
#include "ast/display_dimacs.h"
#include "tactic/model_converter.h"
#include "solver/solver.h"
#include "solver/solver_params.hpp"
#include "model/model_evaluator.h"


unsigned solver::get_num_assertions() const {
    UNREACHABLE();
    return 0;
}

expr * solver::get_assertion(unsigned idx) const {
    UNREACHABLE();
    return nullptr;
}

std::ostream& solver::display(std::ostream & out, unsigned n, expr* const* assumptions) const {
    expr_ref_vector fmls(get_manager());
    get_assertions(fmls);    
    ast_pp_util visitor(get_manager());
    model_converter_ref mc = get_model_converter();
    if (mc.get()) { 
        mc->set_env(&visitor); 
    }
    visitor.collect(fmls);
    visitor.collect(n, assumptions);
    visitor.display_decls(out);
    visitor.display_asserts(out, fmls, true);
    if (mc.get()) {
        mc->display(out);
        mc->set_env(nullptr);
    }
    return out;
}

std::ostream& solver::display_dimacs(std::ostream& out) const {
    expr_ref_vector fmls(get_manager());
    get_assertions(fmls);    
    return ::display_dimacs(out, fmls);
}

void solver::get_assertions(expr_ref_vector& fmls) const {
    unsigned sz = get_num_assertions();
    for (unsigned i = 0; i < sz; ++i) {
        fmls.push_back(get_assertion(i));
    }
}

expr_ref_vector solver::get_assertions() const {
    expr_ref_vector result(get_manager());
    get_assertions(result);
    return result;
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
    return check_sat(0, nullptr);
}


static bool is_m_atom(ast_manager& m, expr* f) {
    if (!is_app(f)) return true;
    app* _f = to_app(f);
    family_id bfid = m.get_basic_family_id();
    if (_f->get_family_id() != bfid) return true;
    if (_f->get_num_args() > 0 && m.is_bool(_f->get_arg(0))) return false;    
    return m.is_eq(f) || m.is_distinct(f);
}

bool solver::is_literal(ast_manager& m, expr* e) {
    return is_m_atom(m, e) || (m.is_not(e, e) && is_m_atom(m, e));
}

void solver::assert_expr(expr* f) {
    expr_ref fml(f, get_manager());
    if (m_enforce_model_conversion) {
        model_converter_ref mc = get_model_converter();
        if (mc) {
            (*mc)(fml);        
        }
    }
    assert_expr_core(fml);    
}

void solver::assert_expr(expr* f, expr* t) {
    ast_manager& m = get_manager();
    expr_ref fml(f, m);    
    expr_ref a(t, m);
    if (m_enforce_model_conversion) {
        model_converter_ref mc = get_model_converter();
        if (mc) {
            (*mc)(fml);        
            // (*mc)(a);        
        }
    }
    assert_expr_core2(fml, a);    
}



void solver::collect_param_descrs(param_descrs & r) {
    r.insert("solver.enforce_model_conversion", CPK_BOOL, "(default: false) enforce model conversion when asserting formulas");
    insert_timeout(r);
    insert_rlimit(r);
    insert_max_memory(r);
    insert_ctrl_c(r);
}

void solver::reset_params(params_ref const & p) {
    m_params = p;
    solver_params sp(m_params);
    m_enforce_model_conversion = sp.enforce_model_conversion();
    m_cancel_backup_file = sp.cancel_backup_file();
}

void solver::updt_params(params_ref const & p) {
    m_params.copy(p);
    solver_params sp(m_params);
    m_enforce_model_conversion = sp.enforce_model_conversion();
    m_cancel_backup_file = sp.cancel_backup_file();
}


expr_ref_vector solver::get_units() {
    ast_manager& m = get_manager();
    expr_ref_vector fmls(m), result(m), tmp(m);
    get_assertions(fmls);
    obj_map<expr, bool> units;
    for (expr* f : fmls) {
        if (m.is_not(f, f) && is_literal(m, f)) {
            m.inc_ref(f);
            units.insert(f, false);
        }
        else if (is_literal(m, f)) {
            m.inc_ref(f);
            units.insert(f, true);
        }
    }
    model_converter_ref mc = get_model_converter();
    if (mc) {
        mc->get_units(units);
    }
    for (auto const& kv : units) {
        tmp.push_back(kv.m_key);
        if (kv.m_value) 
            result.push_back(kv.m_key); 
        else 
            result.push_back(m.mk_not(kv.m_key));
    }
    for (expr* e : tmp) {
        m.dec_ref(e);
    }

    return result;
}


expr_ref_vector solver::get_non_units() {
    ast_manager& m = get_manager();
    expr_ref_vector result(m), fmls(m);
    get_assertions(fmls);
    family_id bfid = m.get_basic_family_id();
    expr_mark marked;
    unsigned sz0 = fmls.size();
    for (unsigned i = 0; i < fmls.size(); ++i) {
        expr* f = fmls.get(i);
        if (marked.is_marked(f)) continue;
        marked.mark(f);
        if (!is_app(f)) {
            if (i >= sz0) result.push_back(f);
            continue;
        }
        app* _f = to_app(f);
        if (_f->get_family_id() == bfid) {
            // basic objects are true/false/and/or/not/=/distinct 
            // and proof objects (that are not Boolean).
            if (i < sz0 && m.is_not(f) && is_m_atom(m, _f->get_arg(0))) {
                marked.mark(_f->get_arg(0));
            }
            else if (_f->get_num_args() > 0 && m.is_bool(_f->get_arg(0))) {
                fmls.append(_f->get_num_args(), _f->get_args());
            }
            else if (i >= sz0 && is_m_atom(m, f)) {
                result.push_back(f);
            }
        }
        
        else {
            if (i >= sz0) result.push_back(f);
        }
    }
    return result;
}


lbool solver::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    lbool r = l_undef;
    try {
        r = check_sat_core(num_assumptions, assumptions);
    }
    catch (...) {
        if (!get_manager().limit().inc(0)) {
            dump_state(num_assumptions, assumptions);
        }
        throw;
    }
    if (r == l_undef && get_manager().canceled()) {
        dump_state(num_assumptions, assumptions);        
    }
    return r;
}

void solver::dump_state(unsigned sz, expr* const* assumptions) {
    if ((symbol::null != m_cancel_backup_file) &&
        !m_cancel_backup_file.is_numerical() && 
        m_cancel_backup_file.c_ptr() &&
        m_cancel_backup_file.bare_str()[0]) {
        std::string file = m_cancel_backup_file.str();
        std::ofstream ous(file);
        display(ous, sz, assumptions);
    }
}
