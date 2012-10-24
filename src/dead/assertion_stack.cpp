/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    assertion_stack.cpp

Abstract:
    
    Assertion stacks
    
Author:

    Leonardo de Moura (leonardo) 2012-02-17

Revision History:

--*/
#include"assertion_stack.h"
#include"well_sorted.h"
#include"ast_smt2_pp.h"
#include"ref_util.h"

assertion_stack::assertion_stack(ast_manager & m, bool models_enabled, bool core_enabled):
    m_manager(m),
    m_forbidden(m),
    m_csubst(m, core_enabled),
    m_fsubst(m, core_enabled) {
    init(m.proofs_enabled(), models_enabled, core_enabled);
}

assertion_stack::assertion_stack(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
    m_manager(m),
    m_forbidden(m),
    m_csubst(m, core_enabled, proofs_enabled),
    m_fsubst(m, core_enabled, proofs_enabled) {
    init(proofs_enabled, models_enabled, core_enabled);
}

void assertion_stack::init(bool proofs_enabled, bool models_enabled, bool core_enabled) {
    m_ref_count      = 0;
    m_models_enabled = models_enabled;
    m_proofs_enabled = proofs_enabled;
    m_core_enabled   = core_enabled;
    m_inconsistent   = false;
    m_form_qhead     = 0;
}

assertion_stack::~assertion_stack() {
    reset();
}

void assertion_stack::reset() {
    m_inconsistent = false;
    m_form_qhead   = 0;
    m_mc_qhead     = 0;
    dec_ref_collection_values(m_manager, m_forms);
    dec_ref_collection_values(m_manager, m_proofs);
    dec_ref_collection_values(m_manager, m_deps);
    m_forbidden_set.reset();
    m_forbidden.reset();
    m_csubst.reset();
    m_fsubst.reset();
    m_mc.reset();
    m_scopes.reset();
}

void assertion_stack::expand(expr * f, proof * pr, expr_dependency * dep, expr_ref & new_f, proof_ref & new_pr, expr_dependency_ref & new_dep) {
    // TODO: expand definitions
    new_f   = f;
    new_pr  = pr;
    new_dep = dep;
}

void assertion_stack::push_back(expr * f, proof * pr, expr_dependency * d) {
    if (m().is_true(f))
        return;
    if (m().is_false(f)) {
        m_inconsistent = true;
    }
    else {
        SASSERT(!m_inconsistent);
    }
    m().inc_ref(f);
    m_forms.push_back(f);
    if (proofs_enabled()) {
        m().inc_ref(pr);
        m_proofs.push_back(pr);
    }
    if (unsat_core_enabled()) {
        m().inc_ref(d);
        m_deps.push_back(d);
    }
}

void assertion_stack::quick_process(bool save_first, expr * & f, expr_dependency * d) {
    if (!m().is_and(f) && !(m().is_not(f) && m().is_or(to_app(f)->get_arg(0)))) {
        if (!save_first) {
            push_back(f, 0, d);
        }
        return; 
    }
    typedef std::pair<expr *, bool> expr_pol;
    sbuffer<expr_pol, 64> todo;
    todo.push_back(expr_pol(f, true));
    while (!todo.empty()) {
        if (m_inconsistent)
            return;
        expr_pol p  = todo.back();
        expr * curr = p.first;
        bool   pol  = p.second;
        todo.pop_back();
        if (pol && m().is_and(curr)) {
            app * t = to_app(curr);
            unsigned i = t->get_num_args();
            while (i > 0) {
                --i;
                todo.push_back(expr_pol(t->get_arg(i), true));
            }
        }
        else if (!pol && m().is_or(curr)) {
            app * t = to_app(curr);
            unsigned i = t->get_num_args();
            while (i > 0) {
                --i;
                todo.push_back(expr_pol(t->get_arg(i), false));
            }
        }
        else if (m().is_not(curr)) {
            todo.push_back(expr_pol(to_app(curr)->get_arg(0), !pol));
        }
        else {
            if (!pol) 
                curr = m().mk_not(curr);
            if (save_first) {
                f  = curr;
                save_first = false;
            }
            else {
                push_back(curr, 0, d);
            }
        }
    }
}

void assertion_stack::process_and(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
    unsigned num = f->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        if (m_inconsistent)
            return;
        slow_process(save_first && i == 0, f->get_arg(i), m().mk_and_elim(pr, i), d, out_f, out_pr);
    }
}

void assertion_stack::process_not_or(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
    unsigned num = f->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        if (m_inconsistent)
            return;
        expr * child = f->get_arg(i);
        if (m().is_not(child)) {
            expr * not_child = to_app(child)->get_arg(0);
            slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), d, out_f, out_pr);
        }
        else {
            expr_ref not_child(m());
            not_child = m().mk_not(child);
            slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), d, out_f, out_pr);
        }
    }
}

void assertion_stack::slow_process(bool save_first, expr * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
    if (m().is_and(f)) 
        process_and(save_first, to_app(f), pr, d, out_f, out_pr);
    else if (m().is_not(f) && m().is_or(to_app(f)->get_arg(0))) 
        process_not_or(save_first, to_app(to_app(f)->get_arg(0)), pr, d, out_f, out_pr);
    else if (save_first) {
        out_f  = f;
        out_pr = pr;
    }
    else {
        push_back(f, pr, d);
    }
}

void assertion_stack::slow_process(expr * f, proof * pr, expr_dependency * d) {
    expr_ref out_f(m());
    proof_ref out_pr(m());
    slow_process(false, f, pr, d, out_f, out_pr);
}


void assertion_stack::assert_expr(expr * f, proof * pr, expr_dependency * d) {
    SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
    if (m_inconsistent)
        return;
    expr_ref new_f(m()); proof_ref new_pr(m()); expr_dependency_ref new_d(m());
    expand(f, pr, d, new_f, new_pr, new_d);
    if (proofs_enabled())
        slow_process(f, pr, d);
    else
        quick_process(false, f, d);
}

#ifdef Z3DEBUG
// bool assertion_stack::is_expanded(expr * f) {
// }
#endif

void assertion_stack::update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    SASSERT(i >= m_form_qhead);
    SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
    if (m_inconsistent)
        return;
    if (proofs_enabled()) {
        expr_ref out_f(m());
        proof_ref out_pr(m());
        slow_process(true, f, pr, d, out_f, out_pr);
        if (!m_inconsistent) {
            if (m().is_false(out_f)) {
                push_back(out_f, out_pr, d);
            }
            else {
                m().inc_ref(out_f);
                m().dec_ref(m_forms[i]);
                m_forms[i] = out_f;

                m().inc_ref(out_pr);
                m().dec_ref(m_proofs[i]);
                m_proofs[i] = out_pr;

                if (unsat_core_enabled()) {
                    m().inc_ref(d);
                    m().dec_ref(m_deps[i]);
                    m_deps[i] = d;
                }
            }
        }
    }
    else {
        quick_process(true, f, d);
        if (!m_inconsistent) {
            if (m().is_false(f)) {
                push_back(f, 0, d);
            }
            else {
                m().inc_ref(f);
                m().dec_ref(m_forms[i]);
                m_forms[i] = f;

                if (unsat_core_enabled()) {
                    m().inc_ref(d);
                    m().dec_ref(m_deps[i]);
                    m_deps[i] = d;
                }
            }
        }
    }
}

void assertion_stack::expand_and_update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    SASSERT(i >= m_form_qhead);
    SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
    if (m_inconsistent)
        return;
    expr_ref new_f(m()); proof_ref new_pr(m()); expr_dependency_ref new_d(m());
    expand(f, pr, d, new_f, new_pr, new_d);
    update(i, new_f, new_pr, new_d);
}

void assertion_stack::push() {
}

void assertion_stack::pop(unsigned num_scopes) {
}

void assertion_stack::commit() {
}

void assertion_stack::add_filter(func_decl * f) const {
}

void assertion_stack::add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
    
}

void assertion_stack::add_definition(func_decl * f, quantifier * q, proof * pr, expr_dependency * dep) {
}

void assertion_stack::convert(model_ref & m) {
}

void assertion_stack::display(std::ostream & out) const {
    out << "(assertion-stack";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  ";
        if (i == m_form_qhead) 
            out << "==>\n";
        out << mk_ismt2_pp(form(i), m(), 2);
    }
    out << ")" << std::endl;
}

bool assertion_stack::is_well_sorted() const {
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        expr * t = form(i);
        if (!::is_well_sorted(m(), t))
            return false;
    }
    return true;
}
