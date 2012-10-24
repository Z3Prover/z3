/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set.cpp

Abstract:

    Assertion set.

Author:

    Leonardo de Moura (leonardo) 2011-04-20

Revision History:

--*/
#include"assertion_set.h"
#include"cmd_context.h"
#include"ast_ll_pp.h"
#include"ast_smt2_pp.h"
#include"for_each_expr.h"

void assertion_set::copy(assertion_set & target) const {
    if (this == &target)
        return;
    m().copy(m_forms, target.m_forms);
    m().copy(m_proofs, target.m_proofs);
    target.m_inconsistent = m_inconsistent;
}

void assertion_set::push_back(expr * f, proof * pr) {
    if (m().is_true(f))
        return;
    if (m().is_false(f)) {
        m().del(m_forms);
        m().del(m_proofs);
        m_inconsistent = true;
    }
    else {
        SASSERT(!m_inconsistent);
    }
    m().push_back(m_forms, f);
    if (m().proofs_enabled())
        m().push_back(m_proofs, pr);
}

void assertion_set::quick_process(bool save_first, expr * & f) {
    if (!m().is_and(f) && !(m().is_not(f) && m().is_or(to_app(f)->get_arg(0)))) {
        if (!save_first) {
            push_back(f, 0);
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
                push_back(curr, 0);
            }
        }
    }
}

void assertion_set::process_and(bool save_first, app * f, proof * pr, expr_ref & out_f, proof_ref & out_pr) {
    unsigned num = f->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        if (m_inconsistent)
            return;
        slow_process(save_first && i == 0, f->get_arg(i), m().mk_and_elim(pr, i), out_f, out_pr);
    }
}

void assertion_set::process_not_or(bool save_first, app * f, proof * pr, expr_ref & out_f, proof_ref & out_pr) {
    unsigned num = f->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        if (m_inconsistent)
            return;
        expr * child = f->get_arg(i);
        if (m().is_not(child)) {
            expr * not_child = to_app(child)->get_arg(0);
            slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), out_f, out_pr);
        }
        else {
            expr_ref not_child(m());
            not_child = m().mk_not(child);
            slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), out_f, out_pr);
        }
    }
}

void assertion_set::slow_process(bool save_first, expr * f, proof * pr, expr_ref & out_f, proof_ref & out_pr) {
    if (m().is_and(f)) 
        process_and(save_first, to_app(f), pr, out_f, out_pr);
    else if (m().is_not(f) && m().is_or(to_app(f)->get_arg(0))) 
        process_not_or(save_first, to_app(to_app(f)->get_arg(0)), pr, out_f, out_pr);
    else if (save_first) {
        out_f  = f;
        out_pr = pr;
    }
    else {
        push_back(f, pr);
    }
}

void assertion_set::slow_process(expr * f, proof * pr) {
    expr_ref out_f(m());
    proof_ref out_pr(m());
    slow_process(false, f, pr, out_f, out_pr);
}

void assertion_set::assert_expr(expr * f, proof * pr) {
    SASSERT(m().proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
    if (m_inconsistent)
        return;
    if (m().proofs_enabled())
        slow_process(f, pr);
    else
        quick_process(false, f);
}

void assertion_set::update(unsigned i, expr * f, proof * pr) {
    SASSERT(m().proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
    if (m_inconsistent)
        return;
    if (m().proofs_enabled()) {
        expr_ref out_f(m());
        proof_ref out_pr(m());
        slow_process(true, f, pr, out_f, out_pr);
        if (!m_inconsistent) {
            if (m().is_false(out_f)) {
                push_back(out_f, out_pr);
            }
            else {
                m().set(m_forms, i, out_f);
                m().set(m_proofs, i, out_pr);
            }
        }
    }
    else {
        quick_process(true, f);
        if (!m_inconsistent) {
            if (m().is_false(f))
                push_back(f, 0);
            else
                m().set(m_forms, i, f);
        }
    }
}

void assertion_set::reset() {
    m().del(m_forms);
    m().del(m_proofs);
    m_inconsistent = false;
}

void assertion_set::display(cmd_context & ctx, std::ostream & out) const {
    out << "(assertion-set";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  ";
        ctx.display(out, form(i), 2);
    }
    out << ")" << std::endl;
}

void assertion_set::display(cmd_context & ctx) const {
    display(ctx, ctx.regular_stream());
}

void assertion_set::display(std::ostream & out) const {
    out << "(assertion-set";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  ";
        out << mk_ismt2_pp(form(i), m(), 2);
    }
    out << ")" << std::endl;
}

void assertion_set::display_as_and(std::ostream & out) const {
    ptr_buffer<expr> args;
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++)
        args.push_back(form(i));
    expr_ref tmp(m());
    tmp = m().mk_and(args.size(), args.c_ptr());
    out << mk_ismt2_pp(tmp, m()) << "\n";
}

void assertion_set::display_ll(std::ostream & out) const {
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << mk_ll_pp(form(i), m()) << "\n";
    }
}

/**
   \brief Assumes that the formula is already in CNF.
*/
void assertion_set::display_dimacs(std::ostream & out) const {
    obj_map<expr, unsigned> expr2var;
    unsigned num_vars = 0;
    unsigned num_cls  = size();
    for (unsigned i = 0; i < num_cls; i++) {
        expr * f = form(i);
        unsigned num_lits;
        expr * const * lits;
        if (m().is_or(f)) {
            num_lits = to_app(f)->get_num_args();
            lits     = to_app(f)->get_args();
        }
        else {
            num_lits = 1;
            lits     = &f;
        }
        for (unsigned j = 0; j < num_lits; j++) {
            expr * l = lits[j];
            if (m().is_not(l))
                l = to_app(l)->get_arg(0);
            if (expr2var.contains(l))
                continue;
            num_vars++;
            expr2var.insert(l, num_vars);
        }
    }
    out << "p cnf " << num_vars << " " << num_cls << "\n";
    for (unsigned i = 0; i < num_cls; i++) {
        expr * f = form(i);
        unsigned num_lits;
        expr * const * lits;
        if (m().is_or(f)) {
            num_lits = to_app(f)->get_num_args();
            lits     = to_app(f)->get_args();
        }
        else {
            num_lits = 1;
            lits     = &f;
        }
        for (unsigned j = 0; j < num_lits; j++) {
            expr * l = lits[j];
            if (m().is_not(l)) {
                out << "-";
                l = to_app(l)->get_arg(0);
            }
            unsigned id = UINT_MAX;
            expr2var.find(l, id);
            SASSERT(id != UINT_MAX);
            out << id << " ";
        }
        out << "0\n";
    }
}

unsigned assertion_set::num_exprs() const {
    expr_fast_mark1 visited;
    unsigned sz = size();
    unsigned r  = 0;
    for (unsigned i = 0; i < sz; i++) {
        r += get_num_exprs(form(i), visited);
    }
    return r;
}

/**
   \brief Eliminate true formulas.
*/
void assertion_set::elim_true() {
    unsigned sz = size();
    unsigned j = 0;
    for (unsigned i = 0; i < sz; i++) {
        expr * f = form(i);
        if (m().is_true(f))
            continue;
        if (i == j) {
            j++;
            continue;
        }
        m().set(m_forms, j, f);
        if (m().proofs_enabled())
            m().set(m_proofs, j, m().get(m_proofs, i));
        j++;
    }
    for (; j < sz; j++) {
        m().pop_back(m_forms);
        if (m().proofs_enabled())
            m().pop_back(m_proofs);
    }
}

void assertion_set::elim_redundancies() {
    if (inconsistent())
        return;
    expr_ref_fast_mark1 neg_lits(m());
    expr_ref_fast_mark2 pos_lits(m());
    unsigned sz = size();
    unsigned j  = 0;
    for (unsigned i = 0; i < sz; i++) {
        expr * f = form(i);
        if (m().is_true(f))
            continue;
        if (m().is_not(f)) {
            expr * atom = to_app(f)->get_arg(0);
            if (neg_lits.is_marked(atom))
                continue;
            if (pos_lits.is_marked(atom)) {
                proof * p = 0;
                if (m().proofs_enabled()) {
                    proof * pr1 = 0;
                    proof * pr2 = pr(i);
                    for (unsigned j = 0; j < i; j++) {
                        if (form(j) == atom) {
                            pr1 = pr(j);
                            break;
                        }
                    }
                    SASSERT(pr1);
                    proof * prs[2] = { pr1, pr2 };
                    p = m().mk_unit_resolution(2, prs);
                }
                push_back(m().mk_false(), p);                    
                return;
            }
            neg_lits.mark(atom);
        }
        else {
            if (pos_lits.is_marked(f))
                continue;
            if (neg_lits.is_marked(f)) {
                proof * p = 0;
                if (m().proofs_enabled()) {
                    proof * pr1 = 0;
                    proof * pr2 = pr(i);
                    for (unsigned j = 0; j < i; j++) {
                        expr * curr = form(j);
                        expr * atom;
                        if (m().is_not(curr, atom) && atom == f) {
                            pr1 = pr(j);
                            break;
                        }
                    }
                    SASSERT(pr1);
                    proof * prs[2] = { pr1, pr2 };
                    p = m().mk_unit_resolution(2, prs);
                }
                push_back(m().mk_false(), p);
                return;
            }
            pos_lits.mark(f);
        }
        if (i == j) {
            j++;
            continue;
        }
        m().set(m_forms, j, f);
        if (m().proofs_enabled())
            m().set(m_proofs, j, pr(i));
        j++;
    }
    
    for (; j < sz; j++) {
        m().pop_back(m_forms);
        if (m().proofs_enabled())
            m().pop_back(m_proofs);
    }
}

/**
   \brief Assert expressions from ctx into t.
*/
void assert_exprs_from(cmd_context const & ctx, assertion_set & t) {
    ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
    ptr_vector<expr>::const_iterator end = ctx.end_assertions();
    for (; it != end; ++it) {
        t.assert_expr(*it);
    }
}

/**
   \brief Translate the assertion set to a new one that uses a different ast_manager.
*/
assertion_set * assertion_set::translate(ast_translation & translator) const {
    ast_manager & m_to = translator.to();
    assertion_set * res = alloc(assertion_set, m_to);
    
    unsigned sz = m().size(m_forms);
    for (unsigned i = 0; i < sz; i++) {
        res->m().push_back(res->m_forms, translator(m().get(m_forms, i)));        
        if (m_to.proofs_enabled())
            res->m().push_back(res->m_proofs, translator(m().get(m_proofs, i)));
    }

    res->m_inconsistent = m_inconsistent;

    return res;
}
