/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal.cpp

Abstract:

    Proof / Model finding Goals

Author:

    Leonardo de Moura (leonardo) 2011-10-12

Revision History:

--*/
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/well_sorted.h"
#include "ast/display_dimacs.h"
#include "tactic/goal.h"

goal::precision goal::mk_union(precision p1, precision p2) {
    if (p1 == PRECISE) return p2;
    if (p2 == PRECISE) return p1;
    if (p1 != p2) return UNDER_OVER;
    return p1;
}

std::ostream & operator<<(std::ostream & out, goal::precision p) {
    switch (p) {
    case goal::PRECISE: out << "precise"; break;
    case goal::UNDER:   out << "under"; break;
    case goal::OVER:    out << "over"; break;
    case goal::UNDER_OVER: out << "under-over"; break;
    }
    return out;
}

goal::goal(ast_manager & m, bool models_enabled, bool core_enabled):
    m_manager(m),
    m_ref_count(0),
    m_depth(0),
    m_models_enabled(models_enabled),
    m_proofs_enabled(m.proofs_enabled()),
    m_core_enabled(core_enabled),
    m_inconsistent(false),
    m_precision(PRECISE) {
    }

goal::goal(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
    m_manager(m),
    m_ref_count(0),
    m_depth(0),
    m_models_enabled(models_enabled),
    m_proofs_enabled(proofs_enabled),
    m_core_enabled(core_enabled),
    m_inconsistent(false),
    m_precision(PRECISE) {
    SASSERT(!proofs_enabled || m.proofs_enabled());
    }

goal::goal(goal const & src):
    m_manager(src.m()),
    m_ref_count(0),
    m_depth(0),
    m_models_enabled(src.models_enabled()),
    m_proofs_enabled(src.proofs_enabled()),
    m_core_enabled(src.unsat_core_enabled()),
    m_inconsistent(false),
    m_precision(PRECISE) {
    copy_from(src);
    }

// Copy configuration: depth, models/proofs/cores flags, and precision from src.
// The assertions are not copied
goal::goal(goal const & src, bool):
    m_manager(src.m()),
    m_ref_count(0),
    m_depth(src.m_depth),
    m_models_enabled(src.models_enabled()),
    m_proofs_enabled(src.proofs_enabled()),
    m_core_enabled(src.unsat_core_enabled()),
    m_inconsistent(false),
    m_precision(src.m_precision) {
    m_mc = src.m_mc.get();
    m_pc = src.m_pc.get();
    m_dc = src.m_dc.get();
}

goal::~goal() {
    reset_core();
}

void goal::copy_to(goal & target) const {
    SASSERT(&m_manager == &(target.m_manager));
    if (this == &target)
        return;

    m().copy(m_forms, target.m_forms);
    m().copy(m_proofs, target.m_proofs);
    m().copy(m_dependencies, target.m_dependencies);

    target.m_depth                = std::max(m_depth, target.m_depth);
    SASSERT(target.m_proofs_enabled == m_proofs_enabled);
    SASSERT(target.m_core_enabled   == m_core_enabled);
    target.m_inconsistent         = m_inconsistent;
    target.m_precision            = mk_union(prec(), target.prec());
    target.m_mc                   = m_mc.get(); 
    target.m_pc                   = m_pc.get(); 
    target.m_dc                   = m_dc.get();
}

void goal::push_back(expr * f, proof * pr, expr_dependency * d) {
    SASSERT(!proofs_enabled() || pr);
    if (m().is_true(f))
        return;
    if (m().is_false(f)) {
        // Make sure pr and d are not deleted by the m().del(...) statements.
        proof_ref saved_pr(m());
        expr_dependency_ref saved_d(m());
        saved_pr = pr;
        saved_d  = d;
        m().del(m_forms);
        m().del(m_proofs);
        m().del(m_dependencies);
        m_inconsistent = true;
        m().push_back(m_forms, m().mk_false());
        m().push_back(m_proofs, saved_pr);
        if (unsat_core_enabled())
            m().push_back(m_dependencies, saved_d);
    }
    else {
        SASSERT(!pr || m().get_fact(pr) == f);
        SASSERT(!m_inconsistent);
        m().push_back(m_forms, f);
        m().push_back(m_proofs, pr);
        if (unsat_core_enabled())
            m().push_back(m_dependencies, d);
    }
}

void goal::quick_process(bool save_first, expr_ref& f, expr_dependency * d) {
    expr* g = nullptr;
    if (!m().is_and(f) && !(m().is_not(f, g) && m().is_or(g))) {
        if (!save_first) {
            push_back(f, nullptr, d);
        }
        return;
    }
    typedef std::pair<expr *, bool> expr_pol;
    sbuffer<expr_pol, 64> todo;
    expr_ref_vector tmp_exprs(m());
    todo.push_back(expr_pol(f, true));
    while (!todo.empty()) {
        if (m_inconsistent)
            return;
        expr_pol p = todo.back();
        expr * curr = p.first;
        bool   pol = p.second;
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
        else if (m().is_not(curr, g)) {
            todo.push_back(expr_pol(g, !pol));
        }
        else {
            if (!pol) {
                curr = m().mk_not(curr);                
                tmp_exprs.push_back(curr);
            }
            if (save_first) {
                f = curr;
                save_first = false;
            }
            else {
                push_back(curr, nullptr, d);
            }
        }
    }
}

void goal::process_and(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
    unsigned num = f->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        if (m_inconsistent)
            return;
        slow_process(save_first && i == 0, f->get_arg(i), m().mk_and_elim(pr, i), d, out_f, out_pr);
    }
}

void goal::process_not_or(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
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

void goal::slow_process(bool save_first, expr * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
    expr* g = nullptr;
    proof_ref _pr(pr, m());
    if (m().is_and(f))
        process_and(save_first, to_app(f), pr, d, out_f, out_pr);
    else if (m().is_not(f, g) && m().is_or(g))
        process_not_or(save_first, to_app(g), pr, d, out_f, out_pr);
    else if (save_first) {
        out_f  = f;
        out_pr = pr;
    }
    else {
        push_back(f, pr, d);
    }
}

void goal::slow_process(expr * f, proof * pr, expr_dependency * d) {
    expr_ref out_f(m());
    proof_ref out_pr(m());
    slow_process(false, f, pr, d, out_f, out_pr);
}

void goal::assert_expr(expr * f, proof * pr, expr_dependency * d) {
    expr_ref _f(f, m());
    proof_ref _pr(pr, m());
    expr_dependency_ref _d(d, m());
    if (m_inconsistent) {
        return;
    }
    SASSERT(!proofs_enabled() || pr);
    if (pr) {
        CTRACE("goal", f != m().get_fact(pr), tout << mk_pp(f, m()) << "\n" << mk_pp(pr, m()) << "\n";);
        SASSERT(f == m().get_fact(pr));
        slow_process(f, pr, d);
    }
    else {
        expr_ref fr(f, m());
        quick_process(false, fr, d);
    }
}

void goal::assert_expr(expr * f, expr_dependency * d) {
    assert_expr(f, proofs_enabled() ? m().mk_asserted(f) : nullptr, d);
}

void goal::get_formulas(ptr_vector<expr> & result) const {
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        result.push_back(form(i));
    }
}

void goal::get_formulas(expr_ref_vector & result) const {
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        result.push_back(form(i));
    }
}

void goal::update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    if (m_inconsistent)
        return;
    if (proofs_enabled()) {
        SASSERT(pr);
        if (!pr)
            return;
        SASSERT(f == m().get_fact(pr));
        expr_ref out_f(m());
        proof_ref out_pr(m());
        slow_process(true, f, pr, d, out_f, out_pr);
        if (!m_inconsistent) {
            if (m().is_false(out_f)) {
                push_back(out_f, out_pr, d);
            }
            else {
                m().set(m_forms, i, out_f);
                m().set(m_proofs, i, out_pr);
                if (unsat_core_enabled())
                    m().set(m_dependencies, i, d);
            }
        }
    }
    else {
        expr_ref fr(f, m());
        quick_process(true, fr, d);
        if (!m_inconsistent) {
            if (m().is_false(fr)) {
                push_back(f, nullptr, d);
            }
            else {
                m().set(m_forms, i, fr);
                if (unsat_core_enabled())
                    m().set(m_dependencies, i, d);
            }
        }
    }
}

void goal::reset_core() {
    m().del(m_forms);
    m().del(m_proofs);
    m().del(m_dependencies);
}

void goal::reset_all() {
    reset_core();
    m_depth = 0;
    m_inconsistent = false;
    m_precision = PRECISE;
}

void goal::reset() {
    reset_core();
    m_inconsistent = false;
}

void goal::display(ast_printer & prn, std::ostream & out) const {
    out << "(goal";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  ";
        prn.display(out, form(i), 2);
    }
    out << "\n  :precision " << prec() << " :depth " << depth() << ")" << std::endl;
}

void goal::display_with_dependencies(ast_printer & prn, std::ostream & out) const {
    ptr_vector<expr> deps;
    obj_hashtable<expr> to_pp;
    out << "(goal";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  |-";
        deps.reset();
        m().linearize(dep(i), deps);
        for (expr * d : deps) {
            if (is_uninterp_const(d)) {
                out << " " << mk_ismt2_pp(d, m());
            }
            else {
                out << " #" << d->get_id();
                to_pp.insert(d);
            }
        }
        out << "\n  ";
        prn.display(out, form(i), 2);
    }
    if (!to_pp.empty()) {
        out << "\n  :dependencies-definitions (";
        for (expr* d : to_pp) {
            out << "\n  (#" << d->get_id() << "\n  ";
            prn.display(out, d, 2);
            out << ")";
        }
        out << ")";
    }
    out << "\n  :precision " << prec() << " :depth " << depth() << ")" << std::endl;
}

void goal::display_with_dependencies(std::ostream & out) const {
    ptr_vector<expr> deps;
    out << "(goal";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  |-";
        deps.reset();
        m().linearize(dep(i), deps);
        for (expr * d : deps) {
            if (is_uninterp_const(d)) {
                out << " " << mk_ismt2_pp(d, m());
            }
            else {
                out << " #" << d->get_id();
            }
        }
        out << "\n  " << mk_ismt2_pp(form(i), m(), 2);
    }
    out << "\n  :precision " << prec() << " :depth " << depth() << ")" << std::endl;
}


void goal::display_with_proofs(std::ostream& out) const {
    out << "(goal";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  |-";
        if (pr(i)) {
            out << mk_ismt2_pp(pr(i), m(), 4);
        }
        out << "\n  " << mk_ismt2_pp(form(i), m(), 2);
    }
    out << "\n  :precision " << prec() << " :depth " << depth() << ")" << std::endl;
}

void goal::display(ast_printer_context & ctx) const {
    display(ctx, ctx.regular_stream());
}

void goal::display_with_dependencies(ast_printer_context & ctx) const {
    display_with_dependencies(ctx, ctx.regular_stream());
}

void goal::display(std::ostream & out) const {
    out << "(goal";
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << "\n  ";
        out << mk_ismt2_pp(form(i), m(), 2);
    }
    out << ")" << std::endl;
}

void goal::display_as_and(std::ostream & out) const {
    ptr_buffer<expr> args;
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++)
        args.push_back(form(i));
    expr_ref tmp(m());
    tmp = m().mk_and(args.size(), args.data());
    out << mk_ismt2_pp(tmp, m()) << "\n";
}

void goal::display_ll(std::ostream & out) const {
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        out << mk_ll_pp(form(i), m()) << "\n";
    }
}

/**
   \brief Assumes that the formula is already in CNF.
*/
void goal::display_dimacs(std::ostream & out, bool include_names) const {
    expr_ref_vector fmls(m());
    get_formulas(fmls);
    ::display_dimacs(out, fmls, include_names);
}

unsigned goal::num_exprs() const {
    expr_fast_mark1 visited;
    unsigned sz = size();
    unsigned r  = 0;
    for (unsigned i = 0; i < sz; i++) {
        r += get_num_exprs(form(i), visited);
    }
    return r;
}

void goal::shrink(unsigned j) {
    SASSERT(j <= size());
    unsigned sz = size();
    for (unsigned i = j; i < sz; i++)
        m().pop_back(m_forms);
    for (unsigned i = j; i < sz; i++)
        m().pop_back(m_proofs);
    if (unsat_core_enabled()) 
        for (unsigned i = j; i < sz; i++)
            m().pop_back(m_dependencies);
}

/**
   \brief Eliminate true formulas.
*/
void goal::elim_true() {
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
        m().set(m_proofs, j, m().get(m_proofs, i));
        if (unsat_core_enabled())
            m().set(m_dependencies, j, m().get(m_dependencies, i));
        j++;
    }
    shrink(j);
}

/**
   \brief Return the position of formula f in the goal.
   Return UINT_MAX if f is not in the goal
*/
unsigned goal::get_idx(expr * f) const {
    unsigned sz = size();
    for (unsigned j = 0; j < sz; j++) {
        if (form(j) == f)
            return j;
    }
    return UINT_MAX;
}

/**
   \brief Return the position of formula (not f) in the goal.
   Return UINT_MAX if (not f) is not in the goal
*/
unsigned goal::get_not_idx(expr * f) const {
    expr * atom;
    unsigned sz = size();
    for (unsigned j = 0; j < sz; j++) {
        if (m().is_not(form(j), atom) && atom == f)
            return j;
    }
    return UINT_MAX;
}

void goal::elim_redundancies() {
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
                proof * p = nullptr;
                if (proofs_enabled()) {
                    proof * prs[2] = { pr(get_idx(atom)), pr(i) };
                    p = m().mk_unit_resolution(2, prs);
                }
                expr_dependency_ref d(m());
                if (unsat_core_enabled())
                    d = m().mk_join(dep(get_idx(atom)), dep(i));
                push_back(m().mk_false(), p, d);
                return;
            }
            neg_lits.mark(atom);
        }
        else {
            if (pos_lits.is_marked(f))
                continue;
            if (neg_lits.is_marked(f)) {
                proof * p = nullptr;
                if (proofs_enabled()) {
                    proof * prs[2] = { pr(get_not_idx(f)), pr(i) };
                    p = m().mk_unit_resolution(2, prs);
                }
                expr_dependency_ref d(m());
                if (unsat_core_enabled())
                    d = m().mk_join(dep(get_not_idx(f)), dep(i));
                push_back(m().mk_false(), p, d);
                return;
            }
            pos_lits.mark(f);
        }
        if (i == j) {
            j++;
            continue;
        }
        m().set(m_forms, j, f);
        m().set(m_proofs, j, pr(i));
        if (unsat_core_enabled())
            m().set(m_dependencies, j, dep(i));
        j++;
    }
    shrink(j);
}

bool goal::is_well_formed() const {
    unsigned sz = size();
    for (unsigned i = 0; i < sz; i++) {
        expr * t = form(i);
        if (!::is_well_sorted(m(), t))
            return false;
#if 0
        if (pr(i) && m().get_fact(pr(i)) != form(i)) {
            TRACE("tactic", tout << mk_ismt2_pp(pr(i), m()) << "\n" << mk_ismt2_pp(form(i), m()) << "\n";);
            SASSERT(m().get_fact(pr(i)) == form(i));
            return false;
        }
#endif
    }
    return true;
}

/**
   \brief Translate the assertion set to a new one that uses a different ast_manager.
*/
goal * goal::translate(ast_translation & translator) const {
    expr_dependency_translation dep_translator(translator);

    ast_manager & m_to = translator.to();
    goal * res = alloc(goal, m_to, m_to.proofs_enabled() && proofs_enabled(), models_enabled(), unsat_core_enabled());

    unsigned sz = m().size(m_forms);
    for (unsigned i = 0; i < sz; i++) {
        res->m().push_back(res->m_forms, translator(m().get(m_forms, i)));
        res->m().push_back(res->m_proofs, translator(m().get(m_proofs, i)));
        if (res->unsat_core_enabled())
            res->m().push_back(res->m_dependencies, dep_translator(m().get(m_dependencies, i)));
    }

    res->m_inconsistent = m_inconsistent;
    res->m_depth        = m_depth;
    res->m_precision    = m_precision;
    res->m_pc           = m_pc ? m_pc->translate(translator) : nullptr;
    res->m_mc           = m_mc ? m_mc->translate(translator) : nullptr;
    res->m_dc           = m_dc ? m_dc->translate(translator) : nullptr;

    return res;
}

bool goal::sat_preserved() const {
    return prec() == PRECISE || prec() == UNDER;
}

bool goal::unsat_preserved() const {
    return prec() == PRECISE || prec() == OVER;
}

bool goal::is_decided_sat() const {
    return size() == 0 && sat_preserved();
}

bool goal::is_decided_unsat() const {
    return inconsistent() && unsat_preserved();
}

bool goal::is_decided() const {
    return is_decided_sat() || is_decided_unsat();
}

bool is_equal(goal const & s1, goal const & s2) {
    if (s1.size() != s2.size())
        return false;
    unsigned num1 = 0; // num unique ASTs in s1
    unsigned num2 = 0; // num unique ASTs in s2
    expr_fast_mark1 visited1;
    expr_fast_mark2 visited2;
    unsigned sz = s1.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f1 = s1.form(i);
        if (visited1.is_marked(f1))
            continue;
        num1++;
        visited1.mark(f1);
    }
    SASSERT(num1 <= sz);
    SASSERT(0 <= num1);
    for (unsigned i = 0; i < sz; i++) {
        expr * f2 = s2.form(i);
        if (visited2.is_marked(f2))
            continue;
        num2++;
        visited2.mark(f2);
        if (!visited1.is_marked(f2))
            return false;
    }
    SASSERT(num2 <= sz);
    SASSERT(0 <= num2);
    SASSERT(num1 >= num2);
    return num1 == num2;
}

bool goal::is_cnf() const {
    for (unsigned i = 0; i < size(); i++) {
        expr * f = form(i);
        if (m_manager.is_or(f)) {
            for (expr* lit : *to_app(f)) {
                if (!is_literal(lit)) {
                    return false;
                }
            }
            return true;
        }
        if (!is_literal(f)) {
            return false;
        }
    }
    return true;
}

bool goal::is_literal(expr* f) const {
    m_manager.is_not(f, f);
    if (!is_app(f)) return false;
    if (to_app(f)->get_family_id() == m_manager.get_basic_family_id()) {
        for (expr* arg : *to_app(f)) 
            if (m_manager.is_bool(arg)) {
                return false;
            }
    }
    return true;
}
