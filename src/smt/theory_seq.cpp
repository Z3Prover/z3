/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_seq.h

Abstract:

    Native theory solver for sequences.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12

Revision History:

--*/

#include "value_factory.h"
#include "smt_context.h"
#include "smt_model_generator.h"
#include "theory_seq.h"
#include "seq_rewriter.h"

using namespace smt;

theory_seq::theory_seq(ast_manager& m):
    theory(m.mk_family_id("seq")), 
    m(m),
    m_dam(m_dep_array_value_manager, m_alloc),
    m_rep(m),    
    m_eqs_head(0),
    m_ineqs(m),
    m_axioms(m),
    m_axioms_head(0),
    m_incomplete(false), 
    m_rewrite(m), 
    m_util(m),
    m_autil(m),
    m_trail_stack(*this),
    m_find(*this) {
    m_lhs.push_back(expr_array());
    m_rhs.push_back(expr_array());
    m_deps.push_back(enode_pair_dependency_array());
}

final_check_status theory_seq::final_check_eh() { 
    context & ctx   = get_context();
    if (!check_ineqs()) {
        return FC_CONTINUE;
    }
    if (simplify_and_solve_eqs()) {
        return FC_CONTINUE;
    }
    if (m.size(m_lhs.back()) > 0) {
        return FC_GIVEUP;        
    }
    return m_incomplete?FC_GIVEUP:FC_DONE; 
}

bool theory_seq::check_ineqs() {
    context & ctx   = get_context();
    for (unsigned i = 0; i < m_ineqs.size(); ++i) {
        expr_ref a(m_ineqs[i].get(), m);
        enode_pair_dependency* eqs = 0;
        expr_ref b = canonize(a, eqs);
        if (m.is_true(b)) {
            ctx.internalize(a, false);
            literal lit(ctx.get_literal(a));
            ctx.mark_as_relevant(lit);
            vector<enode_pair, false> _eqs;
            m_dm.linearize(eqs, _eqs);
            ctx.assign(
                lit, 
                ctx.mk_justification(
                    ext_theory_propagation_justification(
                        get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), lit)));
            return false;
        }
    }
    return true;
}


bool theory_seq::simplify_eq(expr* l, expr* r, enode_pair_dependency* deps) {
    context& ctx = get_context();
    seq_rewriter rw(m);
    expr_ref_vector lhs(m), rhs(m);
    SASSERT(ctx.e_internalized(l));
    SASSERT(ctx.e_internalized(r));
    expr_ref lh = canonize(l, deps);
    expr_ref rh = canonize(r, deps);
    if (!rw.reduce_eq(l, r, lhs, rhs)) {
        // equality is inconsistent.
        // create conflict assignment.  
        expr_ref a(m);
        a = m.mk_eq(l, r);
        literal lit(ctx.get_literal(a));
        vector<enode_pair, false> _eqs;
        m_dm.linearize(deps, _eqs);
        ctx.assign(
            ~lit,
            ctx.mk_justification(
                ext_theory_propagation_justification(
                    get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), ~lit)));
        return true;
    }
    if (lhs.size() == 1 && l == lhs[0].get() &&
        rhs.size() == 1 && r == rhs[0].get()) {
        return false;
    }
    SASSERT(lhs.size() == rhs.size());
    for (unsigned i = 0; i < lhs.size(); ++i) {
        m.push_back(m_lhs.back(), lhs[i].get());
        m.push_back(m_rhs.back(), rhs[i].get());
        m_dam.push_back(m_deps.back(), deps);
    }    
    return true;
}

bool theory_seq::solve_unit_eq(expr* l, expr* r, enode_pair_dependency* deps) {
    expr_ref lh = canonize(l, deps);
    expr_ref rh = canonize(r, deps);
    if (is_var(lh) && !occurs(lh, rh)) {
        add_solution(lh, rh, deps);
        return true;
    }
    if (is_var(rh) && !occurs(rh, lh)) {
        add_solution(rh, lh, deps);
        return true;
    }
    // Use instead reference counts for dependencies to GC?

    return false;
}

bool theory_seq::occurs(expr* a, expr* b) {
    // TBD
    return true;
}

bool theory_seq::is_var(expr* a) {
    // TBD
    return false;
}

void theory_seq::add_solution(expr* l, expr* r, enode_pair_dependency* deps) {
    context& ctx = get_context();
    // TBD: internalize lh, rh;
    // 
    enode* n1 = ctx.get_enode(l);
    enode* n2 = ctx.get_enode(r);
    // TBD: add substitution l -> r
    vector<enode_pair, false> _eqs;
    m_dm.linearize(deps, _eqs);
    // alloc?
    ctx.assign_eq(n1, n2, eq_justification(
                      alloc(ext_theory_eq_propagation_justification,
                            get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), n1, n2)));
}

bool theory_seq::simplify_eqs() {
    return pre_process_eqs(true);
}

bool theory_seq::solve_basic_eqs() {
    return pre_process_eqs(false);
}

bool theory_seq::pre_process_eqs(bool simplify_or_solve) {
    context& ctx = get_context();
    bool change = false;
    expr_array& lhs = m_lhs.back();
    expr_array& rhs = m_rhs.back();
    enode_pair_dependency_array& deps = m_deps.back();
    for (unsigned i = 0; !ctx.inconsistent() && i < m.size(lhs); ++i) {
        if (simplify_or_solve?
            simplify_eq(m.get(lhs, i), m.get(rhs, i), m_dam.get(deps, i)):
            solve_unit_eq(m.get(lhs, i), m.get(rhs, i), m_dam.get(deps, i))) {  
            if (i + 1 != m.size(lhs)) {
                m.set(lhs, i, m.get(lhs, m.size(lhs)-1));
                m.set(rhs, i, m.get(rhs, m.size(rhs)-1));
                m_dam.set(deps, i, m_dam.get(deps, m_dam.size(deps)-1));
                --i;
                change = true;
            }
            m.pop_back(lhs);
            m.pop_back(rhs);
            m_dam.pop_back(deps);
        }
    }    
    return change;
}

bool theory_seq::simplify_and_solve_eqs() {
    context & ctx   = get_context();
    bool change = simplify_eqs();
    while (!ctx.inconsistent() && solve_basic_eqs()) {
        simplify_eqs();
        change = true;
    }
    return change;
}


final_check_status theory_seq::add_axioms() {
    for (unsigned i = 0; i < get_num_vars(); ++i) {

        // add axioms for len(x) when x = a ++ b
    }
    return FC_DONE;
}

bool theory_seq::internalize_atom(app* a, bool) { 
    return internalize_term(a);
}

bool theory_seq::internalize_term(app* term) { 
    context & ctx   = get_context();
    unsigned num_args = term->get_num_args();
    for (unsigned i = 0; i < num_args; i++) {
        ctx.internalize(term->get_arg(i), false);
    }
    if (ctx.e_internalized(term)) {
        return true;
    }
    enode * e = ctx.mk_enode(term, false, m.is_bool(term), true); 
    if (m.is_bool(term)) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
    }
    else {
        theory_var v = mk_var(e);
        ctx.attach_th_var(e, this, v);
    }
    if (!m_util.str.is_concat(term) &&
        !m_util.str.is_string(term) &&
        !m_util.str.is_suffix(term) &&
        !m_util.str.is_prefix(term) &&
        !m_util.str.is_contains(term)) {
        set_incomplete(term);
    }
        
    // assert basic axioms    
    return true;
}

void theory_seq::set_incomplete(app* term) {
    TRACE("seq", tout << "No support for: " << mk_pp(term, m) << "\n";);
    if (!m_incomplete) { 
        m_trail_stack.push(value_trail<theory_seq,bool>(m_incomplete)); 
        m_incomplete = true; 
    } 
}

theory_var theory_seq::mk_var(enode* n) {
    theory_var r = theory::mk_var(n);
    VERIFY(r == m_find.mk_var());
    m_rep.push_back(n->get_owner());
    return r;
}

bool theory_seq::can_propagate() {
    return m_axioms_head < m_axioms.size();
}

expr_ref theory_seq::canonize(expr* e, enode_pair_dependency*& eqs) {
    expr_ref result = expand(e, eqs);
    m_rewrite(result);
    return result;
}

expr_ref theory_seq::expand(expr* e, enode_pair_dependency*& eqs) {
    context& ctx = get_context();
    expr* e1, *e2;
    SASSERT(ctx.e_internalized(e));
    enode* n = ctx.get_enode(e);
    enode* start = n;
    do {
        e = n->get_owner();
        if (m_util.str.is_concat(e, e1, e2)) {
            add_dependency(eqs, start, n);
            return expr_ref(m_util.str.mk_concat(expand(e1, eqs), expand(e2, eqs)), m);
        }        
        if (m_util.str.is_empty(e) || m_util.str.is_string(e)) {
            add_dependency(eqs, start, n);
            return expr_ref(e, m);
        }
        if (m.is_eq(e, e1, e2)) {
            add_dependency(eqs, start, n);
            return expr_ref(m.mk_eq(expand(e1, eqs), expand(e2, eqs)), m);
        }
        if (m_util.str.is_prefix(e, e1, e2)) {
            add_dependency(eqs, start, n);
            return expr_ref(m_util.str.mk_prefix(expand(e1, eqs), expand(e2, eqs)), m);
        }
        if (m_util.str.is_suffix(e, e1, e2)) {
            add_dependency(eqs, start, n);
            return expr_ref(m_util.str.mk_suffix(expand(e1, eqs), expand(e2, eqs)), m);
        }
        if (m_util.str.is_contains(e, e1, e2)) {
            add_dependency(eqs, start, n);
            return expr_ref(m_util.str.mk_contains(expand(e1, eqs), expand(e2, eqs)), m);
        }
#if 0
        if (m_util.str.is_unit(e)) {
            // TBD: canonize the element.
            if (start != n) eqs.push_back(enode_pair(start, n));
            return expr_ref(e, m);
        }
#endif
        n = n->get_next();
    }
    while (n != start);
    return expr_ref(n->get_root()->get_owner(), m);
}

void theory_seq::add_dependency(enode_pair_dependency*& dep, enode* a, enode* b) {
    dep = join(dep, leaf(a, b));
}

theory_seq::enode_pair_dependency* theory_seq::join(enode_pair_dependency* a, enode_pair_dependency* b) {
    if (!a) return b;
    if (!b) return a;
    return m_dm.mk_join(a, b);
}

theory_seq::enode_pair_dependency* theory_seq::leaf(enode* a, enode* b) {
    return (a == b)?0:m_dm.mk_leaf(std::make_pair(a, b));
}

void theory_seq::propagate() {
    context & ctx = get_context();
    while (m_axioms_head < m_axioms.size() && !ctx.inconsistent()) {
        expr_ref e(m);
        e = m_axioms[m_axioms_head].get();
        assert_axiom(e);
        ++m_axioms_head;
    }
}

void theory_seq::create_axiom(expr_ref& e) {
    m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_axioms));
    m_axioms.push_back(e);
}

void theory_seq::assert_axiom(expr_ref& e) {
    context & ctx = get_context();
    if (m.is_true(e)) return;
    TRACE("seq", tout << "asserting " << e << "\n";);
    ctx.internalize(e, false);
    literal lit(ctx.get_literal(e));
    ctx.mark_as_relevant(lit);
    ctx.mk_th_axiom(get_id(), 1, &lit);

}

expr_ref theory_seq::mk_skolem(char const* name, expr* e1, expr* e2) {
    expr_ref result(m);
    sort* s = m.get_sort(e1);
    SASSERT(s == m.get_sort(e2));
    sort* ss[2] = { s, s };
    result = m.mk_app(m.mk_func_decl(symbol("#prefix_eq"), 2, ss, s), e1, e2);
    return result;
}

void theory_seq::propagate_eq(bool_var v, expr* e1, expr* e2) {
    context& ctx = get_context();
    ctx.internalize(e1, false);
    enode* n1 = ctx.get_enode(e1);
    enode* n2 = ctx.get_enode(e2);
    literal lit(v);
    ctx.assign_eq(n1, n2, eq_justification(
                      alloc(ext_theory_eq_propagation_justification,
                          get_id(), ctx.get_region(), 1, &lit, 0, 0, n1, n2)));
}

void theory_seq::assign_eq(bool_var v, bool is_true) {
    context & ctx = get_context();

    enode* n = ctx.bool_var2enode(v);
    app*  e = n->get_owner();
    if (is_true) {
        expr* e1, *e2;
        expr_ref f(m);
        if (m_util.str.is_prefix(e, e1, e2)) {
            f = mk_skolem("#prefix_eq", e1, e2);
            f = m_util.str.mk_concat(e1, f);
            propagate_eq(v, f, e2);
        }
        else if (m_util.str.is_suffix(e, e1, e2)) {
            f = mk_skolem("#suffix_eq", e1, e2);
            f = m_util.str.mk_concat(f, e1);
            propagate_eq(v, f, e2);
        }
        else if (m_util.str.is_contains(e, e1, e2)) {
            expr_ref f1 = mk_skolem("#contains_eq1", e1, e2);
            expr_ref f2 = mk_skolem("#contains_eq2", e1, e2);
            f = m_util.str.mk_concat(m_util.str.mk_concat(f1, e1), f2);
            propagate_eq(v, f, e2);
        }
        else if (m_util.str.is_in_re(e, e1, e2)) {
            NOT_IMPLEMENTED_YET();
        }
        else {
            UNREACHABLE();
        }
    }
    else {
        m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_ineqs));
        m_ineqs.push_back(e);
    }
}

void theory_seq::new_eq_eh(theory_var v1, theory_var v2) { 
    m_find.merge(v1, v2);
    expr_ref e1(m), e2(m);
    e1 = get_enode(v1)->get_owner();
    e2 = get_enode(v2)->get_owner();
    m.push_back(m_lhs.back(), get_enode(v1)->get_owner());
    m.push_back(m_rhs.back(), get_enode(v2)->get_owner());
}

void theory_seq::new_diseq_eh(theory_var v1, theory_var v2) {
    expr* e1 = get_enode(v1)->get_owner();
    expr* e2 = get_enode(v2)->get_owner();
    m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_ineqs));
    m_ineqs.push_back(m.mk_eq(e1, e2));
}

void theory_seq::push_scope_eh() {
    theory::push_scope_eh();
    m_dm.push_scope();
    m_trail_stack.push_scope();
    m_trail_stack.push(value_trail<theory_seq, unsigned>(m_axioms_head));
    m_trail_stack.push(value_trail<theory_seq, unsigned>(m_eqs_head));
    expr_array lhs, rhs;
    enode_pair_dependency_array deps;
    m.copy(m_lhs.back(), lhs);
    m.copy(m_rhs.back(), rhs);
    m_dam.copy(m_deps.back(), deps);
    m_lhs.push_back(lhs);
    m_rhs.push_back(rhs);
    m_deps.push_back(deps);
}

void theory_seq::pop_scope_eh(unsigned num_scopes) {
    m_trail_stack.pop_scope(num_scopes);
    theory::pop_scope_eh(num_scopes);   
    m_dm.pop_scope(num_scopes); 
    m_rep.resize(get_num_vars());
    while (num_scopes > 0) {
        --num_scopes;
        m.del(m_lhs.back());
        m.del(m_rhs.back());
        m_dam.del(m_deps.back());
        m_lhs.pop_back();
        m_rhs.pop_back();
        m_deps.pop_back();
    }
}

void theory_seq::restart_eh() {

}

void theory_seq::relevant_eh(app* n) {
    if (m_util.str.is_length(n)) {
        expr_ref e(m);
        e = m_autil.mk_le(m_autil.mk_numeral(rational(0), true), n);
        create_axiom(e);
    }
}
