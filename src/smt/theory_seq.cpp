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

void theory_seq::solution_map::update(expr* e, expr* r, enode_pair_dependency* d) {
    std::pair<expr*, enode_pair_dependency*> value;
    if (m_map.find(e, value)) {
        m_updates.push_back(DEL);
        m_lhs.push_back(e);
        m_rhs.push_back(value.first);
        m_deps.push_back(value.second);
    }
    value.first = r;
    value.second = d;
    m_map.insert(e, value);
    m_updates.push_back(INS);
    m_lhs.push_back(e);
    m_rhs.push_back(value.first);
    m_deps.push_back(value.second);
}

expr* theory_seq::solution_map::find(expr* e, enode_pair_dependency*& d) {
    std::pair<expr*, enode_pair_dependency*> value;
    d = 0;
    // TBD add path compression?
    while (m_map.find(e, value)) {
        d = d ? m_dm.mk_join(d, value.second) : value.second;;
        e = value.first;
    }
    return e;
}

void theory_seq::solution_map::pop_scope(unsigned num_scopes) {
    if (num_scopes == 0) return;    
    unsigned start = m_limit[m_limit.size() - num_scopes];
    for (unsigned i = m_updates.size(); i > start; ) {
        --i;
        if (m_updates[i] == INS) {
            m_map.remove(m_lhs[i].get());
        }
        else {
            m_map.insert(m_lhs[i].get(), std::make_pair(m_rhs[i].get(), m_deps[i]));
        }
    }
    m_updates.resize(start);
    m_lhs.resize(start);
    m_rhs.resize(start);
    m_deps.resize(start);
    m_limit.resize(m_limit.size() - num_scopes);
}

theory_seq::theory_seq(ast_manager& m):
    theory(m.mk_family_id("seq")), 
    m(m),
    m_dam(m_dep_array_value_manager, m_alloc),
    m_rep(m, m_dm),    
    m_ineqs(m),
    m_axioms(m),
    m_axioms_head(0),
    m_incomplete(false), 
    m_rewrite(m), 
    m_util(m),
    m_autil(m),
    m_trail_stack(*this) {
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
    if (lh == rh) {
        return true;
    }
    if (is_var(lh) && !occurs(lh, rh)) {
        add_solution(lh, rh, deps);
        return true;
    }
    if (is_var(rh) && !occurs(rh, lh)) {
        add_solution(rh, lh, deps);
        return true;
    }
    // Use instead reference counts for dependencies to GC?

    // TBD: Solutions to units are not necessarily variables, but
    // they may induce new equations.

    return false;
}

bool theory_seq::occurs(expr* a, expr* b) {
    SASSERT(is_var(a));
    // true if a occurs under an interpreted function or under left/right selector.
    if (a == b) {
        return true;
    }
    expr* e1, *e2;
    if (m_util.str.is_concat(b, e1, e2)) {
        return occurs(a, e1) || occurs(a, e2);
    }
    if (is_left_select(b, e1) || is_right_select(b, e1)) {
        return occurs(a, e1);
    }
    return false;
}

bool theory_seq::is_var(expr* a) {
    return is_uninterp(a);
}

bool theory_seq::is_left_select(expr* a, expr*& b) {
    return false;
}

bool theory_seq::is_right_select(expr* a, expr*& b) {
    return false;
}


void theory_seq::add_solution(expr* l, expr* r, enode_pair_dependency* deps) {
    context& ctx = get_context();
    m_rep.update(l, r, deps);
    // TBD: skip new equalities for non-internalized terms.
    if (ctx.e_internalized(l) && ctx.e_internalized(r)) {
        enode* n1 = ctx.get_enode(l);
        enode* n2 = ctx.get_enode(r);
        vector<enode_pair, false> _eqs;
        m_dm.linearize(deps, _eqs);
        // alloc?
        ctx.assign_eq(n1, n2, eq_justification(
                          alloc(ext_theory_eq_propagation_justification,
                                get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), n1, n2)));
    }
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
        !m_util.str.is_empty(term)  && 
        !m_util.str.is_unit(term)   &&
        !m_util.str.is_suffix(term) &&
        !m_util.str.is_prefix(term) &&
        !m_util.str.is_contains(term)) {
        set_incomplete(term);
    }
        
    // assert basic axioms    
    return true;
}

void theory_seq::apply_sort_cnstr(enode* n, sort* s) {
    if (!is_attached_to_var(n)) {
        mk_var(n);
    }
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
    enode_pair_dependency* deps = 0;
    e = m_rep.find(e, deps);
    expr* e1, *e2;
    eqs = join(eqs, deps);
    if (m_util.str.is_concat(e, e1, e2)) {
        return expr_ref(m_util.str.mk_concat(expand(e1, eqs), expand(e2, eqs)), m);
    }        
    if (m_util.str.is_empty(e) || m_util.str.is_string(e)) {
        return expr_ref(e, m);
    }
    if (m.is_eq(e, e1, e2)) {
        return expr_ref(m.mk_eq(expand(e1, eqs), expand(e2, eqs)), m);
    }
    if (m_util.str.is_prefix(e, e1, e2)) {
        return expr_ref(m_util.str.mk_prefix(expand(e1, eqs), expand(e2, eqs)), m);
    }
    if (m_util.str.is_suffix(e, e1, e2)) {
        return expr_ref(m_util.str.mk_suffix(expand(e1, eqs), expand(e2, eqs)), m);
    }
    if (m_util.str.is_contains(e, e1, e2)) {
        return expr_ref(m_util.str.mk_contains(expand(e1, eqs), expand(e2, eqs)), m);
    }
    return expr_ref(e, m);
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
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);
    m.push_back(m_lhs.back(), n1->get_owner());
    m.push_back(m_rhs.back(), n2->get_owner());
    m_dam.push_back(m_deps.back(), leaf(n1, n2));
}

void theory_seq::new_diseq_eh(theory_var v1, theory_var v2) {
    expr* e1 = get_enode(v1)->get_owner();
    expr* e2 = get_enode(v2)->get_owner();
    m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_ineqs));
    m_ineqs.push_back(m.mk_eq(e1, e2));
}

void theory_seq::push_scope_eh() {
    theory::push_scope_eh();
    m_rep.push_scope();
    m_dm.push_scope();
    m_trail_stack.push_scope();
    m_trail_stack.push(value_trail<theory_seq, unsigned>(m_axioms_head));
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
    m_rep.pop_scope(num_scopes);
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
    SASSERT(m_lhs.size() == 1);
    m.del(m_lhs.back());
    m.del(m_rhs.back());
    m_dam.del(m_deps.back());
    m_lhs.reset();
    m_rhs.reset();
    m_deps.reset();
    m_lhs.push_back(expr_array());
    m_rhs.push_back(expr_array());
    m_deps.push_back(enode_pair_dependency_array());

}

void theory_seq::relevant_eh(app* n) {
    if (m_util.str.is_length(n)) {
        expr_ref e(m);
        e = m_autil.mk_le(m_autil.mk_numeral(rational(0), true), n);
        create_axiom(e);
    }
}
