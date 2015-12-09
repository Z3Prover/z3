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
    unsigned num_finds = 0;
    expr* result = e;
    while (m_map.find(result, value)) {
        d = m_dm.mk_join(d, value.second);
        result = value.first;
        ++num_finds;
    }
    if (num_finds > 1) { // path compression for original key only.
        update(e, result, d);
    }
    return result;
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

void theory_seq::solution_map::display(std::ostream& out) const {
    map_t::iterator it = m_map.begin(), end = m_map.end();
    for (; it != end; ++it) {
        out << mk_pp(it->m_key, m) << " |-> " << mk_pp(it->m_value.first, m) << "\n";
    }
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
    m_prefix_sym = "prefix";
    m_suffix_sym = "suffix";
    m_left_sym = "left";
    m_right_sym = "right";
    m_contains_left_sym = "contains_left";
    m_contains_right_sym = "contains_right";
}

theory_seq::~theory_seq() {
    unsigned num_scopes = m_lhs.size()-1;
    if (num_scopes > 0) pop_scope_eh(num_scopes);
    m.del(m_lhs.back());
    m.del(m_rhs.back());
    m_dam.del(m_deps.back());
}


final_check_status theory_seq::final_check_eh() { 
    context & ctx   = get_context();
    TRACE("seq", display(tout););
    if (!check_ineqs()) {
        return FC_CONTINUE;
    }
    if (simplify_and_solve_eqs()) {
        return FC_CONTINUE;
    }
    if (ctx.inconsistent()) {
        return FC_CONTINUE;
    }
    if (m.size(m_lhs.back()) > 0 || m_incomplete) {
        return FC_GIVEUP;        
    }
    return FC_DONE; 
}

bool theory_seq::check_ineqs() {
    context & ctx   = get_context();
    for (unsigned i = 0; i < m_ineqs.size(); ++i) {
        expr* a = m_ineqs[i].get();
        enode_pair_dependency* eqs = 0;
        expr_ref b = canonize(a, eqs);
        if (m.is_true(b)) {
            TRACE("seq", tout << "Evaluates to false: " << mk_pp(a,m) << "\n";);
            ctx.internalize(a, false);
            propagate_lit(eqs, ctx.get_literal(a));
            return false;
        }
    }
    return true;
}

void theory_seq::propagate_lit(enode_pair_dependency* dep, literal lit) {
    context& ctx = get_context();
    ctx.mark_as_relevant(lit);
    vector<enode_pair, false> _eqs;
    m_dm.linearize(dep, _eqs);
    TRACE("seq", 
          ctx.display_detailed_literal(tout, lit);
          tout << " <- ";
          for (unsigned i = 0; i < _eqs.size(); ++i) {
              tout << mk_pp(_eqs[i].first->get_owner(), m) << " = " 
                   << mk_pp(_eqs[i].second->get_owner(), m) << "\n";
          }
          ); 
    justification* js = 
        ctx.mk_justification(
            ext_theory_propagation_justification(
                get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), lit));

    ctx.assign(lit, js);
}

void theory_seq::set_conflict(enode_pair_dependency* dep) {
    context& ctx = get_context();
    vector<enode_pair, false> _eqs;
    m_dm.linearize(dep, _eqs);
    TRACE("seq", 
          for (unsigned i = 0; i < _eqs.size(); ++i) {
              tout << mk_pp(_eqs[i].first->get_owner(), m) << " = " 
                   << mk_pp(_eqs[i].second->get_owner(), m) << "\n";
          }
          ); 
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), 0, 0)));
}

void theory_seq::propagate_eq(enode_pair_dependency* dep, enode* n1, enode* n2) {
    context& ctx = get_context();
    vector<enode_pair, false> _eqs;
    m_dm.linearize(dep, _eqs);
    TRACE("seq",
          tout << mk_pp(n1->get_owner(), m) << " " << mk_pp(n2->get_owner(), m) << " <- ";
          for (unsigned i = 0; i < _eqs.size(); ++i) {
              tout << mk_pp(_eqs[i].first->get_owner(), m) << " = " 
                   << mk_pp(_eqs[i].second->get_owner(), m) << "\n";
          }
          ); 
    
    justification* js = ctx.mk_justification(
        ext_theory_eq_propagation_justification(
            get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), n1, n2));
    ctx.assign_eq(n1, n2, eq_justification(js));
}



bool theory_seq::simplify_eq(expr* l, expr* r, enode_pair_dependency* deps) {
    context& ctx = get_context();
    seq_rewriter rw(m);
    expr_ref_vector lhs(m), rhs(m);
    expr_ref lh = canonize(l, deps);
    expr_ref rh = canonize(r, deps);
    if (!rw.reduce_eq(lh, rh, lhs, rhs)) {
        // equality is inconsistent.
        TRACE("seq", tout << lh << " != " << rh << "\n";);
        set_conflict(deps);
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
    TRACE("seq",
          tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " => ";
          for (unsigned i = 0; i < lhs.size(); ++i) {
              tout << mk_pp(lhs[i].get(), m) << " = " << mk_pp(rhs[i].get(), m) << "; ";
          }
          tout << "\n";
          );
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
    // true if a occurs under an interpreted function or under left/right selector.    
    SASSERT(is_var(a));
    expr* e1, *e2;
    while (is_left_select(a, e1) || is_right_select(a, e1)) {
        a = e1;
    }
    if (m_util.str.is_concat(b, e1, e2)) {
        return occurs(a, e1) || occurs(a, e2);
    }
    while (is_left_select(b, e1) || is_right_select(b, e1)) {
        b = e1;
    }          
    if (a == b) {
        return true;
    }  
    return false;
}

bool theory_seq::is_var(expr* a) {
    return is_uninterp(a) || m_util.is_skolem(a);
}

bool theory_seq::is_left_select(expr* a, expr*& b) {
    return m_util.is_skolem(a) && 
        to_app(a)->get_decl()->get_parameter(0).get_symbol() == m_left_sym && (b = to_app(a)->get_arg(0), true);
}

bool theory_seq::is_right_select(expr* a, expr*& b) {
    return m_util.is_skolem(a) &&
        to_app(a)->get_decl()->get_parameter(0).get_symbol() == m_right_sym && (b = to_app(a)->get_arg(0), true);
}


void theory_seq::add_solution(expr* l, expr* r, enode_pair_dependency* deps) {
    context& ctx = get_context();
    m_rep.update(l, r, deps);
    // TBD: skip new equalities for non-internalized terms.
    if (ctx.e_internalized(l) && ctx.e_internalized(r)) {
        enode* n1 = ctx.get_enode(l);
        enode* n2 = ctx.get_enode(r);
        propagate_eq(deps, n1, n2);
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
                ++m_stats.m_num_reductions;
            }
            m.pop_back(lhs);
            m.pop_back(rhs);
            m_dam.pop_back(deps);
            change = true;
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
    if (m.is_bool(term)) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
    }
    else {
        enode * e = ctx.mk_enode(term, false, m.is_bool(term), true); 
        theory_var v = mk_var(e);
        ctx.attach_th_var(e, this, v);
    }
    if (!m_util.str.is_concat(term) &&
        !m_util.str.is_string(term) &&
        !m_util.str.is_empty(term)  && 
        !m_util.str.is_unit(term)   &&
        !m_util.str.is_suffix(term) &&
        !m_util.str.is_prefix(term) &&
        !m_util.str.is_contains(term) &&
        !m_util.is_skolem(term)) {
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

void theory_seq::display(std::ostream & out) const {
    expr_array const& lhs = m_lhs.back();
    expr_array const& rhs = m_rhs.back();
    enode_pair_dependency_array const& deps = m_deps.back();
    out << "Equations:\n";
    for (unsigned i = 0; i < m.size(lhs); ++i) {
        out << mk_pp(m.get(lhs, i), m) << " = " << mk_pp(m.get(rhs, i), m) << " <-\n";
        enode_pair_dependency* dep = m_dam.get(deps, i);
        if (dep) {
            vector<enode_pair, false> _eqs;
            const_cast<enode_pair_dependency_manager&>(m_dm).linearize(dep, _eqs);
            for (unsigned i = 0; i < _eqs.size(); ++i) {
                out << " " << mk_pp(_eqs[i].first->get_owner(), m) << " = " << mk_pp(_eqs[i].second->get_owner(), m) << "\n";
            }
        }
    }
    out << "Negative constraints:\n";
    for (unsigned i = 0; i < m_ineqs.size(); ++i) {
        out << mk_pp(m_ineqs[i], m) << "\n";
    }
    out << "Solved equations:\n";
    m_rep.display(out);
}

void theory_seq::collect_statistics(::statistics & st) const {
    st.update("seq num splits", m_stats.m_num_splits);
    st.update("seq num reductions", m_stats.m_num_reductions);
}

void theory_seq::init_model(model_generator & mg) {
    m_factory = alloc(seq_factory, get_manager(), 
                      get_family_id(), mg.get_model());
    mg.register_factory(m_factory);
    // TBD: this is still unsound model generation.
    // disequalities are not guaranteed. we need to
    // prime the factory with a prefix that cannot be
    // constructed using any existing combinations of the
    // strings (or units) that are used.
    for (unsigned i = 0; i < get_num_vars(); ++i) {
        expr* e = get_enode(i)->get_owner();
        if (m_util.is_seq(e)) {
            enode_pair_dependency* deps = 0;
            e = m_rep.find(e, deps);
            if (is_var(e)) {
                expr* val = m_factory->get_fresh_value(m.get_sort(e));
                m_rep.update(e, val, 0);
            }
        }
        else if (m_util.is_re(e)) {
            // TBD
        }
    }
}

model_value_proc * theory_seq::mk_value(enode * n, model_generator & mg) {
    enode_pair_dependency* deps = 0;
    expr_ref e(n->get_owner(), m);
    canonize(e, deps);
    SASSERT(is_app(e));
    m_factory->add_trail(e);
    return alloc(expr_wrapper_proc, to_app(e));
}



void theory_seq::set_incomplete(app* term) {
    TRACE("seq", tout << "No support for: " << mk_pp(term, m) << "\n";);
    if (!m_incomplete) { 
        m_trail_stack.push(value_trail<theory_seq,bool>(m_incomplete)); 
        m_incomplete = true; 
    } 
}

theory_var theory_seq::mk_var(enode* n) {
    return theory::mk_var(n);
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
    eqs = m_dm.mk_join(eqs, deps);
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
    if (a != b) {
        dep = m_dm.mk_join(dep, m_dm.mk_leaf(std::make_pair(a, b)));
    }
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

expr_ref theory_seq::mk_skolem(symbol const& name, expr* e1, expr* e2) {
    expr* es[2] = { e1, e2 };
    return expr_ref(m_util.mk_skolem(name, 2, es, m.get_sort(e1)), m);
}

void theory_seq::propagate_eq(bool_var v, expr* e1, expr* e2) {
    context& ctx = get_context();
    TRACE("seq", 
          tout << mk_pp(ctx.bool_var2enode(v)->get_owner(), m) << " => " 
          << mk_pp(e1, m) << " = " << mk_pp(e2, m) << "\n";); 

    ctx.internalize(e1, false);
    SASSERT(ctx.e_internalized(e2));
    enode* n1 = ctx.get_enode(e1);
    enode* n2 = ctx.get_enode(e2);
    literal lit(v);
    justification* js = 
        ctx.mk_justification(
            ext_theory_eq_propagation_justification(
                get_id(), ctx.get_region(), 1, &lit, 0, 0, n1, n2));

    ctx.assign_eq(n1, n2, eq_justification(js));
}

void theory_seq::assign_eq(bool_var v, bool is_true) {
    context & ctx = get_context();
    enode* n = ctx.bool_var2enode(v);
    app*  e = n->get_owner();
    if (is_true) {
        expr* e1, *e2;
        expr_ref f(m);
        if (m_util.str.is_prefix(e, e1, e2)) {
            f = mk_skolem(m_prefix_sym, e1, e2);
            f = m_util.str.mk_concat(e1, f);
            propagate_eq(v, f, e2);
        }
        else if (m_util.str.is_suffix(e, e1, e2)) {
            f = mk_skolem(m_suffix_sym, e1, e2);
            f = m_util.str.mk_concat(f, e1);
            propagate_eq(v, f, e2);
        }
        else if (m_util.str.is_contains(e, e1, e2)) {
            expr_ref f1 = mk_skolem(m_contains_left_sym, e1, e2);
            expr_ref f2 = mk_skolem(m_contains_right_sym, e1, e2);
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
    if (n1 != n2) {
        m.push_back(m_lhs.back(), n1->get_owner());
        m.push_back(m_rhs.back(), n2->get_owner());
        m_dam.push_back(m_deps.back(), m_dm.mk_leaf(enode_pair(n1, n2)));
    }
}

void theory_seq::new_diseq_eh(theory_var v1, theory_var v2) {
    expr* e1 = get_enode(v1)->get_owner();
    expr* e2 = get_enode(v2)->get_owner();
    m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_ineqs));
    m_ineqs.push_back(mk_eq_atom(e1, e2));
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
