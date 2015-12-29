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
#include "ast_trail.h"
#include "theory_arith.h"

using namespace smt;

struct display_expr {
    ast_manager& m;
    display_expr(ast_manager& m): m(m) {}
    std::ostream& display(std::ostream& out, expr* e) const {
        return out << mk_pp(e, m);
    }
};



void theory_seq::solution_map::update(expr* e, expr* r, enode_pair_dependency* d) {
    if (e == r) {
        return;
    }
    m_cache.reset();
    std::pair<expr*, enode_pair_dependency*> value;
    if (m_map.find(e, value)) {
        add_trail(DEL, e, value.first, value.second);
    }
    value.first = r;
    value.second = d;
    m_map.insert(e, value);
    add_trail(INS, e, r, d);
}

void theory_seq::solution_map::add_trail(map_update op, expr* l, expr* r, enode_pair_dependency* d) {
    m_updates.push_back(op);
    m_lhs.push_back(l);
    m_rhs.push_back(r);
    m_deps.push_back(d);
}

bool theory_seq::solution_map::is_root(expr* e) const {
    return !m_map.contains(e);
}

expr* theory_seq::solution_map::find(expr* e, enode_pair_dependency*& d) {
    std::pair<expr*, enode_pair_dependency*> value;
    d = 0;
    expr* result = e;
    while (m_map.find(result, value)) {
        d = m_dm.mk_join(d, value.second);
        TRACE("seq", tout << mk_pp(result, m) << " -> " << mk_pp(value.first, m) << "\n";);
        SASSERT(result != value.first);
        SASSERT(e != value.first);
        result = value.first;
    }
    return result;
}

void theory_seq::solution_map::pop_scope(unsigned num_scopes) {
    if (num_scopes == 0) return;    
    m_cache.reset();
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
    eqdep_map_t::iterator it = m_map.begin(), end = m_map.end();
    for (; it != end; ++it) {
        out << mk_pp(it->m_key, m) << " |-> " << mk_pp(it->m_value.first, m) << "\n";
    }
}

bool theory_seq::exclusion_table::contains(expr* e, expr* r) const {
    if (e->get_id() > r->get_id()) {
        std::swap(e, r);
    }
    return m_table.contains(std::make_pair(e, r));
}

void theory_seq::exclusion_table::update(expr* e, expr* r) {
    if (e->get_id() > r->get_id()) {
        std::swap(e, r);
    }
    if (e != r && !m_table.contains(std::make_pair(e, r))) {
        m_lhs.push_back(e);
        m_rhs.push_back(r);
        m_table.insert(std::make_pair(e, r));
    }
}

void theory_seq::exclusion_table::pop_scope(unsigned num_scopes) {
    if (num_scopes == 0) return;
    unsigned start = m_limit[m_limit.size() - num_scopes];
    for (unsigned i = start; i < m_lhs.size(); ++i) {
        m_table.erase(std::make_pair(m_lhs[i].get(), m_rhs[i].get()));
    }
    m_lhs.resize(start);
    m_rhs.resize(start);
    m_limit.resize(m_limit.size() - num_scopes);
}

void theory_seq::exclusion_table::display(std::ostream& out) const {
    table_t::iterator it = m_table.begin(), end = m_table.end();
    for (; it != end; ++it) {
        out << mk_pp(it->first, m) << " != " << mk_pp(it->second, m) << "\n";
    }
}

theory_seq::theory_seq(ast_manager& m):
    theory(m.mk_family_id("seq")), 
    m(m),
    m_rep(m, m_dm),
    m_factory(0),
    m_ineqs(m),
    m_exclude(m),
    m_axioms(m),
    m_axioms_head(0),
    m_branch_variable_head(0),
    m_mg(0),
    m_rewrite(m), 
    m_util(m),
    m_autil(m),
    m_trail_stack(*this),
    m_accepts_qhead(0),
    m_rejects_qhead(0),
    m_steps_qhead(0) {    
    m_prefix = "seq.prefix.suffix";
    m_suffix = "seq.suffix.prefix";
    m_contains_left = "seq.contains.left";
    m_contains_right = "seq.contains.right";
    m_accept = "aut.accept";
    m_reject = "aut.reject";
    m_tail           = "seq.tail";
    m_nth            = "seq.nth";
    m_seq_first      = "seq.first";
    m_seq_last       = "seq.last";
    m_indexof_left   = "seq.indexof.left";
    m_indexof_right  = "seq.indexof.right";
    m_aut_step       = "aut.step";
    m_extract_prefix = "seq.extract.prefix";
    m_at_left        = "seq.at.left";
    m_at_right       = "seq.at.right";
}

theory_seq::~theory_seq() {
    m_trail_stack.reset();
}


final_check_status theory_seq::final_check_eh() { 
    context & ctx   = get_context();
    TRACE("seq", display(tout););
    if (!check_ineqs()) {
        TRACE("seq", tout << ">>check_ineqs\n";);
        return FC_CONTINUE;
    }
    if (simplify_and_solve_eqs()) {
        TRACE("seq", tout << ">>solve_eqs\n";);
        return FC_CONTINUE;
    }
    if (solve_nqs()) {
        TRACE("seq", tout << ">>solve_nqs\n";);
        return FC_CONTINUE;
    }
    if (branch_variable()) {
        TRACE("seq", tout << ">>branch_variable\n";);
        return FC_CONTINUE;
    }
    if (!check_length_coherence()) {
        TRACE("seq", tout << ">>check_length_coherence\n";);
        return FC_CONTINUE;
    }
    if (propagate_automata()) {
        TRACE("seq", tout << ">>propagate_automata\n";);
        return FC_CONTINUE;
    }
    if (is_solved()) {
        TRACE("seq", tout << ">>is_solved\n";);
        return FC_DONE;
    }

    return FC_GIVEUP;
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
        else if (!m.is_false(b)) {
            TRACE("seq", tout << "Disequality is undetermined: " << mk_pp(a, m) << " " << b << "\n";);
        }
    }
    return true;
}

bool theory_seq::branch_variable() {
    context& ctx = get_context();
    unsigned sz = m_eqs.size();
    expr_ref_vector ls(m), rs(m);
    for (unsigned i = 0; i < sz; ++i) {
        unsigned k = (i + m_branch_variable_head) % sz;
        eq e = m_eqs[k];
        TRACE("seq", tout << e.m_lhs << " = " << e.m_rhs << "\n";);
        ls.reset(); rs.reset();
        m_util.str.get_concat(e.m_lhs, ls);
        m_util.str.get_concat(e.m_rhs, rs);
        
        if (!ls.empty() && find_branch_candidate(ls[0].get(), rs)) {
            m_branch_variable_head = k;
            return true;
        }
        if (!rs.empty() && find_branch_candidate(rs[0].get(), ls)) {
            m_branch_variable_head = k;
            return true;
        }
    }
    return ctx.inconsistent();
}

bool theory_seq::find_branch_candidate(expr* l, expr_ref_vector const& rs) {

    TRACE("seq", tout << mk_pp(l, m) << " " 
          << (is_var(l)?"var":"not var") << "\n";);

    if (!is_var(l)) {
        return false;
    }

    expr_ref v0(m), v(m);
    v0 = m_util.str.mk_empty(m.get_sort(l));
    if (assume_equality(l, v0)) {
        return true;
    }
    for (unsigned j = 0; j < rs.size(); ++j) {
        if (occurs(l, rs[j])) {
            return false;
        }
        zstring s;
        if (m_util.str.is_string(rs[j], s)) {
            for (unsigned k = 1; k < s.length(); ++k) {
                v = m_util.str.mk_string(s.extract(0, k));
                if (v0) v = m_util.str.mk_concat(v0, v);
                if (assume_equality(l, v)) {
                    return true;
                }
            }
        }
        v0 = (j == 0)? rs[0] : m_util.str.mk_concat(v0, rs[j]); 
        if (assume_equality(l, v0)) {
            return true;
        }
    }           
    return false;
}

bool theory_seq::assume_equality(expr* l, expr* r) {
    context& ctx = get_context();
    if (m_exclude.contains(l, r)) {
        return false;
    }
    else {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << "\n";);
        enode* n1 = ensure_enode(l);
        enode* n2 = ensure_enode(r);
        ctx.mark_as_relevant(n1);
        ctx.mark_as_relevant(n2);
        ctx.assume_eq(n1, n2);
        return true;
    }
}

bool theory_seq::propagate_length_coherence(expr* e) {
    expr_ref head(m), tail(m), emp(m);
    rational lo, hi;
    TRACE("seq", tout << "Unsolved " << mk_pp(e, m);
          if (!lower_bound(e, lo)) lo = -rational::one();
          if (!upper_bound(e, hi)) hi = -rational::one();
          tout << " lo: " << lo << " hi: " << hi << "\n";
          );

    if (!lower_bound(e, lo) || !lo.is_pos() || lo >= rational(2048)) {
        return false;
    }
    literal low(mk_literal(m_autil.mk_ge(m_util.str.mk_length(e), m_autil.mk_numeral(lo, true))));
    expr_ref seq(e, m);
    expr_ref_vector elems(m);
    unsigned _lo = lo.get_unsigned();
    for (unsigned j = 0; j < _lo; ++j) {
        mk_decompose(seq, emp, head, tail);
        elems.push_back(head);
        seq = tail;
    }
    elems.push_back(seq);
    tail = m_util.str.mk_concat(elems.size(), elems.c_ptr());
    // len(e) >= low => e = tail
    add_axiom(~low, mk_eq(e, tail, false));
    assume_equality(tail, e);
    if (upper_bound(e, hi)) {
        expr_ref high1(m_autil.mk_le(m_util.str.mk_length(e), m_autil.mk_numeral(hi, true)), m);                    
        expr_ref high2(m_autil.mk_le(m_util.str.mk_length(seq), m_autil.mk_numeral(hi-lo, true)), m);                    
        add_axiom(~mk_literal(high1), mk_literal(high2));
    }
    return true;
}

bool theory_seq::check_length_coherence() {
    if (m_length.empty()) return true;
    context& ctx = get_context();
    bool coherent = true;
    obj_hashtable<expr>::iterator it = m_length.begin(), end = m_length.end();
    for (; it != end; ++it) {
        expr* e = *it;
        if (is_var(e) && m_rep.is_root(e)) {
            expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
            expr_ref head(m), tail(m);
                                              
            if (propagate_length_coherence(e)) {
                //m_replay_length_coherence.push_back(e);
                //m_replay_length_coherence_qhead = m_replay_length_coherence.size();
            }
            else if (!assume_equality(e, emp)) {
                mk_decompose(e, emp, head, tail);
                // e = emp \/ e = unit(head.elem(e))*tail(e)
                expr_ref conc(m_util.str.mk_concat(head, tail), m);
                add_axiom(mk_eq(e, emp, false), mk_eq(e, conc, false));
                assume_equality(tail, emp);
            }
            return false;
        }
    }
    return coherent;
}    

expr_ref theory_seq::mk_nth(expr* s, expr* idx) {
    sort* char_sort = 0;
    VERIFY(m_util.is_seq(m.get_sort(s), char_sort));
    return mk_skolem(m_nth, s, idx, 0, char_sort);
}

void theory_seq::mk_decompose(expr* e, expr_ref& emp, expr_ref& head, expr_ref& tail) {
    expr* e1, *e2;
    zstring s;
    emp  = m_util.str.mk_empty(m.get_sort(e));
    if (m_util.str.is_empty(e)) {
        head = m_util.str.mk_unit(mk_nth(e, m_autil.mk_int(0)));
        tail = e;
    }
    else if (m_util.str.is_string(e, s)) {
        head = m_util.str.mk_unit(m_util.str.mk_char(s, 0));
        tail = m_util.str.mk_string(s.extract(1, s.length()-1));
    }
    else if (m_util.str.is_unit(e)) {
        head = e;
        tail = emp;
    }
    else if (m_util.str.is_concat(e, e1, e2) && m_util.str.is_unit(e1)) {
        head = e1;
        tail = e2;
    }
    else if (is_skolem(m_tail, e)) {
        rational r;
        app* a = to_app(e);
        expr* s = a->get_arg(0);
        VERIFY (m_autil.is_numeral(a->get_arg(1), r));
        expr* idx = m_autil.mk_int(r.get_unsigned() + 1);
        head = m_util.str.mk_unit(mk_nth(s, idx));
        tail = mk_skolem(m_tail, s, idx);
    }
    else {
        head = m_util.str.mk_unit(mk_nth(e, m_autil.mk_int(0)));
        tail = mk_skolem(m_tail, e, m_autil.mk_int(0));
    } 
}

bool theory_seq::check_ineq_coherence() {
    bool all_false = true;
    for (unsigned i = 0; all_false && i < m_ineqs.size(); ++i) {
        expr* a = m_ineqs[i].get();
        enode_pair_dependency* eqs = 0;
        expr_ref b = canonize(a, eqs);
        all_false = m.is_false(b);
        if (all_false) {
            TRACE("seq", tout << "equality is undetermined: " << mk_pp(a, m) << " " << b << "\n";);
        }
    }
    return all_false;
}

/*
   - Eqs = 0
   - Diseqs evaluate to false
   - lengths are coherent.
*/

bool theory_seq::is_solved() {
    if (!m_eqs.empty()) {
        return false;
    }
    if (!check_ineq_coherence()) {
        return false;
    }
    for (unsigned i = 0; i < m_automata.size(); ++i) {
        if (!m_automata[i]) return false;
    }
    
    return true;

}

void theory_seq::propagate_lit(enode_pair_dependency* dep, unsigned n, literal const* lits, literal lit) {
    context& ctx = get_context();
    ctx.mark_as_relevant(lit);
    vector<enode_pair, false> _eqs;
    m_dm.linearize(dep, _eqs);
    TRACE("seq", ctx.display_detailed_literal(tout, lit); 
          tout << " <- "; ctx.display_literals_verbose(tout, n, lits); display_deps(tout, dep);); 
    justification* js = 
        ctx.mk_justification(
            ext_theory_propagation_justification(
                get_id(), ctx.get_region(), n, lits, _eqs.size(), _eqs.c_ptr(), lit));

    ctx.assign(lit, js);
}

void theory_seq::set_conflict(enode_pair_dependency* dep, literal_vector const& lits) {
    context& ctx = get_context();
    vector<enode_pair, false> _eqs;
    m_dm.linearize(dep, _eqs);
    TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); display_deps(tout, dep); ;); 
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), _eqs.size(), _eqs.c_ptr(), 0, 0)));
}

void theory_seq::propagate_eq(enode_pair_dependency* dep, enode* n1, enode* n2) {
    context& ctx = get_context();
    vector<enode_pair, false> _eqs;
    m_dm.linearize(dep, _eqs);
    TRACE("seq",
          tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << " <- ";
          display_deps(tout, dep);
          ); 
    
    justification* js = ctx.mk_justification(
        ext_theory_eq_propagation_justification(
            get_id(), ctx.get_region(), 0, 0, _eqs.size(), _eqs.c_ptr(), n1, n2));
    ctx.assign_eq(n1, n2, eq_justification(js));
}



bool theory_seq::simplify_eq(expr* l, expr* r, enode_pair_dependency* deps, bool& propagated) {
    context& ctx = get_context();
    seq_rewriter rw(m);
    expr_ref_vector lhs(m), rhs(m);
    expr_ref lh = canonize(l, deps);
    expr_ref rh = canonize(r, deps);
    if (!rw.reduce_eq(lh, rh, lhs, rhs)) {
        // equality is inconsistent.
        TRACE("seq", tout << lh << " != " << rh << "\n";);
        set_conflict(deps);
        propagated = true;
        return true;
    }
    if (unchanged(l, lhs) && unchanged(r, rhs)) {
        return false;
    }
    if (unchanged(r, lhs) && unchanged(l, rhs)) {
        return false;
    }
    SASSERT(lhs.size() == rhs.size());
    for (unsigned i = 0; i < lhs.size(); ++i) {
        expr_ref li(lhs[i].get(), m);
        expr_ref ri(rhs[i].get(), m);
        if (m_util.is_seq(li) || m_util.is_re(li)) {
            m_eqs.push_back(eq(li, ri, deps));
        }
        else {
            propagate_eq(deps, ensure_enode(li), ensure_enode(ri));
            propagated = true;
        }
    }        
    TRACE("seq",
          tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " => ";
          for (unsigned i = 0; i < lhs.size(); ++i) {
              tout << mk_pp(lhs[i].get(), m) << " = " << mk_pp(rhs[i].get(), m) << "; ";
          }
          tout << "\n";);
    return true;
}

bool theory_seq::solve_unit_eq(expr* l, expr* r, enode_pair_dependency* deps, bool& propagated) {
    expr_ref lh = canonize(l, deps);
    expr_ref rh = canonize(r, deps);
    if (lh == rh) {
        return true;
    }
    if (is_var(lh) && !occurs(lh, rh)) {
        propagated = add_solution(lh, rh, deps) || propagated;
        return true;
    }
    if (is_var(rh) && !occurs(rh, lh)) {
        propagated = add_solution(rh, lh, deps) || propagated;
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
    SASSERT(m_todo.empty());
    expr* e1, *e2;
    m_todo.push_back(b);
    while (!m_todo.empty()) {
        b = m_todo.back();
        if (a == b) {
            m_todo.reset();
            return true;
        }
        m_todo.pop_back();
        if (m_util.str.is_concat(b, e1, e2)) {
            m_todo.push_back(e1);
            m_todo.push_back(e2);
        }   
    }
    return false;
}

bool theory_seq::is_var(expr* a) {
    return 
        m_util.is_seq(a) &&
        !m_util.str.is_concat(a) && 
        !m_util.str.is_empty(a)  && 
        !m_util.str.is_string(a) && 
        !m_util.str.is_unit(a);
}


bool theory_seq::is_head_elem(expr* e) const {
    return is_skolem(m_nth, e);
}

bool theory_seq::add_solution(expr* l, expr* r, enode_pair_dependency* deps) {
    if (l == r) {
        return false;
    }
    context& ctx = get_context();
    TRACE("seq", tout << mk_pp(l, m) << " ==> " << mk_pp(r, m) << "\n";);
    m_rep.update(l, r, deps);
    // TBD: skip new equalities for non-internalized terms.
    if (ctx.e_internalized(l) && ctx.e_internalized(r) && ctx.get_enode(l)->get_root() != ctx.get_enode(r)->get_root()) {
        propagate_eq(deps, ctx.get_enode(l), ctx.get_enode(r));
        return true;
    }
    else {
        return false;
    }
}


bool theory_seq::pre_process_eqs(bool simplify_or_solve, bool& propagated) {
    context& ctx = get_context();
    bool change = false;
    for (unsigned i = 0; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        eq e = m_eqs[i];
        
        if (simplify_or_solve?
            simplify_eq(e.m_lhs, e.m_rhs, e.m_dep, propagated):
            solve_unit_eq(e.m_lhs, e.m_rhs, e.m_dep, propagated)) {
            if (i + 1 != m_eqs.size()) {
                eq e1 = m_eqs[m_eqs.size()-1];
                m_eqs.set(i, e1);
                --i;
                ++m_stats.m_num_reductions;
            }
            m_eqs.pop_back();
            change = true;
        }
    }    
    return change;
}

bool theory_seq::solve_nqs() {
    bool change = false;
    context & ctx = get_context();
    for (unsigned i = 0; !ctx.inconsistent() && i < m_nqs.size(); ++i) {
        if (!m_nqs[i].is_solved()) {
            change = solve_ne(i) || change;
        }
    }
    return change || ctx.inconsistent();
}

bool theory_seq::solve_ne(unsigned idx) {
    context& ctx = get_context();
    seq_rewriter rw(m);
    bool change = false;
    ne const& n = m_nqs[idx];
    TRACE("seq", display_disequation(tout, n););

    SASSERT(!n.is_solved());
    unsigned num_undef_lits = 0;
    for (unsigned i = 0; i < n.m_lits.size(); ++i) {
        switch (ctx.get_assignment(n.m_lits[i])) {
        case l_false:
            // mark as solved in 
            mark_solved(idx);
            return false;
        case l_true:
            break;            
        case l_undef:
            ++num_undef_lits;
            break;
        }
    }
    for (unsigned i = 0; i < n.m_lhs.size(); ++i) {
        expr_ref_vector lhs(m), rhs(m);
        enode_pair_dependency* deps = 0;
        expr* l = n.m_lhs[i];
        expr* r = n.m_rhs[i];
        expr_ref lh = canonize(l, deps);
        expr_ref rh = canonize(r, deps);
        if (!rw.reduce_eq(lh, rh, lhs, rhs)) {
            mark_solved(idx);
            return change;
        }
        else if (unchanged(l, lhs) && unchanged(r, rhs)) {
            // continue
        }
        else if (unchanged(r, lhs) && unchanged(l, rhs)) {
            // continue
        }
        else {
            TRACE("seq", 
                  for (unsigned j = 0; j < lhs.size(); ++j) {
                      tout << mk_pp(lhs[j].get(), m) << " ";
                  }
                  tout << "\n";
                  tout << mk_pp(l, m) << " != " << mk_pp(r, m) << "\n";);

            for (unsigned j = 0; j < lhs.size(); ++j) {
                expr_ref nl(lhs[j].get(), m);
                expr_ref nr(rhs[j].get(), m);
                if (m_util.is_seq(nl) || m_util.is_re(nl)) {
                    m_trail_stack.push(push_ne(*this, idx, nl, nr));
                }
                else {
                    literal lit(mk_eq(nl, nr, false));
                    m_trail_stack.push(push_lit(*this, idx, lit));
                    ctx.mark_as_relevant(lit);
                    switch (ctx.get_assignment(lit)) {
                    case l_false:
                        mark_solved(idx);
                        return false;
                    case l_true:
                        break;
                    case l_undef:
                        ++num_undef_lits;
                        break;
                    }
                }
            }                
            m_trail_stack.push(push_dep(*this, idx, deps));
            erase_index(idx, i);
            --i;
            change = true;
        }
    }
    if (num_undef_lits == 0 && n.m_lhs.empty()) {
        literal_vector lits(n.m_lits);
        lits.push_back(~mk_eq(n.m_l, n.m_r, false));
        set_conflict(n.m_dep, lits);
        return true;
    }
    return change;
}


void theory_seq::mark_solved(unsigned idx) {
    m_trail_stack.push(solved_ne(*this, idx));
}

void theory_seq::erase_index(unsigned idx, unsigned i) {
    ne const& n = m_nqs[idx];   
    unsigned sz = n.m_lhs.size();
    if (i + 1 != sz) {
        m_trail_stack.push(set_ne(*this, idx, i, n.m_lhs[sz-1], n.m_rhs[sz-1]));
    }
    m_trail_stack.push(pop_ne(*this, idx));
}

bool theory_seq::simplify_and_solve_eqs() {
    context & ctx = get_context();
    bool propagated = false;
    simplify_eqs(propagated);
    while (!ctx.inconsistent() && solve_basic_eqs(propagated)) {
        simplify_eqs(propagated);
    }
    return propagated || ctx.inconsistent();
}


bool theory_seq::internalize_term(app* term) { 
    TRACE("seq", tout << mk_pp(term, m) << "\n";);
    context & ctx   = get_context();
    unsigned num_args = term->get_num_args();
    expr* arg;
    for (unsigned i = 0; i < num_args; i++) {
        arg = term->get_arg(i);
        mk_var(ensure_enode(arg));
    }
    if (m.is_bool(term)) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
    }
    else {
        enode* e = 0;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        }
        else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        } 
        mk_var(e);
    }
    return true;
}

void theory_seq::add_length(expr* e) {
    SASSERT(!has_length(e));
    m_length.insert(e);
    m_trail_stack.push(insert_obj_trail<theory_seq, expr>(m_length, e));
}

/*
  ensure that all elements in equivalence class occur under an applicatin of 'length'
*/
void theory_seq::enforce_length(enode* n) {
    enode* n1 = n;
    do {
        expr* o = n->get_owner();
        if (!has_length(o)) {
            expr_ref len(m_util.str.mk_length(o), m);
            enque_axiom(len);
            add_length(o);
        }
        n = n->get_next();
    }
    while (n1 != n);
}

void theory_seq::apply_sort_cnstr(enode* n, sort* s) {
    mk_var(n);    
}

void theory_seq::display(std::ostream & out) const {
    if (m_eqs.size() == 0 &&
        m_nqs.size() == 0 && 
        m_ineqs.empty() &&
        m_rep.empty() && 
        m_exclude.empty()) {
        return;
    }
    out << "Theory seq\n";
    if (m_eqs.size() > 0) {
        out << "Equations:\n";
        display_equations(out);
    }
    if (m_nqs.size() > 0) {
        out << "Disequations:\n";
        display_disequations(out);
    }
    if (!m_ineqs.empty()) {
        out << "Negative constraints:\n";
        for (unsigned i = 0; i < m_ineqs.size(); ++i) {
            out << mk_pp(m_ineqs[i], m) << "\n";
        }
    }
    if (!m_re2aut.empty()) {
        out << "Regex\n";
        obj_map<expr, eautomaton*>::iterator it = m_re2aut.begin(), end = m_re2aut.end();
        for (; it != end; ++it) {
            out << mk_pp(it->m_key, m) << "\n";
            display_expr disp(m);
            it->m_value->display(out, disp);
        }
    }
    if (!m_rep.empty()) {
        out << "Solved equations:\n";
        m_rep.display(out);
    }
    if (!m_exclude.empty()) {
        out << "Exclusions:\n";
        m_exclude.display(out);
    }
}

void theory_seq::display_equations(std::ostream& out) const {
    for (unsigned i = 0; i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[i];
        out << e.m_lhs << " = " << e.m_rhs << " <- ";
        display_deps(out, e.m_dep);
    }       
}

void theory_seq::display_disequations(std::ostream& out) const {
    for (unsigned i = 0; i < m_nqs.size(); ++i) {
        display_disequation(out, m_nqs[i]);
    }       
}

void theory_seq::display_disequation(std::ostream& out, ne const& e) const {
    for (unsigned j = 0; j < e.m_lits.size(); ++j) {
        out << e.m_lits[j] << " ";
    }
    if (e.m_lits.size() > 0) {
        out << "\n";
    }
    for (unsigned j = 0; j < e.m_lhs.size(); ++j) {
        out << mk_pp(e.m_lhs[j], m) << " != " << mk_pp(e.m_rhs[j], m) << "\n";
    }
    display_deps(out, e.m_dep);        
}

void theory_seq::display_deps(std::ostream& out, enode_pair_dependency* dep) const {
    vector<enode_pair, false> _eqs;
    const_cast<enode_pair_dependency_manager&>(m_dm).linearize(dep, _eqs);
    for (unsigned i = 0; i < _eqs.size(); ++i) {
        out << " " << mk_pp(_eqs[i].first->get_owner(), m) << " = " << mk_pp(_eqs[i].second->get_owner(), m);
    }
    out << "\n";
}

void theory_seq::collect_statistics(::statistics & st) const {
    st.update("seq num splits", m_stats.m_num_splits);
    st.update("seq num reductions", m_stats.m_num_reductions);
}

void theory_seq::init_model(model_generator & mg) {
    m_factory = alloc(seq_factory, get_manager(), get_family_id(), mg.get_model());
    mg.register_factory(m_factory);
}


class seq_value_proc : public model_value_proc {
    theory_seq& th;
    app* n;
    svector<model_value_dependency> m_dependencies;
public:
    seq_value_proc(theory_seq& th, app* n): th(th), n(n) {
    }
    virtual ~seq_value_proc() {}
    void add_dependency(enode* n) { m_dependencies.push_back(model_value_dependency(n)); }
    virtual void get_dependencies(buffer<model_value_dependency> & result) {
        result.append(m_dependencies.size(), m_dependencies.c_ptr());
    }
    virtual app * mk_value(model_generator & mg, ptr_vector<expr> & values) {
        SASSERT(values.size() == m_dependencies.size());
        ast_manager& m = mg.get_manager();
        if (values.empty()) {
            return th.mk_value(n);
        }
        SASSERT(values.size() == n->get_num_args());
        return th.mk_value(mg.get_manager().mk_app(n->get_decl(), values.size(), values.c_ptr()));
    }    
};


model_value_proc * theory_seq::mk_value(enode * n, model_generator & mg) {
    context& ctx = get_context();
    enode_pair_dependency* dep = 0;
    expr* e = m_rep.find(n->get_owner(), dep);    
    expr* e1, *e2;
    seq_value_proc* sv = alloc(seq_value_proc, *this, to_app(e));
    if (m_util.str.is_concat(e, e1, e2)) {
        sv->add_dependency(ctx.get_enode(e1));
        sv->add_dependency(ctx.get_enode(e2));
    }
    else if (m_util.str.is_unit(e, e1)) {
        sv->add_dependency(ctx.get_enode(e1));
    }                          
    return sv;
}

app* theory_seq::mk_value(app* e) {
    expr* e1;
    expr_ref result(e, m);
    if (m_util.str.is_unit(e, e1)) {
        enode_pair_dependency* deps = 0;
        result = expand(e1, deps);
        bv_util bv(m);
        rational val;
        unsigned sz;
        if (bv.is_numeral(result, val, sz) && sz == zstring().num_bits()) {
            svector<bool> val_as_bits;
            for (unsigned i = 0; i < sz; ++i) {
                val_as_bits.push_back(!val.is_even());
                val = div(val, rational(2));
            }
            result = m_util.str.mk_string(zstring(sz, val_as_bits.c_ptr()));
        }
        else {
            result = m_util.str.mk_unit(result);
        }
    }
    else if (is_var(e)) {
        SASSERT(m_factory);
        expr_ref val(m);
        val = m_factory->get_some_value(m.get_sort(e));
        if (val) {
            result = val;
        }
        else {
            result = e;
        }
    }
    else if (is_head_elem(e)) {
        enode* n = get_context().get_enode(e)->get_root();
        enode* n0 = n;
        bool found_value = false;
        do {
            result = n->get_owner();
            found_value = m.is_model_value(result);
        }
        while (n0 != n && !found_value);

        if (!found_value) {
            if (m_util.is_char(result)) {
                result = m_util.str.mk_char('#');
            }
            else {
                result = m_mg->get_some_value(m.get_sort(result));
            }
        }
    }
    m_rewrite(result);
    m_factory->add_trail(result);
    TRACE("seq", tout << mk_pp(e, m) << " -> " << result << "\n";);
    return to_app(result);
}


theory_var theory_seq::mk_var(enode* n) {
    if (!m_util.is_seq(n->get_owner()) &&
        !m_util.is_re(n->get_owner())) {
        return null_theory_var;
    }
    if (is_attached_to_var(n)) {
        return n->get_th_var(get_id());
    }
    else {
        theory_var v = theory::mk_var(n);
        get_context().attach_th_var(n, this, v);
        get_context().mark_as_relevant(n);
        return v;
    }
}

bool theory_seq::can_propagate() {
    return m_axioms_head < m_axioms.size();
}

expr_ref theory_seq::canonize(expr* e, enode_pair_dependency*& eqs) {
    expr_ref result = expand(e, eqs);
    m_rewrite(result);
    return result;
}

expr_ref theory_seq::expand(expr* e0, enode_pair_dependency*& eqs) {
    expr_ref result(m);
    enode_pair_dependency* deps = 0;
    expr_dep ed;
    if (m_rep.find_cache(e0, ed)) {
        eqs = m_dm.mk_join(eqs, ed.second);
        result = ed.first;
        return result;
    }
    expr* e = m_rep.find(e0, deps);
    expr* e1, *e2;
    if (m_util.str.is_concat(e, e1, e2)) {
        result = m_util.str.mk_concat(expand(e1, deps), expand(e2, deps));
    }        
    else if (m_util.str.is_empty(e) || m_util.str.is_string(e)) {
        result = e;
    }
    else if (m_util.str.is_prefix(e, e1, e2)) {
        result = m_util.str.mk_prefix(expand(e1, deps), expand(e2, deps));
    }
    else if (m_util.str.is_suffix(e, e1, e2)) {
        result = m_util.str.mk_suffix(expand(e1, deps), expand(e2, deps));
    }
    else if (m_util.str.is_contains(e, e1, e2)) {
        result = m_util.str.mk_contains(expand(e1, deps), expand(e2, deps));
    }
    else {
        result = e;
    }
    if (result == e0) {
        deps = 0;
    }
    expr_dep edr(result, deps);
    m_rep.add_cache(e0, edr);
    eqs = m_dm.mk_join(eqs, deps);
    TRACE("seq_verbose", tout << mk_pp(e0, m) << " |--> " << result << "\n";
          display_deps(tout, eqs););
    return result;
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
        deque_axiom(e);
        ++m_axioms_head;
    }
}

void theory_seq::enque_axiom(expr* e) {
    TRACE("seq", tout << "add axioms for: " << mk_pp(e, m) << "\n";);
    if (!m_axiom_set.contains(e)) {
        m_axioms.push_back(e);
        m_axiom_set.insert(e);
        m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_axioms));
        m_trail_stack.push(insert_obj_trail<theory_seq, expr>(m_axiom_set, e));;

    }
}

void theory_seq::deque_axiom(expr* n) {
    if (m_util.str.is_length(n)) {        
        add_length_axiom(n);
    }
    else if (m_util.str.is_index(n)) {
        add_indexof_axiom(n);
    }
    else if (m_util.str.is_replace(n)) {
        add_replace_axiom(n);
    }
    else if (m_util.str.is_extract(n)) {
        add_extract_axiom(n);
    }
    else if (m_util.str.is_at(n)) {
        add_at_axiom(n);
    }
    else if (m_util.str.is_string(n)) {
        add_elim_string_axiom(n);
    }
}


/*
  encode that s is not a proper prefix of xs1
  where s1 is all of s, except the last element.
  
  lit or s = "" or s = s1*c
  lit or s = "" or len(c) = 1
  lit or s = "" or !prefix(s, x*s1)
*/
void theory_seq::tightest_prefix(expr* s, expr* x, literal lit1, literal lit2) {
    expr_ref s1 = mk_skolem(m_seq_first, s);
    expr_ref c  = mk_skolem(m_seq_last,  s);
    expr_ref s1c(m_util.str.mk_concat(s1, c), m);
    expr_ref lc(m_util.str.mk_length(c), m);
    expr_ref one(m_autil.mk_int(1), m);
    expr_ref emp(m_util.str.mk_empty(m.get_sort(s)), m);
    literal s_eq_emp = mk_eq(s, emp, false);
    add_axiom(lit1, lit2, s_eq_emp, mk_eq(s, s1c, false));
    add_axiom(lit1, lit2, s_eq_emp, mk_eq(lc, one, false));
    add_axiom(lit1, lit2, s_eq_emp, ~mk_literal(m_util.str.mk_contains(s, m_util.str.mk_concat(x, s1))));
}

/*
  // index of s in t starting at offset.

  let i = Index(t, s, 0):
  
  len(t) = 0  => i = -1
  len(t) != 0 & !contains(t, s) => i = -1
  len(t) != 0 & contains(t, s) => t = xsy & i = len(x)
  len(t) != 0 & contains(t, s) & s != emp => tightest_prefix(x, s)

  let i = Index(t, s, offset)


  0 <= offset < len(t) => xy = t & len(x) = offset & (-1 = indexof(t, s, 0) => -1 = i)
                                                   & (indexof(t, s, 0) >= 0 => indexof(t, s, 0) + offset = i)
  

  offset = len(t) => i = -1
  
  if offset < 0 or offset >= len(t)
     under specified

  optional lemmas:
  (len(s) > len(t)  -> i = -1) 
  (len(s) <= len(t) -> i <= len(t)-len(s))  
*/
void theory_seq::add_indexof_axiom(expr* i) {
    expr* s, *t, *offset;
    rational r;
    VERIFY(m_util.str.is_index(i, t, s, offset));
    expr_ref emp(m), minus_one(m), zero(m), xsy(m);
    minus_one   = m_autil.mk_int(-1);
    zero        = m_autil.mk_int(0);
    emp         = m_util.str.mk_empty(m.get_sort(s));
    literal offset_ne_zero = null_literal;
    bool is_num = m_autil.is_numeral(offset, r); 
    if (is_num && r.is_zero()) {
        offset_ne_zero = null_literal;
    }
    else {
        offset_ne_zero = ~mk_eq(offset, zero, false);
    }
    if (!is_num || r.is_zero()) {
        expr_ref x  = mk_skolem(m_contains_left, t, s);
        expr_ref y  = mk_skolem(m_contains_right, t, s);    
        xsy         = m_util.str.mk_concat(x,s,y);
        literal cnt = mk_literal(m_util.str.mk_contains(t, s));
        literal eq_empty = mk_eq(s, emp, false);
        add_axiom(offset_ne_zero, cnt,  mk_eq(i, minus_one, false));
        add_axiom(offset_ne_zero, ~eq_empty, mk_eq(i, zero, false));
        add_axiom(offset_ne_zero, ~cnt, eq_empty, mk_eq(t, xsy, false));
        tightest_prefix(s, x, ~cnt, offset_ne_zero);
    }
    if (is_num && r.is_zero()) {
        return;
    }
    // offset >= len(t) => indexof(s, t, offset) = -1
    expr_ref len_t(m_util.str.mk_length(t), m);
    literal offset_ge_len = mk_literal(m_autil.mk_ge(mk_sub(offset, len_t), zero));
    add_axiom(offset_ge_len, mk_eq(i, minus_one, false));

    // 0 <= offset & offset < len(t) => t = xy
    // 0 <= offset & offset < len(t) => len(x) = offset
    // 0 <= offset & offset < len(t) & ~contains(s, y) => indexof(t, s, offset) = -1
	// 0 <= offset & offset < len(t) & contains(s, y) => index(t, s, offset) = indexof(y, s, 0) + len(t) 
    expr_ref x = mk_skolem(m_indexof_left, t, s, offset);
    expr_ref y = mk_skolem(m_indexof_right, t, s, offset);
    expr_ref indexof(m_util.str.mk_index(y, s, zero), m);
	// TBD:
    //literal offset_ge_0 = mk_literal(m_autil.mk_ge(offset, zero));
    //add_axiom(~offset_ge_0, offset_ge_len, mk_eq(indexof, i, false));
    //add_axiom(~offset_ge_0, offset_ge_len, mk_eq(m_util.str.mk_length(x), offset, false));
    //add_axiom(~offset_ge_0, offset_ge_len, mk_eq(t, m_util.str.mk_concat(x, y), false));
}

/*
  let r = replace(a, s, t)
  
  (contains(a, s) -> tightest_prefix(s,xs))
  (contains(a, s) -> r = xty & a = xsy) & 
  (!contains(a, s) -> r = a)
   
*/
void theory_seq::add_replace_axiom(expr* r) {
    expr* a, *s, *t;
    VERIFY(m_util.str.is_replace(r, a, s, t));
    expr_ref x  = mk_skolem(m_contains_left, a, s);
    expr_ref y  = mk_skolem(m_contains_right, a, s);    
    expr_ref xty(m_util.str.mk_concat(x, t, y), m);
    expr_ref xsy(m_util.str.mk_concat(x, s, y), m);
    literal cnt = mk_literal(m_util.str.mk_contains(a ,s));
    add_axiom(cnt,  mk_eq(r, a, false));
    add_axiom(~cnt, mk_eq(a, xsy, false));
    add_axiom(~cnt, mk_eq(r, xty, false));
    tightest_prefix(s, x, ~cnt);
}

void theory_seq::add_elim_string_axiom(expr* n) {
    zstring s;
    VERIFY(m_util.str.is_string(n, s));
    if (s.length() == 0) {
        return;
    }
    expr_ref result(m_util.str.mk_unit(m_util.str.mk_char(s, s.length()-1)), m);
    for (unsigned i = s.length()-1; i > 0; ) {
        --i;
        result = m_util.str.mk_concat(m_util.str.mk_unit(m_util.str.mk_char(s, i)), result);
    }
    add_axiom(mk_eq(n, result, false));
    m_rep.update(n, result, 0);
}


/*
    let n = len(x)

    len(x) >= 0
    len(x) = 0 => x = ""
    x = "" => len(x) = 0
 */
void theory_seq::add_length_axiom(expr* n) {
    expr* x;
    VERIFY(m_util.str.is_length(n, x));
    if (m_util.str.is_concat(x) ||
        m_util.str.is_unit(x) ||
        m_util.str.is_empty(x) ||
        m_util.str.is_string(x)) {
        expr_ref len(n, m);
        m_rewrite(len);
        if (n != len) {
            TRACE("seq", tout << "Add length coherence for " << mk_pp(n, m) << "\n";);
            add_axiom(mk_eq(n, len, false));
        }
    }
    else {
        expr_ref zero(m_autil.mk_int(0), m);
        expr_ref emp(m_util.str.mk_empty(m.get_sort(x)), m);
        literal eq1(mk_eq(zero, n, false));
        literal eq2(mk_eq(x, emp, false));
        add_axiom(mk_literal(m_autil.mk_ge(n, zero)));
        add_axiom(~eq1, eq2);
        add_axiom(~eq2, eq1);
    }
}



void theory_seq::propagate_in_re(expr* n, bool is_true) {
    TRACE("seq", tout << mk_pp(n, m) << " <- " << (is_true?"true":"false") << "\n";);
    expr* e1, *e2;
    VERIFY(m_util.str.is_in_re(n, e1, e2));

    expr_ref tmp(n, m);
    m_rewrite(tmp);
    if (m.is_true(tmp)) {
        if (!is_true) {
            literal_vector lits;
            lits.push_back(mk_literal(n));
            set_conflict(0, lits);
        }
        return;
    }
    else if (m.is_false(tmp)) {
        if (is_true) {
            literal_vector lits;
            lits.push_back(~mk_literal(n));
            set_conflict(0, lits);
        }
        return;
    }

    eautomaton* a = get_automaton(e2);
    if (!a) return;
    // if (m_util.str.is_empty(e1)) return;

    context& ctx = get_context();

    expr_ref len(m_util.str.mk_length(e1), m);
    for (unsigned i = 0; i < a->num_states(); ++i) {
        literal acc = mk_accept(e1, len, e2, i);
        literal rej = mk_reject(e1, len, e2, i);
        add_axiom(a->is_final_state(i)?acc:~acc);
        add_axiom(a->is_final_state(i)?~rej:rej);
    }

    expr_ref zero(m_autil.mk_int(0), m);
    unsigned_vector states;
    a->get_epsilon_closure(a->init(), states);
    literal_vector lits;
    literal lit = ctx.get_literal(n);
    if (is_true) {
        lits.push_back(~lit);
    }
    for (unsigned i = 0; i < states.size(); ++i) {
        if (is_true) {
            lits.push_back(mk_accept(e1, zero, e2, states[i]));
        }
        else {
            literal nlit = ~lit;
            propagate_lit(0, 1, &nlit, mk_reject(e1, zero, e2, states[i]));
        }
    }
    if (is_true) {
        if (lits.size() == 2) {
            propagate_lit(0, 1, &lit, lits[1]);
        }
        else {
            TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        }
    }
}


expr_ref theory_seq::mk_sub(expr* a, expr* b) {
    expr_ref result(m_autil.mk_sub(a, b), m);
    m_rewrite(result);
    return result;
}

enode* theory_seq::ensure_enode(expr* e) {
    context& ctx = get_context();
    if (!ctx.e_internalized(e)) {
        ctx.internalize(e, false);
        ctx.mark_as_relevant(ctx.get_enode(e));
    }
    return ctx.get_enode(e);
}

static theory_mi_arith* get_th_arith(context& ctx, theory_id afid, expr* e) {
    ast_manager& m = ctx.get_manager();
    theory* th = ctx.get_theory(afid);
    if (th && ctx.e_internalized(e)) {
        return dynamic_cast<theory_mi_arith*>(th);
    }
    else {
        return 0;
    }
}

bool theory_seq::lower_bound(expr* _e, rational& lo) {
    context& ctx = get_context();
    expr_ref e(m_util.str.mk_length(_e), m);
    theory_mi_arith* tha = get_th_arith(ctx, m_autil.get_family_id(), e);
    expr_ref _lo(m);
    if (!tha || !tha->get_lower(ctx.get_enode(e), _lo)) return false;
    return m_autil.is_numeral(_lo, lo) && lo.is_int();
}

bool theory_seq::upper_bound(expr* _e, rational& hi) {
    context& ctx = get_context();
    expr_ref e(m_util.str.mk_length(_e), m);
    theory_mi_arith* tha = get_th_arith(ctx, m_autil.get_family_id(), e);
    expr_ref _hi(m);
    if (!tha || !tha->get_upper(ctx.get_enode(e), _hi)) return false;
    return m_autil.is_numeral(_hi, hi) && hi.is_int();
}

bool theory_seq::get_length(expr* e, rational& val) {
    context& ctx = get_context();
    theory* th = ctx.get_theory(m_autil.get_family_id());
    if (!th) return false;
    theory_mi_arith* tha = dynamic_cast<theory_mi_arith*>(th);
    if (!tha) return false;
    rational val1;
    expr_ref len(m), len_val(m);
    expr* e1, *e2;
    ptr_vector<expr> todo;
    todo.push_back(e);
    val.reset();
    zstring s;
    while (!todo.empty()) {
        expr* c = todo.back();
        todo.pop_back();
        if (m_util.str.is_concat(c, e1, e2)) {
            todo.push_back(e1);
            todo.push_back(e2);
        }
        else if (m_util.str.is_unit(c)) {
            val += rational(1);
        }
        else if (m_util.str.is_empty(c)) {
            continue;
        }
        else if (m_util.str.is_string(c, s)) {
            val += rational(s.length());
        }
        else {
            len = m_util.str.mk_length(c);
            if (ctx.e_internalized(len) &&
                tha->get_value(ctx.get_enode(len), len_val) &&
                m_autil.is_numeral(len_val, val1)) {
                val += val1;
            }
            else {
                TRACE("seq", tout << "No length provided for " << len << "\n";);
                return false;
            }
        }
    }
    return val.is_int();
}

/*
  TBD: check semantics of extract.

  let e = extract(s, i, l)

  0 <= i < len(s) -> prefix(xe,s) & len(x) = i
  0 <= i < len(s) & l >= len(s) - i -> len(e) = len(s) - i
  0 <= i < len(s) & 0 <= l < len(s) - i -> len(e) = l
  0 <= i < len(s) & l < 0 -> len(e) = 0
  *  i < 0 -> e = s
  *  i >= len(s) -> e = empty
*/

void theory_seq::add_extract_axiom(expr* e) {
    expr* s, *i, *l;
    VERIFY(m_util.str.is_extract(e, s, i, l));
    expr_ref x(mk_skolem(m_extract_prefix, s, e), m);
    expr_ref ls(m_util.str.mk_length(s), m);
    expr_ref lx(m_util.str.mk_length(x), m);
    expr_ref le(m_util.str.mk_length(e), m);
    expr_ref ls_minus_i(mk_sub(ls, i), m);
    expr_ref xe(m_util.str.mk_concat(x, e), m);
    expr_ref zero(m_autil.mk_int(0), m);
    
    literal i_ge_0  = mk_literal(m_autil.mk_ge(i, zero));
    literal i_ge_ls = mk_literal(m_autil.mk_ge(mk_sub(i, ls), zero));
    literal l_ge_ls = mk_literal(m_autil.mk_ge(mk_sub(l, ls), zero));
    literal l_ge_zero = mk_literal(m_autil.mk_ge(l, zero));

    add_axiom(~i_ge_0, i_ge_ls, mk_literal(m_util.str.mk_prefix(xe, s)));
    add_axiom(~i_ge_0, i_ge_ls, mk_eq(lx, i, false));
    add_axiom(~i_ge_0, i_ge_ls, ~l_ge_ls, mk_eq(le, ls_minus_i, false));
    add_axiom(~i_ge_0, i_ge_ls, l_ge_zero, mk_eq(le, zero, false));    
}

/*
   let e = at(s, i)
   
   0 <= i < len(s) -> s = xey & len(x) = i & len(e) = 1
   
*/
void theory_seq::add_at_axiom(expr* e) {
    expr* s, *i;
    VERIFY(m_util.str.is_at(e, s, i));
    expr_ref x(m), y(m), lx(m), le(m), xey(m), zero(m), one(m), len_e(m), len_x(m);
    x     = mk_skolem(m_at_left, s);
    y     = mk_skolem(m_at_right, s);
    xey   = m_util.str.mk_concat(x, e, y);
    zero  = m_autil.mk_int(0);
    one   = m_autil.mk_int(1);
    len_e = m_util.str.mk_length(e);
    len_x = m_util.str.mk_length(x);

    literal i_ge_0 = mk_literal(m_autil.mk_ge(i, zero));
    literal i_ge_len_s = mk_literal(m_autil.mk_ge(mk_sub(i, m_util.str.mk_length(s)), zero));

    add_axiom(~i_ge_0, i_ge_len_s, mk_eq(s, xey, false));
    add_axiom(~i_ge_0, i_ge_len_s, mk_eq(one, len_e, false));
    add_axiom(~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false));
}

/**
   step(s, idx, re, i, j, t) -> nth(s, idx) == t
*/
void theory_seq::propagate_step(bool_var v, expr* step) {
    context& ctx = get_context();
    expr* re, *t, *s, *idx, *i, *j;
    VERIFY(is_step(step, s, idx, re, i, j, t));
    expr_ref nth = mk_nth(s, idx);
    propagate_eq(v, t, nth);
}


literal theory_seq::mk_literal(expr* _e) {
    expr_ref e(_e, m);
    context& ctx = get_context();
    ensure_enode(e);
    return ctx.get_literal(e);
}

void theory_seq::add_axiom(literal l1, literal l2, literal l3, literal l4) {
    context& ctx = get_context();
    literal_vector lits;
    if (l1 != null_literal) { ctx.mark_as_relevant(l1); lits.push_back(l1); }
    if (l2 != null_literal) { ctx.mark_as_relevant(l2); lits.push_back(l2); }
    if (l3 != null_literal) { ctx.mark_as_relevant(l3); lits.push_back(l3); }
    if (l4 != null_literal) { ctx.mark_as_relevant(l4); lits.push_back(l4); }
    TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
    ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
}


expr_ref theory_seq::mk_skolem(symbol const& name, expr* e1, 
                               expr* e2, expr* e3, sort* range) {
    expr* es[3] = { e1, e2, e3 };
    unsigned len = e3?3:(e2?2:1);
    if (!range) {
        range = m.get_sort(e1);
    }
    return expr_ref(m_util.mk_skolem(name, len, es, range), m);
}

bool theory_seq::is_skolem(symbol const& s, expr* e) const {
    return m_util.is_skolem(e) && to_app(e)->get_decl()->get_parameter(0).get_symbol() == s;
}


void theory_seq::propagate_eq(bool_var v, expr* e1, expr* e2) {
    context& ctx = get_context();

    enode* n1 = ensure_enode(e1);
    enode* n2 = ensure_enode(e2);
    if (n1->get_root() == n2->get_root()) {
        return;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    TRACE("seq", 
          tout << mk_pp(ctx.bool_var2expr(v), m) << " => " 
          << mk_pp(e1, m) << " = " << mk_pp(e2, m) << "\n";); 
    literal lit(v);
    justification* js = 
        ctx.mk_justification(
            ext_theory_eq_propagation_justification(
                get_id(), ctx.get_region(), 1, &lit, 0, 0, n1, n2));

    ctx.assign_eq(n1, n2, eq_justification(js));
}


void theory_seq::assign_eh(bool_var v, bool is_true) {
    context & ctx = get_context();
    expr* e = ctx.bool_var2expr(v);
    expr* e1, *e2;
    expr_ref f(m);

    if (is_true && m_util.str.is_prefix(e, e1, e2)) {
        f = mk_skolem(m_prefix, e1, e2);
        f = m_util.str.mk_concat(e1, f);
        propagate_eq(v, f, e2);
    }
    else if (is_true && m_util.str.is_suffix(e, e1, e2)) {
        f = mk_skolem(m_suffix, e1, e2);
        f = m_util.str.mk_concat(f, e1);
        propagate_eq(v, f, e2);
    }
    else if (is_true && m_util.str.is_contains(e, e1, e2)) {
        expr_ref f1 = mk_skolem(m_contains_left, e1, e2);
        expr_ref f2 = mk_skolem(m_contains_right, e1, e2);
        f = m_util.str.mk_concat(f1, m_util.str.mk_concat(e2, f2));
        propagate_eq(v, f, e1);
    }
    else if (is_accept(e)) {
        if (is_true) {
            m_trail_stack.push(push_back_vector<theory_seq, ptr_vector<expr> >(m_accepts));
            m_accepts.push_back(e);
        }
    }
    else if (is_reject(e)) {
        if (is_true) {
            m_trail_stack.push(push_back_vector<theory_seq, ptr_vector<expr> >(m_rejects));
            m_rejects.push_back(e);
        }
    }
    else if (is_step(e)) {
        if (is_true) {
            propagate_step(v, e);
            m_trail_stack.push(push_back_vector<theory_seq, ptr_vector<expr> >(m_steps));
            m_steps.push_back(e);
        }
    }
    else if (m_util.str.is_in_re(e)) {
        propagate_in_re(e, is_true);
    }
    else {
        SASSERT(!is_true);
        //if (m_util.str.is_prefix(e, e1, e2)) {
            // could add negative prefix axioms:
            // len(e1) <= len(e2) => e2 = seq.prefix.left(e2)*seq.prefix.right(e2)
            //                    &  len(seq.prefix.left(e2)) = len(e1)
            //                    &  seq.prefix.left(e2) != e1
            // or could solve prefix/suffix disunification constraints.
        //}
        m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_ineqs));
        m_ineqs.push_back(e);
    }
}

void theory_seq::new_eq_eh(theory_var v1, theory_var v2) { 
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);
    if (n1 != n2) {
        expr_ref o1(n1->get_owner(), m);
        expr_ref o2(n2->get_owner(), m);
        TRACE("seq", tout << o1 << " = " << o2 << "\n";);
        enode_pair_dependency* deps = m_dm.mk_leaf(enode_pair(n1, n2));
        bool propagated = false;
        if (!simplify_eq(o1, o2, deps, propagated)) {
            m_eqs.push_back(eq(o1, o2, deps));
        }
        if (has_length(o1) && !has_length(o2)) {
            enforce_length(n2);
        }
        else if (has_length(o2) && !has_length(o1)) {
            enforce_length(n1);
        }
    }
}

void theory_seq::new_diseq_eh(theory_var v1, theory_var v2) {
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);
    expr_ref e1(n1->get_owner(), m);
    expr_ref e2(n2->get_owner(), m);
    m_exclude.update(e1, e2);
    expr_ref eq(m.mk_eq(e1, e2), m);
    m_rewrite(eq);
    if (!m.is_false(eq)) {
        m_nqs.push_back(ne(e1, e2));
    }
}

void theory_seq::push_scope_eh() {
    theory::push_scope_eh();
    m_rep.push_scope();
    m_exclude.push_scope();
    m_dm.push_scope();
    m_trail_stack.push_scope();
    m_trail_stack.push(value_trail<theory_seq, unsigned>(m_axioms_head));
    m_eqs.push_scope();
    m_nqs.push_scope();
}

void theory_seq::pop_scope_eh(unsigned num_scopes) {
    m_trail_stack.pop_scope(num_scopes);
    theory::pop_scope_eh(num_scopes);   
    m_dm.pop_scope(num_scopes); 
    m_rep.pop_scope(num_scopes);
    m_exclude.pop_scope(num_scopes);
    m_eqs.pop_scope(num_scopes);
    m_nqs.pop_scope(num_scopes);
}

void theory_seq::restart_eh() {
}

void theory_seq::relevant_eh(app* n) {    
    if (m_util.str.is_index(n)   ||
        m_util.str.is_replace(n) ||
        m_util.str.is_extract(n) ||
        m_util.str.is_at(n) ||
        m_util.str.is_string(n) ||
        is_step(n)) {
        enque_axiom(n);
    }

    expr* arg;
    if (m_util.str.is_length(n, arg) && !has_length(arg)) {
        enforce_length(get_context().get_enode(arg));
    }
}


eautomaton* theory_seq::get_automaton(expr* re) {
    eautomaton* result = 0;
    if (m_re2aut.find(re, result)) {
        return result;
    }
    result = re2automaton(m)(re);
    if (result) {
        display_expr disp(m);
        TRACE("seq", result->display(tout, disp););
    }
    if (result) {
        m_automata.push_back(result);
        m_trail_stack.push(push_back_vector<theory_seq, scoped_ptr_vector<eautomaton> >(m_automata));
    }
    m_re2aut.insert(re, result);
    m_trail_stack.push(insert_obj_map<theory_seq, expr, eautomaton*>(m_re2aut, re));
    return result;
}

literal theory_seq::mk_accept(expr* s, expr* idx, expr* re, expr* state) {
    expr_ref_vector args(m);
    args.push_back(s).push_back(idx).push_back(re).push_back(state);
    return mk_literal(m_util.mk_skolem(m_accept, args.size(), args.c_ptr(), m.mk_bool_sort()));
}
literal theory_seq::mk_reject(expr* s, expr* idx, expr* re, expr* state) {
    expr_ref_vector args(m);
    args.push_back(s).push_back(idx).push_back(re).push_back(state);
    return mk_literal(m_util.mk_skolem(m_reject, args.size(), args.c_ptr(), m.mk_bool_sort()));
}

bool theory_seq::is_acc_rej(symbol const& ar, expr* e, expr*& s, expr*& idx, expr*& re, unsigned& i, eautomaton*& aut) {
    if (is_skolem(ar, e)) {
        rational r;
        s  = to_app(e)->get_arg(0);
        idx = to_app(e)->get_arg(1);
        re = to_app(e)->get_arg(2);
        VERIFY(m_autil.is_numeral(to_app(e)->get_arg(3), r));
        SASSERT(r.is_unsigned());
        i = r.get_unsigned();
        aut = m_re2aut[re];
        return true;
    }
    else {
        return false;
    }
}

bool theory_seq::is_step(expr* e) const {
    return is_skolem(m_aut_step, e);
}

bool theory_seq::is_step(expr* e, expr*& s, expr*& idx, expr*& re, expr*& i, expr*& j, expr*& t) const {
    if (is_step(e)) {
        s    = to_app(e)->get_arg(0);
        idx  = to_app(e)->get_arg(1);
        re   = to_app(e)->get_arg(2);
        i    = to_app(e)->get_arg(3);
        j    = to_app(e)->get_arg(4);
        t    = to_app(e)->get_arg(5);
        return true;
    }
    else {
        return false;
    }
}

expr_ref theory_seq::mk_step(expr* s, expr* idx, expr* re, unsigned i, unsigned j, expr* t) { 
    expr_ref_vector args(m);
    args.push_back(s).push_back(idx).push_back(re);
    args.push_back(m_autil.mk_int(i));
    args.push_back(m_autil.mk_int(j));
    args.push_back(t);
    return expr_ref(m_util.mk_skolem(m_aut_step, args.size(), args.c_ptr(), m.mk_bool_sort()), m);
}


/**
   acc(s, idx, re, i) ->  \/ step(s, idx, re, i, j, t)                  if i is non-final
   acc(s, idx, re, i) -> len(s) <= idx \/ step(s, idx, re, i, j, t)   if i is final
   acc(s, idx, re, i) -> len(s) >= idx
*/
void theory_seq::add_accept2step(expr* acc) {
    context& ctx = get_context();
    SASSERT(ctx.get_assignment(acc) == l_true);
    expr *e, * idx, *re;
    expr_ref step(m);
    unsigned src;
    eautomaton* aut = 0;
    VERIFY(is_accept(acc, e, idx, re, src, aut));
    if (!aut || m_util.str.is_length(idx)) return;
    SASSERT(m_autil.is_numeral(idx));
    eautomaton::moves mvs;
    aut->get_moves_from(src, mvs);
     
    expr_ref len(m_util.str.mk_length(e), m);
    literal_vector lits;
    lits.push_back(~ctx.get_literal(acc));
    if (aut->is_final_state(src)) {
        lits.push_back(mk_literal(m_autil.mk_le(len, idx)));
    }
    for (unsigned i = 0; i < mvs.size(); ++i) {
        eautomaton::move mv = mvs[i];
        step = mk_step(e, idx, re, src, mv.dst(), mv.t());
        lits.push_back(mk_literal(step));
    }
    TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
    for (unsigned i = 0; i < lits.size(); ++i) { // TBD
        ctx.mark_as_relevant(lits[i]);
    }
    ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    add_axiom(~ctx.get_literal(acc), mk_literal(m_autil.mk_ge(len, idx)));
}


/**
   acc(s, idx, re, i) & step(s, idx, re, i, j, t) => acc(s, idx + 1, re, j)
*/

void theory_seq::add_step2accept(expr* step) {
    context& ctx = get_context();
    SASSERT(ctx.get_assignment(step) == l_true);
    rational r;
    expr* re, *t, *s, *idx, *i, *j;
    VERIFY(is_step(step, s, idx, re, i, j, t));
    VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());    
    expr_ref idx1(m_autil.mk_int(r.get_unsigned() + 1), m);
    literal acc1 = mk_accept(s, idx,  re, i);
    literal acc2 = mk_accept(s, idx1, re, j);    
    add_axiom(~acc1, ~ctx.get_literal(step), acc2);
}


/*
   rej(s, idx, re, i) & nth(s,idx) = t & idx < len(s) => rej(s, idx + 1 re, j)
   rej(s, idx, re, i) => idx <= len(s)
*/ 
void theory_seq::add_reject2reject(expr* rej) {
    context& ctx = get_context();
    SASSERT(ctx.get_assignment(rej) == l_true);
    expr* e, *idx, *re;
    unsigned src;
    rational r;
    eautomaton* aut = 0;
    VERIFY(is_reject(rej, e, idx, re, src, aut));
    if (!aut || m_util.str.is_length(idx)) return;
    VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());
    expr_ref idx1(m_autil.mk_int(r.get_unsigned() + 1), m);
    eautomaton::moves mvs;
    aut->get_moves_from(src, mvs);
    literal rej1 = ctx.get_literal(rej);
    expr_ref len(m_util.str.mk_length(e), m);
    add_axiom(~rej1, mk_literal(m_autil.mk_ge(len, idx)));
    for (unsigned i = 0; i < mvs.size(); ++i) {
        eautomaton::move const& mv = mvs[i];        
        expr_ref nth = mk_nth(e, idx);        
        literal rej2 = mk_reject(e, idx1, re, m_autil.mk_int(mv.dst()));
        add_axiom(~rej1, ~mk_eq(nth, mv.t(), false), ~mk_literal(m_autil.mk_ge(len, idx)), rej2);
    }
}

bool theory_seq::propagate_automata() {
    context& ctx = get_context();
    bool change = false;
    if (m_accepts_qhead < m_accepts.size())  
        m_trail_stack.push(value_trail<theory_seq, unsigned>(m_accepts_qhead)), change = true;
    if (m_rejects_qhead < m_rejects.size())
        m_trail_stack.push(value_trail<theory_seq, unsigned>(m_rejects_qhead)), change = true;
    if (m_steps_qhead < m_steps.size())
        m_trail_stack.push(value_trail<theory_seq, unsigned>(m_steps_qhead)), change = true;

    while (m_accepts_qhead < m_accepts.size() && !ctx.inconsistent()) {
        add_accept2step(m_accepts[m_accepts_qhead]);       
        ++m_accepts_qhead;
    }
    while (m_rejects_qhead < m_rejects.size() && !ctx.inconsistent()) {
        add_reject2reject(m_rejects[m_rejects_qhead]);        
        ++m_rejects_qhead;
    }
    while (m_steps_qhead < m_steps.size() && !ctx.inconsistent()) {
        add_step2accept(m_steps[m_steps_qhead]);        
        ++m_steps_qhead;
    }
    return change || ctx.inconsistent();
}
