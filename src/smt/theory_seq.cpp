/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_seq.h

Abstract:

    Native theory solver for sequences.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12

Revision History:

    // Use instead reference counts for dependencies to GC?

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



void theory_seq::solution_map::update(expr* e, expr* r, dependency* d) {
    if (e == r) {
        return;
    }
    m_cache.reset();
    std::pair<expr*, dependency*> value;
    if (m_map.find(e, value)) {
        add_trail(DEL, e, value.first, value.second);
    }
    value.first = r;
    value.second = d;
    m_map.insert(e, value);
    add_trail(INS, e, r, d);
}

void theory_seq::solution_map::add_trail(map_update op, expr* l, expr* r, dependency* d) {
    m_updates.push_back(op);
    m_lhs.push_back(l);
    m_rhs.push_back(r);
    m_deps.push_back(d);
}

bool theory_seq::solution_map::is_root(expr* e) const {
    return !m_map.contains(e);
}

expr* theory_seq::solution_map::find(expr* e, dependency*& d) {
    std::pair<expr*, dependency*> value;
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

expr* theory_seq::solution_map::find(expr* e) {
    std::pair<expr*, dependency*> value;
    while (m_map.find(e, value)) {
        e = value.first;
    }
    return e;
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
    m_exclude(m),
    m_axioms(m),
    m_axioms_head(0),
    m_branch_variable_head(0),
    m_mg(0),
    m_rewrite(m), 
    m_util(m),
    m_autil(m),
    m_trail_stack(*this),
    m_atoms_qhead(0),
    m_new_solution(false),
    m_new_propagation(false) {    
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
    if (simplify_and_solve_eqs()) {
        ++m_stats.m_solve_eqs;
        TRACE("seq", tout << ">>solve_eqs\n";);
        return FC_CONTINUE;
    }
    if (solve_nqs(0)) {
        ++m_stats.m_solve_nqs;
        TRACE("seq", tout << ">>solve_nqs\n";);
        return FC_CONTINUE;
    }
    if (branch_variable()) {
        ++m_stats.m_branch_variable;
        TRACE("seq", tout << ">>branch_variable\n";);
        return FC_CONTINUE;
    }
    if (!check_length_coherence()) {
        ++m_stats.m_check_length_coherence;
        TRACE("seq", tout << ">>check_length_coherence\n";);
        return FC_CONTINUE;
    }
    if (propagate_automata()) {
        ++m_stats.m_propagate_automata;
        TRACE("seq", tout << ">>propagate_automata\n";);
        return FC_CONTINUE;
    }
    if (is_solved()) {
        TRACE("seq", tout << ">>is_solved\n";);
        return FC_DONE;
    }

    return FC_GIVEUP;
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

#if 1       
        if (!ls.empty() && find_branch_candidate(e.m_dep, ls[0].get(), rs)) {
            m_branch_variable_head = k;
            return true;
        }
        if (!rs.empty() && find_branch_candidate(e.m_dep, rs[0].get(), ls)) {
            m_branch_variable_head = k;
            return true;
        }
#else
        if (ls.size() > 1 && find_branch_candidate(e.m_dep, ls.back(), rs)) {
            m_branch_variable_head = k;
            return true;
        }
        if (rs.size() > 1 && find_branch_candidate(e.m_dep, rs.back(), ls)) {
            m_branch_variable_head = k;
            return true;
        }
#endif
#if 0
        if (!has_length(e.m_lhs)) {
            enforce_length(ensure_enode(e.m_lhs));
        }
        if (!has_length(e.m_rhs)) {
            enforce_length(ensure_enode(e.m_rhs));
        }
#endif
    }
    return ctx.inconsistent();
}

bool theory_seq::find_branch_candidate(dependency* dep, expr* l, expr_ref_vector const& rs) {

    TRACE("seq", tout << mk_pp(l, m) << " " 
          << (is_var(l)?"var":"not var") << "\n";);

    if (!is_var(l)) {
        return false;
    }

    bool all_units = true;
    expr_ref_vector cases(m);
    expr_ref v0(m), v(m);
    v0 = m_util.str.mk_empty(m.get_sort(l));
    if (l_false != assume_equality(l, v0)) {
        return true;
    }
    for (unsigned j = 0; j < rs.size(); ++j) {
        if (occurs(l, rs[j])) {
            return false;
        }
        SASSERT(!m_util.str.is_string(rs[j]));
        all_units &= m_util.str.is_unit(rs[j]);
        v0 = m_util.str.mk_concat(j + 1, rs.c_ptr());
        if (l_false != assume_equality(l, v0)) {
            return true;
        }
    }           
    if (all_units) {
        literal_vector lits;
        lits.push_back(~mk_eq_empty(l));
        for (unsigned i = 0; i < rs.size(); ++i) {
            v0 = m_util.str.mk_concat(i + 1, rs.c_ptr());
            lits.push_back(~mk_eq(l, v0, false));
        }
        set_conflict(dep, lits);
        return true;
    }
    return false;
}

lbool theory_seq::assume_equality(expr* l, expr* r) {
    context& ctx = get_context();
    if (m_exclude.contains(l, r)) {
        return l_false;
    }

    expr_ref eq(m.mk_eq(l, r), m);
    m_rewrite(eq);
    if (m.is_true(eq)) {
        return l_true;
    }
    if (m.is_false(eq)) {
        return l_false;
    }
    
    TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << "\n";);
    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);
    if (n1->get_root() == n2->get_root()) {
        return l_true;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);    
    ctx.assume_eq(n1, n2);
    return l_undef;
}

bool theory_seq::propagate_length_coherence(expr* e) {
    expr_ref head(m), tail(m);
    rational lo, hi;

    if (!is_var(e) || !m_rep.is_root(e)) {
        return false;
    }
    if (!lower_bound(e, lo) || !lo.is_pos() || lo >= rational(2048)) {
        return false;
    }
    TRACE("seq", tout << "Unsolved " << mk_pp(e, m);
          if (!lower_bound(e, lo)) lo = -rational::one();
          if (!upper_bound(e, hi)) hi = -rational::one();
          tout << " lo: " << lo << " hi: " << hi << "\n";
          );

    expr_ref seq(e, m);
    expr_ref_vector elems(m);
    unsigned _lo = lo.get_unsigned();
    for (unsigned j = 0; j < _lo; ++j) {
        mk_decompose(seq, head, tail);
        elems.push_back(head);
        seq = tail;
    }
    expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
    elems.push_back(seq);
    tail = m_util.str.mk_concat(elems.size(), elems.c_ptr());
    // len(e) >= low => e = tail;
    literal low(mk_literal(m_autil.mk_ge(m_util.str.mk_length(e), m_autil.mk_numeral(lo, true))));
    add_axiom(~low, mk_eq(e, tail, false));    
    assume_equality(seq, emp);
    if (upper_bound(e, hi)) {
        expr_ref high1(m_autil.mk_le(m_util.str.mk_length(e), m_autil.mk_numeral(hi, true)), m);
        expr_ref high2(m_autil.mk_le(m_util.str.mk_length(seq), m_autil.mk_numeral(hi-lo, true)), m);     
        add_axiom(~mk_literal(high1), mk_literal(high2));
        m_trail_stack.push(push_replay(alloc(replay_length_coherence, m, e)));
    }

    return true;
}

bool theory_seq::check_length_coherence() {
    bool coherent = true;
    obj_hashtable<expr>::iterator it = m_length.begin(), end = m_length.end();
    for (; it != end; ++it) {
        expr* e = *it;
        if (is_var(e) && m_rep.is_root(e)) {
            expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
            expr_ref head(m), tail(m);
            if (!propagate_length_coherence(e) &&
                l_false == assume_equality(e, emp)) {
                // e = emp \/ e = unit(head.elem(e))*tail(e)
                mk_decompose(e, head, tail);
                expr_ref conc(m_util.str.mk_concat(head, tail), m);
                propagate_is_conc(e, conc);
                assume_equality(tail, emp);
            }
            return false;
        }
    }
    return coherent;
}    

/*
    lit => s != ""
*/
void theory_seq::propagate_non_empty(literal lit, expr* s) {
    SASSERT(get_context().get_assignment(lit) == l_true);
    propagate_lit(0, 1, &lit, ~mk_eq_empty(s));    
}

void theory_seq::propagate_is_conc(expr* e, expr* conc) {
    TRACE("seq", tout << mk_pp(conc, m) << " is non-empty\n";);
    context& ctx = get_context();
    literal lit = ~mk_eq_empty(e);
    SASSERT(ctx.get_assignment(lit) == l_true);
    propagate_lit(0, 1, &lit, mk_eq(e, conc, false));
    expr_ref e1(e, m), e2(conc, m);
    new_eq_eh(m_dm.mk_leaf(assumption(lit)), ctx.get_enode(e1), ctx.get_enode(e2));
}

bool theory_seq::is_nth(expr* e) const {
    return is_skolem(m_nth, e);
}

expr_ref theory_seq::mk_nth(expr* s, expr* idx) {
    sort* char_sort = 0;
    VERIFY(m_util.is_seq(m.get_sort(s), char_sort));
    return mk_skolem(m_nth, s, idx, 0, char_sort);
}

expr_ref theory_seq::mk_last(expr* s) {
    sort* char_sort = 0;
    VERIFY(m_util.is_seq(m.get_sort(s), char_sort));
    return mk_skolem(m_seq_last, s, 0, 0, char_sort);
}


void theory_seq::mk_decompose(expr* e, expr_ref& head, expr_ref& tail) {
    expr* e1, *e2;
    zstring s;
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
        tail = m_util.str.mk_empty(m.get_sort(e));
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


/*
   - Eqs = 0
   - Diseqs evaluate to false
   - lengths are coherent.
*/

bool theory_seq::is_solved() {
    if (!m_eqs.empty()) {
        IF_VERBOSE(10, verbose_stream() << "(seq.giveup " << m_eqs[0].m_lhs << " = " << m_eqs[0].m_rhs << " is unsolved)\n";);
        return false;
    }
    for (unsigned i = 0; i < m_automata.size(); ++i) {
        if (!m_automata[i]) {
            IF_VERBOSE(10, verbose_stream() << "(seq.giveup regular expression did not compile to automaton)\n";);
            return false;
        }
    }    
    return true;
}

void theory_seq::linearize(dependency* dep, enode_pair_vector& eqs, literal_vector& lits) const {
    svector<assumption> assumptions;
    const_cast<dependency_manager&>(m_dm).linearize(dep, assumptions);
    for (unsigned i = 0; i < assumptions.size(); ++i) {
        assumption const& a = assumptions[i];
        if (a.lit != null_literal) {
            lits.push_back(a.lit);
        }
        if (a.n1 != 0) {
            eqs.push_back(enode_pair(a.n1, a.n2));
        }
    }
}



void theory_seq::propagate_lit(dependency* dep, unsigned n, literal const* _lits, literal lit) {
    context& ctx = get_context();
    ctx.mark_as_relevant(lit);
    literal_vector lits(n, _lits);
    enode_pair_vector eqs;
    linearize(dep, eqs, lits);
    TRACE("seq", ctx.display_detailed_literal(tout, lit); 
          tout << " <- "; ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); display_deps(tout, dep);); 
    justification* js = 
        ctx.mk_justification(
            ext_theory_propagation_justification(
                get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), lit));

    m_new_propagation = true;
    ctx.assign(lit, js);
}

void theory_seq::set_conflict(dependency* dep, literal_vector const& _lits) {
    context& ctx = get_context();
    enode_pair_vector eqs;
    literal_vector lits(_lits);
    linearize(dep, eqs, lits);
    TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); display_deps(tout, dep); ;); 
    m_new_propagation = true;
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), 0, 0)));
}

void theory_seq::propagate_eq(dependency* dep, enode* n1, enode* n2) {
    if (n1->get_root() == n2->get_root()) {
        return;
    }
    context& ctx = get_context();
    literal_vector lits;
    enode_pair_vector eqs;
    linearize(dep, eqs, lits);
    TRACE("seq",
          tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << " <- ";
          display_deps(tout, dep);
          ); 
    
    justification* js = ctx.mk_justification(
        ext_theory_eq_propagation_justification(
            get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), n1, n2));
    ctx.assign_eq(n1, n2, eq_justification(js));
    m_new_propagation = true;

    enforce_length_coherence(n1, n2);
}

void theory_seq::enforce_length_coherence(enode* n1, enode* n2) {
    expr* o1 = n1->get_owner();
    expr* o2 = n2->get_owner();
    if (has_length(o1) && !has_length(o2)) {
        enforce_length(n2);
    }
    else if (has_length(o2) && !has_length(o1)) {
        enforce_length(n1);
    }
}



bool theory_seq::simplify_eq(expr* l, expr* r, dependency* deps) {
    context& ctx = get_context();
    seq_rewriter rw(m);
    expr_ref_vector lhs(m), rhs(m);
    if (!rw.reduce_eq(l, r, lhs, rhs)) {
        // equality is inconsistent.
        TRACE("seq", tout << mk_pp(l, m) << " != " << mk_pp(r, m) << "\n";);
        set_conflict(deps);
        return true;
    }
    if (unchanged(l, lhs, r, rhs)) {
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

bool theory_seq::solve_unit_eq(expr* l, expr* r, dependency* deps) {
    if (l == r) {
        return true;
    }
    if (is_var(l) && !occurs(l, r) && add_solution(l, r, deps)) {
        return true;
    }
    if (is_var(r) && !occurs(r, l) && add_solution(r, l, deps)) {
        return true;
    }

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



bool theory_seq::add_solution(expr* l, expr* r, dependency* deps)  {
    if (l == r) {
        return false;
    }
    context& ctx = get_context();
    TRACE("seq", tout << mk_pp(l, m) << " ==> " << mk_pp(r, m) << "\n";);
    m_new_solution = true;
    m_rep.update(l, r, deps);
    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);
    if (n1->get_root() != n2->get_root()) {
        propagate_eq(deps, n1, n2);
    }
    return true;
}

bool theory_seq::solve_eqs(unsigned i) {
    context& ctx = get_context();
    bool change = false;
    for (; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        eq e = m_eqs[i];
        if (solve_eq(e.m_lhs, e.m_rhs, e.m_dep)) {
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
    return change || ctx.inconsistent();
}

bool theory_seq::solve_eq(expr* _l, expr* _r, dependency* deps) {
    context& ctx = get_context();
    expr_ref l = canonize(_l, deps);
    expr_ref r = canonize(_r, deps);
    TRACE("seq", tout << l << " = " << r << "\n";);
    if (!ctx.inconsistent() && simplify_eq(l, r, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_unit_eq(l, r, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_binary_eq(l, r, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && (_l != l || _r != r)) {
        m_eqs.push_back(eq(l, r, deps));
        return true;
    }
    return false;
}

bool theory_seq::is_binary_eq(expr* l, expr* r, expr*& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr*& y) {    
    xs.reset();
    ys.reset();
    get_concat(l, xs);
    if (xs.size() > 1 && is_var(xs[0])) {
        get_concat(r, ys);
        if (ys.size() > 1 && is_var(ys.back())) {
            x = xs[0];
            y = ys.back();
            for (unsigned i = 1; i < xs.size(); ++i) {
                if (!m_util.str.is_unit(xs[i])) return false;
                xs[i-1] = xs[i];
            }
            xs.pop_back();
            for (unsigned i = 0; i < ys.size()-1; ++i) {
                if (!m_util.str.is_unit(ys[i])) return false;
            }
            ys.pop_back();
            return true;
        }
    }
    return false;
}

bool theory_seq::solve_binary_eq(expr* l, expr* r, dependency* dep) {
    context& ctx = get_context();
    ptr_vector<expr> xs, ys;
    expr* x, *y;
    bool is_binary = is_binary_eq(l, r, x, xs, ys, y);
    if (!is_binary) {
        std::swap(l, r);
        is_binary = is_binary_eq(l, r, x, xs, ys, y);
    }
    if (!is_binary) {
        return false;
    }
    // Equation is of the form x ++ xs = ys ++ y
    // where xs, ys are units.
    if (x != y) {
        return false;
    }
    if (xs.size() != ys.size()) {
        set_conflict(dep);
        return false;
    }
    if (xs.empty()) {
        // this should have been solved already
        UNREACHABLE();        
        return false;
    }
    unsigned sz = xs.size();
    literal_vector conflict;
    for (unsigned offset = 0; offset < sz; ++offset) {
        bool has_conflict = false;
        for (unsigned j = 0; !has_conflict && j < sz; ++j) {
            unsigned j1 = (offset + j) % sz;
            literal eq = mk_eq(xs[j], ys[j1], false);
            switch (ctx.get_assignment(eq)) {
            case l_false:
                conflict.push_back(~eq);
                has_conflict = true;
                break;
            case l_undef: {
                enode* n1 = ensure_enode(xs[j]);
                enode* n2 = ensure_enode(ys[j1]);
                if (n1->get_root() == n2->get_root()) {
                    break;
                }
                ctx.mark_as_relevant(eq);
                if (sz == 1) {
                    propagate_lit(dep, 0, 0, eq);
                    return true;
                }
                m_new_propagation = true;
                break;
            }
            case l_true:
                break;
            }
        }
        if (!has_conflict) {
            TRACE("seq", tout << "offset: " << offset << " equality ";
                  for (unsigned j = 0; j < sz; ++j) {
                      tout << mk_pp(xs[j], m) << " = " << mk_pp(ys[(offset+j) % sz], m) << "; ";
                  }
                  tout << "\n";);
            // current equalities can work when solving x ++ xs = ys ++ y
            return false;
        }
    }
    TRACE("seq", tout << conflict << "\n";);
    set_conflict(dep, conflict);
    return false;
}

bool theory_seq::solve_nqs(unsigned i) {
    bool change = false;
    context & ctx = get_context();
    for (; !ctx.inconsistent() && i < m_nqs.size(); ++i) {
        if (!m_nqs[i].is_solved()) {
            solve_ne(i);
        }
    }
    return m_new_propagation || ctx.inconsistent();
}

void theory_seq::solve_ne(unsigned idx) {
    context& ctx = get_context();
    seq_rewriter rw(m);
    ne const& n = m_nqs[idx];
    TRACE("seq", display_disequation(tout, n););

    SASSERT(!n.is_solved());
    unsigned num_undef_lits = 0;
    for (unsigned i = 0; i < n.m_lits.size(); ++i) {
        switch (ctx.get_assignment(n.m_lits[i])) {
        case l_false:
            // mark as solved in 
            mark_solved(idx);
            return;
        case l_true:
            break;            
        case l_undef:
            ++num_undef_lits;
            break;
        }
    }
    for (unsigned i = 0; i < n.m_lhs.size(); ++i) {
        expr_ref_vector lhs(m), rhs(m);
        dependency* deps = 0;
        expr* l = n.m_lhs[i];
        expr* r = n.m_rhs[i];
        expr_ref lh = canonize(l, deps);
        expr_ref rh = canonize(r, deps);
        if (!rw.reduce_eq(lh, rh, lhs, rhs)) {
            mark_solved(idx);
            return;
        }
        else if (unchanged(l, lhs, r, rhs) ) {
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
                        return;
                    case l_true:
                        break;
                    case l_undef:
                        ++num_undef_lits;
                        m_new_propagation = true;
                        break;
                    }
                }
            }                
            m_trail_stack.push(push_dep(*this, idx, deps));
            erase_index(idx, i);
            --i;
        }
    }
    if (num_undef_lits == 0 && n.m_lhs.empty()) {
        literal_vector lits(n.m_lits);
        lits.push_back(~mk_eq(n.m_l, n.m_r, false));
        set_conflict(n.m_dep, lits);
        SASSERT(m_new_propagation);
    }
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
    m_new_propagation = false;
    m_new_solution = true;
    while (m_new_solution && !ctx.inconsistent()) {
        m_new_solution = false;
        solve_eqs(0);
    }
    return m_new_propagation || ctx.inconsistent();
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
    enode* e = 0;
    if (ctx.e_internalized(term)) {
        e = ctx.get_enode(term);
    }
    else {
        e = ctx.mk_enode(term, false, m.is_bool(term), true);
    } 
    mk_var(e);
    
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
        display_disequations(out);
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
    bool first = true;
    for (unsigned i = 0; i < m_nqs.size(); ++i) {
        if (!m_nqs[i].is_solved()) {
            if (first) out << "Disequations:\n";
            first = false;
            display_disequation(out, m_nqs[i]);
        }
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

void theory_seq::display_deps(std::ostream& out, dependency* dep) const {
    literal_vector lits;
    enode_pair_vector eqs;
    linearize(dep, eqs, lits);
    for (unsigned i = 0; i < eqs.size(); ++i) {
        out << "\n   " << mk_pp(eqs[i].first->get_owner(), m) << " = " << mk_pp(eqs[i].second->get_owner(), m);
    }
    for (unsigned i = 0; i < lits.size(); ++i) {
        literal lit = lits[i];
        get_context().display_literals_verbose(out << "\n   ", 1, &lit);
    }
    out << "\n";
    
}

void theory_seq::collect_statistics(::statistics & st) const {
    st.update("seq num splits", m_stats.m_num_splits);
    st.update("seq num reductions", m_stats.m_num_reductions);
    st.update("seq unfold def", m_stats.m_propagate_automata);
    st.update("seq length coherence", m_stats.m_check_length_coherence);
    st.update("seq branch", m_stats.m_branch_variable);
    st.update("seq solve !=", m_stats.m_solve_nqs);
    st.update("seq solve =", m_stats.m_solve_eqs);

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
        return th.mk_value(mg.get_manager().mk_app(n->get_decl(), values.size(), values.c_ptr()));
    }    
};


model_value_proc * theory_seq::mk_value(enode * n, model_generator & mg) {
    context& ctx = get_context();
    expr_ref e(m);
    expr* e1;
    ptr_vector<expr> concats;
    get_concat(n->get_owner(), concats);
    switch (concats.size()) {
    case 0:
        e = m_util.str.mk_empty(m.get_sort(n->get_owner()));
        break;
    case 1:
        e = concats[0];
        SASSERT(!m_util.str.is_concat(e));
        break;
    default: 
        e = m_rep.find(n->get_owner());
        SASSERT(m_util.str.is_concat(e));
        break;
    }
    seq_value_proc* sv = alloc(seq_value_proc, *this, to_app(e));
    TRACE("seq", tout << mk_pp(n->get_owner(), m) << " ";
          for (unsigned i = 0; i < concats.size(); ++i) {
              tout << mk_pp(concats[i], m) << " ";
          }
          tout << "\n";
          );
    
    if (concats.size() > 1) {
        for (unsigned i = 0; i < concats.size(); ++i) {
            sv->add_dependency(ctx.get_enode(concats[i]));
        }
    }
    else if (m_util.str.is_unit(e, e1)) {
        sv->add_dependency(ctx.get_enode(e1));
    }                          
    return sv;
}

void theory_seq::get_concat(expr* e, ptr_vector<expr>& concats) {
    expr* e1, *e2;
    while (true) {
        e = m_rep.find(e);
        if (m_util.str.is_concat(e, e1, e2)) {
            get_concat(e1, concats);
            e = e2;
            continue;
        }
        if (!m_util.str.is_empty(e)) {
            concats.push_back(e);
        }
        return;        
    }
}

app* theory_seq::mk_value(app* e) {
    expr* e1;
    expr_ref result(e, m);
    if (m_util.str.is_unit(e, e1)) {
        dependency* deps = 0;
        result = expand(e1, deps);
        bv_util bv(m);
        rational val;
        unsigned sz;
        if (bv.is_numeral(result, val, sz) && sz == zstring().num_bits()) {
            unsigned v = val.get_unsigned();
            if ((0 <= v && v < 7) || (14 <= v && v < 32) || v == 127) {
                result = m_util.str.mk_unit(result);                
            }
            else {
                svector<bool> val_as_bits;
                for (unsigned i = 0; i < sz; ++i) {
                    val_as_bits.push_back(1 == v % 2);
                    v = v / 2;
                }
                result = m_util.str.mk_string(zstring(sz, val_as_bits.c_ptr()));
            }
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
    else if (is_nth(e)) {
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
    return m_axioms_head < m_axioms.size() || !m_replay.empty() || m_new_solution;
}

expr_ref theory_seq::canonize(expr* e, dependency*& eqs) {
    expr_ref result = expand(e, eqs);
    m_rewrite(result);
    return result;
}

expr_ref theory_seq::expand(expr* e0, dependency*& eqs) {
    expr_ref result(m);
    dependency* deps = 0;
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

void theory_seq::add_dependency(dependency*& dep, enode* a, enode* b) {
    if (a != b) {
        dep = m_dm.mk_join(dep, m_dm.mk_leaf(assumption(a, b)));
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
    while (!m_replay.empty() && !ctx.inconsistent()) {
        (*m_replay[m_replay.size()-1])(*this);
        TRACE("seq", tout << "replay: " << ctx.get_scope_level() << "\n";);
        m_replay.pop_back();
    }
    if (m_new_solution) {
        simplify_and_solve_eqs();
        m_new_solution = false;
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
    else if (m_util.str.is_empty(n) && !has_length(n) && !m_length.empty()) {
        enforce_length(get_context().get_enode(n));
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
  
  lit or s = "" or s = s1*(unit c)
  lit or s = "" or !prefix(s, x*s1)
*/
void theory_seq::tightest_prefix(expr* s, expr* x, literal lit1, literal lit2) {
    expr_ref s1 = mk_skolem(m_seq_first, s);
    expr_ref c  = mk_last(s);
    expr_ref s1c(m_util.str.mk_concat(s1, m_util.str.mk_unit(c)), m);
    literal s_eq_emp = mk_eq_empty(s);
    add_axiom(lit1, lit2, s_eq_emp, mk_eq(s, s1c, false));
    add_axiom(lit1, lit2, s_eq_emp, ~mk_literal(m_util.str.mk_prefix(s, m_util.str.mk_concat(x, s1))));
}

/*
  // index of s in t starting at offset.

  let i = Index(t, s, offset):
  
  offset >= len(t) => i = -1

  offset fixed to 0:

  len(t) != 0 & !contains(t, s) => i = -1
  len(t) != 0 & contains(t, s) => t = xsy & i = len(x)
  len(t) != 0 & contains(t, s) & s != emp => tightest_prefix(x, s)

  offset not fixed:

  0 <= offset < len(t) => xy = t & 
                          len(x) = offset & 
                          (-1 = indexof(y, s, 0) => -1 = i) & 
                          (indexof(y, s, 0) >= 0 => indexof(t, s, 0) + offset = i)
    
  if offset < 0 
     under specified

  optional lemmas:
   (len(s) > len(t)  -> i = -1) 
   (len(s) <= len(t) -> i <= len(t)-len(s))  
*/
void theory_seq::add_indexof_axiom(expr* i) {
    expr* s, *t, *offset;
    rational r;
    VERIFY(m_util.str.is_index(i, t, s, offset));
    expr_ref minus_one(m_autil.mk_int(-1), m);
    expr_ref zero(m_autil.mk_int(0), m);
    expr_ref xsy(m);

    // offset >= len(t) => indexof(s, t, offset) = -1
    expr_ref len_t(m_util.str.mk_length(t), m);
    literal offset_ge_len = mk_literal(m_autil.mk_ge(mk_sub(offset, len_t), zero));
    add_axiom(offset_ge_len, mk_eq(i, minus_one, false));

    if (m_autil.is_numeral(offset, r) && r.is_zero()) {
        expr_ref x  = mk_skolem(m_contains_left, t, s);
        expr_ref y  = mk_skolem(m_contains_right, t, s);    
        xsy         = m_util.str.mk_concat(x,s,y);
        literal cnt = mk_literal(m_util.str.mk_contains(t, s));
        literal eq_empty = mk_eq_empty(s);
        add_axiom(cnt,  mk_eq(i, minus_one, false));
        add_axiom(~eq_empty, mk_eq(i, zero, false));
        add_axiom(~cnt, eq_empty, mk_eq(t, xsy, false));
        tightest_prefix(s, x, ~cnt);
    }
    else {
        expr_ref x = mk_skolem(m_indexof_left, t, s, offset);
        expr_ref y = mk_skolem(m_indexof_right, t, s, offset);
        expr_ref indexof0(m_util.str.mk_index(y, s, zero), m);
        expr_ref offset_p_indexof0(m_autil.mk_add(offset, indexof0), m);
        literal offset_ge_0 = mk_literal(m_autil.mk_ge(offset, zero));
   	
        // 0 <= offset & offset < len(t) => t = xy   
        // 0 <= offset & offset < len(t) => len(x) = offset
        // 0 <= offset & offset < len(t) & -1 = indexof(y,s,0) = -1 => -1 = i
        // 0 <= offset & offset < len(t) & indexof(y,s,0) >= 0 = -1 => 
        //                  -1 = indexof(y,s,0) + offset = indexof(t, s, offset)
        
        add_axiom(~offset_ge_0, offset_ge_len, mk_eq(t, m_util.str.mk_concat(x, y), false));
        add_axiom(~offset_ge_0, offset_ge_len, mk_eq(m_util.str.mk_length(x), offset, false));
        add_axiom(~offset_ge_0, offset_ge_len, 
                  ~mk_eq(indexof0, minus_one, false), mk_eq(i, minus_one, false));
        add_axiom(~offset_ge_0, offset_ge_len, 
                  ~mk_literal(m_autil.mk_ge(indexof0, zero)), 
                  mk_eq(offset_p_indexof0, i, false));
    }
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
    m_new_solution = true;
}


/*
    let n = len(x)
    - len(a ++ b) = len(a) + len(b) if x = a ++ b
    - len(unit(u)) = 1              if x = unit(u)
    - len(str) = str.length()       if x = str
    - len(empty) = 0                if x = empty
    - len(x) >= 0                   otherwise
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
        add_axiom(mk_literal(m_autil.mk_ge(n, m_autil.mk_int(0))));        
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
    }
    enode* n = ctx.get_enode(e);
    ctx.mark_as_relevant(n);
    return n;
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
   step(s, idx, re, i, j, t) -> nth(s, idx) == t & len(s) > idx
*/
void theory_seq::propagate_step(literal lit, expr* step) {
    context& ctx = get_context();
    SASSERT(ctx.get_assignment(lit) == l_true);
    expr* re, *t, *s, *idx, *i, *j;
    VERIFY(is_step(step, s, idx, re, i, j, t));
    expr_ref nth = mk_nth(s, idx);
    TRACE("seq", tout << mk_pp(step, m) << " -> " << mk_pp(t, m) << " = " << nth << "\n";);
    propagate_eq(lit, t, nth);
    propagate_lit(0, 1, &lit, ~mk_literal(m_autil.mk_le(m_util.str.mk_length(s), idx)));
    ensure_nth(lit, s, idx);
}

/*
    lit => s = (nth s 0) ++ (nth s 1) ++ ... ++ (nth s idx) ++ (tail s idx)
*/
void theory_seq::ensure_nth(literal lit, expr* s, expr* idx) {
    context& ctx = get_context();
    rational r;
    VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());
    unsigned _idx = r.get_unsigned();
    dependency* dep = 0;
    expr_ref s1 = canonize(s, dep);
    ptr_vector<expr> es;
    expr* e1;
    expr_ref nth = mk_nth(s, idx);
    expr_ref head(m), tail(m), conc(m);
    expr_ref_vector elems(m);
    get_concat(s1, es);
    unsigned i = 0;
    for (; i < _idx && i < es.size() && m_util.str.is_unit(es[i]); ++i) {};    
    if (i == _idx && i < es.size() && m_util.str.is_unit(es[i], e1)) {
        dep = m_dm.mk_join(dep, m_dm.mk_leaf(assumption(lit)));
        propagate_eq(dep, ensure_enode(nth), ensure_enode(e1));
        return;
    }
    // TBD could tune this aggregate quadratic overhead
    expr* s2 = s;
    for (unsigned j = 0; j <= _idx; ++j) {
        mk_decompose(s2, head, tail);
        elems.push_back(head);
        s2 = tail;
    }
    elems.push_back(s2);
    conc = m_util.str.mk_concat(elems.size(), elems.c_ptr());
    propagate_eq(lit, s, conc, true);

    // TBD: examine other places for enforcing constraints on tail
    add_axiom(~lit, mk_eq(m_util.str.mk_length(s), m_util.str.mk_length(conc), false));
}

literal theory_seq::mk_literal(expr* _e) {
    expr_ref e(_e, m);
    context& ctx = get_context();
    ensure_enode(e);
    return ctx.get_literal(e);
}

literal theory_seq::mk_equals(expr* a, expr* b) {
    literal lit = mk_eq(a, b, false);
    get_context().force_phase(lit);
    return lit;
}

literal theory_seq::mk_eq_empty(expr* _e) {
    expr_ref e(_e, m);
    SASSERT(m_util.is_seq(e));
    expr_ref emp(m);
    emp = m_util.str.mk_empty(m.get_sort(e));
    return mk_equals(e, emp);
}

void theory_seq::add_axiom(literal l1, literal l2, literal l3, literal l4) {
    context& ctx = get_context();
    literal_vector lits;
    if (l1 != null_literal) { ctx.mark_as_relevant(l1); lits.push_back(l1); }
    if (l2 != null_literal) { ctx.mark_as_relevant(l2); lits.push_back(l2); }
    if (l3 != null_literal) { ctx.mark_as_relevant(l3); lits.push_back(l3); }
    if (l4 != null_literal) { ctx.mark_as_relevant(l4); lits.push_back(l4); }
    TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
    m_new_propagation = true;
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


void theory_seq::propagate_eq(literal lit, expr* e1, expr* e2, bool add_to_eqs) {
    context& ctx = get_context();

    enode* n1 = ensure_enode(e1);
    enode* n2 = ensure_enode(e2);
    if (n1->get_root() == n2->get_root()) {
        return;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    if (add_to_eqs) {
        SASSERT(l_true == ctx.get_assignment(lit));
        dependency* deps = m_dm.mk_leaf(assumption(lit));
        new_eq_eh(deps, n1, n2);
        
    }
    TRACE("seq", 
          tout << mk_pp(ctx.bool_var2expr(lit.var()), m) << " => " 
          << mk_pp(e1, m) << " = " << mk_pp(e2, m) << "\n";); 
    justification* js = 
        ctx.mk_justification(
            ext_theory_eq_propagation_justification(
                get_id(), ctx.get_region(), 1, &lit, 0, 0, n1, n2));

    m_new_propagation = true;
    ctx.assign_eq(n1, n2, eq_justification(js));
}


void theory_seq::assign_eh(bool_var v, bool is_true) {
    context & ctx = get_context();
    expr* e = ctx.bool_var2expr(v);
    expr* e1, *e2;
    expr_ref f(m);
    literal lit(v, !is_true);

    if (m_util.str.is_prefix(e, e1, e2)) {
        if (is_true) {
            f = mk_skolem(m_prefix, e1, e2);
            f = m_util.str.mk_concat(e1, f);
            propagate_eq(lit, f, e2, true);
        }
        else {
            // !prefix(e1,e2) => e1 != ""
            propagate_non_empty(lit, e1);
            if (add_prefix2prefix(e)) {
                add_atom(e);
            }
        }
    }
    else if (m_util.str.is_suffix(e, e1, e2)) {
        if (is_true) {
            f = mk_skolem(m_suffix, e1, e2);
            f = m_util.str.mk_concat(f, e1);
            propagate_eq(lit, f, e2, true);
        }
        else {
            // lit => e1 != empty
            propagate_non_empty(lit, e1);

            // lit => e1 = first ++ (unit last)
            expr_ref f1 = mk_skolem(m_seq_first, e1);
            expr_ref f2 = mk_last(e1);
            f = m_util.str.mk_concat(f1, m_util.str.mk_unit(f2));
            propagate_eq(lit, e1, f, true);

            if (add_suffix2suffix(e)) {
                add_atom(e);
            }
        }
    }
    else if (m_util.str.is_contains(e, e1, e2)) {
        if (is_true) {
            expr_ref f1 = mk_skolem(m_contains_left, e1, e2);
            expr_ref f2 = mk_skolem(m_contains_right, e1, e2);
            f = m_util.str.mk_concat(f1, e2, f2);
            propagate_eq(lit, f, e1, true);
        }
        else if (!canonizes(false, e)) {
            propagate_non_empty(lit, e2);
            propagate_lit(0, 1, &lit, ~mk_literal(m_util.str.mk_prefix(e2, e1)));
            if (add_contains2contains(e)) {
                add_atom(e);
            }
        }
    }
    else if (is_accept(e)) {
        if (is_true) {
            propagate_acc_rej_length(lit, e);
            if (add_accept2step(e)) {
                add_atom(e);
            }
        }
    }
    else if (is_reject(e)) {
        if (is_true) {
            propagate_acc_rej_length(lit, e);
            add_atom(e);
        }
    }
    else if (is_step(e)) {
        if (is_true) {
            propagate_step(lit, e);
            if (add_step2accept(e)) {
                add_atom(e);
            }
        }
    }
    else if (m_util.str.is_in_re(e)) {
        propagate_in_re(e, is_true);
    }
    else {
        UNREACHABLE();
    }
}

void theory_seq::add_atom(expr* e) {
    m_trail_stack.push(push_back_vector<theory_seq, ptr_vector<expr> >(m_atoms));
    m_atoms.push_back(e);
}

void theory_seq::new_eq_eh(theory_var v1, theory_var v2) { 
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);
    dependency* deps = m_dm.mk_leaf(assumption(n1, n2));
    new_eq_eh(deps, n1, n2);
}

void theory_seq::new_eq_eh(dependency* deps, enode* n1, enode* n2) {
    if (n1 != n2 && m_util.is_seq(n1->get_owner())) {
        expr_ref o1(n1->get_owner(), m);
        expr_ref o2(n2->get_owner(), m);
        TRACE("seq", tout << o1 << " = " << o2 << "\n";);
        m_eqs.push_back(eq(o1, o2, deps));        
        solve_eqs(m_eqs.size()-1);
        enforce_length_coherence(n1, n2);
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
        solve_nqs(m_nqs.size() - 1);
    }
    // add solution for variable that is non-empty?
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
    m_atoms_lim.push_back(m_atoms.size());
}

void theory_seq::pop_scope_eh(unsigned num_scopes) {
    m_trail_stack.pop_scope(num_scopes);
    theory::pop_scope_eh(num_scopes);   
    m_dm.pop_scope(num_scopes); 
    m_rep.pop_scope(num_scopes);
    m_exclude.pop_scope(num_scopes);
    m_eqs.pop_scope(num_scopes);
    m_nqs.pop_scope(num_scopes);
    m_atoms.resize(m_atoms_lim[m_atoms_lim.size()-num_scopes]);
    m_atoms_lim.shrink(m_atoms_lim.size()-num_scopes);
}

void theory_seq::restart_eh() {
}

void theory_seq::relevant_eh(app* n) {    
    if (m_util.str.is_index(n)   ||
        m_util.str.is_replace(n) ||
        m_util.str.is_extract(n) ||
        m_util.str.is_at(n) ||
        m_util.str.is_empty(n) ||
        m_util.str.is_string(n)) {
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

/*
   acc(s, idx, re, i) -> len(s) >= idx    if i is final
   rej(s, idx, re, i) -> len(s) >= idx    if i is non-final

   acc(s, idx, re, i) -> len(s) > idx     if i is non-final
   rej(s, idx, re, i) -> len(s) > idx     if i is final
*/
void theory_seq::propagate_acc_rej_length(literal lit, expr* e) {
    context& ctx = get_context();
    expr *s, * idx, *re;
    unsigned src;
    eautomaton* aut = 0;
    bool is_acc;
    is_acc = is_accept(e, s, idx, re, src, aut);
    if (!is_acc) {
        VERIFY(is_reject(e, s, idx, re, src, aut));
    }
    if (m_util.str.is_length(idx)) return;
    SASSERT(m_autil.is_numeral(idx));
    SASSERT(ctx.get_assignment(lit) == l_true);
    bool is_final = aut->is_final_state(src);
    if (is_final == is_acc) {
        propagate_lit(0, 1, &lit, mk_literal(m_autil.mk_ge(m_util.str.mk_length(s), idx)));
    }
    else {
        propagate_lit(0, 1, &lit, ~mk_literal(m_autil.mk_le(m_util.str.mk_length(s), idx)));    
    }
}

/**
   acc(s, idx, re, i) ->  \/ step(s, idx, re, i, j, t)                if i is non-final
   acc(s, idx, re, i) -> len(s) <= idx \/ step(s, idx, re, i, j, t)   if i is final
*/
bool theory_seq::add_accept2step(expr* acc) {
    context& ctx = get_context();
    
    TRACE("seq", tout << mk_pp(acc, m) << "\n";);
    SASSERT(ctx.get_assignment(acc) == l_true);
    expr *e, * idx, *re;
    expr_ref step(m);
    unsigned src;
    eautomaton* aut = 0;
    VERIFY(is_accept(acc, e, idx, re, src, aut));
    if (!aut || m_util.str.is_length(idx)) {
        return false;
    }
    SASSERT(m_autil.is_numeral(idx));
    eautomaton::moves mvs;
    aut->get_moves_from(src, mvs);
     
    expr_ref len(m_util.str.mk_length(e), m);
    literal_vector lits;
    lits.push_back(~ctx.get_literal(acc));
    if (aut->is_final_state(src)) {
        lits.push_back(mk_literal(m_autil.mk_le(len, idx)));
        switch (ctx.get_assignment(lits.back())) {
        case l_true:
            return false;
        case l_undef:
            ctx.force_phase(lits.back());           
            return true;
        default:
            break;
        }
    }
    bool has_undef = false;
    int start = ctx.get_random_value();
    for (unsigned i = 0; i < mvs.size(); ++i) {
        unsigned j = (i + start) % mvs.size();
        eautomaton::move mv = mvs[j];
        step = mk_step(e, idx, re, src, mv.dst(), mv.t());
        lits.push_back(mk_literal(step));
        switch (ctx.get_assignment(lits.back())) {
        case l_true:
            return false;
        case l_undef:
            //ctx.force_phase(lits.back());
            //return true;
            has_undef = true;
            break;
        default:
            break;
        }
    }
    if (has_undef) {
        return true;
    }    
    TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
    for (unsigned i = 0; i < lits.size(); ++i) {        
        SASSERT(ctx.get_assignment(lits[i]) == l_false);
        lits[i].neg();
    }
    set_conflict(0, lits);
    return false;
}


/**
   acc(s, idx, re, i) & step(s, idx, re, i, j, t) => acc(s, idx + 1, re, j)
*/

bool theory_seq::add_step2accept(expr* step) {
    context& ctx = get_context();
    SASSERT(ctx.get_assignment(step) == l_true);
    expr* re, *t, *s, *idx, *i, *j;
    VERIFY(is_step(step, s, idx, re, i, j, t));
    literal acc1 = mk_accept(s, idx,  re, i);
    switch (ctx.get_assignment(acc1)) {
    case l_false:
        break;
    case l_undef:
        return true;
    case l_true: {
        rational r;
        VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());    
        expr_ref idx1(m_autil.mk_int(r.get_unsigned() + 1), m);
        literal acc2 = mk_accept(s, idx1, re, j);
        literal_vector lits;
        lits.push_back(acc1);
        lits.push_back(ctx.get_literal(step));
        lits.push_back(~acc2);
        switch (ctx.get_assignment(acc2)) {
        case l_undef:
            propagate_lit(0, 2, lits.c_ptr(), acc2);
            break;
        case l_true:
            break;
        case l_false:
            set_conflict(0, lits);
            break;
        }
        break;
    }
    }
    return false;
}


/*
   rej(s, idx, re, i) & nth(s, idx) = t & idx < len(s) => rej(s, idx + 1, re, j)
   
   len(s) > idx -> s = (nth 0 s) ++ .. ++ (nth idx s) ++ (tail idx s)

Recall we also have:
   rej(s, idx, re, i) -> len(s) >= idx    if i is non-final
   rej(s, idx, re, i) -> len(s) > idx     if i is final

*/ 
bool theory_seq::add_reject2reject(expr* rej) {
    context& ctx = get_context();
    SASSERT(ctx.get_assignment(rej) == l_true);
    expr* s, *idx, *re;
    unsigned src;
    rational r;
    eautomaton* aut = 0;
    VERIFY(is_reject(rej, s, idx, re, src, aut));
    if (!aut || m_util.str.is_length(idx)) return false;
    VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());
    expr_ref idx1(m_autil.mk_int(r.get_unsigned() + 1), m);
    eautomaton::moves mvs;
    aut->get_moves_from(src, mvs);
    literal rej1 = ctx.get_literal(rej);
    expr_ref len(m_util.str.mk_length(s), m);
    literal len_le_idx = mk_literal(m_autil.mk_le(len, idx));
    switch (ctx.get_assignment(len_le_idx)) {
    case l_true: 
        return false;
    case l_undef:
        ctx.force_phase(len_le_idx);
        return true;
    default:
        break;
    }
    expr_ref nth = mk_nth(s, idx);        
    ensure_nth(~len_le_idx, s, idx);
    literal_vector eqs;
    bool has_undef = false;
    for (unsigned i = 0; i < mvs.size(); ++i) {
        eautomaton::move const& mv = mvs[i];        
        literal eq = mk_eq(nth, mv.t(), false);
        switch (ctx.get_assignment(eq)) {
        case l_false:
        case l_true:
            break;
        case l_undef:
            ctx.force_phase(~eq);
            has_undef = true;
            break;
        }
        eqs.push_back(eq);
    }
    if (has_undef) {
        return true;
    }
    for (unsigned i = 0; i < mvs.size(); ++i) {
        eautomaton::move const& mv = mvs[i];        
        literal eq = eqs[i];
        if (ctx.get_assignment(eq) == l_true) {
            literal rej2 = mk_reject(s, idx1, re, m_autil.mk_int(mv.dst()));
            add_axiom(~rej1, ~eq, len_le_idx, rej2);   
        }      
    }
    return false;
}

/*
  !prefix -> e2 = emp \/ nth(e1,0) != nth(e2,0) \/ !prefix(tail(e1),tail(e2))  
*/
bool theory_seq::add_prefix2prefix(expr* e) {
    context& ctx = get_context();
    expr* e1, *e2;
    VERIFY(m_util.str.is_prefix(e, e1, e2));
    SASSERT(ctx.get_assignment(e) == l_false);
    if (canonizes(false, e)) {
        return false;
    }
    expr_ref emp(m_util.str.mk_empty(m.get_sort(e1)), m);
    switch (assume_equality(e2, emp)) {
    case l_true:
        return false; // done
    case l_undef:
        return true;  // retry
    default:
        break;
    }
    expr_ref head1(m), tail1(m), head2(m), tail2(m);
    mk_decompose(e1, head1, tail1);
    mk_decompose(e2, head2, tail2);
    
    literal lit = mk_eq(head1, head2, false);
    switch (ctx.get_assignment(lit)) {
    case l_true: {
        literal_vector lits;
        lits.push_back(~ctx.get_literal(e));
        lits.push_back(~mk_eq(e2, emp, false));
        lits.push_back(lit);
        propagate_lit(0, lits.size(), lits.c_ptr(), ~mk_literal(m_util.str.mk_prefix(tail1, tail2)));
        return false;
    }
    case l_false:
        return false;
    case l_undef:
        ctx.force_phase(~lit);
        return true;
    }
    return true;
}

/*
  !suffix(e1, e2) -> e2 = emp \/ last(e1) != last(e2) \/ !suffix(first(e1), first(e2))
 */
bool theory_seq::add_suffix2suffix(expr* e) {
    context& ctx = get_context();
    expr* e1, *e2;
    VERIFY(m_util.str.is_suffix(e, e1, e2));
    SASSERT(ctx.get_assignment(e) == l_false);
    if (canonizes(false, e)) {
        return false;
    }

    expr_ref emp(m_util.str.mk_empty(m.get_sort(e1)), m);

    switch (assume_equality(e2, emp)) {
    case l_true:
        return false; // done
    case l_undef:
        ctx.force_phase(mk_eq(e2, emp, false));
        return true;  // retry
    case l_false:
        break;
    }
    expr_ref first2 = mk_skolem(m_seq_first, e2);
    expr_ref last2  = mk_last(e2);
    expr_ref first1 = mk_skolem(m_seq_first, e1);
    expr_ref last1  = mk_last(e1);
    expr_ref conc(m_util.str.mk_concat(first2, m_util.str.mk_unit(last2)), m);
    propagate_eq(~mk_eq(e2, emp, false), e2, conc);
    
    literal last_eq = mk_eq(last1, last2, false);
    switch (ctx.get_assignment(last_eq)) {
    case l_false:
        return false; // done
    case l_undef:
        ctx.force_phase(~last_eq);
        return true;
    case l_true:
        break;
    }

    literal_vector lits;
    lits.push_back(~ctx.get_literal(e));
    lits.push_back(~mk_eq(e2, emp, false));
    lits.push_back(last_eq);
    propagate_lit(0, lits.size(), lits.c_ptr(), ~mk_literal(m_util.str.mk_suffix(first1, first2)));
    return false;    
}

bool theory_seq::canonizes(bool sign, expr* e) {
    context& ctx = get_context();
    dependency* deps = 0;
    expr_ref cont = canonize(e, deps);
    TRACE("seq", tout << mk_pp(e, m) << " -> " << cont << "\n";);
    if ((m.is_true(cont) && !sign) ||
        (m.is_false(cont) && sign)) {
        propagate_lit(deps, 0, 0, ctx.get_literal(e));
        return true;
    }
    if ((m.is_false(cont) && !sign) ||
        (m.is_true(cont) && sign)) {
        return true;
    }
    return false;
}

/*
   !contains(e1, e2) -> !prefix(e2, e1)
   !contains(e1, e2) -> e1 = emp \/ !contains(tail(e1), e2)
 */

bool theory_seq::add_contains2contains(expr* e) {
    context& ctx = get_context();
    expr* e1, *e2;
    VERIFY(m_util.str.is_contains(e, e1, e2));
    SASSERT(ctx.get_assignment(e) == l_false);
    if (canonizes(false, e)) {
        return false;
    }
    expr_ref emp(m_util.str.mk_empty(m.get_sort(e1)), m);
    
    switch (assume_equality(e1, emp)) {
    case l_true:
        return false; // done
    case l_undef:
        return true;  // retry
    default:
        break;
    }
    expr_ref head(m), tail(m);
    mk_decompose(e1, head, tail);
    literal lits[2] = { ~ctx.get_literal(e), ~mk_eq(e1, emp, false) };
    propagate_lit(0, 2, lits, ~mk_literal(m_util.str.mk_contains(tail, e2)));
    return false;
}

bool theory_seq::propagate_automata() {
    context& ctx = get_context();
    if (m_atoms_qhead == m_atoms.size()) {
        return false;
    }
    m_trail_stack.push(value_trail<theory_seq, unsigned>(m_atoms_qhead));
    ptr_vector<expr> re_add;
    while (m_atoms_qhead < m_atoms.size() && !ctx.inconsistent()) {
        expr* e = m_atoms[m_atoms_qhead];
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        bool reQ = false;
        if (is_accept(e)) {
            reQ = add_accept2step(e);
        }
        else if (is_reject(e)) {
            reQ = add_reject2reject(e);
        }
        else if (is_step(e)) {
            reQ = add_step2accept(e);
        }
        else if (m_util.str.is_prefix(e)) {
            reQ = add_prefix2prefix(e);
        }
        else if (m_util.str.is_suffix(e)) {
            reQ = add_suffix2suffix(e);
        }
        else if (m_util.str.is_contains(e)) {
            reQ = add_contains2contains(e);
        }
        if (reQ) {
            re_add.push_back(e);
        }
        ++m_atoms_qhead;        
    }
    m_atoms.append(re_add);
    return true;
}
