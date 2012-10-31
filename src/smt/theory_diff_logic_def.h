/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_diff_logic_def.h

Abstract:

    Difference Logic

Author:

    Leonardo de Moura (leonardo) 2006-11-29.
    Nikolaj Bjorner (nbjorner) 2008-05-11

Revision History:

    2008-05-11 ported from v1.2. Add theory propagation.

--*/
#ifndef _THEORY_DIFF_LOGIC_DEF_H_
#define _THEORY_DIFF_LOGIC_DEF_H_

#include"theory_diff_logic.h"
#include"smt_context.h"
#include"map.h"
#include"ast_pp.h"
#include"warning.h"
#include"smt_model_generator.h"

using namespace smt;

template<typename Ext>
std::ostream& theory_diff_logic<Ext>::atom::display(theory_diff_logic const& th, std::ostream& out) const {
    context& ctx = th.get_context();
    lbool asgn = ctx.get_assignment(m_bvar);
    //SASSERT(asgn == l_undef || ((asgn == l_true) == m_true));
    bool sign = (l_undef == asgn) || m_true;
    return out << literal(m_bvar, sign) 
               << " " << mk_pp(ctx.bool_var2expr(m_bvar), th.get_manager()) << " "; 
}

template<typename Ext>
std::ostream& theory_diff_logic<Ext>::eq_atom::display(theory_diff_logic const& th, std::ostream& out) const {
    atom::display(th, out);
    lbool asgn = th.get_context().get_assignment(this->m_bvar);
    if (l_undef == asgn) {
        out << "unassigned\n";
    }
    else {
        out << mk_pp(m_le.get(), m_le.get_manager()) << " " 
            << mk_pp(m_ge.get(), m_ge.get_manager()) << "\n";
    }
    return out;
}

template<typename Ext>
std::ostream& theory_diff_logic<Ext>::le_atom::display(theory_diff_logic const& th, std::ostream& out) const { 
    atom::display(th, out);
    lbool asgn = th.get_context().get_assignment(this->m_bvar);
    if (l_undef == asgn) {
        out << "unassigned\n";
    }
    else {
        th.m_graph.display_edge(out, get_asserted_edge());
    }
    return out;
}

// -----------------------------------------
// theory_diff_logic::nc_functor

template<typename Ext>
void theory_diff_logic<Ext>::nc_functor::reset() {
    m_antecedents.reset();
}


// -----------------------------------------
// theory_diff_logic

template<typename Ext>
void theory_diff_logic<Ext>::init(context * ctx) {
    theory::init(ctx);
    app* zero;
    enode* e;
    zero = m_util.mk_numeral(rational(0), true);
    e = ctx->mk_enode(zero, false, false, true);
    SASSERT(!is_attached_to_var(e));
    m_zero_int = mk_var(e);

    zero = m_util.mk_numeral(rational(0), false);
    e = ctx->mk_enode(zero, false, false, true);
    SASSERT(!is_attached_to_var(e));
    m_zero_real = mk_var(e);

}


template<typename Ext>
bool theory_diff_logic<Ext>::internalize_term(app * term) {
    bool result = null_theory_var != mk_term(term);
    CTRACE("arith", !result, tout << "Did not internalize " << mk_pp(term, get_manager()) << "\n";);
    found_non_diff_logic_expr(term);
    return result;
}

template<typename numeral>
class diff_logic_bounds {
    bool m_inf_is_set;
    bool m_sup_is_set;
    bool m_eq_found;
    literal m_inf_l;
    literal m_sup_l;
    literal m_eq_l;
    numeral m_inf_w;
    numeral m_sup_w;
    numeral m_w;
    
public:
    diff_logic_bounds() {
        reset(numeral(0));
    }
    void reset(numeral const& w) {
        m_inf_is_set = false;
        m_sup_is_set = false;
        m_eq_found = false;
        m_inf_l = null_literal;
        m_sup_l = null_literal;
        m_eq_l = null_literal;
        m_w = w;
    }

    void operator()(numeral const& w, literal l) {
        if (l != null_literal) {
            if ((w < m_w) && (!m_inf_is_set || w > m_inf_w)) {
                m_inf_w = w;
                m_inf_l = l;
                m_inf_is_set = true;
            }
            else if ((w > m_w) && (!m_sup_is_set || w < m_sup_w)) {
                m_sup_w = w;
                m_sup_l = l;
                m_sup_is_set = true;
            }
            else if (w == m_w) {
                m_eq_found = true;
                m_eq_l = l;
            }
        }
    }

    bool get_inf(numeral& w, literal& l) const {
        w = m_inf_w;
        l = m_inf_l;
        return m_inf_is_set;
    }

    bool get_sup(numeral& w, literal& l) const {
        w = m_sup_w;
        l = m_sup_l;
        return m_sup_is_set;
    }
    
    bool get_eq(literal& l) const {
        l = m_eq_l;
        return m_eq_found;
    }
    
};

// 
// Atoms are of the form x +  -1*y <= k, or x + -1*y = k
//

template<typename Ext>
void theory_diff_logic<Ext>::found_non_diff_logic_expr(expr * n) {
    if (!m_non_diff_logic_exprs) {
        TRACE("non_diff_logic", tout << "found non diff logic expression:\n" << mk_pp(n, get_manager()) << "\n";);
        get_context().push_trail(value_trail<context, bool>(m_non_diff_logic_exprs));
        m_non_diff_logic_exprs = true;
    }
}

template<typename Ext>
bool theory_diff_logic<Ext>::internalize_atom(app * n, bool gate_ctx) {
    context & ctx = get_context();
    if (!m_util.is_le(n) && !m_util.is_ge(n)) {
        found_non_diff_logic_expr(n);
        return false;
    }
    SASSERT(m_util.is_le(n) || m_util.is_ge(n));
    SASSERT(!ctx.b_internalized(n));

    bool is_ge = m_util.is_ge(n);
    bool_var bv;
    rational kr;
    app * x, *y, *z;
    theory_var source, target; // target - source <= k
    app * lhs = to_app(n->get_arg(0));
    app * rhs = to_app(n->get_arg(1));
    if (!m_util.is_numeral(rhs)) {
        std::swap(rhs, lhs);
        is_ge = !is_ge;
    }
    if (!m_util.is_numeral(rhs, kr)) {
        found_non_diff_logic_expr(n);
        return false;
    }
    numeral k(kr);

    bool is_add = m_util.is_add(lhs) && lhs->get_num_args() == 2;

    if (is_add) {
        x = to_app(lhs->get_arg(0));
        y = to_app(lhs->get_arg(1));
    }

    if (is_add && is_negative(x, z)) {  
        target = mk_var(y);
        source = mk_var(z);
    }
    else if (is_add && is_negative(y, z)) {
        target = mk_var(x);
        source = mk_var(z);
    }
    else {
        target = mk_var(lhs);
        source = get_zero(lhs);
    }
    if (is_ge) {
        std::swap(target, source);
        k.neg();
    }

    bv = ctx.mk_bool_var(n);
    ctx.set_var_theory(bv, get_id());
    literal l(bv);

    // 
    // Create axioms for situations as:
    // x - y <= 5 => x - y <= 7
    //

    if (m_params.m_arith_add_binary_bounds) {
        literal l0;
        numeral k0;
        diff_logic_bounds<numeral> bounds;
        bounds.reset(k);
        m_graph.enumerate_edges(source, target, bounds);
        if (bounds.get_eq(l0)) {
            ctx.mk_th_axiom(get_id(),~l0,l);
            ctx.mk_th_axiom(get_id(),~l,l0);
        }
        else {
            if (bounds.get_inf(k0, l0)) {
                SASSERT(k0 <= k);
                ctx.mk_th_axiom(get_id(),~l0,l);
            }
            if (bounds.get_sup(k0, l0)) {
                SASSERT(k <= k0);
                ctx.mk_th_axiom(get_id(),~l,l0);
            }
        }
    }

    edge_id pos = m_graph.add_edge(source, target,  k, l);
    k.neg();
    if (m_util.is_int(lhs)) {
        SASSERT(k.is_int());
        k -= numeral(1);
    }
    else {
        m_is_lia = false;
        k -= this->m_epsilon; 
    }
    edge_id neg = m_graph.add_edge(target, source, k, ~l);
    le_atom * a = alloc(le_atom, bv, pos, neg);
    m_atoms.push_back(a);
    m_bool_var2atom.insert(bv, a);

    TRACE("arith", 
          tout << mk_pp(n, get_manager()) << "\n";
          m_graph.display_edge(tout << "pos: ", pos); 
          m_graph.display_edge(tout << "neg: ", neg); 
          );

    return true;
}

template<typename Ext>
void theory_diff_logic<Ext>::internalize_eq_eh(app * atom, bool_var v) {
    context & ctx  = get_context();
    app * lhs      = to_app(atom->get_arg(0));
    app * rhs      = to_app(atom->get_arg(1));
    app * s;
    if (m_util.is_add(lhs) && to_app(lhs)->get_num_args() == 2 && 
        is_negative(to_app(to_app(lhs)->get_arg(1)), s) && m_util.is_numeral(rhs)) {
        // force axioms for (= (+ x (* -1 y)) k)
        // this is necessary because (+ x (* -1 y)) is not a diff logic term.
        m_arith_eq_adapter.mk_axioms(ctx.get_enode(lhs), ctx.get_enode(rhs));
        return;
    }
    
    if (m_params.m_arith_eager_eq_axioms) {
        enode * n1 = ctx.get_enode(lhs);
        enode * n2 = ctx.get_enode(rhs);
        if (n1->get_th_var(get_id()) != null_theory_var &&
            n2->get_th_var(get_id()) != null_theory_var)
            m_arith_eq_adapter.mk_axioms(n1, n2);
    }
}


template<typename Ext>
void theory_diff_logic<Ext>::assign_eh(bool_var v, bool is_true) {
    m_stats.m_num_assertions++;
    atom * a = 0;
    m_bool_var2atom.find(v, a);
    SASSERT(a);
    SASSERT(get_context().get_assignment(v) != l_undef);
    SASSERT((get_context().get_assignment(v) == l_true) == is_true);    
    a->assign_eh(is_true);
    m_asserted_atoms.push_back(a);
}


template<typename Ext>
void theory_diff_logic<Ext>::collect_statistics(::statistics & st) const {
    st.update("dl conflicts", m_stats.m_num_conflicts);
    st.update("dl propagations", m_stats.m_num_th2core_prop);
    st.update("dl asserts", m_stats.m_num_assertions);
    st.update("core->dl eqs", m_stats.m_num_core2th_eqs);
    m_arith_eq_adapter.collect_statistics(st);
}

template<typename Ext>
void theory_diff_logic<Ext>::push_scope_eh() {

    theory::push_scope_eh();
    m_graph.push();
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_atoms_lim = m_atoms.size();
    s.m_asserted_atoms_lim = m_asserted_atoms.size();
    s.m_asserted_qhead_old = m_asserted_qhead;
}

template<typename Ext>
void theory_diff_logic<Ext>::pop_scope_eh(unsigned num_scopes) {
    unsigned lvl     = m_scopes.size();
    SASSERT(num_scopes <= lvl);
    unsigned new_lvl = lvl - num_scopes;
    scope & s        = m_scopes[new_lvl];
    del_atoms(s.m_atoms_lim);
    m_asserted_atoms.shrink(s.m_asserted_atoms_lim);
    m_asserted_qhead = s.m_asserted_qhead_old;
    m_scopes.shrink(new_lvl);
    m_graph.pop(num_scopes);
    theory::pop_scope_eh(num_scopes);
}

template<typename Ext>
final_check_status theory_diff_logic<Ext>::final_check_eh() {

    if (can_propagate()) {
        propagate_core();
        return FC_CONTINUE;
    }

    TRACE("arith_final", display(tout); );
    // either will already be zero (as we don't do mixed constraints).
    m_graph.set_to_zero(m_zero_int, m_zero_real);
    SASSERT(is_consistent());

    
#if 0
 TBD:
    if (propagate_cheap_equalities()) {
        return FC_CONTINUE;
    }
#endif

    if (m_non_diff_logic_exprs) {
        return FC_GIVEUP; 
    }

    return FC_DONE;
}


template<typename Ext>
void theory_diff_logic<Ext>::del_atoms(unsigned old_size) {
    typename atoms::iterator begin = m_atoms.begin() + old_size;
    typename atoms::iterator it    = m_atoms.end();
    while (it != begin) {
        --it;
        atom * a     = *it;
        bool_var bv  = a->get_bool_var();
        m_bool_var2atom.erase(bv);
        dealloc(a);
    }    
    m_atoms.shrink(old_size);
}



template<typename Ext>
bool theory_diff_logic<Ext>::is_negative(app* n, app*& m) { 
    expr* a0, *a1, *a2;
    rational r;
    if (!m_util.is_mul(n, a0, a1)) {
        return false;
    }
    if (m_util.is_numeral(a1)) {
        std::swap(a0, a1);
    }
    if (m_util.is_numeral(a0, r) && r.is_minus_one() && is_app(a1)) {
        m = to_app(a1);
        return true;
    }
    if (m_util.is_uminus(a1)) {
        std::swap(a0, a1);
    }
    if (m_util.is_uminus(a0, a2) && m_util.is_numeral(a2, r) && r.is_one() && is_app(a1)) {
        m = to_app(a1);
        return true;
    }
    return false;
}

template<typename Ext>
void theory_diff_logic<Ext>::propagate() {
    if (m_params.m_arith_adaptive) {

        switch(m_params.m_arith_propagation_strategy) {

        case ARITH_PROP_PROPORTIONAL: {

            ++m_num_propagation_calls;
            if (m_num_propagation_calls * (m_stats.m_num_conflicts + 1) > 
                m_params.m_arith_adaptive_propagation_threshold * get_context().m_stats.m_num_conflicts) {
                m_num_propagation_calls = 1;
                TRACE("arith_prop", tout << "propagating: " << m_num_propagation_calls << "\n";);
                propagate_core();            
            }
            else {
                TRACE("arith_prop", tout << "skipping propagation " << m_num_propagation_calls << "\n";);
            }
            break;
        }
        case ARITH_PROP_AGILITY: {
            // update agility with factor generated by other conflicts.

            double g = m_params.m_arith_adaptive_propagation_threshold;
            while (m_num_core_conflicts < get_context().m_stats.m_num_conflicts) {
                m_agility = m_agility*g;
                ++m_num_core_conflicts;
            }        
            ++m_num_propagation_calls;
            bool do_propagate = (m_num_propagation_calls * m_agility > m_params.m_arith_adaptive_propagation_threshold);
            TRACE("arith_prop", tout << (do_propagate?"propagating: ":"skipping ") 
                  << " " << m_num_propagation_calls 
                  << " agility: " << m_agility << "\n";);
            if (do_propagate) {
                m_num_propagation_calls = 0;
                propagate_core();
            }
            break;
        }
        default:
            UNREACHABLE();
            propagate_core();
        }
    }
    else {
        propagate_core();            
    }
}

template<typename Ext>
void theory_diff_logic<Ext>::inc_conflicts() {
     m_stats.m_num_conflicts++;   
     if (m_params.m_arith_adaptive) {
         double g = m_params.m_arith_adaptive_propagation_threshold;
         m_agility = m_agility*g + 1 - g;
     }
}

template<typename Ext>
void theory_diff_logic<Ext>::propagate_core() {
    bool consistent = true;
    while (consistent && can_propagate()) {
        atom * a = m_asserted_atoms[m_asserted_qhead];
        m_asserted_qhead++;
        consistent = propagate_atom(a);
    }
}

template<typename Ext>
bool theory_diff_logic<Ext>::propagate_atom(atom* a) {
    context& ctx = get_context();
    TRACE("arith", a->display(*this, tout); );
    if (ctx.inconsistent()) {
        return false;
    }
    switch(a->kind()) {
    case LE_ATOM: {
        int edge_id = dynamic_cast<le_atom*>(a)->get_asserted_edge();
        if (!m_graph.enable_edge(edge_id)) {
            set_neg_cycle_conflict();
            return false;
        }
#if 0
        if (m_params.m_arith_bound_prop != BP_NONE) {
            svector<int> subsumed;
            m_graph.find_subsumed1(edge_id, subsumed);
            for (unsigned i = 0; i < subsumed.size(); ++i) {
                int subsumed_edge_id = subsumed[i];
                literal l = m_graph.get_explanation(subsumed_edge_id);
                context & ctx = get_context();
                region& r = ctx.get_region();
                ++m_stats.m_num_th2core_prop;
                ctx.assign(l, new (r) implied_bound_justification(*this, subsumed_edge_id, edge_id));
            }

        }
#endif
        break;
    }
    case EQ_ATOM: 
        if (!a->is_true()) {
            SASSERT(ctx.get_assignment(a->get_bool_var()) == l_false);
            // eq_atom * ea = dynamic_cast<eq_atom*>(a);
        }
        break;
    }
    return true;
}



template<typename Ext>
void theory_diff_logic<Ext>::mark_as_modified_since_eq_prop() {
    if (!m_modified_since_eq_prop) {
        get_context().push_trail(value_trail<context, bool>(m_modified_since_eq_prop));
        m_modified_since_eq_prop = true;
    }
}

template<typename Ext>
void theory_diff_logic<Ext>::unmark_as_modified_since_eq_prop() {
    get_context().push_trail(value_trail<context, bool>(m_modified_since_eq_prop));
    m_modified_since_eq_prop = false;
}

template<typename Ext>
void theory_diff_logic<Ext>::del_clause_eh(clause* cls) {
    
}

template<typename Ext>
void theory_diff_logic<Ext>::new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {

    if (!theory_resolve()) {
        return;
    }

    TRACE("dl_activity", tout << "\n";);

    context& ctx = get_context();
    numeral w(0);
    for (unsigned i = 0; i < num_edges; ++i) {
        w += m_graph.get_weight(edges[i]);
    }
    enode* e1 = get_enode(src);
    enode* e2 = get_enode(dst);
    expr*  n1 = e1->get_owner();
    expr*  n2 = e2->get_owner();
    bool is_int = m_util.is_int(n1);
    rational num = w.get_rational().to_rational();

    expr_ref le(get_manager());
    if (w.is_rational()) {
        // x - y <= w
        expr*  n3 = m_util.mk_numeral(num, is_int);
        n2 = m_util.mk_mul(m_util.mk_numeral(rational(-1), is_int), n2);
        le = m_util.mk_le(m_util.mk_add(n1,n2), n3);
    }
    else {
        //     x - y < w 
        // <=> 
        //     not (x - y >= w)
        // <=>
        //     not (y - x <= -w)
        //
        SASSERT(w.get_infinitesimal().is_neg());
        expr*  n3 = m_util.mk_numeral(-num, is_int);
        n1 = m_util.mk_mul(m_util.mk_numeral(rational(-1), is_int), n1);
        le = m_util.mk_le(m_util.mk_add(n2,n1), n3);
        le = get_manager().mk_not(le);
    }
    ctx.internalize(le, false);
    ctx.mark_as_relevant(le.get());
    literal lit(ctx.get_literal(le));
    bool_var bv = lit.var();
    atom* a = 0;
    m_bool_var2atom.find(bv, a);
    SASSERT(a);
    edge_id e_id = static_cast<le_atom*>(a)->get_pos();

    literal_vector lits;
    for (unsigned i = 0; i < num_edges; ++i) {
        lits.push_back(~m_graph.get_explanation(edges[i]));        
    }
    lits.push_back(lit);

    TRACE("dl_activity", 
          tout << mk_pp(le, get_manager()) << "\n";
          tout << "edge: " << e_id << "\n";
          ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr());
          tout << "\n";
          );

    justification * js = 0;
    if (get_manager().proofs_enabled()) {
        vector<parameter> params;
        params.push_back(parameter(symbol("farkas")));
        params.resize(lits.size()+1, parameter(rational(1)));
        js = new (ctx.get_region()) theory_lemma_justification(get_id(), ctx, 
                   lits.size(), lits.c_ptr(), 
                   params.size(), params.c_ptr());
    }
    clause_del_eh* del_eh = alloc(theory_diff_logic_del_eh, *this);
    clause* cls = ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, del_eh);
    if (!cls) {
        dealloc(del_eh);
    }
    if (dump_lemmas()) {
        char const * logic = m_is_lia ? "QF_LIA" : "QF_LRA";
        ctx.display_lemma_as_smt_problem(lits.size(), lits.c_ptr(), false_literal, logic);
    }

#if 0
    TRACE("arith",
          tout << "shortcut:\n";
          for (unsigned i = 0; i < num_edges; ++i) {
              edge_id e = edges[i];
              // tgt <= src + w
              numeral w = m_graph.get_weight(e);
              dl_var tgt = m_graph.get_target(e);
              dl_var src = m_graph.get_source(e);
              if (i + 1 < num_edges) {
                  dl_var tgt2 = m_graph.get_target(edges[i+1]);
                  SASSERT(src == tgt2);
              }        
              tout << "$" << tgt << " <= $" << src << " + " << w << "\n";
          }
          {
              numeral w = m_graph.get_weight(e_id);
              dl_var tgt = m_graph.get_target(e_id);
              dl_var src = m_graph.get_source(e_id);
              tout << "$" << tgt << " <= $" << src << " + " << w << "\n";
          }
          );
#endif

}

template<typename Ext>
void theory_diff_logic<Ext>::set_neg_cycle_conflict() {
    m_nc_functor.reset();
    m_graph.traverse_neg_cycle2(m_params.m_arith_stronger_lemmas, m_nc_functor);
    inc_conflicts();
    literal_vector const& lits = m_nc_functor.get_lits();
    context & ctx = get_context();
    TRACE("arith_conflict", 
          //display(tout);
          tout << "conflict: ";
          for (unsigned i = 0; i < lits.size(); ++i) {
              ctx.display_literal_info(tout, lits[i]);
          }
          tout << "\n";
          );

    if (dump_lemmas()) {
        char const * logic = m_is_lia ? "QF_LIA" : "QF_LRA";
        ctx.display_lemma_as_smt_problem(lits.size(), lits.c_ptr(), false_literal, logic);
    }

    vector<parameter> params;
    if (get_manager().proofs_enabled()) {
        params.push_back(parameter(symbol("farkas")));
        params.resize(lits.size()+1, parameter(rational(1)));
    } 
   
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), 
                lits.size(), lits.c_ptr(), 0, 0, params.size(), params.c_ptr())));

}

template<typename Ext>
bool theory_diff_logic<Ext>::is_offset(app* n, app*& v, app*& offset, rational& r) {
    if (!m_util.is_add(n)) {
        return false;
    }

    if (n->get_num_args() == 2 && m_util.is_numeral(n->get_arg(0), r)) {
        v = to_app(n->get_arg(1));
        offset = to_app(n->get_arg(0));
        return true;
    }
    if (n->get_num_args() == 2 && m_util.is_numeral(n->get_arg(1), r)) {
        v = to_app(n->get_arg(0));
        offset = to_app(n->get_arg(1));
        return true;
    }
    return false;
}

template<typename Ext>
theory_var theory_diff_logic<Ext>::mk_term(app* n) {
    SASSERT(!m_util.is_sub(n));
    SASSERT(!m_util.is_uminus(n));
    app* a, *offset;
    theory_var source, target;
    enode* e;

    TRACE("arith", tout << mk_pp(n, get_manager()) << "\n";);

    rational r;
    if (m_util.is_numeral(n, r)) {
        return mk_num(n, r);
    }
    else if (is_offset(n, a, offset, r)) {
        // n = a + k
        source = mk_var(a);
        e = get_context().mk_enode(n, false, false, true);
        target = mk_var(e);
        numeral k(r);
        // target - source <= k, source - target <= -k 
        m_graph.enable_edge(m_graph.add_edge(source, target, k, null_literal));
        m_graph.enable_edge(m_graph.add_edge(target, source, -k, null_literal));        
        return target;
    }
    else if (m_util.is_add(n)) {
        return null_theory_var;
    }
    else if (m_util.is_mul(n)) {
        return null_theory_var;
    }
    else if (m_util.is_div(n)) {
        return null_theory_var;
    }
    else if (m_util.is_idiv(n)) {
        return null_theory_var;
    }
    else if (m_util.is_mod(n)) {
        return null_theory_var;
    }
    else if (m_util.is_rem(n)) {
        return null_theory_var;
    }
    else {
        return mk_var(n);
    }
}


template<typename Ext>
theory_var theory_diff_logic<Ext>::mk_num(app* n, rational const& r) {
    theory_var v = null_theory_var;
    enode* e = 0;
    context& ctx = get_context();
    if (r.is_zero()) {
        v = get_zero(n);
    }
    else if (ctx.e_internalized(n)) {
        e = ctx.get_enode(n);
        v = e->get_th_var(get_id());
        SASSERT(v != null_theory_var);
    }
    else {
        theory_var zero = get_zero(n);
        e = ctx.mk_enode(n, false, false, true);
        v = mk_var(e);
        // internalizer is marking enodes as interpreted whenever the associated ast is a value and a constant.
        // e->mark_as_interpreted();
        numeral k(r);
        // v = k: v - zero <= k, zero - v <= - k
        m_graph.enable_edge(m_graph.add_edge(zero, v, k, null_literal));
        m_graph.enable_edge(m_graph.add_edge(v, zero, -k, null_literal));
    }
    return v;
}


template<typename Ext>
theory_var theory_diff_logic<Ext>::mk_var(enode* n) {
    mark_as_modified_since_eq_prop();
    theory_var v = theory::mk_var(n);
    TRACE("diff_logic_vars", tout << "mk_var: " << v << "\n";);
    m_graph.init_var(v);
    get_context().attach_th_var(n, this, v);
    return v;
}

template<typename Ext>
bool theory_diff_logic<Ext>::is_interpreted(app* n) const {
    return n->get_family_id() == get_family_id();
}

template<typename Ext>
theory_var theory_diff_logic<Ext>::mk_var(app* n) {
    context & ctx = get_context();
    enode* e = 0;
    theory_var v = null_theory_var;
    if (ctx.e_internalized(n)) {
        e = ctx.get_enode(n);
        v = e->get_th_var(get_id());
    }
    else {
        ctx.internalize(n, false);
        e = ctx.get_enode(n);
    }
    if (v == null_theory_var) {
        v = mk_var(e);
    }      
    if (is_interpreted(n)) {
        found_non_diff_logic_expr(n);
    }
    TRACE("arith", tout << mk_pp(n, get_manager()) << " |-> " << v << "\n";);
    return v;
}




template<typename Ext>
void theory_diff_logic<Ext>::reset_eh() {
    for (unsigned i = 0; i < m_atoms.size(); ++i) {
        dealloc(m_atoms[i]);
    }
    m_graph            .reset();
    m_zero_int          = null_theory_var;
    m_zero_real         = null_theory_var;
    m_atoms            .reset();
    m_asserted_atoms   .reset();
    m_stats            .reset();
    m_scopes           .reset();
    m_modified_since_eq_prop = false;
    m_asserted_qhead        = 0;
    m_num_core_conflicts    = 0;
    m_num_propagation_calls = 0;
    m_agility               = 0.5;
    m_is_lia                = true;
    m_non_diff_logic_exprs  = false;
    theory::reset_eh();
}


template<typename Ext>
bool theory_diff_logic<Ext>::propagate_cheap_equalities() {
    bool result = false;
    TRACE("dl_new_eq", get_context().display(tout););
    context& ctx = get_context();
    region&  reg = ctx.get_region();
    SASSERT(m_eq_prop_info_set.empty());
    SASSERT(m_eq_prop_infos.empty());
    if (m_modified_since_eq_prop) {
        m_graph.compute_zero_edge_scc(m_scc_id);
        int n = get_num_vars();
        for (theory_var v = 0; v < n; v++) {
            rational delta_r;
            theory_var x_v = expand(true, v, delta_r);
            numeral delta(delta_r);
            int scc_id = m_scc_id[x_v];
            if (scc_id != -1) {
                delta += m_graph.get_assignment(x_v);
                TRACE("eq_scc", tout << v << " " << x_v << " " << scc_id << " " << delta << "\n";);
                eq_prop_info info(scc_id, delta);
                typename eq_prop_info_set::entry * entry = m_eq_prop_info_set.find_core(&info);
                if (entry == 0) {
                    eq_prop_info * new_info = alloc(eq_prop_info, scc_id, delta, v);
                    m_eq_prop_info_set.insert(new_info);
                    m_eq_prop_infos.push_back(new_info);
                }
                else {
                    // new equality found
                    theory_var r = entry->get_data()->get_root();
                    
                    enode * n1 = get_enode(v);
                    enode * n2 = get_enode(r);
                    if (n1->get_root() != n2->get_root()) {
                        // r may be an alias (i.e., it is not realy in the graph). So, I should expand it. 
                        // nsb: ?? 
                        rational r_delta;
                        theory_var x_r = expand(true, r, r_delta);
                        
                        justification* j = new (reg) implied_eq_justification(*this, x_v, x_r, m_graph.get_timestamp());
                        (void)j;

                        m_stats.m_num_th2core_eqs++;
                        // TBD: get equality into core.

                        NOT_IMPLEMENTED_YET();
                        // new_eq_eh(x_v, x_r, *j);
                        result = true;
                    }
                }
            }
        }
        m_eq_prop_info_set.reset();
        std::for_each(m_eq_prop_infos.begin(), m_eq_prop_infos.end(), delete_proc<eq_prop_info>());
        m_eq_prop_infos.reset();
        unmark_as_modified_since_eq_prop();        
    }

    TRACE("dl_new_eq", get_context().display(tout););
    SASSERT(!m_modified_since_eq_prop);

    return result;
}


template<typename Ext>
void theory_diff_logic<Ext>::compute_delta() {
    m_delta = rational(1);
    unsigned num_edges = m_graph.get_num_edges();
    for (unsigned i = 0; i < num_edges; ++i) {
        if (!m_graph.is_enabled(i)) {
            continue;
        }
        numeral w = m_graph.get_weight(i);
        dl_var tgt = m_graph.get_target(i);
        dl_var src = m_graph.get_source(i);
        rational n_x = m_graph.get_assignment(tgt).get_rational().to_rational();
        rational k_x = m_graph.get_assignment(tgt).get_infinitesimal().to_rational();
        rational n_y = m_graph.get_assignment(src).get_rational().to_rational();
        rational k_y = m_graph.get_assignment(src).get_infinitesimal().to_rational();
        rational n_c = w.get_rational().to_rational();
        rational k_c = w.get_infinitesimal().to_rational();
        TRACE("epsilon", tout << "(n_x,k_x): " << n_x << ", " << k_x << ", (n_y,k_y): " 
              << n_y << ", " << k_y << ", (n_c,k_c): " << n_c << ", " << k_c << "\n";);
        if (n_x < n_y + n_c && k_x > k_y + k_c) {
            rational new_delta = (n_y + n_c - n_x) / (k_x - k_y - k_c);
            if (new_delta < m_delta) {
                TRACE("epsilon", tout << "new delta: " << new_delta << "\n";);
                m_delta = new_delta;
            }
        }
    }
}


template<typename Ext>
void theory_diff_logic<Ext>::init_model(smt::model_generator & m) {
    m_factory = alloc(arith_factory, get_manager());
    m.register_factory(m_factory);
    compute_delta();
}
        

template<typename Ext>
model_value_proc * theory_diff_logic<Ext>::mk_value(enode * n, model_generator & mg) {
    theory_var v = n->get_th_var(get_id());
    SASSERT(v != null_theory_var);
    numeral val = m_graph.get_assignment(v);
    rational num = val.get_rational().to_rational() + m_delta * val.get_infinitesimal().to_rational();
    TRACE("arith", tout << mk_pp(n->get_owner(), get_manager()) << " |-> " << num << "\n";);
    return alloc(expr_wrapper_proc, m_factory->mk_value(num, m_util.is_int(n->get_owner())));
}

template<typename Ext>
bool theory_diff_logic<Ext>::validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
    NOT_IMPLEMENTED_YET();
    return true;
}


template<typename Ext>
void theory_diff_logic<Ext>::display(std::ostream & out) const {
    for (unsigned i = 0; i < m_atoms.size(); ++i) {
        m_atoms[i]->display(*this, out);
    }
    m_graph.display(out);
}

template<typename Ext>
bool theory_diff_logic<Ext>::is_consistent() const {
    context& ctx = get_context();
    for (unsigned i = 0; i < m_atoms.size(); ++i) {
        atom* a = m_atoms[i];
        bool_var bv = a->get_bool_var();
        lbool asgn = ctx.get_assignment(bv);        
        if (ctx.is_relevant(ctx.bool_var2expr(bv)) && asgn != l_undef) {
            SASSERT((asgn == l_true) == a->is_true());
            switch(a->kind()) {
            case LE_ATOM: {
                le_atom* le = dynamic_cast<le_atom*>(a);
                int edge_id = le->get_asserted_edge();
                SASSERT(m_graph.is_enabled(edge_id));
                SASSERT(m_graph.is_feasible(edge_id));
                break;
            }
            case EQ_ATOM: {
                eq_atom* ea = dynamic_cast<eq_atom*>(a);
                bool_var bv1 = ctx.get_bool_var(ea->get_le());                    
                bool_var bv2 = ctx.get_bool_var(ea->get_ge());
                lbool val1 = ctx.get_assignment(bv1);
                lbool val2 = ctx.get_assignment(bv2);
                if (asgn == l_true) {
                    SASSERT(val1 == l_true);
                    SASSERT(val2 == l_true);
                }
                else {
                    SASSERT(val1 == l_false || val2 == l_false);
                }
                break;
            }
            }
        }
    }
    return m_graph.is_feasible();
}


template<class Ext>
theory_var theory_diff_logic<Ext>::expand(bool pos, theory_var v, rational & k) {
    context& ctx = get_context();
    enode* e = get_enode(v);
    rational r;
    for (;;) {
        app* n = e->get_owner();
        if (m_util.is_add(n) && n->get_num_args() == 2) {
            app* x = to_app(n->get_arg(0));
            app* y = to_app(n->get_arg(1));
            if (m_util.is_numeral(x, r)) {
                e = ctx.get_enode(y);                
            }
            else if (m_util.is_numeral(y, r)) {
                e = ctx.get_enode(x);
            }
            v = e->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            if (v == null_theory_var) {
                break;
            }
            if (pos) {
                k += r;
            }
            else {
                k -= r;
            }
        }
        else {
            break;
        }
    }
    return v;
}

template<typename Ext>
void theory_diff_logic<Ext>::new_eq_or_diseq(bool is_eq, theory_var v1, theory_var v2, justification& eq_just) {
    rational k;
    theory_var s = expand(true,  v1, k);
    theory_var t = expand(false, v2, k);
    context& ctx = get_context();
    ast_manager& m = get_manager();

    if (s == t) {
        if (is_eq != k.is_zero()) {
            // conflict 0 /= k;
            inc_conflicts();
            ctx.set_conflict(&eq_just);            
        }
    }
    else {
        //
        // Create equality ast, internalize_atom
        // assign the corresponding equality literal.
        //

        mark_as_modified_since_eq_prop();

        app_ref eq(m), s2(m), t2(m);
        app* s1 = get_enode(s)->get_owner();
        app* t1 = get_enode(t)->get_owner();
        s2 = m_util.mk_sub(t1, s1);
        t2 = m_util.mk_numeral(k, m.get_sort(s2.get()));
        // t1 - s1 = k
        eq = m.mk_eq(s2.get(), t2.get());
        
        TRACE("diff_logic", 
              tout << v1 << " .. " << v2 << "\n";
              tout << mk_pp(eq.get(), m) <<"\n";);

        if (!internalize_atom(eq.get(), false)) {
            UNREACHABLE();
        }
                
        literal l(ctx.get_literal(eq.get()));
        if (!is_eq) {
            l = ~l;
        }

        ctx.assign(l, b_justification(&eq_just), false);
    }
}

template<typename Ext>
void theory_diff_logic<Ext>::new_eq_eh(
    theory_var v1, theory_var v2, justification& j) {
    m_stats.m_num_core2th_eqs++;
    new_eq_or_diseq(true, v1, v2, j);
}


template<typename Ext>
void theory_diff_logic<Ext>::new_diseq_eh(
    theory_var v1, theory_var v2, justification& j) {
    m_stats.m_num_core2th_diseqs++;
    new_eq_or_diseq(false, v1, v2, j);    
}


template<typename Ext>
void theory_diff_logic<Ext>::new_eq_eh(theory_var v1, theory_var v2) {
    m_arith_eq_adapter.new_eq_eh(v1, v2);
}


template<typename Ext>
void theory_diff_logic<Ext>::new_diseq_eh(theory_var v1, theory_var v2) {
    m_arith_eq_adapter.new_diseq_eh(v1, v2);
}


template<typename Ext>
void theory_diff_logic<Ext>::relevant_eh(app* e) {
}


struct imp_functor {
    conflict_resolution & m_cr;
    imp_functor(conflict_resolution& cr) : m_cr(cr) {}
    void operator()(literal l) {
        m_cr.mark_literal(l);
    }
};

template<typename Ext>
void theory_diff_logic<Ext>::get_eq_antecedents(
    theory_var v1, theory_var v2, unsigned timestamp, conflict_resolution & cr) {
    imp_functor functor(cr);
    bool r;
    r = m_graph.find_shortest_zero_edge_path(v1, v2, timestamp, functor);
    SASSERT(r);
    r = m_graph.find_shortest_zero_edge_path(v2, v1, timestamp, functor);
    SASSERT(r);
}

template<typename Ext>
void theory_diff_logic<Ext>::get_implied_bound_antecedents(edge_id bridge_edge, edge_id subsumed_edge, conflict_resolution & cr) {
    imp_functor f(cr);
    m_graph.explain_subsumed_lazy(bridge_edge, subsumed_edge, f);
}

#endif /* _THEORY_DIFF_LOGIC_DEF_H_ */

