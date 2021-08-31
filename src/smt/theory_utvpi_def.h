/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_utvpi_def.h

Abstract:

    Implementation of UTVPI solver.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26

Revision History:

 1. introduce x^+ and x^-, such that 2*x := x^+ - x^-
 2. rewrite constraints as follows:

   x - y <= k    =>  x^+ - y^+ <= k
                     y^- - x^- <= k

   x <= k        =>  x^+ - x^- <= 2k


   x + y <= k    =>  x^+ - y^- <= k
                     y^+ - x^- <= k


   - x - y <= k  =>   x^- - y^+ <= k
                      y^- - x^+ <= k

 3. Solve for x^+ and x^-
 4. Check parity condition for integers (see Lahiri and Musuvathi 05)
    This checks if x^+ and x^- are in the same component but of different
    parities.
 5. Enforce parity on variables. This checks if x^+ and x^- have different
    parities. If they have different parities, the assignment to one  
    of the variables is decremented (choose the variable that is not tightly
    constrained with 0). 
    The process that adjusts parities converges: Suppose we break a parity
    of a different variable y while fixing x's parity. A cyclic breaking/fixing
    of parities implies there is a strongly connected component between x, y
    and the two polarities of the variables. This contradicts the test in 4.
 6. extract model for M(x) := (M(x^+)- M(x^-))/2

--*/

#pragma once
#include "smt/theory_utvpi.h"
#include "util/heap.h"
#include "ast/ast_pp.h"
#include "smt/smt_context.h"

namespace smt {


    template<typename Ext>
    theory_utvpi<Ext>::theory_utvpi(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("arith")),
        a(ctx.get_manager()),
        m_arith_eq_adapter(*this, a),
        m_consistent(true),
        m_izero(null_theory_var),
        m_rzero(null_theory_var),
        m_nc_functor(*this),
        m_asserted_qhead(0),
        m_agility(0.5),
        m_lia(false),
        m_lra(false),
        m_non_utvpi_exprs(false),
        m_test(ctx.get_manager()),
        m_factory(nullptr),
        m_var_value_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)) {
        }            

    template<typename Ext>
    theory_utvpi<Ext>::~theory_utvpi() {
        reset_eh();
    }                

    template<typename Ext>
    std::ostream& theory_utvpi<Ext>::atom::display(theory_utvpi const& th, std::ostream& out) const { 
        context& ctx = th.get_context();
        lbool asgn = ctx.get_assignment(m_bvar);
        bool sign = (l_undef == l_false);
        return out << literal(m_bvar, sign) << " " << mk_pp(ctx.bool_var2expr(m_bvar), th.get_manager()) << " ";         
        if (l_undef == asgn) {
            out << "unassigned\n";
        }
        else {
            th.m_graph.display_edge(out, get_asserted_edge());
        }
        return out;
    }

    template<typename Ext>
    theory_var theory_utvpi<Ext>::mk_var(enode* n) {
        th_var v = theory::mk_var(n);
        TRACE("utvpi", tout << v << " " << mk_pp(n->get_expr(), m) << "\n";);
        m_graph.init_var(to_var(v));
        m_graph.init_var(neg(to_var(v)));
        ctx.attach_th_var(n, this, v);
        return v;
    }
    
    template<typename Ext>
    theory_var theory_utvpi<Ext>::mk_var(expr* n) {
        enode* e = nullptr;
        th_var v = null_theory_var;
        m_lia |= a.is_int(n);
        m_lra |= a.is_real(n);
        if (!is_app(n)) {
            return v;
        }
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
        if (is_interpreted(to_app(n))) {
            found_non_utvpi_expr(n);
        }
        return v;
    }

    template<typename Ext>
    void theory_utvpi<Ext>::reset_eh() {
        m_graph            .reset();
        m_izero              = null_theory_var;
        m_rzero              = null_theory_var;
        m_atoms            .reset();
        m_asserted_atoms   .reset();
        m_stats            .reset();
        m_scopes           .reset();
        m_asserted_qhead    = 0;
        m_agility           = 0.5;
        m_lia               = false;
        m_lra               = false;
        m_non_utvpi_exprs   = false;
        theory::reset_eh();
    }    

    template<typename Ext>
    void theory_utvpi<Ext>::new_eq_or_diseq(bool is_eq, th_var v1, th_var v2, justification& eq_just) {
        rational k(0);
        th_var s = expand(true,  v1, k);
        th_var t = expand(false, v2, k);
        
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
            // t1 - s1 = k
            //
                        
            app_ref eq(m), s2(m), t2(m);
            app* s1 = get_enode(s)->get_expr();
            app* t1 = get_enode(t)->get_expr();
            s2 = a.mk_sub(t1, s1);
            t2 = a.mk_numeral(k, s2->get_sort());
            eq = m.mk_eq(s2.get(), t2.get());
            
            TRACE("utvpi", tout << v1 << " .. " << v2 << "\n" << eq << "\n";);
            
            VERIFY (internalize_atom(eq.get(), false));
            
            literal l(ctx.get_literal(eq.get()));
            if (!is_eq) {
                l.neg();
            }            
            ctx.assign(l, b_justification(&eq_just), false);
        }
    }

    template<typename Ext>
    void theory_utvpi<Ext>::inc_conflicts() {
        ctx.push_trail(value_trail<bool>(m_consistent));
        m_consistent = false;
        m_stats.m_num_conflicts++;   
        if (m_params.m_arith_adaptive) {
            double g = m_params.m_arith_adaptive_propagation_threshold;
            m_agility = m_agility*g + 1 - g;
        }
    }

    template<typename Ext>
    void theory_utvpi<Ext>::set_conflict() {
        inc_conflicts();
        literal_vector const& lits = m_nc_functor.get_lits();
        IF_VERBOSE(20, ctx.display_literals_smt2(verbose_stream() << "conflict:\n", lits));
        TRACE("utvpi", ctx.display_literals_smt2(tout << "conflict:\n", lits););
        
        if (m_params.m_arith_dump_lemmas) {
            symbol logic(m_lra ? (m_lia?"QF_LIRA":"QF_LRA") : "QF_LIA");
            ctx.display_lemma_as_smt_problem(lits.size(), lits.data(), false_literal, logic);
        }
        
        vector<parameter> params;
        if (m.proofs_enabled()) {
            params.push_back(parameter(symbol("farkas")));
            for (unsigned i = 0; i < m_nc_functor.get_coeffs().size(); ++i) {
                params.push_back(parameter(rational(m_nc_functor.get_coeffs()[i])));
            }
        } 
        
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(), 
                    lits.size(), lits.data(), 0, nullptr, params.size(), params.data())));

        m_nc_functor.reset();
    }

    template<typename Ext>
    void theory_utvpi<Ext>::found_non_utvpi_expr(expr* n) {
        if (m_non_utvpi_exprs) {
            return;
        }
        std::stringstream msg;
        msg << "found non utvpi logic expression:\n" << mk_pp(n, m) << '\n';
        auto str = msg.str();
        TRACE("utvpi", tout << str;);
        warning_msg("%s", str.c_str());
        ctx.push_trail(value_trail<bool>(m_non_utvpi_exprs));
        m_non_utvpi_exprs = true;        
    }

    template<typename Ext>
    void theory_utvpi<Ext>::init_zero() {
        if (m_izero == null_theory_var) {
            m_izero  = mk_var(ctx.mk_enode(a.mk_numeral(rational(0), true), false, false, true));
            m_rzero  = mk_var(ctx.mk_enode(a.mk_numeral(rational(0), false), false, false, true));
        }
    }

    /**
       \brief Create negated literal.
       
       The negation of: E <= 0

       -E + epsilon <= 0
       or
       -E + 1 <= 0
     */
    template<typename Ext>
    void theory_utvpi<Ext>::negate(coeffs& coeffs, rational& weight) {
        for (auto& c : coeffs) {
            c.second.neg();
        }
        weight.neg();
    }    

    template<typename Ext>
    typename theory_utvpi<Ext>::numeral theory_utvpi<Ext>::mk_weight(bool is_real, bool is_strict, rational const& w) const {
        if (is_strict) {
            return numeral(w) + (is_real?Ext::m_epsilon:numeral(1));
        }
        else {
            return numeral(w);
        }
    }

    template<typename Ext>
    void theory_utvpi<Ext>::mk_coeffs(vector<std::pair<expr*,rational> > const& terms, coeffs& coeffs, rational& w) {
        coeffs.reset();
        w = m_test.get_weight();
        for (auto const& t : terms) {
            coeffs.push_back(std::make_pair(mk_var(t.first), t.second));
        }
    }

    template<typename Ext>
    void theory_utvpi<Ext>::internalize_eq_eh(app * atom, bool_var v) {
        app * lhs      = to_app(atom->get_arg(0));
        app * rhs      = to_app(atom->get_arg(1));
        if (a.is_numeral(rhs)) {
            std::swap(rhs, lhs);
        }
        if (!a.is_numeral(rhs)) {
            return;
        }
        if (a.is_add(lhs) || a.is_sub(lhs)) {
            // force axioms for (= (+ x y) k)
            // this is necessary because (+ x y) is not expressible as a utvpi term.
            m_arith_eq_adapter.mk_axioms(ctx.get_enode(lhs), ctx.get_enode(rhs));
        }
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::internalize_atom(app * n, bool) {
        if (!m_consistent)
            return false;
        if (!a.is_le(n) && !a.is_ge(n) && !a.is_lt(n) && !a.is_gt(n)) {
            found_non_utvpi_expr(n);
            return false;
        }
        SASSERT(!ctx.b_internalized(n));
        expr* e1 = n->get_arg(0), *e2 = n->get_arg(1);
        if (a.is_ge(n) || a.is_gt(n)) {
            std::swap(e1, e2);
        }
        bool is_strict = a.is_gt(n) || a.is_lt(n);

        bool cl = m_test.linearize(e1, e2);
        if (!cl) {
            found_non_utvpi_expr(n);
            return false;
        }

        rational w;
        coeffs coeffs;
        mk_coeffs(m_test.get_linearization(), coeffs, w);

        if (coeffs.empty()) {
            found_non_utvpi_expr(n);
            return false;
        }

        bool_var bv = ctx.mk_bool_var(n);
        ctx.set_var_theory(bv, get_id());
        literal l(bv);
        m_bool_var2atom.insert(bv, m_atoms.size());

        numeral w1 = mk_weight(a.is_real(e1), is_strict, w);
        edge_id pos = add_ineq(coeffs, w1, l);        
        negate(coeffs, w);
        numeral w2 = mk_weight(a.is_real(e1), !is_strict, w);
        edge_id neg = add_ineq(coeffs, w2, ~l);
        m_atoms.push_back(atom(bv, pos, neg));
        
        TRACE("utvpi", 
              tout << mk_pp(n, m) << "\n";
              m_graph.display_edge(tout << "pos: ", pos); 
              m_graph.display_edge(tout << "neg: ", neg); 
              );
        
        return true;
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::internalize_term(app * term) {
        if (!m_consistent)
            return false;
        bool result = !ctx.inconsistent() && null_theory_var != mk_term(term);
        CTRACE("utvpi", !result, tout << "Did not internalize " << mk_pp(term, m) << "\n";);
        return result;
    }

    template<typename Ext>
    void theory_utvpi<Ext>::assign_eh(bool_var v, bool is_true) {
        m_stats.m_num_assertions++;
        unsigned idx = m_bool_var2atom.find(v);
        SASSERT(ctx.get_assignment(v) != l_undef);
        SASSERT((ctx.get_assignment(v) == l_true) == is_true);    
        m_atoms[idx].assign_eh(is_true);
        m_asserted_atoms.push_back(idx);   
    }

    template<typename Ext>
    void theory_utvpi<Ext>::push_scope_eh() {
        theory::push_scope_eh();
        m_graph.push();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        s.m_atoms_lim = m_atoms.size();
        s.m_asserted_atoms_lim = m_asserted_atoms.size();
        s.m_asserted_qhead_old = m_asserted_qhead;
    }

    template<typename Ext>
    void theory_utvpi<Ext>::pop_scope_eh(unsigned num_scopes) {
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
    final_check_status theory_utvpi<Ext>::final_check_eh() {
        SASSERT(is_consistent());
        if (can_propagate()) {
            propagate();
            return FC_CONTINUE;
        }        
        else if (!check_z_consistency()) {
            return FC_CONTINUE;
        }
        else if (has_shared() && assume_eqs_core()) {
            return FC_CONTINUE;
        }
        else if (m_non_utvpi_exprs) {
            return FC_GIVEUP;
        }
        else {
            return FC_DONE;
        }
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::has_shared() {
        auto sz = static_cast<theory_var>(get_num_vars());
        for (theory_var v = 0; v < sz; ++v) {
            if (is_relevant_and_shared(get_enode(v)))
                return true;
        }
        return false;
    }


    template<typename Ext>
    bool theory_utvpi<Ext>::check_z_consistency() {
        int_vector scc_id;
        m_graph.compute_zero_edge_scc(scc_id);
        
        unsigned sz = get_num_vars();
        for (unsigned i = 0; i < sz; ++i) {
            enode* e = get_enode(i);
            if (!a.is_int(e->get_expr())) {
                continue;
            }
            th_var v1 = to_var(i);
            th_var v2 = neg(v1);
            rational r1 = m_graph.get_assignment(v1).get_rational();
            rational r2 = m_graph.get_assignment(v2).get_rational();
            SASSERT(r1.is_int());
            SASSERT(r2.is_int());
            if (r1.is_even() == r2.is_even()) {
                continue;
            }
            if (scc_id[v1] != scc_id[v2]) {
                continue;
            }
            if (scc_id[v1] == -1) {
                continue;
            }
            // they are in the same SCC and have different parities => contradiction.
            m_nc_functor.reset();
            VERIFY(m_graph.find_shortest_zero_edge_path(v1, v2, UINT_MAX, m_nc_functor));
            VERIFY(m_graph.find_shortest_zero_edge_path(v2, v1, UINT_MAX, m_nc_functor));
            IF_VERBOSE(1, verbose_stream() << "parity conflict " << mk_pp(e->get_expr(), m) << "\n";);
            set_conflict();
                        
            return false;            
        }
        return true;
    }

    template<typename Ext>
    void theory_utvpi<Ext>::display(std::ostream& out) const {
        for (auto const& a : m_atoms) {
            a.display(*this, out); out << "\n";
        }
        m_graph.display(out);        
    }

    template<typename Ext>
    void theory_utvpi<Ext>::collect_statistics(::statistics& st) const {
        st.update("utvpi conflicts",   m_stats.m_num_conflicts);
        st.update("utvpi asserts", m_stats.m_num_assertions);
        st.update("core->utvpi eqs", m_stats.m_num_core2th_eqs);
        st.update("core->utvpi diseqs", m_stats.m_num_core2th_diseqs);
        m_arith_eq_adapter.collect_statistics(st);
        m_graph.collect_statistics(st);
    }

    template<typename Ext>
    void theory_utvpi<Ext>::del_atoms(unsigned old_size) {
        typename atoms::iterator begin = m_atoms.begin() + old_size;
        typename atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            m_bool_var2atom.erase(it->get_bool_var());
        }    
        m_atoms.shrink(old_size);
    }

    template<typename Ext>
    void theory_utvpi<Ext>::propagate() {
        bool consistent = is_consistent() && !ctx.inconsistent();
        while (consistent && can_propagate()) {
            unsigned idx = m_asserted_atoms[m_asserted_qhead];
            m_asserted_qhead++;
            consistent = propagate_atom(m_atoms[idx]);            
        }
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::propagate_atom(atom const& a) {
        TRACE("utvpi", a.display(*this, tout); tout << "\n";);       
        int edge_id = a.get_asserted_edge();
        if (!enable_edge(edge_id)) {
            m_graph.traverse_neg_cycle2(m_params.m_arith_stronger_lemmas, m_nc_functor);
            set_conflict();
            return false;
        }
        return true;
    }
    
    template<typename Ext>
    theory_var theory_utvpi<Ext>::mk_term(app* n) {
        TRACE("utvpi", tout << mk_pp(n, m) << "\n";);
        
        bool cl = m_test.linearize(n);
        if (!cl) {
            found_non_utvpi_expr(n);
            return null_theory_var;
        }

        coeffs coeffs;
        rational w;
        mk_coeffs(m_test.get_linearization(), coeffs, w);
        if (coeffs.empty()) {
            return mk_num(n, w);
        }
        if (coeffs.size() == 1 && coeffs[0].second.is_one() && ctx.e_internalized(n)) {
            return coeffs[0].first;
        }
        if (coeffs.size() == 2) {
            // do not create an alias.
            found_non_utvpi_expr(n);
            return null_theory_var;
        }
        for (expr* arg : *n) {
            if (!ctx.e_internalized(arg))
                ctx.internalize(arg, false);
        }
        th_var target = mk_var(ctx.mk_enode(n, false, false, true));
        coeffs.push_back(std::make_pair(target, rational(-1)));

        VERIFY(enable_edge(add_ineq(coeffs, numeral(w), null_literal)));        
        negate(coeffs, w);
        VERIFY(enable_edge(add_ineq(coeffs, numeral(w), null_literal)));
        return target;
    }
    
    template<typename Ext>
    theory_var theory_utvpi<Ext>::mk_num(app* n, rational const& r) {
        theory_var v = null_theory_var;
        if (r.is_zero()) {            
            v = get_zero(n);
            if (!ctx.e_internalized(n)) {
                found_non_utvpi_expr(n);
                v = null_theory_var;
            }
        }
        else if (ctx.e_internalized(n)) {
            enode* e = ctx.get_enode(n);
            v = e->get_th_var(get_id());
            SASSERT(v != null_theory_var);
        }
        else {
            for (expr* arg : *n) {
                if (!ctx.e_internalized(arg))
                    ctx.internalize(arg, false);
            }
            v = mk_var(ctx.mk_enode(n, false, false, true));
            // v = k: v <= k k <= v
            coeffs coeffs;
            coeffs.push_back(std::make_pair(v, rational(-1)));
            VERIFY(enable_edge(add_ineq(coeffs, numeral(r), null_literal)));
            coeffs.back().second.neg();
            VERIFY(enable_edge(add_ineq(coeffs, numeral(-r), null_literal)));
        }
        return v;
    }

    template<typename Ext>
    theory_var theory_utvpi<Ext>::expand(bool pos, th_var v, rational & k) {
        enode* e = get_enode(v);
        expr* x, *y;
        rational r;
        for (;;) {
            app* n = e->get_expr();
            if (a.is_add(n, x, y)) {
                if (a.is_numeral(x, r)) {
                    e = ctx.get_enode(y);                
                }
                else if (a.is_numeral(y, r)) {
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

    // m_graph(source, target, weight, ex);
    // target - source <= weight

    template<typename Ext>
    edge_id theory_utvpi<Ext>::add_ineq(vector<std::pair<th_var, rational> > const& terms, numeral const& weight, literal l) {

        SASSERT(!terms.empty());
        SASSERT(terms.size() <= 2);
        SASSERT(terms.size() < 1 || terms[0].second.is_one() || terms[0].second.is_minus_one());
        SASSERT(terms.size() < 2 || terms[1].second.is_one() || terms[1].second.is_minus_one());
        
        th_var v1 = null_theory_var, v2 = null_theory_var;
        bool   pos1 = true, pos2 = true;
        if (!terms.empty()) {
            v1 = terms[0].first;
            pos1 = terms[0].second.is_one();
            SASSERT(v1 != null_theory_var);
            SASSERT(pos1 || terms[0].second.is_minus_one());
        }
        if (terms.size() >= 2) {
            v2 = terms[1].first;
            pos2 = terms[1].second.is_one();
            SASSERT(v2 != null_theory_var);
            SASSERT(pos2 || terms[1].second.is_minus_one());
        }            
        TRACE("utvpi", tout << (pos1?"$":"-$") << v1;
              if (terms.size() == 2) tout << (pos2?" + $":" - $") << v2;
              tout << " + " << weight << " <= 0\n";);
        edge_id id = m_graph.get_num_edges();
        th_var w1 = to_var(v1), w2 = to_var(v2);

        if (terms.size() == 1 && pos1) {
            m_graph.add_edge(neg(w1), pos(w1), -weight-weight, std::make_pair(l,2));
            m_graph.add_edge(neg(w1), pos(w1), -weight-weight, std::make_pair(l,2));
        }
        else if (terms.size() == 1 && !pos1) {
            m_graph.add_edge(pos(w1), neg(w1), -weight-weight, std::make_pair(l,2));
            m_graph.add_edge(pos(w1), neg(w1), -weight-weight, std::make_pair(l,2));
        }
        else if (pos1 && pos2) {
            m_graph.add_edge(neg(w2), pos(w1), -weight, std::make_pair(l,1));
            m_graph.add_edge(neg(w1), pos(w2), -weight, std::make_pair(l,1));
        }
        else if (pos1 && !pos2) {
            m_graph.add_edge(pos(w2), pos(w1), -weight, std::make_pair(l,1));
            m_graph.add_edge(neg(w1), neg(w2), -weight, std::make_pair(l,1));
        }
        else if (!pos1 && pos2) {
            m_graph.add_edge(neg(w2), neg(w1), -weight, std::make_pair(l,1));
            m_graph.add_edge(pos(w1), pos(w2), -weight, std::make_pair(l,1));
        }
        else {
            m_graph.add_edge(pos(w1), neg(w2), -weight, std::make_pair(l,1));
            m_graph.add_edge(pos(w2), neg(w1), -weight, std::make_pair(l,1));
        }        
        return id;
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::enable_edge(edge_id id) {
        return
            (id == null_edge_id) ||
            (m_graph.enable_edge(id) && m_graph.enable_edge(id + 1));
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::is_consistent() const {        
        return m_consistent;
    }


    template<typename Ext>
    bool theory_utvpi<Ext>::is_parity_ok(unsigned i) const {
        th_var v1 = to_var(i);
        th_var v2 = neg(v1);
        rational r1 = m_graph.get_assignment(v1).get_rational();
        rational r2 = m_graph.get_assignment(v2).get_rational();
        return r1.is_even() == r2.is_even();
    }

 
    /**
       \brief adjust values for variables in the difference graph
              such that for variables of integer sort it is
              the case that x^+ - x^- is even.
       The informal justification for the procedure enforce_parity relies
       on a set of properties:
       1. the graph does not contain a strongly connected component where
          x^+ and x+- are connected. They can be independently changed.
          This is checked prior to enforce_parity.
       2. When x^+ - x^- is odd, the values are adjusted by first 
          decrementing the value of x^+, provided x^- is not 0-dependent.
          Otherwise decrement x^-. 
          x^- is "0-dependent" if there is a set of tight 
          inequalities from x^+ to x^-.
       3. The affinity to x^+ (the same component of x^+) ensures that 
          the parity is broken only a finite number of times when 
          traversing that component. Namely, suppose that the parity of y
          gets broken when fixing 'x'. Then first note that 'y' cannot 
          be equal to 'x'. If it were, then we have a state where:
             parity(x^+) != parity(x^-) and 
             parity(y^+) == parity(y^-)
          but x^+ and y^+ are tightly connected and x^- and y^- are
          also tightly connected using two copies of the same inequalities.
          This is a contradiction.
          Thus, 'y' cannot be equal to 'x' if 'y's parity gets broken when
          repairing 'x'.
                 
     */
    template<typename Ext>
    void theory_utvpi<Ext>::enforce_parity() {
        SASSERT(m_graph.is_feasible_dbg());
        unsigned_vector todo;        
        unsigned sz = get_num_vars();
        for (unsigned i = 0; i < sz; ++i) {
            enode* e = get_enode(i);
            if (a.is_int(e->get_expr()) && !is_parity_ok(i)) {
                todo.push_back(i);
            }            
        }
        if (todo.empty()) {
            return;
        }
        while (!todo.empty()) {
            unsigned i = todo.back();
            todo.pop_back();
            if (is_parity_ok(i)) {
                continue;
            }
            th_var v1 = to_var(i);
            th_var v2 = neg(v1);

            int_vector zero_v;
            m_graph.compute_zero_succ(v1, zero_v);
            for (auto v0 : zero_v) {
                if (v0 == v2) {
                    zero_v.reset();
                    m_graph.compute_zero_succ(v2, zero_v);
                    break;
                }
            }

            TRACE("utvpi", 
                  tout << "Disparity: " << v1 << " - " << v2 << "\n";
                  tout << "decrement: " << zero_v << "\n";
                  display(tout);
                  );

            for (auto v : zero_v) {                
                m_graph.inc_assignment(v, numeral(-1));
                th_var k = from_var(v);
                if (!is_parity_ok(k)) {
                    todo.push_back(k);
                }
            }    
            TRACE("utvpi", display(tout););
            SASSERT(m_graph.is_feasible_dbg());     
        }
        DEBUG_CODE(
            for (unsigned i = 0; i < sz; ++i) {
                enode* e = get_enode(i);
                if (a.is_int(e->get_expr()) && !is_parity_ok(i)) {
                    IF_VERBOSE(0, verbose_stream() << "disparities not fixed\n";);
                    UNREACHABLE();
                }            
            });
        SASSERT(m_graph.is_feasible_dbg());
    }
    

    // models:
    template<typename Ext>
    void theory_utvpi<Ext>::init_model(model_generator & m) {            
        m_factory = alloc(arith_factory, get_manager());
        m.register_factory(m_factory);
        init_model();
    }

    template<typename Ext>
    void theory_utvpi<Ext>::init_model() {            
        enforce_parity();
        init_zero();
        dl_var vs[4] = { to_var(m_izero), neg(to_var(m_izero)), to_var(m_rzero), neg(to_var(m_rzero)) };
        m_graph.set_to_zero(4, vs);
        compute_delta();   
        DEBUG_CODE(model_validate(););
    }

    template<typename Ext>
    bool theory_utvpi<Ext>::assume_eqs_core() {
        init_model();
        return assume_eqs(m_var_value_table);
    }


    template<typename Ext>    
    void theory_utvpi<Ext>::model_validate() {
        for (auto const& a : m_atoms) {
            bool_var b = a.get_bool_var();
            if (!ctx.is_relevant(b)) {
                continue;
            }
            bool ok = true;
            expr* e = ctx.bool_var2expr(b);
            lbool assign = ctx.get_assignment(b);
            switch(assign) {
            case l_true:
                ok = eval(e);
                break;
            case l_false:
                ok = !eval(e);
                break;
            default:
                break;
            }
            (void)ok;
            CTRACE("utvpi", !ok, 
                   tout << "validation failed:\n";
                   tout << "Assignment: " << assign << "\n";
                   tout << mk_pp(e, m) << "\n";
                   a.display(*this, tout);
                   tout << "\n";
                   display(tout);
                   m_graph.display_agl(tout);
                   );
            // CTRACE("utvpi",  ok, tout << "validation success: " << mk_pp(e, m) << "\n";);
            SASSERT(ok);
        }
    }

    template<typename Ext>    
    bool theory_utvpi<Ext>::eval(expr* e) {
        expr* e1, *e2;
        if (a.is_le(e, e1, e2) || a.is_ge(e, e2, e1)) {
            return eval_num(e1) <= eval_num(e2);
        }
        if (a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) {
            return eval_num(e1) < eval_num(e2);
        }
        if (m.is_eq(e, e1, e2)) {
            return eval_num(e1) == eval_num(e2);
        }
        TRACE("utvpi", tout << "expression not handled: " << mk_pp(e, m) << "\n";);
        return false;
    }

    template<typename Ext>    
    rational theory_utvpi<Ext>::eval_num(expr* e) {
        rational r;
        expr* e1, *e2;
        if (a.is_numeral(e, r)) {
            return r;
        }
        if (a.is_sub(e, e1, e2)) {
            return eval_num(e1) - eval_num(e2);
        }
        if (a.is_add(e)) {
            r.reset();
            for (expr* arg : *to_app(e)) r+= eval_num(arg);
            return r;
        }
        if (a.is_mul(e)) {
            r = rational(1);
            for (expr* arg : *to_app(e)) r*= eval_num(arg);
            return r;
        }
        if (a.is_uminus(e, e1)) {
            return -eval_num(e1);
        }
        if (a.is_to_real(e, e1)) {
            return eval_num(e1);
        }
        if (is_uninterp_const(e)) {
            return mk_value(mk_var(e), a.is_int(e));
        }
        TRACE("utvpi", tout << "expression not handled: " << mk_pp(e, m) << "\n";);
        UNREACHABLE();
        return rational(0);
    }


    template<typename Ext>    
    rational theory_utvpi<Ext>::mk_value(th_var v, bool is_int) {
        SASSERT(v != null_theory_var);
        numeral val1 = m_graph.get_assignment(to_var(v));
        numeral val2 = m_graph.get_assignment(neg(to_var(v)));
        numeral val = val1 - val2;
        rational num = val.get_rational() + (m_delta * val.get_infinitesimal().to_rational());
        num = num/rational(2);
        SASSERT(!is_int || num.is_int());
        TRACE("utvpi", 
              expr* n = get_enode(v)->get_expr();
              tout << mk_pp(n, m) << " |-> (" << val1 << " - " << val2 << ")/2 = " << num << "\n";);

        return num;
    }
    
    template<typename Ext>    
    model_value_proc * theory_utvpi<Ext>::mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        bool is_int = a.is_int(n->get_expr());
        rational num = mk_value(v, is_int);
        TRACE("utvpi", tout << mk_pp(n->get_expr(), m) << " |-> " << num << "\n";);
        return alloc(expr_wrapper_proc, m_factory->mk_num_value(num, is_int));
    }

    /**
       \brief Compute numeral values for the infinitesimals to satisfy the inequalities.
     */

    template<typename Ext>
    void theory_utvpi<Ext>::compute_delta() {
        m_delta = rational(1,4);
        unsigned sz = m_graph.get_num_edges();

        for (unsigned i = 0; i < sz; ++i) {
            if (!m_graph.is_enabled(i)) {
                continue;
            }
            numeral w = m_graph.get_weight(i);
            numeral tgt = m_graph.get_assignment(m_graph.get_target(i));
            numeral src = m_graph.get_assignment(m_graph.get_source(i));
            numeral b = tgt - src - w;
            SASSERT(b.is_nonpos());
            rational eps_r = b.get_infinitesimal();

            // Given: b <= 0
            // suppose that 0 < b.eps
            // then we have 0 > b.num
            // then delta must ensure: 
            //      0 >= b.num + delta*b.eps
            // <=>
            //      -b.num/b.eps >= delta
            if (eps_r.is_pos()) {
                rational num_r = -b.get_rational();
                SASSERT(num_r.is_pos());
                rational new_delta = num_r/(4*eps_r);
                if (new_delta < m_delta) {
                    m_delta = new_delta;
                }
            }
        }
    }

    template<typename Ext>
    theory* theory_utvpi<Ext>::mk_fresh(context* new_ctx) { 
        return alloc(theory_utvpi<Ext>, *new_ctx); 
    }


};


