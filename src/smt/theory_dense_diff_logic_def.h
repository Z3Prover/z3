/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_dense_diff_logic_def.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-16.

Revision History:

--*/
#ifndef THEORY_DENSE_DIFF_LOGIC_DEF_H_
#define THEORY_DENSE_DIFF_LOGIC_DEF_H_

#include"smt_context.h"
#include"theory_dense_diff_logic.h"
#include"ast_pp.h"
#include"smt_model_generator.h"
#include"simplex.h"
#include"simplex_def.h"

namespace smt {

    template<typename Ext>
    theory_dense_diff_logic<Ext>::theory_dense_diff_logic(ast_manager & m, theory_arith_params & p):
        theory(m.mk_family_id("arith")),
        m_params(p),
        m_autil(m),
        m_arith_eq_adapter(*this, p, m_autil),
        m_non_diff_logic_exprs(false),
        m_var_value_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)) {
        m_edges.push_back(edge());
    }

    template<typename Ext>
    theory* theory_dense_diff_logic<Ext>::mk_fresh(context * new_ctx) { 
        return alloc(theory_dense_diff_logic<Ext>, new_ctx->get_manager(), m_params); 
    }

    template<typename Ext>
    inline app * theory_dense_diff_logic<Ext>::mk_zero_for(expr * n) {
        return m_autil.mk_numeral(rational(0), get_manager().get_sort(n));
    }

    template<typename Ext>
    theory_var theory_dense_diff_logic<Ext>::mk_var(enode * n) {
        theory_var v = theory::mk_var(n);
        bool is_int  = m_autil.is_int(n->get_owner());
        m_is_int.push_back(is_int);
        m_f_targets.push_back(f_target());
        typename matrix::iterator it  = m_matrix.begin();
        typename matrix::iterator end = m_matrix.end();
        for (; it != end; ++it) {
            it->push_back(cell());
        }
        m_matrix.push_back(row());
        row & r = m_matrix.back();
        SASSERT(r.empty());
        r.resize(v+1);
        cell & c    = m_matrix[v][v];
        c.m_edge_id = self_edge_id;
        c.m_distance.reset();
        SASSERT(check_vector_sizes());
        get_context().attach_th_var(n, this, v);
        return v;
    }

    template<typename Ext>
    theory_var theory_dense_diff_logic<Ext>::internalize_term_core(app * n) {
        context & ctx = get_context();
        if (ctx.e_internalized(n)) {
            enode * e    = ctx.get_enode(n);
            if (is_attached_to_var(e))
                return e->get_th_var(get_id());
        }

        rational _k;
        if (m_autil.is_add(n) && to_app(n)->get_num_args() == 2 && m_autil.is_numeral(to_app(n)->get_arg(0), _k)) {
            numeral k(_k);
            if (m_params.m_arith_reflect)
                internalize_term_core(to_app(to_app(n)->get_arg(0)));
            theory_var s = internalize_term_core(to_app(to_app(n)->get_arg(1)));
            enode * e    = ctx.mk_enode(n, !m_params.m_arith_reflect, false, true);
            theory_var v = mk_var(e);
            add_edge(s, v, k, null_literal);
            k.neg();
            add_edge(v, s, k, null_literal);
            return v;
        }
        else if (m_autil.is_numeral(n, _k)) {
            enode * e    = ctx.mk_enode(n, false, false, true);
            // internalizer is marking enodes as interpreted whenever the associated ast is a value and a constant.
            // e->mark_as_interpreted();
            theory_var v = mk_var(e);
            if (_k.is_zero()) 
                return v;
            theory_var z = internalize_term_core(mk_zero_for(n));
            numeral k(_k);
            add_edge(z, v, k, null_literal);
            k.neg();
            add_edge(v, z, k, null_literal);
            return v;
        }
        else if (!m_autil.is_arith_expr(n)) {
            if (!ctx.e_internalized(n))
                ctx.internalize(n, false);
            enode * e    = ctx.get_enode(n);
            if (!is_attached_to_var(e))
                return mk_var(e);
            else
                return e->get_th_var(get_id());
        }
        else {
            return null_theory_var;
        }
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::found_non_diff_logic_expr(expr * n) {
        if (!m_non_diff_logic_exprs) {
            TRACE("non_diff_logic", tout << "found non diff logic expression:\n" << mk_pp(n, get_manager()) << "\n";);
            get_context().push_trail(value_trail<context, bool>(m_non_diff_logic_exprs));
        IF_VERBOSE(0, verbose_stream() << "(smt.diff_logic: non-diff logic expression " << mk_pp(n, get_manager()) << ")\n";); 
            m_non_diff_logic_exprs = true;
        }
    }
                          
    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::internalize_atom(app * n, bool gate_ctx) {
        if (memory::above_high_watermark()) {
            found_non_diff_logic_expr(n); // little hack... TODO: change to no_memory and return l_undef if SAT
            return false;
        }
        TRACE("ddl", tout << "internalizing atom:\n" << mk_pp(n, get_manager()) << "\n";);
        context & ctx = get_context();
        SASSERT(!ctx.b_internalized(n));
        SASSERT(m_autil.is_le(n) || m_autil.is_ge(n));
        theory_var source, target;
        SASSERT(m_autil.is_le(n) || m_autil.is_ge(n));
        app * lhs      = to_app(n->get_arg(0));
        app * rhs      = to_app(n->get_arg(1));
        SASSERT(m_autil.is_numeral(rhs));
        rational _k;
        m_autil.is_numeral(rhs, _k);
        numeral offset(_k);
        app * s, * t;
        if (m_autil.is_add(lhs) && to_app(lhs)->get_num_args() == 2 && is_times_minus_one(to_app(lhs)->get_arg(1), s)) {
            t = to_app(to_app(lhs)->get_arg(0));
        }
        else if (m_autil.is_mul(lhs) && to_app(lhs)->get_num_args() == 2 && m_autil.is_minus_one(to_app(lhs)->get_arg(0))) {
            s = to_app(to_app(lhs)->get_arg(1));
            t = mk_zero_for(s);
        }
        else if (!m_autil.is_arith_expr(lhs)) {
            t = to_app(lhs);
            s = mk_zero_for(t);
        }
        else {
            TRACE("ddl", tout << "failed to internalize:\n" << mk_pp(n, get_manager()) << "\n";);
            found_non_diff_logic_expr(n);
            return false;
        }
        source = internalize_term_core(s);
        target = internalize_term_core(t);
        if (source == null_theory_var || target == null_theory_var) {
            TRACE("ddl", tout << "failed to internalize:\n" << mk_pp(n, get_manager()) << "\n";);
            found_non_diff_logic_expr(n);
            return false;
        }
        SASSERT(source != null_theory_var && target != null_theory_var);
        if (m_autil.is_ge(n)) {
            std::swap(source, target);
            offset.neg();
        }
        bool_var bv = ctx.mk_bool_var(n);
        ctx.set_var_theory(bv, get_id());
        atom * a    = alloc(atom, bv, source, target, offset);
        m_atoms.push_back(a);
        m_bv2atoms.setx(bv, a, 0);
        m_matrix[source][target].m_occs.push_back(a);
        m_matrix[target][source].m_occs.push_back(a);
        TRACE("ddl", tout << "succeeded internalizing:\n" << mk_pp(n, get_manager()) << "\n";);
        return true;
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::mk_clause(literal l1, literal l2) {
        get_context().mk_th_axiom(get_id(), l1, l2);
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::mk_clause(literal l1, literal l2, literal l3) {
        get_context().mk_th_axiom(get_id(), l1, l2, l3);
    }

    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::internalize_term(app * term) {
        if (memory::above_high_watermark()) {
            found_non_diff_logic_expr(term); // little hack... TODO: change to no_memory and return l_undef if SAT
            return false;
        }
        TRACE("ddl", tout << "internalizing term: " << mk_pp(term, get_manager()) << "\n";);
        theory_var v = internalize_term_core(term);
        TRACE("ddl", tout << mk_pp(term, get_manager()) << "\ninternalization result: " << (v != null_theory_var) << "\n";);
        if (v == null_theory_var)
            found_non_diff_logic_expr(term);
        return v != null_theory_var;
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::internalize_eq_eh(app * atom, bool_var v) {
        if (memory::above_high_watermark())
            return;
        context & ctx  = get_context();
        app * lhs      = to_app(atom->get_arg(0));
        app * rhs      = to_app(atom->get_arg(1));
        app * s;
        if (m_autil.is_add(lhs) && to_app(lhs)->get_num_args() == 2 && is_times_minus_one(to_app(lhs)->get_arg(1), s) 
            && m_autil.is_numeral(rhs)) {
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
    void theory_dense_diff_logic<Ext>::apply_sort_cnstr(enode * n, sort * s) {
        // do nothing...
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::assign_eh(bool_var v, bool is_true) {
        if (get_context().has_th_justification(v, get_id())) {
            TRACE("ddl", tout << "ignoring atom propagated by the theory.\n";);
            return;
        }
        atom * a = m_bv2atoms.get(v, 0);
        if (!a) {
            SASSERT(get_manager().is_eq(get_context().bool_var2expr(v)));
            return;
        }
        m_stats.m_num_assertions++;
        literal l    = literal(v, !is_true);
        theory_var s = a->get_source();
        theory_var t = a->get_target();
        numeral  k   = a->get_offset();
        TRACE("assign_profile", tout << "#" << get_enode(s)->get_owner_id() << " #" << get_enode(t)->get_owner_id() << " " << k << "\n";);
        if (l.sign()) {
            k.neg();
            k -= get_epsilon(s);
            add_edge(t, s, k, l);
        }
        else {
            add_edge(s, t, k, l);
        }
        TRACE("ddl_detail", display(tout););
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::new_eq_eh(theory_var v1, theory_var v2) {
        m_arith_eq_adapter.new_eq_eh(v1, v2);
    }

    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::use_diseqs() const {
        return true;
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::new_diseq_eh(theory_var v1, theory_var v2) {
        m_arith_eq_adapter.new_diseq_eh(v1, v2);
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::conflict_resolution_eh(app * atom, bool_var v) {
        // do nothing
    }
    
    template<typename Ext>
    void theory_dense_diff_logic<Ext>::push_scope_eh() {
        theory::push_scope_eh();
        m_scopes.push_back(scope());
        scope & s          = m_scopes.back();
        s.m_atoms_lim      = m_atoms.size();
        s.m_edges_lim      = m_edges.size();
        s.m_cell_trail_lim = m_cell_trail.size();
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::pop_scope_eh(unsigned num_scopes) {
        unsigned lvl     = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl = lvl - num_scopes;
        scope & s        = m_scopes[new_lvl];
        restore_cells(s.m_cell_trail_lim);
        m_edges.shrink(s.m_edges_lim);
        del_atoms(s.m_atoms_lim);
        del_vars(get_old_num_vars(num_scopes));
        m_scopes.shrink(new_lvl);
        theory::pop_scope_eh(num_scopes);
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::restore_cells(unsigned old_size) {
        unsigned sz = m_cell_trail.size();
        unsigned i  = sz;
        while (i > old_size) {
            i--;
            cell_trail & t = m_cell_trail[i];
            cell & c       = m_matrix[t.m_source][t.m_target];
            c.m_edge_id    = t.m_old_edge_id;
            c.m_distance   = t.m_old_distance;
        }
        m_cell_trail.shrink(old_size);
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::del_atoms(unsigned old_size) {
        typename atoms::iterator begin = m_atoms.begin() + old_size;
        typename atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            atom * a                      = *it;
            TRACE("del_atoms", tout << "deleting: p" << a->get_bool_var() << "\n";);
            m_bv2atoms[a->get_bool_var()] = 0;
            theory_var s = a->get_source();
            theory_var t = a->get_target();
            TRACE("del_atoms", tout << "m_matrix.size() " << m_matrix.size() << 
                  ", m_matrix[s].size() " << m_matrix[s].size() <<
                  ", m_matrix[t].size(): " << m_matrix[t].size() <<
                  ", t: " << t << ", s: " << s << "\n";);
            SASSERT(m_matrix[s][t].m_occs.back() == a);
            SASSERT(m_matrix[t][s].m_occs.back() == a);
            m_matrix[s][t].m_occs.pop_back();
            m_matrix[t][s].m_occs.pop_back();
            dealloc(a);
        } 
        m_atoms.shrink(old_size);
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::del_vars(unsigned old_num_vars) {
        int num_vars = get_num_vars();
        SASSERT(num_vars >= static_cast<int>(old_num_vars));
        if (num_vars != static_cast<int>(old_num_vars)) {
            m_is_int.shrink(old_num_vars);
            m_f_targets.shrink(old_num_vars);
            m_matrix.shrink(old_num_vars);
            typename matrix::iterator it  = m_matrix.begin();
            typename matrix::iterator end = m_matrix.end();
            for (; it != end; ++it) {
                it->shrink(old_num_vars);
            }
        }
    }
        
    template<typename Ext>
    void theory_dense_diff_logic<Ext>::restart_eh() {
        m_arith_eq_adapter.restart_eh();
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::init_search_eh() {
        m_arith_eq_adapter.init_search_eh();
    }

    template<typename Ext>
    final_check_status theory_dense_diff_logic<Ext>::final_check_eh() {
        init_model();
        if (assume_eqs(m_var_value_table))
            return FC_CONTINUE;
        // logical context contains arithmetic expressions that are not
        // in the difference logic fragment.
        if (m_non_diff_logic_exprs)
            return FC_GIVEUP; 
        return FC_DONE;
    }
        
    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::can_propagate() {
        // do nothing
        return false; 
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::propagate() {
        // do nothing
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::flush_eh() {
        // do nothing
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::reset_eh() {
        del_atoms(0);
        m_atoms      .reset();
        m_bv2atoms   .reset();
        m_edges      .reset();
        m_matrix     .reset();
        m_is_int     .reset();
        m_f_targets  .reset();
        m_cell_trail .reset();
        m_scopes     .reset();
        m_non_diff_logic_exprs = false;
        m_edges.push_back(edge());
        theory::reset_eh();
    }
    
    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
        return is_true ? m_assignment[v1] == m_assignment[v2] : m_assignment[v1] != m_assignment[v2];
    }

    /**
       \brief Store in results the antecedents that justify that the distance between source and target.
    */
    template<typename Ext>
    void theory_dense_diff_logic<Ext>::get_antecedents(theory_var source, theory_var target, literal_vector & result) {
        TRACE("ddl", tout << "get_antecedents, source: #" << get_enode(source)->get_owner_id() << ", target: #" << get_enode(target)->get_owner_id() << "\n";);
        CTRACE("ddl", !is_connected(source, target), display(tout););
        SASSERT(is_connected(source, target));
        svector<var_pair> & todo = m_tmp_pairs;
        todo.reset();

        if (source != target)
            todo.push_back(var_pair(source, target));

        while (!todo.empty()) {
            var_pair & curr = todo.back();
            theory_var s    = curr.first;
            theory_var t    = curr.second;
            todo.pop_back();
        
            SASSERT(is_connected(s, t));
            cell & c        = m_matrix[s][t];
            SASSERT(c.m_edge_id != self_edge_id);
            
            edge & e    = m_edges[c.m_edge_id];
            if (e.m_justification != null_literal)
                result.push_back(e.m_justification);
            
            if (s != e.m_source)
                todo.push_back(var_pair(s, e.m_source));
            if (e.m_target != t)
                todo.push_back(var_pair(e.m_target, t));
        }
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::update_cells() {
        edge_id new_edge_id = m_edges.size() - 1;
        edge & last         = m_edges.back();
        theory_var s        = last.m_source;
        theory_var t        = last.m_target;
        numeral const & k   = last.m_offset;

        // Compute set F of nodes such that:
        // x in F iff
        //    k + d(t, x) < d(s, x)
        
        numeral new_dist;
        row & t_row                = m_matrix[t];
        typename row::iterator it           = t_row.begin();
        typename row::iterator end          = t_row.end();
        typename f_targets::iterator fbegin = m_f_targets.begin();
        typename f_targets::iterator target = fbegin;
        for (theory_var x = 0; it != end; ++it, ++x) {
            if (it->m_edge_id != null_edge_id && x != s) {
                new_dist    = k;
                new_dist   += it->m_distance;
                cell & s_x  = m_matrix[s][x];
                TRACE("ddl", 
                      tout << "s: #" << get_enode(s)->get_owner_id() << " x: #" << get_enode(x)->get_owner_id() << " new_dist: " << new_dist << "\n";
                      tout << "already has edge: " << s_x.m_edge_id << "  old dist: " << s_x.m_distance << "\n";);
                if (s_x.m_edge_id == null_edge_id || new_dist < s_x.m_distance) {
                    target->m_target       = x;
                    target->m_new_distance = new_dist;
                    ++target;
                }
            }
        }
        
        typename f_targets::iterator fend = target;
        
        // For each node y such that y --> s, and for each node x in F,
        // check whether d(y, s) + new_dist(x) < d(y, x).
        typename matrix::iterator it2    = m_matrix.begin();
        typename matrix::iterator end2   = m_matrix.end();
        for (theory_var y = 0; it2 != end2; ++it2, ++y) {
            if (y != t) {
                row  & r = *it2;
                cell & c = r[s];
                if (c.m_edge_id != null_edge_id) {
                    numeral const & d_y_s = c.m_distance;
                    target = fbegin;
                    for (; target != fend; ++target) {
                        theory_var x = target->m_target;
                        if (x != y) {
                            new_dist  = d_y_s;
                            new_dist += target->m_new_distance;
                            cell & y_x = m_matrix[y][x];
                            if (y_x.m_edge_id == null_edge_id || new_dist < y_x.m_distance) {
                                m_cell_trail.push_back(cell_trail(y, x, y_x.m_edge_id, y_x.m_distance));
                                y_x.m_edge_id  = new_edge_id;
                                y_x.m_distance = new_dist;
                                if (!y_x.m_occs.empty()) {
                                    propagate_using_cell(y, x);
                                }
                            }
                        }
                    }
                }
            }
        }
        CASSERT("ddl", check_matrix());
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::assign_literal(literal l, theory_var source, theory_var target) {
        context & ctx = get_context();
        literal_vector & antecedents = m_tmp_literals;
        antecedents.reset();
        get_antecedents(source, target, antecedents);
        ctx.assign(l, ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), antecedents.size(), antecedents.c_ptr(), l)));
    }
    
    template<typename Ext>
    void theory_dense_diff_logic<Ext>::propagate_using_cell(theory_var source, theory_var target) {
        cell & c = m_matrix[source][target];
        SASSERT(c.m_edge_id != null_edge_id);
        numeral neg_dist = c.m_distance;
        neg_dist.neg();
        context & ctx = get_context();
        typename atoms::const_iterator it  = c.m_occs.begin();
        typename atoms::const_iterator end = c.m_occs.end();
        for (; it != end; ++it) {
            atom * a = *it;
            if (ctx.get_assignment(a->get_bool_var()) == l_undef) {
                if (a->get_source() == source) {
                    SASSERT(a->get_target() == target);
                    if (c.m_distance <= a->get_offset()) {
                        m_stats.m_num_propagations++;
                        TRACE("ddl", tout << "asserting atom to true: "; display_atom(tout, a);
                              tout << "distance(#" << get_enode(source)->get_owner_id() << ", #" << get_enode(target)->get_owner_id()
                              << "): " << c.m_distance << "\n";);
                        assign_literal(literal(a->get_bool_var(), false), source, target);
                    }
                }
                else {
                    SASSERT(a->get_source() == target);
                    SASSERT(a->get_target() == source);
                    if (neg_dist > a->get_offset()) {
                        m_stats.m_num_propagations++;
                        TRACE("ddl", tout << "asserting atom to true: "; display_atom(tout, a);
                              tout << "distance(#" << get_enode(source)->get_owner_id() << ", #" << get_enode(target)->get_owner_id()
                              << "): " << c.m_distance << "\n";);
                        assign_literal(literal(a->get_bool_var(), true), source, target);
                    }
                }
            }
        }
    }

    template<typename Ext>
    inline void theory_dense_diff_logic<Ext>::add_edge(theory_var source, theory_var target, numeral const & offset, literal l) {
        TRACE("ddl", tout << "trying adding edge: #" << get_enode(source)->get_owner_id() << " -- " << offset << " --> #" << get_enode(target)->get_owner_id() << "\n";);
        cell & c_inv = m_matrix[target][source];
        if (c_inv.m_edge_id != null_edge_id && - c_inv.m_distance > offset) {
            // conflict detected.
            TRACE("ddl", tout << "conflict detected: #" << get_enode(source)->get_owner_id() << " #" << get_enode(target)->get_owner_id() <<
                  " offset: " << offset << ", c_inv.m_edge_id: " << c_inv.m_edge_id << ", c_inv.m_distance: " << c_inv.m_distance << "\n";);
            literal_vector & antecedents = m_tmp_literals;
            antecedents.reset();
            get_antecedents(target, source, antecedents);
            if (l != null_literal)
                antecedents.push_back(l);
            context & ctx = get_context();
            region & r    = ctx.get_region();
            ctx.set_conflict(ctx.mk_justification(theory_conflict_justification(get_id(), r, antecedents.size(), antecedents.c_ptr())));

            if (dump_lemmas()) {
                ctx.display_lemma_as_smt_problem(antecedents.size(), antecedents.c_ptr(), false_literal);
            }

            return;
        }
        
        cell & c = m_matrix[source][target];
        if (c.m_edge_id == null_edge_id || offset < c.m_distance) {
            TRACE("ddl", tout << "adding edge: #" << get_enode(source)->get_owner_id() << " -- " << offset << " --> #" << get_enode(target)->get_owner_id() << "\n";);
            m_edges.push_back(edge(source, target, offset, l));
            update_cells();
        }
    }


#ifdef Z3DEBUG
    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::check_vector_sizes() const {
        SASSERT(m_matrix.size() == m_f_targets.size());
        SASSERT(m_is_int.size() == m_matrix.size());
        typename matrix::const_iterator it  = m_matrix.begin();
        typename matrix::const_iterator end = m_matrix.end();
        for (; it != end; ++it) {
            SASSERT(it->size() == m_matrix.size());
        }
        return true;
    }

    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::check_matrix() const {
        int sz = m_matrix.size();
        for (theory_var i = 0; i < sz; i++) {
            for (theory_var j = 0; j < sz; j++) {
                cell const & c = m_matrix[i][j];
                if (c.m_edge_id == self_edge_id) {
                    SASSERT(i == j);
                    SASSERT(c.m_distance.is_zero());
                }
                else if (c.m_edge_id != null_edge_id) {
                    edge const & e = m_edges[c.m_edge_id];
                    theory_var s = e.m_source;
                    theory_var t = e.m_target;
                    numeral k  = get_distance(i, s);
                    k         += e.m_offset;
                    k         += get_distance(t, j);
                    if (c.m_distance != k) {
                        CTRACE("ddl", c.m_distance != k, tout << "i: " << i << " j: " << j << " k: " << k << " c.m_distance: " << c.m_distance << "\n";
                              display(tout););
                        SASSERT(c.m_distance == k);
                    }
                }
            }
        }
        return true;
    }
#endif        

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::display(std::ostream & out) const {
        out << "Theory dense difference logic:\n";
        display_var2enode(out);
        typename matrix::const_iterator it1  = m_matrix.begin();
        typename matrix::const_iterator end1 = m_matrix.end();
        for (int v1 = 0; it1 != end1; ++it1, ++v1) {
            typename row::const_iterator it2  = it1->begin();
            typename row::const_iterator end2 = it1->end();
            for (int v2 = 0; it2 != end2; ++it2, ++v2) {
                if (it2->m_edge_id != null_edge_id && it2->m_edge_id != self_edge_id) {
                    out << "#";
                    out.width(5);
                    out << std::left << get_enode(v1)->get_owner_id() << " -- ";
                    out.width(10);
                    out << std::left << it2->m_distance << " : id";
                    out.width(5);
                    out << std::left << it2->m_edge_id << " --> #";
                    out << get_enode(v2)->get_owner_id() << "\n";
                }
            }
        }
        out << "atoms:\n";
        typename atoms::const_iterator it2  = m_atoms.begin();
        typename atoms::const_iterator end2 = m_atoms.end();
        for (;it2 != end2; ++it2) {
            atom * a = *it2;
            display_atom(out, a);
        }
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::display_atom(std::ostream & out, atom * a) const {
        out << "#";
        out.width(5);
        out << std::left << get_enode(a->get_target())->get_owner_id() << " - #";
        out.width(5);
        out << std::left << get_enode(a->get_source())->get_owner_id() << " <= ";
        out.width(10);
        out << std::left << a->get_offset() << "        assignment: " << get_context().get_assignment(a->get_bool_var()) << "\n";
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::collect_statistics(::statistics & st) const {
        st.update("dd assertions", m_stats.m_num_assertions);
        st.update("dd propagations", m_stats.m_num_propagations);
        m_arith_eq_adapter.collect_statistics(st);
    }

    /**
       \brief Build a model for doing model-based theory combination.
    */
    template<typename Ext>
    void theory_dense_diff_logic<Ext>::init_model() {
        int num_vars = get_num_vars();
        m_assignment.reset();
        m_assignment.resize(num_vars);
        for (int i = 0; i < num_vars; i++) {
            row & r     = m_matrix[i];
            numeral & d = m_assignment[i];
            for (int j = 0; j < num_vars; j++) {
                if (i != j) {
                    cell & c = r[j];
                    if (c.m_edge_id != null_edge_id && c.m_distance < d) {
                        d = c.m_distance;
                    }
                }
            }
        }
        for (int i = 0; i < num_vars; i++)
            m_assignment[i].neg();
        TRACE("ddl_model", 
              tout << "ddl model\n";
              for (theory_var v = 0; v < num_vars; v++) {
                  tout << "#" << mk_pp(get_enode(v)->get_owner(), get_manager()) << " = " << m_assignment[v] << "\n";
              });
    }

    /**
       The arithmetic module uses infinitesimals. So,
       an inf_numeral (n,k) represents  n + k*epsilon
       where epsilon is a very small number. 
       In order to generate a model, we need to compute
       a value for epsilon in a way all inequalities remain
       satisfied.

       assume we have the inequality
       x - y <= (n_c, k_c)

       where the interpretation for x and y is:
       (n_x, k_x) and (n_y, k_y).

       So,
       
       (n_x, k_x) <= (n_y + n_c, k_y + k_c)
       

       The only intersting case is n_x < n_y + n_c and k_x > k_y + k_c. 
       Using the definition of infinitesimal numbers
       we have:
       
       n_x + k_x * epsilon <= n_y + n_c + (k_y + k_c) * epsilon

       Therefore:
       
       epsilon <= (n_y + n_c - n_x) / (k_x - k_y - k_c)
    */
    template<typename Ext>
    void theory_dense_diff_logic<Ext>::compute_epsilon() {
        m_epsilon = rational(1);
        typename edges::const_iterator it  = m_edges.begin();
        typename edges::const_iterator end = m_edges.end();
        // first edge is null
        SASSERT(it->m_target == null_theory_var);
        SASSERT(it->m_source == null_theory_var);
        ++it; 
        for (; it != end; ++it) {
            edge const & e = *it;
            rational n_x = m_assignment[e.m_target].get_rational().to_rational();
            rational k_x = m_assignment[e.m_target].get_infinitesimal().to_rational();
            rational n_y = m_assignment[e.m_source].get_rational().to_rational();
            rational k_y = m_assignment[e.m_source].get_infinitesimal().to_rational();
            rational n_c = e.m_offset.get_rational().to_rational();
            rational k_c = e.m_offset.get_infinitesimal().to_rational();
            TRACE("epsilon", tout << "(n_x,k_x): " << n_x << ", " << k_x << ", (n_y,k_y): " << n_y << ", " << k_y << ", (n_c,k_c): " << n_c << ", " << k_c << "\n";);
            if (n_x < n_y + n_c && k_x > k_y + k_c) {
                rational new_epsilon = (n_y + n_c - n_x) / (k_x - k_y - k_c);
                if (new_epsilon < m_epsilon) {
                    TRACE("epsilon", tout << "new epsilon: " << new_epsilon << "\n";);
                    m_epsilon = new_epsilon;
                }
            }
        }
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::fix_zero() {
        int num_vars = get_num_vars();
        for (int v = 0; v < num_vars; ++v) {
            enode * n = get_enode(v);
            if (m_autil.is_zero(n->get_owner()) && !m_assignment[v].is_zero()) {
                numeral val = m_assignment[v];
                sort * s = get_manager().get_sort(n->get_owner());
                // adjust the value of all variables that have the same sort.
                for (int v2 = 0; v2 < num_vars; ++v2) {
                    enode * n2 = get_enode(v2);
                    if (get_manager().get_sort(n2->get_owner()) == s) {
                        m_assignment[v2] -= val;
                    }
                }
                SASSERT(m_assignment[v].is_zero());
            }
        }
        TRACE("ddl_model", 
              tout << "ddl model\n";
              for (theory_var v = 0; v < num_vars; v++) {
                  tout << "#" << mk_pp(get_enode(v)->get_owner(), get_manager()) << " = " << m_assignment[v] << "\n";
              });
    }

    template<typename Ext>
    void theory_dense_diff_logic<Ext>::init_model(model_generator & m) {
        m_factory = alloc(arith_factory, get_manager());
        m.register_factory(m_factory);
        fix_zero();
        compute_epsilon();
    }

    template<typename Ext>
    model_value_proc * theory_dense_diff_logic<Ext>::mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        numeral const & val = m_assignment[v];
        rational num = val.get_rational().to_rational() +  m_epsilon *  val.get_infinitesimal().to_rational();
        return alloc(expr_wrapper_proc, m_factory->mk_value(num, is_int(v)));
    }

    // TBD: code is common to both sparse and dense difference logic solvers.
    template<typename Ext>
    bool theory_dense_diff_logic<Ext>::internalize_objective(expr * n, rational const& m, rational& q, objective_term & objective) {

        // Compile term into objective_term format
        rational r;
        expr* x, *y;
        if (m_autil.is_numeral(n, r)) {
            q += r;
        }
        else if (m_autil.is_add(n)) {
            for (unsigned i = 0; i < to_app(n)->get_num_args(); ++i) {
                if (!internalize_objective(to_app(n)->get_arg(i), m, q, objective)) {
                    return false;
                }
            }
        }
        else if (m_autil.is_mul(n, x, y) && m_autil.is_numeral(x, r)) {
            return internalize_objective(y, m*r, q, objective);
        }
        else if (m_autil.is_mul(n, y, x) && m_autil.is_numeral(x, r)) {
            return internalize_objective(y, m*r, q, objective);
        }
        else if (!is_app(n)) {
            return false;
        }
        else if (to_app(n)->get_family_id() == m_autil.get_family_id()) {
            return false;
        }
        else {
            context& ctx = get_context();
            enode * e = 0;
            theory_var v = 0;
            if (ctx.e_internalized(n)) {
                e = ctx.get_enode(to_app(n));                
            }
            else {
                e = ctx.mk_enode(to_app(n), false, false, true);
            }            
            v = e->get_th_var(get_id());
            if (v == null_theory_var) {
                v = mk_var(e);                
            }

            objective.push_back(std::make_pair(v, m));
        }
        return true;
    }

    template<typename Ext>
    inf_eps_rational<inf_rational> theory_dense_diff_logic<Ext>::value(theory_var v) {
        objective_term const& objective = m_objectives[v];   
        inf_eps r = inf_eps(m_objective_consts[v]);
        for (unsigned i = 0; i < objective.size(); ++i) {
            numeral n = m_assignment[v];
            rational r1 = n.get_rational().to_rational();
            rational r2 = n.get_infinitesimal().to_rational();
            r += objective[i].second * inf_eps(rational(0), inf_rational(r1, r2));
        }
        return r;
    }

    template<typename Ext>
    inf_eps_rational<inf_rational> theory_dense_diff_logic<Ext>::maximize(theory_var v, expr_ref& blocker, bool& has_shared) {
        typedef simplex::simplex<simplex::mpq_ext> Simplex;
        ast_manager& m = get_manager();
        Simplex S(m.limit());
        objective_term const& objective = m_objectives[v];
        has_shared = false;
        
        IF_VERBOSE(1,
                   for (unsigned i = 0; i < objective.size(); ++i) {
                       verbose_stream() << objective[i].second 
                                        << " * v" << objective[i].first << " ";
                   }
                   verbose_stream() << " + " << m_objective_consts[v] << "\n";);

        unsigned num_nodes = get_num_vars();
        unsigned num_edges = m_edges.size();
        S.ensure_var(num_nodes + num_edges + m_objectives.size());
        for (unsigned i = 0; i < num_nodes; ++i) {
            numeral const& a = m_assignment[i];
            rational fin = a.get_rational().to_rational();
            rational inf = a.get_infinitesimal().to_rational();
            mpq_inf q(fin.to_mpq(), inf.to_mpq());
            S.set_value(i, q);
        }
        for (unsigned i = 0; i < num_nodes; ++i) {
            enode * n = get_enode(i);
            if (m_autil.is_zero(n->get_owner())) {
                S.set_lower(v, mpq_inf(mpq(0), mpq(0)));
                S.set_upper(v, mpq_inf(mpq(0), mpq(0)));
                break;
            }
        }
        svector<unsigned> vars;
        unsynch_mpq_manager mgr;
        scoped_mpq_vector coeffs(mgr);
        coeffs.push_back(mpq(1));
        coeffs.push_back(mpq(-1));
        coeffs.push_back(mpq(-1));
        vars.resize(3);
        for (unsigned i = 0; i < num_edges; ++i) {
            edge const& e = m_edges[i];
            if (e.m_source == null_theory_var || e.m_target == null_theory_var) {
                continue;
            }
            unsigned base_var = num_nodes + i;
            vars[0] = e.m_target;
            vars[1] = e.m_source;
            vars[2] = base_var;
            S.add_row(base_var, 3, vars.c_ptr(), coeffs.c_ptr());
            // t - s <= w
            // t - s - b = 0, b >= w
            numeral const& w = e.m_offset;
            rational fin = w.get_rational().to_rational();
            rational inf = w.get_infinitesimal().to_rational();
            mpq_inf q(fin.to_mpq(),inf.to_mpq());
            S.set_upper(base_var, q);            
        }
        unsigned w = num_nodes + num_edges + v;

        // add objective function as row.
        coeffs.reset();
        vars.reset();
        for (unsigned i = 0; i < objective.size(); ++i) {
            coeffs.push_back(objective[i].second.to_mpq());
            vars.push_back(objective[i].first);
        }
        coeffs.push_back(mpq(1));
        vars.push_back(w);
        Simplex::row row = S.add_row(w, vars.size(), vars.c_ptr(), coeffs.c_ptr());
        
        TRACE("opt", S.display(tout); display(tout););
        
        // optimize    
        lbool is_sat = S.make_feasible();
        if (is_sat == l_undef) {
            blocker = m.mk_false();
            return inf_eps::infinity();        
        }
        TRACE("opt", S.display(tout); );    
        SASSERT(is_sat != l_false);
        lbool is_fin = S.minimize(w);
        
        switch (is_fin) {
        case l_true: {
            simplex::mpq_ext::eps_numeral const& val = S.get_value(w);
            inf_rational r(-rational(val.first), -rational(val.second));
            TRACE("opt", tout << r << " " << "\n"; 
                  S.display_row(tout, row, true););
            Simplex::row_iterator it = S.row_begin(row), end = S.row_end(row);
            expr_ref_vector& core = m_objective_assignments[v];
            expr_ref tmp(m);
            core.reset();
            for (; it != end; ++it) {
                unsigned v = it->m_var;
                if (num_nodes <= v && v < num_nodes + num_edges) {
                    unsigned edge_id = v - num_nodes;
                    literal lit = m_edges[edge_id].m_justification;
                    get_context().literal2expr(lit, tmp);
                    core.push_back(tmp);
                }
            }
            for (unsigned i = 0; i < num_nodes; ++i) {
                mpq_inf const& val = S.get_value(i);
                rational q(val.first), eps(val.second);
                numeral  a(q);
                m_assignment[i] = a;
                // TBD: if epsilon is != 0, then adjust a by some small fraction.
            }
            blocker = mk_gt(v, r);
            IF_VERBOSE(10, verbose_stream() << blocker << "\n";);
            return inf_eps(rational(0), r);
        }
        default:
            TRACE("opt", tout << "unbounded\n"; );        
            blocker = m.mk_false();
            return inf_eps::infinity();        
        }
    }

    template<typename Ext>
    theory_var theory_dense_diff_logic<Ext>::add_objective(app* term) {
        objective_term objective;
        theory_var result = m_objectives.size();
        rational q(1), r(0);
        expr_ref_vector vr(get_manager());
        if (!is_linear(get_manager(), term)) {
            result = null_theory_var;
        }
        else if (internalize_objective(term, q, r, objective)) {
            m_objectives.push_back(objective);
            m_objective_consts.push_back(r);
            m_objective_assignments.push_back(vr);
        }
        else {
            result = null_theory_var;
        }
        return result;
    }

    template<typename Ext>
    expr_ref theory_dense_diff_logic<Ext>::mk_gt(theory_var v, inf_rational const& val) {
        return mk_ineq(v, val, true);
    }

    template<typename Ext>
    expr_ref theory_dense_diff_logic<Ext>::mk_ge(
        filter_model_converter& fm, theory_var v, inf_rational const& val) {
        return mk_ineq(v, val, false);
    }

    template<typename Ext>
    expr_ref theory_dense_diff_logic<Ext>::mk_ineq(theory_var v, inf_rational const& val, bool is_strict) {
        ast_manager& m = get_manager();
        objective_term const& t = m_objectives[v];
        expr_ref e(m), f(m), f2(m);
        if (t.size() == 1 && t[0].second.is_one()) {
            f = get_enode(t[0].first)->get_owner();
        }
        else if (t.size() == 1 && t[0].second.is_minus_one()) {
            f = m_autil.mk_uminus(get_enode(t[0].first)->get_owner());
        }
        else if (t.size() == 2 && t[0].second.is_one() && t[1].second.is_minus_one()) {
            f = get_enode(t[0].first)->get_owner();
            f2 = get_enode(t[1].first)->get_owner();
            f = m_autil.mk_sub(f, f2); 
        }
        else if (t.size() == 2 && t[1].second.is_one() && t[0].second.is_minus_one()) {
            f = get_enode(t[1].first)->get_owner();
            f2 = get_enode(t[0].first)->get_owner();
            f = m_autil.mk_sub(f, f2);
        }
        else {
            // 
            expr_ref_vector const& core = m_objective_assignments[v];
            f = m.mk_and(core.size(), core.c_ptr());
            if (is_strict) {
                f = m.mk_not(f);
            }
            TRACE("arith", tout << "block: " << f << "\n";);
            return f;
        }
        
        e = m_autil.mk_numeral(val.get_rational(), m.get_sort(f));
        
        if (val.get_infinitesimal().is_neg()) {
            if (is_strict) {
                f = m_autil.mk_ge(f, e);
            }
            else {
                expr_ref_vector const& core = m_objective_assignments[v];
                f = m.mk_and(core.size(), core.c_ptr());
            }
        }
        else {
            if (is_strict) {
                f = m_autil.mk_gt(f, e);
            }
            else {
                f = m_autil.mk_ge(f, e);
            }
        }
        return f;
    }

};

#endif /* THEORY_DENSE_DIFF_LOGIC_DEF_H_ */

