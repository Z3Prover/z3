/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    seq_regex.cpp

Abstract:

    Solver for regexes 

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-22

--*/

#include "smt/seq_regex.h"
#include "smt/theory_seq.h"
#include "ast/expr_abstract.h"

namespace smt {

    seq_regex::seq_regex(theory_seq& th):
        th(th),
        ctx(th.get_context()),
        m(th.get_manager()),
        m_state_to_expr(m)
    {}

    seq_util& seq_regex::u() { return th.m_util; }
    class seq_util::re& seq_regex::re() { return th.m_util.re; }
    class seq_util::str& seq_regex::str() { return th.m_util.str; }
    seq_rewriter& seq_regex::seq_rw() { return th.m_seq_rewrite; }
    seq_skolem& seq_regex::sk() { return th.m_sk; }
    arith_util& seq_regex::a() { return th.m_autil; }
    void seq_regex::rewrite(expr_ref& e) { th.m_rewrite(e); }

    bool seq_regex::can_propagate() const {
        for (auto const& p : m_to_propagate) {
            literal trigger = p.m_trigger;
            if (trigger == null_literal || ctx.get_assignment(trigger) != l_undef)
                return true;
        }
        return false;
    }

    bool seq_regex::propagate() {
        bool change = false;
        for (unsigned i = 0; !ctx.inconsistent() && i < m_to_propagate.size(); ++i) {
            propagation_lit const& pl = m_to_propagate[i];
            literal trigger = pl.m_trigger;
            if (trigger != null_literal && ctx.get_assignment(trigger) == l_undef)
                continue;
            if (propagate_accept_core(pl.m_lit, trigger)) {
                m_to_propagate.erase_and_swap(i--);
                change = true;
            }
            else if (trigger != pl.m_trigger) {
                m_to_propagate.set(i, propagation_lit(pl.m_lit, trigger));
            }
                
        }
        return change;
    }

    /**
     * is_string_equality holds of str.in_re s R, 
     * 
     * s in (all ++ x ++ all ++ y ++ all)
     * => 
     * s = fresh1 ++ x ++ fresh2 ++ y ++ fresh3
     * 
     * TBD General rewrite possible:
     *
     * s in (R ++ Q)
     * =>
     * s = x ++ y and x in R and y in Q
     */

    bool seq_regex::is_string_equality(literal lit) {
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        expr_ref id(a().mk_int(e->get_id()), m);
        VERIFY(str().is_in_re(e, s, r));
        sort* seq_sort = m.get_sort(s);
        vector<expr_ref_vector> patterns;
        auto mk_cont = [&](unsigned idx) { 
            return sk().mk("seq.cont", id, a().mk_int(idx), seq_sort);
        };
        unsigned idx = 0;
        if (seq_rw().is_re_contains_pattern(r, patterns)) {
            expr_ref_vector ts(m);
            ts.push_back(mk_cont(idx));
            for (auto const& p : patterns) {
                ts.append(p);
                ts.push_back(mk_cont(++idx));
            }
            expr_ref t = th.mk_concat(ts, seq_sort);
            th.propagate_eq(lit, s, t, true);
            return true;
        }
        return false;
    }

    /**
     * Propagate the atom (str.in_re s r)
     * 
     * Propagation implements the following inference rules
     * 
     * (not (str.in_re s r)) => (str.in_re s (complement r))
     * (str.in_re s r) => r != {}
     * 
     * (str.in_re s r) => (accept s 0 r)
     */

    void seq_regex::propagate_in_re(literal lit) {
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));

        TRACE("seq_regex", tout << "propagate in RE: " << lit.sign() << " " << mk_pp(e, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "PIR(" << mk_pp(s, m) << ","
                                       << state_str(r) << ") ";);

        // convert negative negative membership literals to positive
        // ~(s in R) => s in C(R)
        if (lit.sign()) {
            expr_ref fml(re().mk_in_re(s, re().mk_complement(r)), m);
            rewrite(fml);
            literal nlit = th.mk_literal(fml);
            if (lit == nlit) {
                // is-nullable doesn't simplify for regexes with uninterpreted subterms
                th.add_unhandled_expr(fml);
            }
            th.propagate_lit(nullptr, 1, &lit, nlit);
            return;
        }

        if (coallesce_in_re(lit))
            return;

        if (is_string_equality(lit))
            return;

        expr_ref zero(a().mk_int(0), m);
        expr_ref acc = sk().mk_accept(s, zero, r);
        literal acc_lit = th.mk_literal(acc);

        TRACE("seq", tout << "propagate " << acc << "\n";);

        th.propagate_lit(nullptr, 1, &lit, acc_lit);
    }

    void seq_regex::propagate_accept(literal lit) {
        TRACE("seq_regex", tout << "propagate accept" << std::endl;);
        STRACE("seq_regex_brief", tout << "PA ";);

        literal t = null_literal;
        if (!propagate_accept_core(lit, t))
            m_to_propagate.push_back(propagation_lit(lit, t));
    }

    /**
     * Propagate the atom (accept s i r)
     *
     * The additional 'literal& trigger' is a return value.
     * If propagation returns false, then the trigger is set
     * to indicate what needs to be resolved before propagation
     * can proceed. Currently, however, the trigger is unused and
     * the function always returns true.
     *
     * Propagation triggers updating the state graph for dead state detection:
     * (accept s i r) => update_state_graph(r)
     * (accept s i r) & dead(r) => false
     *
     * Propagation is also blocked under certain conditions to throttle
     * state space exploration past a certain point: see block_unfolding
     *
     * Otherwise, propagation implements the following inference rules:
     *
     * Rule 1. (accept s i r) => len(s) >= i + min_len(r)
     * Rule 2. (accept s i r) & len(s) <= i => nullable(r)
     * Rule 3. (accept s i r) and len(s) > i =>
     *             (accept s (i + 1) (derivative s[i] r)
     *
     * Acceptance of a derivative is unfolded into a disjunction over
     * all derivatives. Effectively, this implements the following rule,
     * but all in one step:
     * (accept s i (ite c r1 r2)) =>
     *             c & (accept s i r1) \/ ~c & (accept s i r2)
     */
    bool seq_regex::propagate_accept_core(literal lit, literal& trigger) {
        SASSERT(!lit.sign());

        expr* s = nullptr, *i = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        unsigned idx = 0;
        VERIFY(sk().is_accept(e, s, i, idx, r));

        TRACE("seq_regex", tout << "propagate: " << mk_pp(e, m) << std::endl;);
        STRACE("seq_regex_brief", tout << std::endl
                                       << "P(" << mk_pp(s, m) << "@" << idx
                                       << "," << state_str(r) << ") ";);

        if (re().is_empty(r)) {
            STRACE("seq_regex_brief", tout << "(empty) ";);
            th.add_axiom(~lit);
            return true;
        }

        update_state_graph(r);

        if (m_state_graph.is_dead(get_state_id(r))) {
            STRACE("seq_regex_brief", tout << "(dead) ";);
            th.add_axiom(~lit);
            return true;
        }

        if (block_unfolding(lit, idx)) {
            STRACE("seq_regex_brief", tout << "(blocked) ";);
            return true;
        }

        STRACE("seq_regex_brief", tout << "(unfold) ";);

        // Rule 1: use min_length to prune search
        expr_ref s_to_re(re().mk_to_re(s), m);
        expr_ref s_plus_r(re().mk_concat(s_to_re, r), m);
        unsigned min_len = re().min_length(s_plus_r);
        literal len_s_ge_min = th.m_ax.mk_ge(th.mk_len(s), min_len);
        th.add_axiom(~lit, len_s_ge_min);

        // Rule 2: nullable check
        literal len_s_le_i = th.m_ax.mk_le(th.mk_len(s), idx);
        literal is_nullable = th.mk_literal(is_nullable_wrapper(r));
        th.add_axiom(~lit, ~len_s_le_i, is_nullable);

        // Rule 3: derivative unfolding
        literal_vector accept_next;
        expr_ref hd = th.mk_nth(s, i);
        expr_ref deriv(m);
        deriv = derivative_wrapper(hd, r);
        accept_next.push_back(~lit);
        accept_next.push_back(len_s_le_i);
        expr_ref_pair_vector cofactors(m);
        get_cofactors(deriv, cofactors);
        for (auto const& p : cofactors) {
            if (m.is_false(p.first) || re().is_empty(p.second)) continue;
            expr_ref cond(p.first, m);
            expr_ref deriv_leaf(p.second, m);

            expr_ref acc = sk().mk_accept(s, a().mk_int(idx + 1), deriv_leaf);
            expr_ref choice(m.mk_and(cond, acc), m);
            literal choice_lit = th.mk_literal(choice);
            accept_next.push_back(choice_lit);
            // TBD: try prioritizing unvisited states here over visited
            // ones (in the state graph), to improve performance
            STRACE("seq_regex_verbose", tout << "added choice: "
                                           << mk_pp(choice, m) << std::endl;);
        }
        th.add_axiom(accept_next);

        // Propagated successfully
        return true;
    }

    /**
     * Put a limit to the unfolding of s. 
     */
    bool seq_regex::block_unfolding(literal lit, unsigned i) {
        return 
            i > th.m_max_unfolding_depth &&
            th.m_max_unfolding_lit != null_literal && 
            ctx.get_assignment(th.m_max_unfolding_lit) == l_true && 
            !ctx.at_base_level() &&
            (th.propagate_lit(nullptr, 1, &lit, ~th.m_max_unfolding_lit), 
             true);
    }

    /**
     * Combine a conjunction of membership relations for the same string
     * within the same Regex.
     */
    bool seq_regex::coallesce_in_re(literal lit) {
        return false; // disabled
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));
        expr_ref regex(r, m);
        literal_vector lits;    
        for (unsigned i = 0; i < m_s_in_re.size(); ++i) {
            auto const& entry = m_s_in_re[i];
            if (!entry.m_active)
                continue;
            enode* n1 = th.ensure_enode(entry.m_s);
            enode* n2 = th.ensure_enode(s);
            if (n1->get_root() != n2->get_root())
                continue;
            if (entry.m_re == regex) 
                continue;

            th.m_trail_stack.push(vector_value_trail<theory_seq, s_in_re, true>(m_s_in_re, i));
            m_s_in_re[i].m_active = false;
            IF_VERBOSE(11, verbose_stream() << "Intersect " << regex << " " << 
                       mk_pp(entry.m_re, m) << " " << mk_pp(s, m) << " " << mk_pp(entry.m_s, m) << std::endl;);
            regex = re().mk_inter(entry.m_re, regex);
            rewrite(regex);
            lits.push_back(~entry.m_lit);
            if (n1 != n2) 
                lits.push_back(~th.mk_eq(n1->get_owner(), n2->get_owner(), false));
        }
        m_s_in_re.push_back(s_in_re(lit, s, regex));
        th.get_trail_stack().push(push_back_vector<theory_seq, vector<s_in_re>>(m_s_in_re));
        if (lits.empty())
            return false;
        lits.push_back(~lit);
        lits.push_back(th.mk_literal(re().mk_in_re(s, regex)));
        th.add_axiom(lits);
        return true;
    }

    expr_ref seq_regex::symmetric_diff(expr* r1, expr* r2) {
        expr_ref r(m);
        if (re().is_empty(r1)) 
            std::swap(r1, r2);
        if (re().is_empty(r2))
            r = r1;
        else 
            r = re().mk_union(re().mk_diff(r1, r2), re().mk_diff(r2, r1));
        rewrite(r);
        return r;
    }

    /*
        Wrapper around calls to is_nullable from the seq rewriter.

        Note: the nullable wrapper and derivative wrapper actually use
        different sequence rewriters; these are at:
            m_seq_rewrite
                (returned by seq_rw())
            th.m_rewrite.m_imp->m_cfg.m_seq_rw
                (private, can't be accessed directly)
        As a result operations are cached separately for the nullable
        and derivative calls. TBD if caching them using the same rewriter
        makes any difference.
    */
    expr_ref seq_regex::is_nullable_wrapper(expr* r) {
        STRACE("seq_regex", tout << "nullable: " << mk_pp(r, m) << std::endl;);

        expr_ref result = seq_rw().is_nullable(r);
        rewrite(result);

        STRACE("seq_regex", tout << "nullable result: " << mk_pp(result, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "n(" << state_str(r) << ")="
                                       << mk_pp(result, m) << " ";);

        return result;
    }

    /*
        Wrapper around the regex symbolic derivative from the seq rewriter.
        Ensures that the derivative is written in a normalized BDD form
        with optimizations for if-then-else expressions involving the head.

        Note: the nullable wrapper and derivative wrapper actually use
        different sequence rewriters; these are at:
            m_seq_rewrite
                (returned by seq_rw())
            th.m_rewrite.m_imp->m_cfg.m_seq_rw
                (private, can't be accessed directly)
        As a result operations are cached separately for the nullable
        and derivative calls. TBD if caching them using the same rewriter
        makes any difference.
    */
    expr_ref seq_regex::derivative_wrapper(expr* hd, expr* r) {
        STRACE("seq_regex", tout << "derivative(" << mk_pp(hd, m) << "): " << mk_pp(r, m) << std::endl;);

        // Use canonical variable for head
        expr_ref hd_canon(m.mk_var(0, m.get_sort(hd)), m);
        expr_ref result(re().mk_derivative(hd_canon, r), m);
        rewrite(result);

        // Substitute with real head
        var_subst subst(m);
        expr_ref_vector sub(m);
        sub.push_back(hd);
        result = subst(result, sub);

        STRACE("seq_regex", tout << "derivative result: " << mk_pp(result, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "d(" << state_str(r) << ")="
                                       << state_str(result) << " ";);

        return result;
    }

    void seq_regex::propagate_eq(expr* r1, expr* r2) {
        TRACE("seq_regex", tout << "propagate EQ: " << mk_pp(r1, m) << ", " << mk_pp(r2, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "PEQ ";);

        sort* seq_sort = nullptr;
        VERIFY(u().is_re(r1, seq_sort));
        expr_ref r = symmetric_diff(r1, r2);
        expr_ref emp(re().mk_empty(m.get_sort(r)), m);
        expr_ref n(m.mk_fresh_const("re.char", seq_sort), m); 
        expr_ref is_empty = sk().mk_is_empty(r, emp, n);
        th.add_axiom(~th.mk_eq(r1, r2, false), th.mk_literal(is_empty));
    }
    
    void seq_regex::propagate_ne(expr* r1, expr* r2) {
        TRACE("seq_regex", tout << "propagate NEQ: " << mk_pp(r1, m) << ", " << mk_pp(r2, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "PNEQ ";);

        sort* seq_sort = nullptr;
        VERIFY(u().is_re(r1, seq_sort));
        expr_ref r = symmetric_diff(r1, r2);
        expr_ref emp(re().mk_empty(m.get_sort(r)), m);
        expr_ref n(m.mk_fresh_const("re.char", seq_sort), m); 
        expr_ref is_non_empty = sk().mk_is_non_empty(r, emp, n);
        th.add_axiom(th.mk_eq(r1, r2, false), th.mk_literal(is_non_empty));
    }

    bool seq_regex::is_member(expr* r, expr* u) {
        expr* u2 = nullptr;
        while (re().is_union(u, u, u2)) {
            if (r == u2)
                return true;
        }
        return r == u;        
    }

    /**
     * is_non_empty(r, u) => nullable or \/_i (c_i and is_non_empty(r_i, u union r))
     *
     * for each (c_i, r_i) in cofactors (min-terms)
     *
     * is_non_empty(r_i, u union r) := false if r_i in u
     *
     */
    void seq_regex::propagate_is_non_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r = nullptr, *u = nullptr, *n = nullptr;
        VERIFY(sk().is_is_non_empty(e, r, u, n));

        TRACE("seq_regex", tout << "propagate nonempty: " << mk_pp(e, m) << std::endl;);
        STRACE("seq_regex_brief", tout
            << std::endl << "PNE(" << expr_id_str(e) << "," << state_str(r)
            << "," << expr_id_str(u) << "," << expr_id_str(n) << ") ";);

        expr_ref is_nullable = is_nullable_wrapper(r);
        if (m.is_true(is_nullable))
            return;
        literal null_lit = th.mk_literal(is_nullable);
        expr_ref hd = mk_first(r, n);
        expr_ref d(m);
        d = derivative_wrapper(hd, r);

        literal_vector lits;
        lits.push_back(~lit);
        if (null_lit != false_literal) 
            lits.push_back(null_lit);

        expr_ref_pair_vector cofactors(m);
        get_cofactors(d, cofactors);
        for (auto const& p : cofactors) {
            if (is_member(p.second, u))
                continue;
            expr_ref cond(p.first, m);
            seq_rw().elim_condition(hd, cond);
            rewrite(cond);
            if (m.is_false(cond))
                continue;            
            expr_ref next_non_empty = sk().mk_is_non_empty(p.second, re().mk_union(u, r), n);
            if (!m.is_true(cond))
                next_non_empty = m.mk_and(cond, next_non_empty);
            lits.push_back(th.mk_literal(next_non_empty));
        }

        th.add_axiom(lits);
    }

    void seq_regex::get_cofactors(expr* r, expr_ref_vector& conds, expr_ref_pair_vector& result) {
        expr* cond = nullptr, *th = nullptr, *el = nullptr;
        if (m.is_ite(r, cond, th, el)) {
            conds.push_back(cond);
            get_cofactors(th, conds, result);
            conds.pop_back();
            conds.push_back(mk_not(m, cond));
            get_cofactors(el, conds, result);
            conds.pop_back();
        }
        else {
            expr_ref conj = mk_and(conds);
            result.push_back(conj, r);
        }
    }

    void seq_regex::get_all_derivatives(expr* r, expr_ref_vector& results) {
        // Get derivative
        sort* seq_sort = nullptr;
        VERIFY(u().is_re(r, seq_sort));
        expr_ref n(m.mk_fresh_const("re.char", seq_sort), m);
        expr_ref hd = mk_first(r, n);
        expr_ref d(m);
        d = derivative_wrapper(hd, r);
        // Use get_cofactors method and try to filter out unsatisfiable conds
        expr_ref_pair_vector cofactors(m);
        get_cofactors(d, cofactors);
        STRACE("seq_regex_verbose", tout << "getting all derivatives of: " << mk_pp(r, m) << std::endl;);
        for (auto const& p : cofactors) {
            if (m.is_false(p.first) || re().is_empty(p.second)) continue;
            STRACE("seq_regex_verbose", tout << "adding derivative: " << mk_pp(p.second, m) << std::endl;);
            results.push_back(p.second);
        }
    }

    /*
      is_empty(r, u) => ~is_nullable(r)
      is_empty(r, u) => (forall x . ~cond(x)) or is_empty(r1, u union r)    for (cond, r) in min-terms(D(x,r))      

      is_empty(r, u) is true if r is a member of u
     */
    void seq_regex::propagate_is_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r = nullptr, *u = nullptr, *n = nullptr;
        VERIFY(sk().is_is_empty(e, r, u, n));
        expr_ref is_nullable = is_nullable_wrapper(r);

        TRACE("seq_regex", tout << "propagate empty: " << mk_pp(e, m) << std::endl;);
        STRACE("seq_regex_brief", tout
            << std::endl << "PE(" << expr_id_str(e) << "," << state_str(r)
            << "," << expr_id_str(u) << "," << expr_id_str(n) << ") ";);

        if (m.is_true(is_nullable)) {
            th.add_axiom(~lit);
            return;
        }
        th.add_axiom(~lit, ~th.mk_literal(is_nullable));
        expr_ref hd = mk_first(r, n);
        expr_ref d(m);
        d = derivative_wrapper(hd, r);
        literal_vector lits;
        expr_ref_pair_vector cofactors(m);
        get_cofactors(d, cofactors);        
        for (auto const& p : cofactors) {
            if (is_member(p.second, u))
                continue;
            expr_ref cond(p.first, m);
            seq_rw().elim_condition(hd, cond);
            rewrite(cond);
            if (m.is_false(cond))
                continue;
            lits.reset();
            lits.push_back(~lit);
            if (!m.is_true(cond)) {
                expr_ref ncond(mk_not(m, cond), m);
                lits.push_back(th.mk_literal(mk_forall(m, hd, ncond)));
            }
            expr_ref is_empty1 = sk().mk_is_empty(p.second, re().mk_union(u, r), n);    
            lits.push_back(th.mk_literal(is_empty1)); 
            th.add_axiom(lits);
        }        
    }

    expr_ref seq_regex::mk_first(expr* r, expr* n) {
        sort* elem_sort = nullptr, *seq_sort = nullptr;
        VERIFY(u().is_re(r, seq_sort));
        VERIFY(u().is_seq(seq_sort, elem_sort));
        return sk().mk("re.first", n, a().mk_int(r->get_id()), elem_sort);
    }

    /**
     * Dead state elimination using the state_graph class
     */

    unsigned seq_regex::get_state_id(expr* e) {
        // Assign increasing IDs starting from 1
        if (!m_expr_to_state.contains(e)) {
            m_state_to_expr.push_back(e);
            unsigned new_id = m_state_to_expr.size();
            m_expr_to_state.insert(e, new_id);
            STRACE("seq_regex_brief", tout << "new(" << expr_id_str(e)
                                           << ")=" << state_str(e) << " ";);
        }
        return m_expr_to_state.find(e);
    }
    expr* seq_regex::get_expr_from_id(unsigned id) {
        SASSERT(id >= 1);
        SASSERT(id <= m_state_to_expr.size());
        return m_state_to_expr.get(id);
    }

    bool seq_regex::can_be_in_cycle(expr *r1, expr *r2) {
        // TBD: This can be used to optimize the state graph:
        // return false here if it is known that r1 -> r2 can never be
        // in a cycle. There are various easy syntactic checks on r1 and r2
        // that can be used to infer this (e.g. star height, or length if
        // both are star-free).
        return true;
    }

    /*
        Update the state graph with expression r and all its derivatives.
    */
    bool seq_regex::update_state_graph(expr* r) {
        unsigned r_id = get_state_id(r);
        if (m_state_graph.is_done(r_id)) return false;
        if (m_state_graph.get_size() >= m_max_state_graph_size) {
            STRACE("seq_regex", tout << "Warning: ignored state graph update -- max size of seen states reached!" << std::endl;);
            STRACE("seq_regex_brief", tout << "(MAX SIZE REACHED) ";);
            return false;
        }
        STRACE("seq_regex", tout << "Updating state graph for regex "
                                 << mk_pp(r, m) << ") ";);
        // Add state
        m_state_graph.add_state(r_id);
        STRACE("seq_regex_brief", tout << std::endl << "USG("
                                       << state_str(r) << ") ";);
        expr_ref r_nullable = is_nullable_wrapper(r);
        if (m.is_true(r_nullable)) {
            m_state_graph.mark_live(r_id);
        }
        else {
            // Add edges to all derivatives
            expr_ref_vector derivatives(m);
            STRACE("seq_regex_verbose", tout
                << std::endl << "  getting all derivs: " << r_id << " ";);
            get_all_derivatives(r, derivatives);
            for (auto const& dr: derivatives) {
                unsigned dr_id = get_state_id(dr);
                STRACE("seq_regex_verbose", tout
                    << std::endl << "  traversing deriv: " << dr_id << " ";);
                m_state_graph.add_state(dr_id);
                bool maybecycle = can_be_in_cycle(r, dr);
                m_state_graph.add_edge(r_id, dr_id, maybecycle);
            }
            m_state_graph.mark_done(r_id);
        }
        STRACE("seq_regex_brief", tout << std::endl;);
        STRACE("seq_regex_brief", m_state_graph.display(tout););
        return true;
    }

    std::string seq_regex::state_str(expr* e) {
        if (m_expr_to_state.contains(e))
            return std::to_string(get_state_id(e));
        else
            return expr_id_str(e);
    }
    std::string seq_regex::expr_id_str(expr* e) {
        return std::string("id") + std::to_string(e->get_id());
    }

}
