/*++
Copyright (c) 2011 Microsoft Corporation

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
        m(th.get_manager())
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
            if (propagate(pl.m_lit, trigger)) {
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
        STRACE("seq_regex_brief",
            tout << "PIR("
                 << s->get_id()
                 << ","
                 << r->get_id()
                 << ") ";);

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

        //
        // TBD s in R => R != {}
        // non-emptiness enforcement could instead of here, 
        // be added to propagate_accept after some threshold is met.
        // 
        if (false) {
            expr_ref is_empty(m.mk_eq(r, re().mk_empty(m.get_sort(s))), m);
            rewrite(is_empty);
            literal is_emptyl = th.mk_literal(is_empty);
            if (ctx.get_assignment(is_emptyl) != l_false) {
                th.propagate_lit(nullptr, 1, &lit, ~is_emptyl);
                return;
            }
        }

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
        if (!propagate(lit, t))
            m_to_propagate.push_back(propagation_lit(lit, t));
    }

    /**
     * Propagate the atom (accept s i r)
     * 
     * Propagation implements the following inference rules
     *
     * (accept s i r[if(c,r1,r2)]) & c => (accept s i r[r1])
     * (accept s i r[if(c,r1,r2)]) & ~c => (accept s i r[r2])
     * (accept s i r) & nullable(r) => len(s) >= i
     * (accept s i r) & ~nullable(r) => len(s) >= i + 1
     * (accept s i r) & len(s) <= i => nullable(r)
     * (accept s i r) & len(s) > i => (accept s (+ i 1) D(nth(s,i), r))
     */
    
    bool seq_regex::propagate(literal lit, literal& trigger) {
        SASSERT(!lit.sign());

        expr* s = nullptr, *i = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        unsigned idx = 0;
        VERIFY(sk().is_accept(e, s, i, idx, r));

        TRACE("seq_regex", tout << "propagate: " << mk_pp(e, m) << std::endl;);
        STRACE("seq_regex_brief",
            tout << std::endl << "P(" << mk_pp(s, m)
                              << "," << idx
                              << "," << r->get_id()
                              << ") ";);

        if (re().is_empty(r)) {
            th.add_axiom(~lit);
            return true;
        }

        if (block_unfolding(lit, idx))
            return true;

        propagate_nullable(lit, s, idx, r);

        return propagate_derivative(lit, e, s, i, idx, r, trigger);
    }

    /**
       Implement the two axioms as propagations:

       (accept s i r) => len(s) >= i
       (accept s i r) & ~nullable(r) => len(s) >= i + 1

       evaluate nullable(r):
       nullable(r) := true -> propagate: (accept s i r) => len(s) >= i
       nullable(r) := false -> propagate: (accept s i r) => len(s) >= i + 1
 
       Otherwise: 
       propagate: (accept s i r) => len(s) >= i
       evaluate len(s) <= i:
       len(s) <= i := undef -> axiom:     (accept s i r) & len(s) <= i => nullable(r)
       len(s) <= i := true  -> propagate: (accept s i r) & len(s) <= i => nullable(r)
       len(s) <= i := false -> noop.
    
     */

    void seq_regex::propagate_nullable(literal lit, expr* s, unsigned idx, expr* r) {
        TRACE("seq_regex", tout << "propagate nullable: " << mk_pp(r, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "PN ";);

        expr_ref is_nullable = is_nullable_wrapper(r);

        literal len_s_ge_i = th.m_ax.mk_ge(th.mk_len(s), idx);
        if (m.is_true(is_nullable)) {
            th.propagate_lit(nullptr, 1,&lit, len_s_ge_i);
        }
        else if (m.is_false(is_nullable)) {
            th.propagate_lit(nullptr, 1, &lit, th.m_ax.mk_ge(th.mk_len(s), idx + 1));
            // @EXP (experimental change)
            //unsigned len = std::max(1u, re().min_length(r));
            //th.propagate_lit(nullptr, 1, &lit, th.m_ax.mk_ge(th.mk_len(s), idx + re().min_length(r)));
        }
        else {
            literal is_nullable_lit = th.mk_literal(is_nullable);
            ctx.mark_as_relevant(is_nullable_lit);
            literal len_s_le_i = th.m_ax.mk_le(th.mk_len(s), idx);
            switch (ctx.get_assignment(len_s_le_i)) {
            case l_undef:
                th.add_axiom(~lit, ~len_s_le_i, is_nullable_lit);
                break;
            case l_true: {
                literal lits[2] = { lit, len_s_le_i };
                th.propagate_lit(nullptr, 2, lits, is_nullable_lit);
                break;
            }
            case l_false:
                break;
            }
            th.propagate_lit(nullptr, 1, &lit, len_s_ge_i);
        }
    }
    
    bool seq_regex::propagate_derivative(literal lit, expr* e, expr* s, expr* i, unsigned idx, expr* r, literal& trigger) {
        TRACE("seq_regex", tout << "propagate derivative: " << mk_pp(r, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "PD ";);

        // (accept s i R) & len(s) > i => (accept s (+ i 1) D(nth(s, i), R)) or conds
        expr_ref d(m);
        expr_ref head = th.mk_nth(s, i);

        d = derivative_wrapper(m.mk_var(0, m.get_sort(head)), r);
        // timer tm;
        // std::cout << d->get_id() << " " << tm.get_seconds() << std::endl;
        //if (tm.get_seconds() > 0.3) 
        //    std::cout << d << std::endl;
        // std::cout.flush();
        literal_vector conds;
        conds.push_back(~lit);
        conds.push_back(th.m_ax.mk_le(th.mk_len(s), idx));
        expr* cond = nullptr, *tt = nullptr, *el = nullptr;
        var_subst subst(m);
        expr_ref_vector sub(m);
        sub.push_back(head);       
        // s in R[if(p,R1,R2)] & p => s in R[R1]
        // s in R[if(p,R1,R2)] & ~p => s in R[R2]
        while (m.is_ite(d, cond, tt, el)) {
            literal lcond = th.mk_literal(subst(cond, sub));
            switch (ctx.get_assignment(lcond)) {
            case l_true:
                conds.push_back(~lcond);
                d = tt;
                break;
            case l_false:
                conds.push_back(lcond);
                d = el;
                break;
            case l_undef:
#if 1
                ctx.mark_as_relevant(lcond);
                trigger = lcond;
                return false;
#else
                if (re().is_empty(tt)) {
                    literal_vector ensure_false(conds);
                    ensure_false.push_back(~lcond);
                    th.add_axiom(ensure_false);
                    conds.push_back(lcond);
                    d = el;
                }
                else if (re().is_empty(el)) {
                    literal_vector ensure_true(conds);
                    ensure_true.push_back(lcond);
                    th.add_axiom(ensure_true);
                    conds.push_back(~lcond);
                    d = tt;
                }
                else {
                    ctx.mark_as_relevant(lcond);
                    trigger = lcond;
                    return false;
                }
                break;
#endif
            }
        }

        if (!is_ground(d)) {
            d = subst(d, sub);
        }
        // at this point there should be no free variables as the ites are at top-level.
        if (!re().is_empty(d)) 
            conds.push_back(th.mk_literal(sk().mk_accept(s, a().mk_int(idx + 1), d)));
        th.add_axiom(conds);        
        TRACE("seq_regex", tout << "unfold " << head << std::endl << mk_pp(r, m) << std::endl;);
        STRACE("seq_regex_brief", tout << "u ";);

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
        // @EXP (experimental change)
        return false;
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
    */
    expr_ref seq_regex::is_nullable_wrapper(expr* r) {
        STRACE("seq_regex", tout << "nullable: " << mk_pp(r, m) << std::endl;);

        expr_ref result = seq_rw().is_nullable(r);
        rewrite(result);

        STRACE("seq_regex", tout << "nullable result: " << mk_pp(result, m) << std::endl;);
        STRACE("seq_regex_brief",
            tout << "n("
                 << r->get_id()
                 << "->"
                 << result->get_id()
                 << ") ";);
        seq_rw().trace_and_reset_cache_counts();

        return result;
    }

    /*
        Wrapper around the regex symbolic derivative from the seq rewriter.
        Ensures that the derivative is written in a normalized BDD form
        with optimizations for if-then-else expressions involving the head.
    */
    expr_ref seq_regex::derivative_wrapper(expr* hd, expr* r) {
        STRACE("seq_regex", tout << "derivative(" << mk_pp(hd, m) << "): " << mk_pp(r, m) << std::endl;);

        expr_ref result = expr_ref(re().mk_derivative(hd, r), m);
        rewrite(result);

        STRACE("seq_regex", tout << "derivative result: " << mk_pp(result, m) << std::endl;);
        STRACE("seq_regex_brief",
            tout << "d("
                 << mk_pp(hd, m)
                 << ","
                 << r->get_id()
                 << "->"
                 << result->get_id()
                 << ") ";);
        seq_rw().trace_and_reset_cache_counts();

        /*  If the following lines are enabled instead, we use the
            same rewriter for the nullable and derivative calls.
            However, it currently seems to cause a performance
            bug as a side effect.

            The two seq rewriters used are at:
                m_seq_rewrite
                    (returned by seq_rw())
                th.m_rewrite.m_imp->m_cfg.m_seq_rw
                    (private, can't be accessed directly)

            TODO: experiment with making them the same and see
            if it results in significant speedup (due to fewer
            cache misses).
           */
        // expr_ref result = seq_rw().mk_derivative(hd, r);
        // rewrite(result)
        // STRACE("seq_regex", tout << "derivative result: " << mk_pp(result, m) << std::endl;);
        // seq_rw().trace_and_reset_cache_counts();

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
        STRACE("seq_regex_brief",
            tout << std::endl << "PNE(" << e->get_id()
                              << "," << r->get_id()
                              << "," << u->get_id()
                              << ") ";);

        expr_ref is_nullable = is_nullable_wrapper(r);
        if (m.is_true(is_nullable))
            return;
        literal null_lit = th.mk_literal(is_nullable);
        expr_ref hd = mk_first(r, n);
        expr_ref d(m);
        d = derivative_wrapper(hd, r);

        STRACE("seq_regex_brief", tout << "(d subbed: " << d->get_id() << ") ";);
        TRACE("seq_regex", tout << "d subbed: " << mk_pp(d, m) << std::endl;);

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
            expr_ref next_non_empty = sk().mk_is_non_empty(p.second, re().mk_union(u, p.second), n);
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
        STRACE("seq_regex_brief",
            tout << std::endl << "PE(" << e->get_id()
                              << "," << r->get_id()
                              << "," << u->get_id()
                              << "," << n->get_id()
                              << ") ";);

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

    /****************************************************
     *** Dead state elimination and seen_states class ***
     ****************************************************/

    seq_regex::seen_states::state seq_regex::seen_states::get_state(expr* e) {
        return m_state_ufind.find(e->get_id());
    }

    void seq_regex::seen_states::mark_unknown(state s) {
        SASSERT(m_unvisited.contains(s));
        m_unvisited.remove(s);
        m_unknown.insert(s);
    }
    void seq_regex::seen_states::mark_alive(state s) {
        SASSERT(m_unknown.contains(s));
        m_unknown.remove(s);
        m_alive.insert(s);
    }
    void seq_regex::seen_states::mark_dead(state s) {
        SASSERT(m_unknown.contains(s));
        m_unknown.remove(s);
        m_dead.insert(s);
    }

    bool seq_regex::seen_states::is_resolved(state s) {
        return (m_alive.contains(s) || m_dead.contains(s));
    }
    bool seq_regex::seen_states::is_unresolved(state s) {
        return (m_unknown.contains(s) || m_unvisited.contains(s));
    }

    /*
        Merge two states or more generally a set of states into one,
        returning the new state.

        Preconditions: the set should be nonempty, and every state
        in the set should be unresolved. Also, each state should
        be current (not a previous SCC that was later merged into another).

        Removes the old state from m_unknown or m_univisited,
        but leaves it in m_seen.
    */
    seq_regex::seen_states::state
            seq_regex::seen_states::merge_states(state s1, state s2) {
        SASSERT(is_unresolved(s1));
        SASSERT(is_unresolved(s2));
        SASSERT(m_state_ufind.is_root(s1));
        SASSERT(m_state_ufind.is_root(s2));
        m_state_ufind.merge(s1, s2);
        if (m_state_ufind.is_root(s1)) std::swap(s1, s2);
        // Remove old state s2
        if (m_unknown.contains(s2)) {
            m_unknown.remove(s2);
        } else {
            m_unvisited.remove(s2);
        }
        return s1;
    }
    seq_regex::seen_states::state
            seq_regex::seen_states::merge_states(state_set& s_set) {
        SASSERT(s_set.num_elems() > 0);
        state prev_s;
        bool first_iter = true;
        for (auto const& s: s_set) {
            if (first_iter) {
                prev_s = s;
                first_iter = false;
            } else {
                prev_s = merge_states(prev_s, s);
            }
        }
        return prev_s;
    }

    bool seq_regex::seen_states::can_be_in_cycle(expr *e1, expr *e2) {
        // Simple placeholder. TODO: Implement full check
        return true;
    }
    void seq_regex::seen_states::find_and_merge_cycles(state s1, state s2) {
        // Search backwards from s1 to see if (s1, s2) creates a cycle.
        if (s1 == s2) return;
        // TODO: Implement full check
        // Simple placeholder for now: check if this is a loop or if there
        // is an edge both ways
        if (m_to.find(s2)->contains(s1)) {
            merge_states(s1, s2);
        }
    }

    void seq_regex::seen_states::add_state(expr* e) {
        unsigned id = e->get_id();
        if (m_seen.contains(id)) return;
        if (m_seen.num_elems() >= m_max_size) {
            STRACE("seq_regex", tout << "Warning: max size of seen states reached!" << std::endl;);
            STRACE("seq_regex_brief", tout << "(MAX SIZE REACHED) ";);
            return;
        }
        // Save e as expr_ref so it's not deleted
        m_trail.push_back(e);
        // Ensure corresponding var in connected components
        while (id >= m_state_ufind.get_num_vars()) {
            m_state_ufind.mk_var();
        }
        // Initialize as unvisited
        m_seen.insert(id);
        m_unvisited.insert(id);
        m_to.insert(id, new state_set());
        m_from_cycle.insert(id, new state_set());
        m_from_nocycle.insert(id, new state_set());
    }
    void seq_regex::seen_states::add_transition(expr* e1, expr* e2) {
        // Precondition: e1 and e2 already correspond to existing states
        SASSERT(m_seen.contains(e1->get_id()));
        SASSERT(m_seen.contains(e2->get_id()));
        state s1 = get_state(e1);
        state s2 = get_state(e2);
        if (s1 == s2) {
            return;
        }
        // TODO:
        // If e1 is dead, assert e1 is marked dead
        // If e1 is live, add edge and return
        // If e2 is live, mark e1 live, propagate backwards
        else if (!can_be_in_cycle(e1, e2)) {
            // Don't need to check for cycles here
            if (m_from_nocycle.find(s2)->contains(s1)) {
                return;
            }
            else if (m_from_cycle.find(s2)->contains(s2)) {
                // update edge label
                m_from_cycle.find(s2)->remove(s2);
                m_from_nocycle.find(s2)->insert(s1);
            }
            else {
                // add edge
                m_to.find(s1)->insert(s2);
                m_from_nocycle.find(s2)->insert(s1);
            }
        }
        else if (m_to.find(s1)->contains(s2)) {
            return;
        }
        else {
            // Need to check for cycles here
            m_to.find(s1)->insert(s2);
            m_from_cycle.find(s2)->insert(s1);
            find_and_merge_cycles(s1, s2);
        }
    }

    bool seq_regex::seen_states::is_alive(expr* e) {
        return m_alive.contains(get_state(e));
    }
    bool seq_regex::seen_states::is_dead(expr* e) {
        return m_dead.contains(get_state(e));
    }

}
