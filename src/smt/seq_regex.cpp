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

    bool seq_regex::propagate() {
        bool change = false;
        for (unsigned i = 0; !ctx.inconsistent() && i < m_to_propagate.size(); ++i) {
            if (propagate(m_to_propagate[i])) {
                m_to_propagate.erase_and_swap(i--);
                change = true;
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
     * Propagate the atom (str.in.re s r)
     * 
     * Propagation implements the following inference rules
     * 
     * (not (str.in.re s r)) => (str.in.re s (complement r))
     * (str.in.re s r) => r != {}
     * 
     * (str.in.re s r) => (accept s 0 r)
     */

    void seq_regex::propagate_in_re(literal lit) {
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));

        TRACE("seq", tout << "propagate " << mk_pp(e, m) << "\n";);

        // convert negative negative membership literals to positive
        // ~(s in R) => s in C(R)
        if (lit.sign()) {
            expr_ref fml(re().mk_in_re(s, re().mk_complement(r)), m);
            rewrite(fml);
            literal nlit = th.mk_literal(fml);
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

        th.propagate_lit(nullptr, 1, &lit, acc_lit);
    }

    void seq_regex::propagate_accept(literal lit) {
        if (!propagate(lit))
            m_to_propagate.push_back(lit);
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
    
    bool seq_regex::propagate(literal lit) {
        SASSERT(!lit.sign());

        expr* s = nullptr, *i = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        unsigned idx = 0;
        VERIFY(sk().is_accept(e, s, i, idx, r));

        TRACE("seq", tout << "propagate " << mk_pp(e, m) << "\n";);

        if (re().is_empty(r)) {
            th.add_axiom(~lit);
            return true;
        }

        if (block_unfolding(lit, idx))
            return true;

        propagate_nullable(lit, e, s, idx, r);

        return propagate_derivative(lit, e, s, i, idx, r);
    }

    /**
       Implement the two axioms as propagations:

       (accept s i r) => len(s) >= i
       (accept s i r) & ~nullable(r) => len(s) >= i + 1
     */

    void seq_regex::propagate_nullable(literal lit, expr* e, expr* s, unsigned idx, expr* r) {
        expr_ref is_nullable = seq_rw().is_nullable(r);
        rewrite(is_nullable);
        literal len_s_ge_i = th.m_ax.mk_ge(th.mk_len(s), idx);
        if (m.is_true(is_nullable)) {
            th.propagate_lit(nullptr, 1,&lit, len_s_ge_i);
        }
        else if (m.is_false(is_nullable)) {
            th.propagate_lit(nullptr, 1, &lit, th.m_ax.mk_ge(th.mk_len(s), idx + 1));
        }
        else {
            literal len_s_le_i = th.m_ax.mk_le(th.mk_len(s), idx);
            switch (ctx.get_assignment(len_s_le_i)) {
            case l_undef:
                th.add_axiom(~lit, ~len_s_le_i, th.mk_literal(is_nullable));
                break;
            case l_true: {
                literal lits[2] = { lit, len_s_le_i };
                th.propagate_lit(nullptr, 2, lits, th.mk_literal(is_nullable));
                break;
            }
            case l_false:
                break;
            }
            th.propagate_lit(nullptr, 1, &lit, len_s_ge_i);
        }
    }
    
    bool seq_regex::propagate_derivative(literal lit, expr* e, expr* s, expr* i, unsigned idx, expr* r) {
        // (accept s i R) & len(s) > i => (accept s (+ i 1) D(nth(s, i), R)) or conds
        expr_ref d(m);
        expr_ref head = th.mk_nth(s, i);

        d = derivative_wrapper(m.mk_var(0, m.get_sort(head)), r);
        // timer tm;
        // std::cout << d->get_id() << " " << tm.get_seconds() << "\n";
        //if (tm.get_seconds() > 0.3) 
        //    std::cout << d << "\n";
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
        TRACE("seq", tout << "unfold " << head << "\n" << mk_pp(r, m) << "\n";);
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
                       mk_pp(entry.m_re, m) << " " << mk_pp(s, m) << " " << mk_pp(entry.m_s, m) << "\n";);
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
        Wrapper around the regex symbolic derivative from the rewriter.
        Ensures that the derivative is written in a normalized BDD form
        with optimizations for if-then-else expressions involving the head.
    */
    expr_ref seq_regex::derivative_wrapper(expr* hd, expr* r) {
        expr_ref result = expr_ref(re().mk_derivative(hd, r), m);
        rewrite(result);
        return result;
    }

    void seq_regex::propagate_eq(expr* r1, expr* r2) {
        expr_ref r = symmetric_diff(r1, r2);       
        expr_ref emp(re().mk_empty(m.get_sort(r)), m);
        expr_ref is_empty = sk().mk_is_empty(r, emp);
        th.add_axiom(~th.mk_eq(r1, r2, false), th.mk_literal(is_empty));
    }
    
    void seq_regex::propagate_ne(expr* r1, expr* r2) {
        expr_ref r = symmetric_diff(r1, r2);
        expr_ref emp(re().mk_empty(m.get_sort(r)), m);
        expr_ref is_non_empty = sk().mk_is_non_empty(r, emp);
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
        expr* e = ctx.bool_var2expr(lit.var()), *r = nullptr, *u = nullptr;
        VERIFY(sk().is_is_non_empty(e, r, u));
        expr_ref is_nullable = seq_rw().is_nullable(r);
        rewrite(is_nullable);
        if (m.is_true(is_nullable))
            return;
        literal null_lit = th.mk_literal(is_nullable);
        expr_ref hd = mk_first(r);
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
            expr_ref next_non_empty = sk().mk_is_non_empty(p.second, re().mk_union(u, r));
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
            cond = mk_and(conds);
            result.push_back(cond, r);
        }
    }

    /*
      is_empty(r, u) => ~is_nullable(r)
      is_empty(r, u) => (forall x . ~cond(x)) or is_empty(r1, u union r)    for (cond, r) in min-terms(D(x,r))      

      is_empty(r, u) is true if r is a member of u
     */
    void seq_regex::propagate_is_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r = nullptr, *u = nullptr;
        VERIFY(sk().is_is_empty(e, r, u));
        expr_ref is_nullable = seq_rw().is_nullable(r);
        rewrite(is_nullable);
        if (m.is_true(is_nullable)) {
            th.add_axiom(~lit);
            return;
        }
        th.add_axiom(~lit, ~th.mk_literal(is_nullable));
        expr_ref hd = mk_first(r);
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
                lits.push_back(th.mk_literal(mk_forall(m, hd, mk_not(m, cond))));
            }
            expr_ref is_empty1 = sk().mk_is_empty(p.second, re().mk_union(u, r));    
            lits.push_back(th.mk_literal(is_empty1)); 
            th.add_axiom(lits);
        }        
    }

    expr_ref seq_regex::mk_first(expr* r) {
        sort* elem_sort = nullptr, *seq_sort = nullptr;
        VERIFY(u().is_re(r, seq_sort));
        VERIFY(u().is_seq(seq_sort, elem_sort));
        return expr_ref(m.mk_fresh_const("re.first", elem_sort), m);
    }
}
