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
     * is_string_equality holds of str.in_re s R, if R is of the form .* ++ x ++ .* ++ y ++ .* ++ 
     * s = fresh1 ++ x ++ fresh2 ++ y ++ fresh3
     * 
     * example rewrite:
     * (str.in_re s .* ++ R) => s = x ++ y and (str.in_re y R)
     * 
     * is_string_equality is currently placed under propagate_accept.
     * this allows extracting string equalities after processing regexes that are not
     * simple unions of simple concatentations. Though, it may produce different equations for 
     * alternate values of the unfolding index.
     */

    bool seq_regex::is_string_equality(literal lit) {
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

       
    // s in R[if(p,R1,R2)] & p => s in R[R1]
    // s in R[if(p,R1,R2)] & ~p => s in R[R2]

    bool seq_regex::unfold_cofactors(expr_ref& r, literal_vector& conds) {
        expr_ref cond(m), tt(m), el(m);
        while (seq_rw().has_cofactor(r, cond, tt, el)) {
            rewrite(cond);
            literal lcond = th.mk_literal(cond);
            switch (ctx.get_assignment(lcond)) {
            case l_true: 
                conds.push_back(~lcond);
                r = tt;
                break;
            case l_false:
                conds.push_back(lcond);
                r = el;
                break;
            case l_undef:
                ctx.mark_as_relevant(lcond);
                return false;
            }
            rewrite(r);
        }
        return true;
    }

    /**
     * Propagate the atom (accept s i r)
     * 
     * Propagation implements the following inference rules
     *
     * (accept s i r[if(c,r1,r2)]) & c => (accept s i r[r1])
     * (accept s i r[if(c,r1,r2)]) & ~c => (accept s i r[r2])
     * (accept s i r) & len(s) <= i => nullable(r)
     * (accept s i r) & len(s) > i => (accept s (+ i 1) D(nth(s,i), r))
     */
    
    bool seq_regex::propagate(literal lit) {
        SASSERT(!lit.sign());

        expr* s = nullptr, *i = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        unsigned idx = 0;
        VERIFY(sk().is_accept(e, s, i, idx, r));
        expr_ref is_nullable(m), d(r, m);

        TRACE("seq", tout << "propagate " << mk_pp(e, m) << "\n";);

        if (is_string_equality(lit))
            return true;

        if (block_unfolding(lit, idx))
            return true;

        // s in R & len(s) <= i => nullable(R)
        literal len_s_le_i = th.m_ax.mk_le(th.mk_len(s), idx);
        switch (ctx.get_assignment(len_s_le_i)) {
        case l_undef:
            ctx.mark_as_relevant(len_s_le_i);
            return false;
        case l_true: 
            is_nullable = seq_rw().is_nullable(r);
            rewrite(is_nullable);
            th.add_axiom(~lit, ~len_s_le_i, th.mk_literal(is_nullable));
            return true;
        case l_false:
            break;
        }

        literal_vector conds;
        if (!unfold_cofactors(d, conds)) 
            return false;

        // (accept s i R) & len(s) > i => (accept s (+ i 1) D(nth(s, i), R)) or conds
        expr_ref head = th.mk_nth(s, i);        
        d = seq_rw().derivative(head, d);
        if (!d) 
            throw default_exception("unable to expand derivative");

        literal acc_next = th.mk_literal(sk().mk_accept(s, a().mk_int(idx + 1), d));
        conds.push_back(~lit);
        conds.push_back(len_s_le_i);
        conds.push_back(acc_next);
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
        // initially disable this
        return false;
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));
        expr_ref regex(r, m);
        literal_vector lits;    
        for (unsigned i = 0; i < m_s_in_re.size(); ++i) {
            auto const& entry = m_s_in_re[i];
            enode* n1 = th.ensure_enode(entry.m_s);
            enode* n2 = th.ensure_enode(s);
            if (!entry.m_active)
                continue;
            if (n1->get_root() != n2->get_root())
                continue;
            if (entry.m_re == regex) 
                continue;

            th.m_trail_stack.push(vector_value_trail<theory_seq, s_in_re, true>(m_s_in_re, i));
            m_s_in_re[i].m_active = false;
            IF_VERBOSE(11, verbose_stream() << "intersect " << regex << " " << 
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

    void seq_regex::propagate_eq(expr* r1, expr* r2) {
        expr_ref r(m);
        if (re().is_empty(r1)) 
            std::swap(r1, r2);
        if (re().is_empty(r2))
            r = r1;
        else 
            r = re().mk_union(re().mk_diff(r1, r2), re().mk_diff(r2, r1));
        rewrite(r);
        sort* seq_sort = nullptr;        
        VERIFY(u().is_re(r, seq_sort));
        expr_ref emp(re().mk_empty(seq_sort), m);
        literal lit = ~th.mk_eq(r, emp, false);
        expr_ref is_empty = sk().mk_is_empty(r, emp);
        th.add_axiom(~lit, th.mk_literal(is_empty));
    }
    
    void seq_regex::propagate_ne(expr* r1, expr* r2) {
        expr_ref r(m);
        if (re().is_empty(r1)) 
            std::swap(r1, r2);
        if (re().is_empty(r2))
            r = r1;
        else 
            r = re().mk_union(re().mk_diff(r1, r2), re().mk_diff(r2, r1));
        rewrite(r);
        sort* seq_sort = nullptr;        
        VERIFY(u().is_re(r, seq_sort));
        expr_ref emp(re().mk_empty(seq_sort), m);
        literal lit = ~th.mk_eq(r, emp, false);
        expr_ref is_non_empty = sk().mk_is_non_empty(r, emp);
        th.add_axiom(~lit, th.mk_literal(is_non_empty));
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
     * is_non_empty(r, u) => nullable or not c_i or is_non_empty(r_i, u union r)
     *
     * for each (c_i, r_i) in cofactors
     *
     * is_non_empty(r_i, u union r) := false if r_i in u
     *
     */
    void seq_regex::propagate_is_non_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r, *u;
        VERIFY(sk().is_is_non_empty(e, r, u));
        expr_ref is_nullable = seq_rw().is_nullable(r);
        rewrite(is_nullable);
        if (m.is_true(is_nullable))
            return;
        literal null_lit = th.mk_literal(is_nullable);
        expr_ref hd = mk_first(r);
        expr_ref d = seq_rw().derivative(hd, r);
        if (!d)
            throw default_exception("derivative was not defined");
        literal_vector lits;
        expr_ref_pair_vector cofactors(m);
        seq_rw().get_cofactors(d, cofactors);
        for (auto const& p : cofactors) {
            expr_ref cond(p.first, m);
            seq_rw().elim_condition(hd, cond);
            rewrite(cond);
            if (m.is_false(cond))
                continue;            
            lits.reset();
            lits.push_back(~lit);
            if (!m.is_true(cond))
                lits.push_back(~th.mk_literal(cond));
            if (false_literal != null_lit) 
                lits.push_back(null_lit);
            if (!is_member(p.second, u))
                lits.push_back(th.mk_literal(sk().mk_is_non_empty(p.second, re().mk_union(u, r))));
            th.add_axiom(lits);
        }
    }


    /*
      is_empty(r, u) => ~is_nullable(r)
      is_empty(r, u) => (forall x . ~cond(x)) or is_empty(r1, u union r)    for (cond, r) in min-terms(D(x,r))      

      is_empty(r, u) is true if r is a member of u
     */
    void seq_regex::propagate_is_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r, *u;
        VERIFY(sk().is_is_empty(e, r, u));
        expr_ref is_nullable = seq_rw().is_nullable(r);
        rewrite(is_nullable);
        if (m.is_true(is_nullable)) {
            th.add_axiom(~lit);
            return;
        }
        th.add_axiom(~lit, ~th.mk_literal(is_nullable));
        expr_ref hd = mk_first(r);
        expr_ref d = seq_rw().derivative(hd, r);
        if (!d)
            throw default_exception("derivative was not defined");
        literal_vector lits;
        expr_ref_pair_vector cofactors(m);
        seq_rw().get_cofactors(d, cofactors);

        // is_empty(r, u) => forall hd . cond => is_empty(r1, u union r)
        
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
            expr_ref is_empty1 = sk().mk_is_non_empty(p.second, re().mk_union(u, r));
            if (!m.is_true(cond)) {
                lits.push_back(th.mk_literal(mk_forall(m, hd, m.mk_not(cond))));
            }
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
