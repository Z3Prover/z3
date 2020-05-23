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
    void seq_regex::rewrite(expr_ref& e) { th.m_rewrite(e); }

    void seq_regex::propagate_in_re(literal lit) {
        if (!propagate(lit))
            m_to_propagate.push_back(lit);
    }

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
     * Propagate the atom (str.in.re s r)
     * 
     * Propagation implements the following inference rules
     * 
     * (not (str.in.re s r)) => (str.in.re s (complement r))
     * (str.in.re s r) => r != {}
     * 
     * (str.in.re s r[if(c,r1,r2)]) & c => (str.in.re s r[r1])
     * (str.in.re s r[if(c,r1,r2)]) & ~c => (str.in.re s r[r2])
     * (str.in.re s r) & s = "" => nullable(r)
     * s != "" => s = unit(head) ++ tail
     * (str.in.re s r) & s != "" => (str.in.re tail D(head,r))
     */
    
    bool seq_regex::propagate(literal lit) {
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));

        TRACE("seq", tout << "propagate " << mk_pp(e, m) << "\n";);

        // only positive assignments of membership propagation are relevant.
        if (lit.sign() && sk().is_tail(s)) 
            return true;

        // convert negative negative membership literals to positive
        // ~(s in R) => s in C(R)
        if (lit.sign()) {
            expr_ref fml(re().mk_in_re(s, re().mk_complement(r)), m);
            rewrite(fml);
            literal nlit = th.mk_literal(fml);
            th.propagate_lit(nullptr, 1, &lit, nlit);
            return true;
        }

        if (!sk().is_tail(s) && coallesce_in_re(lit))
            return true;

        // TBD
        // for !sk().is_tail(s):  s in R => R != {}
        if (false && !sk().is_tail(s)) {
            expr_ref is_empty(m.mk_eq(r, re().mk_empty(m.get_sort(s))), m);
            rewrite(is_empty);
            literal is_emptyl = mk_literal(is_empty);
            if (ctx.get_assignment(is_emptyl) != l_false) {
                th.propagate_lit(nullptr, 1, &lit, ~is_emptyl);
                return true;
            }
        }

        if (block_unfolding(lit, s))
            return true;
       
        // s in R[if(p,R1,R2)] & p => s in R[R1]
        // s in R[if(p,R1,R2)] & ~p => s in R[R2]
        expr_ref cond(m), tt(m), el(m);
        if (seq_rw().has_cofactor(r, cond, tt, el)) {
            literal lcond = th.mk_literal(cond), next_lit;
            switch (ctx.get_assignment(lcond)) {
            case l_true: {
                rewrite(tt);
                literal lits[2] = { lit, lcond };
                next_lit = th.mk_literal(re().mk_in_re(s, tt));
                th.propagate_lit(nullptr, 2, lits, next_lit);
                return true;
            }
            case l_false: {
                rewrite(el);
                next_lit = th.mk_literal(re().mk_in_re(s, el));
                literal lits[2] = { lit, ~lcond };
                th.propagate_lit(nullptr, 2, lits, next_lit);
                return true;
            }
            case l_undef:
                ctx.mark_as_relevant(lcond);
                return false;
            }
        }

        // s in R & s = "" => nullable(R)
        literal is_empty = th.mk_eq(s, str().mk_empty(m.get_sort(s)), false);
        expr_ref is_nullable = seq_rw().is_nullable(r);
        rewrite(is_nullable);
        th.add_axiom(~lit, ~is_empty, th.mk_literal(is_nullable));
        switch (ctx.get_assignment(is_empty)) {
        case l_undef:
            ctx.mark_as_relevant(is_empty);
            return false;
        case l_true:
            return true;
        case l_false:
            break;
        }

        // s in R & s != "" => s = head ++ tail
        // s in R & s != "" => tail in D(head, R)
        expr_ref head(m), tail(m), d(m);
        expr* h = nullptr;
        sk().decompose(s, head, tail);
        if (!str().is_unit(head, h))
            throw default_exception("expected a unit");
        d = seq_rw().derivative(h, r);
        if (!d) 
            throw default_exception("unable to expand derivative");
        th.add_axiom(is_empty, th.mk_eq(s, th.mk_concat(head, tail), false));
        th.add_axiom(~lit, is_empty, th.mk_literal(re().mk_in_re(tail, d)));

        TRACE("seq", tout << "head " << head << "\n";
              tout << mk_pp(r, m) << "\n";);
        return true;
    }

    /**
     * Put a limit to the unfolding of s. 
     * TBD: 
     * Given an Regex R, we can compute the minimal length string accepted by R
     * A strong analysis could compute the minimal length of s to be accepted by R
     * For example if s = x + "abc" and R = .* ++ "def" . .**, then minimal length
     * of s is 6.
     * Limiting the depth of unfolding s below such lengths is not useful.
     */

    bool seq_regex::block_unfolding(literal lit, expr* s) {
        expr* t = nullptr;
        unsigned i = 0;
        if (!sk().is_tail_u(s, t, i))
            return false;
        if (i > th.m_max_unfolding_depth && 
            th.m_max_unfolding_lit != null_literal && 
            ctx.get_assignment(th.m_max_unfolding_lit) == l_true && 
            !ctx.at_base_level()) {
            th.propagate_lit(nullptr, 1, &lit, ~th.m_max_unfolding_lit);
            return true;
        }
        return false;
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
            if (!entry.m_active)
                continue;
            if (th.get_root(entry.m_s) != th.get_root(s))
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
            enode* n1 = th.ensure_enode(entry.m_s);
            enode* n2 = th.ensure_enode(s);
            if (n1 != n2) {
                lits.push_back(~th.mk_eq(n1->get_owner(), n2->get_owner(), false));
            }
        }
        m_s_in_re.push_back(s_in_re(lit, s, regex));
        th.get_trail_stack().push(push_back_vector<theory_seq, vector<s_in_re>>(m_s_in_re));
        if (lits.empty())
            return false;
        lits.push_back(~lit);
        lits.push_back(th.mk_literal(re().mk_in_re(s, regex)));
        ctx.mk_th_axiom(th.get_id(), lits.size(), lits.c_ptr());
        return true;
    }


    void seq_regex::propagate_eq(expr* r1, expr* r2) {
        // the dual version of unroll_non_empty, but
        // skolem functions have to be eliminated or turned into 
        // universal quantifiers.
        throw default_exception("emptiness checking for regex is TBD");
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
        literal lit = ~th.mk_eq(r, re().mk_empty(seq_sort), false);
        expr_mark seen;
        expr_ref non_empty = unroll_non_empty(r, seen, 0);
        if (non_empty) {
            rewrite(non_empty);
            th.add_axiom(~lit, th.mk_literal(non_empty));
        }
        else {
            // generally introduce predicate (re.nonempty r seen)
            // with inference rules based on unroll_non_empty
            throw default_exception("unrolling large regexes is TBD");
        }
    }

    /**
       nonempty(R union Q, Seen) = R = {} or Q = {}
       nonempty(R[if(p,R1,R2)], Seen) = if(p, nonempty(R[R1], Seen), nonempty(R[R2], Seen))           (co-factor)
       nonempty(R, Seen) = nullable(R) or (R not in Seen and nonempty(D(first(R),R), Seen u { R }))  (derivative)
       
       TBD: eliminate variables from p when possible to perform quantifier elimination.
       
       p := first(R) == 'a'
       then replace first(R) by 'a' in R[R1]
       TBD: 
       empty(R, Seen) = R = {} if R does not contain a subterm in Seen and Seen is non-empty


       first : RegEx -> Char is a skolem function
    */

    expr_ref seq_regex::mk_first(expr* r) {
        sort* elem_sort = nullptr, *seq_sort = nullptr;
        VERIFY(u().is_re(r, seq_sort));
        VERIFY(u().is_seq(seq_sort, elem_sort));
        return expr_ref(m.mk_fresh_const("re.first", elem_sort), m);
        // return sk().mk("re.first", r, elem_sort);
    }

    expr_ref seq_regex::unroll_non_empty(expr* r, expr_mark& seen, unsigned depth) {
        if (seen.is_marked(r))
            return expr_ref(m.mk_false(), m);
        if (depth > 300)
            return expr_ref(m);
        expr_ref result(m), cond(m), th(m), el(m);
        // TBD: try also rewriting
        if (seq_rw().has_cofactor(r, cond, th, el)) {
            th = unroll_non_empty(th, seen, depth + 1);
            el = unroll_non_empty(el, seen, depth + 1);
            if (th && el) 
                result = m.mk_ite(cond, th, el);
            return result;
        }    
        expr_ref hd = mk_first(r);
        result = seq_rw().derivative(hd, r);
        if (result) {
            // TBD fast check if r is a subterm of result, if not, then 
            // loop instead of recurse
            seen.mark(r, true);
            result = unroll_non_empty(result, seen, depth + 1);
            seen.mark(r, false);
        }
        return result;
    }
}
