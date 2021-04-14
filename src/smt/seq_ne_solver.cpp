/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_ne_solver.cpp

Abstract:

    Features from theory_seq that are specific to solving dis-equations.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12
*/

#include <typeinfo>
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_trail.h"
#include "ast/for_each_expr.h"
#include "smt/smt_context.h"
#include "smt/theory_seq.h"
#include "smt/theory_arith.h"

using namespace smt;

bool theory_seq::solve_nqs(unsigned i) {
    for (; !ctx.inconsistent() && i < m_nqs.size(); ++i) {
        if (solve_ne(i)) {
            m_nqs.erase_and_swap(i--);
        }
    }
    return m_new_propagation || ctx.inconsistent();
}


bool theory_seq::solve_ne(unsigned idx) {
    TRACE("seq", display_disequation(tout << "solve: ", m_nqs[idx]););
    unsigned num_undef_lits = 0;
    return 
        (!check_ne_literals(idx, num_undef_lits))
        || (num_undef_lits <= 1 && propagate_ne2lit(idx))
        || (num_undef_lits == 0 && propagate_ne2eq(idx))
        || reduce_ne(idx);
}
        
bool theory_seq::check_ne_literals(unsigned idx, unsigned& num_undef_lits) {
    ne const& n = m_nqs[idx];
    for (literal lit : n.lits()) {
        switch (ctx.get_assignment(lit)) {
        case l_false:
            TRACE("seq", display_disequation(tout << "has false literal\n", n);
                  ctx.display_literal_verbose(tout, lit);
                  tout << "\n" << lit << " " << ctx.is_relevant(lit) << "\n";
                  display(tout);
                  );
            return false;
        case l_true:
            break;
        case l_undef:
            ++num_undef_lits;
            break;
        }
    }
    return true;
}

/*
  \brief propagate if there is a single undefined literal, others are true.
*/

bool theory_seq::propagate_ne2lit(unsigned idx) {
    ne const& n = m_nqs[idx];
    if (!n.eqs().empty()) {
        return false;
    }
    literal_vector lits;
    literal undef_lit = null_literal;
    for (literal lit : n.lits()) {
        switch (ctx.get_assignment(lit)) {
        case l_true:
            lits.push_back(lit);
            break;
        case l_false:
            return true;
            break;
        case l_undef:
            if (undef_lit != null_literal)
                return false;
            undef_lit = lit;
            break;
        }
    }
    if (undef_lit == null_literal) {
        dependency* dep = n.dep();
        dependency* dep1 = nullptr;
        if (explain_eq(n.l(), n.r(), dep1)) {
            literal diseq = mk_eq(n.l(), n.r(), false);
            if (ctx.get_assignment(diseq) == l_false) {
                lits.reset();                
                lits.push_back(~diseq);
                dep = dep1;
                TRACE("seq", tout << "conflict explained\n";);
            }
        }
        set_conflict(dep, lits);
    }
    else {
        TRACE("seq", tout << "propagate: " << undef_lit << "\n";);
        propagate_lit(n.dep(), lits.size(), lits.data(), ~undef_lit);
    }
    return true;
}

/*
  \brief propagate "" != s into s = head(s) + tail(s)
  Assumes all literals are assigned to true.
*/
bool theory_seq::propagate_ne2eq(unsigned idx) {
    ne const& n = m_nqs[idx];
    if (n.eqs().size() != 1)
        return false;
    auto const& l = n[0].first;
    auto const& r = n[0].second;
    if (l.empty()) 
        return propagate_ne2eq(idx, r);
    if (r.empty())
        return propagate_ne2eq(idx, l);
    return false;
}
 
bool theory_seq::propagate_ne2eq(unsigned idx, expr_ref_vector const& es) {
    if (es.empty())
        return false;
    for (expr* e : es) {
        expr_ref len_e = mk_len(e);
        rational lo;
        if (lower_bound(len_e, lo) && lo > 0) {
            return true;
        }
    }
    ne const& n = m_nqs[idx];
    expr_ref e(m), head(m), tail(m);
    e = mk_concat(es, es[0]->get_sort());
    m_sk.decompose(e, head, tail);
    propagate_eq(n.dep(), n.lits(), e, mk_concat(head, tail), true);
    return true;
}
 
bool theory_seq::reduce_ne(unsigned idx) {
    ne const& n = m_nqs[idx];
    bool updated = false;
    dependency* new_deps = n.dep();
    vector<decomposed_eq> new_eqs;
    literal_vector new_lits(n.lits());
    for (unsigned i = 0; i < n.eqs().size(); ++i) {
        auto const& p = n[i];
        expr_ref_vector& ls = m_ls;
        expr_ref_vector& rs = m_rs;
        expr_ref_pair_vector& eqs = m_new_eqs;
        ls.reset(); rs.reset(); eqs.reset();
        dependency* deps = nullptr;
        bool change = false;
        if (!canonize(p.first,  ls, deps, change)) return false;
        if (!canonize(p.second, rs, deps, change)) return false;
        new_deps = m_dm.mk_join(deps, new_deps);
        bool is_sat = m_seq_rewrite.reduce_eq(ls, rs, eqs, change);

        TRACE("seq", display_disequation(tout << "reduced\n", n);
              tout << p.first << " -> " << ls << "\n";
              tout << p.second << " -> " << rs << "\n";
              tout << eqs << "\n";
              );
        
        if (!is_sat) {
            return true;
        }
        
        if (!change) {
            TRACE("seq", tout << "no change " << p.first << " " << p.second << "\n";);
            if (updated) {
                new_eqs.push_back(p);
            }
            continue;
        }

        if (!updated) {
            for (unsigned j = 0; j < i; ++j) {
                new_eqs.push_back(n[j]);
            }
            updated = true;
        }
        if (!ls.empty() || !rs.empty()) {
            new_eqs.push_back(decomposed_eq(ls, rs));
        }
        TRACE("seq",
              tout << "num eqs: " << eqs.size() << "\n";
              tout << "num new eqs: " << new_eqs.size() << "\n";
              tout << eqs << "\n";
              for (auto const& p : new_eqs) tout << p.first << " != " << p.second << "\n";
              tout << p.first << " != " << p.second << "\n";);
        
        for (auto const& p : eqs) {
            expr* nl = p.first;
            expr* nr = p.second;
            if (m_util.is_seq(nl) || m_util.is_re(nl)) {
                ls.reset();
                rs.reset(); 
                m_util.str.get_concat_units(nl, ls);
                m_util.str.get_concat_units(nr, rs);
                new_eqs.push_back(decomposed_eq(ls, rs));
            }
            else if (nl != nr) {                
                literal lit(mk_eq(nl, nr, false));
                ctx.mark_as_relevant(lit);
                new_lits.push_back(lit);
                switch (ctx.get_assignment(lit)) {
                case l_false:
                    return true;
                case l_true:
                    break;
                case l_undef:
                    m_new_propagation = true;
                    break;
                }
            }
        }
    }

    if (updated) {
        TRACE("seq", display_disequation(tout, n););
        m_nqs.set(idx, ne(n.l(), n.r(), new_eqs, new_lits, new_deps));
        TRACE("seq", display_disequation(tout << "updated:\n", m_nqs[idx]););
    }
    return false;
}


bool theory_seq::branch_nqs() {
   for (unsigned i = 0; i < m_nqs.size(); ++i) {
       ne n = m_nqs[i];
       lbool r = branch_nq(n);
       switch (r) {
       case l_undef: // needs assignment to a literal.
           return true;
       case l_true:  // disequality is satisfied.
           m_nqs.erase_and_swap(i--);
           break;
       case l_false: // needs to be expanded.
           m_nqs.erase_and_swap(i--);
           return true;
       }
   }
   return false;
}

lbool theory_seq::branch_nq(ne const& n) {
    expr_ref len_l(mk_len(n.l()), m);
    expr_ref len_r(mk_len(n.r()), m);
#if 0
    // TBD: breaks 
    if (!has_length(n.l())) {
        enque_axiom(len_l);
        add_length(n.l(), len_l);
        return l_undef;
    }
    if (!has_length(n.r())) {
        enque_axiom(len_r);
        add_length(n.r(), len_r);
        return l_undef;
    }
#endif
    literal eq_len = mk_eq(len_l, len_r, false);
    ctx.mark_as_relevant(eq_len);
    switch (ctx.get_assignment(eq_len)) {
    case l_false:
        TRACE("seq", 
              display_disequation(tout, n);
              ctx.display_literal_smt2(tout << "lengths are different: ", eq_len) << "\n";);
        return l_true;
    case l_undef:
        return l_undef;
    default:
        break;
    }
    literal eq = mk_eq(n.l(), n.r(), false);
    literal len_gt = mk_literal(m_autil.mk_ge(mk_len(n.l()), m_autil.mk_int(1)));
    ctx.mark_as_relevant(len_gt);
    switch (ctx.get_assignment(len_gt)) {
    case l_false:
        add_axiom(eq, ~eq_len, len_gt);
        return l_false;
    case l_undef:
        return l_undef;
    default:
        break;
    }

    expr_ref h1(m), t1(m), h2(m), t2(m);
    mk_decompose(n.l(), h1, t1);
    mk_decompose(n.r(), h2, t2);
    literal eq_head = mk_eq(h1, h2, false);
    ctx.mark_as_relevant(eq_head);
    switch (ctx.get_assignment(eq_head)) {
    case l_false:
        TRACE("seq", ctx.display_literal_smt2(tout << "heads are different: ", eq_head) << "\n";);
        return l_true;
    case l_undef:
        return l_undef;
    default:
        break;
    }
    // l = r or |l| != |r| or |l| > 0
    // l = r or |l| != |r| or h1 != h2 or t1 != t2
    add_axiom(eq, ~eq_len, len_gt);
    add_axiom(eq, ~eq_len, ~eq_head, ~mk_eq(t1, t2, false));
    return l_false;
}

