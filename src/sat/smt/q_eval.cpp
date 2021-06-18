/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_eval.cpp

Abstract:

    Evaluation of clauses

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/

#include "sat/smt/q_eval.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/q_solver.h"

namespace q {

    struct eval::scoped_mark_reset {
        eval& e;
        scoped_mark_reset(eval& e): e(e) {}
        ~scoped_mark_reset() { e.m_mark.reset(); }
    };

    eval::eval(euf::solver& ctx):
        ctx(ctx),
        m(ctx.get_manager())
    {}

    lbool eval::operator()(euf::enode* const* binding, clause& c, unsigned& idx) {
        scoped_mark_reset _sr(*this);
        idx = UINT_MAX;
        unsigned sz = c.m_lits.size();
        unsigned n = c.num_decls();
        m_indirect_nodes.reset();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned lim = m_indirect_nodes.size();
            lit l = c[i];
            lbool cmp = compare(n, binding, l.lhs, l.rhs);
            switch (cmp) {
            case l_false:
                m_indirect_nodes.shrink(lim);
                if (!l.sign)
                    break;
                if (i > 0)
                    std::swap(c[0], c[i]);
                return l_true;
            case l_true:
                m_indirect_nodes.shrink(lim);
                if (l.sign)
                    break;
                if (i > 0)
                    std::swap(c[0], c[i]);
                return l_true;
            case l_undef:
                TRACE("q", tout << l.lhs << " ~~ " << l.rhs << " is undef\n";);
                if (idx == 0) {
                    idx = UINT_MAX;
                    return l_undef;
                }
                if (i > 0)
                    std::swap(c[0], c[i]);
                idx = 0;
                break;
            }
        }
        if (idx == UINT_MAX)
            return l_false;
        
        return l_undef;
    }

    lbool eval::operator()(euf::enode* const* binding, clause& c) {
        unsigned idx = 0;
        return (*this)(binding, c, idx);
    }

    lbool eval::compare(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        if (s == t)
            return l_true;
        if (m.are_distinct(s, t))
            return l_false;

        euf::enode* sn = (*this)(n, binding, s);
        euf::enode* tn = (*this)(n, binding, t);
        if (sn) sn = sn->get_root();
        if (tn) tn = tn->get_root();
        TRACE("q", tout << mk_pp(s, m) << " ~~ " << mk_pp(t, m) << "\n";
              tout << ctx.bpp(sn) << " " << ctx.bpp(tn) << "\n";);
        
        lbool c;
        if (sn && sn == tn)
            return l_true;
        if (sn && tn && ctx.get_egraph().are_diseq(sn, tn))
            return l_false;
        if (sn && tn)
            return l_undef;
        if (!sn && !tn) 
            return compare_rec(n, binding, s, t);
        if (!tn && sn) {
            std::swap(tn, sn);
            std::swap(t, s);
        }
        for (euf::enode* t1 : euf::enode_class(tn)) 
            if (c = compare_rec(n, binding, s, t1->get_expr()), c != l_undef)
                return c;
        return l_undef;
    }

    // f(p1) = f(p2)  if p1 = p2
    // f(p1) != f(p2) if p1 != p2 and f is injective
    lbool eval::compare_rec(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        if (m.are_equal(s, t))
            return l_true;
        if (m.are_distinct(s, t))
            return l_false;
        if (!is_app(s) || !is_app(t))
            return l_undef;
        if (to_app(s)->get_decl() != to_app(t)->get_decl())
            return l_undef;
        if (to_app(s)->get_num_args() != to_app(t)->get_num_args())
            return l_undef;
        bool is_injective = to_app(s)->get_decl()->is_injective();
        bool has_undef = false;
        for (unsigned i = to_app(s)->get_num_args(); i-- > 0; ) {
            switch (compare(n, binding, to_app(s)->get_arg(i), to_app(t)->get_arg(i))) {
            case l_true:
                break;
            case l_false:
                if (is_injective)
                    return l_false;
                return l_undef;
            case l_undef:
                if (!is_injective)
                    return l_undef;
                has_undef = true;
                break;
            }
        }
        return has_undef ? l_undef : l_true;
    }

    euf::enode* eval::operator()(unsigned n, euf::enode* const* binding, expr* e) {
        if (is_ground(e))
            return ctx.get_egraph().find(e);
        if (m_mark.is_marked(e))
            return m_eval[e->get_id()];
        ptr_buffer<expr> todo;
        ptr_buffer<euf::enode> args;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            SASSERT(!is_ground(t) || ctx.get_egraph().find(t));
            if (is_ground(t)) {
                m_mark.mark(t);
                m_eval.setx(t->get_id(), ctx.get_egraph().find(t), nullptr);
                SASSERT(m_eval[t->get_id()]);
                todo.pop_back();
                continue;
            }
            if (m_mark.is_marked(t)) {
                todo.pop_back();
                continue;
            }
            if (is_var(t)) {
                m_mark.mark(t);
                m_eval.setx(t->get_id(), binding[n - 1 - to_var(t)->get_idx()], nullptr);
                todo.pop_back();
                continue;
            }
            if (!is_app(t))
                return nullptr;
            args.reset();
            for (expr* arg : *to_app(t)) {
                if (m_mark.is_marked(arg))
                    args.push_back(m_eval[arg->get_id()]);
                else
                    todo.push_back(arg);
            }
            if (args.size() == to_app(t)->get_num_args()) {
                euf::enode* n = ctx.get_egraph().find(t, args.size(), args.data());
                if (!n)
                    return nullptr;
                m_indirect_nodes.push_back(n);
                m_eval.setx(t->get_id(), n, nullptr);
                m_mark.mark(t);
                todo.pop_back();
            }
        }
        return m_eval[e->get_id()];
    }

    void eval::explain(clause& c, unsigned literal_idx, euf::enode* const* b) {
        unsigned n = c.num_decls();
        for (unsigned i = c.size(); i-- > 0; ) {
            if (i == literal_idx) 
                continue;
            auto const& lit = c[i];
            if (lit.sign) 
                explain_eq(n, b, lit.lhs, lit.rhs);
            else 
                explain_diseq(n, b, lit.lhs, lit.rhs);
        }
    }

    void eval::explain_eq(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        SASSERT(l_true == compare(n, binding, s, t));
        if (s == t)
            return;
        euf::enode* sn = (*this)(n, binding, s);
        euf::enode* tn = (*this)(n, binding, t);
        if (sn && tn) {
            SASSERT(sn->get_root() == tn->get_root());
            ctx.add_antecedent(sn, tn);
            return;
        }
        if (!sn && tn) {
            std::swap(sn, tn);
            std::swap(s, t);
        }
        if (sn && !tn) {
            for (euf::enode* s1 : euf::enode_class(sn)) {
                if (l_true == compare_rec(n, binding, t, s1->get_expr())) {
                    ctx.add_antecedent(sn, s1);
                    explain_eq(n, binding, t, s1->get_expr());
                    return;
                }
            }
            UNREACHABLE();
        }
        SASSERT(is_app(s) && is_app(t));
        SASSERT(to_app(s)->get_decl() == to_app(t)->get_decl());
        for (unsigned i = to_app(s)->get_num_args(); i-- > 0; ) 
            explain_eq(n, binding, to_app(s)->get_arg(i), to_app(t)->get_arg(i));
    }

    void eval::explain_diseq(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        SASSERT(l_false == compare(n, binding, s, t));
        if (m.are_distinct(s, t))
            return;
        euf::enode* sn = (*this)(n, binding, s);
        euf::enode* tn = (*this)(n, binding, t);
        if (sn && tn && ctx.get_egraph().are_diseq(sn, tn)) {
            ctx.add_diseq_antecedent(sn, tn);
            return;
        }
        if (!sn && tn) {
            std::swap(sn, tn);
            std::swap(s, t);
        }
        if (sn && !tn) {
            for (euf::enode* s1 : euf::enode_class(sn)) {
                if (l_false == compare_rec(n, binding, t, s1->get_expr())) {
                    ctx.add_antecedent(sn, s1);
                    explain_diseq(n, binding, t, s1->get_expr());
                    return;
                }
            }
            UNREACHABLE();
        }
        SASSERT(is_app(s) && is_app(t));
        app* at = to_app(t);
        app* as = to_app(s);
        SASSERT(as->get_decl() == at->get_decl());
        for (unsigned i = as->get_num_args(); i-- > 0; ) {
            if (l_false == compare_rec(n, binding, as->get_arg(i), at->get_arg(i))) {                
                explain_eq(n, binding, as->get_arg(i), at->get_arg(i));
                return;
            }
        }
        UNREACHABLE();
    }


    void eval::explain(sat::literal l, justification& j, sat::literal_vector& r, bool probing) {
        scoped_mark_reset _sr(*this);
        unsigned l_idx = 0;
        clause& c = j.m_clause;
        for (; l_idx < c.size(); ++l_idx) {
            if (c[l_idx].lhs == j.m_lhs && c[l_idx].rhs == j.m_rhs && c[l_idx].sign == j.m_sign)
                break;
        }
        explain(c, l_idx, j.m_binding);
        r.push_back(c.m_literal);
        (void)probing; // ignored
    }

    
}
