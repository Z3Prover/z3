/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_eval.cpp

Abstract:

    Evaluation of clauses

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/

#include "ast/has_free_vars.h"
#include "sat/smt/q_eval.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/q_solver.h"

namespace q {

    struct eval::scoped_mark_reset {
        eval& e;
        scoped_mark_reset(eval& e): e(e) {}
        ~scoped_mark_reset() { 
            e.m_mark.reset(); 
            e.m_diseq_undef = euf::enode_pair(); 
        }
    };

    eval::eval(euf::solver& ctx):
        ctx(ctx),
        m(ctx.get_manager())
    {}

    lbool eval::operator()(euf::enode* const* binding, clause& c, unsigned& idx, euf::enode_pair_vector& evidence) {
        scoped_mark_reset _sr(*this);
        idx = UINT_MAX;
        unsigned sz = c.m_lits.size();
        unsigned n = c.num_decls();
        m_indirect_nodes.reset();
        for (unsigned j = 0; j < sz; ++j) {
            unsigned i = (j + c.m_watch) % sz;
            unsigned lim = m_indirect_nodes.size();
            lit l = c[i];
            lbool cmp = compare(n, binding, l.lhs, l.rhs, evidence);
            TRACE("q", tout << l.lhs << " ~~ " << l.rhs << " is " << cmp << "\n";);
            switch (cmp) {
            case l_false:                
                m_indirect_nodes.shrink(lim);
                if (!l.sign)
                    break;
                c.m_watch = i;
                return l_true;
            case l_true:   
                m_indirect_nodes.shrink(lim);
                if (l.sign)
                    break;                
                c.m_watch = i;
                return l_true;
            case l_undef:
                if (idx != UINT_MAX) {
                    idx = UINT_MAX;
                    return l_undef;
                }
                idx = i;
                break;
            }
        }
        if (idx == UINT_MAX)
            return l_false;
        c.m_watch = idx;
        return l_undef;
    }

    lbool eval::operator()(euf::enode* const* binding, clause& c, euf::enode_pair_vector& evidence) {
        unsigned idx = 0;
        return (*this)(binding, c, idx, evidence);
    }

    lbool eval::compare(unsigned n, euf::enode* const* binding, expr* s, expr* t, euf::enode_pair_vector& evidence) {
        if (s == t)
            return l_true;
        if (m.are_distinct(s, t))
            return l_false;

        euf::enode* sn = (*this)(n, binding, s, evidence);
        euf::enode* tn = (*this)(n, binding, t, evidence);
        euf::enode* sr = sn ? sn->get_root() : sn;
        euf::enode* tr = tn ? tn->get_root() : tn;
        if (sn != sr) evidence.push_back(euf::enode_pair(sn, sr)), sn = sr;
        if (tn != tr) evidence.push_back(euf::enode_pair(tn, tr)), tn = tr;
        TRACE("q", tout << mk_pp(s, m) << " ~~ " << mk_pp(t, m) << "\n";
              tout << ctx.bpp(sn) << " " << ctx.bpp(tn) << "\n";);
        
        lbool c;
        if (sn && sn == tn) 
            return l_true;
        
        if (sn && sn == m_diseq_undef.first && tn == m_diseq_undef.second) 
            return l_undef;

        if (sn && tn && ctx.get_egraph().are_diseq(sn, tn)) {
            evidence.push_back(euf::enode_pair(sn, tn));
            return l_false;
        }
        if (sn && tn) {
            m_diseq_undef = euf::enode_pair(sn, tn);
            return l_undef;
        }

        if (!sn && !tn) 
            return compare_rec(n, binding, s, t, evidence);

        // in recursive calls we ensure the first argument is decomposed
        if (!tn && sn && m_freeze_swap)
            return l_undef;
        flet<bool> _freeze_swap(m_freeze_swap, true);
        if (!tn && sn) {
            std::swap(tn, sn);
            std::swap(t, s);
        }        
        unsigned sz = evidence.size();
        for (euf::enode* t1 : euf::enode_class(tn)) { 
            if (!t1->is_cgr())
                continue;
            expr* t2 = t1->get_expr();
            if ((c = compare_rec(n, binding, s, t2, evidence), c != l_undef)) {
                evidence.push_back(euf::enode_pair(t1, tn));
                return c;
            }
            evidence.shrink(sz);
        }
        return l_undef;
    }

    // f(p1) = f(p2)  if p1 = p2
    // f(p1) != f(p2) if p1 != p2 and f is injective
    lbool eval::compare_rec(unsigned n, euf::enode* const* binding, expr* s, expr* t, euf::enode_pair_vector& evidence) {
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
        unsigned sz = evidence.size();
        for (unsigned i = to_app(s)->get_num_args(); i-- > 0; ) {
            unsigned sz1 = evidence.size(), sz2;
            switch (compare(n, binding, to_app(s)->get_arg(i), to_app(t)->get_arg(i), evidence)) {
            case l_true:
                break;
            case l_false:                                
                if (!is_injective)
                    return l_undef;
                sz2 = evidence.size();
                for (unsigned i = 0; i < sz2 - sz1; ++i)
                    evidence[sz + i] = evidence[sz1 + i];
                evidence.shrink(sz + sz2 - sz1);
                return l_false;
            case l_undef:
                if (!is_injective)
                    return l_undef;
                has_undef = true;
                break;
            }
        }

        if (!has_undef)
            return l_true;

        evidence.shrink(sz);
        return l_undef;
    }

    euf::enode* eval::operator()(unsigned n, euf::enode* const* binding, expr* e, euf::enode_pair_vector& evidence) {
        if (m_mark.is_marked(e))
            return m_eval[e->get_id()];
        if (is_ground(e))
            return ctx.get_egraph().find(e);
        ptr_buffer<expr> todo;
        ptr_buffer<euf::enode> args;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            SASSERT(!is_ground(t) || ctx.get_egraph().find(t));
            if (m_mark.is_marked(t)) {
                todo.pop_back();
                continue;
            }
            if (is_ground(t) || (has_quantifiers(t) && !m_contains_vars(t))) {
                m_eval.setx(t->get_id(), ctx.get_egraph().find(t), nullptr);                
                if (!m_eval[t->get_id()])
                    return nullptr;
                m_mark.mark(t);
                todo.pop_back();
                continue;
            }
            if (is_var(t)) {
                if (to_var(t)->get_idx() >= n)
                    return nullptr;
                m_eval.setx(t->get_id(), binding[n - 1 - to_var(t)->get_idx()], nullptr);
                if (!m_eval[t->get_id()])
                    return nullptr;
                m_mark.mark(t);
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
                for (unsigned i = args.size(); i-- > 0; ) {
                    euf::enode* a = args[i], *b = n->get_arg(i);
                    if (a == b)
                        continue;

                    // roots could be different when using commutativity
                    // instead of compensating for this, we just bail out
                    if (a->get_root() != b->get_root())
                        return nullptr;

                    TRACE("q", tout << "evidence " << ctx.bpp(a) << " " << ctx.bpp(b) << "\n");
                    evidence.push_back(euf::enode_pair(a, b));
                }
                m_indirect_nodes.push_back(n);
                m_eval.setx(t->get_id(), n, nullptr);
                m_mark.mark(t);
                todo.pop_back();
            }
        }
        return m_eval[e->get_id()];
    }
    
}
