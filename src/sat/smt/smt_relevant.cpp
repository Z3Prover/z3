/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_relevant.cpp

Abstract:

    Relevancy propagation

Author:

    Nikolaj Bjorner (nbjorner) 2021-12-27

--*/
#include "sat/sat_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/smt_relevant.h"


namespace smt {

    relevancy::relevancy(euf::solver& ctx): ctx(ctx) {
    }

    void relevancy::relevant_eh(euf::enode* n) {
        SASSERT(is_relevant(n));
        ctx.relevant_eh(n);
    }

    void relevancy::relevant_eh(sat::literal lit) {
        SASSERT(ctx.s().value(lit) == l_true);
        SASSERT(is_relevant(lit));
        ctx.asserted(lit);
    }
    
    void relevancy::pop(unsigned n) {
        if (n <= m_num_scopes) {
            m_num_scopes -= n;
            return;
        }
        else if (m_num_scopes > 0) {
            n -= m_num_scopes;
            m_num_scopes = 0;
        }
        SASSERT(n > 0);
        unsigned sz = m_lim[m_lim.size() - n];
        for (unsigned i = m_trail.size(); i-- > sz; ) {
            auto [u, idx] = m_trail[i];
            switch (u) {
            case update::relevant_var:
                m_relevant_var_ids[idx] = false;
                m_queue.pop_back();
                break;
            case update::add_clause: {
                sat::clause* c = m_clauses.back();
                for (sat::literal lit : *c) {
                    SASSERT(m_occurs[lit.index()].back() == m_clauses.size() - 1);
                    m_occurs[lit.index()].pop_back();
                }
                m_clauses.pop_back();
                m_roots.pop_back();
                m_alloc.del_clause(c);
                break;
            }
            case update::set_root:
                m_roots[idx] = false;
                break;
            case update::set_qhead:
                m_qhead = idx;
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        m_trail.shrink(sz);
        m_lim.shrink(m_lim.size() - n);
    }
    
    void relevancy::add_root(unsigned n, sat::literal const* lits) {
        if (!m_enabled)
            return;
        flush();
        sat::literal true_lit = sat::null_literal;
        for (unsigned i = 0; i < n; ++i) {
            if (ctx.s().value(lits[i]) == l_true) {
                if (is_relevant(lits[i]))
                    return;
                true_lit = lits[i];                
            }
        }
        if (true_lit != sat::null_literal) {
            mark_relevant(true_lit);
            return;
        }

        sat::clause* cl = m_alloc.mk_clause(n, lits, false);
        unsigned sz = m_clauses.size();
        m_clauses.push_back(cl);
        m_roots.push_back(true);
        m_trail.push_back(std::make_pair(update::add_clause, 0));
        for (sat::literal lit : *cl) {
            ctx.s().set_external(lit.var());
            occurs(lit).push_back(sz);
        }
    }
    
    void relevancy::add_def(unsigned n, sat::literal const* lits) {
        if (!m_enabled)
            return;
        flush();
        for (unsigned i = 0; i < n; ++i) {
            if (ctx.s().value(lits[i]) == l_false && is_relevant(lits[i])) {
                add_root(n, lits);
                return;
            }
        }
        sat::clause* cl = m_alloc.mk_clause(n, lits, false);
        unsigned sz = m_clauses.size();
        m_clauses.push_back(cl);
        m_roots.push_back(false);
        m_trail.push_back(std::make_pair(update::add_clause, 0));
        for (sat::literal lit : *cl) {
            ctx.s().set_external(lit.var());
            occurs(lit).push_back(sz);
        }
    }

    void relevancy::asserted(sat::literal lit) {
        if (!m_enabled)
            return;
        flush();
        if (ctx.s().lvl(lit) <= ctx.s().search_lvl()) {
            mark_relevant(lit);
            return;
        }
        for (auto idx : occurs(lit)) {
            if (!m_roots[idx])
                continue;
            for (sat::literal lit2 : *m_clauses[idx]) 
                if (lit2 != lit && ctx.s().value(lit2) == l_true && is_relevant(lit2))
                    goto next;                       
            mark_relevant(lit);
            return;
        next:
            ;
        }
    }

    void relevancy::propagate() {
        if (!m_enabled)
            return;
        flush();
        if (m_qhead == m_queue.size())
            return;
        m_trail.push_back(std::make_pair(update::set_qhead, m_qhead));
        while (m_qhead < m_queue.size() && !ctx.s().inconsistent() && ctx.get_manager().inc()) {
            auto [lit, n] = m_queue[m_qhead++];
            SASSERT(n || lit != sat::null_literal);
            SASSERT(!n || lit == sat::null_literal);
            if (n)
                propagate_relevant(n);
            else 
                propagate_relevant(lit);            
        }
    }

    void relevancy::merge(euf::enode* root, euf::enode* other) {
        if (is_relevant(root))
            mark_relevant(other);
        else if (is_relevant(other))
            mark_relevant(root);
    }
    
    void relevancy::mark_relevant(euf::enode* n) {
        if (!m_enabled)
            return;
        flush();
        if (is_relevant(n))
            return;
        if (ctx.get_si().is_bool_op(n->get_expr()))
            return; 
        for (euf::enode* sib : euf::enode_class(n))
            set_relevant(sib);
    }

    void relevancy::set_relevant(euf::enode* n) {
        if (n->is_relevant())
            return;
        ctx.get_egraph().set_relevant(n);
        m_queue.push_back(std::make_pair(sat::null_literal, n));
    }

    void relevancy::mark_relevant(sat::literal lit) {
        if (!m_enabled)
            return;
        flush();
        if (is_relevant(lit))
            return;        
        euf::enode* n = ctx.bool_var2enode(lit.var());
        if (n)
            mark_relevant(n);
        m_relevant_var_ids.setx(lit.var(), true, false);
        m_trail.push_back(std::make_pair(update::relevant_var, lit.var()));
        m_queue.push_back(std::make_pair(lit, nullptr));
    }

    void relevancy::propagate_relevant(sat::literal lit) {
        relevant_eh(lit);
        euf::enode* n = ctx.bool_var2enode(lit.var());
        if (n && !ctx.get_si().is_bool_op(n->get_expr()))
            return;
        for (auto idx : occurs(~lit)) {
            if (m_roots[idx])
                continue;
            sat::clause* cl = m_clauses[idx];
            sat::literal true_lit = sat::null_literal;
            for (sat::literal lit2 : *cl) {
                if (ctx.s().value(lit2) == l_true) {
                    if (is_relevant(lit2))
                        goto next;
                    true_lit = lit2;
                }
            }

            if (true_lit != sat::null_literal)
                mark_relevant(true_lit);
            else {
                m_trail.push_back(std::make_pair(update::set_root, idx));
                m_roots[idx] = true;
            }
        next:
            ;
        }
    }

    void relevancy::propagate_relevant(euf::enode* n) {
        relevant_eh(n);
        for (euf::enode* arg : euf::enode_args(n))
            mark_relevant(arg);
    }

    void relevancy::set_enabled(bool e) {
        m_enabled = e;
        ctx.get_egraph().set_default_relevant(!e);
    }

}
