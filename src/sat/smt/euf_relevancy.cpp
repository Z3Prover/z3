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
#include "sat/smt/euf_relevancy.h"


namespace euf {
    
    void relevancy::pop(unsigned n) {
        if (!m_enabled)
            return;
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
            auto const& [u, idx] = m_trail[i];
            switch (u) {
            case update::relevant_var:
                m_relevant_var_ids[idx] = false;
                break;
            case update::add_queue:
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
        TRACE("relevancy", tout << "root " << sat::literal_vector(n, lits) << "\n");
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
        TRACE("relevancy", tout << "def " << sat::literal_vector(n, lits) << "\n");
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

    void relevancy::add_to_propagation_queue(sat::literal lit) {
        m_trail.push_back(std::make_pair(update::add_queue, lit.var()));
        m_queue.push_back(std::make_pair(lit, nullptr));
    }

    void relevancy::set_relevant(sat::literal lit) {
        euf::enode* n = ctx.bool_var2enode(lit.var());
        if (n)
            mark_relevant(n);        
        m_relevant_var_ids.setx(lit.var(), true, false);
        m_trail.push_back(std::make_pair(update::relevant_var, lit.var()));
    }

    void relevancy::set_asserted(sat::literal lit) {
        SASSERT(!is_relevant(lit));
        SASSERT(ctx.s().value(lit) == l_true);
        set_relevant(lit);
        add_to_propagation_queue(lit);
        ctx.asserted(lit);
    }

    /**
    * Boolean variable is set relevant because an E-node is relevant.
    * 
    */
    void relevancy::relevant_eh(sat::bool_var v) {
        if (is_relevant(v))
            return;
        sat::literal lit(v);
        switch (ctx.s().value(lit)) {
        case l_undef:
            set_relevant(lit);
            break;
        case l_true:
            set_asserted(lit);
            break;
        case l_false:
            set_asserted(~lit);
            break;
        }
    }

    void relevancy::asserted(sat::literal lit) {
        TRACE("relevancy", tout << "asserted " << lit << " relevant " << is_relevant(lit) << "\n");
        if (!m_enabled)
            return;
        flush();
        if (is_relevant(lit)) {
            add_to_propagation_queue(lit);
            return;
        }
        if (ctx.s().lvl(lit) <= ctx.s().search_lvl()) {
            set_relevant(lit);
            add_to_propagation_queue(lit);
            return;
        }

        for (auto idx : occurs(lit)) {
            if (!m_roots[idx])
                continue;
            for (sat::literal lit2 : *m_clauses[idx]) 
                if (lit2 != lit && ctx.s().value(lit2) == l_true && is_relevant(lit2))
                    goto next;  
            set_relevant(lit);
            add_to_propagation_queue(lit);
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
            auto const& [lit, n] = m_queue[m_qhead++];
            SASSERT(n || lit != sat::null_literal);
            SASSERT(!n || lit == sat::null_literal);
            if (n)
                propagate_relevant(n);
            else 
                propagate_relevant(lit);            
        }
    }

    void relevancy::merge(euf::enode* root, euf::enode* other) {
        TRACE("relevancy", tout << "merge #" << ctx.bpp(root) << " " << is_relevant(root) << " #" << ctx.bpp(other) << " " << is_relevant(other) << "\n");
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
        TRACE("relevancy", tout << "mark #" << ctx.bpp(n) << "\n");
        m_trail.push_back(std::make_pair(update::add_queue, 0));
        m_queue.push_back(std::make_pair(sat::null_literal, n));
    }

    void relevancy::mark_relevant(sat::literal lit) {
        TRACE("relevancy", tout << "mark " << lit << " " << is_relevant(lit) << " " << ctx.s().value(lit) << " lim: " << m_lim.size() << "\n");
        if (!m_enabled)
            return;
        flush();
        if (is_relevant(lit))
            return;        
        set_relevant(lit);
        switch (ctx.s().value(lit)) {
        case l_true:
            break;
        case l_false:
            lit.neg();
            break;
        default:
            return;               
        }
        add_to_propagation_queue(lit);
    }

    void relevancy::propagate_relevant(sat::literal lit) {
        SASSERT(m_num_scopes == 0);
        TRACE("relevancy", tout << "propagate " << lit << " lim: " << m_lim.size() << "\n");
        SASSERT(ctx.s().value(lit) == l_true);
        SASSERT(is_relevant(lit));
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
                set_asserted(true_lit);            
            else {
                m_trail.push_back(std::make_pair(update::set_root, idx));
                m_roots[idx] = true;
            }
        next:
            TRACE("relevancy", tout << "propagate " << lit << " " << true_lit << " " << m_roots[idx] << "\n");
            ;
        }
    }

    void relevancy::propagate_relevant(euf::enode* n) {
        m_todo.push_back(n);
        while (!m_todo.empty()) {
            n = m_todo.back();
            m_todo.pop_back();
            TRACE("relevancy", tout << "propagate #" << ctx.bpp(n) << " lim: " << m_lim.size() << "\n");
            if (n->is_relevant())
                continue;
            m_stack.push_back(n);
            while (!m_stack.empty()) {
                n = m_stack.back();
                unsigned sz = m_stack.size();
                bool is_bool_op = ctx.get_si().is_bool_op(n->get_expr());
                if (!is_bool_op)
                    for (euf::enode* arg : euf::enode_args(n))
                        if (!arg->is_relevant())
                            m_stack.push_back(arg);
                if (sz != m_stack.size())
                    continue;
                if (!n->is_relevant()) {
                    ctx.get_egraph().set_relevant(n);
                    ctx.relevant_eh(n);
                    sat::bool_var v = n->bool_var();                    
                    if (v != sat::null_bool_var)
                        relevant_eh(v);
                    for (euf::enode* sib : euf::enode_class(n))
                        if (!sib->is_relevant())
                            m_todo.push_back(sib);
                }
                if (!ctx.get_manager().inc()) {
                    m_todo.reset();
                    m_stack.reset();
                    return;
                }
                m_stack.pop_back();
            }
        }
    }

    void relevancy::set_enabled(bool e) {
        m_enabled = e;
        ctx.get_egraph().set_default_relevant(!e);
    }

}
