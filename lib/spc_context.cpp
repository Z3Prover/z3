/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_context.cpp

Abstract:

    Superposition Calculus Engine

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#include"spc_context.h"
#include"buffer.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"ast_smt2_pp.h"
#include"warning.h"

namespace spc {

    context::context(ast_manager & m, order & o, clause_selection & cs, literal_selection & ls, simplifier & s, spc_params & params):
        m_manager(m),
        m_params(params),
        m_alloc(m.get_allocator()),
        m_order(o),
        m_cls_sel(cs),
        m_lit_sel(ls),
        m_simplifier(s),
        m_time(0),
        m_scope_lvl(0),
        m_sem_taut(m),
        m_asserted_literals(m),
        m_rewriter(m, s, m_order, m_asserted_literals),
        m_der(m), 
        m_subsumption(m, m_asserted_literals, params),
        m_eq_resolution(m, m_order, m_stats),
        m_factoring(m, m_order, m_stats),
        m_superposition(m, m_order, m_stats),
        m_unsat(0) {
        m_order.reserve_offsets(3);
    }

    context::~context() {
        reset();
    }

    void context::reset() {
        m_cls_sel.reset();
        m_time      = 0;
        m_scope_lvl = 0;

        if (m_unsat)
            m_unsat = 0;
        for (unsigned i = 0; i <= m_scope_lvl; i++) {
            del_clauses(i);
            if (i < m_clauses_to_unfreeze.size())
                m_clauses_to_unfreeze[i].reset();
        }

        m_asserted_literals.reset();
        m_rewriter.reset();
        m_subsumption.reset();
        m_superposition.reset();
    }

    /**
       \brief Insert the given clause into the indexes of processed clauses.
    */
    void context::insert_index(clause * cls) {
        TRACE("insert_index", tout << "indexing clause, num_vars: " << cls->get_num_vars() << "\n"; 
              cls->display(tout, m_manager); tout << "\n";);
        m_order.reserve_vars(cls->get_num_vars());
        m_lit_sel(cls);
        m_asserted_literals.insert(cls);
        m_rewriter.insert(cls);
        m_subsumption.insert(cls);
        m_superposition.insert(cls);
        cls->set_indexed(true);
    }

    void context::erase_index(clause * cls) {
        if (cls->is_indexed()) {
            m_asserted_literals.erase(cls);
            m_rewriter.erase(cls);
            m_subsumption.erase(cls);
            m_superposition.erase(cls);
            cls->set_indexed(false);
        }
    }

    void context::set_conflict(clause * cls) {
        SASSERT(cls->get_num_literals() == 0);
        m_unsat = cls;
        if (m_params.m_spc_trace) {
            cls->display(std::cout, m_manager); std::cout << " "; 
            cls->get_justification()->display(std::cout);
            std::cout << "\n";
            std::cout.flush();
        }
    }

    void context::del_clause(clause * cls) {
        TRACE("context", tout << "deleting clause:\n"; cls->display(tout, m_manager); tout << "\n";);
        m_stats.m_num_del_clause++;

        erase_index(cls);
        if (!cls->is_processed())
            m_cls_sel.erase(cls);

        unsigned scope_lvl = cls->get_scope_lvl();
        unsigned bidx      = cls->get_bidx();
        m_clauses_to_delete[scope_lvl][bidx] = 0;

        cls->deallocate(m_manager);
    }

    void context::freeze_clause_until(clause * cls, unsigned scope_lvl) {
        if (cls->get_scope_lvl() >= scope_lvl) {
            del_clause(cls);
            return;
        }
        TRACE("context", tout << "freezing clause until: " << scope_lvl << ":\n"; cls->display(tout, m_manager); tout << "\n";);
        if (scope_lvl >= m_clauses_to_unfreeze.size())
            m_clauses_to_unfreeze.resize(scope_lvl+1, clause_vector());

        erase_index(cls);
        cls->set_processed(false);

        m_clauses_to_unfreeze[scope_lvl].push_back(cls);
    }

    void context::unfreeze_clause(clause * cls) {
        TRACE("context", tout << "unfreezing clausel: "; cls->display(tout, m_manager); tout << "\n";);
        SASSERT(!cls->is_processed());
        m_cls_sel.insert(cls);
    }

    void context::init_clause(clause * cls) {
        m_stats.m_num_mk_clause++;

        cls->init(m_cls_id_gen.mk(), m_time);
        m_time++;
        unsigned scope_lvl = cls->get_scope_lvl();

        if (scope_lvl >= m_clauses_to_delete.size())
            m_clauses_to_delete.resize(scope_lvl+1, clause_vector());
        
        clause_vector & cv = m_clauses_to_delete[scope_lvl];
        unsigned bidx = cv.size();
        cv.push_back(cls);
        cls->set_bidx(bidx);
    }

    clause * context::mk_clause(unsigned num_lits, literal * lits, justification * p, unsigned scope_lvl) {
        clause * cls = clause::mk(m_manager, num_lits, lits, p, scope_lvl);
        init_clause(cls);
        return cls;
    }

    void context::assert_expr(expr * n, proof * p, unsigned scope_lvl) {
        TRACE("spc_assert_expr", tout << mk_ismt2_pp(n, m_manager) << "\n";);
        SASSERT(scope_lvl <= m_scope_lvl);
        justification_ref ref(m_manager);
        ref = justification_proof_wrapper::mk(p, m_manager);
        assert_expr(n, ref, scope_lvl);
    }

    void invalid_clause(expr * n) {
        warning_msg("ignoring formula containing an universally quantified boolean variable.");
    }

    void context::assert_expr(expr * n, justification * p, unsigned scope_lvl) {
        SASSERT(scope_lvl <= m_scope_lvl);
        buffer<literal> lits;
        if (is_forall(n))
            n = to_quantifier(n)->get_expr();
        if (m_manager.is_or(n)) {
            unsigned num = to_app(n)->get_num_args();
            for (unsigned i = 0; i < num; i++) {
                expr * c    = to_app(n)->get_arg(i);
                bool is_neg = m_manager.is_not(c);
                if (is_var(c) || (is_neg && is_var(to_app(c)->get_arg(0)))) {
                    invalid_clause(n);
                    return;
                }
                if (is_neg)
                    lits.push_back(literal(to_app(c)->get_arg(0), true));
                else 
                    lits.push_back(literal(c, false));
            }
        }
        else if (m_manager.is_false(n)) {
            // skip
        }
        else if (m_manager.is_not(n)) {
            if (is_var(to_app(n)->get_arg(0))) {
                invalid_clause(n);
                return;
            }
            lits.push_back(literal(to_app(n)->get_arg(0), true));
        }
        else {
            if (is_var(n)) {
                invalid_clause(n);
                return;
            }
            lits.push_back(literal(n, false));
        }
        
        if (trivial(lits.size(), lits.c_ptr()))
            return;

        clause * cls = mk_clause(lits.size(), lits.c_ptr(), p, scope_lvl);
        m_cls_sel.insert(cls);
        if (cls->get_num_literals() == 0)
            set_conflict(cls);
    }

    /**
       \brief Return true if the given clause (set of literals) is trivial.
       That is, it contains the literal s = s or complementary literals.
    */
    bool context::trivial(unsigned num_lits, literal * lits) {
        SASSERT(m_found_literals.empty());
        for (unsigned i = 0; i < num_lits; i++) {
            literal l       = lits[i];
            if (m_found_literals.contains_neg(l) || l.is_true(m_manager)) {
                m_found_literals.reset();
                m_stats.m_num_trivial++;
                return true;
            }
            m_found_literals.insert(l);
        }
        m_found_literals.reset();
        return false;
    }

    bool context::trivial(clause * cls) {
        return trivial(cls->get_num_literals(), cls->get_literals());
    }
    
    /**
       \brief Simplify the given clause using the set of processed clauses.
       Return the simplified clause.
    */
    clause * context::simplify(clause * cls) {
        clause * old_cls = cls;
        m_der(cls);
        cls = m_rewriter(old_cls);
        if (cls != old_cls) {
            // freeze old clause until simplified clause is deleted.
            freeze_clause_until(old_cls, cls->get_scope_lvl());
            init_clause(cls);
            m_stats.m_num_simplified++;
        }
        m_der(cls);
        return cls;
    }
    
    /**
       \brief Use the given clause to simplify the set of processed clauses.
       
       \remark: processed clauses that can be simplified, are moved to the
       set of unprocessed clauses.
    */
    void context::simplify_processed(clause * cls) {
        // TODO
    }

    /**
       \brief Return true if the clause is redundant. 
    */
    bool context::redundant(clause * cls) {
        int r_scope_lvl = -1;
        if (trivial(cls)) {
            TRACE("redundant", tout << "clause is trivial:\n"; cls->display(tout, m_manager); tout << "\n";);
            r_scope_lvl = 0;
        }
        else if (m_sem_taut(cls->get_num_literals(), cls->get_literals())) {
            TRACE("redundant", tout << "clause is a semantic tautology:\n"; cls->display(tout, m_manager); tout << "\n";);
            r_scope_lvl = 0;
        }
        else {
            clause * subsumer = m_subsumption.forward(cls);
            if (subsumer != 0) {
                TRACE("redundant", tout << "clause was subsumed: "; cls->display(tout, m_manager);
                      tout << "\nsubsumer:\n"; subsumer->display(tout, m_manager); tout << "\n";);
                r_scope_lvl = subsumer->get_scope_lvl();
                m_stats.m_num_subsumed++;
            }
        }

        if (r_scope_lvl >= 0) {
            m_stats.m_num_redundant++;
            TRACE("spc_saturate", tout << "clause is redundant until level: " << r_scope_lvl << " ...\n";);
            freeze_clause_until(cls, r_scope_lvl);
            return true;
        }

        return false;
    }

    /**
       \brief Process a newly generated clause.
    */
    void context::process_new_clause(clause * cls) {
        if (cls) {
            SASSERT(cls->get_justification() != 0);
            init_clause(cls);
            if (trivial(cls)) {
                del_clause(cls);
                return;
            }
            cls = simplify(cls);
            if (trivial(cls)) {
                del_clause(cls);
                return;
            }
            // if (!redundant(cls)) {
            m_cls_sel.insert(cls);
            if (cls->get_num_literals() == 0)
                set_conflict(cls);
            // }
        }
    }

    /**
       \brief Apply superposition (left&right), resolution, (equality) factoring, and equality resolution
       with the given clause and the set of processed clauses.
    */
    void context::generate(clause * cls) {
        m_new_clauses.reset();
        m_eq_resolution(cls, m_new_clauses);
        m_factoring(cls, m_new_clauses);
        m_superposition(cls, m_new_clauses);

        ptr_vector<clause>::iterator it  = m_new_clauses.begin();
        ptr_vector<clause>::iterator end = m_new_clauses.end();
        for (; it != end; ++it) {
            TRACE("spc_generate", tout << "new generated clause:\n"; (*it)->display(tout, m_manager); tout << "\n";);
            process_new_clause(*it);
        }
    }

    void context::saturate(unsigned threshold) {
        if (inconsistent())
            return;
        TRACE("spc_saturate", tout << "initial state:\n"; display(tout););
        unsigned i = 0;
        ptr_buffer<clause> to_simplify;
        while (i < threshold && !processed_all()) {
            i++;
            m_stats.m_num_processed++;
            clause * cls = m_cls_sel.get_best();
            if (m_params.m_spc_trace) {
                cls->display(std::cout, m_manager); std::cout << " "; 
                cls->get_justification()->display(std::cout);
                std::cout << "\n";
                std::cout.flush();
            }
            cls->set_processed(true);
            TRACE("spc_saturate", tout << "get best: "; cls->display(tout, m_manager); tout << "\n";);
            cls = simplify(cls);
            
            TRACE("spc_saturate", tout << "clause after simplification: "; cls->display(tout, m_manager); tout << "\n";);
            if (redundant(cls))
                continue;
            if (cls->empty()) {
                set_conflict(cls);
                break;
            }
            cls->try_to_orient_literals(m_order);
            simplify_processed(cls);
            insert_index(cls);
            generate(cls);
            if (inconsistent())
                break;
        }

        TRACE("spc_saturate", tout << "final state:\n"; display(tout););

#if 0
        IF_VERBOSE(10000, 
                   display(std::cout););
        display_statistics(std::cout);
        if (m_unsat && m_manager.fine_grain_proofs()) {
            std::cout << mk_ll_pp(m_unsat->get_justification()->get_proof(), m_manager);
        }
#endif 
    }

    void context::push_scope() {
        m_scope_lvl++;
        m_time_trail.push_back(m_time);
    }

    void context::del_clauses(unsigned scope_lvl) {
        if (scope_lvl < m_clauses_to_delete.size()) {
            clause_vector & cv = m_clauses_to_delete[m_scope_lvl];
            clause_vector::iterator it  = cv.begin();
            clause_vector::iterator end = cv.end();
            for (; it != end; ++it) {
                clause * cls = *it;
                if (cls)
                    del_clause(cls);
            }
            cv.reset();
        }
    }

    void context::unfreeze_clauses(unsigned scope_lvl) {
        if (scope_lvl < m_clauses_to_unfreeze.size()) {
            clause_vector & cv = m_clauses_to_unfreeze[m_scope_lvl];
            clause_vector::iterator it  = cv.begin();
            clause_vector::iterator end = cv.end();
            for (; it != end; ++it)
                unfreeze_clause(*it);
            cv.reset();
        }
    }

    void context::pop_scope(unsigned num_scopes) {
        SASSERT(num_scopes >= m_scope_lvl);
        unsigned new_lvl = m_scope_lvl - num_scopes;
        m_time = m_time_trail[new_lvl];
        m_time_trail.shrink(new_lvl);

        if (m_unsat && new_lvl < m_unsat->get_scope_lvl()) 
            m_unsat = 0;
        
        while (m_scope_lvl > new_lvl) {
            del_clauses(m_scope_lvl);
            unfreeze_clauses(m_scope_lvl);
            m_scope_lvl --;
        }
    }

    void context::display(std::ostream & out, vector<clause_vector> const & cvs, unsigned scope_lvl, bool frozen) const {
        if (scope_lvl < cvs.size()) {
            bool first = true;
            clause_vector const & cv = cvs[scope_lvl];
            clause_vector::const_iterator it  = cv.begin();
            clause_vector::const_iterator end = cv.end();
            for (; it != end; ++it) {
                clause * cls = *it;
                if (cls) {
                    if (first) {
                        out << "level " << scope_lvl << ":\n";
                        first = false;
                    }
                    cls->display(out, m_manager);
                    if (frozen)
                        out << " [frozen]";
                    out << "\n";
                }
            }
        }
    }
    
    void context::display(std::ostream & out) const {
        for (unsigned i = 0; i <= m_scope_lvl; i++) {
            display(out, m_clauses_to_delete, i, false);
            display(out, m_clauses_to_unfreeze, i, true);
        }
    }

    void context::display_statistics(std::ostream & out) const {
        m_stats.display(out);
    }
    

/**
   Generate new clauses

   5) Object equality resolution 1
   
   (R or X = i)  
   ==>
   sigma(R)

   sigma = { X -> j }
   where i and j are distinct objects
   sigma(X = i) is not smaller or equal than any other literal in the clause

   6) Object equality resolution 2
   
   (R or X = Y)
   ==>
   sigma(R)

   sigma = { X -> i, Y -> j }
   For every pair of distinct objects i and j
   sigma(X = Y) is not smaller or equal than any other literal in the clause
   
*/

};
