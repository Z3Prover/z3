/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_clause.cpp

Abstract:

    Superposition Calculus Clause

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#include"spc_clause.h"
#include"splay_tree_def.h"

template class splay_tree<spc::clause *, spc::clause::compare>;

namespace spc {

    clause::clause(ast_manager & m, unsigned num_lits, literal * lits, justification * p, unsigned scope_lvl):
        m_id(UINT_MAX),
        m_time(UINT_MAX),
        m_scope_lvl(scope_lvl),
        m_bidx(UINT_MAX),
        m_processed(false),
        m_indexed(false), 
        m_has_sel_lit(false), 
        m_justification(p) {
        
        set_fields(num_lits, lits);

        m_num_lits_capacity = m_num_lits[0] + m_num_lits[1];
        
        memcpy(m_lits, lits, sizeof(literal) * get_num_literals());

        for (unsigned i = 0; i < num_lits; i++)
            m.inc_ref(m_lits[i].atom());
        m_justification->inc_ref();
        m_justification->set_owner(this);
        
        sort_literals();
    }

    clause * clause::mk(ast_manager & m, unsigned num_lits, literal * lits, justification * p, unsigned scope_lvl) {
        void * mem   = m.get_allocator().allocate(sizeof(clause) + num_lits * sizeof(literal));
        return new (mem) clause(m, num_lits, lits, p, scope_lvl);
    }

    void clause::init(unsigned id, unsigned time) {
        SASSERT(m_id == UINT_MAX);
        SASSERT(m_time == UINT_MAX);

        m_id          = id;
        m_time        = time;
        m_proof_depth = 0;

        justification_stat j_stat;
        get_justification_stat(m_justification, j_stat);

        m_proof_depth = j_stat.m_proof_depth;
        
        if (j_stat.m_max_scope_lvl > m_scope_lvl) 
            m_scope_lvl = j_stat.m_max_scope_lvl;
        
        update_parents(j_stat.m_parent_clauses);
    }

    void clause::update_parents(ptr_buffer<clause> & parents) {
        ptr_buffer<clause>::iterator it  = parents.begin();
        ptr_buffer<clause>::iterator end = parents.end();
        for (; it != end; ++it) {
            clause * parent = *it;
            parent->add_child(this);
        }
    }

    void clause::deallocate(ast_manager & m) {

        justification_stat j_stat;
        get_justification_stat(get_justification(), j_stat);

        ptr_buffer<clause>::iterator it  = j_stat.m_parent_clauses.begin();
        ptr_buffer<clause>::iterator end = j_stat.m_parent_clauses.end();
        for (; it != end; ++it) {
            clause * parent = *it;
            parent->del_child(this);
        }

        dec_ref(get_justification(), m);
        
        unsigned num_lits = get_num_literals();
        for (unsigned i = 0; i < num_lits; i++)
            m.dec_ref(get_literal(i).atom());

        unsigned capacity = get_num_literals_capacity();
        this->~clause();
        m.get_allocator().deallocate(sizeof(clause) +  capacity * sizeof(literal), this);
    }

    void clause::select_literal(unsigned idx) {
        SASSERT(idx < get_num_literals());
        m_lits[idx].set_selected(true);
        m_has_sel_lit = true;
    }

    /**
       \brief Return true if l is maximal in the clause, given a substitution s.
       
       s(l) is considered maximal if there is no literal l' in the clause such s(l') is greater
       than s(l).
    */
    bool clause::is_maximal(order & o, literal const & l, unsigned offset, substitution * s) const {
        unsigned num_lits = get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l_prime = m_lits[i];
            if (l != l_prime && greater(o, l_prime, l, offset, s))
                return false;
        }
        return true;
    }

    /**
       \brief Return true if l is a maximal selected literal in the clause, given a substitution s.
       
       s(l) is considered maximal selected literal if there is no
       selected literal l' in the clause such s(l') is greater than s(l).
    */
    bool clause::is_sel_maximal(order & o, literal const & l, unsigned offset, substitution * s) const {
        if (!l.is_selected())
            return false;
        unsigned num_lits = get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l_prime = m_lits[i];
            if (l != l_prime && l_prime.is_selected() && greater(o, l_prime, l, offset, s))
                return false;
        }
        return true;
    }

    /**
       \brief Return true if l is eligible for resolution.
    */
    bool clause::is_eligible_for_resolution(order & o, literal const & l, unsigned offset, substitution * s) const {
        if (has_sel_lit()) 
            return is_sel_maximal(o, l, offset, s);
        else
            return is_maximal(o, l, offset, s);
    }

    /**
       \brief Return true if l is eligible for paramodulation.
    */
    bool clause::is_eligible_for_paramodulation(order & o, literal const & l, unsigned offset, substitution * s) const {
        return !has_sel_lit() && is_maximal(o, l, offset, s);
    }

    /**
       \brief Try to orient literals.
    */
    void clause::try_to_orient_literals(order & o) {
        o.reserve_vars(get_num_vars());
        unsigned num_lits = get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal & l = m_lits[i];
            l.try_to_orient(o);
        }
    }

    void clause::set_fields(unsigned num_lits, literal * lits) {
        clause_stat c_stat;
        get_clause_stat(num_lits, lits, c_stat);

        m_num_vars          = c_stat.m_max_var_idx + 1;
        m_sym_count         = c_stat.m_sym_count;
        m_const_count       = c_stat.m_const_count;
        m_depth             = c_stat.m_depth;
        m_num_lits[0]       = c_stat.m_num_lits[0];
        m_num_lits[1]       = c_stat.m_num_lits[1];
        m_ground            = c_stat.m_ground;
    }

    struct lit_lt {
        bool operator()(literal const & l1, literal const & l2) const {
            if (l1.is_ground() > l2.is_ground())
                return true;
            if (l1.is_ground() != l2.is_ground())
                return false;
            if (l1.get_approx_depth() > l2.get_approx_depth())
                return true;
            if (l1.get_approx_depth() != l2.get_approx_depth())
                return false;
            if (l1.get_approx_sym_count() > l2.get_approx_sym_count())
                return true;
            if (l1.get_approx_sym_count() != l2.get_approx_sym_count())
                return false;
            if (l1.get_approx_const_count() > l2.get_approx_const_count())
                return true;
            if (l1.get_approx_const_count() != l2.get_approx_const_count())
                return false;
            return l1.get_id() < l2.get_id();
        }
    };

    /**
       \brief Sort literals to improve the performance of subsumption tests.
    */
    void clause::sort_literals() {
        DEBUG_CODE({
            unsigned num_lits = get_num_literals();
            for (unsigned i = 0; i < num_lits; i++) {
                SASSERT(m_lits[i].has_stats());
            }
        });
        std::sort(m_lits, m_lits + get_num_literals(), lit_lt());
    }

    /**
       \brief Replace clause literal with the given literals.
       Use the given justification to justify the new clause.
    */
    void clause::update_lits(ast_manager & m, unsigned num_lits, literal * lits, justification * j) {
        unsigned old_num_lits = get_num_literals();
        SASSERT(num_lits <= old_num_lits);
     
        for (unsigned i = 0; i < num_lits; i++)
            m.inc_ref(lits[i].atom());

        for (unsigned i = 0; i < old_num_lits; i++)
            m.dec_ref(m_lits[i].atom());
        
        for (unsigned i = 0; i < num_lits; i++) 
            m_lits[i] = lits[i];
        
        set_fields(num_lits, m_lits);

        SASSERT(get_num_literals() == num_lits);

        j->inc_ref();
        m_justification->set_owner(0); // release ownership
        dec_ref(m_justification, m);
        m_justification = j;
        m_justification->set_owner(this);

        sort_literals();

        justification_stat j_stat;
        get_justification_stat(m_justification, j_stat);

        m_proof_depth = j_stat.m_proof_depth;
        
        SASSERT(m_scope_lvl == j_stat.m_max_scope_lvl);
        
        update_parents(j_stat.m_parent_clauses);
    }

    void clause::display(std::ostream & out, ast_manager & m, bool detailed) {
        if (get_num_literals() == 0) {
            out << "empty-clause";
            return;
        }
        out << "#" << m_id << ": (clause ";
        spc::display(out, get_num_literals(), m_lits, m, detailed);
        out << ")";
        if (m_processed)
            out << "*";
    }

    void get_clause_stat(unsigned num_lits, literal * lits, clause_stat & stat) {
        for (unsigned i = 0; i < num_lits; i++) {
            literal_stat c;
            lits[i].get_stat(c);
            stat.m_sym_count   += c.m_sym_count;
            stat.m_depth        = std::max(stat.m_depth, c.m_depth);
            stat.m_max_var_idx  = std::max(stat.m_max_var_idx, c.m_max_var_idx);
            stat.m_const_count += c.m_const_count;
            stat.m_ground      &= c.m_ground;
            stat.m_num_lits[static_cast<unsigned>(lits[i].sign())]++;
        }
    }

};
