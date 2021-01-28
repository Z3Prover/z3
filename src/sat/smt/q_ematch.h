/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_ematch.h

Abstract:

    E-matching quantifier instantiation plugin

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/
#pragma once

#include "util/nat_set.h"
#include "solver/solver.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/q_mam.h"

namespace euf {
    class solver;
}

namespace q {

    class solver;

    class ematch {
        struct stats {
            unsigned m_num_instantiations;
            
            stats() { reset(); }

            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };


        struct lit {
            expr_ref lhs;
            expr_ref rhs;
            bool     sign;
            lit(expr_ref const& lhs, expr_ref const& rhs, bool sign):
                lhs(lhs), rhs(rhs), sign(sign) {}
            
        };

        struct binding {
            bool               m_propagated { false };
            euf::enode*        m_nodes[0];

            binding() {}

            bool propagated() const { return m_propagated; }
            void set_propagated(bool b) { m_propagated = b; }
            euf::enode* const* nodes() { return m_nodes; }
        };

        binding* alloc_binding(unsigned n);
        
        struct clause {
            vector<lit>         m_lits;
            quantifier*         m_q;
            ptr_vector<binding> m_bindings;

            ptr_vector<binding> const& bindings() { return m_bindings; }
        };

        struct pop_clause;
        
        euf::solver&                           ctx;
        solver&                                m_qs;
        ast_manager&                           m;
        scoped_ptr<q::mam>                     m_mam, m_lazy_mam;
        ptr_vector<clause>                     m_clauses;
        obj_map<quantifier, unsigned>          m_q2clauses;
        vector<unsigned_vector>                m_watch;     // expr_id -> clause-index*
        stats                                  m_stats;
        expr_fast_mark1                        m_mark;

        nat_set         m_node_in_queue;
        nat_set         m_clause_in_queue;
        unsigned        m_qhead { 0 };
        unsigned_vector m_queue;

        ptr_vector<app> m_ground;
        void ensure_ground_enodes(expr* e);
        void ensure_ground_enodes(clause const& c);

        // compare s, t modulo sign under binding
        lbool compare(euf::enode* const* binding, expr* s, expr* t);
        lbool compare_rec(euf::enode* const* binding, expr* s, expr* t);
        euf::enode_vector m_eval, m_indirect_nodes;
        euf::enode* eval(euf::enode* const* binding, expr* e);

        bool propagate(euf::enode* const* binding, clause& c);
        void instantiate(euf::enode* const* binding, clause& c);

        // register as callback into egraph.
        void on_merge(euf::enode* root, euf::enode* other);          
        void insert_to_propagate(unsigned node_id);

        void add_watch(euf::enode* root, unsigned clause_idx);
        void init_watch(expr* e, unsigned clause_idx);
        void init_watch(clause& c, unsigned idx);

        // extract explanation
        void get_antecedents(euf::enode* const* binding, unsigned clause_idx, bool probing);

        void attach_ground_pattern_terms(expr* pat);
        clause* clausify(quantifier* q);


    public:
        
        ematch(euf::solver& ctx, solver& s);
            
        bool operator()();

        bool propagate();

        void init_search();

        void add(quantifier* q);

        void collect_statistics(statistics& st) const;

        // callback from mam
        void on_binding(quantifier* q, app* pat, euf::enode* const* binding);

    };

}
