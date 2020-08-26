/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_egraph.h

Abstract:

    E-graph layer

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

Notes:
   
    It relies on
    - data structures form the (legacy) SMT solver.
      - it still uses eager path compression.
    - delayed congruence table reconstruction from egg. 
      - it does not deduplicate parents.

--*/

#pragma once
#include "util/statistics.h"
#include "ast/euf/euf_enode.h"
#include "ast/euf/euf_etable.h"

namespace euf {

    struct add_eq_record {
        enode* r1;
        enode* n1;
        unsigned r2_num_parents;
        add_eq_record(enode* r1, enode* n1, unsigned r2_num_parents):
            r1(r1), n1(n1), r2_num_parents(r2_num_parents) {}
    };
    
    class egraph {        
        struct scope {
            bool     m_inconsistent;
            unsigned m_num_eqs;
            unsigned m_num_nodes;
        };
        struct stats {
            unsigned m_num_merge;
            unsigned m_num_lits;
            unsigned m_num_eqs;
            unsigned m_num_conflicts;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        ast_manager&           m;
        region                 m_region;
        enode_vector           m_worklist;
        etable                 m_table;
        svector<add_eq_record> m_eqs;
        svector<scope>         m_scopes;
        enode_vector           m_expr2enode;
        enode_vector           m_nodes;
        expr_ref_vector        m_exprs;
        unsigned               m_num_scopes { 0 };
        bool                   m_inconsistent { false };
        enode                  *m_n1 { nullptr };
        enode                  *m_n2 { nullptr };
        justification          m_justification;
        enode_vector           m_new_eqs;
        enode_vector           m_new_lits;
        enode_vector           m_todo;
        stats                  m_stats;
            

        void push_eq(enode* r1, enode* n1, unsigned r2_num_parents) {
            m_eqs.push_back(add_eq_record(r1, n1, r2_num_parents));
        }
        void undo_eq(enode* r1, enode* n1, unsigned r2_num_parents);
        enode* mk_enode(expr* f, unsigned num_args, enode * const* args);
        void reinsert(enode* n);
        void force_push();
        void set_conflict(enode* n1, enode* n2, justification j);
        void merge(enode* n1, enode* n2, justification j);
        void merge_justification(enode* n1, enode* n2, justification j);
        void unmerge_justification(enode* n1);
        void dedup_equalities();
        void reinsert_equality(enode* p);
        void update_children(enode* n);
        void push_lca(enode* a, enode* b);
        void push_congruence(enode* n1, enode* n2, bool commutative);
        void push_todo(enode* n);
        template <typename T>
        void explain_eq(ptr_vector<T>& justifications, enode* a, enode* b, justification const& j) {
            if (j.is_external())
                justifications.push_back(j.ext<T>());
            else if (j.is_congruence()) 
                push_congruence(a, b, j.is_commutative());
        }
        template <typename T>
        void explain_todo(ptr_vector<T>& justifications);
        
    public:
        egraph(ast_manager& m): m(m), m_table(m), m_exprs(m) {}
        enode* find(expr* f) { return m_expr2enode.get(f->get_id(), nullptr); }
        enode* mk(expr* f, unsigned n, enode *const* args);
        void push() { ++m_num_scopes; }
        void pop(unsigned num_scopes);

        bool is_equality(enode* n) const;

        /**
           \brief merge nodes, all effects are deferred to the propagation step.
         */
        void merge(enode* n1, enode* n2, void* reason) { merge(n1, n2, justification::external(reason)); }        

        /**
           \brief propagate set of merges. 
           This call may detect an inconsistency. Then inconsistent() is true.
           Use then explain() to extract an explanation for the conflict.

           It may also infer new implied equalities, when the roots of the 
           equated nodes are merged. Use then new_eqs() to extract the vector
           of new equalities.
        */
        void propagate();
        bool inconsistent() const { return m_inconsistent; }
        enode_vector const& new_eqs() const { return m_new_eqs; }
        enode_vector const& new_lits() const { return m_new_lits; }
        template <typename T>
        void explain(ptr_vector<T>& justifications);
        template <typename T>
        void explain_eq(ptr_vector<T>& justifications, enode* a, enode* b, bool comm);
        enode_vector const& nodes() const { return m_nodes; }
        void invariant();
        void copy_from(egraph const& src, std::function<void*(void*)>& copy_justification);
        std::ostream& display(std::ostream& out) const;        
        void collect_statistics(statistics& st) const;
    };

    inline std::ostream& operator<<(std::ostream& out, egraph const& g) { return g.display(out); }
}
