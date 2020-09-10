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
#include "util/trail.h"
#include "ast/euf/euf_enode.h"
#include "ast/euf/euf_etable.h"

namespace euf {

    /***
      \brief store derived theory equalities.
      Theory 'id' is notified with the equality of theory variables v1, v2
      that are merged into the common root of child and root (their roots may
      have been updated since the equality was derived, but the explanation for
      v1 == v2 is provided by explaining the equality child == root.
    */
    struct th_eq {
        theory_id  m_id;
        theory_var m_v1;
        theory_var m_v2;
        enode* m_child;
        enode* m_root;
        th_eq(theory_id id, theory_var v1, theory_var v2, enode* c, enode* r) :
            m_id(id), m_v1(v1), m_v2(v2), m_child(c), m_root(r) {}
    };
    
    class egraph {        
        typedef ptr_vector<trail<egraph> > trail_stack;
        struct stats {
            unsigned m_num_merge;
            unsigned m_num_th_eqs;
            unsigned m_num_lits;
            unsigned m_num_eqs;
            unsigned m_num_conflicts;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct update_record {
            struct toggle_merge {};
            struct add_th_var {};
            struct replace_th_var {};
            struct new_lit {};
            struct new_th_eq {};
            struct new_th_eq_qhead {};
            struct new_lits_qhead {};
            struct inconsistent {};
            enum class tag_t { is_set_parent, is_add_node, is_toggle_merge, 
                         is_add_th_var, is_replace_th_var, is_new_lit, is_new_th_eq,
                         is_new_th_eq_qhead, is_new_lits_qhead, is_inconsistent };
            tag_t  tag;
            enode* r1;
            enode* n1;
            union {
                unsigned r2_num_parents;
                struct {
                    unsigned   m_th_id : 8;
                    unsigned   m_old_th_var : 24;
                };
                unsigned qhead;
                bool     m_inconsistent;
            };
            update_record(enode* r1, enode* n1, unsigned r2_num_parents) :
                tag(tag_t::is_set_parent), r1(r1), n1(n1), r2_num_parents(r2_num_parents) {}
            update_record(enode* n) :
                tag(tag_t::is_add_node), r1(n), n1(nullptr), r2_num_parents(UINT_MAX) {}
            update_record(enode* n, toggle_merge) :
                tag(tag_t::is_toggle_merge), r1(n), n1(nullptr), r2_num_parents(UINT_MAX) {}
            update_record(enode* n, unsigned id, add_th_var) :
                tag(tag_t::is_add_th_var), r1(n), n1(nullptr), r2_num_parents(id) {}
            update_record(enode* n, theory_id id, theory_var v, replace_th_var) :
                tag(tag_t::is_replace_th_var), r1(n), n1(nullptr), m_th_id(id), m_old_th_var(v) {}
            update_record(new_lit) :
                tag(tag_t::is_new_lit), r1(nullptr), n1(nullptr), r2_num_parents(0) {}
            update_record(new_th_eq) :
                tag(tag_t::is_new_th_eq), r1(nullptr), n1(nullptr), r2_num_parents(0) {}
            update_record(unsigned qh, new_th_eq_qhead):
                tag(tag_t::is_new_th_eq_qhead), r1(nullptr), n1(nullptr), qhead(qh) {}
            update_record(unsigned qh, new_lits_qhead):
                tag(tag_t::is_new_lits_qhead), r1(nullptr), n1(nullptr), qhead(qh) {}
            update_record(bool inc, inconsistent) :
                tag(tag_t::is_inconsistent), m_inconsistent(inc) {}
        };
        ast_manager&           m;
        enode_vector           m_worklist;
        etable                 m_table;
        region                 m_region;
        svector<update_record> m_updates;
        unsigned_vector        m_scopes;
        enode_vector           m_expr2enode;
        enode_vector           m_nodes;
        expr_ref_vector        m_exprs;
        unsigned               m_num_scopes { 0 };
        bool                   m_inconsistent { false };
        enode                  *m_n1 { nullptr };
        enode                  *m_n2 { nullptr };
        justification          m_justification;
        unsigned               m_new_lits_qhead { 0 };
        unsigned               m_new_th_eqs_qhead { 0 };
        svector<enode_bool_pair>  m_new_lits;
        svector<th_eq>         m_new_th_eqs;
        enode_vector           m_todo;
        stats                  m_stats;
        std::function<void(expr*,expr*,expr*)> m_used_eq;
        std::function<void(app*,app*)>        m_used_cc;  

        void push_eq(enode* r1, enode* n1, unsigned r2_num_parents) {
            m_updates.push_back(update_record(r1, n1, r2_num_parents));
        }
        void push_node(enode* n) { m_updates.push_back(update_record(n)); }

        void add_th_eq(theory_id id, theory_var v1, theory_var v2, enode* c, enode* r);
        void add_literal(enode* n, bool is_eq);
        void undo_eq(enode* r1, enode* n1, unsigned r2_num_parents);
        void undo_add_th_var(enode* n, theory_id id);
        enode* mk_enode(expr* f, unsigned num_args, enode * const* args);
        void reinsert(enode* n);
        void force_push();
        void set_conflict(enode* n1, enode* n2, justification j);
        void merge(enode* n1, enode* n2, justification j);
        void merge_th_eq(enode* n, enode* root);
        void merge_justification(enode* n1, enode* n2, justification j);
        void unmerge_justification(enode* n1);
        void reinsert_equality(enode* p);
        void update_children(enode* n);
        void push_lca(enode* a, enode* b);
        enode* find_lca(enode* a, enode* b);
        void push_to_lca(enode* a, enode* lca);
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

        std::ostream& display(std::ostream& out, unsigned max_args, enode* n) const;
        
    public:
        egraph(ast_manager& m): m(m), m_table(m), m_exprs(m) {}
        ~egraph();
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
        bool propagate();
        bool inconsistent() const { return m_inconsistent; }

        /**
           \brief Maintain and update cursor into propagated consequences.
           The result of get_literal() is a pair (n, is_eq)
           where \c n is an enode and \c is_eq indicates whether the enode
           is an equality consequence. 
         */
        bool       has_literal() const { return m_new_lits_qhead < m_new_lits.size(); }
        bool       has_th_eq() const { return m_new_th_eqs_qhead < m_new_th_eqs.size(); }
        enode_bool_pair get_literal() const { return m_new_lits[m_new_lits_qhead]; }
        th_eq      get_th_eq() const { return m_new_th_eqs[m_new_th_eqs_qhead]; }
        void       next_literal() { SASSERT(m_new_lits_qhead < m_new_lits.size()); m_new_lits_qhead++; }
        void       next_th_eq() { SASSERT(m_new_th_eqs_qhead < m_new_th_eqs.size()); m_new_th_eqs_qhead++; }


        void add_th_var(enode* n, theory_var v, theory_id id);
        void set_merge_enabled(enode* n, bool enable_merge);

        void set_used_eq(std::function<void(expr*,expr*,expr*)>& used_eq) { m_used_eq = used_eq; }
        void set_used_cc(std::function<void(app*,app*)>& used_cc) { m_used_cc = used_cc; }

        void begin_explain();
        void end_explain();
        template <typename T>
        void explain(ptr_vector<T>& justifications);
        template <typename T>
        void explain_eq(ptr_vector<T>& justifications, enode* a, enode* b);
        enode_vector const& nodes() const { return m_nodes; }
        void invariant();
        void copy_from(egraph const& src, std::function<void*(void*)>& copy_justification);
        struct e_pp {
            egraph const& g;
            enode*  n;
            e_pp(egraph const& g, enode* n) : g(g), n(n) {}
            std::ostream& display(std::ostream& out) const { return g.display(out, 0, n); }
        };
        e_pp pp(enode* n) const { return e_pp(*this, n); }
        std::ostream& display(std::ostream& out) const; 
        void collect_statistics(statistics& st) const;
    };

    inline std::ostream& operator<<(std::ostream& out, egraph const& g) { return g.display(out); }
    inline std::ostream& operator<<(std::ostream& out, egraph::e_pp const& p) { return p.display(out); }
}
