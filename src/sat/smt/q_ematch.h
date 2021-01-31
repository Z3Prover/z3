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
#include "util/dlist.h"
#include "ast/quantifier_stat.h"
#include "ast/pattern/pattern_inference.h"
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
            std::ostream& display(std::ostream& out) const;
        };

        struct remove_binding;
        struct insert_binding;

        struct binding : public dll_base<binding> {
            unsigned           m_max_generation;
            unsigned           m_min_top_generation;
            unsigned           m_max_top_generation;
            euf::enode*        m_nodes[0];

            binding(unsigned max_generation, unsigned min_top, unsigned max_top):
                m_max_generation(max_generation),
                m_min_top_generation(min_top),
                m_max_top_generation(max_top) {}

            euf::enode* const* nodes() { return m_nodes; }

        };

        binding* alloc_binding(unsigned n, unsigned max_generation, unsigned min_top, unsigned max_top);
        
        struct clause {
            vector<lit>         m_lits;
            quantifier_ref      m_q;
            sat::literal        m_literal;
            q::quantifier_stat* m_stat { nullptr };
            binding*            m_bindings { nullptr };

            clause(ast_manager& m): m_q(m) {}

            void add_binding(ematch& em, euf::enode* const* b, unsigned max_generation, unsigned min_top, unsigned max_top);
            std::ostream& display(euf::solver& ctx, std::ostream& out) const;
            lit const& operator[](unsigned i) const { return m_lits[i]; }
            lit& operator[](unsigned i) { return m_lits[i]; }
            unsigned size() const { return m_lits.size(); }
            unsigned num_decls() const { return m_q->get_num_decls(); }
        };

        struct fingerprint {
            clause&  c;
            binding& b;
            unsigned max_generation;
            fingerprint(clause& c, binding& b, unsigned max_generation):
                c(c), b(b), max_generation(max_generation) {}
            unsigned hash() const;
            bool eq(fingerprint const& other) const;
        };

        struct fingerprint_hash_proc {
            bool operator()(fingerprint const* f) const { return f->hash(); }
        };
        struct fingerprint_eq_proc {
            bool operator()(fingerprint const* a, fingerprint const* b) const { return a->eq(*b); }
        };
        typedef ptr_hashtable<fingerprint, fingerprint_hash_proc, fingerprint_eq_proc> fingerprints;    

        struct justification {
            expr*     m_lhs, *m_rhs;
            bool      m_sign;
            clause&   m_clause;
            euf::enode* const* m_binding;
        justification(lit const& l, clause& c, euf::enode* const* b):
        m_lhs(l.lhs), m_rhs(l.rhs), m_sign(l.sign), m_clause(c), m_binding(b) {}
            sat::ext_constraint_idx to_index() const { 
                return sat::constraint_base::mem2base(this); 
            }
            static justification& from_index(size_t idx) {
                return *reinterpret_cast<justification*>(sat::constraint_base::from_index(idx)->mem());
            }
            static size_t get_obj_size() { return sat::constraint_base::obj_size(sizeof(justification)); }
        };
        sat::ext_justification_idx mk_justification(unsigned idx, clause& c, euf::enode* const* b);

        struct pop_clause;
        
        euf::solver&                           ctx;
        solver&                                m_qs;
        ast_manager&                           m;
        q::quantifier_stat_gen                 m_qstat_gen;
        fingerprints                           m_fingerprints;
        pattern_inference_rw                   m_infer_patterns;
        scoped_ptr<q::mam>                     m_mam, m_lazy_mam;
        ptr_vector<clause>                     m_clauses;
        obj_map<quantifier, unsigned>          m_q2clauses;
        vector<unsigned_vector>                m_watch;     // expr_id -> clause-index*
        stats                                  m_stats;
        expr_fast_mark1                        m_mark;

        struct scoped_mark_reset;

        nat_set         m_node_in_queue;
        nat_set         m_clause_in_queue;
        unsigned        m_qhead { 0 };
        unsigned_vector m_queue;

        ptr_vector<app> m_ground;
        void ensure_ground_enodes(expr* e);
        void ensure_ground_enodes(clause const& c);

        // compare s, t modulo sign under binding
        lbool compare(unsigned n, euf::enode* const* binding, expr* s, expr* t);
        lbool compare_rec(unsigned n, euf::enode* const* binding, expr* s, expr* t);
        euf::enode_vector m_eval, m_indirect_nodes;
        euf::enode* eval(unsigned n, euf::enode* const* binding, expr* e);

        bool propagate(euf::enode* const* binding, clause& c);
        void instantiate(binding& b, clause& c);
        sat::literal instantiate(clause& c, euf::enode* const* binding, lit const& l);

        // register as callback into egraph.
        void on_merge(euf::enode* root, euf::enode* other);          
        void insert_to_propagate(unsigned node_id);

        void add_watch(euf::enode* root, unsigned clause_idx);
        void init_watch(expr* e, unsigned clause_idx);
        void init_watch(clause& c, unsigned idx);

        // extract explanation
        ptr_vector<size_t> m_explain;
        void explain(clause& c, unsigned literal_idx, euf::enode* const* binding);
        void explain_eq(unsigned n, euf::enode* const* binding, expr* s, expr* t);
        void explain_diseq(unsigned n, euf::enode* const* binding, expr* s, expr* t);

        void attach_ground_pattern_terms(expr* pat);
        clause* clausify(quantifier* q);

        fingerprint* add_fingerprint(clause& c, binding& b, unsigned max_generation);


    public:
        
        ematch(euf::solver& ctx, solver& s);
            
        bool operator()();

        bool propagate();

        void init_search();

        void add(quantifier* q);

        void collect_statistics(statistics& st) const;

        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing);

        // callback from mam
        void on_binding(quantifier* q, app* pat, euf::enode* const* binding, unsigned max_generation, unsigned min_gen, unsigned max_gen);

        std::ostream& display(std::ostream& out) const;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const;

    };

}
