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
#include "ast/quantifier_stat.h"
#include "ast/pattern/pattern_inference.h"
#include "ast/normal_forms/nnf.h"
#include "solver/solver.h"
#include "sat/smt/sat_th.h"
#include "ast/euf/euf_mam.h"
#include "sat/smt/q_clause.h"
#include "sat/smt/q_queue.h"
#include "sat/smt/q_eval.h"

namespace euf {
    class solver;
}

namespace q {

    class solver;

    class ematch : public euf::on_binding_callback {
        struct stats {
            unsigned m_num_instantiations;
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            unsigned m_num_redundant;
            unsigned m_num_delayed_bindings;
            
            stats() { reset(); }

            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };

        struct prop {
            bool is_conflict;
            unsigned idx;
            sat::ext_justification_idx j;
            prop(bool is_conflict, unsigned idx, sat::ext_justification_idx j) : is_conflict(is_conflict), idx(idx), j(j) {}
        };

        struct remove_binding;
        struct insert_binding;
        struct pop_clause;
        struct scoped_mark_reset;
        struct reset_in_queue;

        
        euf::solver&                  ctx;
        solver&                       m_qs;
        ast_manager&                  m;
        eval                          m_eval;
        quantifier_stat_gen           m_qstat_gen;
        bindings                      m_bindings;
        scoped_ptr<binding>           m_tmp_binding;
        unsigned                      m_tmp_binding_capacity = 0;
        queue                         m_inst_queue;
        svector<prop>                 m_prop_queue;
        pattern_inference_rw          m_infer_patterns;
        scoped_ptr<euf::mam>          m_mam, m_lazy_mam;
        ptr_vector<clause>            m_clauses;
        obj_map<quantifier, unsigned> m_q2clauses;
        vector<unsigned_vector>       m_watch;     // expr_id -> clause-index*
        stats                         m_stats;
        expr_fast_mark1               m_mark;
        unsigned                      m_generation_propagation_threshold = 3;
        ptr_vector<app>               m_ground;
        bool                          m_in_queue_set = false;
        nat_set                       m_node_in_queue;
        nat_set                       m_clause_in_queue;
        unsigned                      m_qhead = 0;
        unsigned_vector               m_clause_queue;
        euf::enode_pair_vector        m_evidence;
        bool                          m_enable_propagate = true;
        symbol                        m_ematch = symbol("ematch");

        euf::enode* const* copy_nodes(clause& c, euf::enode* const* _binding);
        binding* tmp_binding(clause& c, app* pat, euf::enode* const* _binding);
        binding* alloc_binding(clause& c, app* pat, euf::enode* const* _binding, unsigned max_generation, unsigned min_top, unsigned max_top);
       
        ptr_vector<size_t> m_explain;
        euf::cc_justification m_explain_cc;
        sat::ext_justification_idx mk_justification(unsigned idx, unsigned generation, clause& c, euf::enode* const* b);

        void ensure_ground_enodes(expr* e);
        void ensure_ground_enodes(clause const& c);

        void instantiate(binding& b);
        sat::literal instantiate(clause& c, unsigned generation, euf::enode* const* binding, lit const& l);

        // register as callback into egraph.
        void on_merge(euf::enode* root, euf::enode* other);          
        void insert_to_propagate(unsigned node_id);
        void insert_clause_in_queue(unsigned idx);

        void add_watch(euf::enode* root, unsigned clause_idx);
        void init_watch(expr* e, unsigned clause_idx);
        void init_watch(clause& c);

        void attach_ground_pattern_terms(expr* pat);
        clause* clausify(quantifier* q);
        lit clausify_literal(expr* arg);

        bool flush_prop_queue();
        void propagate(bool is_conflict, unsigned idx, sat::ext_justification_idx j_idx);

        bool propagate(bool flush);
        void propagate(clause& c, bool flush, bool& propagated);

        expr_ref_vector m_new_defs;
        proof_ref_vector m_new_proofs;
        defined_names    m_dn;
        nnf              m_nnf;
        
        quantifier_ref nnf_skolem(quantifier* q);

    public:
        
        ematch(euf::solver& ctx, solver& s);
            
        bool operator()();

        bool unit_propagate();        

        void add(quantifier* q);

        void relevant_eh(euf::enode* n);

        void collect_statistics(statistics& st) const;

        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing);

        // callback from mam
        void on_binding(quantifier* q, app* pat, euf::enode* const* binding, unsigned max_generation, unsigned min_gen, unsigned max_gen) override;

        // callbacks from queue
        lbool evaluate(euf::enode* const* binding, clause& c) { m_evidence.reset();  return m_eval(binding, c, m_evidence); }

        void add_instantiation(clause& c, binding& b, sat::literal lit);

        bool propagate(bool is_owned, euf::enode* const* binding, unsigned max_generation, clause& c, bool& new_propagation);

        std::ostream& display(std::ostream& out) const;

        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const;

    };

}
