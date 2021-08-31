/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    qi_queue.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-15.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/quantifier_stat.h"
#include "ast/rewriter/cached_var_subst.h"
#include "parsers/util/cost_parser.h"
#include "smt/smt_checker.h"
#include "smt/smt_quantifier.h"
#include "smt/fingerprints.h"
#include "smt/params/qi_params.h"
#include "ast/cost_evaluator.h"
#include "util/statistics.h"

namespace smt {
    class context;

    struct qi_queue_stats {
        unsigned m_num_instances, m_num_lazy_instances;
        void reset() { memset(this, 0, sizeof(qi_queue_stats)); }
        qi_queue_stats() { reset(); }
    };

    class qi_queue {
        quantifier_manager &          m_qm;
        context &                     m_context;
        ast_manager &                 m;
        qi_params &                   m_params;
        qi_queue_stats                m_stats;
        checker                       m_checker;
        expr_ref                      m_cost_function;
        expr_ref                      m_new_gen_function;
        cost_parser                   m_parser;
        cost_evaluator                m_evaluator;
        cached_var_subst              m_subst;
        svector<float>                m_vals;
        double                        m_eager_cost_threshold;
        struct entry {
            fingerprint * m_qb;
            float         m_cost;
            unsigned      m_generation:31;
            unsigned      m_instantiated:1;
            entry(fingerprint * f, float c, unsigned g):m_qb(f), m_cost(c), m_generation(g), m_instantiated(false) {}
        };
        svector<entry>                m_new_entries;
        svector<entry>                m_delayed_entries;
        expr_ref_vector               m_instances;
        unsigned_vector               m_instantiated_trail;
        struct scope {
            unsigned   m_delayed_entries_lim;
            unsigned   m_instances_lim;
            unsigned   m_instantiated_trail_lim;
        };
        svector<scope>                m_scopes;

        void init_parser_vars();
        q::quantifier_stat * set_values(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation, float cost);
        float get_cost(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation);
        unsigned get_new_gen(quantifier * q, unsigned generation, float cost);
        void instantiate(entry & ent);
        void get_min_max_costs(float & min, float & max) const;
        void display_instance_profile(fingerprint * f, quantifier * q, unsigned num_bindings, enode * const * bindings, unsigned proof_id, unsigned generation);

    public:
        qi_queue(quantifier_manager & qm, context & ctx, qi_params & params);
        ~qi_queue();
        void setup();
        /**
           \brief Insert a new quantifier in the queue, f contains the quantifier and bindings.
           f->get_data() is the quantifier.
        */
        void insert(fingerprint * f, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation);
        void instantiate();
        bool has_work() const { return !m_new_entries.empty(); }
        void init_search_eh();
        bool final_check_eh();
        void push_scope();
        void pop_scope(unsigned num_scopes);
        void reset();
        void display_delayed_instances_stats(std::ostream & out) const;
        void collect_statistics(::statistics & st) const;
    };
};


