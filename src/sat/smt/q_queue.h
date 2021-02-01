/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_queue.h

Abstract:

    Instantiation queue for quantifiers

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/
#pragma once

#include "ast/quantifier_stat.h"
#include "ast/cost_evaluator.h"
#include "ast/rewriter/cached_var_subst.h"
#include "parsers/util/cost_parser.h"
#include "sat/smt/q_fingerprint.h"



namespace euf {
    class solver;
};

namespace q {

    class ematch;

    class queue {

        struct stats {
            unsigned m_num_instances, m_num_lazy_instances;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        ematch&                       em;
        euf::solver&                  ctx;
        ast_manager &                 m;
        qi_params const &             m_params;
        stats                         m_stats;
        expr_ref                      m_cost_function;
        expr_ref                      m_new_gen_function;
        cost_parser                   m_parser;
        cost_evaluator                m_evaluator;
        cached_var_subst              m_subst;
        svector<float>                m_vals;
        double                        m_eager_cost_threshold { 0 };
        struct entry {
            fingerprint * m_qb;
            float         m_cost;
            bool          m_instantiated{ false };
            entry(fingerprint * f, float c):m_qb(f), m_cost(c) {}
        };
        struct reset_new_entries;
        struct reset_instantiated;

        svector<entry>                m_new_entries;
        svector<entry>                m_delayed_entries;

        float get_cost(fingerprint& f);
        void set_values(fingerprint& f, float cost);
        void init_parser_vars();
        void setup();
        unsigned get_new_gen(fingerprint& f, float cost);
        void instantiate(entry& e);

    public:

        queue(ematch& em, euf::solver& ctx);
            
        void insert(fingerprint* f);

        bool propagate();

        bool lazy_propagate();

        void collect_statistics(::statistics & st) const;

    };
}
