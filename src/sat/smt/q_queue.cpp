/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_queue.cpp

Abstract:

    Instantiation queue for quantifiers

    Based on smt/qi_queue

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24    

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/q_queue.h"
#include "sat/smt/q_ematch.h"


namespace q {

    queue::queue(ematch& em, euf::solver& ctx):
        em(em),
        ctx(ctx),
        m(ctx.get_manager()),
        m_params(ctx.get_config()),
        m_cost_function(m),
        m_new_gen_function(m),
        m_parser(m),
        m_evaluator(m),
        m_subst(m)
    {
        init_parser_vars();
        m_vals.resize(15, 0.0f);
        setup();
    }

    void queue::setup() {
        TRACE("q", tout << "qi_cost: " << m_params.m_qi_cost << "\n";);
        if (!m_parser.parse_string(m_params.m_qi_cost.c_str(), m_cost_function)) {
            warning_msg("invalid cost function '%s', switching to default one", m_params.m_qi_cost.c_str());
            VERIFY(m_parser.parse_string("(+ weight generation)", m_cost_function));
        }
        if (!m_parser.parse_string(m_params.m_qi_new_gen.c_str(), m_new_gen_function)) {
            warning_msg("invalid new_gen function '%s', switching to default one", m_params.m_qi_new_gen.c_str());
            VERIFY(m_parser.parse_string("cost", m_new_gen_function));
        }
        m_eager_cost_threshold = m_params.m_qi_eager_threshold;
    }

    void queue::init_parser_vars() {
#define COST 14
        m_parser.add_var("cost");
#define MIN_TOP_GENERATION 13
        m_parser.add_var("min_top_generation");
#define MAX_TOP_GENERATION 12
        m_parser.add_var("max_top_generation");
#define INSTANCES 11
        m_parser.add_var("instances");
#define SIZE 10
        m_parser.add_var("size");
#define DEPTH 9
        m_parser.add_var("depth");
#define GENERATION 8
        m_parser.add_var("generation");
#define QUANT_GENERATION 7
        m_parser.add_var("quant_generation");
#define WEIGHT 6
        m_parser.add_var("weight");
#define VARS 5
        m_parser.add_var("vars");
#define PATTERN_WIDTH 4
        m_parser.add_var("pattern_width");
#define TOTAL_INSTANCES 3
        m_parser.add_var("total_instances");
#define SCOPE 2
        m_parser.add_var("scope");
#define NESTED_QUANTIFIERS 1
        m_parser.add_var("nested_quantifiers");
#define CS_FACTOR 0
        m_parser.add_var("cs_factor");
    }

    void queue::set_values(fingerprint& f, float cost) {
        quantifier_stat * stat  = f.c->m_stat;
        quantifier* q = f.q();
        app* pat = f.b->m_pattern;
        m_vals[COST]               = cost;
        m_vals[MIN_TOP_GENERATION] = static_cast<float>(f.b->m_min_top_generation);
        m_vals[MAX_TOP_GENERATION] = static_cast<float>(f.b->m_max_top_generation);
        m_vals[INSTANCES]          = static_cast<float>(stat->get_num_instances_curr_branch());
        m_vals[SIZE]               = static_cast<float>(stat->get_size());
        m_vals[DEPTH]              = static_cast<float>(stat->get_depth());
        m_vals[GENERATION]         = static_cast<float>(f.m_max_generation);
        m_vals[QUANT_GENERATION]   = static_cast<float>(stat->get_generation());
        m_vals[WEIGHT]             = static_cast<float>(q->get_weight());
        m_vals[VARS]               = static_cast<float>(q->get_num_decls());
        m_vals[PATTERN_WIDTH]      = pat ? static_cast<float>(pat->get_num_args()) : 1.0f;
        m_vals[TOTAL_INSTANCES]    = static_cast<float>(stat->get_num_instances_curr_search());
        m_vals[SCOPE]              = static_cast<float>(ctx.s().num_scopes());
        m_vals[NESTED_QUANTIFIERS] = static_cast<float>(stat->get_num_nested_quantifiers());
        m_vals[CS_FACTOR]          = static_cast<float>(stat->get_case_split_factor());
        TRACE("q_detail", for (unsigned i = 0; i < m_vals.size(); i++) { tout << m_vals[i] << " "; } tout << "\n";);
    }

    float queue::get_cost(fingerprint& f) {
        set_values(f, 0);
        float r = m_evaluator(m_cost_function, m_vals.size(), m_vals.data());
        f.c->m_stat->update_max_cost(r);
        return r;
    }

    unsigned queue::get_new_gen(fingerprint& f, float cost) {
        set_values(f, cost);
        float r = m_evaluator(m_new_gen_function, m_vals.size(), m_vals.data());
        return std::max(f.m_max_generation + 1, static_cast<unsigned>(r));
    }

    struct queue::reset_new_entries : public trail {
        svector<entry>& m_entries;
        reset_new_entries(svector<entry>& e): m_entries(e) {}
        void undo() override {
            m_entries.reset();
        }
    };

    void queue::insert(fingerprint* f) {
        float cost = get_cost(*f);
        if (m_new_entries.empty()) 
            ctx.push(reset_new_entries(m_new_entries));
        m_new_entries.push_back(entry(f, cost));
    }

    void queue::instantiate(entry& ent) {
        fingerprint & f          = *ent.m_qb;
        quantifier * q           = f.q();
        unsigned num_bindings    = f.size();
        quantifier_stat * stat   = f.c->m_stat;

        ent.m_instantiated = true;
                
        unsigned gen = get_new_gen(f, ent.m_cost);
        bool new_propagation = false;
        if (em.propagate(true, f.nodes(), gen, *f.c, new_propagation))
            return;

        auto* ebindings = m_subst(q, num_bindings);
        for (unsigned i = 0; i < num_bindings; ++i)
            ebindings[i] = f.nodes()[i]->get_expr();
        expr_ref instance = m_subst();
        ctx.get_rewriter()(instance);
        if (m.is_true(instance)) {
            stat->inc_num_instances_simplify_true();
            return;
        }
        stat->inc_num_instances();

        m_stats.m_num_instances++;
        
        euf::solver::scoped_generation _sg(ctx, gen);
        sat::literal result_l = ctx.mk_literal(instance);
        em.add_instantiation(*f.c, *f.b, result_l);
    }

    bool queue::propagate() {
        if (m_new_entries.empty())
            return false;
        unsigned since_last_check = 0;
        for (entry & curr : m_new_entries) {
            since_last_check = (1 + since_last_check) & 0xFF;
            if (!m.inc())
                break;
            if (0 == since_last_check && ctx.resource_limits_exceeded()) 
                break;

            fingerprint& f = *curr.m_qb;

            if (curr.m_cost <= m_eager_cost_threshold) 
                instantiate(curr);
            else if (m_params.m_qi_promote_unsat && l_false == em.evaluate(f.nodes(), *f.c)) {
                // do not delay instances that produce a conflict.
                TRACE("q", tout << "promoting instance that produces a conflict\n" << mk_pp(f.q(), m) << "\n";);
                instantiate(curr);
            }
            else {
                TRACE("q", tout << "delaying quantifier instantiation... " << f << "\n" << mk_pp(f.q(), m) << "\ncost: " << curr.m_cost << "\n";);
                m_delayed_entries.push_back(curr);
                ctx.push(push_back_vector<svector<entry>>(m_delayed_entries));
            }
        }
        m_new_entries.reset();
        return true;
    }    

    struct queue::reset_instantiated : public trail {
        queue& q;
        unsigned idx;
        reset_instantiated(queue& q, unsigned idx): q(q), idx(idx) {}
        void undo() override {
            q.m_delayed_entries[idx].m_instantiated = false;
        }
    };
    
    bool queue::lazy_propagate() {
        if (m_delayed_entries.empty())
            return false;

        double cost_limit = m_params.m_qi_lazy_threshold;
        if (m_params.m_qi_conservative_final_check) {
            bool init = false;
            cost_limit = 0.0;
            for (entry & e : m_delayed_entries) {
                TRACE("q", tout << e.m_qb << ", cost: " << e.m_cost << ", instantiated: " << e.m_instantiated << "\n";);
                if (!e.m_instantiated && e.m_cost <= m_params.m_qi_lazy_threshold && (!init || e.m_cost < cost_limit)) {
                    init = true;
                    cost_limit = e.m_cost;
                }
            }
        }
        bool instantiated = false;
        unsigned idx = 0;
        for (entry & e : m_delayed_entries) {
            if (!e.m_instantiated && e.m_cost <= cost_limit) {
                instantiated = true;
                ctx.push(reset_instantiated(*this, idx));
                m_stats.m_num_lazy_instances++;
                instantiate(e);
            }
            ++idx;
        }
        return instantiated;
    }

    void queue::collect_statistics(::statistics & st) const {
        float fmin = 0.0f, fmax = 0.0f;
        bool found = false;
        for (auto const& e : m_delayed_entries) {
            if (!e.m_instantiated) {
                if (found)
                    fmin = std::min(fmin, e.m_cost), fmax = std::max(fmax, e.m_cost);
                else
                    fmin = e.m_cost, fmax = e.m_cost, found = true;
            }
        }
        st.update("q instantiations", m_stats.m_num_instances);
        st.update("q lazy instantiations", m_stats.m_num_lazy_instances);
        st.update("q missed instantiations", m_delayed_entries.size());
        st.update("q min missed cost", fmin);
        st.update("q max missed cost", fmax);
    }

}
