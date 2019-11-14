/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    qi_queue.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-15.

Revision History:

--*/
#include "util/warning.h"
#include "util/stats.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/var_subst.h"
#include "smt/smt_context.h"
#include "smt/qi_queue.h"

namespace smt {

    qi_queue::qi_queue(quantifier_manager & qm, context & ctx, qi_params & params):
        m_qm(qm),
        m_context(ctx),
        m(m_context.get_manager()),
        m_params(params),
        m_checker(m_context),
        m_cost_function(m),
        m_new_gen_function(m),
        m_parser(m),
        m_evaluator(m),
        m_subst(m),
        m_instances(m) {
        init_parser_vars();
        m_vals.resize(15, 0.0f);
    }

    qi_queue::~qi_queue() {
    }

    void qi_queue::setup() {
        TRACE("qi_cost", tout << "qi_cost: " << m_params.m_qi_cost << "\n";);
        if (!m_parser.parse_string(m_params.m_qi_cost.c_str(), m_cost_function)) {
            // it is not reasonable to abort here during the creation of smt::context just because an invalid option was provided.
            // throw default_exception("invalid cost function %s", m_params.m_qi_cost.c_str());

            // using warning message instead
            warning_msg("invalid cost function '%s', switching to default one", m_params.m_qi_cost.c_str());
            // Trying again with default function
            VERIFY(m_parser.parse_string("(+ weight generation)", m_cost_function));
        }
        if (!m_parser.parse_string(m_params.m_qi_new_gen.c_str(), m_new_gen_function)) {
            // See comment above
            // throw default_exception("invalid new-gen function %s", m_params.m_qi_new_gen.c_str());
            warning_msg("invalid new_gen function '%s', switching to default one", m_params.m_qi_new_gen.c_str());
            VERIFY(m_parser.parse_string("cost", m_new_gen_function));
        }
        m_eager_cost_threshold = m_params.m_qi_eager_threshold;
    }

    void qi_queue::init_parser_vars() {
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

    quantifier_stat * qi_queue::set_values(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation, float cost) {
        quantifier_stat * stat     = m_qm.get_stat(q);
        m_vals[COST]               = cost;
        m_vals[MIN_TOP_GENERATION] = static_cast<float>(min_top_generation);
        m_vals[MAX_TOP_GENERATION] = static_cast<float>(max_top_generation);
        m_vals[INSTANCES]          = static_cast<float>(stat->get_num_instances_curr_branch());
        m_vals[SIZE]               = static_cast<float>(stat->get_size());
        m_vals[DEPTH]              = static_cast<float>(stat->get_depth());
        m_vals[GENERATION]         = static_cast<float>(generation);
        m_vals[QUANT_GENERATION]   = static_cast<float>(stat->get_generation());
        m_vals[WEIGHT]             = static_cast<float>(q->get_weight());
        m_vals[VARS]               = static_cast<float>(q->get_num_decls());
        m_vals[PATTERN_WIDTH]      = pat ? static_cast<float>(pat->get_num_args()) : 1.0f;
        m_vals[TOTAL_INSTANCES]    = static_cast<float>(stat->get_num_instances_curr_search());
        m_vals[SCOPE]              = static_cast<float>(m_context.get_scope_level());
        m_vals[NESTED_QUANTIFIERS] = static_cast<float>(stat->get_num_nested_quantifiers());
        m_vals[CS_FACTOR]          = static_cast<float>(stat->get_case_split_factor());
        TRACE("qi_queue_detail", for (unsigned i = 0; i < m_vals.size(); i++) { tout << m_vals[i] << " "; } tout << "\n";);
        return stat;
    }

    float qi_queue::get_cost(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation) {
        quantifier_stat * stat = set_values(q, pat, generation, min_top_generation, max_top_generation, 0);
        float r = m_evaluator(m_cost_function, m_vals.size(), m_vals.c_ptr());
        stat->update_max_cost(r);
        return r;
    }

    unsigned qi_queue::get_new_gen(quantifier * q, unsigned generation, float cost) {
        // max_top_generation and min_top_generation are not available for computing inc_gen
        set_values(q, nullptr, generation, 0, 0, cost);
        float r = m_evaluator(m_new_gen_function, m_vals.size(), m_vals.c_ptr());
        return std::max(generation + 1, static_cast<unsigned>(r));
    }

    void qi_queue::insert(fingerprint * f, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation) {
        quantifier * q         = static_cast<quantifier*>(f->get_data());
        float cost             = get_cost(q, pat, generation, min_top_generation, max_top_generation);
        TRACE("qi_queue_detail",
              tout << "new instance of " << q->get_qid() << ", weight " << q->get_weight()
              << ", generation: " << generation << ", scope_level: " << m_context.get_scope_level() << ", cost: " << cost << "\n";
              for (unsigned i = 0; i < f->get_num_args(); i++) {
                  tout << "#" << f->get_arg(i)->get_owner_id() << " d:" << f->get_arg(i)->get_owner()->get_depth() << " ";
              }
              tout << "\n";);
        TRACE("new_entries_bug", tout << "[qi:insert]\n";);
        m_new_entries.push_back(entry(f, cost, generation));
    }

    void qi_queue::instantiate() {
        unsigned since_last_check = 0;
        for (entry & curr : m_new_entries) {
            fingerprint * f    = curr.m_qb;
            quantifier * qa    = static_cast<quantifier*>(f->get_data());

            if (curr.m_cost <= m_eager_cost_threshold) {
                instantiate(curr);
            }
            else if (m_params.m_qi_promote_unsat && m_checker.is_unsat(qa->get_expr(), f->get_num_args(), f->get_args())) {
                // do not delay instances that produce a conflict.
                TRACE("qi_unsat", tout << "promoting instance that produces a conflict\n" << mk_pp(qa, m) << "\n";);
                instantiate(curr);
            }
            else {
                TRACE("qi_queue", tout << "delaying quantifier instantiation... " << f << "\n" << mk_pp(qa, m) << "\ncost: " << curr.m_cost << "\n";);
                m_delayed_entries.push_back(curr);
            }

            // Periodically check if we didn't run out of time/memory.
            if (since_last_check++ > 100) {
                if (m_context.resource_limits_exceeded()) {
                    break;
                }
                if (m_context.get_cancel_flag()) {
                    break;
                }
                since_last_check = 0;
            }
        }
        m_new_entries.reset();
        TRACE("new_entries_bug", tout << "[qi:instantiate]\n";);
    }

    void qi_queue::display_instance_profile(fingerprint * f, quantifier * q, unsigned num_bindings, enode * const * bindings, unsigned proof_id, unsigned generation) {
        if (m.has_trace_stream()) {
            m.trace_stream() << "[instance] ";
            m.trace_stream() << static_cast<void*>(f);
            if (m.proofs_enabled())
                m.trace_stream() << " #" << proof_id;
            m.trace_stream() << " ; " << generation;
            m.trace_stream() << "\n";
        }
    }

    void qi_queue::instantiate(entry & ent) {
        fingerprint * f          = ent.m_qb;
        quantifier * q           = static_cast<quantifier*>(f->get_data());
        unsigned generation      = ent.m_generation;
        unsigned num_bindings    = f->get_num_args();
        enode * const * bindings = f->get_args();

        ent.m_instantiated = true;

        TRACE("qi_queue_profile", tout << q->get_qid() << ", gen: " << generation << " " << *f << " cost: " << ent.m_cost << "\n";);

        if (m_checker.is_sat(q->get_expr(), num_bindings, bindings)) {
            TRACE("checker", tout << "instance already satisfied\n";);
            return;
        }
        expr_ref instance(m);
        m_subst(q, num_bindings, bindings, instance);

        TRACE("qi_queue", tout << "new instance:\n" << mk_pp(instance, m) << "\n";);
        TRACE("qi_queue_instance", tout << "new instance:\n" << mk_pp(instance, m) << "\n";);
        expr_ref  s_instance(m);
        proof_ref pr(m);
        m_context.get_rewriter()(instance, s_instance, pr);
        TRACE("qi_queue_bug", tout << "new instance after simplification:\n" << s_instance << "\n";);
        if (m.is_true(s_instance)) {
            TRACE("checker", tout << "reduced to true, before:\n" << mk_ll_pp(instance, m););

            if (m.has_trace_stream()) {
                display_instance_profile(f, q, num_bindings, bindings, pr ? pr->get_id() : 0, generation);
                m.trace_stream() << "[end-of-instance]\n";
            }

            return;
        }
        quantifier_stat * stat = m_qm.get_stat(q);
        stat->inc_num_instances();
        if (stat->get_num_instances() % m_params.m_qi_profile_freq == 0) {
            m_qm.display_stats(verbose_stream(), q);
        }
        expr_ref lemma(m);
        if (m.is_or(s_instance)) {
            ptr_vector<expr> args;
            args.push_back(m.mk_not(q));
            args.append(to_app(s_instance)->get_num_args(), to_app(s_instance)->get_args());
            lemma = m.mk_or(args.size(), args.c_ptr());
        }
        else if (m.is_false(s_instance)) {
            lemma = m.mk_not(q);
        }
        else if (m.is_true(s_instance)) {
            lemma = s_instance;
        }
        else {
            lemma = m.mk_or(m.mk_not(q), s_instance);
        }
        m_instances.push_back(lemma);
        proof_ref pr1(m);
        unsigned proof_id = 0;
        if (m.proofs_enabled()) {
            expr_ref_vector bindings_e(m);
            for (unsigned i = 0; i < num_bindings; ++i) {
                bindings_e.push_back(bindings[i]->get_owner());
            }
            app * bare_lemma    = m.mk_or(m.mk_not(q), instance);
            proof * qi_pr       = m.mk_quant_inst(bare_lemma, num_bindings, bindings_e.c_ptr());
            proof_id            = qi_pr->get_id();
            if (bare_lemma == lemma) {
                pr1             = qi_pr;
            }
            else if (instance == s_instance) {
                proof * rw      = m.mk_rewrite(bare_lemma, lemma);
                pr1             = m.mk_modus_ponens(qi_pr, rw);
            }
            else {
                app * bare_s_lemma  = m.mk_or(m.mk_not(q), s_instance);
                proof * prs[1]      = { pr.get() };
                proof * cg          = m.mk_congruence(bare_lemma, bare_s_lemma, 1, prs);
                proof * rw          = m.mk_rewrite(bare_s_lemma, lemma);
                proof * tr          = m.mk_transitivity(cg, rw);
                pr1                 = m.mk_modus_ponens(qi_pr, tr);
            }
            m_instances.push_back(pr1);
        }
        TRACE("qi_queue", tout << mk_pp(lemma, m) << "\n#" << lemma->get_id() << ":=\n" << mk_ll_pp(lemma, m););
        m_stats.m_num_instances++;
        unsigned gen = get_new_gen(q, generation, ent.m_cost);
        display_instance_profile(f, q, num_bindings, bindings, proof_id, gen);
        m_context.internalize_instance(lemma, pr1, gen);
        if (f->get_def()) {
            m_context.internalize(f->get_def(), true);
        }
        TRACE_CODE({
            static unsigned num_useless = 0;
            if (m.is_or(lemma)) {
                app * n = to_app(lemma);
                bool has_unassigned = false;
                expr * true_child = 0;
                for (unsigned i = 0; i < n->get_num_args(); i++) {
                    expr * arg = n->get_arg(i);
                    switch(m_context.get_assignment(arg)) {
                    case l_undef: has_unassigned = true; break;
                    case l_true:  true_child = arg; break;
                    default:
                        break;
                    }
                }
                if (true_child && has_unassigned) {
                    TRACE("qi_queue_profile_detail", tout << "missed:\n" << mk_ll_pp(s_instance, m) << "\n#" << true_child->get_id() << "\n";);
                    num_useless++;
                    if (num_useless % 10 == 0) {
                        TRACE("qi_queue_profile", tout << "num useless: " << num_useless << "\n";);
                    }
                }
            }
        });

        if (m.has_trace_stream())
            m.trace_stream() << "[end-of-instance]\n";

    }

    void qi_queue::push_scope() {
        TRACE("new_entries_bug", tout << "[qi:push-scope]\n";);
        m_scopes.push_back(scope());
        SASSERT(m_new_entries.empty());
        scope & s = m_scopes.back();
        s.m_delayed_entries_lim    = m_delayed_entries.size();
        s.m_instances_lim          = m_instances.size();
        s.m_instantiated_trail_lim = m_instantiated_trail.size();
    }

    void qi_queue::pop_scope(unsigned num_scopes) {
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        unsigned old_sz     = s.m_instantiated_trail_lim;
        unsigned sz         = m_instantiated_trail.size();
        for (unsigned i = old_sz; i < sz; i++)
            m_delayed_entries[m_instantiated_trail[i]].m_instantiated = false;
        m_instantiated_trail.shrink(old_sz);
        m_delayed_entries.shrink(s.m_delayed_entries_lim);
        m_instances.shrink(s.m_instances_lim);
        m_new_entries.reset();
        m_scopes.shrink(new_lvl);
        TRACE("new_entries_bug", tout << "[qi:pop-scope]\n";);
    }

    void qi_queue::reset() {
        m_new_entries.reset();
        m_delayed_entries.reset();
        m_instances.reset();
        m_scopes.reset();
    }

    void qi_queue::init_search_eh() {
        m_subst.reset();
    }

    bool qi_queue::final_check_eh() {
        TRACE("qi_queue", display_delayed_instances_stats(tout); tout << "lazy threshold: " << m_params.m_qi_lazy_threshold
              << ", scope_level: " << m_context.get_scope_level() << "\n";);
        if (m_params.m_qi_conservative_final_check) {
            bool  init = false;
            float min_cost = 0.0;
            unsigned sz = m_delayed_entries.size();
            for (unsigned i = 0; i < sz; i++) {
                entry & e       = m_delayed_entries[i];
                TRACE("qi_queue", tout << e.m_qb << ", cost: " << e.m_cost << ", instantiated: " << e.m_instantiated << "\n";);
                if (!e.m_instantiated && e.m_cost <= m_params.m_qi_lazy_threshold && (!init || e.m_cost < min_cost)) {
                    init = true;
                    min_cost = e.m_cost;
                }
            }
            TRACE("qi_queue_min_cost", tout << "min_cost: " << min_cost << ", scope_level: " << m_context.get_scope_level() << "\n";);
            bool result = true;
            for (unsigned i = 0; i < sz; i++) {
                entry & e       = m_delayed_entries[i];
                TRACE("qi_queue", tout << e.m_qb << ", cost: " << e.m_cost << ", instantiated: " << e.m_instantiated << "\n";);
                if (!e.m_instantiated && e.m_cost <= min_cost) {
                    TRACE("qi_queue",
                          tout << "lazy quantifier instantiation...\n" << mk_pp(static_cast<quantifier*>(e.m_qb->get_data()), m) << "\ncost: " << e.m_cost << "\n";);
                    result             = false;
                    m_instantiated_trail.push_back(i);
                    m_stats.m_num_lazy_instances++;
                    instantiate(e);
                }
            }
            return result;
        }

        bool result = true;
        for (unsigned i = 0; i < m_delayed_entries.size(); i++) {
            entry & e       = m_delayed_entries[i];
            TRACE("qi_queue", tout << e.m_qb << ", cost: " << e.m_cost << ", instantiated: " << e.m_instantiated << "\n";);
            if (!e.m_instantiated && e.m_cost <= m_params.m_qi_lazy_threshold)  {
                TRACE("qi_queue",
                      tout << "lazy quantifier instantiation...\n" << mk_pp(static_cast<quantifier*>(e.m_qb->get_data()), m) << "\ncost: " << e.m_cost << "\n";);
                result             = false;
                m_instantiated_trail.push_back(i);
                m_stats.m_num_lazy_instances++;
                instantiate(e);
            }
        }
        return result;
    }

    struct delayed_qa_info {
        unsigned m_num;
        float    m_min_cost;
        float    m_max_cost;
        delayed_qa_info():m_num(0), m_min_cost(0.0f), m_max_cost(0.0f) {}
    };

    void qi_queue::display_delayed_instances_stats(std::ostream & out) const {
        obj_map<quantifier, delayed_qa_info> qa2info;
        ptr_vector<quantifier> qas;
        for (entry const & e : m_delayed_entries) {
            if (e.m_instantiated)
                continue;
            quantifier * qa = static_cast<quantifier*>(e.m_qb->get_data());
            delayed_qa_info info;
            if (qa2info.find(qa, info)) {
                info.m_num++;
                info.m_min_cost = std::min(info.m_min_cost, e.m_cost);
                info.m_max_cost = std::min(info.m_max_cost, e.m_cost);
            }
            else {
                qas.push_back(qa);
                info.m_num      = 1;
                info.m_min_cost = e.m_cost;
                info.m_max_cost = e.m_cost;
            }
            qa2info.insert(qa, info);
        }
        for (quantifier * qa : qas) {
            delayed_qa_info info;
            qa2info.find(qa, info);
            out << qa->get_qid() << ": " << info.m_num << " [" << info.m_min_cost << ", " << info.m_max_cost << "]\n";
        }
    }

    void qi_queue::get_min_max_costs(float & min, float & max) const {
        min = 0.0f;
        max = 0.0f;
        bool found = false;
        for (unsigned i = 0; i < m_delayed_entries.size(); i++) {
            if (!m_delayed_entries[i].m_instantiated) {
                float c = m_delayed_entries[i].m_cost;
                if (found) {
                    min = std::min(min, c);
                    max = std::max(max, c);
                }
                else {
                    found = true;
                    min = c;
                    max = c;
                }
            }
        }
    }

    void qi_queue::collect_statistics(::statistics & st) const {
        st.update("quant instantiations", m_stats.m_num_instances);
        st.update("lazy quant instantiations", m_stats.m_num_lazy_instances);
        st.update("missed quant instantiations", m_delayed_entries.size());
        float min, max;
        get_min_max_costs(min, max);
        st.update("min missed qa cost", min);
        st.update("max missed qa cost", max);
#if 0
        if (m_params.m_qi_profile) {
            out << "missed/delayed quantifier instances:\n";
            display_delayed_instances_stats(out);
        }
#endif
    }

};

