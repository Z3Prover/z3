/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_quantifier.cpp

Abstract:

    Quantifier reasoning support for smt::context.

Author:

    Leonardo de Moura (leonardo) 2012-02-16.

Revision History:

--*/
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/macros/macro_util.h"
#include "ast/occurs.h"
#include "ast/quantifier_stat.h"
#include "ast/euf/ho_matcher.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/well_sorted.h"
#include "ast/has_free_vars.h"
#include "smt/smt_quantifier.h"
#include "smt/smt_context.h"
#include "smt/smt_ho_qsolver.h"
#include "smt/smt_model_finder.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_quick_checker.h"
#include "smt/mam.h"
#include "smt/qi_queue.h"
#include "util/statistics.h"
#include "util/obj_hashtable.h"

namespace smt {

    quantifier_manager_plugin * mk_default_plugin();

    void log_single_justification(std::ostream & out, enode *en, obj_hashtable<enode> &visited, context &ctx, ast_manager &m);

    /**
         \brief Ensures that all relevant proof steps to explain why the enode is equal to the root of its
        equivalence class are in the log and up-to-date.
    */
    void quantifier_manager::log_justification_to_root(std::ostream & out, enode *en, obj_hashtable<enode> &visited, context &ctx, ast_manager &m) {
        enode *root = en->get_root();
        for (enode *it = en; it != root; it = it->get_trans_justification().m_target) {
            if (visited.find(it) == visited.end()) visited.insert(it);
            else break;

            if (!it->m_proof_is_logged) {
                log_single_justification(out, it, visited, ctx, m);
                it->m_proof_is_logged = true;
            } else if (it->get_trans_justification().m_justification.get_kind() == smt::eq_justification::kind::CONGRUENCE) {

                // When the justification of an argument changes m_proof_is_logged is not reset => We need to check if the proofs of all arguments are logged.
                const unsigned num_args = it->get_num_args();
                enode *target = it->get_trans_justification().m_target;

                for (unsigned i = 0; i < num_args; ++i) {
                    log_justification_to_root(out, it->get_arg(i), visited, ctx, m);
                    log_justification_to_root(out, target->get_arg(i), visited, ctx, m);
                }
                it->m_proof_is_logged = true;
            }
        }
        if (!root->m_proof_is_logged) {
            out << "[eq-expl] #" << root->get_owner_id() << " root\n";
            root->m_proof_is_logged = true;
        }
    }

    /**
         \brief Logs a single equality explanation step and, if necessary, recursively calls log_justification_to_root to log
        equalities needed by the step (e.g. argument equalities for congruence steps).
    */
    void log_single_justification(std::ostream & out, enode *en, obj_hashtable<enode> &visited, context &ctx, ast_manager &m) {
        smt::literal lit;
        unsigned num_args;
        enode *target = en->get_trans_justification().m_target;
        theory_id th_id;

        switch (en->get_trans_justification().m_justification.get_kind()) {
        case smt::eq_justification::kind::EQUATION:
            lit = en->get_trans_justification().m_justification.get_literal();
            out << "[eq-expl] #" << en->get_owner_id() << " lit #" << ctx.bool_var2expr(lit.var())->get_id() << " ; #" << target->get_owner_id() << "\n";
            break;
        case smt::eq_justification::kind::AXIOM:
            out << "[eq-expl] #" << en->get_owner_id() << " ax ; #" << target->get_owner_id() << "\n";
            break;
        case smt::eq_justification::kind::CONGRUENCE:
            if (!en->get_trans_justification().m_justification.used_commutativity()) {
                num_args = en->get_num_args();

                for (unsigned i = 0; i < num_args; ++i) {
                    quantifier_manager::log_justification_to_root(out, en->get_arg(i), visited, ctx, m);
                    quantifier_manager::log_justification_to_root(out, target->get_arg(i), visited, ctx, m);
                }

                out << "[eq-expl] #" << en->get_owner_id() << " cg";
                for (unsigned i = 0; i < num_args; ++i) {
                    out << " (#" << en->get_arg(i)->get_owner_id() << " #" << target->get_arg(i)->get_owner_id() << ")";
                }
                out << " ; #" << target->get_owner_id() << "\n";

                break;
            } else {

                // The e-graph only supports commutativity for binary functions
                out << "[eq-expl] #" << en->get_owner_id()
                    << " cg (#" << en->get_arg(0)->get_owner_id() << " #" << target->get_arg(1)->get_owner_id()
                    << ") (#" << en->get_arg(1)->get_owner_id() << " #" << target->get_arg(0)->get_owner_id()
                    << ") ; #" << target->get_owner_id() << "\n";
                break;
            }
        case smt::eq_justification::kind::JUSTIFICATION:
            th_id = en->get_trans_justification().m_justification.get_justification()->get_from_theory();
            if (th_id != null_theory_id) {
                symbol const theory = m.get_family_name(th_id);
                out << "[eq-expl] #" << en->get_owner_id() << " th " << theory.str() << " ; #" << target->get_owner_id() << "\n";
            } else {
                out << "[eq-expl] #" << en->get_owner_id() << " unknown ; #" << target->get_owner_id() << "\n";
            }
            break;
        }
    }

    struct quantifier_manager::imp {
        quantifier_manager &                   m_wrapper;
        context &                              m_context;
        smt_params &                           m_params;
        qi_queue                               m_qi_queue;
        obj_map<quantifier, q::quantifier_stat *> m_quantifier_stat;
        q::quantifier_stat_gen                    m_qstat_gen;
        ptr_vector<quantifier>                 m_quantifiers;
        scoped_ptr<quantifier_manager_plugin>  m_plugin;
        scoped_ptr<ho_qsolver>                 m_ho_qsolver;
        unsigned                               m_num_instances = 0;

        imp(quantifier_manager & wrapper, context & ctx, smt_params & p, quantifier_manager_plugin * plugin):
            m_wrapper(wrapper),
            m_context(ctx),
            m_params(p),
            m_qi_queue(m_wrapper, ctx, p),
            m_qstat_gen(ctx.get_manager(), ctx.get_region()),
            m_plugin(plugin) {
            m_qi_queue.setup();
            m_ho_qsolver = alloc(ho_qsolver, ctx, wrapper);
        }

        ast_manager& m() const { return m_context.get_manager(); }
        bool has_trace_stream() const { return m().has_trace_stream(); }
        std::ostream & trace_stream() { return m().trace_stream(); }

        q::quantifier_stat * get_stat(quantifier * q) const {
            return m_quantifier_stat.find(q);
        }

        unsigned get_generation(quantifier * q) const {
            auto* s = m_quantifier_stat.find_core(q);
            return s ? s->get_data().get_value()->get_generation() : 0;
        }

        void add(quantifier * q, unsigned generation) {
            q::quantifier_stat * stat = m_qstat_gen(q, generation);
            m_quantifier_stat.insert(q, stat);
            m_quantifiers.push_back(q);
            m_plugin->add(q);
        }

        bool has_quantifiers() const { return !m_quantifiers.empty(); }

        void display_stats(std::ostream & out, quantifier * q) {
            q::quantifier_stat * s     = get_stat(q);
            unsigned num_instances  = s->get_num_instances();
            unsigned num_instances_simplify_true = s->get_num_instances_simplify_true();
            unsigned num_instances_checker_sat  = s->get_num_instances_checker_sat();
            unsigned max_generation = s->get_max_generation();
            float max_cost          = s->get_max_cost();
            if (num_instances > 0 || num_instances_simplify_true>0 || num_instances_checker_sat>0) {
                out << "[quantifier_instances] ";
                out.width(10);
                out << q->get_qid().str() << " : ";
                out.width(6);
                out << num_instances << " : ";
                out.width(3);
                out << num_instances_simplify_true << " : ";
                out.width(3);
                out << num_instances_checker_sat << " : ";
                out.width(3);
                out << max_generation << " : " << max_cost << "\n";
            }
        }

        void del(quantifier * q) {
            if (m_params.m_qi_profile) {
                display_stats(verbose_stream(), q);
            }
            m_quantifiers.pop_back();
            m_quantifier_stat.erase(q);
        }

        bool empty() const {
            return m_quantifiers.empty();
        }

        bool is_shared(enode * n) const {
            return m_plugin->is_shared(n);
        }

        void log_causality(
            fingerprint* f,
            app * pat,
            vector<std::tuple<enode *, enode *>> & used_enodes) {

            if (pat != nullptr) {
                if (used_enodes.size() > 0) {
                    STRACE(causality, tout << "New-Match: "<< static_cast<void*>(f););
                    STRACE(triggers,  tout <<", Pat: "<< expr_ref(pat, m()););
                    STRACE(causality, tout <<", Father:";);
                }
                for (auto [orig, substituted] : used_enodes) {
                    (void) substituted;
                    if (orig == nullptr) {
                        STRACE(causality, tout << " #" << substituted->get_owner_id(););
                    }
                    else {
                        STRACE(causality, tout << " (#" << orig->get_owner_id() << " #" << substituted->get_owner_id() << ")";);
                    }
                }
                if (used_enodes.size() > 0) {
                    STRACE(causality, tout << "\n";);
                }
            }
        }

        void log_add_instance(
             fingerprint* f,
             quantifier * q, app * pat,
             unsigned num_bindings,
             enode * const * bindings,
             vector<std::tuple<enode *, enode *>> & used_enodes) {

            if (pat == nullptr) {
                trace_stream() << "[inst-discovered] MBQI " << f->get_data_hash() << " #" << q->get_id();
                for (unsigned i = 0; i < num_bindings; ++i) {
                    trace_stream() << " #" << f->get_arg(num_bindings - i - 1)->get_owner_id();
                }
                trace_stream() << "\n";
            } else {
                std::ostream & out = trace_stream();
                obj_hashtable<enode> already_visited;
                // In the term produced by the quantifier instantiation the root of the equivalence class of the terms bound to the quantified variables
                // is used. We need to make sure that all of these equalities appear in the log.
                for (unsigned i = 0; i < num_bindings; ++i) {
                    log_justification_to_root(out, bindings[i], already_visited, m_context, m());
                }

                for (auto [orig, substituted] : used_enodes) {
                    if (orig != nullptr) {
                        log_justification_to_root(out, orig, already_visited, m_context, m());
                        log_justification_to_root(out, substituted, already_visited, m_context, m());
                    }
                }
                // At this point all relevant equalities for the match are logged.
                out << "[new-match] " << f->get_data_hash() << " #" << q->get_id() << " #" << pat->get_id();
                for (unsigned i = 0; i < num_bindings; ++i) {
                    // I don't want to use mk_pp because it creates expressions for pretty printing.
                    // This nasty side-effect may change the behavior of Z3.
                    out << " #" << f->get_arg(num_bindings - i - 1)->get_owner_id();
                }
                out << " ;";
                for (auto n : used_enodes) {
                    enode *orig = std::get<0>(n);
                    enode *substituted = std::get<1>(n);
                    if (orig == nullptr)
                        out << " #" << substituted->get_owner_id();
                    else {
                        out << " (#" << orig->get_owner_id() << " #" << substituted->get_owner_id() << ")";
                    }
                }
                out << "\n";
            }
        }
        
        bool add_instance(quantifier * q, app * pat,
                          unsigned num_bindings,
                          enode * const * bindings,
                          unsigned max_generation,
                          unsigned min_top_generation,
                          unsigned max_top_generation,
                          vector<std::tuple<enode *, enode *>> & used_enodes, bool mbqi_instance) {

            // Try higher-order refinement first
            if (pat && m_plugin->refine_instance(q, pat, num_bindings, bindings, max_generation, min_top_generation, max_top_generation, used_enodes))
                return true;

            if (!m_quantifier_stat.contains(q)) {
                IF_VERBOSE(2, verbose_stream() << "add_instance: quantifier not in stat map: " << mk_pp(q, m()) << "\n");
                return false;
            }

            max_generation = std::max(max_generation, get_generation(q));
            
            get_stat(q)->update_max_generation(max_generation);
            fingerprint * f = m_context.add_fingerprint(q, q->get_id(), num_bindings, bindings);
            if (f) {
                vector<std::tuple<enode *, enode *>> trace_used_enodes(used_enodes);
                for (unsigned i = 0; i < num_bindings; ++i) {
                    enode * orig = bindings[i];
                    enode * root = f->get_arg(i);
                    if (orig == root)
                        continue;
                    bool found = false;
                    for (auto [used_orig, used_substituted] : trace_used_enodes) {
                        if (used_orig == orig && used_substituted == root) {
                            found = true;
                            break;
                        }
                    }
                    if (!found)
                        trace_used_enodes.push_back(std::make_tuple(orig, root));
                }
                if (is_trace_enabled(TraceTag::causality)) {
                    log_causality(f, pat, trace_used_enodes);
                }
                if (has_trace_stream()) {
                    log_add_instance(f, q, pat, num_bindings, bindings, trace_used_enodes);
                }
                m_qi_queue.insert(f, pat, max_generation, min_top_generation, max_top_generation, mbqi_instance); // TODO
                m_num_instances++;
            }

            CTRACE(bindings, f != nullptr, 
                  tout << expr_ref(q, m()) << "\n";
                  for (unsigned i = 0; i < num_bindings; ++i) {
                      tout << expr_ref(bindings[i]->get_expr(), m()) << " [r " << bindings[i]->get_root()->get_owner_id() << "] ";
                  }
                  tout << "\n";
                  );

            return f != nullptr;
        }

        void init_search_eh() {
            m_num_instances = 0;
            for (quantifier * q : m_quantifiers) {
                get_stat(q)->reset_num_instances_curr_search();
            }
            m_qi_queue.init_search_eh();
            m_plugin->init_search_eh();
            TRACE(smt_params, m_params.display(tout); );
        }

        void assign_eh(quantifier * q) {
            m_plugin->assign_eh(q);
        }

        void add_eq_eh(enode * n1, enode * n2) {
            m_plugin->add_eq_eh(n1, n2);
        }

        void register_on_binding(std::function<bool(quantifier*, expr*)>& on_binding) {
            m_qi_queue.register_on_binding(on_binding);
        }

        void relevant_eh(enode * n) {
            m_plugin->relevant_eh(n);
        }

        void restart_eh() {
            m_plugin->restart_eh();
        }

        void push() {
            m_plugin->push();
            m_qi_queue.push_scope();
        }

        void pop(unsigned num_scopes) {
            m_plugin->pop(num_scopes);
            m_qi_queue.pop_scope(num_scopes);
        }

        bool can_propagate() {
            return m_qi_queue.has_work() || m_plugin->can_propagate();
        }

        void propagate() {
            m_plugin->propagate();
            m_qi_queue.instantiate();
        }

        bool check_quantifier(quantifier* q) {
            return m_context.is_relevant(q) && m_context.get_assignment(q) == l_true;
        }

        bool quick_check_quantifiers() {
            if (m_params.m_qi_quick_checker == MC_NO)
                return true;
            if (m_quantifiers.empty())
                return true;
            IF_VERBOSE(10, verbose_stream() << "quick checking quantifiers (unsat)...\n";);
            quick_checker mc(m_context);
            bool result = true;
            for (quantifier* q : m_quantifiers) 
                if (check_quantifier(q) && mc.instantiate_unsat(q))
                    result = false;
            if (m_params.m_qi_quick_checker == MC_UNSAT || !result) {
                m_qi_queue.instantiate();
                return result;
            }
            // MC_NO_SAT is too expensive (it creates too many irrelevant instances).
            // we should use MBQI=true instead.
            IF_VERBOSE(10, verbose_stream() << "quick checking quantifiers (not sat)...\n";);
            for (quantifier* q : m_quantifiers) 
                if (check_quantifier(q) && mc.instantiate_not_sat(q))
                    result = false;
            m_qi_queue.instantiate();
            return result;
        }

        final_check_status final_check_eh(bool full) {
            if (full) {
                IF_VERBOSE(100, if (!m_quantifiers.empty()) verbose_stream() << "(smt.final-check \"quantifiers\")\n";);
                bool ho_instance = m_ho_qsolver->final_check();
                final_check_status result  = m_qi_queue.final_check_eh() && !ho_instance ? FC_DONE : FC_CONTINUE;
                final_check_status presult = m_plugin->final_check_eh(full);
                if (presult != FC_DONE)
                    result = presult;
                if (m_context.can_propagate())
                    result = FC_CONTINUE;
                if (result == FC_DONE && !m_params.m_qi_lazy_quick_checker && !quick_check_quantifiers())
                    result = FC_CONTINUE;
                return result;
            }
            else {
                return m_plugin->final_check_eh(false);
            }
        }

        check_model_result check_model(proto_model * m, obj_map<enode, app *> const & root2value) {
            if (empty())
                return SAT;
            return m_plugin->check_model(m, root2value);
        }

    };

    quantifier_manager::quantifier_manager(context & ctx, smt_params & fp, params_ref const & p) {
        m_imp = alloc(imp, *this, ctx, fp, mk_default_plugin());
        m_imp->m_plugin->set_manager(*this);
        m_lazy_scopes = 0;
        m_lazy = true;
        
    }

    quantifier_manager::~quantifier_manager() {
        dealloc(m_imp);
    }

    context & quantifier_manager::get_context() const {
        return m_imp->m_context;
    }

    void quantifier_manager::add(quantifier * q, unsigned generation) {
        if (m_lazy) {
            while (m_lazy_scopes-- > 0) m_imp->push();
            m_lazy = false;
        }
        m_imp->add(q, generation);
    }

    void quantifier_manager::del(quantifier * q) {
        m_imp->del(q);
    }

    bool quantifier_manager::empty() const {
        return m_imp->empty();
    }

    bool quantifier_manager::is_shared(enode * n) const {
        return m_imp->is_shared(n);
    }

    q::quantifier_stat * quantifier_manager::get_stat(quantifier * q) const {
        return m_imp->get_stat(q);
    }

    unsigned quantifier_manager::get_generation(quantifier * q) const {
        return m_imp->get_generation(q);
    }

    bool quantifier_manager::add_instance(quantifier * q, app * pat,
                                          unsigned num_bindings,
                                          enode * const * bindings,
                                          unsigned max_generation,
                                          unsigned min_top_generation,
                                          unsigned max_top_generation,
                                          vector<std::tuple<enode *, enode *>> & used_enodes, bool mbqi_instance) {
        return m_imp->add_instance(q, pat, num_bindings, bindings, max_generation, min_top_generation, max_top_generation, used_enodes, mbqi_instance);
    }

    bool quantifier_manager::add_instance(quantifier * q, unsigned num_bindings, enode * const * bindings, unsigned generation) {
        vector<std::tuple<enode *, enode *>> tmp;
        return add_instance(q, nullptr, num_bindings, bindings,
            generation, generation, generation, tmp);
    }

    void quantifier_manager::init_search_eh() {
        m_imp->init_search_eh();
    }

    void quantifier_manager::assign_eh(quantifier * q) {
        m_imp->assign_eh(q);
    }

    void quantifier_manager::add_eq_eh(enode * n1, enode * n2) {
        m_imp->add_eq_eh(n1, n2);
    }

    void quantifier_manager::register_on_binding(std::function<bool(quantifier*, expr*)>& on_binding) {
        m_imp->register_on_binding(on_binding);
    }

    void quantifier_manager::relevant_eh(enode * n) {
        m_imp->relevant_eh(n);
    }

    final_check_status quantifier_manager::final_check_eh(bool full) {
        return m_imp->final_check_eh(full);
    }

    void quantifier_manager::restart_eh() {
        m_imp->restart_eh();
    }

    bool quantifier_manager::can_propagate() const {
        return m_imp->can_propagate();
    }

    void quantifier_manager::propagate() {
        m_imp->propagate();
    }

    bool quantifier_manager::model_based() const {
        return m_imp->m_plugin->model_based();
    }

    bool quantifier_manager::has_quantifiers() const {
        return m_imp->has_quantifiers();
    }

    bool quantifier_manager::mbqi_enabled(quantifier *q) const {
        return m_imp->m_plugin->mbqi_enabled(q);
    }

    void quantifier_manager::adjust_model(proto_model * m) {
        m_imp->m_plugin->adjust_model(m);
    }

    quantifier_manager::check_model_result quantifier_manager::check_model(proto_model * m, obj_map<enode, app *> const & root2value) {
        return m_imp->check_model(m, root2value);
    }

    void quantifier_manager::push() {        
        if (m_lazy) 
            ++m_lazy_scopes;
        else 
            m_imp->push();
    }

    void quantifier_manager::pop(unsigned num_scopes) {
        if (m_lazy)
            m_lazy_scopes -= num_scopes;
        else
            m_imp->pop(num_scopes);
    }

    void quantifier_manager::reset() {
        context & ctx        = m_imp->m_context;
        smt_params & p = m_imp->m_params;
        quantifier_manager_plugin * plugin = m_imp->m_plugin->mk_fresh();
        m_imp->~imp();
        m_imp = new (m_imp) imp(*this, ctx, p, plugin);
        plugin->set_manager(*this);
    }

    void quantifier_manager::display(std::ostream & out) const {
    }

    void quantifier_manager::collect_instances(vector<std::pair<expr_ref, app_ref>> & out) {
        m_imp->m_qi_queue.collect_instances(out);
    }

    void quantifier_manager::collect_statistics(::statistics & st) const {
        m_imp->m_qi_queue.collect_statistics(st);
        m_imp->m_plugin->collect_statistics(st);
        m_imp->m_ho_qsolver->collect_statistics(st);
    }

    void quantifier_manager::reset_statistics() {
    }

    void quantifier_manager::display_stats(std::ostream & out, quantifier * q) const {
        m_imp->display_stats(out, q);
    }

    ptr_vector<quantifier>::const_iterator quantifier_manager::begin_quantifiers() const {
        return m_imp->m_quantifiers.begin();
    }

    ptr_vector<quantifier>::const_iterator quantifier_manager::end_quantifiers() const {
        return m_imp->m_quantifiers.end();
    }

    unsigned quantifier_manager::num_quantifiers() const {
        return m_imp->m_quantifiers.size();
    }

    // The default plugin uses E-matching, MBQI and quick-checker
    class default_qm_plugin : public quantifier_manager_plugin {
        quantifier_manager *        m_qm;
        smt_params *                m_fparams;
        context *                   m_context;
        scoped_ptr<mam>             m_mam;
        scoped_ptr<mam>             m_lazy_mam;
        scoped_ptr<model_finder>    m_model_finder;
        scoped_ptr<model_checker>   m_model_checker;
        scoped_ptr<euf::ho_matcher> m_ho_matcher;
        unsigned                    m_new_enode_qhead;
        unsigned                    m_lazy_matching_idx;
        bool                        m_active;

        // State for higher-order match refinement callback
        struct ho_match_state {
            quantifier*  m_q = nullptr;
            app*         m_pat = nullptr;
            unsigned     m_num_bindings = 0;
            enode* const* m_bindings = nullptr;
            unsigned     m_max_generation = 0;
            unsigned     m_min_top_generation = 0;
            unsigned     m_max_top_generation = 0;
            vector<std::tuple<enode*, enode*>>* m_used_enodes = nullptr;
            vector<std::pair<quantifier*, expr_ref_vector>> m_matches;
        };
        ho_match_state m_ho_state;
        unsigned       m_stat_ho_refine = 0;    // number of times ho-matching refinement is invoked
        unsigned       m_stat_ho_instances = 0; // number of instances added via ho-matching
        unsigned       m_stat_arith_instances = 0;
        bool           m_arith_matching_done = false;
        static constexpr unsigned arith_max_bounds = 64;

        struct arith_bound {
            quantifier* q = nullptr;
            // Nested declarations guide matching, but only q's declarations receive emitted bindings.
            unsigned inner_decls = 0;
            unsigned num_decls = 0;
            app_ref head;
            expr_ref rest;
            rational coefficient;

            arith_bound(ast_manager& m): head(m), rest(m) {}
        };

        static expr* arith_atom(arith_util& a, expr* t, rational& coefficient) {
            expr* n = nullptr, *atom = nullptr;
            coefficient = rational(1);
            if (a.is_mul(t, n, atom) && a.is_numeral(n, coefficient))
                return atom;
            coefficient = rational(1);
            return t;
        }

        static bool arith_coefficient(arith_util& a, expr* polynomial, expr* atom,
                                      rational& coefficient, expr_ref& rest) {
            expr_ref_vector terms(rest.get_manager());
            coefficient = rational(0);
            unsigned size = a.is_add(polynomial) ? to_app(polynomial)->get_num_args() : 1;
            if (size > 32)
                return false;
            for (unsigned i = 0; i < size; ++i) {
                expr* t = a.is_add(polynomial) ? to_app(polynomial)->get_arg(i) : polynomial;
                rational k;
                if (arith_atom(a, t, k) == atom)
                    coefficient += k;
                else
                    terms.push_back(t);
            }
            if (coefficient.is_zero())
                return false;
            rest = terms.empty() ? a.mk_real(0) :
                   terms.size() == 1 ? terms.get(0) : a.mk_add(terms.size(), terms.data());
            return true;
        }

        using arith_definitions = vector<std::pair<func_decl*, expr_ref_vector>>;

        bool arith_scaled_polynomial(expr* polynomial, expr* term, app_ref& head, expr_ref& normalized,
                                     arith_util& a, th_rewriter& rw) {
            if (!a.is_mul(term))
                return false;
            ast_manager& m = a.get_manager();
            auto flatten = [&](expr* monomial, ptr_buffer<expr>& factors) {
                ptr_buffer<expr> todo;
                todo.push_back(monomial);
                for (unsigned inspected = 0; !todo.empty() && inspected < 8; ++inspected) {
                    expr* factor = todo.back();
                    todo.pop_back();
                    if (a.is_mul(factor)) {
                        if (todo.size() + factors.size() + to_app(factor)->get_num_args() > 4)
                            return false;
                        for (expr* arg : *to_app(factor))
                            todo.push_back(arg);
                    }
                    else
                        factors.push_back(factor);
                }
                return todo.empty();
            };
            ptr_buffer<expr> head_factors;
            if (!flatten(term, head_factors))
                return false;
            expr_ref_vector scales(m);
            for (expr* factor : head_factors) {
                if (has_free_vars(factor)) {
                    if (head || !is_uninterp(factor) || !a.is_real(factor))
                        return false;
                    head = to_app(factor);
                }
                else {
                    rational value;
                    if (!a.is_numeral(factor, value))
                        scales.push_back(factor);
                }
            }
            if (!head || scales.empty())
                return false;
            expr_ref scale(scales.size() == 1 ? scales.get(0) : a.mk_mul(scales.size(), scales.data()), m);
            expr_ref negative(a.mk_uminus(scale), m);
            expr_ref nonnegative(a.mk_ge(scale, a.mk_real(0)), m);
            expr_ref magnitude(m.mk_ite(nonnegative, scale, negative), m);
            expr_ref denominator(a.mk_add(a.mk_real(1), magnitude), m);
            expr_ref_vector terms(m);
            unsigned size = a.is_add(polynomial) ? to_app(polynomial)->get_num_args() : 1;
            if (size > 32)
                return false;
            // These are hints, not division identities for possibly zero symbolic factors.
            for (unsigned i = 0; i < size; ++i) {
                expr* monomial = a.is_add(polynomial) ? to_app(polynomial)->get_arg(i) : polynomial;
                ptr_buffer<expr> factors;
                if (!flatten(monomial, factors))
                    return false;
                svector<bool> removed(factors.size(), false);
                bool shared = true;
                for (expr* factor : scales) {
                    unsigned j = 0;
                    for (; j < factors.size(); ++j)
                        if (!removed[j] && factors[j] == factor) {
                            removed[j] = true;
                            break;
                        }
                    shared &= j < factors.size();
                }
                if (!shared) {
                    terms.push_back(a.mk_div(monomial, denominator));
                    continue;
                }
                expr_ref_vector remaining(m);
                for (unsigned j = 0; j < factors.size(); ++j)
                    if (!removed[j])
                        remaining.push_back(factors[j]);
                terms.push_back(remaining.empty() ? a.mk_real(1) :
                                remaining.size() == 1 ? remaining.get(0) :
                                a.mk_mul(remaining.size(), remaining.data()));
            }
            normalized = terms.size() == 1 ? terms.get(0) : a.mk_add(terms.size(), terms.data());
            rw(normalized);
            return true;
        }

        void get_arith_definitions(quantifier* q, arith_util& a, arith_definitions& definitions) {
            ast_manager& m = a.get_manager();
            if (!is_forall(q) || q->get_num_decls() != 1 || !a.is_real(q->get_decl_sort(0)) ||
                !m.is_or(q->get_expr()) || to_app(q->get_expr())->get_num_args() > 4)
                return;
            // Guarded branches guide bindings; they never replace asserted definitions.
            macro_util util(m);
            macro_util::macro_candidates candidates(m);
            util.collect_macro_candidates(q, candidates);
            for (unsigned index = 0; index < candidates.size(); ++index) {
                func_decl* f = candidates.get_f(index);
                if (candidates.ineq(index) || f->get_arity() != 1 || !a.is_real(f->get_range()))
                    continue;
                expr* rhs = candidates.get_def(index);
                unsigned size = a.is_add(rhs) ? to_app(rhs)->get_num_args() : 1;
                bool affine = size <= 4;
                for (unsigned i = 0; i < size && affine; ++i) {
                    expr* term = a.is_add(rhs) ? to_app(rhs)->get_arg(i) : rhs;
                    rational k, value;
                    expr* atom = arith_atom(a, term, k);
                    affine = (is_var(atom) && to_var(atom)->get_idx() == 0) || a.is_numeral(atom, value);
                }
                if (!affine)
                    continue;
                for (auto& [previous, branches] : definitions)
                    if (previous == f) {
                        for (expr* branch : branches)
                            if (branch == rhs)
                                return;
                        if (branches.size() < 2)
                            branches.push_back(rhs);
                        return;
                    }
                if (definitions.size() < 4) {
                    expr_ref_vector branches(m);
                    branches.push_back(rhs);
                    definitions.push_back({f, branches});
                }
                return;
            }
        }

        void get_arith_bounds(quantifier* q, arith_util& a, th_rewriter& rw, vector<arith_bound>& bounds,
                              arith_definitions const& definitions) {
            if (!is_forall(q) || q->get_num_decls() > 4)
                return;
            for (unsigned i = 0; i < q->get_num_decls(); ++i)
                if (!a.is_real(q->get_decl_sort(i)))
                    return;
            ast_manager& m = a.get_manager();
            unsigned inspected = 0;
            auto collect = [&](auto&& self, expr* body, unsigned inner, bool negated) -> void {
                if (++inspected > 128 || bounds.size() == arith_max_bounds)
                    return;
                expr* arg = nullptr;
                if (m.is_not(body, arg)) {
                    self(self, arg, inner, !negated);
                    return;
                }
                if (m.is_and(body) || m.is_or(body)) {
                    for (expr* child : *to_app(body)) {
                        if (inspected >= 128 || bounds.size() == arith_max_bounds)
                            break;
                        self(self, child, inner, negated);
                    }
                    return;
                }
                expr* condition = nullptr, *yes = nullptr, *no = nullptr;
                if (m.is_ite(body, condition, yes, no) && m.is_bool(body)) {
                    self(self, yes, inner, negated);
                    self(self, no, inner, negated);
                    self(self, condition, inner, false);
                    return;
                }
                if (is_forall(body) && !negated) {
                    quantifier* nested = to_quantifier(body);
                    if (inner + nested->get_num_decls() + q->get_num_decls() > 4)
                        return;
                    for (unsigned i = 0; i < nested->get_num_decls(); ++i)
                        if (!a.is_real(nested->get_decl_sort(i)))
                            return;
                    self(self, nested->get_expr(), inner + nested->get_num_decls(), negated);
                    return;
                }
                expr* lhs = nullptr, *rhs = nullptr;
                bool reverse;
                if (a.is_le(body, lhs, rhs) || a.is_lt(body, lhs, rhs))
                    reverse = true;
                else if (a.is_ge(body, lhs, rhs) || a.is_gt(body, lhs, rhs))
                    reverse = false;
                else
                    return;
                if (!a.is_real(lhs))
                    return;
                expr_ref_vector left(m), right(m);
                auto expand = [&](expr* side, expr_ref_vector& terms) {
                    expr* c = nullptr, *t = nullptr, *e = nullptr;
                    if (m.is_ite(side, c, t, e)) {
                        terms.push_back(t);
                        terms.push_back(e);
                        return;
                    }
                    unsigned size = a.is_add(side) ? to_app(side)->get_num_args() : 1;
                    for (unsigned i = 0; i < size && i < 32; ++i) {
                        expr* term = a.is_add(side) ? to_app(side)->get_arg(i) : side;
                        rational k;
                        expr* atom = arith_atom(a, term, k);
                        if (!is_uninterp(atom) || to_app(atom)->get_num_args() != 1)
                            continue;
                        for (auto const& [f, branches] : definitions)
                            if (f == to_app(atom)->get_decl()) {
                                expr_ref_vector arguments(m);
                                arguments.push_back(to_app(atom)->get_arg(0));
                                var_subst subst(m, false);
                                for (expr* branch : branches) {
                                    expr_ref value = subst(branch, arguments);
                                    expr_safe_replace replace(m);
                                    replace.insert(atom, value);
                                    expr_ref expanded(side, m);
                                    replace(expanded);
                                    rw(expanded);
                                    terms.push_back(expanded);
                                }
                                return;
                            }
                    }
                    terms.push_back(side);
                };
                expand(lhs, left);
                expand(rhs, right);
                for (expr* x : left)
                    for (expr* y : right) {
                        expr_ref polynomial(reverse ? a.mk_sub(y, x) : a.mk_sub(x, y), m);
                        if (negated)
                            polynomial = a.mk_uminus(polynomial);
                        rw(polynomial);
                        unsigned size = a.is_add(polynomial) ? to_app(polynomial)->get_num_args() : 1;
                        if (size > 32)
                            continue;
                        for (unsigned i = 0; i < size && bounds.size() < arith_max_bounds; ++i) {
                            expr* term = a.is_add(polynomial) ? to_app(polynomial)->get_arg(i) : polynomial.get();
                            rational k;
                            expr* atom = arith_atom(a, term, k);
                            arith_bound bound(m);
                            expr_ref normalized(polynomial);
                            if (is_uninterp(atom) && has_free_vars(atom) && a.is_real(atom))
                                bound.head = to_app(atom);
                            else if (!arith_scaled_polynomial(polynomial, term, bound.head, normalized, a, rw))
                                continue;
                            bound.q = q;
                            bound.inner_decls = inner;
                            bound.num_decls = q->get_num_decls() + inner;
                            if (arith_coefficient(a, normalized, bound.head, bound.coefficient, bound.rest))
                                bounds.push_back(bound);
                        }
                    }
            };
            collect(collect, q->get_expr(), 0, false);
        }

        bool arith_unify(app* source, app* target, unsigned source_vars,
                         expr_ref_vector const& variables, expr_ref_vector& bindings,
                         arith_util& a, th_rewriter& rw) {
            ast_manager& m = a.get_manager();
            expr_ref_vector equations(m);
            svector<bool> expanded;
            for (unsigned i = 0; i < source->get_num_args(); ++i) {
                if (!a.is_real(source->get_arg(i)))
                    return false;
                equations.push_back(a.mk_sub(source->get_arg(i), target->get_arg(i)));
                expanded.push_back(false);
            }
            for (unsigned round = 0; round <= bindings.size(); ++round) {
                bool progress = false, solved = true;
                for (unsigned i = 0; i < equations.size(); ++i) {
                    expr_ref equation(equations.get(i), m);
                    rw(equation);
                    equations.set(i, equation);
                    if (a.is_zero(equation))
                        continue;
                    solved = false;
                    bool bound = false;
                    for (unsigned j = 0; j < bindings.size(); ++j) {
                        // Prefer binding target variables, leaving source arguments as common anchors.
                        unsigned index = (j + source_vars) % bindings.size();
                        expr* variable = variables.get(index);
                        if (bindings.get(index) != variable)
                            continue;
                        rational coefficient;
                        expr_ref rest(m);
                        if (!arith_coefficient(a, equation, variable, coefficient, rest) || occurs(variable, rest))
                            continue;
                        expr_ref value(a.mk_mul(a.mk_real(-rational(1) / coefficient), rest), m);
                        rw(value);
                        expr_safe_replace replace(m);
                        replace.insert(variable, value);
                        replace(bindings);
                        replace(equations);
                        bound = progress = true;
                        break;
                    }
                    if (bound || expanded[i] || !a.is_add(equation) || to_app(equation)->get_num_args() > 4)
                        continue;
                    rational sum;
                    ptr_buffer<app> applications;
                    for (expr* term : *to_app(equation)) {
                        rational k;
                        expr* atom = arith_atom(a, term, k);
                        if (!is_uninterp(atom) ||
                            (!applications.empty() && applications[0]->get_decl() != to_app(atom)->get_decl()))
                            break;
                        sum += k;
                        applications.push_back(to_app(atom));
                    }
                    if (applications.size() != to_app(equation)->get_num_args() || !sum.is_zero() ||
                        equations.size() + (applications.size() - 1) * applications[0]->get_num_args() > 16)
                        continue;
                    expanded[i] = true;
                    for (unsigned j = 1; j < applications.size(); ++j)
                        for (unsigned k = 0; k < applications[0]->get_num_args(); ++k) {
                            if (!a.is_real(applications[0]->get_arg(k)))
                                return false;
                            equations.push_back(a.mk_sub(applications[0]->get_arg(k), applications[j]->get_arg(k)));
                            expanded.push_back(false);
                        }
                    progress = true;
                }
                if (solved)
                    return true;
                if (!progress)
                    return false;
            }
            return false;
        }

        void arith_eliminate(expr_ref& polynomial, vector<arith_bound> const& bounds,
                             bool positive, arith_util& a, th_rewriter& rw) {
            ast_manager& m = a.get_manager();
            for (unsigned step = 0; step < 4; ++step) {
                unsigned size = a.is_add(polynomial) ? to_app(polynomial)->get_num_args() : 1;
                if (size > 32)
                    return;
                bool changed = false;
                for (unsigned i = 0; i < size && !changed; ++i) {
                    expr* term = a.is_add(polynomial) ? to_app(polynomial)->get_arg(i) : polynomial.get();
                    rational k;
                    expr* atom = arith_atom(a, term, k);
                    if (!is_uninterp(atom))
                        continue;
                    for (auto const& rule : bounds) {
                        if (m.is_or(rule.q->get_expr()) || rule.head->get_decl() != to_app(atom)->get_decl() ||
                            rule.head->get_num_args() != rule.num_decls ||
                            (k.is_pos() == positive) == rule.coefficient.is_pos())
                            continue;
                        expr_ref_vector substitution(m);
                        substitution.resize(rule.num_decls);
                        bool match = true;
                        for (unsigned j = 0; j < rule.head->get_num_args(); ++j) {
                            expr* x = rule.head->get_arg(j);
                            if (!is_var(x) || to_var(x)->get_idx() >= substitution.size() ||
                                substitution.get(to_var(x)->get_idx())) {
                                match = false;
                                break;
                            }
                            substitution.set(to_var(x)->get_idx(), to_app(atom)->get_arg(j));
                        }
                        if (!match)
                            continue;
                        expr_ref rest(m);
                        if (!arith_coefficient(a, polynomial, atom, k, rest))
                            continue;
                        var_subst subst(m, false);
                        expr_ref replacement = subst(rule.rest, substitution);
                        replacement = a.mk_mul(a.mk_real(-k / rule.coefficient), replacement);
                        polynomial = a.mk_add(rest, replacement);
                        rw(polynomial);
                        changed = true;
                        break;
                    }
                }
                if (!changed)
                    return;
            }
        }

        unsigned arith_project_nested(expr_ref& polynomial, vector<arith_bound> const& bounds,
                                      arith_util& a, th_rewriter& rw) {
            ast_manager& m = a.get_manager();
            unsigned projected = 0;
            // Zero outer parameters suggest centers for shared witnesses, not unconditional equalities.
            for (unsigned step = 0; step < 8; ++step) {
                unsigned size = a.is_add(polynomial) ? to_app(polynomial)->get_num_args() : 1;
                if (size > 32)
                    break;
                bool changed = false;
                for (unsigned i = 0; i < size && !changed; ++i) {
                    expr* term = a.is_add(polynomial) ? to_app(polynomial)->get_arg(i) : polynomial.get();
                    rational k;
                    expr* atom = arith_atom(a, term, k);
                    if (!is_uninterp(atom))
                        continue;
                    for (auto const& rule : bounds) {
                        if (!rule.inner_decls || rule.head->get_decl() != to_app(atom)->get_decl() ||
                            rule.head->get_num_args() != rule.inner_decls)
                            continue;
                        expr_ref_vector substitution(m);
                        svector<bool> assigned(rule.inner_decls, false);
                        for (unsigned j = 0; j < rule.num_decls; ++j)
                            substitution.push_back(a.mk_real(0));
                        bool match = true;
                        for (unsigned j = 0; j < rule.head->get_num_args(); ++j) {
                            expr* x = rule.head->get_arg(j);
                            if (!is_var(x) || to_var(x)->get_idx() >= rule.inner_decls ||
                                assigned[to_var(x)->get_idx()]) {
                                match = false;
                                break;
                            }
                            unsigned index = to_var(x)->get_idx();
                            assigned[index] = true;
                            substitution.set(index, to_app(atom)->get_arg(j));
                        }
                        if (!match)
                            continue;
                        expr_ref rest(m);
                        if (!arith_coefficient(a, polynomial, atom, k, rest))
                            continue;
                        var_subst subst(m, false);
                        expr_ref replacement = subst(rule.rest, substitution);
                        replacement = a.mk_mul(a.mk_real(-k / rule.coefficient), replacement);
                        expr_ref next(a.mk_add(rest, replacement), m);
                        rw(next);
                        if (next == polynomial)
                            continue;
                        polynomial = next;
                        ++projected;
                        changed = true;
                        break;
                    }
                }
                if (!changed)
                    break;
            }
            return projected;
        }

        bool add_arith_instance(quantifier* q, expr_ref_vector const& terms,
                                vector<std::pair<quantifier*, expr_ref_vector>>& instances, unsigned& budget) {
            for (auto const& [previous, values] : instances) {
                if (previous != q || values.size() != terms.size())
                    continue;
                bool duplicate = true;
                for (unsigned i = 0; i < terms.size(); ++i)
                    duplicate &= terms.get(i) == values.get(i);
                if (duplicate)
                    return false;
            }
            if (!budget)
                return false;
            --budget;
            instances.push_back({q, terms});
            ptr_buffer<enode> bindings;
            unsigned generation = 0;
            for (expr* term : terms) {
                if (!m_context->e_internalized(term))
                    m_context->internalize(term, false);
                enode* n = m_context->get_enode(term);
                generation = std::max(generation, m_context->get_generation(n));
                bindings.push_back(n);
            }
            bool added = m_qm->add_instance(q, bindings.size(), bindings.data(), generation);
            if (added)
                ++m_stat_arith_instances;
            return added;
        }

        bool arith_match(arith_bound const& source, arith_bound const& target,
                         vector<arith_bound> const& bounds, expr_ref_vector const& variables,
                         vector<std::pair<quantifier*, expr_ref_vector>>& instances,
                         vector<std::pair<quantifier*, expr_ref_vector>>& witnesses,
                         arith_util& a, th_rewriter& rw, unsigned& budget, unsigned& witness_budget,
                         unsigned& chain_budget, unsigned depth) {
            if (source.head->get_decl() != target.head->get_decl() || source.head->get_num_args() > 4 ||
                (!source.inner_decls && target.inner_decls) ||
                (source.q == target.q && (source.inner_decls || target.inner_decls)) ||
                source.coefficient.is_pos() == target.coefficient.is_pos())
                return false;
            ast_manager& m = a.get_manager();
            unsigned ns = source.num_decls, nt = target.num_decls;
            expr_ref_vector bindings(m), source_substitution(m), target_substitution(m);
            for (unsigned i = 0; i < ns + nt; ++i)
                bindings.push_back(variables.get(i));
            for (unsigned i = 0; i < ns; ++i)
                source_substitution.push_back(bindings.get(i));
            for (unsigned i = 0; i < nt; ++i)
                target_substitution.push_back(bindings.get(ns + i));
            var_subst subst(m, false);
            expr_ref source_head = subst(source.head, source_substitution);
            expr_ref target_head = subst(target.head, target_substitution);
            if (!arith_unify(to_app(source_head), to_app(target_head), ns, variables, bindings, a, rw))
                return false;
            for (unsigned i = 0; i < ns; ++i)
                source_substitution.set(i, bindings.get(i));
            for (unsigned i = 0; i < nt; ++i)
                target_substitution.set(i, bindings.get(ns + i));
            expr_ref source_rest = subst(source.rest, source_substitution);
            expr_ref target_rest = subst(target.rest, target_substitution);
            source_rest = a.mk_mul(a.mk_real(rational(1) / source.coefficient), source_rest);
            target_rest = a.mk_mul(a.mk_real(rational(1) / target.coefficient), target_rest);
            expr_ref difference(a.mk_sub(source_rest, target_rest), m);
            rw(difference);
            arith_eliminate(difference, bounds, source.coefficient.is_pos(), a, rw);
            unsigned projected = source.inner_decls ? arith_project_nested(difference, bounds, a, rw) : 0;
            unsigned pivot = bindings.size();
            expr_ref remainder(m);
            rational coefficient;
            for (unsigned i = 0; i < bindings.size(); ++i)
                if ((i < ns ? i >= source.inner_decls : i - ns >= target.inner_decls) &&
                    bindings.get(i) == variables.get(i) &&
                    arith_coefficient(a, difference, variables.get(i), coefficient, remainder) &&
                    !occurs(variables.get(i), remainder)) {
                    pivot = i;
                    break;
                }
            if (pivot == bindings.size())
                return false;
            expr_safe_replace ground(m);
            expr_ref anchor(a.mk_real(0), m);
            ptr_buffer<expr> todo;
            expr_mark visited;
            todo.push_back(source.q->get_expr());
            for (unsigned inspected = 0; !todo.empty() && inspected < 64; ++inspected) {
                expr* e = todo.back();
                todo.pop_back();
                if (visited.is_marked(e))
                    continue;
                visited.mark(e);
                if (is_uninterp(e) && to_app(e)->get_num_args() == 0 && a.is_real(e)) {
                    anchor = e;
                    break;
                }
                if (is_app(e))
                    for (expr* arg : *to_app(e))
                        todo.push_back(arg);
            }
            for (unsigned i = 0; i < bindings.size(); ++i)
                if (i != pivot && bindings.get(i) == variables.get(i))
                    ground.insert(variables.get(i), anchor);
            ground(remainder);
            expr_ref boundary(a.mk_mul(a.mk_real(-rational(1) / coefficient), remainder), m);
            if (projected)
                boundary = a.mk_mul(a.mk_real(rational(1) / rational(projected + 1)), boundary);
            rw(boundary);
            if (projected && a.is_zero(boundary))
                return false;
            bool added = false;
            // These are candidate bindings, including for disjunctive bounds, not asserted arithmetic lemmas.
            for (int offset : {0, 1, -1}) {
                if (projected && offset != 0)
                    break;
                if (!budget)
                    break;
                expr_ref value(a.mk_add(boundary, a.mk_real(offset)), m);
                rw(value);
                expr_safe_replace instantiate(m);
                instantiate.insert(variables.get(pivot), value);
                expr_ref_vector source_terms(m), target_terms(m);
                for (unsigned i = ns + nt; i-- > 0;) {
                    expr_ref term(bindings.get(i), m);
                    ground(term);
                    instantiate(term);
                    rw(term);
                    if (i < ns && i >= source.inner_decls)
                        source_terms.push_back(term);
                    else if (i >= ns && i - ns >= target.inner_decls)
                        target_terms.push_back(term);
                }
                added = add_arith_instance(source.q, source_terms, instances, budget) || added;
                if (offset == 0 && source.inner_decls && !target.inner_decls &&
                    pivot < ns && depth < 4 && chain_budget) {
                    expr_safe_replace transfer(m);
                    for (unsigned i = 0; i < nt; ++i) {
                        expr_ref variable(m.mk_var(i, a.mk_real()), m);
                        transfer.insert(variables.get(ns + i), variable);
                    }
                    for (unsigned i = 0; i < ns; ++i)
                        if (i == pivot)
                            transfer.insert(variables.get(i), value);
                        else if (bindings.get(i) == variables.get(i))
                            transfer.insert(variables.get(i), anchor);
                    expr_ref_vector substitution(m);
                    for (unsigned i = 0; i < ns; ++i) {
                        expr_ref term(bindings.get(i), m);
                        transfer(term);
                        rw(term);
                        substitution.push_back(term);
                    }
                    for (auto const& guard : bounds) {
                        if (!chain_budget || !budget)
                            break;
                        if (guard.q != source.q || guard.inner_decls != source.inner_decls ||
                            guard.head->get_decl() == source.head->get_decl())
                            continue;
                        expr_ref polynomial(a.mk_mul(a.mk_real(guard.coefficient), guard.head), m);
                        polynomial = a.mk_add(polynomial, guard.rest);
                        polynomial = subst(polynomial, substitution);
                        rw(polynomial);
                        unsigned size = a.is_add(polynomial) ? to_app(polynomial)->get_num_args() : 1;
                        if (size > 32)
                            continue;
                        for (unsigned i = 0; i < size && chain_budget && budget; ++i) {
                            expr* term = a.is_add(polynomial) ? to_app(polynomial)->get_arg(i) : polynomial.get();
                            rational k;
                            expr* atom = arith_atom(a, term, k);
                            if (!is_uninterp(atom) || !has_free_vars(atom) || !a.is_real(atom))
                                continue;
                            arith_bound next_target(m);
                            next_target.q = target.q;
                            next_target.num_decls = nt;
                            next_target.head = to_app(atom);
                            if (!arith_coefficient(a, polynomial, atom, next_target.coefficient, next_target.rest))
                                continue;
                            for (auto const& next_source : bounds) {
                                if (!chain_budget || !budget)
                                    break;
                                if (!next_source.inner_decls || next_source.head->get_decl() != to_app(atom)->get_decl())
                                    continue;
                                --chain_budget;
                                added = arith_match(next_source, next_target, bounds, variables, instances,
                                                    witnesses, a, rw, budget, witness_budget, chain_budget,
                                                    depth + 1) || added;
                            }
                        }
                    }
                }
                if (offset != 0 || !source.inner_decls) {
                    added = add_arith_instance(target.q, target_terms, instances, budget) || added;
                    continue;
                }
                expr_ref_vector guard_values(m);
                bool guarded = false;
                for (auto const& guard : bounds) {
                    if (budget == 0 || guard_values.size() == 2)
                        break;
                    if (guard.q != source.q || guard.head->get_decl() == source.head->get_decl())
                        continue;
                    bool closed = true;
                    for (unsigned i = 0; i < guard.inner_decls; ++i) {
                        expr_ref variable(m.mk_var(i, a.mk_real()), m);
                        if (occurs(variable, guard.head))
                            closed = false;
                    }
                    if (!closed)
                        continue;
                    expr_ref_vector substitution(m);
                    for (unsigned i = 0; i < guard.inner_decls; ++i)
                        substitution.push_back(anchor);
                    for (unsigned i = 0; i < source_terms.size(); ++i)
                        substitution.push_back(source_terms.get(source_terms.size() - i - 1));
                    expr_ref candidate = subst(guard.head, substitution);
                    rw(candidate);
                    bool duplicate = false;
                    for (expr* previous : guard_values)
                        duplicate |= previous == candidate;
                    if (duplicate || has_free_vars(candidate))
                        continue;
                    guard_values.push_back(candidate);
                    for (unsigned i = target.inner_decls; i < nt && budget > 0; ++i)
                        if (bindings.get(ns + i) == variables.get(ns + i)) {
                            expr_ref_vector guarded_terms(target_terms);
                            guarded_terms.set(nt - i - 1, candidate);
                            guarded = true;
                            bool deferred = false;
                            if (projected && guarded_terms.size() == 1) {
                                bool found = false;
                                for (auto& [q, values] : witnesses)
                                    if (q == target.q) {
                                        found = true;
                                        for (expr* value : values)
                                            deferred |= value == candidate;
                                        if (!deferred && witness_budget) {
                                            values.push_back(candidate);
                                            --witness_budget;
                                            deferred = true;
                                        }
                                        break;
                                    }
                                if (!found && witness_budget) {
                                    witnesses.push_back({target.q, guarded_terms});
                                    --witness_budget;
                                    deferred = true;
                                }
                            }
                            if (!deferred)
                                added = add_arith_instance(target.q, guarded_terms, instances, budget) || added;
                        }
                }
                if (!guarded)
                    added = add_arith_instance(target.q, target_terms, instances, budget) || added;
            }
            return added;
        }

        bool arith_match() {
            if (m_arith_matching_done || !m_fparams->m_qi_arith || !use_ematching())
                return false;
            m_arith_matching_done = true;
            ast_manager& m = m_context->get_manager();
            arith_util a(m);
            th_rewriter rw(m);
            vector<arith_bound> bounds;
            arith_definitions definitions;
            unsigned scanned = 0;
            for (auto it = m_qm->begin_quantifiers(); it != m_qm->end_quantifiers() && scanned < 64; ++it, ++scanned) {
                quantifier* q = *it;
                if (m_context->is_relevant(q) && m_context->get_assignment(q) == l_true &&
                    m_qm->get_generation(q) == 0)
                    get_arith_definitions(q, a, definitions);
            }
            unsigned inspected = 0;
            for (auto it = m_qm->begin_quantifiers(); it != m_qm->end_quantifiers(); ++it) {
                quantifier* q = *it;
                if (++inspected > 64 || bounds.size() == arith_max_bounds)
                    break;
                if (!m_context->is_relevant(q) || m_context->get_assignment(q) != l_true ||
                    m_qm->get_generation(q) != 0)
                    continue;
                get_arith_bounds(q, a, rw, bounds, definitions);
            }
            if (bounds.size() < 2)
                return false;
            expr_ref_vector variables(m);
            for (unsigned i = 0; i < 8; ++i)
                variables.push_back(m.mk_fresh_const("arith", a.mk_real()));
            bool added = false;
            unsigned budget = 32;
            vector<std::pair<quantifier*, expr_ref_vector>> instances;
            vector<std::pair<quantifier*, expr_ref_vector>> witnesses;
            unsigned witness_budget = 32;
            unsigned chain_budget = 32;
            for (auto const& source : bounds)
                for (auto const& target : bounds) {
                    if (!budget)
                        break;
                    added = arith_match(source, target, bounds, variables, instances, witnesses, a, rw,
                                        budget, witness_budget, chain_budget, 0) || added;
                }
            for (auto const& [q, values] : witnesses) {
                expr_ref value(values.get(0), m);
                for (unsigned i = 1; i < values.size(); ++i) {
                    expr_ref condition(a.mk_le(value, values.get(i)), m);
                    value = m.mk_ite(condition, value, values.get(i));
                }
                expr_ref_vector terms(m);
                terms.push_back(value);
                added = add_arith_instance(q, terms, instances, budget) || added;
            }
            return added;
        }
    public:
        default_qm_plugin():
            m_qm(nullptr),
            m_context(nullptr),
            m_new_enode_qhead(0),
            m_lazy_matching_idx(0),
            m_active(false) {
        }

        void set_manager(quantifier_manager & qm) override {
            SASSERT(m_qm == nullptr);
            m_qm            = &qm;
            m_context       = &(qm.get_context());
            m_fparams       = &(m_context->get_fparams());
            ast_manager & m = m_context->get_manager();

            m_mam           = mk_mam(*m_context);
            m_lazy_mam      = mk_mam(*m_context);
            m_model_finder  = alloc(model_finder, m);
            m_model_checker = alloc(model_checker, m, *m_fparams, *(m_model_finder.get()));

            m_model_finder->set_context(m_context);
            m_model_checker->set_qm(qm);

            if (m_fparams->m_ho_matching) {
                m_ho_matcher = alloc(euf::ho_matcher, m, m_context->get_trail_stack());
                m_ho_matcher->set_max_iterations(m_fparams->m_ho_matching_bound);
                std::function<void(euf::ho_subst&)> on_match = [this](euf::ho_subst& s) {
                    on_ho_match(s);
                };
                m_ho_matcher->set_on_match(on_match);
            }
        }

        quantifier_manager_plugin * mk_fresh() override { return alloc(default_qm_plugin); }

        void on_ho_match(euf::ho_subst &s) {
            auto &st = m_ho_state;
            auto *hoq = st.m_q;
            auto *q = m_ho_matcher->hoq2q(hoq);
            if (!q)
                return;
            auto const &binding = s.get_binding(q);
            st.m_matches.push_back({ q, binding });
        }

        void consume_ho_matches() {
            for (auto const &[q, binding] : m_ho_state.m_matches) 
                consume_ho_match(q, binding);            
            m_ho_state.m_matches.reset();
        }

        void consume_ho_match(quantifier * q, expr_ref_vector const& binding) {
            auto &st = m_ho_state;
            // Create enodes for the refined bindings and add instance
            ptr_buffer<enode> new_bindings;
            unsigned max_gen = st.m_max_generation;
            TRACE(ho_matching, tout << binding << "\n");
            for (expr* e : binding) {
                if (!e)
                    return; // incomplete binding
                if (has_free_vars(e))
                    return;
                if (!m_context->e_internalized(e)) {
                    m_context->internalize(e, false);
                }
                enode* n = m_context->get_enode(e);
                new_bindings.push_back(n);
                unsigned gen = m_context->get_generation(n);
                if (gen > max_gen)
                    max_gen = gen;
            }

            TRACE(ho_matching, 
                ast_manager &m = m_context->get_manager();
                tout << "ho_match refined for " << mk_pp(q, m) << "\n";
                for (unsigned i = 0; i < new_bindings.size(); ++i)
                    tout << "  binding[" << i << "] = " << mk_bounded_pp(new_bindings[i]->get_expr(), m) << "\n";);

            vector<std::tuple<enode*, enode*>> used_enodes;
            m_context->add_instance(q, nullptr, new_bindings.size(), new_bindings.data(),
                                    max_gen, st.m_min_top_generation, st.m_max_top_generation, used_enodes);
            ++m_stat_ho_instances;
        }

        bool try_ho_refine(quantifier* qa, app* pat, unsigned num_bindings, enode* const* bindings,
                           unsigned max_generation, unsigned min_top_gen, unsigned max_top_gen,
                           vector<std::tuple<enode*, enode*>>& used_enodes) {
            if (!m_ho_matcher || !m_ho_matcher->is_ho_pattern(pat))
                return false;

            ast_manager& m = m_context->get_manager();
            expr_ref_vector s(m);
            // With var_subst(std_order=true): var idx maps to s[s.size()-idx-1]
            // SMT MAM bindings: bindings[i] = var at index (num_bindings-1-i)
            // So bindings[i] corresponds to s[i] with std_order
            for (unsigned i = 0; i < num_bindings; ++i)
                s.push_back(bindings[i]->get_expr());

            m_ho_state.m_q = qa;
            m_ho_state.m_pat = pat;
            m_ho_state.m_num_bindings = num_bindings;
            m_ho_state.m_bindings = bindings;
            m_ho_state.m_max_generation = max_generation;
            m_ho_state.m_min_top_generation = min_top_gen;
            m_ho_state.m_max_top_generation = max_top_gen;
            m_ho_state.m_used_enodes = &used_enodes;
            m_ho_state.m_matches.reset();

            IF_VERBOSE(10, verbose_stream() << "try_ho_refine: q=" << mk_pp(qa, m) << "\n  pat=" << mk_pp(pat, m) << "\n";
                for (unsigned i = 0; i < num_bindings; ++i)
                    verbose_stream() << "  s[" << i << "] = " << mk_pp(s.get(i), m) << " sort=" << mk_pp(s.get(i)->get_sort(), m) << "\n";);

            m_ho_matcher->refine_ho_match(pat, s);
            consume_ho_matches();
            ++m_stat_ho_refine;
            return true;
        }

        bool model_based() const override { return m_fparams->m_mbqi; }

        void collect_statistics(::statistics & st) const override {
            if (m_fparams->m_ho_matching) {
                st.update("ho-matching refinements", m_stat_ho_refine);
                st.update("ho-matching instances", m_stat_ho_instances);
            }
            if (m_model_finder)
                m_model_finder->collect_statistics(st);
            st.update("arith-quantifier-instances", m_stat_arith_instances);
        }

        bool mbqi_enabled(quantifier *q) const override {
            if (!m_fparams->m_mbqi_id) return true;
            const symbol &s = q->get_qid();
            size_t len = strlen(m_fparams->m_mbqi_id);
            if (s == symbol::null || s.is_numerical())
                return len == 0;
            return strncmp(s.bare_str(), m_fparams->m_mbqi_id, len) == 0;
        }

        /* Quantifier id's must begin with the prefix specified by parameter
           mbqi.id to be instantiated with MBQI. The default value is the
           empty string, so all quantifiers are instantiated. */
        void add(quantifier * q) override {
            TRACE(model_finder, tout << "add " << q->get_id() << ": " << q << " " << m_fparams->m_mbqi << " " << mbqi_enabled(q) << "\n";);
            if (m_fparams->m_mbqi && mbqi_enabled(q)) {
                m_active = true;
                m_model_finder->register_quantifier(q);
            }
        }

        void del(quantifier * q) override { }

        void push() override {
            m_mam->push_scope();
            m_lazy_mam->push_scope();
            m_model_finder->push_scope();   
        }

        void pop(unsigned num_scopes) override {
            m_mam->pop_scope(num_scopes);
            m_lazy_mam->pop_scope(num_scopes);
            m_model_finder->pop_scope(num_scopes);
        }

        void init_search_eh() override {
            m_lazy_matching_idx = 0;
            m_arith_matching_done = false;
            m_model_finder->init_search_eh();
            m_model_checker->init_search_eh();            
        }

        void assign_eh(quantifier * q) override {
            m_active = true;
            ast_manager& m = m_context->get_manager();
            (void)m;
            if (!m_fparams->m_ematching) {
                return;
            }
            bool has_unary_pattern = false;
            unsigned num_patterns = q->get_num_patterns();
            for (unsigned i = 0; i < num_patterns; ++i) {
                app * mp = to_app(q->get_pattern(i));
                if (mp->get_num_args() == 1) {
                    has_unary_pattern = true;
                    break;
                }
            }
            unsigned num_eager_multi_patterns = m_fparams->m_qi_max_eager_multipatterns;
            if (!has_unary_pattern)
                num_eager_multi_patterns++;
            for (unsigned i = 0, j = 0; i < num_patterns; ++i) {
                app * mp = to_app(q->get_pattern(i));
                SASSERT(m.is_pattern(mp));
                bool unary = (mp->get_num_args() == 1);
                if (!unary && j >= num_eager_multi_patterns) {
                    TRACE(quantifier, tout << "delaying (too many multipatterns):\n" << mk_ismt2_pp(mp, m) << "\n"
                          << "j: " << j << " unary: " << unary << " m_params.m_qi_max_eager_multipatterns: " << m_fparams->m_qi_max_eager_multipatterns
                          << " num_eager_multi_patterns: " << num_eager_multi_patterns << "\n";);
                    m_lazy_mam->add_pattern(q, mp);
                }
                else {
                    TRACE(quantifier, tout << "adding:\n" << expr_ref(mp, m) << "\n";);
                    m_mam->add_pattern(q, mp);
                }
                // Compile HO pattern and also register the compiled version with MAM
                if (m_ho_matcher) {
                    auto [q1, p1] = m_ho_matcher->compile_ho_pattern(q, mp);
                    if (p1 != mp) {
                        IF_VERBOSE(10, verbose_stream() << "ho_matching: q=" << q->get_qid() << " p1= " << mk_pp(p1, m) << "\n");
                        m_lazy_mam->add_pattern(q1, p1);
                    }
                }
                if (!unary)
                    j++;
            }
        }

        bool use_ematching() const {
            return m_fparams->m_ematching && !m_qm->empty();
        }


        bool refine_instance(quantifier* q, app* pat, unsigned num_bindings, enode* const* bindings,
                             unsigned max_generation, unsigned min_top_generation, unsigned max_top_generation,
                             vector<std::tuple<enode*, enode*>>& used_enodes) override {
            return try_ho_refine(q, pat, num_bindings, bindings, max_generation, min_top_generation, max_top_generation, used_enodes);
        }

        void add_eq_eh(enode * e1, enode * e2) override {
            if (use_ematching())
                m_mam->add_eq_eh(e1, e2);
        }

        void relevant_eh(enode * e) override {
            if (use_ematching()) {
                m_mam->relevant_eh(e, false);
                m_lazy_mam->relevant_eh(e, true);
            }
        }

        bool can_propagate() const override {
            bool r = m_active && m_mam->has_work();
            IF_VERBOSE(11, if (r) verbose_stream() << "ho_matching: can_propagate=true\n");
            return r;
        }

        void restart_eh() override {
            if (m_fparams->m_mbqi) {
                m_model_finder->restart_eh();
                m_model_checker->restart_eh();
            }
            TRACE(mam_stats, m_mam->display(tout););
        }

        bool is_shared(enode * n) const override {
            return m_active && (m_mam->is_shared(n) || m_lazy_mam->is_shared(n));
        }

        void adjust_model(proto_model * m) override {
            if (m_fparams->m_mbqi) {
                m_model_finder->fix_model(m);
            }
        }

        void propagate() override {
            if (!m_active)
                return;
            m_mam->match();
            if (!m_context->relevancy() && use_ematching()) {
                ptr_vector<enode>::const_iterator it  = m_context->begin_enodes();
                ptr_vector<enode>::const_iterator end = m_context->end_enodes();
                unsigned sz = static_cast<unsigned>(end - it);
                if (sz > m_new_enode_qhead) {
                    m_context->push_trail(value_trail<unsigned>(m_new_enode_qhead));
                    it += m_new_enode_qhead;
                    while (m_new_enode_qhead < sz) {
                        enode * e = *it;
                        m_mam->relevant_eh(e, false);
                        m_lazy_mam->relevant_eh(e, true);
                        m_new_enode_qhead++;
                        it++;
                    }
                }
            }
        }

        quantifier_manager::check_model_result
        check_model(proto_model * m, obj_map<enode, app *> const & root2value) override {
            if (m_fparams->m_mbqi) {
                IF_VERBOSE(10, verbose_stream() << "(smt.mbqi)\n";);
                if (m_model_checker->check(m, root2value)) {
                    return quantifier_manager::SAT;
                }
                else if (m_model_checker->has_new_instances()) {
                    return quantifier_manager::RESTART;
                }
            }
            return quantifier_manager::UNKNOWN;
        }

        final_check_status final_check_eh(bool full) override {
            if (!full) {
                if (m_fparams->m_qi_lazy_instantiation)
                    return final_check_quant();
                return FC_DONE;
            }
            else {
                return final_check_quant();
            }
        }

        /**
           \brief Final check related with quantifiers...
        */
        final_check_status final_check_quant() {
            if (arith_match())
                return FC_CONTINUE;
            if (use_ematching()) {
                if (m_lazy_matching_idx < m_fparams->m_qi_max_lazy_multipattern_matching) {
                    m_lazy_mam->rematch();
                    m_context->push_trail(value_trail<unsigned>(m_lazy_matching_idx));
                    m_lazy_matching_idx++;
                }
            }
            return FC_DONE;
        }

    };

    quantifier_manager_plugin * mk_default_plugin() {
        return alloc(default_qm_plugin);
    }

}
