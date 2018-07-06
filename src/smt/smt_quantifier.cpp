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
#include "ast/ast_smt2_pp.h"
#include "smt/smt_quantifier.h"
#include "smt/smt_context.h"
#include "smt/smt_quantifier_stat.h"
#include "smt/smt_model_finder.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_quick_checker.h"
#include "smt/mam.h"
#include "smt/qi_queue.h"

namespace smt {

    quantifier_manager_plugin * mk_default_plugin();

    struct quantifier_manager::imp {
        quantifier_manager &                   m_wrapper;
        context &                              m_context;
        smt_params &                           m_params;
        qi_queue                               m_qi_queue;
        obj_map<quantifier, quantifier_stat *> m_quantifier_stat;
        quantifier_stat_gen                    m_qstat_gen;
        ptr_vector<quantifier>                 m_quantifiers;
        scoped_ptr<quantifier_manager_plugin>  m_plugin;
        unsigned                               m_num_instances;

        imp(quantifier_manager & wrapper, context & ctx, smt_params & p, quantifier_manager_plugin * plugin):
            m_wrapper(wrapper),
            m_context(ctx),
            m_params(p),
            m_qi_queue(m_wrapper, ctx, p),
            m_qstat_gen(ctx.get_manager(), ctx.get_region()),
            m_plugin(plugin) {
            m_num_instances = 0;
            m_qi_queue.setup();
        }

        ast_manager& m() const { return m_context.get_manager(); }
        bool has_trace_stream() const { return m().has_trace_stream(); }
        std::ostream & trace_stream() { return m().trace_stream(); }

        quantifier_stat * get_stat(quantifier * q) const {
            return m_quantifier_stat.find(q);
        }

        unsigned get_generation(quantifier * q) const {
            return get_stat(q)->get_generation();
        }

        void add(quantifier * q, unsigned generation) {
            quantifier_stat * stat = m_qstat_gen(q, generation);
            m_quantifier_stat.insert(q, stat);
            m_quantifiers.push_back(q);
            m_plugin->add(q);
        }

        void display_stats(std::ostream & out, quantifier * q) {
            quantifier_stat * s     = get_stat(q);
            unsigned num_instances  = s->get_num_instances();
            unsigned max_generation = s->get_max_generation();
            float max_cost          = s->get_max_cost();
            if (num_instances > 0) {
                out << "[quantifier_instances] ";
                out.width(10);
                out << q->get_qid().str().c_str() << " : ";
                out.width(6);
                out << num_instances << " : ";
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

        /**
           \brief Ensures that all relevant proof steps to explain why the enode is equal to the root of its
           equivalence class are in the log and up-to-date.
        */
        void log_justification_to_root(std::ostream & log, enode *en) {
            enode *root = en->get_root();
            for (enode *it = en; it != root; it = it->get_trans_justification().m_target) {
                if (it->m_proof_logged_status == smt::logged_status::NOT_LOGGED) {
                    it->m_proof_logged_status = smt::logged_status::BEING_LOGGED;
                    log_single_justification(log, it);
                    it->m_proof_logged_status = smt::logged_status::LOGGED;
                } else if (it->m_proof_logged_status != smt::logged_status::BEING_LOGGED && it->get_trans_justification().m_justification.get_kind() == smt::eq_justification::kind::CONGRUENCE) {

                    // When the justification of an argument changes m_proof_logged_status is not reset => We need to check if the proofs of all arguments are logged.
                    it->m_proof_logged_status = smt::logged_status::BEING_LOGGED;
                    const unsigned num_args = it->get_num_args();
                    enode *target = it->get_trans_justification().m_target;

                    for (unsigned i = 0; i < num_args; ++i) {
                        log_justification_to_root(log, it->get_arg(i));
                        log_justification_to_root(log, target->get_arg(i));
                    }
                    it->m_proof_logged_status = smt::logged_status::LOGGED;
                }
            }
            if (root->m_proof_logged_status == smt::logged_status::NOT_LOGGED) {
                log << "[eq-expl] #" << root->get_owner_id() << " root\n";
                root->m_proof_logged_status = smt::logged_status::LOGGED;
            }
        }

        /**
          \brief Logs a single equality explanation step and, if necessary, recursively calls log_justification_to_root to log
          equalities needed by the step (e.g. argument equalities for congruence steps).
        */
        void log_single_justification(std::ostream & out, enode *en) {
            smt::literal lit;
            unsigned num_args;
            enode *target = en->get_trans_justification().m_target;
            theory_id th_id;

            switch (en->get_trans_justification().m_justification.get_kind()) {
            case smt::eq_justification::kind::EQUATION:
                lit = en->get_trans_justification().m_justification.get_literal();
                out << "[eq-expl] #" << en->get_owner_id() << " lit #" << m_context.bool_var2expr(lit.var())->get_id() << " ; #" << target->get_owner_id() << "\n";
                break;
            case smt::eq_justification::kind::AXIOM:
                out << "[eq-expl] #" << en->get_owner_id() << " ax ; #" << target->get_owner_id() << "\n";
                break;
            case smt::eq_justification::kind::CONGRUENCE:
                if (!en->get_trans_justification().m_justification.used_commutativity()) {
                    num_args = en->get_num_args();

                    for (unsigned i = 0; i < num_args; ++i) {
                        log_justification_to_root(out, en->get_arg(i));
                        log_justification_to_root(out, target->get_arg(i));
                    }

                    out << "[eq-expl] #" << en->get_owner_id() << " cg";
                    for (unsigned i = 0; i < num_args; ++i) {
                        out << " (#" << en->get_arg(i)->get_owner_id() << " #" << target->get_arg(i)->get_owner_id() << ")";
                    }
                    out << " ; #" << target->get_owner_id() << "\n";

                    break;
                } else {
                    out << "[eq-expl] #" << en->get_owner_id() << " nyi ; #" << target->get_owner_id() << "\n";
                    break;
                }
            case smt::eq_justification::kind::JUSTIFICATION:
                th_id = en->get_trans_justification().m_justification.get_justification()->get_from_theory();
                if (th_id != null_theory_id) {
                    symbol const theory = m().get_family_name(th_id);
                    out << "[eq-expl] #" << en->get_owner_id() << " th " << theory.str() << " ; #" << target->get_owner_id() << "\n";
                } else {
                    out << "[eq-expl] #" << en->get_owner_id() << " unknown ; #" << target->get_owner_id() << "\n";
                }
                break;
            default:
                out << "[eq-expl] #" << en->get_owner_id() << " unknown ; #" << target->get_owner_id() << "\n";
                break;
            }
        }

        bool add_instance(quantifier * q, app * pat,
                          unsigned num_bindings,
                          enode * const * bindings,
                          expr* def,
                          unsigned max_generation,
                          unsigned min_top_generation,
                          unsigned max_top_generation,
                          vector<std::tuple<enode *, enode *>> & used_enodes) {
            max_generation = std::max(max_generation, get_generation(q));
            if (m_num_instances > m_params.m_qi_max_instances) {
                return false;
            }
            get_stat(q)->update_max_generation(max_generation);
            fingerprint * f = m_context.add_fingerprint(q, q->get_id(), num_bindings, bindings, def);
            if (f) {
                if (has_trace_stream()) {
                    std::ostream & out = trace_stream();

                    // In the term produced by the quantifier instantiation the root of the equivalence class of the terms bound to the quantified variables
                    // is used. We need to make sure that all of these equalities appear in the log.
                    for (unsigned i = 0; i < num_bindings; ++i) {
                        log_justification_to_root(out, bindings[i]);
                    }

                    for (auto n : used_enodes) {
                        enode *orig = std::get<0>(n);
                        enode *substituted = std::get<1>(n);
                        if (orig != nullptr) {
                            log_justification_to_root(out, orig);
                            log_justification_to_root(out, substituted);
                        }
                    }

                    // At this point all relevant equalities for the match are logged.
                    out << "[new-match] " << static_cast<void*>(f) << " #" << q->get_id() << " #" << pat->get_id();
                    for (unsigned i = 0; i < num_bindings; i++) {
                        // I don't want to use mk_pp because it creates expressions for pretty printing.
                        // This nasty side-effect may change the behavior of Z3.
                        out << " #" << bindings[i]->get_owner_id();
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
                m_qi_queue.insert(f, pat, max_generation, min_top_generation, max_top_generation); // TODO
                m_num_instances++;
            }
            TRACE("quantifier",
                  tout << mk_pp(q, m()) << " ";
                  for (unsigned i = 0; i < num_bindings; ++i) {
                      tout << mk_pp(bindings[i]->get_owner(), m()) << " ";
                  }
                  tout << "\n";
                  tout << "inserted: " << (f != 0) << "\n";
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
            TRACE("smt_params", m_params.display(tout); );
        }

        void assign_eh(quantifier * q) {
            m_plugin->assign_eh(q);
        }

        void add_eq_eh(enode * n1, enode * n2) {
            m_plugin->add_eq_eh(n1, n2);
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
            return m_context.is_relevant(q) && m_context.get_assignment(q) == l_true; // && !m().is_rec_fun_def(q);
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
                final_check_status result  = m_qi_queue.final_check_eh() ? FC_DONE : FC_CONTINUE;
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
    }

    quantifier_manager::~quantifier_manager() {
        dealloc(m_imp);
    }

    context & quantifier_manager::get_context() const {
        return m_imp->m_context;
    }

    void quantifier_manager::set_plugin(quantifier_manager_plugin * plugin) {
        m_imp->m_plugin = plugin;
        plugin->set_manager(*this);
    }

    void quantifier_manager::add(quantifier * q, unsigned generation) {
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

    quantifier_stat * quantifier_manager::get_stat(quantifier * q) const {
        return m_imp->get_stat(q);
    }

    unsigned quantifier_manager::get_generation(quantifier * q) const {
        return m_imp->get_generation(q);
    }

    bool quantifier_manager::add_instance(quantifier * q, app * pat,
                                          unsigned num_bindings,
                                          enode * const * bindings,
                                          expr* def,
                                          unsigned max_generation,
                                          unsigned min_top_generation,
                                          unsigned max_top_generation,
                                          vector<std::tuple<enode *, enode *>> & used_enodes) {
        return m_imp->add_instance(q, pat, num_bindings, bindings, def, max_generation, min_top_generation, max_generation, used_enodes);
    }

    bool quantifier_manager::add_instance(quantifier * q, unsigned num_bindings, enode * const * bindings, expr* def, unsigned generation) {
        vector<std::tuple<enode *, enode *>> tmp;
        return add_instance(q, nullptr, num_bindings, bindings, def, generation, generation, generation, tmp);
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
        m_imp->push();
    }

    void quantifier_manager::pop(unsigned num_scopes) {
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

    void quantifier_manager::collect_statistics(::statistics & st) const {
        m_imp->m_qi_queue.collect_statistics(st);
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
        unsigned                    m_new_enode_qhead;
        unsigned                    m_lazy_matching_idx;
        bool                        m_active;
    public:
        default_qm_plugin():
            m_qm(nullptr),
            m_context(nullptr),
            m_new_enode_qhead(0),
            m_lazy_matching_idx(0),
            m_active(false) {
        }

        ~default_qm_plugin() override {
        }

        void set_manager(quantifier_manager & qm) override {
            SASSERT(m_qm == 0);
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
        }

        quantifier_manager_plugin * mk_fresh() override { return alloc(default_qm_plugin); }

        bool model_based() const override { return m_fparams->m_mbqi; }

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
            if (m_fparams->m_mbqi && mbqi_enabled(q)) {
                m_active = true;
                m_model_finder->register_quantifier(q);
            }
        }

        void del(quantifier * q) override { }

        void push() override {
            m_mam->push_scope();
            m_lazy_mam->push_scope();
            if (m_fparams->m_mbqi) {
                m_model_finder->push_scope();
            }
        }

        void pop(unsigned num_scopes) override {
            m_mam->pop_scope(num_scopes);
            m_lazy_mam->pop_scope(num_scopes);
            if (m_fparams->m_mbqi) {
                m_model_finder->pop_scope(num_scopes);
            }
        }

        void init_search_eh() override {
            m_lazy_matching_idx = 0;
            if (m_fparams->m_mbqi) {
                m_model_finder->init_search_eh();
                m_model_checker->init_search_eh();
            }
        }

        void assign_eh(quantifier * q) override {
            m_active = true;
            ast_manager& m = m_context->get_manager();
            if (!m_fparams->m_ematching) {
                return;
            }
            if (false && m.is_rec_fun_def(q) && mbqi_enabled(q)) {
                return;
            }
            bool has_unary_pattern = false;
            unsigned num_patterns = q->get_num_patterns();
            for (unsigned i = 0; i < num_patterns; i++) {
                app * mp = to_app(q->get_pattern(i));
                if (mp->get_num_args() == 1) {
                    has_unary_pattern = true;
                    break;
                }
            }
            unsigned num_eager_multi_patterns = m_fparams->m_qi_max_eager_multipatterns;
            if (!has_unary_pattern)
                num_eager_multi_patterns++;
            for (unsigned i = 0, j = 0; i < num_patterns; i++) {
                app * mp = to_app(q->get_pattern(i));
                SASSERT(m.is_pattern(mp));
                bool unary = (mp->get_num_args() == 1);
                if (m.is_rec_fun_def(q) && i > 0) {
                    // add only the first pattern
                    TRACE("quantifier", tout << "skip recursive function body " << mk_ismt2_pp(mp, m) << "\n";);
                }
                else if (!unary && j >= num_eager_multi_patterns) {
                    TRACE("quantifier", tout << "delaying (too many multipatterns):\n" << mk_ismt2_pp(mp, m) << "\n"
                          << "j: " << j << " unary: " << unary << " m_params.m_qi_max_eager_multipatterns: " << m_fparams->m_qi_max_eager_multipatterns
                          << " num_eager_multi_patterns: " << num_eager_multi_patterns << "\n";);
                    m_lazy_mam->add_pattern(q, mp);
                }
                else {
                    TRACE("quantifier", tout << "adding:\n" << mk_ismt2_pp(mp, m) << "\n";);
                    m_mam->add_pattern(q, mp);
                }
                if (!unary)
                    j++;
            }
        }

        bool use_ematching() const {
            return m_fparams->m_ematching && !m_qm->empty();
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
            return m_mam->has_work();
        }

        void restart_eh() override {
            if (m_fparams->m_mbqi) {
                m_model_finder->restart_eh();
                m_model_checker->restart_eh();
            }
            TRACE("mam_stats", m_mam->display(tout););
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
            m_mam->match();
            if (!m_context->relevancy() && use_ematching()) {
                ptr_vector<enode>::const_iterator it  = m_context->begin_enodes();
                ptr_vector<enode>::const_iterator end = m_context->end_enodes();
                unsigned sz = static_cast<unsigned>(end - it);
                if (sz > m_new_enode_qhead) {
                    m_context->push_trail(value_trail<context, unsigned>(m_new_enode_qhead));
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
            if (use_ematching()) {
                if (m_lazy_matching_idx < m_fparams->m_qi_max_lazy_multipattern_matching) {
                    m_lazy_mam->rematch();
                    m_context->push_trail(value_trail<context, unsigned>(m_lazy_matching_idx));
                    m_lazy_matching_idx++;
                }
            }
            return FC_DONE;
        }

    };

    quantifier_manager_plugin * mk_default_plugin() {
        return alloc(default_qm_plugin);
    }

};
