/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_checker.cpp

Abstract:

    Model checker

Author:

    Leonardo de Moura (leonardo) 2010-12-03.

Revision History:

--*/

#include "ast/normal_forms/pull_quant.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_context.h"
#include "smt/smt_model_finder.h"
#include "model/model_pp.h"

namespace smt {

    model_checker::model_checker(ast_manager & m, qi_params const & p, model_finder & mf):
        m(m),
        m_params(p),
        m_autil(m),
        m_qm(nullptr),
        m_context(nullptr),
        m_root2value(nullptr),
        m_model_finder(mf),
        m_max_cexs(1),
        m_iteration_idx(0),
        m_curr_model(nullptr),
        m_pinned_exprs(m) {
    }

    model_checker::~model_checker() {
        m_aux_context = nullptr; // delete aux context before fparams
        m_fparams = nullptr;
    }

    quantifier * model_checker::get_flat_quantifier(quantifier * q) {
        return m_model_finder.get_flat_quantifier(q);
    }

    void model_checker::set_qm(quantifier_manager & qm) {
        SASSERT(m_qm == 0);
        SASSERT(m_context == 0);
        m_qm = &qm;
        m_context = &(m_qm->get_context());
    }

    /**
       \brief Return a term in the context that evaluates to val.
    */
    expr * model_checker::get_term_from_ctx(expr * val) {
        if (m_value2expr.empty()) {
            // populate m_value2expr
            for (auto const& kv : *m_root2value) {
                enode * n   = kv.m_key;
                expr  * val = kv.m_value;
                n = n->get_eq_enode_with_min_gen();
                m_value2expr.insert(val, n->get_owner());
            }
        }
        expr * t = nullptr;
        m_value2expr.find(val, t);
        return t;
    }

    /**
       \brief Assert in m_aux_context, the constraint

         sk = e_1 OR ... OR sk = e_n

         where {e_1, ..., e_n} is the universe.
     */
    void model_checker::restrict_to_universe(expr * sk, obj_hashtable<expr> const & universe) {
        SASSERT(!universe.empty());
        ptr_buffer<expr> eqs;
        for (expr * e : universe) {
            eqs.push_back(m.mk_eq(sk, e));
        }
        expr_ref fml(m.mk_or(eqs.size(), eqs.c_ptr()), m);
        m_aux_context->assert_expr(fml);
    }

#define PP_DEPTH 8

    /**
       \brief Assert the negation of q after applying the interpretation in m_curr_model to the uninterpreted symbols in q.

       The variables are replaced by skolem constants. These constants are stored in sks.
    */

    void model_checker::assert_neg_q_m(quantifier * q, expr_ref_vector & sks) {
        expr_ref tmp(m);
        if (!m_curr_model->eval(q->get_expr(), tmp, true)) {
            return;
        }
        TRACE("model_checker", tout << "q after applying interpretation:\n" << mk_ismt2_pp(tmp, m) << "\n";);
        ptr_buffer<expr> subst_args;
        unsigned num_decls = q->get_num_decls();
        subst_args.resize(num_decls, 0);
        sks.resize(num_decls, nullptr);
        for (unsigned i = 0; i < num_decls; i++) {
            sort * s  = q->get_decl_sort(num_decls - i - 1);
            expr * sk = m.mk_fresh_const(nullptr, s);
            sks[num_decls - i - 1]        = sk;
            subst_args[num_decls - i - 1] = sk;
            if (m_curr_model->is_finite(s)) {
                restrict_to_universe(sk, m_curr_model->get_known_universe(s));
            }
        }

        expr_ref sk_body(m);
        var_subst s(m);
        s(tmp, subst_args.size(), subst_args.c_ptr(), sk_body);
        expr_ref r(m);
        r = m.mk_not(sk_body);
        TRACE("model_checker", tout << "mk_neg_q_m:\n" << mk_ismt2_pp(r, m) << "\n";);
        m_aux_context->assert_expr(r);
    }

    bool model_checker::add_instance(quantifier * q, model * cex, expr_ref_vector & sks, bool use_inv) {
        if (cex == nullptr) {
            TRACE("model_checker", tout << "no model is available\n";);
            return false;
        }
        unsigned num_decls = q->get_num_decls();
        // Remark: sks were created for the flat version of q.
        SASSERT(sks.size() >= num_decls);
        expr_ref_vector bindings(m);
        bindings.resize(num_decls);
        unsigned max_generation = 0;
        for (unsigned i = 0; i < num_decls; i++) {
            expr * sk = sks.get(num_decls - i - 1);
            func_decl * sk_d = to_app(sk)->get_decl();
            expr_ref sk_value(m);
            sk_value  = cex->get_const_interp(sk_d);
            if (sk_value == 0) {
                sk_value = cex->get_some_value(sk_d->get_range());
                if (sk_value == 0) {
                    TRACE("model_checker", tout << "Could not get value for " << sk_d->get_name() << "\n";);
                    return false; // get_some_value failed... giving up
                }
                TRACE("model_checker", tout << "Got some value " << sk_value << "\n";);
            }
            if (use_inv) {
                unsigned sk_term_gen;
                expr * sk_term = m_model_finder.get_inv(q, i, sk_value, sk_term_gen);
                if (sk_term != nullptr) {
                    TRACE("model_checker", tout << "Found inverse " << mk_pp(sk_term, m) << "\n";);
                    SASSERT(!m.is_model_value(sk_term));
                    if (sk_term_gen > max_generation)
                        max_generation = sk_term_gen;
                    sk_value = sk_term;
                }
                else {
                    TRACE("model_checker", tout << "no inverse value for " << sk_value << "\n";);
                    return false;
                }
            }
            else {
                expr * sk_term = get_term_from_ctx(sk_value);
                if (sk_term != nullptr) {
                    sk_value = sk_term;
                }
            }
            if (contains_model_value(sk_value)) {
                TRACE("model_checker", tout << "value is private to model: " << sk_value << "\n";);
                return false;
            }
            bindings.set(num_decls - i - 1, sk_value);
        }

        TRACE("model_checker", tout << q->get_qid() << " found (use_inv: " << use_inv << ") new instance: ";
              for (unsigned i = 0; i < num_decls; i++) {
                  tout << mk_ismt2_pp(bindings[i].get(), m) << " ";
              }
              tout << "\n";);

        max_generation = std::max(m_qm->get_generation(q), max_generation);
        add_instance(q, bindings, max_generation);
        return true;
    }

    void model_checker::add_instance(quantifier* q, expr_ref_vector const& bindings, unsigned max_generation) {
        SASSERT(q->get_num_decls() == bindings.size());
        for (expr* b : bindings) 
            m_pinned_exprs.push_back(b);
        m_pinned_exprs.push_back(q);

        void * mem = m_new_instances_region.allocate(instance::get_obj_size(q->get_num_decls()));
        instance * new_inst = new (mem) instance(q, bindings.c_ptr(), max_generation);
        m_new_instances.push_back(new_inst);
    }

    void model_checker::operator()(expr *n) {
        if (m.is_model_value(n) || m_autil.is_as_array(n)) {
            throw is_model_value();
        }
    }

    bool model_checker::contains_model_value(expr* n) {
        if (m.is_model_value(n) || m_autil.is_as_array(n)) {
            return true;
        }
        if (is_app(n) && to_app(n)->get_num_args() == 0) {
            return false;
        }
        m_visited.reset();
        try {
            for_each_expr(*this, m_visited, n);
        }
        catch (is_model_value) {
            return true;
        }
        return false;
    }


    bool model_checker::add_blocking_clause(model * cex, expr_ref_vector & sks) {
        SASSERT(cex != 0);
        expr_ref_buffer diseqs(m);
        for (expr * sk : sks) {
            func_decl * sk_d = to_app(sk)->get_decl();
            expr_ref sk_value(m);
            sk_value  = cex->get_const_interp(sk_d);
            if (sk_value == 0) {
                sk_value = cex->get_some_value(sk_d->get_range());
                if (sk_value == 0)
                    return false; // get_some_value failed... aborting add_blocking_clause
            }
            diseqs.push_back(m.mk_not(m.mk_eq(sk, sk_value)));
        }
        expr_ref blocking_clause(m);
        blocking_clause = m.mk_or(diseqs.size(), diseqs.c_ptr());
        TRACE("model_checker", tout << "blocking clause:\n" << mk_ismt2_pp(blocking_clause, m) << "\n";);
        m_aux_context->assert_expr(blocking_clause);
        return true;
    }

    /**
       \brief Return true if q is satisfied by m_curr_model.
    */
    bool model_checker::check(quantifier * q) {
        SASSERT(!m_aux_context->relevancy());
        m_aux_context->push();

        quantifier * flat_q = get_flat_quantifier(q);
        TRACE("model_checker", tout << "model checking:\n" << mk_ismt2_pp(q->get_expr(), m) << "\n" <<
              mk_ismt2_pp(flat_q->get_expr(), m) << "\n";);
        expr_ref_vector sks(m);

        assert_neg_q_m(flat_q, sks);
        TRACE("model_checker", tout << "skolems:\n";
              for (expr* sk : sks) {
                  tout << mk_ismt2_pp(sk, m) << " " << mk_pp(m.get_sort(sk), m) << "\n";
              });

        lbool r = m_aux_context->check();
        TRACE("model_checker", tout << "[complete] model-checker result: " << to_sat_str(r) << "\n";);
        if (r != l_true) {
            m_aux_context->pop(1);
            return r == l_false; // quantifier is satisfied by m_curr_model
        }

        model_ref complete_cex;
        m_aux_context->get_model(complete_cex);

        // try to find new instances using instantiation sets.
        m_model_finder.restrict_sks_to_inst_set(m_aux_context.get(), q, sks);

        unsigned num_new_instances = 0;

        while (true) {
            lbool r = m_aux_context->check();
            TRACE("model_checker", tout << "[restricted] model-checker (" << (num_new_instances+1) << ") result: " << to_sat_str(r) << "\n";);
            if (r != l_true)
                break;
            model_ref cex;
            m_aux_context->get_model(cex);
            if (!add_instance(q, cex.get(), sks, true)) {
                break;
            }
            num_new_instances++;
            if (num_new_instances >= m_max_cexs || !add_blocking_clause(cex.get(), sks)) {
                TRACE("model_checker", tout << "Add blocking clause failed new-instances: " << num_new_instances << " max-cex: " << m_max_cexs << "\n";);
                // add_blocking_clause failed... stop the search for new counter-examples...
                break;
            }
        }

        if (num_new_instances == 0) {
            // failed to create instances when restricting to inst sets... then use result of the complete model check
            TRACE("model_checker", tout << "using complete_cex result:\n"; model_pp(tout, *complete_cex););
            add_instance(q, complete_cex.get(), sks, false);
        }

        m_aux_context->pop(1);
        return false;
    }

    bool model_checker::check_rec_fun(quantifier* q, bool strict_rec_fun) {
        TRACE("model_checker", tout << mk_pp(q, m) << "\n";);
        SASSERT(q->get_num_patterns() == 2); // first pattern is the function, second is the body.
        expr* fn = to_app(q->get_pattern(0))->get_arg(0);
        SASSERT(is_app(fn));
        func_decl* f = to_app(fn)->get_decl();
        enode_vector::const_iterator it  = m_context->begin_enodes_of(f);
        enode_vector::const_iterator end = m_context->end_enodes_of(f);

        bool is_undef = false;
        expr_ref_vector args(m);
        unsigned num_decls = q->get_num_decls();
        args.resize(num_decls, nullptr);
        var_subst sub(m);
        expr_ref tmp(m), result(m);
        for (; it != end; ++it) {
            if (m_context->is_relevant(*it)) {
                app* e = (*it)->get_owner();
                SASSERT(e->get_num_args() == num_decls);
                for (unsigned i = 0; i < num_decls; ++i) {
                    args[i] = e->get_arg(i);
                }
                sub(q->get_expr(), num_decls, args.c_ptr(), tmp);
                m_curr_model->eval(tmp, result, true);
                if (strict_rec_fun ? !m.is_true(result) : m.is_false(result)) {
                    add_instance(q, args, 0);
                    return false;
                }
                TRACE("model_checker", tout << tmp << "\nevaluates to:\n" << result << "\n";);
                // if (!m.is_true(result)) is_undef = true;
            }
        }
        return !is_undef;
    }

    void model_checker::init_aux_context() {
        if (!m_fparams) {
            m_fparams = alloc(smt_params, m_context->get_fparams());
            m_fparams->m_relevancy_lvl = 0; // no relevancy since the model checking problems are quantifier free
            m_fparams->m_case_split_strategy = CS_ACTIVITY; // avoid warning messages about smt.case_split >= 3.
        }
        if (!m_aux_context) {
            symbol logic;
            m_aux_context = m_context->mk_fresh(&logic, m_fparams.get());
        }
    }

    bool model_checker::check(proto_model * md, obj_map<enode, app *> const & root2value) {
        SASSERT(md != 0);

        m_root2value = &root2value;

        if (m_qm->num_quantifiers() == 0)
            return true;

        if (m_iteration_idx >= m_params.m_mbqi_max_iterations) {
            IF_VERBOSE(1, verbose_stream() << "(smt.mbqi \"max instantiations " << m_iteration_idx << " reached\")\n";);
            m_context->set_reason_unknown("max mbqi instantiations reached");
            return false;
        }

        m_curr_model = md;
        m_value2expr.reset();

        md->compress();

        TRACE("model_checker", tout << "MODEL_CHECKER INVOKED\n";
              tout << "model:\n"; model_pp(tout, *m_curr_model););
        if (m_params.m_mbqi_trace) {
            verbose_stream() << "(smt.mbqi \"started\")\n";
        }

        init_aux_context();

        bool found_relevant = false;
        unsigned num_failures = 0;

        check_quantifiers(false, found_relevant, num_failures);


        if (found_relevant)
            m_iteration_idx++;

        TRACE("model_checker", tout << "model after check:\n"; model_pp(tout, *md););
        TRACE("model_checker", tout << "model checker result: " << (num_failures == 0) << "\n";);
        m_max_cexs += m_params.m_mbqi_max_cexs;

        if (num_failures == 0 && !m_context->validate_model()) {
            num_failures = 1;
            // this time force expanding recursive function definitions
            // that are not forced true in the current model.
            check_quantifiers(true, found_relevant, num_failures);
        }
        if (num_failures == 0)
            m_curr_model->cleanup();
        if (m_params.m_mbqi_trace) {
            if (num_failures == 0)
                verbose_stream() << "(smt.mbqi :succeeded true)\n";
            else
                verbose_stream() << "(smt.mbqi :num-failures " << num_failures << ")\n";
        }
        return num_failures == 0;
    }

    void model_checker::check_quantifiers(bool strict_rec_fun, bool& found_relevant, unsigned& num_failures) {
        ptr_vector<quantifier>::const_iterator it  = m_qm->begin_quantifiers();
        ptr_vector<quantifier>::const_iterator end = m_qm->end_quantifiers();
        for (; it != end; ++it) {
            quantifier * q = *it;
        if(!m_qm->mbqi_enabled(q)) continue;
            TRACE("model_checker",
                  tout << "Check: " << mk_pp(q, m) << "\n";
                  tout << m_context->get_assignment(q) << "\n";);

            if (m_context->is_relevant(q) && m_context->get_assignment(q) == l_true) {
                if (m_params.m_mbqi_trace && q->get_qid() != symbol::null) {
                    verbose_stream() << "(smt.mbqi :checking " << q->get_qid() << ")\n";
                }
                found_relevant = true;
                if (m.is_rec_fun_def(q)) {
                    if (!check_rec_fun(q, strict_rec_fun)) {
                        TRACE("model_checker", tout << "checking recursive function failed\n";);
                        num_failures++;
                    }
                }
                else if (!check(q)) {
                    if (m_params.m_mbqi_trace || get_verbosity_level() >= 5) {
                        verbose_stream() << "(smt.mbqi :failed " << q->get_qid() << ")\n";
                    }
                    TRACE("model_checker", tout << "checking quantifier " << mk_pp(q, m) << " failed\n";);
                    num_failures++;
                }
            }
        }
    }

    void model_checker::init_search_eh() {
        m_max_cexs = m_params.m_mbqi_max_cexs;
        m_iteration_idx = 0;
    }

    void model_checker::restart_eh() {
        IF_VERBOSE(100, verbose_stream() << "(smt.mbqi \"instantiating new instances...\")\n";);
        assert_new_instances();
        reset_new_instances();
    }

    bool model_checker::has_new_instances() {
        TRACE("model_checker", tout << "instances: " << m_new_instances.size() << "\n";);
        return !m_new_instances.empty();
    }

    void model_checker::reset_new_instances() {
        m_pinned_exprs.reset();
        m_new_instances.reset();
        m_new_instances_region.reset();
    }

    void model_checker::reset() {
        reset_new_instances();
    }

    void model_checker::assert_new_instances() {
        TRACE("model_checker_bug_detail", tout << "assert_new_instances, inconsistent: " << m_context->inconsistent() << "\n";);
        ptr_buffer<enode> bindings;
        ptr_vector<enode> dummy;
        for (instance* inst : m_new_instances) {
            quantifier * q  = inst->m_q;
            if (m_context->b_internalized(q)) {
                bindings.reset();
                unsigned num_decls = q->get_num_decls();
                unsigned gen       = inst->m_generation;
                for (unsigned i = 0; i < num_decls; i++) {
                    expr * b = inst->m_bindings[i];
                    if (!m_context->e_internalized(b)) {
                        TRACE("model_checker_bug_detail", tout << "internalizing b:\n" << mk_pp(b, m) << "\n";);
                        m_context->internalize(b, false, gen);
                    }
                    bindings.push_back(m_context->get_enode(b));
                }
                TRACE("model_checker_bug_detail", tout << "instantiating... q:\n" << mk_pp(q, m) << "\n";
                      tout << "inconsistent: " << m_context->inconsistent() << "\n";
                      tout << "bindings:\n";
                      for (unsigned i = 0; i < num_decls; i++) {
                          expr * b = inst->m_bindings[i];
                          tout << mk_pp(b, m) << "\n";
                      });
                TRACE("model_checker_instance",
                      expr_ref inst_expr(m);
                      instantiate(m, q, inst->m_bindings, inst_expr);
                      tout << "(assert " << mk_ismt2_pp(inst_expr, m) << ")\n";);
                m_context->add_instance(q, nullptr, num_decls, bindings.c_ptr(), gen, gen, gen, dummy);
                TRACE("model_checker_bug_detail", tout << "after instantiating, inconsistent: " << m_context->inconsistent() << "\n";);
            }
        }
    }

};
