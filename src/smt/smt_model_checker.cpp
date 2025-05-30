/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_checker.cpp

Abstract:

    Model checker

Author:

    Leonardo de Moura (leonardo) 2010-12-03.

Revision History:

- to support lambdas/array models:
  binding sk -> (as-array k!0)
  then include definition for k!0 as part of binding.
  Binding instance can be a pointer into m_pinned expressions.

--*/

#include "ast/normal_forms/pull_quant.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/special_relations_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_context.h"
#include "smt/smt_model_finder.h"
#include "model/model_pp.h"
#include <tuple>

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
        m_fresh_exprs(m),
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
        SASSERT(m_qm == nullptr);
        SASSERT(m_context == nullptr);
        m_qm = &qm;
        m_context = &(m_qm->get_context());
    }

    /**
       \brief Return a term in the context that evaluates to val.
    */
    expr * model_checker::get_term_from_ctx(expr * val) {
        init_value2expr();
        expr * t = nullptr;
        m_value2expr.find(val, t);
        return t;
    }

    expr * model_checker::get_type_compatible_term(expr * val) {
        app* fresh_term;
        if (is_app(val) && to_app(val)->get_num_args() > 0) {
            ptr_buffer<expr> args;
            for (expr* arg : *to_app(val)) 
                args.push_back(get_type_compatible_term(arg));
            fresh_term = m.mk_app(to_app(val)->get_decl(), args.size(), args.data());
        }
        else {
            expr * sk_term = get_term_from_ctx(val);
            if (sk_term != nullptr) 
                return sk_term;

            for (expr* f : m_fresh_exprs) 
                if (f->get_sort() == val->get_sort()) 
                    return f;
            fresh_term = m.mk_fresh_const("sk", val->get_sort());
        }
        m_fresh_exprs.push_back(fresh_term);
        m_context->ensure_internalized(fresh_term);
        return fresh_term;
    }

    void model_checker::init_value2expr() {
        
        if (m_value2expr.empty()) {
            // populate m_value2expr
            for (auto const& kv : *m_root2value) {
                enode * n   = kv.m_key;
                expr  * val = kv.m_value;
                n = n->get_eq_enode_with_min_gen();
                expr* e = n->get_expr();
                if (!m.is_value(e))
                    m_value2expr.insert(val, e);
            }
        }
    }

    expr_ref model_checker::replace_value_from_ctx(expr * e) {
        init_value2expr();
        struct beta_reducer_cfg : default_rewriter_cfg {
            model_checker& mc;
            beta_reducer_cfg(model_checker& mc):mc(mc) {}
            bool get_subst(expr * e, expr* & t, proof *& pr) {
                t = nullptr; pr = nullptr;
                mc.m_value2expr.find(e, t);
                return t != nullptr;
            }
        };
        struct beta_reducer : public rewriter_tpl<beta_reducer_cfg> {
            beta_reducer_cfg m_cfg;
            beta_reducer(model_checker& m):
                rewriter_tpl<beta_reducer_cfg>(m.m, false, m_cfg), m_cfg(m) {}
        };
        beta_reducer br(*this);
        expr_ref result(m);
        br(e, result);
        return result;
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
        expr_ref fml(m.mk_or(eqs.size(), eqs.data()), m);
        m_aux_context->assert_expr(fml);
    }

    /**
       \brief Assert the negation of q after applying the interpretation in m_curr_model to the uninterpreted symbols in q.

       The variables are replaced by skolem constants. These constants are stored in sks.
    */

    bool model_checker::assert_neg_q_m(quantifier * q, expr_ref_vector & sks) {
        expr_ref tmp(m);
        
        TRACE(model_checker, tout << "curr_model:\n"; model_pp(tout, *m_curr_model););

        if (!m_curr_model->eval(q->get_expr(), tmp, true)) {
            return false;
        }
        TRACE(model_checker, tout << "q after applying interpretation:\n" << mk_ismt2_pp(tmp, m) << "\n";);
        ptr_buffer<expr> subst_args;
        unsigned num_decls = q->get_num_decls();
        subst_args.resize(num_decls, nullptr);
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

        var_subst s(m);
        expr_ref sk_body = s(tmp, subst_args.size(), subst_args.data());
        expr_ref r(m);
        r = m.mk_not(sk_body);
        TRACE(model_checker, tout << "mk_neg_q_m:\n" << mk_ismt2_pp(r, m) << "\n";);
        m_aux_context->assert_expr(r);
        return true;
    }

    bool model_checker::add_instance(quantifier * q, model * cex, expr_ref_vector & sks, bool use_inv) {
        if (cex == nullptr || sks.empty()) {
            TRACE(model_checker, tout << "no model is available\n";);
            return false;
        }
        array_util autil(m);
        unsigned num_decls = q->get_num_decls();
        // Remark: sks were created for the flat version of q.
        SASSERT(sks.size() >= num_decls);
        expr_ref_vector bindings(m), defs(m);
        expr_ref def(m);
        bindings.resize(num_decls);
        unsigned max_generation = 0;
        for (unsigned i = 0; i < num_decls; i++) {
            expr * sk = sks.get(num_decls - i - 1);
            func_decl * sk_d = to_app(sk)->get_decl();
            expr_ref sk_value(cex->get_some_const_interp(sk_d), m);
            if (!sk_value) {
                TRACE(model_checker, tout << "Could not get value for " << sk_d->get_name() << "\n";);
                return false; // get_some_value failed... giving up
            }
            TRACE(model_checker, tout << "Got some value " << sk_value << "\n";);

            if (use_inv) {
                unsigned sk_term_gen = 0;
                expr * sk_term = m_model_finder.get_inv(q, i, sk_value, sk_term_gen);
                if (sk_term != nullptr) {
                    TRACE(model_checker, tout << "Found inverse " << mk_pp(sk_term, m) << "\n";);
                    SASSERT(!m.is_model_value(sk_term));
                    max_generation = std::max(sk_term_gen, max_generation);
                    sk_value = sk_term;
                }
                else {
                    TRACE(model_checker, tout << "no inverse value for " << sk_value << "\n";);
                    return false;
                }
            }
            else {
                expr * sk_term = get_term_from_ctx(sk_value);
                func_decl * f = nullptr;
                if (sk_term != nullptr) {
                    TRACE(model_checker, tout << "sk term " << mk_pp(sk_term, m) << "\n");
                    sk_value = sk_term;
                }
                // last ditch: am I an array?
                else if (false && autil.is_as_array(sk_value, f) && cex->get_func_interp(f) && cex->get_func_interp(f)->get_array_interp(f)) {
                    sk_value = cex->get_func_interp(f)->get_array_interp(f);
                }

            }
            if (contains_model_value(sk_value)) {
                TRACE(model_checker, tout << "type compatible term " << mk_pp(sk_value, m) << "\n");
                sk_value = get_type_compatible_term(sk_value);
            }
            func_decl * f = nullptr;
            if (autil.is_as_array(sk_value, f) && cex->get_func_interp(f) && cex->get_func_interp(f)->get_interp()) {
                expr_ref body(cex->get_func_interp(f)->get_interp(), m);
                if (contains_model_value(body))
                    return false;                    
                ptr_vector<sort> sorts(f->get_arity(), f->get_domain());
                svector<symbol> names;
                for (unsigned i = 0; i < f->get_arity(); ++i) 
                    names.push_back(symbol(i));
                defined_names dn(m);
                body = replace_value_from_ctx(body);
                body = m.mk_lambda(sorts.size(), sorts.data(), names.data(), body);
                // sk_value = m.mk_fresh_const(0, m.get_sort(sk_value));  // get rid of as-array
                body = dn.mk_definition(body, to_app(sk_value));
                defs.push_back(body);
            }
            bindings.set(num_decls - i - 1, sk_value);
        }

        TRACE(model_checker, tout << q->get_qid() << " found (use_inv: " << use_inv << ") new instance: " << bindings << "\ndefs:\n" << defs << "\n";);
        if (!defs.empty()) def = mk_and(defs);
        max_generation = std::max(m_qm->get_generation(q), max_generation);
        add_instance(q, bindings, max_generation, def.get());
        return true;
    }

    void model_checker::add_instance(quantifier* q, expr_ref_vector const& bindings, unsigned max_generation, expr* def) {
        SASSERT(q->get_num_decls() == bindings.size());
        unsigned offset = m_pinned_exprs.size();
        m_pinned_exprs.append(bindings);
        m_pinned_exprs.push_back(q);
        m_pinned_exprs.push_back(def);
        m_new_instances.push_back(instance(q, offset, def, max_generation));
    }

    void model_checker::operator()(expr *n) {
        if (m.is_model_value(n) /*|| m_autil.is_as_array(n)*/) {
            throw is_model_value();
        }
    }

    bool model_checker::contains_model_value(expr* n) {
        if (m.is_model_value(n) /*|| m_autil.is_as_array(n)*/) {
            return true;
        }
        if (is_app(n) && to_app(n)->get_num_args() == 0) {
            return false;
        }
        m_visited.reset();
        try {
            for_each_expr(*this, m_visited, n);
        }
        catch (const is_model_value &) {
            return true;
        }
        return false;
    }

    bool model_checker::add_blocking_clause(model * cex, expr_ref_vector & sks) {
        SASSERT(cex != nullptr);
        expr_ref_buffer diseqs(m);
        for (expr * sk : sks) {
            func_decl * sk_d = to_app(sk)->get_decl();
            expr_ref sk_value(cex->get_some_const_interp(sk_d), m);
            if (!sk_value) {
                TRACE(model_checker, tout << "no constant interpretation for " << mk_pp(sk, m) << "\n";);
                return false; // get_some_value failed... aborting add_blocking_clause
            }
            diseqs.push_back(m.mk_not(m.mk_eq(sk, sk_value)));
        }
        expr_ref blocking_clause(m);
        blocking_clause = m.mk_or(diseqs.size(), diseqs.data());
        TRACE(model_checker, tout << "blocking clause:\n" << mk_ismt2_pp(blocking_clause, m) << "\n";);
        m_aux_context->assert_expr(blocking_clause);
        return true;
    }

    struct scoped_ctx_push {
        context* c;
        scoped_ctx_push(context* c): c(c) { c->push(); }
        ~scoped_ctx_push() { 
            try {
                c->pop(1);
            }
            catch (...) {
                ;
            }
        }
    };

    /**
       \brief Return true if q is satisfied by m_curr_model.
    */

    bool model_checker::check(quantifier * q) {
        SASSERT(!m_aux_context->relevancy());
        scoped_ctx_push _push(m_aux_context.get());

        quantifier * flat_q = get_flat_quantifier(q);
        TRACE(model_checker, tout << "model checking:\n" << expr_ref(flat_q->get_expr(), m) << "\n";);
        expr_ref_vector sks(m);

        if (!assert_neg_q_m(flat_q, sks))
            return false;
        TRACE(model_checker, tout << "skolems:\n" << sks << "\n";);

        flet<bool> l(m_aux_context->get_fparams().m_array_fake_support, true);
        lbool r = m_aux_context->check();
        
        TRACE(model_checker, tout << "[complete] model-checker result: " << to_sat_str(r) << "\n";);
        if (r != l_true) {
            return is_safe_for_mbqi(q) && r == l_false; // quantifier is satisfied by m_curr_model
        }

        model_ref complete_cex;
        m_aux_context->get_model(complete_cex);

        // try to find new instances using instantiation sets.
        m_model_finder.restrict_sks_to_inst_set(m_aux_context.get(), q, sks);

        unsigned num_new_instances = 0;

        while (true) {
            flet<bool> l(m_aux_context->get_fparams().m_array_fake_support, true);
            lbool r = m_aux_context->check();
            TRACE(model_checker, tout << "[restricted] model-checker (" << (num_new_instances+1) << ") result: " << to_sat_str(r) << "\n";);
            if (r != l_true)
                break;
            model_ref cex;
            m_aux_context->get_model(cex);
            
            if (!add_instance(q, cex.get(), sks, true)) {
                break;
            }
            num_new_instances++;
            if (num_new_instances >= m_max_cexs || !add_blocking_clause(cex.get(), sks)) {
                TRACE(model_checker, tout << "Add blocking clause failed new-instances: " << num_new_instances << " max-cex: " << m_max_cexs << "\n";);
                // add_blocking_clause failed... stop the search for new counter-examples...
                break;
            }
        }

        if (num_new_instances == 0) {
            // failed to create instances when restricting to inst sets... then use result of the complete model check
            TRACE(model_checker, tout << "using complete_cex result:\n"; model_pp(tout, *complete_cex););
            add_instance(q, complete_cex.get(), sks, false);
        }

        return false;
    }

    bool model_checker::is_safe_for_mbqi(quantifier * q) const {
        special_relations_util sp(m);
        if (!sp.has_special_relation())
            return true;
        ast_fast_mark1 visited;
        struct proc {
            special_relations_util& sp;
            bool found = false;
            proc(special_relations_util& sp):sp(sp) {}
            void operator()(app* f) {
                found |= sp.is_special_relation(f);
            }
            void operator()(expr* e) {}
        };
        proc p(sp);
        quick_for_each_expr(p, visited, q);
        return !p.found;
    }


    void model_checker::init_aux_context() {
        if (!m_fparams) {
            m_fparams = alloc(smt_params, m_context->get_fparams());
            m_fparams->m_relevancy_lvl = 0; // no relevancy since the model checking problems are quantifier free
            m_fparams->m_case_split_strategy = CS_ACTIVITY; // avoid warning messages about smt.case_split >= 3.
            m_fparams->m_axioms2files = false;
            m_fparams->m_lemmas2console = false;
            m_fparams->m_proof_log = symbol::null;
        }
        if (!m_aux_context) {
            symbol logic;
            params_ref p;
            p.set_bool("solver.axioms2files", false);
            p.set_bool("solver.lemmas2console", false);
            p.set_sym("solver.proof.log", symbol::null);
            m_aux_context = m_context->mk_fresh(&logic, m_fparams.get(), p);
        }
    }

    bool model_checker::check(proto_model * md, obj_map<enode, app *> const & root2value) {
        SASSERT(md != nullptr);

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

        TRACE(model_checker, tout << "MODEL_CHECKER INVOKED\n";
        tout << "model:\n"; model_pp(tout, *m_curr_model););

        for (quantifier* q : *m_qm)
            if (m.is_lambda_def(q)) {
                md->add_lambda_defs();
                break;
            }
	
        md->compress();

        TRACE(model_checker, tout << "MODEL_CHECKER INVOKED\n";
              tout << "model:\n"; model_pp(tout, *m_curr_model););
        if (m_params.m_mbqi_trace) {
            verbose_stream() << "(smt.mbqi \"started\")\n";
        }

        init_aux_context();

        bool found_relevant = false;
        unsigned num_failures = 0;

        check_quantifiers(found_relevant, num_failures);

        if (found_relevant)
            m_iteration_idx++;

        TRACE(model_checker, tout << "model after check:\n"; model_pp(tout, *md););
        TRACE(model_checker, tout << "model checker result: " << (num_failures == 0) << "\n";);
        m_max_cexs += m_params.m_mbqi_max_cexs;

        if (num_failures == 0 && !m_context->validate_model()) {
            num_failures = 1;
            // this time force expanding recursive function definitions
            // that are not forced true in the current model.
            check_quantifiers(found_relevant, num_failures);
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

    //
    // (repeated from defined_names.cpp)
    // NB. The pattern for lambdas is incomplete.
    // consider store(a, i, v) == \lambda j . if i = j then v else a[j]
    // the instantiation rules for store(a, i, v) are:
    //     sotre(a, i, v)[j] = if i = j then v else a[j] with patterns {a[j], store(a, i, v)} { store(a, i, v)[j] }
    // The first pattern is not included.
    // TBD use a model-based scheme for extracting instantiations instead of
    // using multi-patterns.
    //

    void model_checker::check_quantifiers(bool& found_relevant, unsigned& num_failures) {
        for (quantifier * q : *m_qm) {
            if (!(m_qm->mbqi_enabled(q) &&
                  m_context->is_relevant(q) &&
                  m_context->get_assignment(q) == l_true &&
                  (!m_context->get_fparams().m_ematching || !m.is_lambda_def(q)))) {
                if (!m_qm->mbqi_enabled(q))
                    ++num_failures;
                continue;
            }

            TRACE(model_checker,
                  tout << "Check: " << mk_pp(q, m) << "\n";
                  tout << m_context->get_assignment(q) << "\n";);

            if (m_params.m_mbqi_trace && q->get_qid() != symbol::null) {
                IF_VERBOSE(1, verbose_stream() << "(smt.mbqi :checking " << q->get_qid() << ")\n");
            }
            found_relevant = true;
            if (!check(q)) {
                if (m_params.m_mbqi_trace || get_verbosity_level() >= 5) {
                    IF_VERBOSE(0, verbose_stream() << "(smt.mbqi :failed " << q->get_qid() << ")\n");
                }
                TRACE(model_checker, tout << "checking quantifier " << mk_pp(q, m) << " failed\n";);
                num_failures++;
            }
        }
    }

    void model_checker::init_search_eh() {
        m_max_cexs = m_params.m_mbqi_max_cexs;
        m_iteration_idx = 0;
    }

    void model_checker::restart_eh() {
        IF_VERBOSE(100, if (has_new_instances()) verbose_stream() << "(smt.mbqi \"instantiating new instances...\")\n";);
        assert_new_instances();
        reset_new_instances();
    }

    bool model_checker::has_new_instances() {
        TRACE(model_checker, tout << "instances: " << m_new_instances.size() << "\n";);
        return !m_new_instances.empty();
    }

    void model_checker::reset_new_instances() {
        m_pinned_exprs.reset();
        m_new_instances.reset();
    }

    void model_checker::reset() {
        reset_new_instances();
    }

    void model_checker::assert_new_instances() {
        TRACE(model_checker_bug_detail, tout << "assert_new_instances, inconsistent: " << m_context->inconsistent() << "\n";);
        ptr_buffer<enode> bindings;
        vector<std::tuple<enode *, enode *>> dummy;
        for (instance const& inst : m_new_instances) {
            quantifier * q  = inst.m_q;
            if (m_context->b_internalized(q)) {
                bindings.reset();
                unsigned num_decls = q->get_num_decls();
                unsigned gen       = inst.m_generation;
                unsigned offset    = inst.m_bindings_offset;
                for (unsigned i = 0; i < num_decls; i++) {
                    expr * b = m_pinned_exprs.get(offset + i);
                    if (!m_context->e_internalized(b)) {
                        TRACE(model_checker, tout << "internalizing b:\n" << mk_pp(b, m) << "\n";);
                        m_context->internalize(b, false, gen);
                    }
                    bindings.push_back(m_context->get_enode(b));
                }

                if (inst.m_def) {
                    unsigned n = 1;
                    expr* const* args = &inst.m_def;
                    if (m.is_and(inst.m_def)) {
                        n = to_app(inst.m_def)->get_num_args();
                        args = to_app(inst.m_def)->get_args();
                    }
                    for (unsigned i = 0; i < n; ++i) {
                        proof* pr = nullptr;
                        expr* arg = args[i];
                        if (m.proofs_enabled()) 
                            pr = m.mk_def_intro(arg);
                        m_context->internalize_assertion(arg, pr, gen);
                    }
                }

                TRACE(model_checker_bug_detail, tout << "instantiating... q:\n" << mk_pp(q, m) << "\n";
                      tout << "inconsistent: " << m_context->inconsistent() << "\n";
                      tout << "bindings:\n" << expr_ref_vector(m, num_decls, m_pinned_exprs.data() + offset) << "\n";
                      tout << "def " << mk_pp(inst.m_def, m) << "\n";);
                m_context->add_instance(q, nullptr, num_decls, bindings.data(), inst.m_def, gen, gen, gen, dummy);
                TRACE(model_checker_bug_detail, tout << "after instantiating, inconsistent: " << m_context->inconsistent() << "\n";);
            }
        }
    }

};
