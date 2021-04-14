/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_bmc_engine.cpp

Abstract:

    BMC engine for fixedpoint solver.

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-20

Revision History:

--*/

#include "ast/datatype_decl_plugin.h"
#include "ast/dl_decl_plugin.h"
#include "ast/ast_smt_pp.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/scoped_proof.h"
#include "smt/smt_solver.h"
#include "tactic/fd_solver/fd_solver.h"
#include "tactic/tactic.h"
#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/bmc/dl_bmc_engine.h"
#include "muz/transforms/dl_mk_slice.h"
#include "model/model_smt2_pp.h"
#include "muz/transforms/dl_transforms.h"
#include "muz/transforms/dl_mk_rule_inliner.h"
#include "muz/base/fp_params.hpp"


namespace datalog {

    // ---------------------------------------------------------------------------
    // Basic linear BMC based on indexed variables using quantified bit-vector domains.

    class bmc::qlinear {
        bmc&             b;
        ast_manager&     m;
        bv_util          m_bv;
        unsigned         m_bit_width;
    public:
        qlinear(bmc& b): b(b), m(b.m), m_bv(m), m_bit_width(1) {}

        lbool check() {
            setup();
            m_bit_width = 4;
            lbool res = l_false;
            while (res == l_false) {
                b.m_solver->push();
                IF_VERBOSE(1, verbose_stream() << "bit_width: " << m_bit_width << "\n";);
                compile();
                b.checkpoint();
                func_decl_ref q = mk_q_func_decl(b.m_query_pred);
                expr* T = m.mk_const(symbol("T"), mk_index_sort());
                expr_ref fml(m.mk_app(q, T), m);
                b.assert_expr(fml);
                res = b.m_solver->check_sat(0, nullptr);

                if (res == l_true) {
                    res = get_model();
                }
                b.m_solver->pop(1);
                ++m_bit_width;
            }
            return res;
        }
    private:

        sort_ref mk_index_sort() {
            return sort_ref(m_bv.mk_sort(m_bit_width), m);
        }

        var_ref mk_index_var() {
            return var_ref(m.mk_var(0, mk_index_sort()), m);
        }

        void compile() {
            sort_ref index_sort = mk_index_sort();
            var_ref var = mk_index_var();
            sort* index_sorts[1] = { index_sort };
            symbol tick("T");
            rule_set::decl2rules::iterator it  = b.m_rules.begin_grouped_rules();
            rule_set::decl2rules::iterator end = b.m_rules.end_grouped_rules();
            for (; it != end; ++it) {
                func_decl* p = it->m_key;
                rule_vector const& rls = *it->m_value;
                // Assert: forall level . p(T) => body of rule i + equalities for head of rule i
                func_decl_ref pr = mk_q_func_decl(p);
                expr_ref pred = expr_ref(m.mk_app(pr, var.get()), m);
                expr_ref_vector rules(m), sub(m), conjs(m);
                expr_ref trm(m), rule_body(m), rule_i(m);
                for (unsigned i = 0; i < rls.size(); ++i) {
                    sub.reset();
                    conjs.reset();
                    rule& r = *rls[i];
                    rule_i = m.mk_app(mk_q_rule(p, i), var.get());
                    rules.push_back(rule_i);

                    mk_qrule_vars(r, i, sub);

                    // apply substitution to body.
                    var_subst vs(m, false);
                    for (unsigned k = 0; k < p->get_arity(); ++k) {
                        trm = vs(r.get_head()->get_arg(k), sub.size(), sub.data());
                        conjs.push_back(m.mk_eq(trm, mk_q_arg(p, k, true)));
                    }
                    for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                        func_decl* q = r.get_decl(j);
                        for (unsigned k = 0; k < q->get_arity(); ++k) {
                            trm = vs(r.get_tail(j)->get_arg(k), sub.size(), sub.data());
                            conjs.push_back(m.mk_eq(trm, mk_q_arg(q, k, false)));
                        }
                        func_decl_ref qr = mk_q_func_decl(q);
                        conjs.push_back(m.mk_app(qr, m_bv.mk_bv_sub(var, mk_q_one())));
                    }
                    for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
                        trm = vs(r.get_tail(j), sub.size(), sub.data());
                        conjs.push_back(trm);
                    }
                    if (r.get_uninterpreted_tail_size() > 0) {
                        conjs.push_back(m_bv.mk_ule(mk_q_one(), var));
                    }
                    bool_rewriter(m).mk_and(conjs.size(), conjs.data(), rule_body);
                    trm = m.mk_implies(rule_i, rule_body);
                    trm = m.mk_forall(1, index_sorts, &tick, trm, 1);
                    b.assert_expr(trm);
                }
                bool_rewriter(m).mk_or(rules.size(), rules.data(), trm);
                trm = m.mk_implies(pred, trm);
                trm = m.mk_forall(1, index_sorts, &tick, trm, 1);
                SASSERT(is_well_sorted(m, trm));
                b.assert_expr(trm);
            }
        }

        void setup() {
            params_ref p;
            p.set_uint("smt.relevancy", 2ul);
            p.set_bool("smt.mbqi", true);
            b.m_solver->updt_params(p);
            b.m_rule_trace.reset();
        }

        void mk_qrule_vars(datalog::rule const& r, unsigned rule_id, expr_ref_vector& sub) {
            ptr_vector<sort> sorts;
            r.get_vars(m, sorts);
            // populate substitution of bound variables.
            sub.reset();
            sub.resize(sorts.size());

            for (unsigned k = 0; k < r.get_decl()->get_arity(); ++k) {
                expr* arg = r.get_head()->get_arg(k);
                if (is_var(arg)) {
                    unsigned idx = to_var(arg)->get_idx();
                    if (!sub[idx].get()) {
                        sub[idx] = mk_q_arg(r.get_decl(), k, true);
                    }
                }
            }
            for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                func_decl* q = r.get_decl(j);
                for (unsigned k = 0; k < q->get_arity(); ++k) {
                    expr* arg = r.get_tail(j)->get_arg(k);
                    if (is_var(arg)) {
                        unsigned idx = to_var(arg)->get_idx();
                        if (!sub[idx].get()) {
                            sub[idx] = mk_q_arg(q, k, false);
                        }
                    }
                }
            }
            for (unsigned j = 0, idx = 0; j < sorts.size(); ++j) {
                if (sorts[j] && !sub[j].get()) {
                    sub[j] = mk_q_var(r.get_decl(), sorts[j], rule_id, idx++);
                }
            }
        }

        expr_ref mk_q_var(func_decl* pred, sort* s, unsigned rule_id, unsigned idx) {
            std::stringstream _name;
            _name << pred->get_name() << "#" <<  rule_id << "_" << idx;
            symbol nm(_name.str());
            var_ref var = mk_index_var();
            return expr_ref(m.mk_app(m.mk_func_decl(nm, mk_index_sort(), s), var), m);
        }

        expr_ref mk_q_arg(func_decl* pred, unsigned idx, bool is_current) {
            SASSERT(idx < pred->get_arity());
            std::stringstream _name;
            _name << pred->get_name() << "#" << idx;
            symbol nm(_name.str());
            expr_ref var(mk_index_var(), m);
            if (!is_current) {
                var = m_bv.mk_bv_sub(var, mk_q_one());
            }
            return expr_ref(m.mk_app(m.mk_func_decl(nm, mk_index_sort(), pred->get_domain(idx)), var), m);
        }

        expr_ref mk_q_one() {
            return mk_q_num(1);
        }

        expr_ref mk_q_num(unsigned i) {
            return expr_ref(m_bv.mk_numeral(i, m_bit_width), m);
        }

        func_decl_ref mk_q_func_decl(func_decl* f) {
            std::stringstream _name;
            _name << f->get_name() << "#";
            symbol nm(_name.str());
            return func_decl_ref(m.mk_func_decl(nm, mk_index_sort(), f->get_range()), m);
        }

        func_decl_ref mk_q_rule(func_decl* f, unsigned rule_id) {
            std::stringstream _name;
            _name << f->get_name() << "#" << rule_id;
            symbol nm(_name.str());
            return func_decl_ref(m.mk_func_decl(nm, mk_index_sort(), m.mk_bool_sort()), m);
        }


        expr_ref eval_q(model_ref& model, func_decl* f, unsigned i) {
            func_decl_ref fn = mk_q_func_decl(f);
            expr_ref t(m);
            t = m.mk_app(mk_q_func_decl(f).get(), mk_q_num(i));
            return (*model)(t);
        }

        expr_ref eval_q(model_ref& model, expr* t, unsigned i) {
            expr_ref tmp(m), result(m), num(m);
            var_subst vs(m, false);
            num = mk_q_num(i);
            expr* nums[1] = { num };
            tmp = vs(t, 1, nums);
            return (*model)(tmp);
        }

        lbool get_model() {
            rule_manager& rm = b.m_ctx.get_rule_manager();
            func_decl_ref q = mk_q_func_decl(b.m_query_pred);
            expr_ref T(m), rule_i(m), vl(m);
            model_ref md;
            proof_ref pr(m);
            rule_unifier unifier(b.m_ctx);
            rational num;
            unsigned level, bv_size;

            b.m_solver->get_model(md);
            func_decl* pred = b.m_query_pred;
            dl_decl_util util(m);
            T = m.mk_const(symbol("T"), mk_index_sort());
            vl = (*md)(T);
            VERIFY (m_bv.is_numeral(vl, num, bv_size));
            SASSERT(num.is_unsigned());
            level = num.get_unsigned();
            SASSERT(m.is_true(eval_q(md, b.m_query_pred, level)));
            TRACE("bmc", model_smt2_pp(tout, m, *md, 0););

            rule_ref r0(rm), r1(rm), r2(rm);
            while (true) {
                TRACE("bmc", tout << "Predicate: " << pred->get_name() << "\n";);
                expr_ref_vector sub(m);
                rule_vector const& rls = b.m_rules.get_predicate_rules(pred);
                rule* r = nullptr;
                unsigned i = 0;
                for (; i < rls.size(); ++i) {
                    rule_i = m.mk_app(mk_q_rule(pred, i), mk_q_num(level).get());
                    TRACE("bmc", rls[i]->display(b.m_ctx, tout << "Checking rule " << mk_pp(rule_i, m) << " "););
                    if (m.is_true(eval_q(md, rule_i, level))) {
                        r = rls[i];
                        break;
                    }
                }
                SASSERT(r);
                mk_qrule_vars(*r, i, sub);
                b.m_rule_trace.push_back(r);
                // we have rule, we have variable names of rule.

                // extract values for the variables in the rule.
                for (unsigned j = 0; j < sub.size(); ++j) {
                    expr_ref vl = eval_q(md, sub[j].get(), i);
                    if (vl) {
                        // vl can be 0 if the interpretation does not assign a value to it.
                        sub[j] = vl;
                    }
                    else {
                        sub[j] = m.mk_var(j, sub[j]->get_sort());
                    }
                }
                svector<std::pair<unsigned, unsigned> > positions;
                vector<expr_ref_vector> substs;
                expr_ref fml(m), concl(m);

                rm.to_formula(*r, fml);
                r2 = r;
                rm.substitute(r2, sub.size(), sub.data());
                proof_ref p(m);
                if (r0) {
                    VERIFY(unifier.unify_rules(*r0.get(), 0, *r2.get()));
                    expr_ref_vector sub1 = unifier.get_rule_subst(*r0.get(), true);
                    expr_ref_vector sub2 = unifier.get_rule_subst(*r2.get(), false);
                    apply_subst(sub, sub2);
                    unifier.apply(*r0.get(), 0, *r2.get(), r1);
                    rm.to_formula(*r1.get(), concl);
                    scoped_proof _sp(m);

                    p = r->get_proof();
                    if (!p) {
                        p = m.mk_asserted(fml);
                    }
                    proof* premises[2] = { pr, p };

                    positions.push_back(std::make_pair(0, 1));

                    substs.push_back(sub1);
                    substs.push_back(sub);
                    pr = m.mk_hyper_resolve(2, premises, concl, positions, substs);
                    r0 = r1;
                }
                else {
                    rm.to_formula(*r, concl);
                    scoped_proof _sp(m);
                    p = r->get_proof();
                    if (!p) {
                        p = m.mk_asserted(fml);
                    }
                    if (sub.empty()) {
                        pr = p;
                    }
                    else {
                        substs.push_back(sub);
                        proof* ps[1] = { p };
                        pr = m.mk_hyper_resolve(1, ps, concl, positions, substs);
                    }
                    r0 = r2;
                }

                if (level == 0) {
                    SASSERT(r->get_uninterpreted_tail_size() == 0);
                    break;
                }
                --level;
                SASSERT(r->get_uninterpreted_tail_size() == 1);
                pred = r->get_decl(0);
            }
            scoped_proof _sp(m);
            apply(m, b.m_ctx.get_proof_converter().get(), pr);
            b.m_answer = pr;
            return l_true;
        }
    };


    // --------------------------------------------------------------------------
    // Basic non-linear BMC based on compiling into quantifiers.

    class bmc::nonlinear {
        bmc&         b;
        ast_manager& m;

    public:

        nonlinear(bmc& b): b(b), m(b.m) {}

        lbool check() {
            setup();
            for (unsigned i = 0; ; ++i) {
                IF_VERBOSE(1, verbose_stream() << "level: " << i << "\n";);
                b.checkpoint();
                expr_ref_vector fmls(m);
                compile(b.m_rules, fmls, i);
                assert_fmls(fmls);
                lbool res = check(i);
                if (res == l_undef) {
                    return res;
                }
                if (res == l_true) {
                    get_model(i);
                    return res;
                }
            }
        }

        expr_ref compile_query(func_decl* query_pred, unsigned level) {
            expr_ref_vector vars(m);
            func_decl_ref level_p = mk_level_predicate(query_pred, level);
            for (unsigned i = 0; i < level_p->get_arity(); ++i) {
                std::stringstream _name;
                _name << query_pred->get_name() << "#" << level << "_" << i;
                symbol nm(_name.str());
                vars.push_back(m.mk_const(nm, level_p->get_domain(i)));
            }
            return expr_ref(m.mk_app(level_p, vars.size(), vars.data()), m);
        }

        void compile(rule_set const& rules, expr_ref_vector& result, unsigned level) {
            bool_rewriter br(m);
            rule_set::decl2rules::iterator it  = rules.begin_grouped_rules();
            rule_set::decl2rules::iterator end = rules.end_grouped_rules();
            for (; it != end; ++it) {
                func_decl* p = it->m_key;
                rule_vector const& rls = *it->m_value;

                // Assert: p_level(vars) => r1_level(vars) \/ r2_level(vars) \/ r3_level(vars) \/ ...
                // Assert: r_i_level(vars) => exists aux_vars . body of rule i for level

                func_decl_ref level_pred = mk_level_predicate(p, level);
                expr_ref_vector rules(m);
                expr_ref body(m), head(m);
                for (unsigned i = 0; i < rls.size(); ++i) {
                    rule& r = *rls[i];
                    func_decl_ref rule_i = mk_level_rule(p, i, level);
                    rules.push_back(apply_vars(rule_i));

                    ptr_vector<sort> rule_vars;
                    expr_ref_vector args(m), conjs(m);

                    r.get_vars(m, rule_vars);
                    obj_hashtable<expr> used_vars;
                    unsigned num_vars = 0;
                    for (unsigned i = 0; i < r.get_decl()->get_arity(); ++i) {
                        expr* arg = r.get_head()->get_arg(i);
                        if (is_var(arg) && !used_vars.contains(arg)) {
                            used_vars.insert(arg);
                            args.push_back(arg);
                            rule_vars[to_var(arg)->get_idx()] = 0;
                        }
                        else {
                            sort* srt = arg->get_sort();
                            args.push_back(m.mk_var(rule_vars.size()+num_vars, srt));
                            conjs.push_back(m.mk_eq(args.back(), arg));
                            ++num_vars;
                        }
                    }
                    head = m.mk_app(rule_i, args.size(), args.data());
                    for (unsigned i = 0; i < r.get_tail_size(); ++i) {
                        conjs.push_back(r.get_tail(i));
                    }
                    br.mk_and(conjs.size(), conjs.data(), body);

                    replace_by_level_predicates(level, body);
                    body = skolemize_vars(r, args, rule_vars, body);
                    body = m.mk_implies(head, body);
                    body = bind_vars(body, head);
                    result.push_back(body);
                }
                br.mk_or(rules.size(), rules.data(), body);
                head = apply_vars(level_pred);
                body = m.mk_implies(head, body);
                body = bind_vars(body, head);
                result.push_back(body);
            }
        }

    private:

        void assert_fmls(expr_ref_vector const& fmls) {
            for (unsigned i = 0; i < fmls.size(); ++i) {
                b.assert_expr(fmls[i]);
            }
        }

        void setup() {
            params_ref p;
            p.set_uint("smt.relevancy", 2ul);
            b.m_solver->updt_params(p);
            b.m_rule_trace.reset();
        }

        lbool check(unsigned level) {
            expr_ref p = compile_query(b.m_query_pred, level);
            expr_ref q(m), q_at_level(m);
            q = m.mk_fresh_const("q",m.mk_bool_sort());
            q_at_level = m.mk_implies(q, p);
            b.assert_expr(q_at_level);
            expr* qr = q.get();
            return b.m_solver->check_sat(1, &qr);
        }

        proof_ref get_proof(model_ref& md, func_decl* pred, app* prop, unsigned level) {
            if (!m.inc()) {
                return proof_ref(nullptr, m);
            }
            TRACE("bmc", tout << "Predicate: " << pred->get_name() << "\n";);
            rule_manager& rm = b.m_ctx.get_rule_manager();
            expr_ref prop_r(m), prop_v(m), fml(m), prop_body(m), tmp(m), body(m);
            expr_ref_vector args(m);
            proof_ref_vector prs(m);
            proof_ref pr(m);

            // find the rule that was triggered by evaluating the arguments to prop.
            rule_vector const& rls = b.m_rules.get_predicate_rules(pred);
            rule* r = nullptr;
            for (unsigned i = 0; i < rls.size(); ++i) {
                func_decl_ref rule_i = mk_level_rule(pred, i, level);
                prop_r = m.mk_app(rule_i, prop->get_num_args(), prop->get_args());
                TRACE("bmc", rls[i]->display(b.m_ctx, tout << "Checking rule " << mk_pp(rule_i, m) << " ");
                      tout << (*md)(prop_r) << "\n";
                      tout << *md << "\n";
                      );
                if (md->is_true(prop_r)) {
                    r = rls[i];
                    break;
                }
            }
            if (!r) 
                throw default_exception("could not expand BMC rule");
            SASSERT(r);
            b.m_rule_trace.push_back(r);
            rm.to_formula(*r, fml);
            IF_VERBOSE(1, verbose_stream() << mk_pp(fml, m) << "\n";);
            if (!r->get_proof()) {
                IF_VERBOSE(0, r->display(b.m_ctx, verbose_stream() << "no proof associated with rule"));
                throw default_exception("no proof associated with rule");
            }
            prs.push_back(r->get_proof());
            unsigned sz = r->get_uninterpreted_tail_size();

            ptr_vector<sort> rule_vars;
            r->get_vars(m, rule_vars);
            args.append(prop->get_num_args(), prop->get_args());
            expr_ref_vector sub = mk_skolem_binding(*r, rule_vars, args);
            if (sub.empty() && sz == 0) {
                pr = prs[0].get();
                return pr;
            }
            for (unsigned j = 0; j < sub.size(); ++j) {
                sub[j] = (*md)(sub[j].get());
            }

            svector<std::pair<unsigned, unsigned> > positions;
            vector<expr_ref_vector> substs;
            var_subst vs(m, false);

            substs.push_back(sub);
            for (unsigned j = 0; j < sz; ++j) {
                func_decl* head_j = r->get_decl(j);
                app* body_j = r->get_tail(j);
                prop_body = vs(body_j, sub.size(), sub.data());
                prs.push_back(get_proof(md, head_j, to_app(prop_body), level-1));
                positions.push_back(std::make_pair(j+1,0));
                substs.push_back(expr_ref_vector(m));
            }
            pr = m.mk_hyper_resolve(sz+1, prs.data(), prop, positions, substs);
            return pr;
        }

        void get_model(unsigned level) {
            scoped_proof _sp(m);
            expr_ref level_query = compile_query(b.m_query_pred, level);
            model_ref md;
            b.m_solver->get_model(md);
            IF_VERBOSE(2, model_smt2_pp(verbose_stream(), m, *md, 0););
            proof_ref pr(m);
            pr = get_proof(md, b.m_query_pred, to_app(level_query), level);
            apply(m, b.m_ctx.get_proof_converter().get(), pr);
            b.m_answer = pr;
        }

        func_decl_ref mk_level_predicate(func_decl* p, unsigned level) {
            std::stringstream _name;
            _name << p->get_name() << "#" << level;
            symbol nm(_name.str());
            return func_decl_ref(m.mk_func_decl(nm, p->get_arity(), p->get_domain(), m.mk_bool_sort()), m);
        }

        func_decl_ref mk_level_rule(func_decl* p, unsigned rule_idx, unsigned level) {
            std::stringstream _name;
            _name << "rule:" << p->get_name() << "#" << level << "_" << rule_idx;
            symbol nm(_name.str());
            return func_decl_ref(m.mk_func_decl(nm, p->get_arity(), p->get_domain(), m.mk_bool_sort()), m);
        }

        expr_ref apply_vars(func_decl* p) {
            expr_ref_vector vars(m);
            for (unsigned i = 0; i < p->get_arity(); ++i) {
                vars.push_back(m.mk_var(i, p->get_domain(i)));
            }
            return expr_ref(m.mk_app(p, vars.size(), vars.data()), m);
        }

        // remove variables from dst that are in src.
        void subtract_vars(ptr_vector<sort>& dst, ptr_vector<sort> const& src) {
            for (unsigned i = 0; i < dst.size(); ++i) {
                if (i >= src.size()) {
                    break;
                }
                if (src[i]) {
                    dst[i] = 0;
                }
            }
        }

        expr_ref_vector mk_skolem_binding(rule& r, ptr_vector<sort> const& vars, expr_ref_vector const& args) {
            expr_ref_vector binding(m);
            ptr_vector<sort> arg_sorts;
            for (unsigned i = 0; i < args.size(); ++i) {
                arg_sorts.push_back(args[i]->get_sort());
            }
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (vars[i]) {
                    func_decl_ref f = mk_body_func(r, arg_sorts, i, vars[i]);
                    binding.push_back(m.mk_app(f, args.size(), args.data()));
                }
                else {
                    binding.push_back(nullptr);
                }
            }
            return binding;
        }

        expr_ref skolemize_vars(rule& r, expr_ref_vector const& args, ptr_vector<sort> const& vars, expr* e) {
            expr_ref_vector binding = mk_skolem_binding(r, vars, args);
            var_subst vs(m, false);
            return vs(e, binding.size(), binding.data());
        }

        func_decl_ref mk_body_func(rule& r, ptr_vector<sort> const& args, unsigned index, sort* s) {
            std::stringstream _name;
            _name << r.get_decl()->get_name() << "@" << index;
            symbol name(_name.str());
            func_decl* f = m.mk_func_decl(name, args.size(), args.data(), s);
            return func_decl_ref(f, m);
        }

        expr_ref bind_vars(expr* e, expr* pat) {
            ptr_vector<sort> sorts;
            svector<symbol> names;
            expr_ref_vector binding(m), patterns(m);
            expr_ref tmp(m), head(m);
            expr_free_vars vars;
            vars(e);
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (vars[i]) {
                    binding.push_back(m.mk_var(sorts.size(), vars[i]));
                    sorts.push_back(vars[i]);
                    names.push_back(symbol(i));
                }
                else {
                    binding.push_back(nullptr);
                }
            }
            sorts.reverse();
            if (sorts.empty()) {
                return expr_ref(e, m);
            }
            var_subst vs(m, false);
            tmp = vs(e, binding.size(), binding.data());
            head = vs(pat, binding.size(), binding.data());
            patterns.push_back(m.mk_pattern(to_app(head)));
            symbol qid, skid;
            return expr_ref(m.mk_forall(sorts.size(), sorts.data(), names.data(), tmp, 1, qid, skid, 1, patterns.data()), m);
        }

    public:
        class level_replacer {
            nonlinear& n;
            unsigned   m_level;
            bool is_predicate(func_decl* f) {
                return n.b.m_ctx.is_predicate(f);
            }
        public:
            level_replacer(nonlinear& n, unsigned level): n(n), m_level(level) {}

            br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
                if (is_predicate(f)) {
                    if (m_level > 0) {
                        result = n.m.mk_app(n.mk_level_predicate(f, m_level-1), num_args, args);
                    }
                    else {
                        result = n.m.mk_false();
                    }
                    return BR_DONE;
                }
                return BR_FAILED;
            }

            bool reduce_quantifier(quantifier* old_q, expr* new_body, expr_ref& result) {
                if (is_ground(new_body)) {
                    result = new_body;
                }
                else {
                    expr * const * no_pats = &new_body;
                    result = n.m.update_quantifier(old_q, 0, nullptr, 1, no_pats, new_body);
                }
                return true;
            }
        };

        struct level_replacer_cfg : public default_rewriter_cfg {
            level_replacer m_r;

            level_replacer_cfg(nonlinear& nl, unsigned level):
                m_r(nl, level) {}

            bool rewrite_patterns() const { return false; }
            br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
                return m_r.mk_app_core(f, num, args, result);
            }
            bool reduce_quantifier(quantifier * old_q,
                                   expr * new_body,
                                   expr * const * new_patterns,
                                   expr * const * new_no_patterns,
                                   expr_ref & result,
                                   proof_ref & result_pr) {
                return m_r.reduce_quantifier(old_q, new_body, result);
            }

        };

        class level_replacer_star : public rewriter_tpl<level_replacer_cfg> {
            level_replacer_cfg m_cfg;
        public:
            level_replacer_star(nonlinear& nl, unsigned level):
                rewriter_tpl<level_replacer_cfg>(nl.m, false, m_cfg),
                m_cfg(nl, level)
            {}
        };

    private:

        void replace_by_level_predicates(unsigned level, expr_ref& fml) {
            level_replacer_star rep(*this, level);
            expr_ref tmp(m);
            rep(fml, tmp);
            fml = tmp;
        }


    };

    // --------------------------------------------------------------------------
    // Basic non-linear BMC based on compiling into data-types (it is inefficient)

    class bmc::nonlinear_dt {
        bmc&             b;
        ast_manager&     m;
        ast_ref_vector   m_pinned;
        sort_ref         m_path_sort;
        obj_map<func_decl, sort*> m_pred2sort;
        obj_map<sort, func_decl*> m_sort2pred;


    public:
        nonlinear_dt(bmc& b): b(b), m(b.m), m_pinned(m), m_path_sort(m) {}

        lbool check() {
            setup();
            declare_datatypes();
            compile();
            return check_query();
        }

    private:
        void setup() {
            m_pred2sort.reset();
            m_pinned.reset();
            m_sort2pred.reset();
            params_ref p;
            p.set_uint("smt.relevancy", 2ul);
            p.set_bool("smt.mbqi", false);
            b.m_solver->updt_params(p);
            b.m_rule_trace.reset();
        }

        func_decl_ref mk_predicate(func_decl* pred) {
            std::stringstream _name;
            _name << pred->get_name() << "#";
            symbol nm(_name.str());
            sort* pred_trace_sort = m_pred2sort.find(pred);
            return func_decl_ref(m.mk_func_decl(nm, pred_trace_sort, m_path_sort, m.mk_bool_sort()), m);
        }

        func_decl_ref mk_rule(func_decl* p, unsigned rule_idx) {
            std::stringstream _name;
            _name << "rule:" << p->get_name() << "#" << rule_idx;
            symbol nm(_name.str());
            sort* pred_trace_sort = m_pred2sort.find(p);
            return func_decl_ref(m.mk_func_decl(nm, pred_trace_sort, m_path_sort, m.mk_bool_sort()), m);
        }

        expr_ref mk_var(func_decl* pred, sort*s, unsigned idx, expr* path_arg, expr* trace_arg) {
            std::stringstream _name;
            _name << pred->get_name() << "#V_" << idx;
            symbol nm(_name.str());
            func_decl_ref fn(m);
            fn = m.mk_func_decl(nm, m_pred2sort.find(pred), m_path_sort, s);
            return expr_ref(m.mk_app(fn, trace_arg, path_arg), m);
        }

        expr_ref mk_arg(func_decl* pred, unsigned idx, expr* path_arg, expr* trace_arg) {
            SASSERT(idx < pred->get_arity());
            std::stringstream _name;
            _name << pred->get_name() << "#X_" << idx;
            symbol nm(_name.str());
            func_decl_ref fn(m);
            fn = m.mk_func_decl(nm, m_pred2sort.find(pred), m_path_sort, pred->get_domain(idx));
            return expr_ref(m.mk_app(fn, trace_arg, path_arg), m);
        }

        void mk_subst(datalog::rule& r, expr* path, app* trace, expr_ref_vector& sub) {
            datatype_util dtu(m);
            ptr_vector<sort> sorts;
            func_decl* p = r.get_decl();
            ptr_vector<func_decl> const& succs  = *dtu.get_datatype_constructors(path->get_sort());
            // populate substitution of bound variables.
            r.get_vars(m, sorts);
            sub.reset();
            sub.resize(sorts.size());
            for (unsigned k = 0; k < r.get_decl()->get_arity(); ++k) {
                expr* arg = r.get_head()->get_arg(k);
                if (is_var(arg)) {
                    unsigned idx = to_var(arg)->get_idx();
                    if (!sub[idx].get()) {
                        sub[idx] = mk_arg(p, k, path, trace);
                    }
                }
            }
            for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                func_decl* q = r.get_decl(j);
                expr_ref path_arg(m);
                if (j == 0) {
                    path_arg = path;
                }
                else {
                    path_arg = m.mk_app(succs[j], path);
                }
                for (unsigned k = 0; k < q->get_arity(); ++k) {
                    expr* arg = r.get_tail(j)->get_arg(k);
                    if (is_var(arg)) {
                        unsigned idx = to_var(arg)->get_idx();
                        if (!sub[idx].get()) {
                            sub[idx] = mk_arg(q, k, path_arg, trace->get_arg(j));
                        }
                    }
                }
            }
            for (unsigned j = 0, idx = 0; j < sorts.size(); ++j) {
                if (sorts[j] && !sub[j].get()) {
                    sub[j] = mk_var(r.get_decl(), sorts[j], idx++, path, trace);
                }
            }
        }

        /**
           \brief compile Horn rule into co-Horn implication.
           forall args . R(path_var, rule_i(trace_vars)) => Body[X(path_var, rule_i(trace_vars)), Y(S_j(path_var), trace_vars_j)]
        */
        void compile() {
            datatype_util dtu(m);

            rule_set::decl2rules::iterator it  = b.m_rules.begin_grouped_rules();
            rule_set::decl2rules::iterator end = b.m_rules.end_grouped_rules();
            for (; it != end; ++it) {
                func_decl* p = it->m_key;
                rule_vector const& rls = *it->m_value;

                // Assert: p_level => r1_level \/ r2_level \/ r3_level \/ ...
                // where:  r_i_level = body of rule i for level + equalities for head of rule i

                expr_ref rule_body(m), tmp(m), pred(m), trace_arg(m), fml(m);
                var_ref path_var(m), trace_var(m);
                expr_ref_vector rules(m), sub(m), conjs(m), vars(m), patterns(m);
                sort* pred_sort = m_pred2sort.find(p);
                path_var  = m.mk_var(0, m_path_sort);
                trace_var = m.mk_var(1, pred_sort);
                // sort* sorts[2] = { pred_sort, m_path_sort };
                ptr_vector<func_decl> const& cnstrs = *dtu.get_datatype_constructors(pred_sort);
                ptr_vector<func_decl> const& succs  = *dtu.get_datatype_constructors(m_path_sort);
                SASSERT(cnstrs.size() == rls.size());
                pred = m.mk_app(mk_predicate(p), trace_var.get(), path_var.get());
                for (unsigned i = 0; i < rls.size(); ++i) {
                    sub.reset();
                    conjs.reset();
                    vars.reset();
                    rule& r = *rls[i];
                    func_decl_ref rule_pred_i = mk_rule(p, i);

                    // Create cnstr_rule_i(Vars)
                    func_decl* cnstr = cnstrs[i];
                    rules.push_back(m.mk_app(rule_pred_i, trace_var.get(), path_var.get()));
                    unsigned arity = cnstr->get_arity();
                    for (unsigned j = 0; j < arity; ++j) {
                        vars.push_back(m.mk_var(arity-j,cnstr->get_domain(j)));
                    }
                    trace_arg = m.mk_app(cnstr, vars.size(), vars.data());

                    mk_subst(r, path_var, to_app(trace_arg), sub);

                    // apply substitution to body.
                    var_subst vs(m, false);
                    for (unsigned k = 0; k < p->get_arity(); ++k) {
                        tmp = vs(r.get_head()->get_arg(k), sub.size(), sub.data());
                        expr_ref arg = mk_arg(p, k, path_var, trace_arg);
                        conjs.push_back(m.mk_eq(tmp, arg));
                    }
                    for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                        expr_ref path_arg(m);
                        if (j == 0) {
                            path_arg = path_var.get();
                        }
                        else {
                            path_arg = m.mk_app(succs[j], path_var.get());
                        }
                        func_decl* q = r.get_decl(j);
                        for (unsigned k = 0; k < q->get_arity(); ++k) {
                            tmp = vs(r.get_tail(j)->get_arg(k), sub.size(), sub.data());
                            expr_ref arg = mk_arg(q, k, path_arg, vars[j].get());
                            conjs.push_back(m.mk_eq(tmp, arg));
                        }
                        func_decl_ref q_pred = mk_predicate(q);
                        conjs.push_back(m.mk_app(q_pred, vars[j].get(), path_arg));
                    }
                    for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
                        tmp = vs(r.get_tail(j), sub.size(), sub.data());
                        conjs.push_back(tmp);
                    }
                    bool_rewriter(m).mk_and(conjs.size(), conjs.data(), rule_body);
                    ptr_vector<sort> q_sorts;
                    vector<symbol> names;
                    for (unsigned i = 0; i < vars.size(); ++i) {
                        q_sorts.push_back(vars[i]->get_sort());
                        names.push_back(symbol(i+1));
                    }
                    vars.push_back(path_var);
                    q_sorts.push_back(path_var->get_sort());
                    names.push_back(symbol("path"));
                    SASSERT(names.size() == q_sorts.size());
                    SASSERT(vars.size() == names.size());
                    symbol qid = r.name(), skid;
                    tmp = m.mk_app(mk_predicate(p), trace_arg.get(), path_var.get());
                    patterns.reset();
                    patterns.push_back(m.mk_pattern(to_app(tmp)));
                    fml = m.mk_implies(tmp, rule_body);
                    fml = m.mk_forall(vars.size(), q_sorts.data(), names.data(), fml, 1, qid, skid, 1, patterns.data());
                    b.assert_expr(fml);
                }
            }
        }

        void declare_datatypes() {
            rule_set::decl2rules::iterator it  = b.m_rules.begin_grouped_rules();
            rule_set::decl2rules::iterator end = b.m_rules.end_grouped_rules();
            datatype_util dtu(m);
            ptr_vector<datatype_decl> dts;

            obj_map<func_decl, unsigned> pred_idx;
            for (unsigned i = 0; it != end; ++it, ++i) {
                pred_idx.insert(it->m_key, i);
            }

            it  = b.m_rules.begin_grouped_rules();
            for (; it != end; ++it) {
                rule_vector const& rls = *it->m_value;
                func_decl* pred = it->m_key;
                ptr_vector<constructor_decl> cnstrs;
                for (unsigned i = 0; i < rls.size(); ++i) {
                    rule* r = rls[i];
                    ptr_vector<accessor_decl> accs;
                    for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                        func_decl* q = r->get_decl(j);
                        unsigned idx = pred_idx.find(q);
                        std::stringstream _name;
                        _name << pred->get_name() << "_" << q->get_name() << j;
                        symbol name(_name.str());
                        type_ref tr(idx);
                        accs.push_back(mk_accessor_decl(m, name, tr));
                    }
                    std::stringstream _name;
                    _name << pred->get_name() << '_' << i;
                    symbol name(_name.str());
                    _name << '?';
                    symbol is_name(_name.str());
                    cnstrs.push_back(mk_constructor_decl(name, is_name, accs.size(), accs.data()));
                }
                dts.push_back(mk_datatype_decl(dtu, pred->get_name(), 0, nullptr, cnstrs.size(), cnstrs.data()));
            }


            sort_ref_vector new_sorts(m);
            family_id dfid = m.mk_family_id("datatype");
            datatype_decl_plugin* dtp = static_cast<datatype_decl_plugin*>(m.get_plugin(dfid));
            VERIFY (dtp->mk_datatypes(dts.size(), dts.data(), 0, nullptr, new_sorts));

            it  = b.m_rules.begin_grouped_rules();
            for (unsigned i = 0; it != end; ++it, ++i) {
                m_pred2sort.insert(it->m_key, new_sorts[i].get());
                m_sort2pred.insert(new_sorts[i].get(), it->m_key);
                m_pinned.push_back(new_sorts[i].get());
            }
            if (!new_sorts.empty()) {
                TRACE("bmc", dtu.display_datatype(new_sorts[0].get(), tout););
            }
            del_datatype_decls(dts.size(), dts.data());

            // declare path data-type.
            {
                new_sorts.reset();
                dts.reset();
                ptr_vector<constructor_decl> cnstrs;
                unsigned max_arity = 0;
                rule_set::iterator it  = b.m_rules.begin();
                rule_set::iterator end = b.m_rules.end();
                for (; it != end; ++it) {
                    rule* r = *it;
                    unsigned sz = r->get_uninterpreted_tail_size();
                    max_arity = std::max(sz, max_arity);
                }
                cnstrs.push_back(mk_constructor_decl(symbol("Z#"), symbol("Z#?"), 0, nullptr));

                for (unsigned i = 0; i + 1 < max_arity; ++i) {
                    std::stringstream _name;
                    _name << "succ#" << i;
                    symbol name(_name.str());
                    _name << "?";
                    symbol is_name(_name.str());
                    std::stringstream _name2;
                    _name2 << "get_succ#" << i;
                    ptr_vector<accessor_decl> accs;
                    type_ref tr(0);
                    accs.push_back(mk_accessor_decl(m, name, tr));
                    cnstrs.push_back(mk_constructor_decl(name, is_name, accs.size(), accs.data()));
                }
                dts.push_back(mk_datatype_decl(dtu, symbol("Path"), 0, nullptr, cnstrs.size(), cnstrs.data()));
                VERIFY (dtp->mk_datatypes(dts.size(), dts.data(), 0, nullptr, new_sorts));
                m_path_sort = new_sorts[0].get();
            }
        }

        proof_ref get_proof(model_ref& md, app* trace, app* path) {
            datatype_util dtu(m);
            rule_manager& rm = b.m_ctx.get_rule_manager();
            sort* trace_sort = trace->get_sort();
            func_decl* p = m_sort2pred.find(trace_sort);
            datalog::rule_vector const& rules = b.m_rules.get_predicate_rules(p);
            ptr_vector<func_decl> const& cnstrs = *dtu.get_datatype_constructors(trace_sort);
            ptr_vector<func_decl> const& succs  = *dtu.get_datatype_constructors(m_path_sort);
            for (unsigned i = 0; i < cnstrs.size(); ++i) {
                if (trace->get_decl() == cnstrs[i]) {
                    svector<std::pair<unsigned, unsigned> > positions;
                    scoped_proof _sc(m);
                    proof_ref_vector prs(m);
                    expr_ref_vector sub(m);
                    vector<expr_ref_vector> substs;
                    proof_ref pr(m);
                    expr_ref fml(m), head(m), tmp(m);
                    app_ref path1(m);

                    // var_subst vs(m, false);
                    mk_subst(*rules[i], path, trace, sub);
                    rm.to_formula(*rules[i], fml);
                    prs.push_back(rules[i]->get_proof());
                    unsigned sz = trace->get_num_args();
                    if (sub.empty() && sz == 0) {
                        pr = prs[0].get();
                        return pr;
                    }
                    for (unsigned j = 0; j < sub.size(); ++j) {
                        sub[j] = (*md)(sub.get(j));
                    }
                    rule_ref rl(b.m_ctx.get_rule_manager());
                    rl = rules[i];
                    b.m_ctx.get_rule_manager().substitute(rl, sub.size(), sub.data());

                    substs.push_back(sub);

                    for (unsigned j = 0; j < sz; ++j) {
                        if (j == 0) {
                            path1 = path;
                        }
                        else {
                            path1 = m.mk_app(succs[j], path);
                        }

                        prs.push_back(get_proof(md, to_app(trace->get_arg(j)), path1));
                        positions.push_back(std::make_pair(j+1,0));
                        substs.push_back(expr_ref_vector(m));
                    }
                    head = rl->get_head();
                    pr = m.mk_hyper_resolve(sz+1, prs.data(), head, positions, substs);
                    b.m_rule_trace.push_back(rl.get());
                    return pr;
                }
            }
            UNREACHABLE();
            return proof_ref(nullptr, m);
        }

        // instantiation of algebraic data-types takes care of the rest.
        lbool check_query() {
            sort* trace_sort = m_pred2sort.find(b.m_query_pred);
            func_decl_ref q = mk_predicate(b.m_query_pred);
            expr_ref trace(m), path(m), fml(m);
            trace = m.mk_const(symbol("trace"), trace_sort);
            path  = m.mk_const(symbol("path"), m_path_sort);
            fml = m.mk_app(q, trace.get(), path.get());
            b.assert_expr(fml);
            while (true) {
                lbool is_sat = b.m_solver->check_sat(0, nullptr);
                model_ref md;
                if (is_sat == l_false) {
                    return is_sat;
                }
                b.m_solver->get_model(md);
                mk_answer(md, trace, path);
                return l_true;
            }
        }

        bool check_model(model_ref& md, expr* trace) {
            expr_ref trace_val(m), eq(m);
            trace_val = (*md)(trace);
            eq = m.mk_eq(trace, trace_val);
            b.m_solver->push();
            b.m_solver->assert_expr(eq);
            lbool is_sat = b.m_solver->check_sat(0, nullptr);
            if (is_sat != l_false) {
                b.m_solver->get_model(md);
            }
            b.m_solver->pop(1);
            if (is_sat == l_false) {
                IF_VERBOSE(1, verbose_stream() << "infeasible trace " << mk_pp(trace_val, m) << "\n";);
                eq = m.mk_not(eq);
                b.assert_expr(eq);
            }
            return is_sat != l_false;
        }

        void mk_answer(model_ref& md, expr_ref& trace, expr_ref& path) {
            IF_VERBOSE(2, model_smt2_pp(verbose_stream(), m, *md, 0););
            trace = (*md)(trace);
            path = (*md)(path);
            IF_VERBOSE(2, verbose_stream() << mk_pp(trace, m) << "\n";
                       for (unsigned i = 0; i < b.m_solver->get_num_assertions(); ++i) {
                           verbose_stream() << mk_pp(b.m_solver->get_assertion(i), m) << "\n";
                       });
            scoped_proof _sp(m);
            proof_ref pr(m);
            pr = get_proof(md, to_app(trace), to_app(path));
            apply(m, b.m_ctx.get_proof_converter().get(), pr);
            b.m_answer = pr;
        }

    };

    // --------------------------------------------------------------------------
    // Basic linear BMC based on incrementally unfolding the transition relation.

    class bmc::linear {
        bmc&         b;
        ast_manager& m;

    public:
        linear(bmc& b): b(b), m(b.m) {}

        lbool check() {
            setup();
            unsigned max_depth = b.m_ctx.get_params().bmc_linear_unrolling_depth();
            for (unsigned i = 0; i < max_depth; ++i) {
                IF_VERBOSE(1, verbose_stream() << "level: " << i << "\n";);
                b.checkpoint();
                compile(i);
                lbool res = check(i);
                if (res == l_undef) {
                    return res;
                }
                if (res == l_true) {
                    get_model(i);
                    return res;
                }
            }
            return l_undef;
        }

    private:

        void get_model(unsigned level) {
            if (!m.inc()) {
                return;
            }
            rule_manager& rm = b.m_ctx.get_rule_manager();
            expr_ref level_query = mk_level_predicate(b.m_query_pred, level);
            model_ref md;
            proof_ref pr(m);
            rule_unifier unifier(b.m_ctx);
            b.m_solver->get_model(md);
            func_decl* pred = b.m_query_pred;
            SASSERT(m.is_true(md->get_const_interp(to_app(level_query)->get_decl())));

            TRACE("bmc", model_smt2_pp(tout, m, *md, 0););

            rule_ref r0(rm), r1(rm), r2(rm);
            while (true) {
                TRACE("bmc", tout << "Predicate: " << pred->get_name() << "\n";);
                expr_ref_vector sub(m);
                rule_vector const& rls = b.m_rules.get_predicate_rules(pred);
                rule* r = nullptr;
                unsigned i = 0;
                for (; i < rls.size(); ++i) {
                    expr_ref rule_i = mk_level_rule(pred, i, level);
                    TRACE("bmc", rls[i]->display(b.m_ctx, tout << "Checking rule " << mk_pp(rule_i, m) << " "););
                    if (m.is_true(md->get_const_interp(to_app(rule_i)->get_decl()))) {
                        r = rls[i];
                        break;
                    }
                }
                SASSERT(r);
                b.m_rule_trace.push_back(r);
                mk_rule_vars(*r, level, i, sub);
                // we have rule, we have variable names of rule.

                // extract values for the variables in the rule.
                for (unsigned j = 0; j < sub.size(); ++j) {
                    expr* vl = md->get_const_interp(to_app(sub[j].get())->get_decl());
                    if (vl) {
                        // vl can be 0 if the interpretation does not assign a value to it.
                        sub[j] = vl;
                    }
                    else {
                        sub[j] = m.mk_var(j, sub[j]->get_sort());
                    }
                }
                svector<std::pair<unsigned, unsigned> > positions;
                vector<expr_ref_vector> substs;
                expr_ref fml(m), concl(m);

                rm.to_formula(*r, fml);
                r2 = r;
                rm.substitute(r2, sub.size(), sub.data());
                proof_ref p(m);
                {
                    scoped_proof _sp(m);
                    p = r->get_proof();
                    if (!p) {
                        p = m.mk_asserted(fml);
                    }
                }

                if (r0) {
                    VERIFY(unifier.unify_rules(*r0.get(), 0, *r2.get()));
                    expr_ref_vector sub1 = unifier.get_rule_subst(*r0.get(), true);
                    expr_ref_vector sub2 = unifier.get_rule_subst(*r2.get(), false);
                    apply_subst(sub, sub2);
                    unifier.apply(*r0.get(), 0, *r2.get(), r1);
                    rm.to_formula(*r1.get(), concl);

                    scoped_proof _sp(m);
                    proof* premises[2] = { pr, p };

                    positions.push_back(std::make_pair(0, 1));

                    substs.push_back(sub1);
                    substs.push_back(sub);
                    pr = m.mk_hyper_resolve(2, premises, concl, positions, substs);
                    r0 = r1;
                }
                else {
                    rm.to_formula(*r2.get(), concl);
                    scoped_proof _sp(m);
                    if (sub.empty()) {
                        pr = p;
                    }
                    else {
                        substs.push_back(sub);
                        proof * ps[1] = { p };
                        pr = m.mk_hyper_resolve(1, ps, concl, positions, substs);
                    }
                    r0 = r2;
                }

                if (level == 0) {
                    SASSERT(r->get_uninterpreted_tail_size() == 0);
                    break;
                }
                --level;
                SASSERT(r->get_uninterpreted_tail_size() == 1);
                pred = r->get_decl(0);
            }
            scoped_proof _sp(m);
            apply(m, b.m_ctx.get_proof_converter().get(), pr);
            b.m_answer = pr;
        }


        void setup() {
            params_ref p;
            p.set_uint("smt.relevancy", 0ul);
            p.set_bool("smt.mbqi", false);
            b.m_solver->updt_params(p);
            b.m_rule_trace.reset();
        }


        lbool check(unsigned level) {
            expr_ref level_query = mk_level_predicate(b.m_query_pred, level);
            expr* q = level_query.get();
            return b.m_solver->check_sat(1, &q);
        }

        expr_ref mk_level_predicate(func_decl* p, unsigned level) {
            return mk_level_predicate(p->get_name(), level);
        }

        expr_ref mk_level_predicate(symbol const& name, unsigned level) {
            std::stringstream _name;
            _name << name << "#" << level;
            symbol nm(_name.str());
            return expr_ref(m.mk_const(nm, m.mk_bool_sort()), m);
        }

        expr_ref mk_level_arg(func_decl* pred, unsigned idx, unsigned level) {
            SASSERT(idx < pred->get_arity());
            std::stringstream _name;
            _name << pred->get_name() << "#" << level << "_" << idx;
            symbol nm(_name.str());
            return expr_ref(m.mk_const(nm, pred->get_domain(idx)), m);
        }

        expr_ref mk_level_var(func_decl* pred, sort* s, unsigned rule_id, unsigned idx, unsigned level) {
            std::stringstream _name;
            _name << pred->get_name() << "#" << level << "_" << rule_id << "_" << idx;
            symbol nm(_name.str());
            return expr_ref(m.mk_const(nm, s), m);
        }

        expr_ref mk_level_rule(func_decl* p, unsigned rule_idx, unsigned level) {
            std::stringstream _name;
            _name << "rule:" << p->get_name() << "#" << level << "_" << rule_idx;
            symbol nm(_name.str());
            return expr_ref(m.mk_const(nm, m.mk_bool_sort()), m);
        }

        void mk_rule_vars(rule& r, unsigned level, unsigned rule_id, expr_ref_vector& sub) {
            ptr_vector<sort> sorts;
            r.get_vars(m, sorts);
            // populate substitution of bound variables.
            sub.reset();
            sub.resize(sorts.size());

            for (unsigned k = 0; k < r.get_decl()->get_arity(); ++k) {
                expr* arg = r.get_head()->get_arg(k);
                if (is_var(arg)) {
                    unsigned idx = to_var(arg)->get_idx();
                    if (!sub[idx].get()) {
                        sub[idx] = mk_level_arg(r.get_decl(), k, level);
                    }
                }
            }
            for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                SASSERT(level > 0);
                func_decl* q = r.get_decl(j);
                for (unsigned k = 0; k < q->get_arity(); ++k) {
                    expr* arg = r.get_tail(j)->get_arg(k);
                    if (is_var(arg)) {
                        unsigned idx = to_var(arg)->get_idx();
                        if (!sub[idx].get()) {
                            sub[idx] = mk_level_arg(q, k, level-1);
                        }
                    }
                }
            }
            for (unsigned j = 0, idx = 0; j < sorts.size(); ++j) {
                if (sorts[j] && !sub[j].get()) {
                    sub[j] = mk_level_var(r.get_decl(), sorts[j], rule_id, idx++, level);
                }
            }
        }

        void compile(unsigned level) {
            rule_set::decl2rules::iterator it  = b.m_rules.begin_grouped_rules();
            rule_set::decl2rules::iterator end = b.m_rules.end_grouped_rules();
            for (; it != end; ++it) {
                func_decl* p = it->m_key;
                rule_vector const& rls = *it->m_value;

                // Assert: p_level => r1_level \/ r2_level \/ r3_level \/ ...
                // Assert: r_i_level => body of rule i for level + equalities for head of rule i

                expr_ref level_pred = mk_level_predicate(p, level);
                expr_ref_vector rules(m), sub(m), conjs(m);
                expr_ref rule_body(m), tmp(m);
                for (unsigned i = 0; i < rls.size(); ++i) {
                    sub.reset();
                    conjs.reset();
                    rule& r = *rls[i];
                    expr_ref rule_i = mk_level_rule(p, i, level);
                    rules.push_back(rule_i);
                    if (level == 0 && r.get_uninterpreted_tail_size() > 0) {
                        tmp = m.mk_not(rule_i);
                        b.assert_expr(tmp);
                        continue;
                    }

                    mk_rule_vars(r, level, i, sub);

                    // apply substitution to body.
                    var_subst vs(m, false);
                    for (unsigned k = 0; k < p->get_arity(); ++k) {
                        tmp = vs(r.get_head()->get_arg(k), sub.size(), sub.data());
                        conjs.push_back(m.mk_eq(tmp, mk_level_arg(p, k, level)));
                    }
                    for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                        SASSERT(level > 0);
                        func_decl* q = r.get_decl(j);
                        for (unsigned k = 0; k < q->get_arity(); ++k) {
                            tmp = vs(r.get_tail(j)->get_arg(k), sub.size(), sub.data());
                            conjs.push_back(m.mk_eq(tmp, mk_level_arg(q, k, level-1)));
                        }
                        conjs.push_back(mk_level_predicate(q, level-1));
                    }
                    for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
                        tmp = vs(r.get_tail(j), sub.size(), sub.data());
                        conjs.push_back(tmp);
                    }
                    bool_rewriter(m).mk_and(conjs.size(), conjs.data(), rule_body);
                    rule_body = m.mk_implies(rule_i, rule_body);
                    b.assert_expr(rule_body);
                }
                bool_rewriter(m).mk_or(rules.size(), rules.data(), tmp);
                tmp = m.mk_implies(level_pred, tmp);
                b.assert_expr(tmp);
            }
        }
    };

    bmc::bmc(context& ctx):
        engine_base(ctx.get_manager(), "bmc"),
        m_ctx(ctx),
        m(ctx.get_manager()),
        m_solver(nullptr),
        m_rules(ctx),
        m_query_pred(m),
        m_answer(m),
        m_rule_trace(ctx.get_rule_manager()) {
    }

    bmc::~bmc() {}

    lbool bmc::query(expr* query) {
        m_solver = nullptr;
        m_answer = nullptr;
        m_ctx.ensure_opened();
        m_rules.reset();
        datalog::rule_manager& rule_manager = m_ctx.get_rule_manager();
        rule_set& rules0 = m_ctx.get_rules();
        datalog::rule_set old_rules(rules0);
        rule_manager.mk_query(query, rules0);
        expr_ref bg_assertion = m_ctx.get_background_assertion();
        apply_default_transformation(m_ctx);

        if (m_ctx.xform_slice()) {
            datalog::rule_transformer transformer(m_ctx);
            datalog::mk_slice* slice = alloc(datalog::mk_slice, m_ctx);
            transformer.register_plugin(slice);
            m_ctx.transform_rules(transformer);
        }

        const rule_set& rules = m_ctx.get_rules();
        if (rules.get_output_predicates().empty()) {
            return l_false;
        }

        m_query_pred = rules.get_output_predicate();
        m_rules.replace_rules(rules);
        m_rules.close();
        m_ctx.reopen();
        m_ctx.replace_rules(old_rules);

        checkpoint();

        IF_VERBOSE(2, m_ctx.display_rules(verbose_stream()););

        params_ref p;
        if (m_rules.get_num_rules() == 0) {
            return l_false;
        }
        if (m_rules.get_predicate_rules(m_query_pred).empty()) {
            return l_false;
        }

        if (is_linear()) {
            if (m_ctx.get_engine() == QBMC_ENGINE) {
                m_solver = mk_smt_solver(m, p, symbol::null);
                qlinear ql(*this);
                return ql.check();
            }
            else {
                if (m_rules.is_finite_domain()) {
                    m_solver = mk_fd_solver(m, p);
                }
                else {
                    m_solver = mk_smt_solver(m, p, symbol::null);
                }
                linear lin(*this);
                return lin.check();
            }
        }
        else {
            m_solver = mk_smt_solver(m, p, symbol::null);
            IF_VERBOSE(0, verbose_stream() << "WARNING: non-linear BMC is highly inefficient\n";);
            nonlinear nl(*this);
            return nl.check();
        }
    }

    void bmc::assert_expr(expr* e) {
        TRACE("bmc", tout << mk_pp(e, m) << "\n";);
        m_solver->assert_expr(e);
    }

    bool bmc::is_linear() const {
        unsigned sz = m_rules.get_num_rules();
        for (unsigned i = 0; i < sz; ++i) {
            if (m_rules.get_rule(i)->get_uninterpreted_tail_size() > 1) {
                return false;
            }
            if (m_rules.get_rule_manager().has_quantifiers(*m_rules.get_rule(i))) {
                return false;
            }
        }
        return true;
    }

    void bmc::checkpoint() {
        tactic::checkpoint(m);
    }

    void bmc::display_certificate(std::ostream& out) const {
        out << mk_pp(m_answer, m) << "\n";
    }

    void bmc::collect_statistics(statistics& st) const {
        if (m_solver) m_solver->collect_statistics(st);
    }

    void bmc::reset_statistics() {
        // m_solver->reset_statistics();
    }

    expr_ref bmc::get_answer()  {
        return m_answer;
    }

    proof_ref bmc::get_proof() {
        return proof_ref(to_app(m_answer), m);
    }

    void bmc::get_rules_along_trace(datalog::rule_ref_vector& rules) {
        rules.append(m_rule_trace);
    }

    void bmc::compile(rule_set const& rules, expr_ref_vector& fmls, unsigned level) {
        nonlinear nl(*this);
        nl.compile(rules, fmls, level);
    }

    expr_ref bmc::compile_query(func_decl* query_pred, unsigned level) {
        nonlinear nl(*this);
        return nl.compile_query(query_pred, level);
    }

};

template class rewriter_tpl<datalog::bmc::nonlinear::level_replacer_cfg>;
