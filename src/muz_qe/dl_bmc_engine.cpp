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

#include "dl_context.h"
#include "dl_rule_transformer.h"
#include "dl_bmc_engine.h"
#include "dl_mk_slice.h"
#include "smt_kernel.h"
#include "datatype_decl_plugin.h"
#include "dl_mk_rule_inliner.h"
#include "dl_decl_plugin.h"
#include "bool_rewriter.h"
#include "model_smt2_pp.h"
#include "ast_smt_pp.h"
#include "well_sorted.h"

namespace datalog {
    bmc::bmc(context& ctx): 
        m_ctx(ctx), 
        m(ctx.get_manager()), 
        m_solver(m, m_fparams),
        m_pinned(m),
        m_rules(ctx),
        m_query_pred(m),
        m_answer(m),
        m_cancel(false), 
        m_path_sort(m),
        m_bv(m) {
        }

    bmc::~bmc() {}

    lbool bmc::query(expr* query) {
        m_solver.reset();
        m_pinned.reset();
        m_pred2sort.reset();
        m_sort2pred.reset();
        m_pred2newpred.reset();
        m_pred2args.reset();
        m_answer = 0;

        m_ctx.ensure_opened();
        m_rules.reset();
        m_ctx.get_rmanager().reset_relations();
        datalog::rule_manager& rule_manager = m_ctx.get_rule_manager();
        datalog::rule_set        old_rules(m_ctx.get_rules());
        datalog::rule_ref_vector query_rules(rule_manager);
        datalog::rule_ref        query_rule(rule_manager);
        rule_manager.mk_query(query, m_query_pred, query_rules, query_rule);
        m_ctx.add_rules(query_rules);
        expr_ref bg_assertion = m_ctx.get_background_assertion();
        
        model_converter_ref mc = datalog::mk_skip_model_converter();
        m_pc = datalog::mk_skip_proof_converter();
        m_ctx.set_output_predicate(m_query_pred);
        m_ctx.apply_default_transformation(mc, m_pc);
        
        if (m_ctx.get_params().get_bool(":slice", true)) {
            datalog::rule_transformer transformer(m_ctx);
            datalog::mk_slice* slice = alloc(datalog::mk_slice, m_ctx);
            transformer.register_plugin(slice);
            m_ctx.transform_rules(transformer, mc, m_pc);        
            m_query_pred = slice->get_predicate(m_query_pred.get());
            m_ctx.set_output_predicate(m_query_pred);
        }
        m_rules.add_rules(m_ctx.get_rules());
        m_rules.close();
        m_ctx.reopen();
        m_ctx.replace_rules(old_rules);

        checkpoint();

        IF_VERBOSE(2, m_ctx.display_rules(verbose_stream()););

        if (m_rules.get_num_rules() == 0) {
            return l_false;
        }

        if (is_linear()) {
            if (m_ctx.get_engine() == QBMC_ENGINE) {
                return check_qlinear();
            }
            return check_linear();
        }
        else {
            IF_VERBOSE(0, verbose_stream() << "WARNING: non-linear BMC is highly inefficient\n";);
            return check_nonlinear();
        }
    }

    bool bmc::is_linear() const {
        unsigned sz = m_rules.get_num_rules();
        for (unsigned i = 0; i < sz; ++i) {
            if (m_rules.get_rule(i)->get_uninterpreted_tail_size() > 1) {
                return false;
            }
        }
        return true;
    }

    // --------------------------------------------------------------------------
    // Basic linear BMC based on incrementally unfolding the transition relation.

    void bmc::get_model_linear(unsigned level) {
         rule_manager& rm = m_ctx.get_rule_manager();
         expr_ref level_query = mk_level_predicate(m_query_pred, level);
         model_ref md;
         proof_ref pr(m);
         rule_unifier unifier(m_ctx);
         m_solver.get_model(md);
         func_decl* pred = m_query_pred;
         SASSERT(m.is_true(md->get_const_interp(to_app(level_query)->get_decl())));
         dl_decl_util util(m);

         TRACE("bmc", model_smt2_pp(tout, m, *md, 0););

         rule_ref r0(rm), r1(rm), r2(rm);
         while (true) {
             TRACE("bmc", tout << "Predicate: " << pred->get_name() << "\n";);
             expr_ref_vector sub(m);
             rule_vector const& rls = m_rules.get_predicate_rules(pred);
             rule* r = 0;
             unsigned i = 0;
             for (; i < rls.size(); ++i) {                
                expr_ref rule_i = mk_level_rule(pred, i, level);
                TRACE("bmc", rls[i]->display(m_ctx, tout << "Checking rule " << mk_pp(rule_i, m) << " "););
                if (m.is_true(md->get_const_interp(to_app(rule_i)->get_decl()))) {
                    r = rls[i];
                    break;
                }
             }
             SASSERT(r);
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
                     sub[j] = m.mk_var(j, m.get_sort(sub[j].get()));
                 }
             }
             svector<std::pair<unsigned, unsigned> > positions;
             vector<expr_ref_vector> substs;
             expr_ref fml(m), concl(m);

             r->to_formula(fml);
             r2 = r;
             rm.substitute(r2, sub.size(), sub.c_ptr());
             if (r0) {
                 VERIFY(unifier.unify_rules(*r0.get(), 0, *r2.get()));
                 expr_ref_vector sub1 = unifier.get_rule_subst(*r0.get(), true);
                 expr_ref_vector sub2 = unifier.get_rule_subst(*r2.get(), false);
                 apply_subst(sub, sub2);
                 unifier.apply(*r0.get(), 0, *r2.get(), r1);
                 r1->to_formula(concl);
                 scoped_coarse_proof _sp(m);
                                  
                 proof* p = m.mk_asserted(fml);
                 proof* premises[2] = { pr, p };

                 positions.push_back(std::make_pair(0, 1));

                 substs.push_back(sub1);
                 substs.push_back(sub);
                 pr = m.mk_hyper_resolve(2, premises, concl, positions, substs);
                 r0 = r1;
             }
             else {
                 r2->to_formula(concl);
                 scoped_coarse_proof _sp(m);
                 proof* p = m.mk_asserted(fml);
                 if (sub.empty()) {
                     pr = p;
                 }
                 else {
                     substs.push_back(sub);
                     pr = m.mk_hyper_resolve(1, &p, concl, positions, substs);
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
         scoped_coarse_proof _sp(m);
         apply(m, m_pc.get(), pr);
         m_answer = pr;
    }


    void bmc::setup_linear() {
        m_fparams.m_relevancy_lvl = 0;
        m_fparams.m_model = true;
        m_fparams.m_model_compact = true;
        m_fparams.m_mbqi = false;
        // m_fparams.m_auto_config = false;
    }

    lbool bmc::check_linear() {
        setup_linear();
        for (unsigned i = 0; ; ++i) {
            IF_VERBOSE(1, verbose_stream() << "level: " << i << "\n";); 
            checkpoint();
            compile_linear(i);
            lbool res = check_linear(i);
            if (res == l_undef) {
                return res;
            }
            if (res == l_true) {
                get_model_linear(i);
                return res;
            }
        }
    }

    lbool bmc::check_linear(unsigned level) {
        expr_ref level_query = mk_level_predicate(m_query_pred, level);
        expr* q = level_query.get();
        return m_solver.check(1, &q);
    }

    void bmc::assert_expr(expr* e) {        
        TRACE("bmc", tout << mk_pp(e, m) << "\n";);
        m_solver.assert_expr(e);
    }

    expr_ref bmc::mk_level_predicate(func_decl* p, unsigned level) {
        return mk_level_predicate(p->get_name(), level);
    }

    expr_ref bmc::mk_level_predicate(symbol const& name, unsigned level) {
        std::stringstream _name;
        _name << name << "#" << level;
        symbol nm(_name.str().c_str());        
        return expr_ref(m.mk_const(nm, m.mk_bool_sort()), m);
    }

    expr_ref bmc::mk_level_arg(func_decl* pred, unsigned idx, unsigned level) {
        SASSERT(idx < pred->get_arity());
        std::stringstream _name;
        _name << pred->get_name() << "#" << level << "_" << idx;
        symbol nm(_name.str().c_str());        
        return expr_ref(m.mk_const(nm, pred->get_domain(idx)), m);
    }

    expr_ref bmc::mk_level_var(func_decl* pred, sort* s, unsigned rule_id, unsigned idx, unsigned level) {
        std::stringstream _name;
        _name << pred->get_name() << "#" << level << "_" << rule_id << "_" << idx;
        symbol nm(_name.str().c_str());        
        return expr_ref(m.mk_const(nm, s), m);
    }

    expr_ref bmc::mk_level_rule(func_decl* p, unsigned rule_idx, unsigned level) {
        std::stringstream _name;
        _name << "rule:" << p->get_name() << "#" << level << "_" << rule_idx;
        symbol nm(_name.str().c_str()); 
        return expr_ref(m.mk_const(nm, m.mk_bool_sort()), m);
    }

    void bmc::mk_rule_vars(rule& r, unsigned level, unsigned rule_id, expr_ref_vector& sub) {
        sort_ref_vector sorts(m);
        r.get_vars(sorts);
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
            if (sorts[j].get() && !sub[j].get()) {
                sub[j] = mk_level_var(r.get_decl(), sorts[j].get(), rule_id, idx++, level);
            }
        }
    }

    void bmc::compile_linear(unsigned level) {
        rule_set::decl2rules::iterator it  = m_rules.begin_grouped_rules();
        rule_set::decl2rules::iterator end = m_rules.end_grouped_rules();
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
                    assert_expr(tmp);
                    continue;
                }

                mk_rule_vars(r, level, i, sub);

                // apply substitution to body.
                var_subst vs(m, false);
                for (unsigned k = 0; k < p->get_arity(); ++k) {
                    vs(r.get_head()->get_arg(k), sub.size(), sub.c_ptr(), tmp);
                    conjs.push_back(m.mk_eq(tmp, mk_level_arg(p, k, level)));
                }
                for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                    SASSERT(level > 0);
                    func_decl* q = r.get_decl(j);
                    for (unsigned k = 0; k < q->get_arity(); ++k) {
                        vs(r.get_tail(j)->get_arg(k), sub.size(), sub.c_ptr(), tmp);
                        conjs.push_back(m.mk_eq(tmp, mk_level_arg(q, k, level-1)));
                    }
                    conjs.push_back(mk_level_predicate(q, level-1));
                }
                for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
                    vs(r.get_tail(j), sub.size(), sub.c_ptr(), tmp);
                    conjs.push_back(tmp);
                }
                bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), rule_body);
                rule_body = m.mk_implies(rule_i, rule_body);
                assert_expr(rule_body);
            }
            bool_rewriter(m).mk_or(rules.size(), rules.c_ptr(), tmp);
            tmp = m.mk_implies(level_pred, tmp);
            assert_expr(tmp);
        }
    }

    // ---------------------------------------------------------------------------
    // Basic linear BMC based on indexed variables using quantified bit-vector domains.

    lbool bmc::check_qlinear() {
        setup_qlinear();
        m_bit_width = 4;
        lbool res = l_false;
        while (res == l_false) {
            m_solver.push();
            IF_VERBOSE(1, verbose_stream() << "bit_width: " << m_bit_width << "\n";);
            compile_qlinear();
            checkpoint();
            func_decl_ref q = mk_q_func_decl(m_query_pred);
            expr* T = m.mk_const(symbol("T"), mk_index_sort());
            expr_ref fml(m.mk_app(q, T), m);
            assert_expr(fml);
            res = m_solver.check();

            if (res == l_true) {
                res = get_model_qlinear();                
            }
            m_solver.pop(1);           
            ++m_bit_width;
        }
        return res;
    }

    sort_ref bmc::mk_index_sort() {
        return sort_ref(m_bv.mk_sort(m_bit_width), m);
    }

    var_ref bmc::mk_index_var() {
        return var_ref(m.mk_var(0, mk_index_sort()), m);
    }

    void bmc::compile_qlinear() {
        sort_ref index_sort = mk_index_sort();
        var_ref var = mk_index_var();
        sort* index_sorts[1] = { index_sort };
        symbol tick("T");
        rule_set::decl2rules::iterator it  = m_rules.begin_grouped_rules();
        rule_set::decl2rules::iterator end = m_rules.end_grouped_rules();
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
                    vs(r.get_head()->get_arg(k), sub.size(), sub.c_ptr(), trm);
                    conjs.push_back(m.mk_eq(trm, mk_q_arg(p, k, true)));
                }
                for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
                    func_decl* q = r.get_decl(j);
                    for (unsigned k = 0; k < q->get_arity(); ++k) {
                        vs(r.get_tail(j)->get_arg(k), sub.size(), sub.c_ptr(), trm);
                        conjs.push_back(m.mk_eq(trm, mk_q_arg(q, k, false)));
                    }
                    func_decl_ref qr = mk_q_func_decl(q);
                    conjs.push_back(m.mk_app(qr, m_bv.mk_bv_sub(var, mk_q_one())));
                }
                for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
                    vs(r.get_tail(j), sub.size(), sub.c_ptr(), trm);
                    conjs.push_back(trm);
                }
                if (r.get_uninterpreted_tail_size() > 0) {
                    conjs.push_back(m_bv.mk_ule(mk_q_one(), var));
                }
                bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), rule_body);
                trm = m.mk_implies(rule_i, rule_body);
                trm = m.mk_forall(1, index_sorts, &tick, trm, 1);
                assert_expr(trm);
            }
            bool_rewriter(m).mk_or(rules.size(), rules.c_ptr(), trm);
            trm = m.mk_implies(pred, trm);
            trm = m.mk_forall(1, index_sorts, &tick, trm, 1);
            SASSERT(is_well_sorted(m, trm));
            assert_expr(trm);
        }
    }

    void bmc::setup_qlinear() {
        m_fparams.m_relevancy_lvl = 2;
        m_fparams.m_model = true;
        m_fparams.m_model_compact = true;
        m_fparams.m_mbqi = true;
    }

    void bmc::mk_qrule_vars(datalog::rule const& r, unsigned rule_id, expr_ref_vector& sub) {
        sort_ref_vector sorts(m);
        r.get_vars(sorts);
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
            if (sorts[j].get() && !sub[j].get()) {
                sub[j] = mk_q_var(r.get_decl(), sorts[j].get(), rule_id, idx++);
            }
        }        
    }

    expr_ref bmc::mk_q_var(func_decl* pred, sort* s, unsigned rule_id, unsigned idx) {
        std::stringstream _name;
        _name << pred->get_name() << "#" <<  rule_id << "_" << idx;
        symbol nm(_name.str().c_str());        
        var_ref var = mk_index_var();
        return expr_ref(m.mk_app(m.mk_func_decl(nm, mk_index_sort(), s), var), m);
    }    

    expr_ref bmc::mk_q_arg(func_decl* pred, unsigned idx, bool is_current) {
        SASSERT(idx < pred->get_arity());
        std::stringstream _name;
        _name << pred->get_name() << "#" << idx;
        symbol nm(_name.str().c_str());        
        expr_ref var(mk_index_var(), m);
        if (!is_current) {
            var = m_bv.mk_bv_sub(var, mk_q_one());
        }
        return expr_ref(m.mk_app(m.mk_func_decl(nm, mk_index_sort(), pred->get_domain(idx)), var), m);
    }

    expr_ref bmc::mk_q_one() {
        return mk_q_num(1);
    }

    expr_ref bmc::mk_q_num(unsigned i) {
        return expr_ref(m_bv.mk_numeral(i, m_bit_width), m);
    }

    func_decl_ref bmc::mk_q_func_decl(func_decl* f) {
        std::stringstream _name;
        _name << f->get_name() << "#";
        symbol nm(_name.str().c_str());    
        return func_decl_ref(m.mk_func_decl(nm, mk_index_sort(), f->get_range()), m);
    }

    func_decl_ref bmc::mk_q_rule(func_decl* f, unsigned rule_id) {
        std::stringstream _name;
        _name << f->get_name() << "#" << rule_id;
        symbol nm(_name.str().c_str());    
        return func_decl_ref(m.mk_func_decl(nm, mk_index_sort(), m.mk_bool_sort()), m);
    }


    expr_ref bmc::eval_q(model_ref& model, func_decl* f, unsigned i) {
        func_decl_ref fn = mk_q_func_decl(f);
        expr_ref t(m), result(m);
        t = m.mk_app(mk_q_func_decl(f).get(), mk_q_num(i));
        model->eval(t, result);
        return result;
    }

    expr_ref bmc::eval_q(model_ref& model, expr* t, unsigned i) {
        expr_ref tmp(m), result(m), num(m);
        var_subst vs(m, false);
        num = mk_q_num(i);
        expr* nums[1] = { num };
        vs(t, 1, nums, tmp);
        model->eval(tmp, result);
        return result;
    }    

    lbool bmc::get_model_qlinear() {
        rule_manager& rm = m_ctx.get_rule_manager();
        func_decl_ref q = mk_q_func_decl(m_query_pred);
        expr_ref T(m), rule_i(m), vl(m);
        model_ref md;
        proof_ref pr(m);
        rule_unifier unifier(m_ctx);
        rational num;
        unsigned level, bv_size;

        m_solver.get_model(md);
        func_decl* pred = m_query_pred;
        dl_decl_util util(m);
        T = m.mk_const(symbol("T"), mk_index_sort());
        md->eval(T, vl);
        VERIFY (m_bv.is_numeral(vl, num, bv_size));
        SASSERT(num.is_unsigned());
        level = num.get_unsigned();
        SASSERT(m.is_true(eval_q(md, m_query_pred, level)));
        TRACE("bmc", model_smt2_pp(tout, m, *md, 0););
        
        rule_ref r0(rm), r1(rm), r2(rm);
        while (true) {
            TRACE("bmc", tout << "Predicate: " << pred->get_name() << "\n";);
            expr_ref_vector sub(m);
            rule_vector const& rls = m_rules.get_predicate_rules(pred);
            rule* r = 0;
            unsigned i = 0;
            for (; i < rls.size(); ++i) {       
                rule_i = m.mk_app(mk_q_rule(pred, i), mk_q_num(level).get());         
                TRACE("bmc", rls[i]->display(m_ctx, tout << "Checking rule " << mk_pp(rule_i, m) << " "););
                if (m.is_true(eval_q(md, rule_i, level))) {
                    r = rls[i];
                    break;
                }
            }
            SASSERT(r);
            mk_qrule_vars(*r, i, sub);
            // we have rule, we have variable names of rule.
            
            // extract values for the variables in the rule.
            for (unsigned j = 0; j < sub.size(); ++j) {
                expr_ref vl = eval_q(md, sub[j].get(), i);
                if (vl) {
                    // vl can be 0 if the interpretation does not assign a value to it.
                    sub[j] = vl;   
                }
                else {
                    sub[j] = m.mk_var(j, m.get_sort(sub[j].get()));
                }
            }
            svector<std::pair<unsigned, unsigned> > positions;
            vector<expr_ref_vector> substs;
            expr_ref fml(m), concl(m);
            
            r->to_formula(fml);
            r2 = r;
            rm.substitute(r2, sub.size(), sub.c_ptr());
            if (r0) {
                VERIFY(unifier.unify_rules(*r0.get(), 0, *r2.get()));
                expr_ref_vector sub1 = unifier.get_rule_subst(*r0.get(), true);
                expr_ref_vector sub2 = unifier.get_rule_subst(*r2.get(), false);
                apply_subst(sub, sub2);
                unifier.apply(*r0.get(), 0, *r2.get(), r1);
                r1->to_formula(concl);
                scoped_coarse_proof _sp(m);
                
                proof* p = m.mk_asserted(fml);
                proof* premises[2] = { pr, p };
                
                positions.push_back(std::make_pair(0, 1));
                
                substs.push_back(sub1);
                substs.push_back(sub);
                pr = m.mk_hyper_resolve(2, premises, concl, positions, substs);
                r0 = r1;
            }
            else {
                r2->to_formula(concl);
                scoped_coarse_proof _sp(m);
                proof* p = m.mk_asserted(fml);
                if (sub.empty()) {
                    pr = p;
                }
                else {
                    substs.push_back(sub);
                    pr = m.mk_hyper_resolve(1, &p, concl, positions, substs);
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
        scoped_coarse_proof _sp(m);
        apply(m, m_pc.get(), pr);
        m_answer = pr;
        return l_true;
    }

    // --------------------------------------------------------------------------
    // Basic non-linear BMC based on compiling into data-types (it is inefficient)


    lbool bmc::check_nonlinear() {
        setup_nonlinear();
        declare_datatypes();
        compile_nonlinear();        
        return check_query();      
    }

    void bmc::setup_nonlinear() {
        setup_linear();
        m_fparams.m_relevancy_lvl = 2;
    }

    func_decl_ref bmc::mk_predicate(func_decl* pred) {
        std::stringstream _name;
        _name << pred->get_name() << "#";
        symbol nm(_name.str().c_str());    
        sort* pred_trace_sort = m_pred2sort.find(pred);
        return func_decl_ref(m.mk_func_decl(nm, pred_trace_sort, m_path_sort, m.mk_bool_sort()), m);
    }

    func_decl_ref bmc::mk_rule(func_decl* p, unsigned rule_idx) {
        std::stringstream _name;
        _name << "rule:" << p->get_name() << "#" << rule_idx;
        symbol nm(_name.str().c_str());    
        sort* pred_trace_sort = m_pred2sort.find(p);
        return func_decl_ref(m.mk_func_decl(nm, pred_trace_sort, m_path_sort, m.mk_bool_sort()), m);        
    }

    expr_ref bmc::mk_var_nonlinear(func_decl* pred, sort*s, unsigned idx, expr* path_arg, expr* trace_arg) {
        std::stringstream _name;
        _name << pred->get_name() << "#V_" << idx;
        symbol nm(_name.str().c_str());        
        func_decl_ref fn(m);
        fn = m.mk_func_decl(nm, m_pred2sort.find(pred), m_path_sort, s);
        return expr_ref(m.mk_app(fn, trace_arg, path_arg), m);
    }

    expr_ref bmc::mk_arg_nonlinear(func_decl* pred, unsigned idx, expr* path_arg, expr* trace_arg) {
        SASSERT(idx < pred->get_arity());
        std::stringstream _name;
        _name << pred->get_name() << "#X_" << idx;
        symbol nm(_name.str().c_str());        
        func_decl_ref fn(m);
        fn = m.mk_func_decl(nm, m_pred2sort.find(pred), m_path_sort, pred->get_domain(idx));
        return expr_ref(m.mk_app(fn, trace_arg, path_arg), m);
    }

    void bmc::mk_subst(datalog::rule& r, expr* path, app* trace, expr_ref_vector& sub) {
        datatype_util dtu(m);
        sort_ref_vector sorts(m);
        func_decl* p = r.get_decl();
        ptr_vector<func_decl> const& succs  = *dtu.get_datatype_constructors(m.get_sort(path));
        // populate substitution of bound variables.
        r.get_vars(sorts);
        sub.reset();
        sub.resize(sorts.size());
        for (unsigned k = 0; k < r.get_decl()->get_arity(); ++k) {
            expr* arg = r.get_head()->get_arg(k);
            if (is_var(arg)) {
                unsigned idx = to_var(arg)->get_idx();
                if (!sub[idx].get()) {
                    sub[idx] = mk_arg_nonlinear(p, k, path, trace);
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
                        sub[idx] = mk_arg_nonlinear(q, k, path_arg, trace->get_arg(j));
                    }
                }
            }
        }
        for (unsigned j = 0, idx = 0; j < sorts.size(); ++j) {
            if (sorts[j].get() && !sub[j].get()) {
                sub[j] = mk_var_nonlinear(r.get_decl(), sorts[j].get(), idx++, path, trace);
            }
        }
    }

    /**
       \brief compile Horn rule into co-Horn implication.
         forall args . R(path_var, rule_i(trace_vars)) => Body[X(path_var, rule_i(trace_vars)), Y(S_j(path_var), trace_vars_j)]
     */ 
    void bmc::compile_nonlinear() {
        datatype_util dtu(m);

        rule_set::decl2rules::iterator it  = m_rules.begin_grouped_rules();
        rule_set::decl2rules::iterator end = m_rules.end_grouped_rules();
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
                trace_arg = m.mk_app(cnstr, vars.size(), vars.c_ptr());

                mk_subst(r, path_var, to_app(trace_arg), sub);

                // apply substitution to body.
                var_subst vs(m, false);
                for (unsigned k = 0; k < p->get_arity(); ++k) {
                    vs(r.get_head()->get_arg(k), sub.size(), sub.c_ptr(), tmp);
                    expr_ref arg = mk_arg_nonlinear(p, k, path_var, trace_arg);
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
                        vs(r.get_tail(j)->get_arg(k), sub.size(), sub.c_ptr(), tmp);
                        expr_ref arg = mk_arg_nonlinear(q, k, path_arg, vars[j].get());
                        conjs.push_back(m.mk_eq(tmp, arg));
                    }
                    func_decl_ref q_pred = mk_predicate(q);
                    conjs.push_back(m.mk_app(q_pred, vars[j].get(), path_arg));
                }
                for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
                    vs(r.get_tail(j), sub.size(), sub.c_ptr(), tmp);
                    conjs.push_back(tmp);
                }
                bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), rule_body);
                ptr_vector<sort> q_sorts;
                vector<symbol> names;
                for (unsigned i = 0; i < vars.size(); ++i) {
                    q_sorts.push_back(m.get_sort(vars[i].get()));
                    names.push_back(symbol(i+1));
                }
                vars.push_back(path_var);
                q_sorts.push_back(m.get_sort(path_var));
                names.push_back(symbol("path"));
                SASSERT(names.size() == q_sorts.size());
                SASSERT(vars.size() == names.size());
                symbol qid = r.name(), skid;               
                tmp = m.mk_app(mk_predicate(p), trace_arg.get(), path_var.get());
                patterns.reset();
                patterns.push_back(m.mk_pattern(to_app(tmp)));
                fml = m.mk_implies(tmp, rule_body);
                fml = m.mk_forall(vars.size(), q_sorts.c_ptr(), names.c_ptr(), fml, 1, qid, skid, 1, patterns.c_ptr());
                assert_expr(fml);
                
            }
        }               
    }

    void bmc::declare_datatypes() {
        rule_set::decl2rules::iterator it  = m_rules.begin_grouped_rules();
        rule_set::decl2rules::iterator end = m_rules.end_grouped_rules();
        datatype_util dtu(m);
        ptr_vector<datatype_decl> dts;

        obj_map<func_decl, unsigned> pred_idx;
        for (unsigned i = 0; it != end; ++it, ++i) {
            pred_idx.insert(it->m_key, i);
        }

        it  = m_rules.begin_grouped_rules();
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
                    symbol name(_name.str().c_str());
                    type_ref tr(idx);
                    accs.push_back(mk_accessor_decl(name, tr));
                }
                std::stringstream _name;
                _name << pred->get_name() << "_" << i;
                symbol name(_name.str().c_str());
                _name << "?";
                symbol is_name(_name.str().c_str());
                cnstrs.push_back(mk_constructor_decl(name, is_name, accs.size(), accs.c_ptr()));
            }            
            dts.push_back(mk_datatype_decl(pred->get_name(), cnstrs.size(), cnstrs.c_ptr()));
        }
        

        sort_ref_vector new_sorts(m);
        family_id dfid = m.get_family_id("datatype");
        datatype_decl_plugin* dtp = static_cast<datatype_decl_plugin*>(m.get_plugin(dfid));
        VERIFY (dtp->mk_datatypes(dts.size(), dts.c_ptr(), new_sorts));

        it  = m_rules.begin_grouped_rules();
        for (unsigned i = 0; it != end; ++it, ++i) {       
            m_pred2sort.insert(it->m_key, new_sorts[i].get());
            m_sort2pred.insert(new_sorts[i].get(), it->m_key);
            m_pinned.push_back(new_sorts[i].get());            
        }
        if (new_sorts.size() > 0) {
            TRACE("bmc", dtu.display_datatype(new_sorts[0].get(), tout););
        }
        del_datatype_decls(dts.size(), dts.c_ptr());

        // declare path data-type.
        {
            new_sorts.reset();
            dts.reset();
            ptr_vector<constructor_decl> cnstrs;
            unsigned max_arity = 0;
            rule_set::iterator it  = m_rules.begin();
            rule_set::iterator end = m_rules.end();
            for (; it != end; ++it) {
                rule* r = *it;
                unsigned sz = r->get_uninterpreted_tail_size();
                max_arity = std::max(sz, max_arity);
            }        
            cnstrs.push_back(mk_constructor_decl(symbol("Z#"), symbol("Z#?"), 0, 0));
            
            for (unsigned i = 0; i + 1 < max_arity; ++i) {
                std::stringstream _name;
                _name << "succ#" << i;
                symbol name(_name.str().c_str());
                _name << "?";
                symbol is_name(_name.str().c_str());
                std::stringstream _name2;
                _name2 << "get_succ#" << i;
                symbol acc_name(_name2.str().c_str());
                ptr_vector<accessor_decl> accs;
                type_ref tr(0);
                accs.push_back(mk_accessor_decl(name, tr));
                cnstrs.push_back(mk_constructor_decl(name, is_name, accs.size(), accs.c_ptr()));
            }        
            dts.push_back(mk_datatype_decl(symbol("Path"), cnstrs.size(), cnstrs.c_ptr()));
            VERIFY (dtp->mk_datatypes(dts.size(), dts.c_ptr(), new_sorts));
            m_path_sort = new_sorts[0].get();
        }
    }

    proof_ref bmc::get_proof(model_ref& md, app* trace, app* path) {
        datatype_util dtu(m);
        sort* trace_sort = m.get_sort(trace);
        func_decl* p = m_sort2pred.find(trace_sort);
        datalog::rule_vector const& rules = m_rules.get_predicate_rules(p);
        ptr_vector<func_decl> const& cnstrs = *dtu.get_datatype_constructors(trace_sort);
        ptr_vector<func_decl> const& succs  = *dtu.get_datatype_constructors(m_path_sort);
        // bool found = false;
        for (unsigned i = 0; i < cnstrs.size(); ++i) {
            if (trace->get_decl() == cnstrs[i]) {
                // found = true;
                svector<std::pair<unsigned, unsigned> > positions;
                scoped_coarse_proof _sc(m);
                proof_ref_vector prs(m);
                expr_ref_vector sub(m);
                vector<expr_ref_vector> substs;
                proof_ref pr(m);
                expr_ref fml(m), head(m), tmp(m);
                app_ref path1(m);

                var_subst vs(m, false);
                mk_subst(*rules[i], path, trace, sub);
                rules[i]->to_formula(fml);
                prs.push_back(m.mk_asserted(fml));
                unsigned sz = trace->get_num_args();
                if (sub.empty() && sz == 0) {
                    pr = prs[0].get();
                    return pr;
                }
                for (unsigned j = 0; j < sub.size(); ++j) {
                    md->eval(sub[j].get(), tmp);
                    sub[j] = tmp;
                }
                rule_ref rl(m_ctx.get_rule_manager());
                rl = rules[i];
                m_ctx.get_rule_manager().substitute(rl, sub.size(), sub.c_ptr());

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
                pr = m.mk_hyper_resolve(sz+1, prs.c_ptr(), head, positions, substs);                
                return pr;
            }
        }
        UNREACHABLE();
        return proof_ref(0, m);
    }

    // instantiation of algebraic data-types takes care of the rest.
    lbool bmc::check_query() {
        sort* trace_sort = m_pred2sort.find(m_query_pred);
        func_decl_ref q = mk_predicate(m_query_pred);
        expr_ref trace(m), path(m), fml(m);
        trace = m.mk_const(symbol("trace"), trace_sort);
        path  = m.mk_const(symbol("path"), m_path_sort);
        fml = m.mk_app(q, trace.get(), path.get());
        assert_expr(fml);
        while (true) {
            lbool is_sat = m_solver.check();
            model_ref md;
            if (is_sat == l_false) {
                return is_sat;
            }
            m_solver.get_model(md);
            mk_answer_nonlinear(md, trace, path);
            return l_true;            
        }
    }

    bool bmc::check_model_nonlinear(model_ref& md, expr* trace) {
        expr_ref trace_val(m), eq(m);
        md->eval(trace, trace_val);
        eq = m.mk_eq(trace, trace_val);
        m_solver.push();
        m_solver.assert_expr(eq);
        lbool is_sat = m_solver.check();
        if (is_sat != l_false) {
            m_solver.get_model(md);
        }
        m_solver.pop(1);
        if (is_sat == l_false) {
            IF_VERBOSE(1, verbose_stream() << "infeasible trace " << mk_pp(trace_val, m) << "\n";);
            eq = m.mk_not(eq);
            m_solver.assert_expr(eq);
        }
        return is_sat != l_false;       
    }

    void bmc::mk_answer_nonlinear(model_ref& md, expr_ref& trace, expr_ref& path) {                
        proof_ref pr(m);            
        IF_VERBOSE(2, model_smt2_pp(verbose_stream(), m, *md, 0););
        md->eval(trace, trace);
        md->eval(path, path);
        IF_VERBOSE(2, verbose_stream() << mk_pp(trace, m) << "\n";
            for (unsigned i = 0; i < m_solver.size(); ++i) {
                verbose_stream() << mk_pp(m_solver.get_formulas()[i], m) << "\n";
            });
        m_answer = get_proof(md, to_app(trace), to_app(path));
    }


    void bmc::checkpoint() {
        if (m_cancel) {
            throw default_exception("bmc canceled");
        }
    }

    void bmc::cancel() {
        m_cancel = true;
        m_solver.cancel();
    }

    void bmc::cleanup() {
        m_cancel = false;
        m_solver.reset();
    }

    void bmc::display_certificate(std::ostream& out) const {
        out << mk_pp(m_answer, m) << "\n";
    }

    void bmc::collect_statistics(statistics& st) const {
        m_solver.collect_statistics(st);
    }

    void bmc::collect_params(param_descrs& p) {
    }

    expr_ref bmc::get_answer() {        
        return m_answer;
    }

};
