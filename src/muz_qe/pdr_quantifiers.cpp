/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pdr_quantifiers.cpp

Abstract:

    Module for handling quantifiers in rule bodies.

Author:

    Nikolaj Bjorner (nbjorner) 2012-05-19.

Revision History:

--*/

#include "pdr_quantifiers.h"
#include "pdr_context.h"
#include "model_smt2_pp.h"
#include "ast_smt2_pp.h"
#include "qe.h"
#include "var_subst.h"
#include "dl_rule_set.h"


namespace pdr {

    /**
       \brief model check a potential model against quantifiers in bodies of rules.
       
       \return true if the model rooted in 'root' is checks with the quantifiers, otherwise
       'false' and a set of instantiations that contradict the current model.
    */

    static void get_nodes(model_node& root, ptr_vector<model_node>& nodes) {
        ptr_vector<model_node> todo;
        todo.push_back(&root);
        while (!todo.empty()) {
            model_node* n = todo.back();
            todo.pop_back();
            nodes.push_back(n);
            todo.append(n->children().size(), n->children().c_ptr());
        }
    }


    void quantifier_model_checker::generalize_binding(expr_ref_vector const& binding, vector<expr_ref_vector>& bindings) {
        expr_ref_vector new_binding(m);
        generalize_binding(binding, 0, new_binding, bindings);
    }

    void quantifier_model_checker::generalize_binding(
        expr_ref_vector const& binding, unsigned idx, 
        expr_ref_vector& new_binding, vector<expr_ref_vector>& bindings) {
        if (idx == binding.size()) {
            bool non_zero = false;
            for (unsigned i = 0; i < binding.size(); ++i) {
                if (new_binding[i].get()) {
                    non_zero = true;
                }
                else {
                    new_binding[i] = binding[i];
                }
            }
            if (non_zero) {
                TRACE("pdr", 
                      for (unsigned i = 0; i < new_binding.size(); ++i) {
                          tout << mk_pp(new_binding[i].get(), m) << " ";
                      }
                      tout << "\n";);
                bindings.push_back(new_binding);
            }
            return;
        }
        model_node& node = *m_current_node;
        expr_ref_vector ands(m);
        expr* e1, *e2;
        datalog::flatten_and(node.state(), ands);
        new_binding.push_back(0);
        generalize_binding(binding, idx + 1, new_binding, bindings);
        for (unsigned i = 0; i < ands.size(); ++i) {
            if (m.is_eq(ands[i].get(), e1, e2)) {
                if (e2 == binding[idx]) {
                    new_binding[new_binding.size()-1] = e1;
                    generalize_binding(binding, idx + 1, new_binding, bindings);
                }
            }
        }
        new_binding.pop_back();        
    }


    void quantifier_model_checker::add_binding(quantifier* q, expr_ref_vector& binding) {          
        apply_binding(q, binding);
        vector<expr_ref_vector> bindings;
        generalize_binding(binding, bindings);
        for (unsigned i = 0; i < bindings.size(); ++i) {
            apply_binding(q, bindings[i]);
        }
    }
     
    void quantifier_model_checker::apply_binding(quantifier* q, expr_ref_vector& binding) {          
        app_ref_vector& var_inst = m_current_pt->get_inst(m_current_rule);
        expr_substitution sub(m);
        for (unsigned i = 0; i < var_inst.size(); ++i) {
            expr* v = var_inst[i].get();
            sub.insert(v, m.mk_var(i, m.get_sort(v)));
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);
        expr_ref e(m);
        var_subst vs(m, false);
        vs(q->get_expr(), binding.size(), binding.c_ptr(), e);
        (*rep)(e);        
        m_rules.push_back(m_current_rule);
        m_apps.push_back(to_app(e));
        TRACE("pdr", tout << mk_pp(e, m) << "\n";);
    }

    void quantifier_model_checker::model_check(model_node& root) {
        m_apps.reset();
        m_rules.reset();
        ptr_vector<model_node> nodes;
        get_nodes(root, nodes);
        for (unsigned i = nodes.size(); i > 0; ) {
            --i;
            model_check_node(*nodes[i]);
        }
        if (m_apps.empty()) {
            return;
        }
        qi q(m);
        for (unsigned i = 0; i < m_apps.size(); ++i) {
            q.add(m_rules[i], m_apps[i].get());
        }
        throw q;
    }

    // As & not Body_i is satisfiable 
    // then instantiate with model for parameters to Body_i

    bool quantifier_model_checker::find_instantiations(qinst& qi, unsigned level) {
        return 
            find_instantiations_proof_based(qi, level); // ||
            // find_instantiations_qe_based(qi, level);
    }

    bool quantifier_model_checker::find_instantiations_model_based(qinst& qi, unsigned level) {
        bool found_instance = false;
        expr_ref C(m);
        front_end_params fparams;
        smt::kernel solver(m, fparams);
        solver.assert_expr(m_A);
        for (unsigned i = 0; i < m_Bs.size(); ++i) {
            expr_ref_vector fresh_vars(m);
            quantifier* q = qi.quantifiers[i].get();
            for (unsigned j = 0; j < q->get_num_decls(); ++j) {
                fresh_vars.push_back(m.mk_fresh_const("V",q->get_decl_sort(j)));
            }
            var_subst varsubst(m, false);
            varsubst(m_Bs[i].get(), fresh_vars.size(), fresh_vars.c_ptr(), C);
            TRACE("pdr", tout << "updated propagation formula: " << mk_pp(C,m) << "\n";);
            
            solver.push();
            // TBD: what to do with the different tags when unfolding the same predicate twice?
            solver.assert_expr(m.mk_not(C));
            lbool result = solver.check();
            if (result == l_true) {
                found_instance = true;
                model_ref mr;
                solver.get_model(mr);                
                TRACE("pdr", model_smt2_pp(tout, m, *mr, 0););
                
                expr_ref_vector insts(m);
                for (unsigned j = 0; j < fresh_vars.size(); ++j) {
                    expr* interp = mr->get_const_interp(to_app(fresh_vars[j].get())->get_decl());
                    if (interp) {
                        insts.push_back(interp);
                    }
                    else {
                        insts.push_back(fresh_vars[j].get());
                    }
                    TRACE("pdr", tout << mk_pp(insts.back(), m) << "\n";);
                }
                add_binding(q, insts);
            }
            solver.pop(1);
        }
        return found_instance;
    }

    //
    // Build:
    //
    //    A & forall x . B1 & forall y . B2 & ...
    // =  
    //    not exists x y . (!A or !B1 or !B2 or ...)
    // 
    // Find an instance that satisfies formula.
    // (or find all instances?)
    //
    bool quantifier_model_checker::find_instantiations_qe_based(qinst& qi, unsigned level) {
        expr_ref_vector fmls(m), conjs(m), fresh_vars(m);
        app_ref_vector all_vars(m);
        expr_ref C(m);
        qe::def_vector defs(m);
        front_end_params fparams;
        qe::expr_quant_elim qe(m, fparams);
        for (unsigned i = 0; i < m_Bs.size(); ++i) {
            quantifier* q = qi.quantifiers[i].get();
            unsigned num_decls = q->get_num_decls();
            unsigned offset = all_vars.size();
            for (unsigned j = 0; j < num_decls; ++j) {
                all_vars.push_back(m.mk_fresh_const("V",q->get_decl_sort(j)));
            }
            var_subst varsubst(m, false);
            varsubst(m_Bs[i].get(), num_decls, (expr**)(all_vars.c_ptr() + offset), C);
            fmls.push_back(C);
        }
        conjs.push_back(m_A);
        conjs.push_back(m.mk_not(m.mk_and(fmls.size(), fmls.c_ptr())));
        // add previous instances.
        expr* r = m.mk_and(m_Bs.size(), m_Bs.c_ptr());
        m_trail.push_back(r);
        expr* inst;
        if (!m_bound.find(m_current_rule, r, inst)) {
            TRACE("pdr", tout << "did not find: " << mk_pp(r, m) << "\n";);
            m_trail.push_back(r);
            inst = m.mk_true();
            m_bound.insert(m_current_rule, r, inst);
        }
        else {
            TRACE("pdr", tout << "blocking: " << mk_pp(inst, m) << "\n";);
            conjs.push_back(inst);
        }
        C = m.mk_and(conjs.size(), conjs.c_ptr());
        lbool result = qe.first_elim(all_vars.size(), all_vars.c_ptr(), C, defs);
        TRACE("pdr", tout << mk_pp(C.get(), m) << "\n" << result << "\n";);
        if (result != l_true) {
            return false;
        }
        inst = m.mk_and(inst, m.mk_not(C));
        m_trail.push_back(inst);
        m_bound.insert(m_current_rule, r, inst);
        TRACE("pdr",
              tout << "Instantiating\n";
              for (unsigned i = 0; i < defs.size(); ++i) {
                  tout << defs.var(i)->get_name() << " " << mk_pp(defs.def(i), m) << "\n";
              }
              );
        expr_substitution sub(m);  
        for (unsigned i = 0; i < defs.size(); ++i) {
            sub.insert(m.mk_const(defs.var(i)), defs.def(i));
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);
        for (unsigned i = 0; i < all_vars.size(); ++i) {
            expr_ref tmp(all_vars[i].get(), m);
            (*rep)(tmp);
            all_vars[i] = to_app(tmp);
            }
        unsigned offset = 0;
        for (unsigned i = 0; i < m_Bs.size(); ++i) {
            quantifier* q = qi.quantifiers[i].get();
            unsigned num_decls = q->get_num_decls();                
            expr_ref_vector new_binding(m);
            for (unsigned j = 0; j < num_decls; ++j) {
                new_binding.push_back(all_vars[offset+j].get());
            }
            offset += num_decls;
            add_binding(q, new_binding);
        }
        return true;
    }

    class collect_insts {
        ast_manager&     m;
        ptr_vector<expr>        m_binding;
        vector<expr_ref_vector> m_bindings;
        ptr_vector<quantifier>  m_quantifiers;
    public:
        collect_insts(ast_manager& m): m(m) { }

        void operator()(expr* n) {
            expr* not_q_or_i, *e1, *e2, *e3;
            if (m.is_quant_inst(n, not_q_or_i, m_binding)) {
                VERIFY(m.is_or(not_q_or_i, e1, e2));
                VERIFY(m.is_not(e1, e3));
                SASSERT(is_quantifier(e3));
                m_quantifiers.push_back(to_quantifier(e3));
                m_bindings.push_back(expr_ref_vector(m,m_binding.size(), m_binding.c_ptr()));
                m_binding.reset();
            }
            else if ((m.is_rewrite(n, e1, e2) ||
                      (m.is_rewrite_star(n) && 
                       (e3 = to_app(n)->get_arg(to_app(n)->get_num_args()-1),
                        e1 = to_app(e3)->get_arg(0),
                        e2 = to_app(e3)->get_arg(1),
                        true))) &&
                     is_quantifier(e1) && m.is_false(e2)) {
                quantifier* q = to_quantifier(e1);
                m_quantifiers.push_back(q);
                m_bindings.push_back(expr_ref_vector(m));
                expr_ref_vector& b = m_bindings.back();
                for (unsigned i = 0; i < q->get_num_decls(); ++i) {
                    b.push_back(m.mk_fresh_const("V", q->get_decl_sort(i)));
                }
            }
        }

        void reset() {
            m_quantifiers.reset();
            m_bindings.reset();
        }

        unsigned size() const { return m_quantifiers.size(); }
        ptr_vector<quantifier> const& quantifiers() const { return m_quantifiers; }
        vector<expr_ref_vector> const& bindings() const { return m_bindings; }
        
    };

    bool quantifier_model_checker::find_instantiations_proof_based(qinst& qi, unsigned level) {
        bool found_instance = false;
        TRACE("pdr", tout << mk_pp(m_A,m) << "\n";);
 
        ast_manager mp(PGM_COARSE);        
        ast_translation tr(m, mp);
        ast_translation rev_tr(mp, m);
        expr_ref_vector fmls(mp);
        front_end_params fparams;
        fparams.m_proof_mode = PGM_COARSE;
        // TBD: does not work on integers: fparams.m_mbqi = true;
        expr_ref C(m);
        fmls.push_back(tr(m_A.get()));
        for (unsigned i = 0; i < m_Bs.size(); ++i) {
            C = m.update_quantifier(qi.quantifiers[i].get(), m_Bs[i].get());
            fmls.push_back(tr(C.get()));
        }        
        TRACE("pdr",
              tout << "assert\n";
              for (unsigned i = 0; i < fmls.size(); ++i) {
                  tout << mk_pp(fmls[i].get(), mp) << "\n";
              });
        smt::kernel solver(mp, fparams);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            solver.assert_expr(fmls[i].get());
        }
        lbool result = solver.check();
        if (result != l_false) {
            TRACE("pdr", tout << result << "\n";);
            return found_instance;
        }
        map<symbol, quantifier*, symbol_hash_proc, symbol_eq_proc> qid_map;
        quantifier* q;
        for (unsigned i = 0; i < qi.quantifiers.size(); ++i) {
            q = qi.quantifiers[i].get();
            qid_map.insert(q->get_qid(), q);
        }

        proof* p = solver.get_proof();
        TRACE("pdr", tout << mk_ismt2_pp(p, mp) << "\n";);
        collect_insts collector(mp);
        for_each_expr(collector, p);
        ptr_vector<quantifier> const& quants = collector.quantifiers();

        for (unsigned i = 0; i < collector.size(); ++i) {
            symbol qid = quants[i]->get_qid();
            if (!qid_map.find(qid, q)) {
                TRACE("pdr", tout << "Could not find quantifier " 
                      << mk_pp(quants[i], mp) << "\n";);
                continue;
            }
            expr_ref_vector const& binding = collector.bindings()[i];

            TRACE("pdr", tout << "Instantiating:\n" << mk_pp(quants[i], mp) << "\n";
                  for (unsigned j = 0; j < binding.size(); ++j) {
                      tout << mk_pp(binding[j], mp) << " ";
                  }
                  tout << "\n";);

            expr_ref_vector new_binding(m);
            for (unsigned j = 0; j < binding.size(); ++j) {
                new_binding.push_back(rev_tr(binding[j]));
            }
            add_binding(q, new_binding);
            found_instance = true;
        }
        if (collector.size() == 0) {
            // Try to create dummy instances.
            for (unsigned i = 0; i < m_Bs.size(); ++i) {
                q = qi.quantifiers[i].get();
                expr_ref_vector binding(m);
                for (unsigned j = 0; j < q->get_num_decls(); ++j) {
                    binding.push_back(m.mk_fresh_const("B", q->get_decl_sort(j)));
                }
                add_binding(q, binding);
            }
            found_instance = true;
        }
        return found_instance;
    }


    void quantifier_model_checker::model_check_node(model_node& node) {
        TRACE("pdr", node.display(tout, 0););
        pred_transformer& pt = node.pt();
        manager& pm = pt.get_pdr_manager();
        expr_ref A(m), B(m), C(m);
        expr_ref_vector As(m);
        m_Bs.reset();
        if (!pt.has_quantifiers()) {
            return;
        }
        //
        // nodes from leaves that are repeated 
        // inside the search tree don't have models.
        //
        if (!node.get_model_ptr()) {
            return;
        }
        m_current_rule = &pt.find_rule(node.get_model());   
        m_current_pt = &pt;
        m_current_node = &node;
        if (!m_current_rule) { 
            return;
        }
        qinst* qi = pt.get_quantifiers(m_current_rule);
        if (!qi) {
            return;
        }        
        unsigned level = node.level();
        unsigned previous_level = (level == 0)?0:(level-1);

        As.push_back(pt.get_propagation_formula(m_ctx.get_pred_transformers(), level));
        As.push_back(node.state());
        As.push_back(pt.rule2tag(m_current_rule));
        m_A = pm.mk_and(As);

        // Add quantifiers:
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        for (unsigned j = 0; j < qi->quantifiers.size(); ++j) {
            quantifier* q = qi->quantifiers[j].get();         
            app* a = to_app(q->get_expr());
            func_decl* f = a->get_decl();
            pred_transformer& pt2 = m_ctx.get_pred_transformer(f);
            B = pt2.get_formulas(previous_level, true);
            TRACE("pdr", tout << mk_pp(B, m) << "\n";);
            
            expr_substitution sub(m);  
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* v = m.mk_const(pm.o2n(pt2.sig(i),0));
                sub.insert(v, a->get_arg(i));
            }
            rep->set_substitution(&sub);
            // TBD: exclude previous bindings here.
            (*rep)(B);
            m_Bs.push_back(B);
            TRACE("pdr", 
                  tout << mk_pp(q, m) << "\n";
                  tout << "propagation formula: " << mk_pp(B, m) << "\n";);
        }
        find_instantiations(*qi, level);
    }

    void quantifier_model_checker::refine(qi& q, datalog::rule_set& rules) {
        IF_VERBOSE(1, verbose_stream() << "instantiating quantifiers\n";);
        datalog::rule_manager& rule_m = rules.get_rule_manager();
        datalog::rule_set new_rules(rules.get_context());
        datalog::rule_set::iterator it = rules.begin(), end = rules.end();
        for (; it != end; ++it) {
            datalog::rule* r = *it;
            app_ref_vector body(m);
            for (unsigned i = 0; i < q.size(); ++i) {
                if (r == q.get_rule(i)) {
                    body.push_back(q.get_app(i));
                }
            }
            if (body.empty()) {
                new_rules.add_rule(r);
            }
            else {
                for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                    body.push_back(r->get_tail(i));
                }
                datalog::rule_ref_vector rules(rule_m);
                expr_ref rule(m.mk_implies(m.mk_and(body.size(), (expr*const*)body.c_ptr()), r->get_head()), m);
                rule_m.mk_rule(rule, rules, r->name());
                for (unsigned i = 0; i < rules.size(); ++i) {
                    new_rules.add_rule(rules[i].get());
                }
            }
        }
        new_rules.close();                  
        rules.reset();
        rules.add_rules(new_rules);
        rules.close();
        m_ctx.update_rules(rules);
        TRACE("pdr", rules.display(tout););
    }
};
