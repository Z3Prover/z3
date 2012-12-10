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
#include "qe.h"
#include "var_subst.h"
#include "dl_rule_set.h"
#include "ast_smt2_pp.h"
#include "model_smt2_pp.h"
#include "ast_smt_pp.h"
#include "expr_abstract.h"
#include "dl_mk_extract_quantifiers.h"
#include "qe_lite.h"
#include "well_sorted.h"
#include "expr_safe_replace.h"


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

    quantifier_model_checker::~quantifier_model_checker() {
        obj_map<func_decl,expr*>::iterator it = m_reachable.begin(), end = m_reachable.end();
        for (; it != end; ++it) {
            m.dec_ref(it->m_value);
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
        if (binding.size() != q->get_num_decls()) {
            // not a full binding. It may happen that the quantifier got simplified.
            return;
        }
        apply_binding(q, binding);
        vector<expr_ref_vector> bindings;
        generalize_binding(binding, bindings);
        for (unsigned i = 0; i < bindings.size(); ++i) {
            apply_binding(q, bindings[i]);
        }
    }
     
    void quantifier_model_checker::apply_binding(quantifier* q, expr_ref_vector& binding) {          
        datalog::scoped_no_proof _scp(m);
        app_ref_vector& var_inst = m_current_pt->get_inst(m_current_rule);
        expr_ref e(m);
        var_subst vs(m, false);
        inv_var_shifter invsh(m);
        vs(q->get_expr(), binding.size(), binding.c_ptr(), e);
        invsh(e, q->get_num_decls(), e);
        expr_ref_vector inst(m);
        inst.append(var_inst.size(), (expr*const*)var_inst.c_ptr());
        inst.reverse();
        expr_abstract(m, 0, inst.size(), inst.c_ptr(), e, e);
        if (m_instantiations.contains(to_app(e))) {
            return;
        }
        m_instantiated_rules.push_back(m_current_rule);
        m_instantiations.push_back(to_app(e));
        TRACE("pdr", tout << mk_pp(q, m) << "\n";
              tout << "binding: ";
              for (unsigned i = 0; i < binding.size(); ++i) {
                  tout << mk_pp(binding[i].get(), m) << " ";
              }
              tout << "\n";
              tout << "inst: ";
              for (unsigned i = 0; i < var_inst.size(); ++i) {
                  tout << mk_pp(var_inst[i].get(), m) << " ";
              }
              tout << "\n";
              tout << mk_pp(e, m) << "\n";
              );
    }


    // As & not Body_i is satisfiable 
    // then instantiate with model for parameters to Body_i

    bool quantifier_model_checker::find_instantiations(quantifier_ref_vector const& qs, unsigned level) {
        return 
            find_instantiations_proof_based(qs, level); // ||
            // find_instantiations_qe_based(qs, level);
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

    bool quantifier_model_checker::find_instantiations_proof_based(quantifier_ref_vector const& qs, unsigned level) {
        bool found_instance = false;
 
        datalog::scoped_fine_proof _scp(m);

        expr_ref_vector fmls(m);
        smt_params fparams;
        SASSERT(m.proofs_enabled());
        fparams.m_mbqi = true;

        fmls.push_back(m_A.get());
        fmls.append(m_Bs);
        TRACE("pdr",
              tout << "assert\n";
              for (unsigned i = 0; i < fmls.size(); ++i) {
                  tout << mk_pp(fmls[i].get(), m) << "\n";
              });

        smt::kernel solver(m, fparams);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            solver.assert_expr(fmls[i].get());
        }
        lbool result = solver.check();

        TRACE("pdr", tout << result << "\n";);

        if (result != l_false) {
            return false;
        }
        m_rules_model_check = false;

        map<symbol, quantifier*, symbol_hash_proc, symbol_eq_proc> qid_map;
        quantifier* q;
        for (unsigned i = 0; i < qs.size();  ++i) {
            q = qs[i];
            qid_map.insert(q->get_qid(), q);
        }

        proof* p = solver.get_proof();
        TRACE("pdr", tout << mk_ismt2_pp(p, m) << "\n";);
        collect_insts collector(m);
        for_each_expr(collector, p);
        ptr_vector<quantifier> const& quants = collector.quantifiers();

        for (unsigned i = 0; i < collector.size(); ++i) {
            symbol qid = quants[i]->get_qid();
            if (!qid_map.find(qid, q)) {
                TRACE("pdr", tout << "Could not find quantifier " << mk_pp(quants[i], m) << "\n";);
                continue;
            }
            expr_ref_vector const& binding = collector.bindings()[i];

            TRACE("pdr", tout << "Instantiating:\n" << mk_pp(quants[i], m) << "\n";
                  for (unsigned j = 0; j < binding.size(); ++j) {
                      tout << mk_pp(binding[j], m) << " ";
                  }
                  tout << "\n";);

            expr_ref_vector new_binding(m);
            for (unsigned j = 0; j < binding.size(); ++j) {
                new_binding.push_back(binding[j]);
            }
            add_binding(q, new_binding);
            found_instance = true;
        }
        return found_instance;
    }


    /**
       For under-approximations:

       m_reachable: set of reachable states, per predicate
       
       rules:       P(x)   :- B[x,y] & Fa z . Q(y,z)
                    Q(y,z) :- C[y,z,u] & Fa w . R(u,w)
       
       qis:         Fa z . Q(y,z)
       
       M:           model satisfying P(x) & B[x,y]
       
       B'[x,y]:     body with reachable states substituted for predicates.
       
       Q'[y,z]:     reachable states substituted for Q.
       
       S'[x]:       Ex y . B'[x,y] & Fa z . Q'[y, z]
       
       Method:

       1. M |= Fa z . Q'[y, z] => done
          
          Weaker variant: 
          Check B[x,y] & Fa z . Q'[y, z] for consistency.

       2. Otherwise, extract instantiations.
      
       3. Update reachable (for next round):

          Q'[y,z] :=  Q'[y,z] \/ C'[y,z,u] & Fa w . R'(u,w)
          
    */


    /**
       For over-approximations:

         - pt - predicate transformer for rule:
                P(x) :- Body1(x,y) || Body2(x,z) & (Fa u . Q(u,x,z)).
         - rule - P(x) :- Body2(x,z)

         - qis - Fa u . Q(u,x,z)

         - A  := node.state(x) && Body2(x,y)


         - Bs := array of Bs of the form:
                 . Fa u . Q(u, P_x, P_y)  - instantiate quantifier to P variables.
                 . B := inv(Q_0,Q_1,Q_2)
                 . B := inv(u, P_x, P_y) := B[u/Q_0, P_x/Q_1, P_y/Q_2]
                 . B := Fa u . inv(u, P_x, P_y)
       
    */

    void quantifier_model_checker::update_reachable(func_decl* f, expr* e) {
        expr* e_old;
        m.inc_ref(e);
        if (m_reachable.find(f, e_old)) {
            m.dec_ref(e_old);
        }
        m_reachable.insert(f, e);
    }


    expr_ref quantifier_model_checker::get_reachable(func_decl* p) {
        expr* e = 0;
        if (!m_reachable.find(p, e)) {
            e = m_ctx.get_pred_transformer(p).initial_state();
            update_reachable(p, e);
        }
        return expr_ref(e, m);
    }

    void quantifier_model_checker::add_over_approximations(quantifier_ref_vector& qis, model_node& n) {
        add_approximations(qis, n, true);
    }

    void quantifier_model_checker::add_under_approximations(quantifier_ref_vector& qis, model_node& n) {
        add_approximations(qis, n, false);
    }
    
    void quantifier_model_checker::add_approximations(quantifier_ref_vector& qis, model_node& n, bool is_over) {
        pred_transformer& pt = n.pt();
        manager& pm = pt.get_pdr_manager();
        unsigned level = n.level();
        expr_ref_vector Bs(m);
        expr_ref B(m), v(m);
        quantifier_ref q(m);
        datalog::scoped_no_proof _no_proof(m);
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        for (unsigned j = 0; j < qis.size(); ++j) {
            q = qis[j].get();
            SASSERT(is_forall(q));
            app_ref_vector& inst      = pt.get_inst(m_current_rule);
            TRACE("pdr", 
                  tout << "q:\n" << mk_pp(q, m) << "\n";
                  tout << "level: " << level << "\n";
                  model_smt2_pp(tout, m, n.get_model(), 0);
                  m_current_rule->display(m_ctx.get_context(), tout << "rule:\n");                  
                  );
            
            var_subst vs(m, false);
            vs(q, inst.size(), (expr*const*)inst.c_ptr(), B);
            q = to_quantifier(B);
            TRACE("pdr", tout << "q instantiated:\n" << mk_pp(q, m) << "\n";);
            
            app* a = to_app(q->get_expr());
            func_decl* f = a->get_decl();
            pred_transformer& pt2 = m_ctx.get_pred_transformer(f);
            if (is_over) {
                B = pt2.get_formulas(level - 1, false);
            }
            else {
                B = get_reachable(f);
                SASSERT(is_well_sorted(m, B));
            }
            TRACE("pdr", tout << "B:\n" << mk_pp(B, m) << "\n";);
                    
            expr_safe_replace sub(m);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                v = m.mk_const(pm.o2n(pt2.sig(i),0));
                sub.insert(v, a->get_arg(i));
            }
            sub(B);
            TRACE("pdr", tout << "B substituted:\n" << mk_pp(B, m) << "\n";);
            datalog::flatten_and(B, Bs);
            for (unsigned i = 0; i < Bs.size(); ++i) {
                m_Bs.push_back(m.update_quantifier(q, Bs[i].get()));                    
            }
        }
    }

    /**
       \brief compute strongest post-conditions for each predicate transformer.
       (or at least something sufficient to change the set of current counter-examples)
     */
    void quantifier_model_checker::weaken_under_approximation() {

        datalog::rule_set::decl2rules::iterator it = m_rules.begin_grouped_rules(), end = m_rules.end_grouped_rules();
        
        for (; it != end; ++it) {
            func_decl* p = it->m_key;
            datalog::rule_vector& rules = *it->m_value;
            expr_ref_vector bodies(m);
            for (unsigned i = 0; i < rules.size(); ++i) {
                bodies.push_back(strongest_post_condition(*rules[i]));
            }           
            update_reachable(p, m.mk_or(bodies.size(), bodies.c_ptr()));
        }
    }

    expr_ref quantifier_model_checker::strongest_post_condition(datalog::rule& r) {
        pred_transformer& pt = m_ctx.get_pred_transformer(r.get_decl());
        manager& pm = pt.get_pdr_manager();
        quantifier_ref_vector* qis = 0;
        m_quantifiers.find(&r, qis);        
        expr_ref_vector body(m), inst(m);
        expr_ref fml(m), v(m);        
        app* a;
        func_decl* p;
        svector<symbol> names;
        unsigned ut_size = r.get_uninterpreted_tail_size();
        unsigned t_size  = r.get_tail_size();   
        var_subst vs(m, false);
        ptr_vector<sort> vars;
        uint_set empty_index_set;
        qe_lite qe(m);

        r.get_vars(vars);
#if 1
        if (qis) {
            quantifier_ref_vector const& qi = *qis;
            for (unsigned i = 0; i < qi.size(); ++i) {
                quantifier* q = qi[i];
                fml = q->get_expr();
                a = to_app(fml);
                p = a->get_decl();
                expr* p_reach = get_reachable(p);
                pred_transformer& pt2 = m_ctx.get_pred_transformer(p);
                expr_safe_replace sub(m);
                for (unsigned j = 0; j < a->get_num_args(); ++j) {
                    v = m.mk_const(pm.o2n(pt2.sig(j),0));
                    sub.insert(v, a->get_arg(j));
                }
                sub(p_reach, fml);
                uint_set is;
                for (unsigned j = 0; j < q->get_num_decls(); ++j) {
                    is.insert(j);
                }
                fml = m.mk_not(fml);
                qe(is, true, fml);
                fml = m.mk_not(fml);
                body.push_back(m.update_quantifier(q, fml));
            }
        }
#endif
        a = r.get_head();
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            v = m.mk_var(vars.size()+i, m.get_sort(a->get_arg(i)));
            body.push_back(m.mk_eq(v, a->get_arg(i)));
        }
        for (unsigned i = 0; i < ut_size; ++i) {
            a = r.get_tail(i);
            p = a->get_decl();
            pred_transformer& pt2 = m_ctx.get_pred_transformer(p);
            expr* p_reach = get_reachable(p);
            expr_safe_replace sub(m);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                v = m.mk_const(pm.o2n(pt2.sig(i),0));
                sub.insert(v, a->get_arg(i));
            }
            sub(p_reach, fml);
            body.push_back(fml);
        }
        for (unsigned i = ut_size; i < t_size; ++i) {
            body.push_back(r.get_tail(i));
        }
        fml = m.mk_and(body.size(), body.c_ptr());
        vars.reverse();
        for (unsigned i = 0; i < vars.size(); ++i) {
            names.push_back(symbol(i));
        }
        if (!vars.empty()) {
            fml = m.mk_exists(vars.size(), vars.c_ptr(), names.c_ptr(), fml);
            SASSERT(is_well_sorted(m, fml));
        }

        for (unsigned i = 0; i < r.get_head()->get_num_args(); ++i) {
            inst.push_back(m.mk_const(pm.o2n(pt.sig(i),0)));
        }
        vs(fml, inst.size(), inst.c_ptr(), fml);
        SASSERT(is_well_sorted(m, fml));
        if (!vars.empty()) {
            fml = to_quantifier(fml)->get_expr();
            qe(empty_index_set, false, fml);
            fml = m.mk_exists(vars.size(), vars.c_ptr(), names.c_ptr(), fml);
            SASSERT(is_well_sorted(m, fml));
            m_ctx.get_context().get_rewriter()(fml);
        }
        SASSERT(is_well_sorted(m, fml));
        
        IF_VERBOSE(0, verbose_stream() << "instantiate to:\n" << mk_pp(fml, m) << "\n";);
        return fml;
    }


    void quantifier_model_checker::model_check_node(model_node& node) {
        TRACE("pdr", node.display(tout, 0););
        pred_transformer& pt = node.pt();
        manager& pm = pt.get_pdr_manager();
        expr_ref A(m), C(m);
        expr_ref_vector As(m);
        m_Bs.reset();
        //
        // nodes from leaves that are repeated 
        // inside the search tree don't have models.
        //
        if (!node.get_model_ptr()) {
            return;
        }
        m_current_rule = node.get_rule();
        m_current_pt = &pt;
        m_current_node = &node;
        if (!m_current_rule) { 
            return;
        }
        
        quantifier_ref_vector* qis = 0;
        m_quantifiers.find(m_current_rule, qis);
        if (!qis) {
            return;
        }
        unsigned level = node.level();
        if (level == 0) {
            return;
        }
        
        As.push_back(pt.get_propagation_formula(m_ctx.get_pred_transformers(), level));
        As.push_back(node.state());
        As.push_back(pt.rule2tag(m_current_rule));
        m_A = pm.mk_and(As);

        // Add quantifiers:
        // add_over_approximations(*qis, node);
        add_under_approximations(*qis, node);

        TRACE("pdr", 
              tout << "A:\n" << mk_pp(m_A, m) << "\n";
              tout << "quantifier:\n";
              for (unsigned i = 0; i < qis->size(); ++i) {
                  tout << mk_pp((*qis)[i].get(), m) << " ";
              }
              tout << "\n";
              tout << "B:\n";
              for (unsigned i = 0; i < m_Bs.size(); ++i) {
                  tout << mk_pp(m_Bs[i].get(), m) << "\n";
              }
              ast_smt_pp pp(m);
              pp.add_assumption(m_A);
              for (unsigned i = 0; i < m_Bs.size(); ++i) {
                  pp.add_assumption(m_Bs[i].get());
              }
              pp.display_smt2(tout, m.mk_true());
              );

        find_instantiations(*qis, level);
    }

    bool quantifier_model_checker::model_check(model_node& root) {
        m_instantiations.reset();
        m_instantiated_rules.reset();
        m_rules_model_check = true;
        ptr_vector<model_node> nodes;
        get_nodes(root, nodes);
        for (unsigned i = nodes.size(); i > 0; ) {
            --i;
            model_check_node(*nodes[i]);
        }
        if (!m_rules_model_check) {
            weaken_under_approximation();
        }
        return m_rules_model_check;
    }

    void quantifier_model_checker::refine() {
        datalog::mk_extract_quantifiers eq(m_ctx.get_context());
        datalog::rule_manager& rm = m_rules.get_rule_manager();
        datalog::rule_set new_rules(m_rules.get_context());
        datalog::rule_set::iterator it = m_rules.begin(), end = m_rules.end();
        for (; it != end; ++it) {
            datalog::rule* r = *it;
            datalog::var_counter vc(true);
            unsigned max_var = vc.get_max_var(*r);
            app_ref_vector body(m);
            for (unsigned i = 0; i < m_instantiations.size(); ++i) {
                if (r == m_instantiated_rules[i]) {
                    eq.ensure_predicate(m_instantiations[i].get(), max_var, body);
                }
            }
            if (body.empty()) {
                new_rules.add_rule(r);
            }
            else {
                for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                    body.push_back(r->get_tail(i));
                }
                quantifier_ref_vector* qs = 0;
                m_quantifiers.find(r, qs);
                m_quantifiers.remove(r);                
                datalog::rule_ref new_rule(rm);
                new_rule = rm.mk(r->get_head(), body.size(), body.c_ptr(), 0, r->name(), false);
                new_rules.add_rule(new_rule);
                m_quantifiers.insert(new_rule, qs);
                IF_VERBOSE(1, 
                           verbose_stream() << "instantiating quantifiers\n";                           
                           r->display(m_ctx.get_context(), verbose_stream());
                           verbose_stream() << "replaced by\n";
                           new_rule->display(m_ctx.get_context(), verbose_stream()););
            }
        }
        new_rules.close();
        m_rules.reset();
        m_rules.add_rules(new_rules);
        m_rules.close();
        m_ctx.update_rules(m_rules);
        TRACE("pdr", m_rules.display(tout););
    }

    bool quantifier_model_checker::check() {
        if (model_check(m_ctx.get_root())) {
            return true;
        }
        refine();
        return false;
    }
};

