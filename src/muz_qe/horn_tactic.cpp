/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    horn_tactic.h

Abstract:

    HORN as a tactic to solve Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-16.

Revision History:

--*/
#include"tactical.h"
#include"model_converter.h"
#include"proof_converter.h"
#include"horn_tactic.h"
#include"dl_context.h"

class horn_tactic : public tactic {
    struct imp {
        ast_manager&             m;
        datalog::context         m_ctx;
        smt_params               m_fparams;

        imp(ast_manager & m, params_ref const & p):
            m(m),
            m_ctx(m, m_fparams) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) {
            m_ctx.updt_params(p);
        }

        void collect_param_descrs(param_descrs & r) {
            m_ctx.collect_params(r);
        }

        void reset_statistics() {
            m_ctx.reset_statistics();
        }

        void collect_statistics(statistics & st) const {
            m_ctx.collect_statistics(st);
        }

        void set_cancel(bool f) {
            if (f) {
                m_ctx.cancel();
            }
        }

        void normalize(expr_ref& f) {
            bool is_positive = true;
            expr* e = 0;
            while (true) {
                if (is_forall(f) && is_positive) {
                    f = to_quantifier(f)->get_expr();
                }
                else if (is_exists(f) && !is_positive) {
                    f = to_quantifier(f)->get_expr();                    
                }
                else if (m.is_not(f, e)) {
                    is_positive = !is_positive;
                    f = e;
                }
                else {
                    break;
                }
            }
            if (!is_positive) {
                f = m.mk_not(f);
            }
            
        }

        bool is_predicate(expr* a) {
            SASSERT(m.is_bool(a));
            return is_app(a) && to_app(a)->get_decl()->get_family_id() == null_family_id;
        }

        void register_predicate(expr* a) {
            SASSERT(is_predicate(a));
            m_ctx.register_predicate(to_app(a)->get_decl(), true);
        }

        void check_predicate(ast_mark& mark, expr* a) {
            ptr_vector<expr> todo;
            todo.push_back(a);
            while (!todo.empty()) {
                a = todo.back();
                todo.pop_back();
                if (mark.is_marked(a)) {
                    continue;
                }
                mark.mark(a, true);
                if (is_quantifier(a)) {
                    a = to_quantifier(a)->get_expr();
                    todo.push_back(a);
                }
                else if (m.is_not(a) || m.is_and(a) || m.is_or(a) || m.is_implies(a)) {
                    todo.append(to_app(a)->get_num_args(), to_app(a)->get_args());
                }
                else if (m.is_ite(a)) {
                    todo.append(to_app(a)->get_arg(1));
                    todo.append(to_app(a)->get_arg(2));
                }
                else if (is_predicate(a)) {
                    register_predicate(a);
                }
            }
        }

        enum formula_kind { IS_RULE, IS_QUERY, IS_NONE };

        formula_kind get_formula_kind(expr_ref& f) {
            normalize(f);
            ast_mark mark;
            expr_ref_vector args(m), body(m);
            expr_ref head(m);
            expr* a = 0, *a1 = 0;
            datalog::flatten_or(f, args);
            for (unsigned i = 0; i < args.size(); ++i) {
                a = args[i].get(); 
                check_predicate(mark, a);
                if (m.is_not(a, a1)) {
                    body.push_back(a1);
                }
                else if (is_predicate(a)) {
                    if (head) {
                        return IS_NONE;
                    }
                    head = a;
                }
                else {
                    body.push_back(m.mk_not(a));
                }
            }
            f = m.mk_and(body.size(), body.c_ptr());
            if (head) {
                f = m.mk_implies(f, head);
                return IS_RULE;
            }
            else {
                return IS_QUERY;
            }
        }

        expr_ref mk_rule(expr* body, expr* head) {
            return expr_ref(m.mk_implies(body, head), m);
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("horn", *g);
            bool produce_models = g->models_enabled();
            bool produce_proofs = g->proofs_enabled();

            if (produce_proofs) {
                if (!m_ctx.get_params().generate_proof_trace()) {
                    params_ref params = m_ctx.get_params().p;
                    params.set_bool("generate_proof_trace", true);
                    updt_params(params);
                }
            }

            unsigned sz = g->size();
            expr_ref q(m), f(m);
            expr_ref_vector queries(m);
            std::stringstream msg;

            for (unsigned i = 0; i < sz; i++) {
                f = g->form(i);
                formula_kind k = get_formula_kind(f);
                switch(k) {
                case IS_RULE:
                    m_ctx.add_rule(f, symbol::null);
                    break;
                case IS_QUERY:
                    queries.push_back(f);
                    break;
                default: 
                    msg << "formula is not in Horn fragment: " << mk_pp(g->form(i), m) << "\n";
                    throw tactic_exception(msg.str().c_str());
                }
            }

            if (queries.size() != 1) {
                q = m.mk_fresh_const("query", m.mk_bool_sort());
                register_predicate(q);
                for (unsigned i = 0; i < queries.size(); ++i) {
                    f = mk_rule(queries[i].get(), q);
                    m_ctx.add_rule(f, symbol::null);
                }
                queries.reset();
                queries.push_back(q);
            }
            SASSERT(queries.size() == 1);
            q = queries[0].get();
            lbool is_reachable = m_ctx.query(q);
            g->inc_depth();
            result.push_back(g.get());
            switch (is_reachable) {
            case l_true: {
                // goal is unsat
                g->assert_expr(m.mk_false());
                if (produce_proofs) {
                    proof_ref proof = m_ctx.get_proof();
                    pc = proof2proof_converter(m, proof);
                }
                break;    
            }
            case l_false: {                
                // goal is sat
                g->reset();
                if (produce_models) {
                    model_ref md = m_ctx.get_model();
                    mc = model2model_converter(&*md);
                }
                break;    
            }
            case l_undef: 
                // subgoal is unchanged.
                break;    
            }
            TRACE("horn", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    params_ref m_params;
    imp *      m_imp;
public:
    horn_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(horn_tactic, m, m_params);
    }
        
    virtual ~horn_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

   
    virtual void collect_param_descrs(param_descrs & r) {
        m_imp->collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }

    
    virtual void collect_statistics(statistics & st) const {
        m_imp->collect_statistics(st);
    }

    virtual void reset_statistics() {
        m_imp->reset_statistics();
    }

    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            m_imp = 0;
        }
        dealloc(d);
        d = alloc(imp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }
    
protected:
    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_horn_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(horn_tactic, m, p));
}

