/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_tactic.cpp

Abstract:

    Tactic for using nonlinear procedure.

Author:

    Leonardo (leonardo) 2012-01-02

Notes:

--*/
#include"tactical.h"
#include"goal2nlsat.h"
#include"nlsat_solver.h"
#include"model.h"
#include"expr2var.h"
#include"arith_decl_plugin.h"
#include"ast_smt2_pp.h"
#include"z3_exception.h"
#include"algebraic_numbers.h"

class nlsat_tactic : public tactic {
    struct expr_display_var_proc : public nlsat::display_var_proc {
        ast_manager & m;
        expr_ref_vector m_var2expr;
        expr_display_var_proc(ast_manager & _m):m(_m), m_var2expr(_m) {}
        virtual void operator()(std::ostream & out, nlsat::var x) const { 
            if (x < m_var2expr.size())
                out << mk_ismt2_pp(m_var2expr.get(x), m); 
            else
                out << "x!" << x;
        }
    };

    struct     imp {
        ast_manager &         m;
        params_ref            m_params;
        expr_display_var_proc m_display_var;
        nlsat::solver         m_solver;
        goal2nlsat            m_g2nl;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_params(p),
            m_display_var(_m),
            m_solver(m.limit(), p) {
        }
        
        void updt_params(params_ref const & p) {
            m_params = p;
            m_solver.updt_params(p);
        }
        
        bool contains_unsupported(expr_ref_vector & b2a, expr_ref_vector & x2t) {
            for (unsigned x = 0; x < x2t.size(); x++) {
                if (!is_uninterp_const(x2t.get(x))) {
                    TRACE("unsupported", tout << "unsupported atom:\n" << mk_ismt2_pp(x2t.get(x), m) << "\n";);
                    return true;
                }
            }
            for (unsigned b = 0; b < b2a.size(); b++) {
                expr * a = b2a.get(b);
                if (a == 0)
                    continue;
                if (is_uninterp_const(a))
                    continue;
                if (m_solver.is_interpreted(b))
                    continue; // arithmetic atom
                TRACE("unsupported", tout << "unsupported atom:\n" << mk_ismt2_pp(a, m) << "\n";);
                return true; // unsupported
            }
            return false;
        }
        
        // Return false if nlsat assigned noninteger value to an integer variable.
        bool mk_model(expr_ref_vector & b2a, expr_ref_vector & x2t, model_converter_ref & mc) {
            bool ok = true;
            model_ref md = alloc(model, m);
            arith_util util(m);
            for (unsigned x = 0; x < x2t.size(); x++) {
                expr * t = x2t.get(x);
                if (!is_uninterp_const(t))
                    continue;
                expr * v;
                try {
                    v = util.mk_numeral(m_solver.value(x), util.is_int(t));
                }
                catch (z3_error & ex) {
                    throw ex;
                }
                catch (z3_exception &) {
                    v = util.mk_to_int(util.mk_numeral(m_solver.value(x), false));
                    ok = false;
                }
                md->register_decl(to_app(t)->get_decl(), v);
            }
            for (unsigned b = 0; b < b2a.size(); b++) {
                expr * a = b2a.get(b);
                if (a == 0 || !is_uninterp_const(a))
                    continue;
                lbool val = m_solver.bvalue(b);
                if (val == l_undef)
                    continue; // don't care
                md->register_decl(to_app(a)->get_decl(), val == l_true ? m.mk_true() : m.mk_false());
            }
            mc = model2model_converter(md.get());
            return ok;
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("nlsat", *g);
            
            if (g->is_decided()) {
                result.push_back(g.get());
                return;
            }

            fail_if_proof_generation("nlsat", g);

            TRACE("nlsat", g->display(tout););
            expr2var  a2b(m);
            expr2var  t2x(m);
            m_g2nl(*g, m_params, m_solver, a2b, t2x);

            m_display_var.m_var2expr.reset();
            t2x.mk_inv(m_display_var.m_var2expr);
            m_solver.set_display_var(m_display_var);
            
            lbool st = m_solver.check();
            
            if (st == l_undef) {
            }
            else if (st == l_true) {
                expr_ref_vector x2t(m);
                expr_ref_vector b2a(m);
                a2b.mk_inv(b2a);
                t2x.mk_inv(x2t);
                if (!contains_unsupported(b2a, x2t)) {
                    // If mk_model is false it means that the model produced by nlsat 
                    // assigns noninteger values to integer variables
                    if (mk_model(b2a, x2t, mc)) {
                        // result goal is trivially SAT
                        g->reset(); 
                    }
                }
            }
            else {
                // TODO: extract unsat core
                g->assert_expr(m.mk_false(), 0, 0);
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("nlsat", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
    statistics m_stats;
    
    struct scoped_set_imp {
        nlsat_tactic & m_owner; 
        scoped_set_imp(nlsat_tactic & o, imp & i):m_owner(o) {
            m_owner.m_imp = &i;            
        }

        ~scoped_set_imp() {
            m_owner.m_imp->m_solver.collect_statistics(m_owner.m_stats);
            m_owner.m_imp = 0;
        }
    };

public:
    nlsat_tactic(params_ref const & p):
        m_params(p) {
        m_imp = 0;
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(nlsat_tactic, m_params);
    }
        
    virtual ~nlsat_tactic() {
        SASSERT(m_imp == 0);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
    }

    virtual void collect_param_descrs(param_descrs & r) {
        goal2nlsat::collect_param_descrs(r);
        nlsat::solver::collect_param_descrs(r);
        algebraic_numbers::manager::collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            imp local_imp(in->m(), m_params);
            scoped_set_imp setter(*this, local_imp);
            local_imp(in, result, mc, pc, core);
        }
        catch (z3_error & ex) {
            throw ex;
        }
        catch (z3_exception & ex) {
            // convert all Z3 exceptions into tactic exceptions.
            throw tactic_exception(ex.msg());
        }
    }
    
    virtual void cleanup() {}
    
    virtual void collect_statistics(statistics & st) const {
        st.copy(m_stats);
    }

    virtual void reset_statistics() {
        m_stats.reset();
    }
};

tactic * mk_nlsat_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(nlsat_tactic, p));
}

