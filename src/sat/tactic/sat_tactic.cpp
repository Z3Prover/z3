/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_tactic.cpp

Abstract:

    Tactic for using the SAT solver and its preprocessing capabilities.
    
Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#include "ast/ast_pp.h"
#include "tactic/tactical.h"
#include "sat/tactic/goal2sat.h"
#include "sat/sat_solver.h"
#include "solver/parallel_tactic.h"
#include "solver/parallel_params.hpp"
#include "model/model_v2_pp.h"

class sat_tactic : public tactic {

    struct imp {
        ast_manager &   m;
        goal2sat        m_goal2sat;
        sat2goal        m_sat2goal;
        sat::solver     m_solver;
        params_ref      m_params;
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_solver(p, m.limit()),
            m_params(p) {
            SASSERT(!m.proofs_enabled());
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result) { 
            fail_if_proof_generation("sat", g);
            bool produce_models = g->models_enabled();
            bool produce_core = g->unsat_core_enabled();
            TRACE("before_sat_solver", g->display(tout););
            g->elim_redundancies();

            atom2bool_var map(m);
            obj_map<expr, sat::literal> dep2asm;
            sat::literal_vector assumptions;
            m_goal2sat(*g, m_params, m_solver, map, dep2asm);
            TRACE("sat_solver_unknown", tout << "interpreted_atoms: " << map.interpreted_atoms() << "\n";
                  for (auto const& kv : map) {
                      if (!is_uninterp_const(kv.m_key))
                          tout << mk_ismt2_pp(kv.m_key, m) << "\n";
                  });
            g->reset();
            g->m().compact_memory();

            CASSERT("sat_solver", m_solver.check_invariant());
            IF_VERBOSE(TACTIC_VERBOSITY_LVL, m_solver.display_status(verbose_stream()););
            TRACE("sat_dimacs", m_solver.display_dimacs(tout););
            dep2assumptions(dep2asm, assumptions);
            lbool r = m_solver.check(assumptions.size(), assumptions.c_ptr());
            if (r == l_false) {
                expr_dependency * lcore = nullptr;
                if (produce_core) {
                    sat::literal_vector const& ucore = m_solver.get_core();
                    u_map<expr*> asm2dep;
                    mk_asm2dep(dep2asm, asm2dep);
                    for (unsigned i = 0; i < ucore.size(); ++i) {
                        sat::literal lit = ucore[i];
                        expr* dep = asm2dep.find(lit.index());
                        lcore = m.mk_join(lcore, m.mk_leaf(dep));                        
                    }
                }
                g->assert_expr(m.mk_false(), nullptr, lcore);
            }
            else if (r == l_true && !map.interpreted_atoms()) {
                // register model
                if (produce_models) {
                    model_ref md = alloc(model, m);
                    sat::model const & ll_m = m_solver.get_model();
                    TRACE("sat_tactic", for (unsigned i = 0; i < ll_m.size(); i++) tout << i << ":" << ll_m[i] << " "; tout << "\n";);
                    for (auto const& kv : map) {
                        expr * n   = kv.m_key;
                        sat::bool_var v = kv.m_value;
                        TRACE("sat_tactic", tout << "extracting value of " << mk_ismt2_pp(n, m) << "\nvar: " << v << "\n";);
                        switch (sat::value_at(v, ll_m)) {
                        case l_true: 
                            md->register_decl(to_app(n)->get_decl(), m.mk_true()); 
                            break;
                        case l_false:
                            md->register_decl(to_app(n)->get_decl(), m.mk_false());
                            break;
                        default:
                            break;
                        }
                    }
                    TRACE("sat_tactic", model_v2_pp(tout, *md););
                    g->add(model2model_converter(md.get()));
                }
            }
            else {
                // get simplified problem.
#if 0
                IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "\"formula constains interpreted atoms, recovering formula from sat solver...\"\n";);
#endif
                m_solver.pop_to_base_level();
                ref<sat2goal::mc> mc;
                m_sat2goal(m_solver, map, m_params, *(g.get()), mc);
                g->add(mc.get());
            }
            g->inc_depth();
            result.push_back(g.get());
        }
        

        void dep2assumptions(obj_map<expr, sat::literal>& dep2asm, 
                             sat::literal_vector& assumptions) {
            for (auto const& kv : dep2asm) {
                assumptions.push_back(kv.m_value);
            }
        }

        void mk_asm2dep(obj_map<expr, sat::literal>& dep2asm,
                        u_map<expr*>& lit2asm) {
            for (auto const& kv : dep2asm) {
                lit2asm.insert(kv.m_value.index(), kv.m_key);
            }
        }
    };
    
    struct scoped_set_imp {
        sat_tactic * m_owner; 

        scoped_set_imp(sat_tactic * o, imp * i):m_owner(o) {
            m_owner->m_imp = i;            
        }
        
        ~scoped_set_imp() {
            m_owner->m_imp = nullptr;
        }
    };

    imp *      m_imp;
    params_ref m_params;
    statistics m_stats;

public:
    sat_tactic(ast_manager & m, params_ref const & p):
        m_imp(nullptr),
        m_params(p) {
    }

    tactic * translate(ast_manager & m) override {
        return alloc(sat_tactic, m, m_params);
    }

    ~sat_tactic() override {
        SASSERT(m_imp == 0);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
    }

    void collect_param_descrs(param_descrs & r) override {
        goal2sat::collect_param_descrs(r);
        sat2goal::collect_param_descrs(r);
        sat::solver::collect_param_descrs(r);
    }
    
    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        imp proc(g->m(), m_params);
        scoped_set_imp set(this, &proc);
        try {
            proc(g, result);
            proc.m_solver.collect_statistics(m_stats);
        }
        catch (sat::solver_exception & ex) {
            proc.m_solver.collect_statistics(m_stats);
            throw tactic_exception(ex.msg());
        }
        TRACE("sat_stats", m_stats.display_smt2(tout););
    }

    void cleanup() override {
        SASSERT(m_imp == 0);
    }

    void collect_statistics(statistics & st) const override {
        st.copy(m_stats);
    }

    void reset_statistics() override {
        m_stats.reset();
    }

protected:

};

tactic * mk_sat_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(sat_tactic, m, p));
}

tactic * mk_sat_preprocessor_tactic(ast_manager & m, params_ref const & p) {
    params_ref p_aux;
    p_aux.set_uint("max_conflicts", 0);
    tactic * t = clean(using_params(mk_sat_tactic(m, p), p_aux));
    t->updt_params(p);
    return t;
}


