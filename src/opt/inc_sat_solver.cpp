/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    inc_sat_solver.cpp

Abstract:

    incremental solver based on SAT core.

Author:

    Nikolaj Bjorner (nbjorner) 2014-7-30

Notes:

--*/

#include "solver.h"
#include "tactical.h"
#include "sat_solver.h"
#include "tactic2solver.h"
#include "nnf_tactic.h"
#include "aig_tactic.h"
#include "propagate_values_tactic.h"
#include "max_bv_sharing_tactic.h"
#include "card2bv_tactic.h"
#include "bit_blaster_tactic.h"
#include "simplify_tactic.h"
#include "goal2sat.h"
#include "ast_pp.h"

// incremental SAT solver.
class inc_sat_solver : public solver {
    ast_manager&    m;
    sat::solver     m_solver;
    goal2sat        m_goal2sat;
    params_ref      m_params;
    expr_ref_vector m_fmls;
    expr_ref_vector m_core;
    atom2bool_var   m_map;
    model_ref       m_model;
    model_converter_ref m_mc;   
    tactic_ref      m_preprocess;
    unsigned        m_num_scopes;
    sat::literal_vector m_asms;
    goal_ref_buffer     m_subgoals;
    proof_converter_ref m_pc;   
    model_converter_ref m_mc2;   
    expr_dependency_ref m_dep_core;


    typedef obj_map<expr, sat::literal> dep2asm_t;
public:
    inc_sat_solver(ast_manager& m, params_ref const& p):
        m(m), m_solver(p,0), m_params(p),
        m_fmls(m), m_core(m), m_map(m),
        m_num_scopes(0), 
        m_dep_core(m) {
        m_params.set_bool("elim_vars", false);
        m_solver.updt_params(m_params);
        params_ref simp2_p = p;
        simp2_p.set_bool("som", true);
        simp2_p.set_bool("pull_cheap_ite", true);
        simp2_p.set_bool("push_ite_bv", false);
        simp2_p.set_bool("local_ctx", true);
        simp2_p.set_uint("local_ctx_limit", 10000000);
        simp2_p.set_bool("flat", true); // required by som
        simp2_p.set_bool("hoist_mul", false); // required by som
        m_preprocess = 
            and_then(mk_card2bv_tactic(m, m_params),
                     mk_simplify_tactic(m),
                     mk_propagate_values_tactic(m),
                     using_params(mk_simplify_tactic(m), simp2_p),
                     mk_max_bv_sharing_tactic(m),
                     mk_bit_blaster_tactic(m), 
                     mk_aig_tactic(),
                     using_params(mk_simplify_tactic(m), simp2_p));
        
        
    }
    
    virtual ~inc_sat_solver() {}
    
    virtual void set_progress_callback(progress_callback * callback) {
    }
    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {        
        m_solver.pop_to_base_level();
        dep2asm_t dep2asm;

        m_model = 0;
        lbool r = internalize_formulas();
        if (r != l_true) return r;
        r = internalize_assumptions(num_assumptions, assumptions, dep2asm);
        if (r != l_true) return r;
        extract_assumptions(dep2asm, m_asms);
        r = m_solver.check(m_asms.size(), m_asms.c_ptr());
        switch (r) {
        case l_true:
            check_assumptions(dep2asm);
            break;
        case l_false:
            // TBD: expr_dependency core is not accounted for.
            if (num_assumptions > 0) {
                extract_core(dep2asm);
            }
            break;
        default:
            break;
        }
        return r;
    }
    virtual void set_cancel(bool f) {
        m_goal2sat.set_cancel(f);
        m_solver.set_cancel(f);
        m_preprocess->set_cancel(f);
    }
    virtual void push() {
        m_solver.user_push();
        ++m_num_scopes;
    }
    virtual void pop(unsigned n) {
        if (n < m_num_scopes) {   // allow inc_sat_solver to 
            n = m_num_scopes;     // take over for another solver.
        }
        SASSERT(n >= m_num_scopes);
        m_solver.user_pop(n);
        m_num_scopes -= n;
    }
    virtual unsigned get_scope_level() const {
        return m_num_scopes;
    }
    virtual void assert_expr(expr * t, expr * a) {
        if (a) {
            m_fmls.push_back(m.mk_implies(a, t));
        }
        else {
            m_fmls.push_back(t);
        }
    }
    virtual void assert_expr(expr * t) {
        m_fmls.push_back(t);
    }
    virtual void set_produce_models(bool f) {}
    virtual void collect_param_descrs(param_descrs & r) {
        goal2sat::collect_param_descrs(r);
        sat::solver::collect_param_descrs(r);
    }
    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_params.set_bool("elim_vars", false);
        m_solver.updt_params(m_params);
    }
    
    virtual void collect_statistics(statistics & st) const {
        m_preprocess->collect_statistics(st);
        m_solver.collect_statistics(st);
    }
    virtual void get_unsat_core(ptr_vector<expr> & r) {
        r.reset();
        r.append(m_core.size(), m_core.c_ptr());
    }
    virtual void get_model(model_ref & m) {
        if (!m_model.get()) {
            extract_model();
        }
        m = m_model;
    }
    virtual proof * get_proof() {
        UNREACHABLE();
        return 0;
    }
    virtual std::string reason_unknown() const {
        return "no reason given";
    }
    virtual void get_labels(svector<symbol> & r) {
        UNREACHABLE();
    }

private:

    lbool internalize_goal(goal_ref& g, dep2asm_t& dep2asm) {
        m_mc2.reset();
        m_pc.reset();
        m_dep_core.reset();
        m_subgoals.reset();
        SASSERT(g->models_enabled());
        SASSERT(!g->proofs_enabled());
        TRACE("opt", g->display(tout););
        try {                   
            (*m_preprocess)(g, m_subgoals, m_mc2, m_pc, m_dep_core);
        }
        catch (tactic_exception & ex) {
            IF_VERBOSE(0, verbose_stream() << "exception in tactic " << ex.msg() << "\n";);
            return l_undef;                    
        }
        m_mc = concat(m_mc.get(), m_mc2.get());
        if (m_subgoals.size() != 1) {
            IF_VERBOSE(0, verbose_stream() << "size of subgoals is not 1, it is: " << m_subgoals.size() << "\n";);
            return l_undef;
        }
        g = m_subgoals[0];
        TRACE("opt", g->display_with_dependencies(tout););
        m_goal2sat(*g, m_params, m_solver, m_map, dep2asm, true);
        return l_true;
    }

    lbool internalize_assumptions(unsigned sz, expr* const* asms, dep2asm_t& dep2asm) {
        if (sz == 0) {
            return l_true;
        }
        goal_ref g = alloc(goal, m, true, true); // models and cores are enabled.
        for (unsigned i = 0; i < sz; ++i) {
            g->assert_expr(asms[i], m.mk_leaf(asms[i]));
        }
        return internalize_goal(g, dep2asm);
    }

    lbool internalize_formulas() {
        if (m_fmls.empty()) {
            return l_true;
        }
        dep2asm_t dep2asm;
        goal_ref g = alloc(goal, m, true, false); // models, maybe cores are enabled
        for (unsigned i = 0; i < m_fmls.size(); ++i) {
            g->assert_expr(m_fmls[i].get());
        }
        m_fmls.reset();
        return internalize_goal(g, dep2asm);
    }

    void extract_assumptions(dep2asm_t& dep2asm, sat::literal_vector& asms) {
        asms.reset();
        dep2asm_t::iterator it = dep2asm.begin(), end = dep2asm.end();
        for (; it != end; ++it) {
            asms.push_back(it->m_value);
        }
    }

    void extract_core(dep2asm_t& dep2asm) {
        u_map<expr*> asm2dep;
        dep2asm_t::iterator it = dep2asm.begin(), end = dep2asm.end();
        for (; it != end; ++it) {
            asm2dep.insert(it->m_value.index(), it->m_key);
        }
        sat::literal_vector const& core = m_solver.get_core();

        m_core.reset();
        for (unsigned i = 0; i < core.size(); ++i) {
            expr* e;
            if (asm2dep.find(core[i].index(), e)) {
                if (core[i].sign()) {
                    e = m.mk_not(e);
                }
                m_core.push_back(e);
            }
        }
        TRACE("opt",
              dep2asm_t::iterator it = dep2asm.begin();
              dep2asm_t::iterator end = dep2asm.end();
              for (; it != end; ++it) {
                  tout << mk_pp(it->m_key, m) << " |-> " << it->m_value << "\n";
              }
              tout << "core: ";
              for (unsigned i = 0; i < core.size(); ++i) {
                  tout << core[i] << ": " << mk_pp(m_core[i].get(), m) << " ";
              }
              tout << "\n";
              );              


    }

    void check_assumptions(dep2asm_t& dep2asm) {
        sat::model const & ll_m = m_solver.get_model();
        dep2asm_t::iterator it = dep2asm.begin(), end = dep2asm.end();
        for (; it != end; ++it) {
            sat::literal lit = it->m_value;
            lbool polarity = lit.sign()?l_false:l_true;
            lbool value = sat::value_at(lit.var(), ll_m); 
            if (value != polarity) {
                std::cout << mk_pp(it->m_key, m) << " evaluates to " << value << "\n";
                std::cout << m_asms << "\n";
                m_solver.display_assignment(std::cout);
                // m_solver.display(std::cout);
                throw default_exception("bad state");
            }
        }
    }

    // TBD: this is super-expensive because of the
    // bit-blasting model converter.

    void extract_model() {
        TRACE("sat", tout << "retrieve model\n";);
        model_ref md = alloc(model, m);
        sat::model const & ll_m = m_solver.get_model();
        atom2bool_var::iterator it  = m_map.begin();
        atom2bool_var::iterator end = m_map.end();
        for (; it != end; ++it) {
            expr * n   = it->m_key;
            if (is_app(n) && to_app(n)->get_num_args() > 0) {
                continue;
            }
            sat::bool_var v = it->m_value;
            // std::cout << mk_pp(n, m) << " -> " << sat::value_at(v, ll_m) << "\n";
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
        m_model = md;
        if (m_mc) {
            (*m_mc)(m_model);
        }
        SASSERT(m_model);
        // IF_VERBOSE(0, model_smt2_pp(verbose_stream(), m, *(m_model.get()), 0););

    }
};

solver* mk_inc_sat_solver(ast_manager& m, params_ref& p) {
    return alloc(inc_sat_solver, m, p);
}
