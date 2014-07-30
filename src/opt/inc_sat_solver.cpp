
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
    statistics      m_stats;
    unsigned        m_num_scopes;

    typedef obj_map<expr, sat::literal> dep2asm_t;
public:
    inc_sat_solver(ast_manager& m, params_ref const& p):
        m(m), m_solver(p,0), m_params(p),
        m_fmls(m), m_core(m), m_map(m),
        m_num_scopes(0) {
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
                     mk_aig_tactic());
        
        
    }
    
    virtual ~inc_sat_solver() {}
    
    virtual void set_progress_callback(progress_callback * callback) {
    }
    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {        
        m_solver.pop_to_base_level();
        goal_ref_buffer result;
        proof_converter_ref pc;   
        model_converter_ref mc;   
        expr_dependency_ref core(m);
        dep2asm_t dep2asm;
        
        if (!m_fmls.empty() || num_assumptions > 0) {                  
            goal_ref g = alloc(goal, m, true, num_assumptions > 0); // models, maybe cores are enabled
            SASSERT(num_assumptions == 0 || g->unsat_core_enabled());
            SASSERT(g->models_enabled());
            SASSERT(!g->proofs_enabled());
            for (unsigned i = 0; i < m_fmls.size(); ++i) {
                g->assert_expr(m_fmls[i].get());
            }
            for (unsigned i = 0; i < num_assumptions; ++i) {
                g->assert_expr(assumptions[i], m.mk_leaf(assumptions[i]));
            }
            TRACE("opt", g->display(tout););
            m_fmls.reset();
            try {                   
                (*m_preprocess)(g, result, mc, pc, core);
                TRACE("opt", result[0]->display(tout););
            }
            catch (tactic_exception & ex) {
                IF_VERBOSE(0, verbose_stream() << "exception in tactic " << ex.msg() << "\n";);
                m_preprocess->collect_statistics(m_stats);
                return l_undef;                    
            }
            m_mc = concat(m_mc.get(), mc.get());
            if (result.size() != 1) {
                IF_VERBOSE(0, verbose_stream() << "size of result is not 1, it is: " << result.size() << "\n";);
                return l_undef;
            }
            g = result[0];
            TRACE("opt", g->display(tout););
            m_goal2sat(*g, m_params, m_solver, m_map, dep2asm);
        }
        
        lbool r = m_solver.check();
        switch (r) {
        case l_true:
            extract_model();
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
        m_solver.collect_statistics(m_stats);
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
        st.copy(m_stats);
    }
    virtual void get_unsat_core(ptr_vector<expr> & r) {
        r.reset();
        r.append(m_core.size(), m_core.c_ptr());
    }
    virtual void get_model(model_ref & m) {
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

    void extract_core(dep2asm_t& dep2asm) {
        u_map<expr*> asm2dep;
        dep2asm_t::iterator it = dep2asm.begin(), end = dep2asm.end();
        for (; it != end; ++it) {
            asm2dep.insert(it->m_value.index(), it->m_key);
        }
        sat::literal_vector const& core = m_solver.get_core();
        for (unsigned i = 0; i < core.size(); ++i) {
            m_core.push_back(asm2dep.find(core[i].index()));
        }
    }

    void extract_model() {
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
        // IF_VERBOSE(0, model_smt2_pp(verbose_stream(), m, *(m_model.get()), 0););

    }
};

solver* mk_inc_sat_solver(ast_manager& m, params_ref& p) {
    return alloc(inc_sat_solver, m, p);
}
