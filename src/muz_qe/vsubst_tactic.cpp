/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    vsubst_tactic.cpp

Abstract:

    Check satisfiability of QF_NRA problems using virtual subsititution quantifier-elimination.

Author:

    Nikolaj (nbjorner) 2011-05-16

Notes:
  Ported to tactic framework on 2012-02-28
  It was qfnra_vsubst.cpp

  This goal transformation checks satsifiability
  of quantifier-free non-linear constraints using
  virtual substitutions (applies to second-degree polynomials).
  . identify non-linear variables
  . use the identified variables as non-linear variables.
  . give up if there are non-linear variables under uninterpreted scope.
    give up if there are no non-linear variables.
  . call quantifier elimination with 
      - non-linear elimination option.
      - get-first-branch option.
  . if the first branch is linear, then done.
    if the result is unsat, then done.
    if the first branch is non-linear then, 
    check candidate model,
    perhaps iterate using rewriting or just give up.

  . helpful facilities: 
    . linearize_rewriter 
        a*a*b + a*b = 0 <=> (b+1) = 0 \/ a = 0 \/ b = 0
    . sign analysis:
        a*a + b*b + c < 0  => c < 0

--*/
#include"tactic.h"
#include"qe.h"
#include"arith_decl_plugin.h"
#include"for_each_expr.h"
#include"extension_model_converter.h"
#include"ast_smt2_pp.h"

class vsubst_tactic : public tactic {
    params_ref m_params;

    class get_var_proc {
        arith_util       m_arith;
        ptr_vector<app>& m_vars;
    public:
        get_var_proc(ast_manager & m, ptr_vector<app>& vars) : m_arith(m), m_vars(vars) {}
        
        void operator()(expr* e) {
            if (is_app(e)) {
                app* a = to_app(e);
                if (m_arith.is_real(e) &&
                    a->get_num_args() == 0 &&
                    a->get_family_id() == null_family_id) {
                    m_vars.push_back(a);
                }
            }
        }
    };

    void get_vars(ast_manager & m, expr* fml, ptr_vector<app>& vars) {
        get_var_proc proc(m, vars);
        for_each_expr(proc, fml);        
    }

    void main(goal & s, model_converter_ref & mc, params_ref const & p) {
        ast_manager & m = s.m();

        ptr_vector<expr> fs;
        for (unsigned i = 0; i < s.size(); ++i) {
            fs.push_back(s.form(i));
        }
        app_ref f(m.mk_and(fs.size(), fs.c_ptr()), m);
        TRACE("vsubst", 
              s.display(tout);
              tout << "goal: " << mk_ismt2_pp(f.get(), m) << "\n";);
        ptr_vector<app> vars;
        get_vars(m, f.get(), vars);
        
        if (vars.empty()) {
            TRACE("vsubst", tout << "no real variables\n";);
            throw tactic_exception("there are no real variables");
        }

        smt_params params;
        params.updt_params(p);
        params.m_model = false;
        flet<bool> fl1(params.m_nlquant_elim, true);
        flet<bool> fl2(params.m_nl_arith_gb, false);
        TRACE("quant_elim", tout << "Produce models: " << params.m_model << "\n";);

        qe::expr_quant_elim_star1 qelim(m, params);
        expr_ref g(f, m);
        qe::def_vector defs(m);
        lbool is_sat = qelim.first_elim(vars.size(), vars.c_ptr(), g, defs);
        if (is_sat == l_undef) {
            TRACE("vsubst", tout << mk_ismt2_pp(g, m) << "\n";);
            throw tactic_exception("elimination was not successful");
        }
        if (!defs.empty()) {
            extension_model_converter * ev = alloc(extension_model_converter, m);
            mc = ev;
            for (unsigned i = defs.size(); i > 0; ) {
                --i;
                ev->insert(defs.var(i), defs.def(i));
            }
        }
        
        s.reset();
        // TBD: wasteful as we already know it is sat or unsat.
        // TBD: extract model from virtual substitution.
        s.assert_expr(g);

        TRACE("qfnra_vsubst", 
              tout << "v-subst result:\n";
              s.display(tout););
    }


public:
    vsubst_tactic(params_ref const & p):m_params(p) {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(vsubst_tactic, m_params);
    }

    virtual ~vsubst_tactic() {}
    
    virtual void updt_params(params_ref const & p) {
        m_params = p;
    }

    /**
       \brief Check satisfiability of an assertion set of QF_NRA
       by using virtual substitutions.
    */
    virtual void operator()(goal_ref const & g,
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        fail_if_proof_generation("vsubst", g);
        fail_if_unsat_core_generation("vsubst", g);
        fail_if_model_generation("vsubst", g); // disable for now due to problems with infinitesimals.
        mc = 0; pc = 0; core = 0; result.reset();
        
        main(*(g.get()), mc, m_params);
        
        result.push_back(g.get());
        SASSERT(g->is_well_sorted());
    }

    virtual void cleanup(void) {}
};

tactic * mk_vsubst_tactic(ast_manager & m, params_ref const & p) {
    return alloc(vsubst_tactic, p);
}
