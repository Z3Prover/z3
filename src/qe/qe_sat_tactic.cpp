/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qe_sat_tactic.cpp

Abstract:

    Procedure for quantifier satisfiability using quantifier projection.
    Based on generalizations by Bjorner & Monniaux 
    (see tvm\papers\z3qe\altqe.tex)

Author:

    Nikolaj Bjorner (nbjorner) 2012-02-24

Revision History:


--*/

#include "qe/qe_sat_tactic.h"
#include "ast/rewriter/quant_hoist.h"
#include "ast/ast_pp.h"
#include "smt/smt_kernel.h"
#include "qe/qe.h"
#include "model/model_v2_pp.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/expr_context_simplifier.h"

// plugin registration.
// solver specific projection operators.
// connect goals to tactic

namespace qe {

    class is_relevant_default : public i_expr_pred {
    public:
        bool operator()(expr* e) override {
            return true;
        }
    };

    class mk_atom_default : public i_nnf_atom {
    public:
        void operator()(expr* e, bool pol, expr_ref& result) override {
            if (pol) result = e; 
            else result = result.get_manager().mk_not(e);
        }
    };

    class sat_tactic : public tactic {

        // forall x . not forall y . not forall z . not forall u . fml.

        ast_manager&            m;
        expr_ref                m_false;
        smt_params              m_fparams;
        params_ref              m_params;
        unsigned                m_extrapolate_strategy_param;
        bool                    m_projection_mode_param;
        bool                    m_strong_context_simplify_param;
        bool                    m_ctx_simplify_local_param;
        vector<app_ref_vector>  m_vars;
        ptr_vector<smt::kernel> m_solvers;
        vector<smt_params>      m_fparamv;
        smt::kernel             m_solver;
        expr_ref                m_fml;
        expr_ref_vector         m_Ms;
        expr_ref_vector         m_assignments;
        is_relevant_default     m_is_relevant;
        mk_atom_default         m_mk_atom;
        th_rewriter             m_rewriter;
        simplify_rewriter_star  m_qe_rw;
        expr_strong_context_simplifier m_ctx_rewriter;

        class solver_context : public i_solver_context {
 
            ast_manager&   m;
            sat_tactic&    m_super;
            smt::kernel&   m_solver;
            atom_set       m_pos;
            atom_set       m_neg;
            app_ref_vector m_vars;
            expr_ref       m_fml;
            ptr_vector<contains_app> m_contains_app; 
            bool           m_projection_mode_param;
        public:
            solver_context(sat_tactic& s, unsigned idx):                 
                m(s.m),
                m_super(s), 
                m_solver(*s.m_solvers[idx+1]),
                m_vars(m), 
                m_fml(m),
                m_projection_mode_param(true) {}

            ~solver_context() override {
                std::for_each(m_contains_app.begin(), m_contains_app.end(), delete_proc<contains_app>());
            }

            void init(expr* fml, unsigned idx) {
                m_fml = fml;
                for (unsigned j = 0; j < m_super.vars(idx).size(); ++j) {
                    add_var(m_super.vars(idx)[j]);
                }
                get_nnf(m_fml, get_is_relevant(), get_mk_atom(), m_pos, m_neg);
            }

            void set_projection_mode(bool p) { m_projection_mode_param = p; }

            ast_manager& get_manager() override { return m; }

            expr* fml() { return m_fml; }

            // set of atoms in current formula.
            atom_set const& pos_atoms() const override { return m_pos; }
            atom_set const& neg_atoms() const override { return m_neg; }
            
            // Access current set of variables to solve
            unsigned      get_num_vars() const override { return m_vars.size(); }
            app*          get_var(unsigned idx) const override { return m_vars[idx]; }
            app_ref_vector const& get_vars() const override { return m_vars; }
            bool          is_var(expr* e, unsigned& idx) const override {
                for (unsigned i = 0; i < m_vars.size(); ++i) {
                    if (e == m_vars[i]) return (idx = i, true);
                }
                return false;
            }
            contains_app& contains(unsigned idx) override { return *m_contains_app[idx]; }

            // callback to replace variable at index 'idx' with definition 'def' and updated formula 'fml'
            void elim_var(unsigned idx, expr* fml, expr* def) override {
                m_fml = fml;
                m_pos.reset();
                m_neg.reset();
                get_nnf(m_fml, get_is_relevant(), get_mk_atom(), m_pos, m_neg);
                m_vars.erase(idx);
                dealloc(m_contains_app[idx]);
                m_contains_app.erase(m_contains_app.c_ptr() + idx);
            }
            
            // callback to add new variable to branch.
            void add_var(app* x) override {
                m_vars.push_back(x);
                m_contains_app.push_back(alloc(contains_app, m, x)); 
            }
            
            // callback to add constraints in branch.
            void add_constraint(bool use_var, expr* l1 = nullptr, expr* l2 = nullptr, expr* l3 = nullptr) override {
                ptr_buffer<expr> args;
                if (l1) args.push_back(l1);
                if (l2) args.push_back(l2);
                if (l3) args.push_back(l3);
                expr_ref cnstr(m.mk_or(args.size(), args.c_ptr()), m);
                m_solver.assert_expr(cnstr);
                TRACE("qe", tout << "add_constraint " << mk_pp(cnstr,m) << "\n";);
            }
            
            // eliminate finite domain variable 'var' from fml.
            void blast_or(app* var, expr_ref& fml) override {
                expr_ref result(m);
                expr_quant_elim qelim(m, m_super.m_fparams);
                qe::mk_exists(1, &var, fml);
                qelim(m.mk_true(), fml, result);
                fml = result;
                TRACE("qe", tout << mk_pp(var, m) << " " << mk_pp(fml, m) << "\n";);
            }

            void project_var_partial(unsigned i) {
                app* x = get_var(i);
                m_super.check_success(has_plugin(x));
                qe_solver_plugin& p = plugin(m.get_sort(x)->get_family_id());
                model_ref model;
                m_solver.get_model(model);                
                m_super.check_success(p.project(contains(i), model, m_fml));
                m_super.m_rewriter(m_fml);
                TRACE("qe", model_v2_pp(tout, *model); tout << "\n";
                      tout << mk_pp(m_fml, m) << "\n";);
                elim_var(i, m_fml, nullptr);
            }

            void project_var_full(unsigned i) {
                expr_ref result(m);
                app* x = get_var(i);
                expr_quant_elim qelim(m, m_super.m_fparams);
                qe::mk_exists(1, &x, m_fml);
                qelim(m.mk_true(), m_fml, result);
                m_fml = result;
                m_super.m_rewriter(m_fml);
                TRACE("qe", tout << mk_pp(m_fml, m) << "\n";);
                elim_var(i, m_fml, nullptr);
            }

            void project_var(unsigned i) {
                if (m_projection_mode_param) {
                    project_var_full(i);
                }
                else {
                    project_var_partial(i);
                }
            }            
        };

    public:
        sat_tactic(ast_manager& m, params_ref const& p = params_ref()):
            m(m),
            m_false(m.mk_false(), m),
            m_params(p),
            m_extrapolate_strategy_param(0),
            m_projection_mode_param(true),
            m_strong_context_simplify_param(true),
            m_ctx_simplify_local_param(false),
            m_solver(m, m_fparams),
            m_fml(m),
            m_Ms(m),
            m_assignments(m),
            m_rewriter(m),
            m_qe_rw(m),
            m_ctx_rewriter(m_fparams, m) {            
            m_fparams.m_model = true;
        }

        tactic * translate(ast_manager & m) override {
            return alloc(sat_tactic, m);
        }

        ~sat_tactic() override {
            reset();
        }

        void operator()(goal_ref const& goal, goal_ref_buffer& result) override {
            try {
                checkpoint();
                reset();            
                ptr_vector<expr> fmls;
                goal->get_formulas(fmls);
                m_fml = m.mk_and(fmls.size(), fmls.c_ptr());
                TRACE("qe", tout << "input: " << mk_pp(m_fml,m) << "\n";);               
                expr_ref tmp(m);
                m_qe_rw(m_fml, tmp);
                m_fml = tmp;
                TRACE("qe", tout << "reduced: " << mk_pp(m_fml,m) << "\n";);
                skolemize_existential_prefix();
                extract_alt_form(m_fml);
                model_ref model;
                expr_ref res = qt(0, m.mk_true(), model);
                goal->inc_depth();
                if (m.is_false(res)) {
                    goal->assert_expr(res);
                }
                else {
                    goal->reset();
                    // equi-satisfiable. What to do with model?
                    goal->add(model2model_converter(&*model));
                }
                result.push_back(goal.get());
            }
            catch (rewriter_exception & ex) {
                throw tactic_exception(ex.msg());
            }
        }

        void collect_statistics(statistics & st) const override {
            for (auto const * s : m_solvers) {
                s->collect_statistics(st);
            }
            m_solver.collect_statistics(st);
            m_ctx_rewriter.collect_statistics(st);
        }

        void reset_statistics() override {
            for (auto * s : m_solvers) {
                s->reset_statistics();
            }            
            m_solver.reset_statistics();
            m_ctx_rewriter.reset_statistics();
        }

        void cleanup() override {}

        void updt_params(params_ref const & p) override {
            m_extrapolate_strategy_param = p.get_uint("extrapolate_strategy", m_extrapolate_strategy_param);
            m_projection_mode_param = p.get_bool("projection_mode", m_projection_mode_param);
            m_strong_context_simplify_param = p.get_bool("strong_context_simplify", m_strong_context_simplify_param);
            m_ctx_simplify_local_param = p.get_bool("strong_context_simplify_local", m_ctx_simplify_local_param);
            m_fparams.updt_params(p);
            m_qe_rw.updt_params(p);
        }

        void collect_param_descrs(param_descrs & r) override {
            r.insert("extrapolate_strategy",CPK_UINT, "(default: 0 trivial extrapolation) 1 - nnf strengthening 2 - smt-test 3 - nnf_weakening");
            r.insert("projection_mode", CPK_BOOL, "(default: true - full) false - partial quantifier instantiation");
            r.insert("strong_context_simplify", CPK_BOOL, "(default: true) use strong context simplifier on result of quantifier elimination");
            r.insert("strong_context_simplify_local", CPK_BOOL, "(default: false) use strong context simplifier locally on the new formula only");
        }


    private:
                        
        unsigned num_alternations() const { return m_vars.size(); }
            
        void init_Ms() {
            for (unsigned i = 0; i <= num_alternations(); ++i) {
                m_fparamv.push_back(m_fparams);
            }
            for (unsigned i = 0; i <= num_alternations(); ++i) {
                m_Ms.push_back(m.mk_true());
                m_solvers.push_back(alloc(smt::kernel, m, m_fparamv[i], m_params));
            }
            m_Ms[m_Ms.size()-1] = m_fml;
            m_solvers.back()->assert_expr(m_fml);
        }

        expr* M(unsigned i) { return m_Ms[i].get(); }

        app_ref_vector const& vars(unsigned i) { return m_vars[i]; }

        smt::kernel& solver(unsigned i) { return *m_solvers[i]; }

        void reset() override {
            for (unsigned i = 0; i < m_solvers.size(); ++i) {
                dealloc(m_solvers[i]);
            }
            m_fml = nullptr;
            m_Ms.reset();
            m_fparamv.reset();
            m_solvers.reset();
            m_vars.reset();
        }

        void skolemize_existential_prefix() {
            quantifier_hoister hoist(m);
            expr_ref result(m);
            app_ref_vector vars(m);
            hoist.pull_exists(m_fml, vars, result);
            m_fml = result;            
        }

        //
        // fa x ex y fa z . phi
        // fa x ! fa y ! fa z ! (!phi)
        // 
        void extract_alt_form(expr* fml) {
            quantifier_hoister hoist(m);
            expr_ref result(m);
            bool is_fa = false;   
            unsigned parity = 0;
            m_fml = fml;
            while (true) {
                app_ref_vector vars(m);                
                hoist(m_fml, vars, is_fa, result);
                if (vars.empty()) {
                    break;
                }
                SASSERT(((parity & 0x1) == 0) == is_fa);
                ++parity;
                TRACE("qe", tout << "Hoist " << (is_fa?"fa":"ex") << "\n";
                      for (unsigned i = 0; i < vars.size(); ++i) {
                          tout << mk_pp(vars[i].get(), m) << " ";
                      }
                      tout << "\n";
                      tout << mk_pp(result, m) << "\n";);

                m_vars.push_back(vars);
                m_fml = result;
            } 
            //
            // negate formula if the last quantifier is universal.
            // so that normal form fa x ! fa y ! fa z ! psi 
            // is obtained.
            //
            if ((parity & 0x1) == 1) {
                m_fml = m.mk_not(m_fml);
            }            
            init_Ms();
            checkpoint();
        }

        /**
           \brief Main quantifier test algorithm loop.

        */
        expr_ref qt(unsigned i, expr* ctx, model_ref& model) {
            model_ref model1;
            while (true) {
                IF_VERBOSE(1, verbose_stream() << "(qt " << i << ")\n";);
                TRACE("qe",
                      tout << i << " " << mk_pp(ctx, m) << "\n";
                      display(tout););
                checkpoint();
                if (is_sat(i, ctx, model)) {
                    expr_ref ctxM = extrapolate(i, ctx, M(i));
                    if (i == num_alternations()) {
                        return ctxM;
                    }
                    expr_ref res = qt(i+1, ctxM, model1);
                    if (m.is_false(res)) {
                        return ctxM;
                    }
                    project(i, res);
                }
                else {
                    return m_false;
                }
            }
            UNREACHABLE();
            return expr_ref(m);
        }

        /**
           \brief compute extrapolant
           
           Assume A & B is sat.
           Compute C, such that 
           1. A & C is sat, 
           2. not B & C is unsat.
           (C strengthens B and is still satisfiable with A).
        */
        expr_ref extrapolate(unsigned i, expr* A, expr* B) {
            switch(m_extrapolate_strategy_param) {
            case 0: return trivial_extrapolate(i, A, B);
            case 1: return nnf_strengthening_extrapolate(i, A, B);
            case 2: return smt_test_extrapolate(i, A, B);
            case 3: return nnf_weakening_extrapolate(i, A, B);
            default: return trivial_extrapolate(i, A, B);
            }
        }

        expr_ref trivial_extrapolate(unsigned i, expr* A, expr* B) {
            return expr_ref(B, m);
        }

        expr_ref conjunction_extrapolate(unsigned i, expr* A, expr* B) {
            return expr_ref(m.mk_and(A, B), m);
        }

        /**
           
           Set C = nnf(B), That is, C is the NNF version of B.
           For each literal in C in order, replace the literal by False and
           check the conditions for extrapolation:
              1. not B & C is unsat, 
              2. A & C is sat.
           The first check holds by construction, so it is redundant. 
           The second is not redundant.
           Instead of replacing literals in an NNF formula, 
           one simply asserts the negation of that literal.
        */
        expr_ref nnf_strengthening_extrapolate(unsigned i, expr* A, expr* B) {
            expr_ref Bnnf(B, m);
            atom_set pos, neg;
            get_nnf(Bnnf, m_is_relevant, m_mk_atom, pos, neg);
            expr_substitution sub(m);

            remove_duplicates(pos, neg);

            // Assumption: B is already asserted in solver[i].
            smt::kernel& solver = *m_solvers[i];
            solver.push();
            solver.assert_expr(A);
            nnf_strengthen(solver, pos, m.mk_false(), sub);
            nnf_strengthen(solver, neg, m.mk_true(),  sub);


            solver.pop(1);
            scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m);
            replace->set_substitution(&sub);
            (*replace)(Bnnf);
            m_rewriter(Bnnf);
            TRACE("qe",
                  tout << "A:  " << mk_pp(A, m) << "\n";
                  tout << "B:  " << mk_pp(B, m) << "\n";
                  tout << "B': " << mk_pp(Bnnf.get(), m) << "\n";
                  // solver.display(tout);
                  );
            DEBUG_CODE(
                solver.push();
                solver.assert_expr(m.mk_not(B));
                solver.assert_expr(Bnnf);
                lbool is_sat = solver.check();
                TRACE("qe", tout << "is sat: " << is_sat << "\n";);
                SASSERT(is_sat == l_false);
                solver.pop(1););
            DEBUG_CODE(
                solver.push();
                solver.assert_expr(A);
                solver.assert_expr(Bnnf);
                lbool is_sat = solver.check();
                TRACE("qe", tout << "is sat: " << is_sat << "\n";);
                SASSERT(is_sat == l_true);
                solver.pop(1););
                       
            return Bnnf;
        }
      
        void nnf_strengthen(smt::kernel& solver, atom_set& atoms, expr* value, expr_substitution& sub) {
            atom_set::iterator it = atoms.begin(), end = atoms.end();
            for (; it != end; ++it) {
                solver.push();
                solver.assert_expr(m.mk_iff(*it, value));
                lbool is_sat = solver.check();
                solver.pop(1);
                if (is_sat == l_true) {
                    TRACE("qe", tout << "consistent with: " << mk_pp(*it, m) << " " << mk_pp(value, m) << "\n";);
                    sub.insert(*it, value);
                    solver.assert_expr(m.mk_iff(*it, value));
                }
                checkpoint();
            }            
        }

        void remove_duplicates(atom_set& pos, atom_set& neg) {
            ptr_vector<app> to_delete;
            atom_set::iterator it = pos.begin(), end = pos.end();
            for (; it != end; ++it) {
                if (neg.contains(*it)) {
                    to_delete.push_back(*it);
                }
            }
            for (unsigned j = 0; j < to_delete.size(); ++j) {
                pos.remove(to_delete[j]);
                neg.remove(to_delete[j]);
            }
        }

        /**
           Set C = nnf(B), That is, C is the NNF version of B.
           For each literal in C in order, replace the literal by True and
           check the conditions for extrapolation
              1. not B & C is unsat, 
              2. A & C is sat.
           The second holds by construction and is redundant.
           The first is not redundant.
        */
        expr_ref nnf_weakening_extrapolate(unsigned i, expr* A, expr* B) {
            expr_ref Bnnf(B, m);
            atom_set pos, neg;
            get_nnf(Bnnf, m_is_relevant, m_mk_atom, pos, neg);
            remove_duplicates(pos, neg);
            expr_substitution sub(m);
                        
            m_solver.push();
            m_solver.assert_expr(A);
            m_solver.assert_expr(m.mk_not(B));
            nnf_weaken(m_solver, Bnnf, pos, m.mk_true(),  sub);
            nnf_weaken(m_solver, Bnnf, neg, m.mk_false(), sub);
            scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m);
            replace->set_substitution(&sub);
            (*replace)(Bnnf);
            m_rewriter(Bnnf);
            m_solver.pop(1);
            return Bnnf;
        }

        void nnf_weaken(smt::kernel& solver, expr_ref& B, atom_set& atoms, expr* value, expr_substitution& sub) {
            atom_set::iterator it = atoms.begin(), end = atoms.end();
            for (; it != end; ++it) {
                solver.push();
                expr_ref fml = B;
                mk_default_expr_replacer(m)->apply_substitution(*it, value, fml);
                solver.assert_expr(fml);
                if (solver.check() == l_false) {
                    sub.insert(*it, value);
                    B = fml;
                }
                solver.pop(1);
                checkpoint();
            }            
        }


        /**
           Use the model for A & B to extrapolate. 
           Initially, C is conjunction of literals from B 
           that are in model of A & B.
           The model is a conjunction of literals. 
           Let us denote this set $C$. We see that the conditions
           for extrapolation are satisfied. Furthermore, 
           C can be generalized by removing literals 
           from C as long as !B & A & C is unsatisfiable.
        */

        expr_ref smt_test_extrapolate(unsigned i, expr* A, expr* B) {
            expr_ref_vector proxies(m), core(m);
            obj_map<expr, expr*> proxy_map;

            checkpoint();
            
            m_solver.push();
            m_solver.assert_expr(m.mk_not(B));
            for (unsigned i = 0; i < m_assignments.size(); ++i) {
                proxies.push_back(m.mk_fresh_const("proxy",m.mk_bool_sort()));
                proxy_map.insert(proxies.back(), m_assignments[i].get());
                m_solver.assert_expr(m.mk_iff(proxies.back(), m_assignments[i].get()));
                TRACE("qe", tout << "assignment: " << mk_pp(m_assignments[i].get(), m) << "\n";);
            }
            VERIFY(l_false == m_solver.check(proxies.size(), proxies.c_ptr()));
            unsigned core_size = m_solver.get_unsat_core_size();
            for (unsigned i = 0; i < core_size; ++i) {
                core.push_back(proxy_map.find(m_solver.get_unsat_core_expr(i)));
            }
            expr_ref result(m.mk_and(core.size(), core.c_ptr()), m);
            TRACE("qe", tout << "core: " << mk_pp(result, m) << "\n";
                  tout << mk_pp(A, m) << "\n";
                  tout << mk_pp(B, m) << "\n";);
            m_solver.pop(1);
            return result;
        }

        /**
           \brief project vars(idx) from fml relative to M(idx).                      
        */
        void project(unsigned idx, expr* _fml) {
            SASSERT(idx < num_alternations());
            expr_ref fml(_fml, m);
            if (m_strong_context_simplify_param && m_ctx_simplify_local_param) {
                m_ctx_rewriter.push();
                m_ctx_rewriter.assert_expr(M(idx));
                m_ctx_rewriter(fml);
                m_ctx_rewriter.pop();
                TRACE("qe", tout << mk_pp(_fml, m) << "\n-- context simplify -->\n" << mk_pp(fml, m) << "\n";);
            }
            solver_context ctx(*this, idx);            
            smt_params fparams(m_fparams);            
            ctx.add_plugin(mk_arith_plugin(ctx, false, fparams));
            ctx.add_plugin(mk_bool_plugin(ctx));
            ctx.add_plugin(mk_bv_plugin(ctx));
            ctx.init(fml, idx);
            ctx.set_projection_mode(m_projection_mode_param);
            m_solvers[idx+1]->push();
            while (ctx.get_num_vars() > 0) {
                VERIFY(l_true == m_solvers[idx+1]->check());
                ctx.project_var(ctx.get_num_vars()-1);               
            }
            m_solvers[idx+1]->pop(1);            
            expr_ref not_fml(m.mk_not(ctx.fml()), m);
            m_rewriter(not_fml);
            if (m_strong_context_simplify_param && !m_ctx_simplify_local_param) {
                m_ctx_rewriter.push();
                m_ctx_rewriter.assert_expr(M(idx));
                m_ctx_rewriter(not_fml);
                m_ctx_rewriter.pop();
            }
            expr_ref tmp(m.mk_and(M(idx), not_fml), m);
            m_rewriter(tmp);
            m_Ms[idx] = tmp;
            m_solvers[idx]->assert_expr(not_fml);            
            TRACE("qe", 
                  tout << mk_pp(fml, m) << "\n--->\n";
                  tout << mk_pp(tmp, m) << "\n";);
        }

        void checkpoint() {
            if (m.canceled()) {
                throw tactic_exception(m.limit().get_cancel_msg());
            }
        }

        void check_success(bool ok) {
            if (!ok) {
                TRACE("qe", tout << "check failed\n";);
                throw tactic_exception(TACTIC_CANCELED_MSG);
            }
        }

        bool is_sat(unsigned i, expr* ctx, model_ref& model) {
            smt::kernel& solver = *m_solvers[i];
            solver.push();
            solver.assert_expr(ctx);
            lbool r = solver.check();
            m_assignments.reset();
            solver.get_assignments(m_assignments);
            solver.pop(1);
            check_success(r != l_undef);
            if (r == l_true && i == 0) solver.get_model(model);
            return r == l_true;
        }

        void display(std::ostream& out) {
            bool is_fa = true;
            for (unsigned i = 0; i < num_alternations(); ++i) {
                out << (is_fa?"fa ":"ex ");
                for (unsigned j = 0; j < vars(i).size(); ++j) {
                    out << mk_pp(m_vars[i][j].get(), m) << " ";
                }
                out << "\n";
                out << mk_pp(m_Ms[i+1].get(), m) << "\n";
                is_fa = !is_fa;
            }
        }        
    };    
        
    tactic * mk_sat_tactic(ast_manager& m, params_ref const& p) {
        return alloc(sat_tactic, m, p);
    }
    
};
