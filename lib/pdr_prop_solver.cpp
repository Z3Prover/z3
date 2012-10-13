/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    prop_solver.cpp

Abstract:

    SMT solver abstraction for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-17.

Revision History:

--*/

#include <sstream>
#include "model.h"
#include "pdr_util.h"
#include "pdr_prop_solver.h"
#include "ast_smt2_pp.h"
#include "dl_util.h"
#include "model_pp.h"
#include "front_end_params.h"
#include "datatype_decl_plugin.h"
#include "pdr_farkas_learner.h"
#include "ast_smt2_pp.h"

//
// Auxiliary structure to introduce propositional names for assumptions that are not
// propositional. It is to work with the smt::context's restriction
// that assumptions be propositional literals.
//

namespace pdr {

    class prop_solver::safe_assumptions {
        prop_solver&        s;
        ast_manager&        m;
        expr_ref_vector     m_atoms;
        expr_ref_vector     m_assumptions;
        obj_map<app,expr *> m_fresh2expr;
        obj_map<expr, app*> m_expr2fresh;
        obj_hashtable<expr> m_equivs;
        unsigned            m_num_fresh;

        app * mk_fresh(expr* atom) {
            app* res;
            SASSERT(!is_var(atom)); //it doesn't make sense to introduce names to variables
            if (m_expr2fresh.find(atom, res)) {
                return res;
            }
            SASSERT(s.m_fresh.size() >= m_num_fresh);
            if (m_num_fresh == s.m_fresh.size()) {
                std::stringstream name;
                name << "pdr_proxy_" << s.m_fresh.size();
                res = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());
                s.m_fresh.push_back(res);
                s.m_aux_symbols.insert(res->get_decl());
            }
            else {
                res = s.m_fresh[m_num_fresh].get();
            }
            ++m_num_fresh;
            m_expr2fresh.insert(atom, res);
            m_fresh2expr.insert(res, atom);
            expr_ref equiv(m.mk_or(atom, m.mk_not(res)), m);
            s.m_ctx->assert_expr(equiv);
            m_assumptions.push_back(equiv);
            m_equivs.insert(equiv);
            TRACE("pdr_verbose", tout << "name asserted " << mk_pp(equiv, m) << "\n";);    
            return res;
        }

        void mk_safe(expr_ref_vector& conjs) {
            datalog::flatten_and(conjs);
            expand_literals(conjs);
            for (unsigned i = 0; i < conjs.size(); ++i) {
                expr * lit = conjs[i].get();
                expr * lit_core = lit;
                m.is_not(lit, lit_core);
                SASSERT(!m.is_true(lit));
                if (!is_uninterp(lit_core) || to_app(lit_core)->get_num_args() != 0) {
                    conjs[i] = mk_fresh(lit);
                }
            }
            m_assumptions.append(conjs);
        }

        void expand_literals(expr_ref_vector& conjs) {
            arith_util arith(m);
            datatype_util dt(m);
            expr* e1, *e2, *c, *val;
            for (unsigned i = 0; i < conjs.size(); ++i) {

                expr* e = conjs[i].get();
                if (m.is_eq(e, e1, e2) && arith.is_int_real(e1)) {
                    conjs[i] = arith.mk_le(e1,e2);
                    if (i+1 == conjs.size()) {
                        conjs.push_back(arith.mk_ge(e1, e2));
                    }
                    else {
                        conjs.push_back(conjs[i+1].get());
                        conjs[i+1] = arith.mk_ge(e1, e2);
                    }
                    ++i;
                }
                else if (m.is_eq(e, c, val) && is_app(val) && dt.is_constructor(to_app(val))) {
                    func_decl* f = to_app(val)->get_decl();
                    func_decl* r = dt.get_constructor_recognizer(f);
                    conjs[i] = m.mk_app(r,c);
                    ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(f);
                    for (unsigned i = 0; i < acc.size(); ++i) {
                        conjs.push_back(m.mk_eq(m.mk_app(acc[i], c), to_app(val)->get_arg(i)));
                    }
                }
            }
        }

    public:
        safe_assumptions(prop_solver& s, expr_ref_vector const& assumptions): 
            s(s), m(s.m), m_atoms(assumptions), m_assumptions(m), m_num_fresh(0) {
              mk_safe(m_atoms);
          }

          ~safe_assumptions() {
          }    

          expr_ref_vector const& atoms() const { return m_atoms; }

          unsigned assumptions_size() const { return m_assumptions.size(); }

          expr* assumptions(unsigned i) const { return m_assumptions[i]; }

          expr* undo_naming(expr* atom) {
              if (m_equivs.contains(atom)) {
                  return m.mk_true();
              }
              SASSERT(is_app(atom)); //only apps can be used in safe cubes
              m_fresh2expr.find(to_app(atom), atom);
              return atom;
          }

          void undo_naming(expr_ref_vector& literals) {
              for (unsigned i = 0; i < literals.size(); ++i) {
                  literals[i] = undo_naming(literals[i].get());
                  if (m.is_true(literals[i].get())) {
                      literals[i] = literals.back();
                      literals.pop_back();
                      --i;
                  }
              }        
          }
    };


    prop_solver::prop_solver(manager& pm, symbol const& name) :
        m_fparams(pm.get_fparams()),
        m(pm.get_manager()),
        m_pm(pm),
        m_name(name),
        m_try_minimize_core(pm.get_params().get_bool(":try-minimize-core", false)),
        m_ctx(pm.mk_fresh()),
        m_pos_level_atoms(m),
        m_neg_level_atoms(m),
        m_fresh(m),
        m_in_level(false)
    {
        m_ctx->assert_expr(m_pm.get_background());
    }

    void prop_solver::add_level() {
        unsigned idx = level_cnt();
        std::stringstream name;
        name << m_name << "#level_" << idx;
        func_decl * lev_pred = m.mk_fresh_func_decl(name.str().c_str(), 0, 0,m.mk_bool_sort());
        m_aux_symbols.insert(lev_pred);
        m_level_preds.push_back(lev_pred);

        app_ref pos_la(m.mk_const(lev_pred), m);
        app_ref neg_la(m.mk_not(pos_la.get()), m);

        m_pos_level_atoms.push_back(pos_la);
        m_neg_level_atoms.push_back(neg_la);

        m_level_atoms_set.insert(pos_la.get());
        m_level_atoms_set.insert(neg_la.get());
    }

    void prop_solver::ensure_level(unsigned lvl) {
        while (lvl>=level_cnt()) {
            add_level();
        }
    }

    unsigned prop_solver::level_cnt() const {
        return m_level_preds.size();
    }

    void prop_solver::push_level_atoms(unsigned level, expr_ref_vector& tgt) const {
        unsigned lev_cnt = level_cnt();
        for (unsigned i=0; i<lev_cnt; i++) {
            bool active = i>=level;
            app * lev_atom = active ? m_neg_level_atoms[i] : m_pos_level_atoms[i];
            tgt.push_back(lev_atom);
        }
    }

    void prop_solver::add_formula(expr * form) {
        SASSERT(!m_in_level);
        m_ctx->assert_expr(form);
        IF_VERBOSE(21, verbose_stream() << "$ asserted " << mk_pp(form, m) << "\n";);
        TRACE("pdr", tout << "add_formula: " << mk_pp(form, m) << "\n";);
    }

    void prop_solver::add_level_formula(expr * form, unsigned level) {
        ensure_level(level);
        app * lev_atom = m_pos_level_atoms[level].get();
        app_ref lform(m.mk_or(form, lev_atom), m);
        add_formula(lform.get());
    }


    lbool prop_solver::check_safe_assumptions(
        safe_assumptions& safe,
        const expr_ref_vector& atoms, 
        expr_ref_vector* core, 
        model_ref * mdl, 
        bool& assumes_level)
    {
        flet<bool> _model(m_fparams.m_model, mdl != 0);
        expr_ref_vector expr_atoms(m);
        expr_atoms.append(atoms.size(), atoms.c_ptr());
        assumes_level = false;

        if (m_in_level) {
            push_level_atoms(m_current_level, expr_atoms);
        }

        lbool result = m_ctx->check(expr_atoms);

        TRACE("pdr", 
               tout << mk_pp(m_pm.mk_and(expr_atoms), m) << "\n";
               tout << result << "\n";);

        if (result == l_true && mdl) {
            m_ctx->get_model(*mdl);
            TRACE("pdr_verbose", model_pp(tout, **mdl); );
        }

        unsigned core_size = m_ctx->get_unsat_core_size(); 

        if (result == l_false && !core) {            
            for (unsigned i = 0; i < core_size; ++i) {
                if (m_level_atoms_set.contains(m_ctx->get_unsat_core_expr(i))) {
                    assumes_level = true;
                    break;
                }
            }
        }

        if (result == l_false && core && m.proofs_enabled()) {
            proof_ref pr(m);
            pr = m_ctx->get_proof();
            IF_VERBOSE(21, verbose_stream() << mk_ismt2_pp(pr, m) << "\n";);
            farkas_learner fl(m_fparams, m);
            expr_ref_vector lemmas(m);
            obj_hashtable<expr> bs;
            for (unsigned i = 0; i < safe.assumptions_size(); ++i) {
                bs.insert(safe.assumptions(i));
            }
            fl.get_lemmas(pr, bs, lemmas);
            safe.undo_naming(lemmas);
            fl.simplify_lemmas(lemmas);

            IF_VERBOSE(2, 
                verbose_stream() << "Lemmas\n";            
                for (unsigned i = 0; i < lemmas.size(); ++i) {
                    verbose_stream() << mk_pp(lemmas[i].get(), m) << "\n";
                });

            core->reset();
            core->append(lemmas);
            return result;
        }

        if (result == l_false && core) {
            core->reset();
            for (unsigned i = 0; i < core_size; ++i) {
                expr * core_expr = m_ctx->get_unsat_core_expr(i);
                SASSERT(is_app(core_expr));

                if (m_level_atoms_set.contains(core_expr)) {
                    assumes_level = true;
                    continue;
                }
                if (m_ctx->is_aux_predicate(core_expr)) {
                    continue;
                }
                core->push_back(to_app(core_expr));
            }
            SASSERT(expr_atoms.size() >= core->size());

            safe.undo_naming(*core);

            TRACE("pdr", 
                tout << mk_pp(m_pm.mk_and(expr_atoms), m) << "\n";
                tout << "core_exprs: ";
                for (unsigned i = 0; i < core_size; ++i) {
                    tout << mk_pp(m_ctx->get_unsat_core_expr(i), m) << " ";
                }
                tout << "\n";
                tout << "core: " << mk_pp(m_pm.mk_and(*core), m) << "\n";              
                );
            
        }
        return result;
    }

    lbool prop_solver::check_assumptions(
        const expr_ref_vector & atoms, 
        expr_ref_vector * core, 
        model_ref * mdl, 
        bool& assumes_level)
    {
        return check_assumptions_and_formula(atoms, m.mk_true(), core, mdl, assumes_level);
    }

    lbool prop_solver::check_conjunction_as_assumptions(
        expr * conj, 
        expr_ref_vector * core, 
        model_ref * mdl, 
        bool& assumes_level) {
        expr_ref_vector asmp(m);
        asmp.push_back(conj);
        return check_assumptions(asmp, core, mdl, assumes_level);
    }

    lbool prop_solver::check_assumptions_and_formula(
        const expr_ref_vector & atoms, 
        expr * form, 
        expr_ref_vector * core, 
        model_ref * mdl, 
        bool& assumes_level) 
    {
        pdr::smt_context::scoped _scoped(*m_ctx);
        safe_assumptions safe(*this, atoms);
        m_ctx->assert_expr(form);    
        CTRACE("pdr", !m.is_true(form), tout << "check with formula: " << mk_pp(form, m) << "\n";);
        lbool res = check_safe_assumptions(safe, safe.atoms(), core, mdl, assumes_level);
        if (res == l_false && core && m_try_minimize_core) {
            unsigned sz = core->size();
            bool assumes_level1 = false;
            lbool res2 = check_safe_assumptions(safe, *core, core, mdl, assumes_level1);
            if (res2 == l_false && sz > core->size()) {
                assumes_level = assumes_level1;
                IF_VERBOSE(1, verbose_stream() << "reduced core size from " << sz << " to " << core->size() << "\n";);
            }
        }

        //
        // we don't have to undo model naming, as from the model 
        // we extract the values for state variables directly
        //
        return res;
    }

    void prop_solver::collect_statistics(statistics& st) const {
    }


}
