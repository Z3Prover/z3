/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    qe_mbi.cpp

Abstract:

    Model-based interpolation utilities

Author:

    Nikolaj Bjorner (nbjorner), Arie Gurfinkel 2018-6-8

Revision History:


Notes:

  Reduction into:
   T_EUF
   T_LIRA

  Other theories: DT, ARR reduced to EUF
  BV is EUF/Boolean.


--*/

#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/arith_decl_plugin.h"
#include "model/model_evaluator.h"
#include "solver/solver.h"
#include "qe/qe_mbi.h"
#include "qe/qe_term_graph.h"
#include "qe/qe_arith.h"


namespace qe {

    lbool mbi_plugin::check(expr_ref_vector& lits, model_ref& mdl) {
        while (true) {
            switch ((*this)(lits, mdl)) {
            case mbi_sat:
                return l_true;
            case mbi_unsat:
                return l_false;
            case mbi_undef:
                return l_undef;
            case mbi_augment:
                break;
            }
        }
    }


    // -------------------------------
    // prop_mbi

    prop_mbi_plugin::prop_mbi_plugin(solver* s): mbi_plugin(s->get_manager()), m_solver(s) {}

    // sketch of propositional

    mbi_result prop_mbi_plugin::operator()(expr_ref_vector& lits, model_ref& mdl)  {
        lbool r = m_solver->check_sat(lits);
        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            return mbi_unsat;
        case l_true:
            m_solver->get_model(mdl);
            lits.reset();
            for (unsigned i = 0, sz = mdl->get_num_constants(); i < sz; ++i) {
                func_decl* c = mdl->get_constant(i);
                if (m_shared.contains(c)) {
                    if (m.is_true(mdl->get_const_interp(c))) {
                        lits.push_back(m.mk_const(c));
                    }
                    else if (m.is_false(mdl->get_const_interp(c))) {
                        lits.push_back(m.mk_not(m.mk_const(c)));
                    }
                }
            }
            return mbi_sat;
        default:
            return mbi_undef;
        }
    }

    void prop_mbi_plugin::block(expr_ref_vector const& lits) {
        m_solver->assert_expr(mk_not(mk_and(lits)));
    }

    // -------------------------------
    // euf_mbi

    struct euf_mbi_plugin::is_atom_proc {
        ast_manager& m;
        expr_ref_vector& m_atoms;
        is_atom_proc(expr_ref_vector& atoms): m(atoms.m()), m_atoms(atoms) {}
        void operator()(app* a) {
            if (m.is_eq(a)) {
                m_atoms.push_back(a);
            }
            else if (m.is_bool(a) && a->get_family_id() != m.get_basic_family_id()) {
                m_atoms.push_back(a);
            }
        }
        void operator()(expr*) {}
    };

    euf_mbi_plugin::euf_mbi_plugin(solver* s, solver* sNot):
        mbi_plugin(s->get_manager()),
        m_atoms(m),
        m_solver(s),
        m_dual_solver(sNot) {
        params_ref p;
        p.set_bool("core.minimize", true);
        m_solver->updt_params(p);
        m_dual_solver->updt_params(p);
        expr_ref_vector fmls(m);
        m_solver->get_assertions(fmls);
        expr_fast_mark1 marks;
        is_atom_proc proc(m_atoms);
        for (expr* e : fmls) {
            quick_for_each_expr(proc, marks, e);
        }
    }

    mbi_result euf_mbi_plugin::operator()(expr_ref_vector& lits, model_ref& mdl) {
        lbool r = m_solver->check_sat(lits);
        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            // optionally minimize core using superposition.
            return mbi_unsat;
        case l_true: {
            m_solver->get_model(mdl);
            model_evaluator mev(*mdl.get());
            lits.reset();
            for (expr* e : m_atoms) {
                if (mev.is_true(e)) {
                    lits.push_back(e);
                }
                else if (mev.is_false(e)) {
                    lits.push_back(m.mk_not(e));
                }
            }
            TRACE("qe", tout << "atoms from model: " << lits << "\n";);
            r = m_dual_solver->check_sat(lits);
            expr_ref_vector core(m);
            term_graph tg(m);
            switch (r) {
            case l_false:
                // use the dual solver to find a 'small' implicant
                m_dual_solver->get_unsat_core(core);
                TRACE("qe", tout << "core: " << core << "\n";);
                // project the implicant onto vars
                tg.set_vars(m_shared, false);
                tg.add_lits(core);
                lits.reset();
                lits.append(tg.project(*mdl));
                TRACE("qe", tout << "project: " << lits << "\n";);
                return mbi_sat;
            case l_undef:
                return mbi_undef;
            case l_true:
                UNREACHABLE();
                return mbi_undef;
            }
            return mbi_sat;
        }
        default:
            // TBD: if not running solver to completion, then:
            // 1. extract unit literals from m_solver.
            // 2. run a cc over the units
            // 3. extract equalities or other assignments over the congruence classes
            // 4. ensure that at least some progress is made over original lits.
            return mbi_undef;
        }
    }

    void euf_mbi_plugin::block(expr_ref_vector const& lits) {
        m_solver->assert_expr(mk_not(mk_and(lits)));
    }


    // -------------------------------
    // euf_arith_mbi

    struct euf_arith_mbi_plugin::is_atom_proc {
        ast_manager&         m;
        expr_ref_vector&     m_atoms;
        obj_hashtable<expr>& m_atom_set;

        is_atom_proc(expr_ref_vector& atoms, obj_hashtable<expr>& atom_set): 
            m(atoms.m()), m_atoms(atoms), m_atom_set(atom_set) {}

        void operator()(app* a) {
            if (m_atom_set.contains(a)) {
                // continue
            }
            else if (m.is_eq(a)) {
                m_atoms.push_back(a);
                m_atom_set.insert(a);
            }
            else if (m.is_bool(a) && a->get_family_id() != m.get_basic_family_id()) {
                m_atoms.push_back(a);
                m_atom_set.insert(a);
            }
        }
        void operator()(expr*) {}
    };

    struct euf_arith_mbi_plugin::is_arith_var_proc {
        ast_manager&    m;
        app_ref_vector& m_pvars;
        app_ref_vector& m_svars;
        arith_util      arith;
        obj_hashtable<func_decl> m_shared;
        is_arith_var_proc(func_decl_ref_vector const& shared, app_ref_vector& pvars, app_ref_vector& svars):
            m(pvars.m()), m_pvars(pvars), m_svars(svars), arith(m) {
            for (func_decl* f : shared) m_shared.insert(f);
        }
        void operator()(app* a) {
            if (!arith.is_int_real(a) || a->get_family_id() == arith.get_family_id()) {
                // no-op
            }
            else if (m_shared.contains(a->get_decl())) {
                m_svars.push_back(a);
            }
            else {
                m_pvars.push_back(a);
            }
        }
        void operator()(expr*) {}

    };

    euf_arith_mbi_plugin::euf_arith_mbi_plugin(solver* s, solver* sNot):
        mbi_plugin(s->get_manager()),
        m_atoms(m),
        m_fmls(m),
        m_solver(s),
        m_dual_solver(sNot) {
        params_ref p;
        p.set_bool("core.minimize", true);
        m_solver->updt_params(p);
        m_dual_solver->updt_params(p);
        m_solver->get_assertions(m_fmls);
        collect_atoms(m_fmls);
    }

    void euf_arith_mbi_plugin::collect_atoms(expr_ref_vector const& fmls) {
        expr_fast_mark1 marks;
        is_atom_proc proc(m_atoms, m_atom_set);
        for (expr* e : fmls) {
            quick_for_each_expr(proc, marks, e);
        }
    }

    bool euf_arith_mbi_plugin::get_literals(model_ref& mdl, expr_ref_vector& lits) {
        lits.reset();
        for (expr* e : m_atoms) {
            if (mdl->is_true(e)) {
                lits.push_back(e);
            }
            else if (mdl->is_false(e)) {
                lits.push_back(m.mk_not(e));
            }
        }
        TRACE("qe", tout << "atoms from model: " << lits << "\n";);
        solver_ref dual = m_dual_solver->translate(m, m_dual_solver->get_params());
        dual->assert_expr(mk_not(mk_and(m_fmls)));
        lbool r = dual->check_sat(lits);
        TRACE("qe", dual->display(tout << "dual result " << r << "\n"););
        if (l_false == r) {
            // use the dual solver to find a 'small' implicant
            lits.reset();
            dual->get_unsat_core(lits);
            return true;
        }
        else {
            return false;
        }
    }

    app_ref_vector euf_arith_mbi_plugin::get_arith_vars(model_ref& mdl, expr_ref_vector& lits) {
        arith_util a(m);
        app_ref_vector pvars(m), svars(m); // private and shared arithmetic variables.
        is_arith_var_proc _proc(m_shared, pvars, svars);
        for_each_expr(_proc, lits);
        rational v1, v2;
        for (expr* p : pvars) {
            VERIFY(a.is_numeral((*mdl)(p), v1));
            for (expr* s : svars) {
                VERIFY(a.is_numeral((*mdl)(s), v2));                
                if (v1 < v2) {
                    lits.push_back(a.mk_lt(p, s));
                }
                else if (v2 < v1) {
                    lits.push_back(a.mk_lt(s, p));                    
                }
                else {
                    lits.push_back(m.mk_eq(s, p));
                }
            }
        }
        return pvars;
    }

    mbi_result euf_arith_mbi_plugin::operator()(expr_ref_vector& lits, model_ref& mdl) {
        lbool r = m_solver->check_sat(lits);

        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            TRACE("qe", tout << "unsat core: " << lits << "\n";);
            // optionally minimize core using superposition.
            return mbi_unsat;
        case l_true: {
            m_solver->get_model(mdl);
            if (!get_literals(mdl, lits)) {
                return mbi_undef;
            }
            TRACE("qe", tout << lits << "\n";);

            // 1. Extract projected variables, add inequalities between
            //    projected variables and non-projected terms according to model.
            // 2. Extract disequalities implied by congruence closure.
            // 3. project arithmetic variables from pure literals.
            // 4. Add projected definitions as equalities to EUF.
            // 5. project remaining literals with respect to EUF.

            app_ref_vector avars = get_arith_vars(mdl, lits);
            TRACE("qe", tout << "vars: " << avars << " lits: " << lits << "\n";);

            // 2.
            term_graph tg1(m);
            func_decl_ref_vector no_shared(m);
            tg1.set_vars(no_shared, false);
            tg1.add_lits(lits);
            arith_util a(m);
            expr_ref_vector foreign = tg1.shared_occurrences(a.get_family_id());
            obj_hashtable<expr> _foreign;
            for (expr* e : foreign) _foreign.insert(e);
            vector<expr_ref_vector> partition = tg1.get_partition(*mdl);
            expr_ref_vector diseq = tg1.get_ackerman_disequalities();
            lits.append(diseq);
            TRACE("qe", tout << "diseq: " << diseq << "\n";
                  tout << "foreign: " << foreign << "\n";
                  for (auto const& v : partition) {
                      tout << "partition: {";
                      bool first = true;
                      for (expr* e : v) {
                          if (first) first = false; else tout << ", ";
                          tout << expr_ref(e, m);
                      }
                      tout << "}\n";
                  }
                  );
            vector<expr_ref_vector> refined_partition;
            for (auto & p : partition) {
                unsigned j = 0; 
                for (expr* e : p) {
                    if (_foreign.contains(e) || 
                        (is_app(e) && m_shared.contains(to_app(e)->get_decl()))) {
                        p[j++] = e;
                    }
                }
                p.shrink(j);
                if (!p.empty()) refined_partition.push_back(p);
            }
            TRACE("qe",
                  for (auto const& v : refined_partition) {
                      tout << "partition: {";
                      bool first = true;
                      for (expr* e : v) {
                          if (first) first = false; else tout << ", ";
                          tout << expr_ref(e, m);
                      }
                      tout << "}\n";
                  });

            
            
            arith_project_plugin ap(m);
            ap.set_check_purified(false);

            // 3.
            auto defs = ap.project(*mdl.get(), avars, lits);

            // 4.
            for (auto const& def : defs) {
                lits.push_back(m.mk_eq(def.var, def.term));
            }
            TRACE("qe", tout << "# arith defs " << defs.size() << " avars: " << avars << " " << lits << "\n";);

            // 5.
            term_graph tg2(m);
            tg2.set_vars(m_shared, false);
            tg2.add_lits(lits);
            lits.reset();
            lits.append(tg2.project());
            TRACE("qe", tout << "project: " << lits << "\n";);
            return mbi_sat;
        }
        default:
            // TBD: if not running solver to completion, then:
            // 1. extract unit literals from m_solver.
            // 2. run a cc over the units
            // 3. extract equalities or other assignments over the congruence classes
            // 4. ensure that at least some progress is made over original lits.
            return mbi_undef;
        }
    }

    void euf_arith_mbi_plugin::block(expr_ref_vector const& lits) {
        collect_atoms(lits);
        m_fmls.push_back(mk_not(mk_and(lits)));
        m_solver->assert_expr(m_fmls.back());
    }


    /** --------------------------------------------------------------
     * ping-pong interpolation of Gurfinkel & Vizel
     * compute a binary interpolant.
     */
    lbool interpolator::pingpong(mbi_plugin& a, mbi_plugin& b, expr_ref& itp) {
        model_ref mdl;
        expr_ref_vector lits(m);
        bool turn = true;
        vector<expr_ref_vector> itps, blocks;
        itps.push_back(expr_ref_vector(m));
        itps.push_back(expr_ref_vector(m));
        blocks.push_back(expr_ref_vector(m));
        blocks.push_back(expr_ref_vector(m));
        mbi_result last_res = mbi_undef;
        bool_rewriter rw(m);
        while (true) {
            auto* t1 = turn ? &a : &b;
            auto* t2 = turn ? &b : &a;
            mbi_result next_res = (*t1)(lits, mdl);
            switch (next_res) {
            case mbi_sat:
                if (last_res == mbi_sat) {
                    itp = nullptr;
                    return l_true;
                }
                TRACE("mbi", tout << "new lits " << lits << "\n";);
                break; // continue
            case mbi_unsat: {
                if (lits.empty()) {
                    // TBD, either a => itp and itp => !b
                    // or          b => itp and itp => !a
                    itp = mk_and(itps[!turn]);
                    return l_false;
                }
                t2->block(lits);
                expr_ref lemma(mk_not(mk_and(lits)));
                TRACE("mbi", tout << lemma << "\n";);
                blocks[turn].push_back(lemma);
                itp = m.mk_implies(mk_and(blocks[!turn]), lemma);
                // TBD: compute closure over variables not in vars
                itps[turn].push_back(itp);
                lits.reset();  // or find a prefix of lits?
                break;
            }
            case mbi_augment:
                break;
            case mbi_undef:
                return l_undef;
            }
            turn = !turn;
            last_res = next_res;
        }
    }

    /**
     * One-sided pogo creates clausal interpolants.
     * It creates a set of consequences of b that are inconsistent with a.
     */
    lbool interpolator::pogo(mbi_plugin& a, mbi_plugin& b, expr_ref& itp) {
        expr_ref_vector lits(m), itps(m);
        while (true) {
            model_ref mdl;
            lits.reset();
            switch (a.check(lits, mdl)) {
            case l_true:
                switch (b.check(lits, mdl)) {
                case l_true:
                    return l_true;
                case l_false:
                    a.block(lits);
                    itps.push_back(mk_not(mk_and(lits)));
                    break;
                case l_undef:
                    return l_undef;
                }
                break;
            case l_false:
                itp = mk_and(itps);
                return l_false;
            case l_undef:
                return l_undef;
            }
        }
    }

    lbool interpolator::vurtego(mbi_plugin& a, mbi_plugin& b, expr_ref& itp, model_ref &mdl) {
        /**
           Assumptions on mbi_plugin()
           Let local be assertions local to the plugin
           Let blocked be clauses added by blocked, kept separately from local
           mbi_plugin::check(lits, mdl, bool force_model):
              if lits.empty()  and mdl == nullptr then
                  if is_sat(local & blocked) then
                      return l_true, mbp of local, mdl of local & blocked
                  else
                      return l_false
              else if !lits.empty() then
                  if is_sat(local & mdl & blocked)
                      return l_true, lits, extension of mdl to local
                  else if is_sat(local & lits & blocked)
                      if (force_model) then
                        return l_false, core of model, nullptr
                      else
                        return l_true, mbp of local, mdl of local & blocked
                  else if !is_sat(local & lits) then
                      return l_false, mbp of local, nullptr
                  else if is_sat(local & lits) && !is_sat(local & lits & blocked)
                      MISSING CASE
                      MUST PRODUCE AN IMPLICANT OF LOCAL that is inconsistent with lits & blocked
                      in this case !is_sat(local & lits & mdl) and is_sat(mdl, blocked)
                          let mdl_blocked be lits of blocked that are true in mdl
                          return l_false, core of lits & mdl_blocked, nullptr

           mbi_plugin::block(phi): add phi to blocked

           probably should use the operator() instead of check.
           mbi_augment -- means consistent with lits but not with the mdl
           mbi_sat -- means consistent with lits and mdl

         */
        expr_ref_vector lits(m), itps(m);
        while (true) {
            // when lits.empty(), this picks an A-implicant consistent with B
            // when !lits.empty(), checks whether mdl of shared vocab extends to A
            bool force_model = !lits.empty();
            switch (a.check_ag(lits, mdl, force_model)) {
            case l_true:
                if (force_model)
                    // mdl is a model for a && b
                    return l_true;
                switch (b.check_ag(lits, mdl, false)) {
                case l_true:
                    /* can return true if know that b did not change
                       the model. For now, cycle back to A.  */
                    SASSERT(!lits.empty());
                    SASSERT(mdl);
                    break;
                case l_false:
                    // Force a different A-implicant
                    a.block(lits);
                    lits.reset();
                    mdl.reset();
                    break;
                case l_undef:
                    return l_undef;
                }
            case l_false:
                if (lits.empty()) {
                    // no more A-implicants, terminate
                    itp = mk_and(itps);
                    return l_false;
                }
                // force B to pick a different model or a different implicant
                b.block(lits);
                itps.push_back(mk_not(mk_and(lits)));
                lits.reset();
                mdl.reset();
                break;
            case l_undef:
                return l_undef;
            }
        }
    }

};
