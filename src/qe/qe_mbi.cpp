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

  Purify EUF1 & LIRA1 & EUF2 & LIRA2

  Then EUF1 & EUF2   |- false
       LIRA1 & LIRA2 |- false

  Sketch of approach by example:

       A: s <= 2a <= t     & f(a) = q

       B: t <= 2b <= s + 1 & f(b) != q

  1. Extract arithmetic consequences of A over shared vocabulary.

       A -> s <= t & (even(t) | s < t)

  2a. Send to B, have B solve shared variables with EUF_B.
        epsilon b . B & A_pure
        epsilon b . t <= 2b <= s + 1 & s <= t & (even(t) | s < t)
        = t <= s + 1 & (even(t) | t <= s) & s <= t & (even(t) | s < t)
        = even(t) & t = s
        b := t div 2

      B & A_pure -> B[b/t div 2] = f(t div 2) != q & t <= s + 1

  3a. Send purified result to A
      A & B_pure -> false

      Invoke the ping-pong principle to extract interpolant.

  2b. Solve for shared variables with EUF.

    epsilon a . A
  = a := (s + 1) div 2 & s < t & f((s + 1) div 2) = q

  3b. Send to B. Produces core
          s < t & f((s + 1) div 2) = q

  4b Solve again in arithmetic for shared variables with EUF.

    epsion a . A & (s >= t | f((s + 1) div 2) != q)

         a := t div 2 | s = t & f(t div 2) = q & even(t)

    Send to B, produces core (s != t | f(t div 2) != q)

  5b. There is no longer a solution for A. A is unsat.

--*/

#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/bool_rewriter.h"
#include "model/model_evaluator.h"
#include "solver/solver.h"
#include "qe/qe_mbi.h"
#include "qe/qe_term_graph.h"


namespace qe {

    lbool mbi_plugin::check(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) {
        while (true) {
            switch ((*this)(vars, lits, mdl)) {
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

    prop_mbi_plugin::prop_mbi_plugin(solver* s): m_solver(s) {}

    // sketch of propositional

    mbi_result prop_mbi_plugin::operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl)  {
        ast_manager& m = lits.m();
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
                if (vars.contains(c)) {
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
    // euf_mbi, TBD

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
        m(s->get_manager()),
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

    mbi_result euf_mbi_plugin::operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) {
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
                tg.set_vars(vars, false);
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


    /** --------------------------------------------------------------
     * ping-pong interpolation of Gurfinkel & Vizel
     * compute a binary interpolant.
     */
    lbool interpolator::pingpong(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp) {
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
            mbi_result next_res = (*t1)(vars, lits, mdl);
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
    lbool interpolator::pogo(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp) {
        expr_ref_vector lits(m), itps(m);
        while (true) {
            model_ref mdl;
            lits.reset();
            switch (a.check(vars, lits, mdl)) {
            case l_true:
                switch (b.check(vars, lits, mdl)) {
                case l_true:
                    return l_true;
                case l_false:
                    a.block(lits);
                    itps.push_back(mk_not(mk_and(lits)));
                    break;
                case l_undef:
                    return l_undef;
                }
            case l_false:
                itp = mk_and(itps);
                return l_false;
            case l_undef:
                return l_undef;
            }
        }
    }
};
