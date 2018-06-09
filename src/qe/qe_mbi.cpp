/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    qe_mbi.cpp

Abstract:

    Model-based interpolation utilities

Author:

    Nikolaj Bjorner (nbjorner), Arie Gurfinkel 2018-6-8

Revision History:


--*/

#include "ast/ast_util.h"
#include "solver/solver.h"
#include "qe/qe_mbi.h"


namespace qe {

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
                        lits.push_back(m.mk_const(c));
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

    euf_mbi_plugin::euf_mbi_plugin(solver* s): m(s->get_manager()), m_solver(s) {}

    mbi_result euf_mbi_plugin::operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) {
        lbool r = m_solver->check_sat(lits);
        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            return mbi_unsat;
        case l_true: {
            expr_ref_vector fmls(m);
            m_solver->get_model(mdl);
            lits.reset();
            // 1. extract formulas from solver
            // 2. extract implicant over formulas
            // 3. extract equalities or other assignments over the congruence classes
            m_solver->get_assertions(fmls);
            NOT_IMPLEMENTED_YET();
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
     * TBD: also implement the one-sided versions that create clausal interpolants.
     */
    lbool interpolator::pogo(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp) {
        NOT_IMPLEMENTED_YET();
        return l_undef;
    }
};
