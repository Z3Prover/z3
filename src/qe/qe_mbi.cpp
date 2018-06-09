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


namespace qe {

    euf_mbi_plugin::euf_mbi_plugin(solver* s): m_solver(s) {}

    euf_mbi_plugin::~euf_mbi_plugin() {}

    mbi_result euf_mbi_plugin::operator()(
        func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) override {
        // really just a sketch of propositional at this point
        scoped_push _sp(m_solver);
        lbool r = m_solver->check_sat(lits);
        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            return mbi_unsat;
        case l_true:
            m_solver->get_model(mdl);
            // update lits? to be all propositioal literals or an implicant.
            // mdl will have map of all constants that we can walk over.
            return mbi_sat;
        case l_undef:
            return mbi_undef;
        }
    }

    void euf_mbi_plugin::block(expr_ref_vector const& lits) override {
        m_solver->assert_expr(mk_not(mk_and(lits)));
    }    
    
    /**
     * ping-pong interpolation of Gurfinkel & Vizel
     */
    lbool interpolator::binary(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp) {
        ast_manager& m = vars.get_manager();
        model_ref mdl;
        literal_vector lits(m);
        bool turn = true;
        vector<expr_ref_vector> itps, blocks;
        ipts.push_back(expr_ref_vector(m));
        ipts.push_back(expr_ref_vector(m));
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
                break; // continue
            case mbi_unsat:
                if (last_res == mbi_unsat) {
                    itp = mk_and(itps[turn]);
                    return l_false;
                }
                t2->block(lits);
                expr_ref lemma(m.mk_not(mk_and(lits)), m);
                blocks[turn].push_back(lemma);
                itps[turn].push_back(m.mk_implies(mk_and(blocks[!turn]), lemma));
                lits.reset();  // or find a prefix of lits?
                next_res = mbi_undef; // hard restart.
                break;
            case mbi_augment:
                break;
            case mbi_undef:
                return l_undef;                    
            }
            turn = !turn;
            last_res = next_res;
        }
    }
};
