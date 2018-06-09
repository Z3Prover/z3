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
    
    lbool interpolator::binary(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp) {
        ast_manager& m = vars.get_manager();
        model_ref mdl;
        literal_vector lits(m);
        bool a_turn = true;
        expr_ref_vector itp_a(m), itp_b(m);
        mbi_result last_res = mbi_undef;
        while (true) {
            auto* t1 = a_turn ? &a : &b;
            auto* t2 = a_turn ? &b : &a;
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
                    // TBD, extract the interpolants
                    // of what was blocked.
                    return l_false;
                }
                t2->block(lits);
                lits.reset();  // or find a prefix of lits?
                next_res = mbi_undef;
                a_turn = !a_turn;
                break;
            case mbi_augment:
                a_turn = !a_turn;
                break;
            case mbi_undef:
                return l_undef;                    
            }
            last_res = next_res;
        }
    }
};
