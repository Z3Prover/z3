/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    qe_mbi.h

Abstract:

    Model-based interpolation utilities

Author:

    Nikolaj Bjorner (nbjorner), Arie Gurfinkel 2018-6-8

Revision History:


--*/

#pragma once

namespace qe {
    enum mbi_result {
        mbi_sat,
        mbi_unsat,
        mbi_augment,
        mbi_undef,
    };

    class mbi_plugin {
    public:
        virtual ~mbi_plugin() {}
        /**
         * \brief Utility that works modulo a background state.
         * - vars
         *   variables to preferrably project onto (other variables would require quantification to fit interpolation signature)
         * - lits
         *   set of literals to check satisfiability with respect to.
         * - mdl
         *   optional model for caller.
         * on return:
         * - mbi_sat:
         *   populates mdl with a satisfying state, and lits with implicant for background state.
         * - mbi_unsat:
         *   populates lits to be inconsistent with background state.
         *   For all practical purposes it is a weakening of lits or even a subset of lits.
         * - mbi_augment:
         *   populates lits with strengthening of lits (superset)
         * - mbi_undef:
         *   inconclusive,
         */
        virtual mbi_result operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) = 0;

        /**
         * \brief Block conjunction of lits from future mbi_augment or mbi_sat.
         */
        virtual void block(expr_ref_vector const& lits) = 0;

        /**
         * \brief perform a full check, consume internal auguments if necessary.
         */
        lbool check(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl);

    };

    class prop_mbi_plugin : public mbi_plugin {
        solver_ref m_solver;
    public:
        prop_mbi_plugin(solver* s);
        ~prop_mbi_plugin() override {}
        mbi_result operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) override;
        void block(expr_ref_vector const& lits) override;
    };

    class euf_mbi_plugin : public mbi_plugin {
        ast_manager& m;
        expr_ref_vector m_atoms;
        solver_ref   m_solver;
        solver_ref   m_dual_solver;
        struct is_atom_proc;
    public:
        euf_mbi_plugin(solver* s, solver* sNot);
        ~euf_mbi_plugin() override {}
        mbi_result operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) override;
        void block(expr_ref_vector const& lits) override;
    };

    /**
     * use cases for interpolation.
     */
    class interpolator {
        ast_manager& m;
    public:
        interpolator(ast_manager& m):m(m) {}
        lbool pingpong(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp);
        lbool pogo(mbi_plugin& a, mbi_plugin& b, func_decl_ref_vector const& vars, expr_ref& itp);
    };

#if 0
    TBD some other scenario, e.g., Farkas, Cute/Beautiful/maybe even Selfless

    class solver_mbi_plugin : public mbi_plugin {
        solver_ref m_solver;
    public:
        solver_mbi_plugin(solver* s);
        ~solver_mbi_plugin() override {}
        mbi_result operator()(func_decl_ref_vector const& vars, expr_ref_vector& lits, model_ref& mdl) override;
        void block(expr_ref_vector const& lits) override;
    };


#endif
};
