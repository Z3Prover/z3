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

#include "qe/qe_arith.h"

namespace qe {
    enum mbi_result {
        mbi_sat,
        mbi_unsat,
        mbi_augment,
        mbi_undef,
    };

    class mbi_plugin {
    protected:
        ast_manager& m;
        func_decl_ref_vector m_shared;
    public:
        mbi_plugin(ast_manager& m): m(m), m_shared(m) {}
        virtual ~mbi_plugin() {}

        /**
         * Set the shared symbols.
         */
        virtual void set_shared(func_decl_ref_vector const& vars) {
            m_shared.reset();
            m_shared.append(vars);
        }

        /**
         * \brief Utility that works modulo a background state.
         * - vars
         *   variables to preferably project onto (other variables would require quantification to fit interpolation signature)
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
        virtual mbi_result operator()(expr_ref_vector& lits, model_ref& mdl) = 0;

        /**
         * \brief Block conjunction of lits from future mbi_augment or mbi_sat.
         */
        virtual void block(expr_ref_vector const& lits) = 0;

        /**
         * \brief perform a full check, consume internal auguments if necessary.
         */
        lbool check(expr_ref_vector& lits, model_ref& mdl);

        virtual lbool check_ag(expr_ref_vector& lits, model_ref& mdl, bool force_model) {
            return l_undef;
        }


    };

    class prop_mbi_plugin : public mbi_plugin {
        solver_ref m_solver;
    public:
        prop_mbi_plugin(solver* s);
        ~prop_mbi_plugin() override {}
        mbi_result operator()(expr_ref_vector& lits, model_ref& mdl) override;
        void block(expr_ref_vector const& lits) override;
    };


    class euf_arith_mbi_plugin : public mbi_plugin {
        expr_ref_vector     m_atoms;
        obj_hashtable<expr> m_atom_set;
        expr_ref_vector     m_fmls;
        solver_ref          m_solver;
        solver_ref          m_dual_solver;
        struct is_atom_proc;
        struct is_arith_var_proc;

        app_ref_vector get_arith_vars(model_ref& mdl, expr_ref_vector& lits, app_ref_vector& proxies);
        bool get_literals(model_ref& mdl, expr_ref_vector& lits);
        void collect_atoms(expr_ref_vector const& fmls);
        void project_euf(model_ref& mdl, expr_ref_vector& lits, app_ref_vector& avars);
        vector<std::pair<rational, app*>> sort_proxies(model_ref& mdl, app_ref_vector const& proxies);
        void minimize_span(model_ref& mdl, app_ref_vector& avars, app_ref_vector const& proxies);
        void order_avars(model_ref& mdl, expr_ref_vector& lits, app_ref_vector& avars, app_ref_vector const& proxies);
        void substitute(vector<def> const& defs, expr_ref_vector& lits);
        void filter_private_arith(app_ref_vector& avars);
    public:
        euf_arith_mbi_plugin(solver* s, solver* emptySolver);
        ~euf_arith_mbi_plugin() override {}
        mbi_result operator()(expr_ref_vector& lits, model_ref& mdl) override;
        void project(model_ref& mdl, expr_ref_vector& lits);
        void block(expr_ref_vector const& lits) override;
    };

    /**
     * use cases for interpolation.
     */
    class interpolator {
        ast_manager&         m;
    public:
        interpolator(ast_manager& m):m(m) {}
        lbool pingpong(mbi_plugin& a, mbi_plugin& b, expr_ref& itp);
        lbool pogo(mbi_plugin& a, mbi_plugin& b, expr_ref& itp);
        lbool vurtego(mbi_plugin &a, mbi_plugin &b, expr_ref &itp, model_ref &mdl);
    };

};
