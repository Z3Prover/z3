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

#include "qe/mbp/mbp_arith.h"
#include "qe/mbp/mbp_plugin.h"
#include "util/lbool.h"

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
        func_decl_ref_vector     m_shared_trail;
        obj_hashtable<func_decl> m_shared;
        svector<lbool>           m_is_shared;
        std::function<expr*(expr*)> m_rep;

        lbool is_shared_cached(expr* e);
    public:
        mbi_plugin(ast_manager& m): m(m), m_shared_trail(m) {}
        virtual ~mbi_plugin() {}

        /**
         * Set the shared symbols.
         */
        void set_shared(func_decl_ref_vector const& vars) {
            m_shared_trail.reset();
            m_shared.reset();
            m_is_shared.reset();
            m_shared_trail.append(vars);
            for (auto* f : vars) m_shared.insert(f);
        }

        void set_shared(expr* a, expr* b);

        /**
         * Set representative (shared) expression finder.
         */
        void set_rep(std::function<expr*(expr*)>& rep) { m_rep = rep; }

        /**
         * determine whether expression/function is shared.
         */
        bool is_shared(expr* e);
        bool is_shared(func_decl* f);

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

    };

    class prop_mbi_plugin : public mbi_plugin {
        solver_ref m_solver;
    public:
        prop_mbi_plugin(solver* s);
        ~prop_mbi_plugin() override {}
        mbi_result operator()(expr_ref_vector& lits, model_ref& mdl) override;
        void block(expr_ref_vector const& lits) override;
    };

    class uflia_mbi : public mbi_plugin {
        expr_ref_vector     m_atoms;
        obj_hashtable<expr> m_atom_set;
        expr_ref_vector     m_fmls;
        solver_ref          m_solver;
        solver_ref          m_dual_solver;
        struct is_atom_proc;

        bool get_literals(model_ref& mdl, expr_ref_vector& lits);
        void collect_atoms(expr_ref_vector const& fmls);
        void order_avars(app_ref_vector& avars);

        void add_dcert(model_ref& mdl, expr_ref_vector& lits);
        void add_arith_dcert(model& mdl, expr_ref_vector& lits);
        void add_arith_dcert(model& mdl, expr_ref_vector& lits, app* a, app* b);
        app_ref_vector get_arith_vars(expr_ref_vector const& lits);
        vector<::mbp::def> arith_project(model_ref& mdl, app_ref_vector& avars, expr_ref_vector& lits);
        void project_euf(model_ref& mdl, expr_ref_vector& lits);
        void split_arith(expr_ref_vector const& lits, 
                         expr_ref_vector& alits,
                         expr_ref_vector& uflits);
    public:
        uflia_mbi(solver* s, solver* emptySolver);
        ~uflia_mbi() override {}
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
        lbool pogo(solver_factory& sf, expr* a, expr* b, expr_ref& itp);
    };

};
