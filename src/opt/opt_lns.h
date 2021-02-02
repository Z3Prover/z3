/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    opt_lns.h

Abstract:
   
    "large" neighborhood search for maxsat problem instances.

    Start with a model that we assume satisfies at least one of the soft constraint assumptions.
    Attempt to improve the model locally by invoking the SAT solver with a phase
    fixed to be the assignment that solved the previous instance.
    Local improvement is performed by hardening each soft constraint in turn.
    The soft constraints are assumed sorted by weight, such that the highest 
    weight soft constraint is first, followed by soft constraints of lower weight.

Author:

    Nikolaj Bjorner (nbjorner) 2021-02-01

--*/

#pragma once

namespace opt {

    class lns {
        ast_manager&     m;
        solver&          s;
        expr_ref_vector  m_hardened;
        expr_ref_vector  m_soft;
        unsigned         m_max_conflicts { 1000 };
        unsigned         m_num_improves { 0 };
        bool             m_cores_are_valid { true };
        bool             m_enable_scoped_bounding { false };

        vector<expr_ref_vector> m_cores;
        expr_mark               m_in_core;
        expr_mark               m_is_assumption;

        struct scoped_bounding;

        std::function<void(model_ref& m)> m_update_model;
        std::function<void(vector<expr_ref_vector> const&)> m_relax_cores;

        expr* soft(unsigned i) const { return m_soft[i]; }
        void  set_lns_params();
        void  save_defaults(params_ref& p);
        unsigned improve_step(model_ref& mdl);
        lbool improve_step(model_ref& mdl, expr* e);
        void relax_cores();
        unsigned improve_linear(model_ref& mdl);
        unsigned improve_rotate(model_ref& mdl, expr_ref_vector const& asms);
        void  setup_assumptions(model_ref& mdl, expr_ref_vector const& asms);

    public:
        lns(solver& s, std::function<void(model_ref&)>& update_model);
        void set_relax(std::function<void(vector<expr_ref_vector> const&)>& rc) { m_relax_cores = rc; }
        void set_conflicts(unsigned c) { m_max_conflicts = c; }
        unsigned climb(model_ref& mdl, expr_ref_vector const& asms);
    };
};
