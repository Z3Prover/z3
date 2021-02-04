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

    class lns_context {
    public:
        virtual ~lns_context() {}
        virtual void update_model(model_ref& mdl) = 0;
        virtual void relax_cores(vector<expr_ref_vector> const& cores) = 0;
        virtual rational cost(model& mdl) = 0;
        virtual rational weight(expr* e) = 0;
        virtual expr_ref_vector const& soft() = 0;
    };

    class lns {
        ast_manager&     m;
        solver&          s;
        lns_context&     ctx;
        random_gen       m_rand;
        expr_ref_vector  m_hardened;
        expr_ref_vector  m_unprocessed;
        unsigned         m_max_conflicts { 10000 };
        unsigned         m_num_improves { 0 };
        bool             m_cores_are_valid { true };
        bool             m_enable_scoped_bounding { false };
        unsigned         m_best_bound { 0 };

        rational         m_best_cost;
        model_ref        m_best_model;
        scoped_ptr<solver::phase> m_best_phase;
        
        vector<expr_ref_vector> m_cores;
        expr_mark               m_in_core;
        expr_mark               m_is_assumption;

        struct scoped_bounding;

        void update_best_model(model_ref& mdl);
        void improve_bs();
        void improve_bs1();
        void apply_best_model();

        expr* unprocessed(unsigned i) const { return m_unprocessed[i]; }
        void  set_lns_params();
        void  save_defaults(params_ref& p);
        unsigned improve_step(model_ref& mdl);
        lbool improve_step(model_ref& mdl, expr* e);
        void relax_cores();
        unsigned improve_linear(model_ref& mdl);

    public:
        lns(solver& s, lns_context& ctx);
        void set_conflicts(unsigned c) { m_max_conflicts = c; }
        unsigned climb(model_ref& mdl);
    };
};
