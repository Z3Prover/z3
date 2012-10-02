/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_generalizers.h

Abstract:

    Generalizer plugins.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-22.

Revision History:

--*/

#ifndef _PDR_GENERALIZERS_H_
#define _PDR_GENERALIZERS_H_

#include "pdr_context.h"
#include "arith_decl_plugin.h"

namespace pdr {

    class bool_model_evaluation_generalizer : public model_generalizer {        
        ternary_model_evaluator m_model_evaluator;
    public:
        bool_model_evaluation_generalizer(context& ctx, ast_manager& m) : model_generalizer(ctx), m_model_evaluator(m) {}
        virtual ~bool_model_evaluation_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& cube);
    };

    class core_bool_inductive_generalizer : public core_generalizer {
        unsigned m_failure_limit;
    public:
        core_bool_inductive_generalizer(context& ctx, unsigned failure_limit) : core_generalizer(ctx), m_failure_limit(failure_limit) {}
        virtual ~core_bool_inductive_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
    };

    class core_farkas_generalizer : public core_generalizer {
        farkas_learner m_farkas_learner;
    public:
        core_farkas_generalizer(context& ctx, ast_manager& m, front_end_params& p);
        virtual ~core_farkas_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);  
        virtual void collect_statistics(statistics& st) const;
    };

    class model_precond_generalizer : public model_generalizer {
    public:
        model_precond_generalizer(context& ctx): model_generalizer(ctx) {}
        virtual ~model_precond_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& cube);
    };

    class model_farkas_generalizer : public model_generalizer {
    public:
        model_farkas_generalizer(context& ctx) : model_generalizer(ctx) {}
        virtual ~model_farkas_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& cube);
    };

    class core_farkas_properties_generalizer : public core_generalizer {
    public:
        core_farkas_properties_generalizer(context& ctx): core_generalizer(ctx) {}
        virtual ~core_farkas_properties_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);        
    };

    class model_evaluation_generalizer : public model_generalizer {        
        th_rewriter_model_evaluator m_model_evaluator;
    public:        
        model_evaluation_generalizer(context& ctx, ast_manager& m) : model_generalizer(ctx), m_model_evaluator(m) {}
        virtual ~model_evaluation_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& cube);
    };

    class core_multi_generalizer : public core_generalizer {
    public:
        core_multi_generalizer(context& ctx): core_generalizer(ctx) {}
        virtual ~core_multi_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
    };

    class core_interpolant_generalizer : public core_generalizer {
    public:
        core_interpolant_generalizer(context& ctx): core_generalizer(ctx) {}
        virtual ~core_interpolant_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
    };

    class core_induction_generalizer : public core_generalizer {
        class imp;
    public:
        core_induction_generalizer(context& ctx): core_generalizer(ctx) {}
        virtual ~core_induction_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
    };
};
#endif
