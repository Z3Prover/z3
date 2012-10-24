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

    class core_multi_generalizer : public core_generalizer {
        core_bool_inductive_generalizer m_gen;
    public:
        core_multi_generalizer(context& ctx, unsigned max_failures): core_generalizer(ctx), m_gen(ctx, max_failures) {}
        virtual ~core_multi_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
        virtual void operator()(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores);
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
