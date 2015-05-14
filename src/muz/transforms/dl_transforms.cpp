/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_transforms.cpp

Abstract:

    Default transformations.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28.

Revision History:

    Extracted from dl_context

--*/

#include"dl_transforms.h"
#include"dl_rule_transformer.h"
#include"dl_mk_coi_filter.h"
#include"dl_mk_filter_rules.h"
#include"dl_mk_interp_tail_simplifier.h"
#include"dl_mk_rule_inliner.h"
#include"dl_mk_bit_blast.h"
#include"dl_mk_array_blast.h"
#include"dl_mk_karr_invariants.h"
#include"dl_mk_magic_symbolic.h"
#include"dl_mk_quantifier_abstraction.h"
#include"dl_mk_quantifier_instantiation.h"
#include"dl_mk_subsumption_checker.h"
#include"dl_mk_scale.h"
#include"fixedpoint_params.hpp"

namespace datalog {

    void apply_default_transformation(context& ctx) {
        flet<bool> _enable_bv(ctx.bind_vars_enabled(), false);

        rule_transformer transf(ctx);
        ctx.ensure_closed();
        transf.reset();
        transf.register_plugin(alloc(datalog::mk_coi_filter, ctx));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, ctx));

        if (ctx.get_params().xform_quantify_arrays()) {
            transf.register_plugin(alloc(datalog::mk_quantifier_abstraction, ctx, 38000));
        }
        transf.register_plugin(alloc(datalog::mk_quantifier_instantiation, ctx, 37000));

        transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 35005));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 35000));
        transf.register_plugin(alloc(datalog::mk_coi_filter, ctx, 34990));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, ctx, 34980));

        //and another round of inlining
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34975));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34970));
        transf.register_plugin(alloc(datalog::mk_coi_filter, ctx, 34960));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, ctx, 34950));

        transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34940));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34930));
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34920));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34910));
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34900));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34890));
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34880));

        transf.register_plugin(alloc(datalog::mk_bit_blast, ctx, 35000));
        transf.register_plugin(alloc(datalog::mk_karr_invariants, ctx, 36010));
        transf.register_plugin(alloc(datalog::mk_scale, ctx, 36030));
        if (!ctx.get_params().xform_quantify_arrays()) {
            transf.register_plugin(alloc(datalog::mk_array_blast, ctx, 36000));
        }
        if (ctx.get_params().xform_magic()) {
            transf.register_plugin(alloc(datalog::mk_magic_symbolic, ctx, 36020));
        }
        ctx.transform_rules(transf);
    }
}
