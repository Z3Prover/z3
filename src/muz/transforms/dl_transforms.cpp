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

#include "muz/transforms/dl_transforms.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/transforms/dl_mk_coi_filter.h"
#include "muz/transforms/dl_mk_filter_rules.h"
#include "muz/transforms/dl_mk_interp_tail_simplifier.h"
#include "muz/transforms/dl_mk_rule_inliner.h"
#include "muz/transforms/dl_mk_bit_blast.h"
#include "muz/transforms/dl_mk_array_blast.h"
#include "muz/transforms/dl_mk_karr_invariants.h"
#include "muz/transforms/dl_mk_magic_symbolic.h"
#include "muz/transforms/dl_mk_quantifier_abstraction.h"
#include "muz/transforms/dl_mk_quantifier_instantiation.h"
#include "muz/transforms/dl_mk_subsumption_checker.h"
#include "muz/transforms/dl_mk_scale.h"
#include "muz/transforms/dl_mk_array_eq_rewrite.h"
#include "muz/transforms/dl_mk_array_instantiation.h"
#include "muz/transforms/dl_mk_elim_term_ite.h"
#include "muz/base/fp_params.hpp"

namespace datalog {

    void apply_default_transformation(context& ctx) {
        flet<bool> _enable_bv(ctx.bind_vars_enabled(), false);

        rule_transformer transf(ctx);
        ctx.ensure_closed();
        transf.reset();
        transf.register_plugin(alloc(datalog::mk_coi_filter, ctx));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, ctx));

        if (ctx.get_params().xform_instantiate_arrays()) {
            transf.register_plugin(alloc(datalog::mk_array_instantiation, ctx, 34999));
        }
        if(ctx.get_params().xform_transform_arrays())
            transf.register_plugin(alloc(datalog::mk_array_eq_rewrite, ctx, 34998));
        if (ctx.get_params().xform_quantify_arrays()) {
            transf.register_plugin(alloc(datalog::mk_quantifier_abstraction, ctx, 38000));
        }
        transf.register_plugin(alloc(datalog::mk_quantifier_instantiation, ctx, 37000));

        if (ctx.get_params().datalog_subsumption()) {
            transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 35005));
        }
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 35000));
        transf.register_plugin(alloc(datalog::mk_coi_filter, ctx, 34990));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, ctx, 34980));

        //and another round of inlining
        if (ctx.get_params().datalog_subsumption()) {
            transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34975));
        }
        transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34970));
        transf.register_plugin(alloc(datalog::mk_coi_filter, ctx, 34960));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, ctx, 34950));

        if (ctx.get_params().datalog_subsumption()) {
            transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34940));
            transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34930));
            transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34920));
            transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34910));
            transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34900));
            transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34890));
            transf.register_plugin(alloc(datalog::mk_subsumption_checker, ctx, 34880));
        }
        else {
            transf.register_plugin(alloc(datalog::mk_rule_inliner, ctx, 34930));
        }

        transf.register_plugin(alloc(datalog::mk_bit_blast, ctx, 35000));
        transf.register_plugin(alloc(datalog::mk_karr_invariants, ctx, 36010));
        transf.register_plugin(alloc(datalog::mk_scale, ctx, 36030));
        if (!ctx.get_params().xform_quantify_arrays()) {
            transf.register_plugin(alloc(datalog::mk_array_blast, ctx, 35999));
        }
        if (ctx.get_params().xform_magic()) {
            transf.register_plugin(alloc(datalog::mk_magic_symbolic, ctx, 36020));
        }

        transf.register_plugin(alloc(datalog::mk_elim_term_ite, ctx, 35010));
        ctx.transform_rules(transf);
    }
}
