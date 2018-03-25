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

#ifndef PDR_GENERALIZERS_H_
#define PDR_GENERALIZERS_H_

#include "muz/pdr/pdr_context.h"
#include "muz/pdr/pdr_closure.h"
#include "ast/arith_decl_plugin.h"

namespace pdr {

    class core_bool_inductive_generalizer : public core_generalizer {
        unsigned m_failure_limit;
    public:
        core_bool_inductive_generalizer(context& ctx, unsigned failure_limit) : core_generalizer(ctx), m_failure_limit(failure_limit) {}
        ~core_bool_inductive_generalizer() override {}
        void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) override;
    };

    template <typename T>
    class r_map : public map<rational, T, rational::hash_proc, rational::eq_proc> {
    };

    class core_arith_inductive_generalizer : public core_generalizer {
        typedef std::pair<expr*, unsigned> term_loc_t;
        typedef r_map<vector<term_loc_t> > bounds_t;

        ast_manager&    m;
        arith_util      a;
        expr_ref_vector m_refs;
        bounds_t        m_lb;
        bounds_t        m_ub;

        struct eq {
            expr*    m_term;
            rational m_value;
            unsigned m_i;
            unsigned m_j;
            eq(expr* t, rational const& r, unsigned i, unsigned j): m_term(t), m_value(r), m_i(i), m_j(j) {}
        };
        void reset();
        void insert_bound(bool is_lower, expr* x, rational const& r, unsigned i);
        void get_eqs(expr_ref_vector const& core, svector<eq>& eqs);
        bool substitute_alias(rational const&r, expr* x, expr* e, expr_ref& result);
    public:
        core_arith_inductive_generalizer(context& ctx);
        ~core_arith_inductive_generalizer() override {}
        void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) override;
    };

    class core_farkas_generalizer : public core_generalizer {
        farkas_learner m_farkas_learner;
    public:
        core_farkas_generalizer(context& ctx, ast_manager& m, smt_params& p);
        ~core_farkas_generalizer() override {}
        void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) override;
        void collect_statistics(statistics& st) const override;
    };


    class core_convex_hull_generalizer : public core_generalizer {
        ast_manager&    m;
        obj_map<expr, expr*> m_models;
        bool m_is_closure;
        void method1(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores);
        void method3(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores);
        bool strengthen_consequences(model_node& n, expr_ref_vector& As, expr* B);
        bool is_unsat(expr_ref_vector const& As, expr* B);
    public:
        core_convex_hull_generalizer(context& ctx, bool is_closure);
        ~core_convex_hull_generalizer() override {}
        void operator()(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores) override;
        void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) override;
    };

    class core_multi_generalizer : public core_generalizer {
        core_bool_inductive_generalizer m_gen;
    public:
        core_multi_generalizer(context& ctx, unsigned max_failures): core_generalizer(ctx), m_gen(ctx, max_failures) {}
        ~core_multi_generalizer() override {}
        void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) override;
        void operator()(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores) override;
    };

    class core_induction_generalizer : public core_generalizer {
        class imp;
    public:
        core_induction_generalizer(context& ctx): core_generalizer(ctx) {}
        ~core_induction_generalizer() override {}
        void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) override;
    };
};
#endif
