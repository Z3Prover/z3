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
        virtual ~core_arith_inductive_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
    };

    class core_farkas_generalizer : public core_generalizer {
        farkas_learner m_farkas_learner;
    public:
        core_farkas_generalizer(context& ctx, ast_manager& m, smt_params& p);
        virtual ~core_farkas_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);  
        virtual void collect_statistics(statistics& st) const;
    };

    class core_convex_hull_generalizer : public core_generalizer {
        ast_manager&    m;
        arith_util      a;
        expr_ref_vector m_sigma;
        expr_ref_vector m_trail;
        obj_map<func_decl, expr*> m_left;
        obj_map<func_decl, expr*> m_right;
        obj_map<expr, expr*> m_models;
        bool mk_convex(expr_ref_vector const& core, unsigned index, expr_ref_vector& conv);
        void mk_convex(expr* fml, unsigned index, expr_ref_vector& conv);
        bool mk_convex(expr* term, unsigned index, bool is_mul, expr_ref& result);
        bool translate(func_decl* fn, unsigned index, expr_ref& result);
        void method1(model_node& n, expr_ref_vector& core, bool& uses_level);
        void method2(model_node& n, expr_ref_vector& core, bool& uses_level);
        void add_variables(model_node& n, expr_ref_vector& eqs);
    public:
        core_convex_hull_generalizer(context& ctx);
        virtual ~core_convex_hull_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
    };	

    class core_multi_generalizer : public core_generalizer {
        core_bool_inductive_generalizer m_gen;
    public:
        core_multi_generalizer(context& ctx, unsigned max_failures): core_generalizer(ctx), m_gen(ctx, max_failures) {}
        virtual ~core_multi_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level);
        virtual void operator()(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores);
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
