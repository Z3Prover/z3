/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_fixer.h

Abstract:

    Model-based quantifier instantiation model-finder plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-10-02

Notes:
   
    Derives from smt/smt_model_finder.cpp

    Contains exclusively functionality that adjusts a model to make it
    easier to satisfy relevant universally quantified literals.

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "solver/solver.h"
#include "model/model_macro_solver.h"

namespace euf {
    class solver;
}

namespace q {

    class solver;

    typedef obj_hashtable<func_decl> func_decl_set;

    class projection_function {
    public:
        virtual ~projection_function() {}
        virtual expr* mk_lt(expr* a, expr* b) = 0;
        virtual bool operator()(expr* a, expr* b) const = 0;
    };

    /**
    * meta-data for a projection function for f at index idx (indexed-decl).
    * The meta-data contains the set of model values that the idx'th argument of f
    * has and a map from model values to terms and back.
    */
    struct projection_meta_data {
        projection_meta_data(ast_manager& m) : values(m) {}
        expr_ref_vector values;
        obj_map<expr, expr*> v2t;
        obj_map<expr, expr*> t2v;
    };

    struct indexed_decl {
        func_decl* f;
        unsigned   idx;
        indexed_decl() : f(nullptr), idx(0) {}
        indexed_decl(func_decl* f, unsigned idx): f(f), idx(idx) {}
        struct hash { unsigned operator()(indexed_decl const& d) const { return d.idx + d.f->hash(); } };
        struct eq { bool operator()(indexed_decl const& a, indexed_decl const& b) const { return a.idx == b.idx && a.f == b.f; } };
    };

    class model_fixer : public quantifier2macro_infos {
        euf::solver&        ctx;      
        solver&             m_qs;
        ast_manager&        m;
        obj_map<quantifier, quantifier_macro_info*> m_q2info;
        func_decl_dependencies                      m_dependencies;
        obj_map<sort, projection_function*>         m_projections;
        map<indexed_decl, projection_meta_data*, indexed_decl::hash, indexed_decl::eq>    m_projection_data;
        scoped_ptr_vector<projection_meta_data>     m_projection_pinned;

        void add_projection_functions(model& mdl, ptr_vector<quantifier> const& qs);
        void add_projection_functions(model& mdl, func_decl* f);
        expr_ref add_projection_function(model& mdl, func_decl* f, unsigned idx);
        void collect_partial_functions(ptr_vector<quantifier> const& qs, func_decl_set& fns);
        projection_function* get_projection(sort* srt);

    public:

        model_fixer(euf::solver& ctx, solver& qs);
        ~model_fixer() override {}

        /**
         * Update model in order to best satisfy quantifiers.
         * For the array property fragment, update the model
         * such that the range of functions behaves monotonically 
         * based on regions over the inputs.
         */
        void operator()(model& mdl);

        quantifier_macro_info* operator()(quantifier* q) override;

        projection_meta_data* operator()(func_decl* f, unsigned idx) const {
            projection_meta_data* r = nullptr;
            m_projection_data.find(indexed_decl(f, idx), r);
            return r;
        }
        
    };

}
