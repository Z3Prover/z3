/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    model_instance_generator.h

Abstract:

    Array and datatype witnesses for model-based quantifier instantiation.

--*/
#pragma once

#include "ast/array_decl_plugin.h"
#include "model/model_core.h"

class model_instance_generator {
public:
    struct context {
        virtual ~context() = default;
        virtual model_core& get_model() = 0;
        // Ground terms from the owning engine; no E-graph representation escapes this interface.
        virtual void get_terms(expr_ref_vector& terms) = 0;
        // Replace model values by closed terms usable in the owning engine.
        virtual expr_ref rewrite_value(expr* e) = 0;
        virtual void add_instance(quantifier* q, expr_ref_vector const& bindings) = 0;
    };

private:
    context& m_context;
    ast_manager& m;
    array_util m_array;
    expr_ref_vector m_terms;
    bool m_terms_initialized = false;

    bool is_auxiliary(expr* e) const;
    void collect_values(quantifier* q, sort* s, expr_ref_vector& values) const;
    bool repair_bindings(expr_ref_vector& bindings) const;
    void add_lambda_instances(quantifier* q, expr_ref_vector const& bindings);
    void add_guarded_instances(quantifier* q, expr_ref_vector const& bindings);
    void add_datatype_instances(quantifier* q, expr_ref_vector const& bindings);
    void add_store_instances(quantifier* q, expr_ref_vector const& bindings, ptr_vector<func_decl> const& bases);

public:
    explicit model_instance_generator(context& ctx);

    // Apply counterexample entries to the closest existing array constant.
    expr_ref mk_store_instance(func_decl* f, model_core& cex, func_decl*& base);
    expr_ref as_array_to_stores(expr* e, model_core& cex);
    // Bindings and their optional store bases are in declaration order.
    void operator()(quantifier* q, expr_ref_vector const& bindings, ptr_vector<func_decl> const& bases);
};
