/*++
Copyright (c) 2025

Module Name:

    ast_sizes.h

Abstract:

    Helper header to compute AST object sizes without circular dependencies.

--*/
#pragma once

// Forward declarations to compute sizes
class expr;
class func_decl;
class sort;

// Mock structures to compute sizes (matching the actual AST structures)
struct app_mock {
    // Inherits from expr, which has some base size
    void* vtable_ptr;     // 8 bytes
    unsigned id;          // 4 bytes
    unsigned kind_flags;  // 4 bytes (packed bitfields)
    // app-specific fields
    func_decl* m_decl;    // 8 bytes
    unsigned m_num_args;  // 4 bytes
    unsigned m_flags;     // 4 bytes (app_flags)
    expr* m_args[0];      // Variable size array
};

struct var_mock {
    void* vtable_ptr;     // 8 bytes
    unsigned id;          // 4 bytes
    unsigned kind_flags;  // 4 bytes
    // var-specific fields
    unsigned m_idx;       // 4 bytes
    sort* m_sort;         // 8 bytes
};

struct quantifier_mock {
    void* vtable_ptr;     // 8 bytes
    unsigned id;          // 4 bytes
    unsigned kind_flags;  // 4 bytes
    // quantifier-specific fields (many)
    unsigned m_kind;           // 4 bytes
    unsigned m_num_decls;      // 4 bytes
    expr* m_expr;              // 8 bytes
    sort* m_sort;              // 8 bytes
    unsigned m_depth;          // 4 bytes
    int m_weight;              // 4 bytes
    bool m_has_unused_vars;    // 1 byte
    bool m_has_labels;         // 1 byte
    unsigned m_qid;            // 4 bytes (symbol)
    unsigned m_skid;           // 4 bytes (symbol)
    unsigned m_num_patterns;   // 4 bytes
    unsigned m_num_no_patterns;// 4 bytes
    char m_patterns_decls[0];  // Variable size
};

// Size computation helpers
namespace ast_sizes {
    static constexpr size_t app_size(unsigned num_args) {
        return sizeof(app_mock) + num_args * sizeof(expr*);
    }

    static constexpr size_t var_size() {
        return sizeof(var_mock);
    }

    static constexpr size_t quantifier_base_size() {
        return sizeof(quantifier_mock);
    }

    // Common sizes
    static constexpr size_t APP_0_ARGS = app_size(0);
    static constexpr size_t APP_1_ARG  = app_size(1);
    static constexpr size_t APP_2_ARGS = app_size(2);
    static constexpr size_t APP_3_ARGS = app_size(3);
    static constexpr size_t APP_4_ARGS = app_size(4);
    static constexpr size_t VAR_SIZE = var_size();
    static constexpr size_t QUANTIFIER_SIZE = quantifier_base_size();
}