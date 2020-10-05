/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    quantifier_macro_info.h

Abstract:

    Macro solving utilities

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

Revision History:

--*/
#pragma once
#include "util/scoped_ptr_vector.h"
#include "ast/ast_ll_pp.h"
#include "ast/macros/cond_macro.h"
#include "ast/macros/macro_util.h"
#include "ast/func_decl_dependencies.h"

/**
   \brief Store relevant information regarding a particular universal quantifier.
   The information is used to (try to) build a model that satisfy the universal quantifier.
*/
class quantifier_macro_info {
protected:
    ast_manager& m;
    quantifier_ref           m_flat_q;         // (flattened) quantifier
    bool                     m_is_auf;
    bool                     m_has_x_eq_y;
    func_decl_set            m_ng_decls; // declarations used in non-ground applications (basic_family operators are ignored here).
    scoped_ptr_vector<cond_macro>   m_cond_macros;
    func_decl_ref            m_the_one; // the macro head used to satisfy the quantifier. this is useful for model checking
    void collect_macro_candidates(quantifier* q);
public:
    quantifier_macro_info(ast_manager& m, quantifier* q);
    virtual ~quantifier_macro_info() {}
    bool is_auf() const { return m_is_auf; }
    quantifier* get_flat_q() const { return m_flat_q; }
    bool has_cond_macros() const { return !m_cond_macros.empty(); }
    scoped_ptr_vector<cond_macro> const& macros() const { return m_cond_macros; }
    void set_the_one(func_decl* f) { m_the_one = f; }
    func_decl* get_the_one() const { return m_the_one; }
    bool contains_ng_decl(func_decl* f) const { return m_ng_decls.contains(f); }
    func_decl_set const& get_ng_decls() const { return m_ng_decls; }
    virtual void reset_the_one() { m_the_one = nullptr; }
    void insert_macro(cond_macro* m) { m_cond_macros.push_back(m); }
    bool unary_function_fragment() const;
    virtual std::ostream& display(std::ostream& out) const;
};
