/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    recfun_finder.h

Abstract:

    Detect recursive-function axioms and turn them into recfun definitions.

Author:

    Jean-Frédéric Etienne (etiennejf) 2026-09-16
    Nikolaj Bjorner (nbjorner) 2026-09-16

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/func_decl_replace.h"
#include "ast/macros/macro_util.h"
#include "ast/recfun_decl_plugin.h"

class recfun_finder : public dependent_expr_simplifier {
    struct alias {
        func_decl_ref m_src;
        func_decl_ref m_dst;
        alias(ast_manager& m, func_decl* src, func_decl* dst):
            m_src(src, m),
            m_dst(dst, m) {}
    };

    vector<alias>           m_aliases;
    obj_map<func_decl, func_decl*> m_alias_map;
    func_decl_ref_vector    m_definitions;
    func_decl_ref_vector    m_pinned;
    macro_util              m_macro_util;
    unsigned                m_num_recfuns = 0;

    struct undo_aliases;
    struct undo_definitions;

    void add_alias(func_decl* src, func_decl* dst);
    void apply_aliases();
    func_decl_replace mk_replace() const;
    bool has_quantifier() const;
    void find_recfuns_core();

public:
    recfun_finder(ast_manager& m, params_ref const& p, dependent_expr_state& s):
        dependent_expr_simplifier(m, s),
        m_definitions(m),
        m_pinned(m),
        m_macro_util(m) {}

    char const* name() const override { return "recfun-finder"; }
    void push() override;
    void reduce() override;
    void collect_statistics(statistics& st) const override { st.update("recfun-finder", m_num_recfuns); }
    void reset_statistics() override { m_num_recfuns = 0; }
};

Z3_ADD_SIMPLIFIER(recfun_finder, "recfun-finder", "detect recursive-function definitions encoded as universally quantified axioms.", alloc(recfun_finder, m, p, s));
