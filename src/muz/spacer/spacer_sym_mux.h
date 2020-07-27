/*++
Copyright (c) 2018 Arie Gurfinkel and Microsoft Corporation

Module Name:

    sym_mux.h

Abstract:

    A symbol multiplexer that helps with having multiple versions of
    each of a set of symbols.

Author:

    Arie Gurfinkel
    Krystof Hoder (t-khoder) 2011-9-8.

Revision History:

--*/

#pragma once

#include <string>

#include "ast/ast.h"
#include "util/map.h"
#include "util/vector.h"

namespace spacer {
class sym_mux {
private:
    class sym_mux_entry {
    public:
        func_decl_ref m_main;
        func_decl_ref_vector m_variants;
        sym_mux_entry(ast_manager &m) : m_main(m), m_variants(m) {};
    };

    typedef obj_map<func_decl, sym_mux_entry*> decl2entry_map;
    typedef obj_map<func_decl, std::pair<sym_mux_entry*, unsigned> > mux2entry_map;

    ast_manager &m;
    mutable decl2entry_map m_entries;
    mutable mux2entry_map m_muxes;

    func_decl_ref mk_variant(func_decl *fdecl, unsigned i) const;
    void ensure_capacity(sym_mux_entry &entry, unsigned sz) const;

public:
    sym_mux(ast_manager & m);
    ~sym_mux();
    ast_manager & get_manager() const { return m; }

    void register_decl(func_decl *fdecl);
    bool find_idx(func_decl * sym, unsigned & idx) const;
    bool has_index(func_decl * sym, unsigned idx) const
    {unsigned v; return find_idx(sym, v) && idx == v;}

    bool is_muxed(func_decl *fdecl) const {return m_muxes.contains(fdecl);}

    /**
       \brief Return symbol created from prefix, or 0 if the prefix
        was never used.
    */
    func_decl * find_by_decl(func_decl* fdecl, unsigned idx) const;

    /**
       \brief Return true if the only multiplexed symbols which e contains are
       of index idx.
    */
    bool is_homogenous_formula(expr * e, unsigned idx) const;


    /**
      \brief Convert symbol sym which has to be of src_idx variant
      into variant tgt_idx.
    */
    func_decl * shift_decl(func_decl * sym, unsigned src_idx, unsigned tgt_idx) const;

    /**
      \brief Convert src_idx symbols in formula f variant into
      tgt_idx.  If homogenous is true, formula cannot contain symbols
      of other variants.
    */
    void shift_expr(expr * f, unsigned src_idx, unsigned tgt_idx,
                    expr_ref & res, bool homogenous = true) const;


};
}

