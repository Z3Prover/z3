/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sym_mux.h

Abstract:

    A symbol multiplexer that helps with having multiple versions of
    each of a set of symbols.

Author:

    Krystof Hoder (t-khoder) 2011-9-8.

Revision History:

--*/

#ifndef _SYM_MUX_H_
#define _SYM_MUX_H_

#include <vector>
#include <string>

#include "ast/ast.h"
#include "util/map.h"
#include "util/vector.h"

class model_core;

namespace spacer {
class sym_mux {
private:
    typedef obj_map<func_decl, unsigned> sym2u;
    typedef obj_map<func_decl, decl_vector> sym2dv;
    typedef obj_map<func_decl, func_decl *> sym2sym;
    typedef obj_map<func_decl, func_decl *> sym2pred;
    typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbols;

    ast_manager &           m;
    mutable ast_ref_vector  m_ref_holder;

    mutable unsigned       m_next_sym_suffix_idx;
    mutable symbols        m_used_suffixes;
    /** Here we have default suffixes for each of the variants */
    mutable std::vector<std::string> m_suffixes;


    /**
       Primary symbol is the 0-th variant. This member maps from primary symbol
       to vector of all its variants (including the primary variant).
    */
    sym2dv m_prim2all;

    /**
       For each symbol contains its variant index
    */
    mutable sym2u m_sym2idx;
    /**
       For each symbol contains its primary variant
    */
    mutable sym2sym m_sym2prim;

    /**
       Maps prefixes passed to the create_tuple to
       the primary symbol created from it.
    */
    sym2pred m_prefix2prim;

    /**
       Maps pripary symbols to prefixes that were used to create them.
    */
    sym2sym     m_prim2prefix;



    struct formula_checker;
    struct conv_rewriter_cfg;

    std::string get_suffix(unsigned i) const;
    void ensure_tuple_size(func_decl * prim, unsigned sz) const;

    // expr_ref isolate_o_idx(expr* e, unsigned idx) const;
public:
    sym_mux(ast_manager & m, const std::vector<std::string> & suffixes);

    ast_manager & get_manager() const { return m; }

    bool is_muxed(func_decl * sym) const { return m_sym2idx.contains(sym); }

    bool try_get_index(func_decl * sym, unsigned & idx) const
    {return m_sym2idx.find(sym, idx);}

    bool has_index(func_decl * sym, unsigned idx) const
    {
        unsigned actual_idx;
        return try_get_index(sym, actual_idx) && idx == actual_idx;
    }

    /** Return primary symbol. sym must be muxed. */
    func_decl * get_primary(func_decl * sym) const
    {
        func_decl * prim;
        TRUSTME(m_sym2prim.find(sym, prim));
        return prim;
    }

    /**
    Return primary symbol created from prefix, or 0 if the prefix was never used.
    */
    func_decl * try_get_primary_by_prefix(func_decl* prefix) const
    {
        func_decl * res;
        if(!m_prefix2prim.find(prefix, res)) {
            return nullptr;
        }
        return res;
    }

    /**
    Return symbol created from prefix, or 0 if the prefix was never used.
    */
    func_decl * try_get_by_prefix(func_decl* prefix, unsigned idx) const
    {
        func_decl * prim = try_get_primary_by_prefix(prefix);
        if(!prim) {
            return nullptr;
        }
        return conv(prim, 0, idx);
    }

    /**
    Create a multiplexed tuple of propositional constants.
    Symbols may be suplied in the tuple vector,
    those beyond the size of the array and those with corresponding positions
    assigned to zero will be created using prefix.
    Tuple length must be at least one.
    */
    void create_tuple(func_decl* prefix, unsigned arity, sort * const * domain, sort * range,
                      unsigned tuple_length, decl_vector & tuple);

    /**
    Return true if the only multiplexed symbols which e contains are of index idx.
    */
    bool is_homogenous_formula(expr * e, unsigned idx) const;


    /**
    Convert symbol sym which has to be of src_idx variant into variant tgt_idx.
    */
    func_decl * conv(func_decl * sym, unsigned src_idx, unsigned tgt_idx) const;


    /**
    Convert src_idx symbols in formula f variant into tgt_idx.
    If homogenous is true, formula cannot contain symbols of other variants.
    */
    void conv_formula(expr * f, unsigned src_idx, unsigned tgt_idx,
                      expr_ref & res, bool homogenous = true) const;


};
}

#endif
