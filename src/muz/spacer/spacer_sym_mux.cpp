/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sym_mux.cpp

Abstract:

    A symbol multiplexer that helps with having multiple versions of each of a set of symbols.

Author:

    Krystof Hoder (t-khoder) 2011-9-8.

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"

#include "model/model.h"

#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_sym_mux.h"

using namespace spacer;

sym_mux::sym_mux(ast_manager & m, const std::vector<std::string> & suffixes)
    : m(m), m_ref_holder(m), m_next_sym_suffix_idx(0), m_suffixes(suffixes)
{
    for (std::string const& s : m_suffixes) {
        m_used_suffixes.insert(symbol(s.c_str()));
    }
}

std::string sym_mux::get_suffix(unsigned i) const
{
    while (m_suffixes.size() <= i) {
        std::string new_suffix;
        symbol new_syffix_sym;
        do {
            std::stringstream stm;
            stm << '_' << m_next_sym_suffix_idx;
            m_next_sym_suffix_idx++;
            new_suffix = stm.str();
            new_syffix_sym = symbol(new_suffix.c_str());
        } while (m_used_suffixes.contains(new_syffix_sym));
        m_used_suffixes.insert(new_syffix_sym);
        m_suffixes.push_back(new_suffix);
    }
    return m_suffixes[i];
}

/**
    populates a vector called tuple with func_decl's
    tuple[0] is called primary and is used as key in various maps
 */
void sym_mux::create_tuple(func_decl* prefix, unsigned arity,
                           sort * const * domain, sort * range,
                           unsigned tuple_length, decl_vector & tuple)
{
    SASSERT(tuple_length > 0);
    while (tuple.size() < tuple_length) {
        tuple.push_back(0);
    }
    SASSERT(tuple.size() == tuple_length);
    for (unsigned i = 0; i < tuple_length; i++) {

        if (tuple[i] != 0) {
            SASSERT(tuple[i]->get_arity() == arity);
            SASSERT(tuple[i]->get_range() == range);
            //domain should match as well, but we won't bother
            //checking an array equality
        } else {
            std::string name = prefix->get_name().str();
            name += get_suffix(i);
            tuple[i] = m.mk_func_decl(symbol(name.c_str()), arity,
                                      domain, range);
        }
        m_ref_holder.push_back(tuple[i]);
        m_sym2idx.insert(tuple[i], i);
        m_sym2prim.insert(tuple[i], tuple[0]);
    }

    m_prim2all.insert(tuple[0], tuple);
    m_prefix2prim.insert(prefix, tuple[0]);
    m_prim2prefix.insert(tuple[0], prefix);
    m_ref_holder.push_back(prefix);
}

/**
   extends a tuple in which prim is primary to the given size
*/
void sym_mux::ensure_tuple_size(func_decl * prim, unsigned sz) const
{
    SASSERT(m_prim2all.contains(prim));
    decl_vector& tuple = m_prim2all.find_core(prim)->get_data().m_value;
    SASSERT(tuple[0] == prim);

    if (sz <= tuple.size()) { return; }

    func_decl * prefix;
    TRUSTME(m_prim2prefix.find(prim, prefix));
    std::string prefix_name = prefix->get_name().bare_str();
    for (unsigned i = tuple.size(); i < sz; ++i) {
        std::string name = prefix_name + get_suffix(i);
        func_decl * new_sym =
            m.mk_func_decl(symbol(name.c_str()), prefix->get_arity(),
                           prefix->get_domain(), prefix->get_range());

        tuple.push_back(new_sym);
        m_ref_holder.push_back(new_sym);
        m_sym2idx.insert(new_sym, i);
        m_sym2prim.insert(new_sym, prim);
    }
}

/** given a func_decl with src_idx returns its version with tgt_idx */
func_decl * sym_mux::conv(func_decl * sym,
                          unsigned src_idx, unsigned tgt_idx) const {
    if (src_idx == tgt_idx) { return sym; }
    func_decl * prim = (src_idx == 0) ? sym : get_primary(sym);
    if (tgt_idx > src_idx) {
        ensure_tuple_size(prim, tgt_idx + 1);
    }
    decl_vector & sym_vect = m_prim2all.find_core(prim)->get_data().m_value;
    SASSERT(sym_vect[src_idx] == sym);
    return sym_vect[tgt_idx];
}


struct sym_mux::formula_checker {
    formula_checker(const sym_mux & parent, unsigned idx) :
        m_parent(parent), m_idx(idx),
        m_found_what_needed(false) {}

    void operator()(expr * e)
    {
        if (m_found_what_needed || !is_app(e)) { return; }

        func_decl * sym = to_app(e)->get_decl();
        unsigned sym_idx;
        if (!m_parent.try_get_index(sym, sym_idx)) { return; }

        bool have_idx = sym_idx == m_idx;
        m_found_what_needed = !have_idx;

    }

    bool all_have_idx() const {return !m_found_what_needed;}


private:
    const sym_mux & m_parent;
    unsigned m_idx;

    /**
    If we check whether all muxed symbols are of given index, we look for
    counter-examples, checking whether form contains a muxed symbol of an index,
    we look for symbol of index m_idx.
    */
    bool m_found_what_needed;
};


bool sym_mux::is_homogenous_formula(expr * e, unsigned idx) const
{
    expr_mark visited;
    formula_checker chck(*this, idx);
    for_each_expr(chck, visited, e);
    return chck.all_have_idx();
}

struct sym_mux::conv_rewriter_cfg : public default_rewriter_cfg {
private:
    ast_manager & m;
    const sym_mux & m_parent;
    unsigned m_from_idx;
    unsigned m_to_idx;
    bool m_homogenous;
public:
    conv_rewriter_cfg(const sym_mux & parent, unsigned from_idx,
                      unsigned to_idx, bool homogenous)
        : m(parent.get_manager()),
          m_parent(parent),
          m_from_idx(from_idx),
          m_to_idx(to_idx),
          m_homogenous(homogenous) {}

    bool get_subst(expr * s, expr * & t, proof * & t_pr)
    {
        if (!is_app(s)) { return false; }
        app * a = to_app(s);
        func_decl * sym = a->get_decl();
        if (!m_parent.has_index(sym, m_from_idx)) {
            (void) m_homogenous;
            SASSERT(!m_homogenous || !m_parent.is_muxed(sym));
            return false;
        }
        func_decl * tgt = m_parent.conv(sym, m_from_idx, m_to_idx);

        t = m.mk_app(tgt, a->get_args());
        return true;
    }
};

void sym_mux::conv_formula(expr * f, unsigned src_idx, unsigned tgt_idx,
                           expr_ref & res, bool homogenous) const {
    if (src_idx == tgt_idx) {
        res = f;
        return;
    }
    conv_rewriter_cfg r_cfg(*this, src_idx, tgt_idx, homogenous);
    rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
    rwr(f, res);
}
