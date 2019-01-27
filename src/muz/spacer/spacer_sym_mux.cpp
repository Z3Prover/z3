/*++
Copyright (c) 2018 Arie Gurfinkel and Microsoft Corporation

Module Name:

    sym_mux.cpp

Abstract:

    A symbol multiplexer that helps with having multiple versions of
    each of a set of symbols.

Author:

    Arie Gurfinkel
    Krystof Hoder (t-khoder) 2011-9-8.

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"

#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_sym_mux.h"

using namespace spacer;

sym_mux::sym_mux(ast_manager & m) : m(m) {}
sym_mux::~sym_mux() {
    for (auto &entry : m_entries) {
        dealloc(entry.m_value);
    }
}

func_decl_ref sym_mux::mk_variant(func_decl *fdecl, unsigned i) const {
    func_decl_ref v(m);
    std::string name = fdecl->get_name().str();
    std::string suffix = "_";
    suffix += i == 0 ? "n" : std::to_string(i - 1);
    name += suffix;
    v =  m.mk_func_decl(symbol(name.c_str()), fdecl->get_arity(),
                        fdecl->get_domain(), fdecl->get_range());
    return v;
}

void sym_mux::register_decl(func_decl *fdecl) {
    sym_mux_entry *entry = alloc(sym_mux_entry, m);
    entry->m_main = fdecl;
    entry->m_variants.push_back(mk_variant(fdecl, 0));
    entry->m_variants.push_back(mk_variant(fdecl, 1));

    m_entries.insert(fdecl, entry);
    m_muxes.insert(entry->m_variants.get(0), std::make_pair(entry, 0));
    m_muxes.insert(entry->m_variants.get(1), std::make_pair(entry, 1));
}
void sym_mux::ensure_capacity(sym_mux_entry &entry, unsigned sz) const {
    while (entry.m_variants.size() < sz) {
        unsigned idx = entry.m_variants.size();
        entry.m_variants.push_back (mk_variant(entry.m_main, idx));
        m_muxes.insert(entry.m_variants.back(), std::make_pair(&entry, idx));
    }
}

bool sym_mux::find_idx(func_decl * sym, unsigned & idx) const {
    std::pair<sym_mux_entry *, unsigned> entry;
    if (m_muxes.find(sym, entry)) {idx = entry.second; return true;}
    return false;
}

func_decl * sym_mux::find_by_decl(func_decl* fdecl, unsigned idx) const {
    sym_mux_entry *entry = nullptr;
    if (m_entries.find(fdecl, entry)) {
        ensure_capacity(*entry, idx+1);
        return entry->m_variants.get(idx);
    }
    return nullptr;
}

func_decl * sym_mux::shift_decl(func_decl * decl,
                                unsigned src_idx, unsigned tgt_idx) const {
    std::pair<sym_mux_entry*,unsigned> entry;
    if (m_muxes.find(decl, entry)) {
        SASSERT(entry.second == src_idx);
        ensure_capacity(*entry.first, tgt_idx + 1);
        return entry.first->m_variants.get(tgt_idx);
    }
    UNREACHABLE();
    return nullptr;
}

namespace {
struct formula_checker {
    formula_checker(const sym_mux & parent, unsigned idx) :
        m_parent(parent), m_idx(idx), m_found(false) {}

    void operator()(expr * e) {
        if (m_found || !is_app(e)) { return; }

        func_decl * sym = to_app(e)->get_decl();
        unsigned sym_idx;
        if (!m_parent.find_idx(sym, sym_idx)) { return; }

        bool have_idx = sym_idx == m_idx;
        m_found = !have_idx;
    }

    bool all_have_idx() const {return !m_found;}

private:
    const sym_mux & m_parent;
    unsigned m_idx;
    bool m_found;
};
}

bool sym_mux::is_homogenous_formula(expr * e, unsigned idx) const {
    expr_mark visited;
    formula_checker fck(*this, idx);
    for_each_expr(fck, visited, e);
    return fck.all_have_idx();
}

namespace {
struct conv_rewriter_cfg : public default_rewriter_cfg {
private:
    ast_manager & m;
    const sym_mux & m_parent;
    unsigned m_from_idx;
    unsigned m_to_idx;
    bool m_homogenous;
    expr_ref_vector m_pinned;
public:
    conv_rewriter_cfg(const sym_mux & parent, unsigned from_idx,
                      unsigned to_idx, bool homogenous)
        : m(parent.get_manager()),
          m_parent(parent),
          m_from_idx(from_idx),
          m_to_idx(to_idx),
          m_homogenous(homogenous), m_pinned(m) {(void) m_homogenous;}

    bool get_subst(expr * s, expr * & t, proof * & t_pr)
    {
        if (!is_app(s)) { return false; }
        app * a = to_app(s);
        func_decl * sym = a->get_decl();
        if (!m_parent.has_index(sym, m_from_idx)) {
            SASSERT(!m_homogenous || !m_parent.is_muxed(sym));
            return false;
        }
        func_decl * tgt = m_parent.shift_decl(sym, m_from_idx, m_to_idx);
        t = m.mk_app(tgt, a->get_args());
        m_pinned.push_back(t);
        return true;
    }
};
}

void sym_mux::shift_expr(expr * f, unsigned src_idx, unsigned tgt_idx,
                         expr_ref & res, bool homogenous) const {
    if (src_idx == tgt_idx) {res = f;}
    else {
        conv_rewriter_cfg r_cfg(*this, src_idx, tgt_idx, homogenous);
        rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
        rwr(f, res);
    }
}
