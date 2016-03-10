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

#include <sstream>
#include "ast_pp.h"
#include "for_each_expr.h"
#include "model.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "pdr_util.h"
#include "pdr_sym_mux.h"

using namespace pdr;

sym_mux::sym_mux(ast_manager & m)
    : m(m), m_ref_holder(m), 
      m_next_sym_suffix_idx(0) {
    m_suffixes.push_back("_n");
    size_t suf_sz = m_suffixes.size();
    for(unsigned i = 0; i < suf_sz; ++i) {
        symbol suff_sym = symbol(m_suffixes[i].c_str());
        m_used_suffixes.insert(suff_sym);
    }
}

std::string sym_mux::get_suffix(unsigned i) {
    while(m_suffixes.size() <= i) {
        std::string new_suffix;
        symbol new_syffix_sym;
        do {
            std::stringstream stm;
            stm<<'_'<<m_next_sym_suffix_idx;
            m_next_sym_suffix_idx++;
            new_suffix = stm.str();
            new_syffix_sym = symbol(new_suffix.c_str());
        } 
        while (m_used_suffixes.contains(new_syffix_sym));
        m_used_suffixes.insert(new_syffix_sym);
        m_suffixes.push_back(new_suffix);
    }
    std::string result = m_suffixes[i];
    return result;
}

void sym_mux::create_tuple(func_decl* prefix, unsigned arity, sort * const * domain, sort * range, 
    unsigned tuple_length, decl_vector & tuple)
{
    SASSERT(tuple_length>0);
    while(tuple.size()<tuple_length) {
        tuple.push_back(0);
    }
    SASSERT(tuple.size()==tuple_length);
    std::string pre = prefix->get_name().str();
    for(unsigned i=0; i<tuple_length; i++) {

        if (tuple[i] != 0) {
            SASSERT(tuple[i]->get_arity()==arity);
            SASSERT(tuple[i]->get_range()==range);
            //domain should match as well, but we won't bother checking an array equality
        }
        else {
            std::string name = pre+get_suffix(i);
            tuple[i] = m.mk_func_decl(symbol(name.c_str()), arity, domain, range);
        }
        m_ref_holder.push_back(tuple[i]);
        m_sym2idx.insert(tuple[i], i);
        m_sym2prim.insert(tuple[i], tuple[0]);
    }

    m_prim2all.insert(tuple[0], tuple);
    m_prefix2prim.insert(prefix, tuple[0]);
    m_prim2prefix.insert(tuple[0], prefix);
    m_prim_preds.push_back(tuple[0]);
    m_ref_holder.push_back(prefix);
}

void sym_mux::ensure_tuple_size(func_decl * prim, unsigned sz)  {
    SASSERT(m_prim2all.contains(prim));
    decl_vector& tuple = m_prim2all.find_core(prim)->get_data().m_value;
    SASSERT(tuple[0]==prim);

    if(sz <= tuple.size()) { return; }

    func_decl * prefix;
    TRUSTME(m_prim2prefix.find(prim, prefix));
    std::string prefix_name = prefix->get_name().bare_str();
    for(unsigned i = tuple.size(); i < sz; ++i) {
        std::string name = prefix_name + get_suffix(i);
        func_decl * new_sym = m.mk_func_decl(symbol(name.c_str()), prefix->get_arity(), 
                                             prefix->get_domain(), prefix->get_range());

        tuple.push_back(new_sym);
        m_ref_holder.push_back(new_sym);
        m_sym2idx.insert(new_sym, i);
        m_sym2prim.insert(new_sym, prim);
    }
}

func_decl * sym_mux::conv(func_decl * sym, unsigned src_idx, unsigned tgt_idx)
{
    if(src_idx==tgt_idx) { return sym; }
    func_decl * prim = (src_idx==0) ? sym : get_primary(sym);
    if(tgt_idx>src_idx) {
        ensure_tuple_size(prim, tgt_idx+1);
    }
    decl_vector & sym_vect = m_prim2all.find_core(prim)->get_data().m_value;
    SASSERT(sym_vect[src_idx]==sym);
    return sym_vect[tgt_idx];
}


func_decl * sym_mux::get_or_create_symbol_by_prefix(func_decl* prefix, unsigned idx, 
    unsigned arity, sort * const * domain, sort * range)
{
    func_decl * prim = try_get_primary_by_prefix(prefix);
    if(prim) {
        SASSERT(prim->get_arity()==arity);
        SASSERT(prim->get_range()==range);
        //domain should match as well, but we won't bother checking an array equality

        return conv(prim, 0, idx);
    }

    decl_vector syms;
    create_tuple(prefix, arity, domain, range, idx+1, syms);
    return syms[idx];
}

bool sym_mux::is_muxed_lit(expr * e, unsigned idx) const
{
    if(!is_app(e)) { return false; }
    app * a = to_app(e);
    if(m.is_not(a) && is_app(a->get_arg(0))) {
        a = to_app(a->get_arg(0));
    }
    return is_muxed(a->get_decl());
}


struct sym_mux::formula_checker
{
    formula_checker(const sym_mux & parent, bool all, unsigned idx) : 
        m_parent(parent), m_all(all), m_idx(idx),
        m_found_what_needed(false)
    {
    }

    void operator()(expr * e)
    {
        if(m_found_what_needed || !is_app(e)) { return; }

        func_decl * sym = to_app(e)->get_decl();
        unsigned sym_idx;
        if(!m_parent.try_get_index(sym, sym_idx)) { return; }
        
        bool have_idx = sym_idx==m_idx;

        if( m_all ? (!have_idx) : have_idx ) {
            m_found_what_needed = true;
        }

    }

    bool all_have_idx() const
    {
        SASSERT(m_all); //we were looking for the queried property
        return !m_found_what_needed;
    }

    bool some_with_idx() const
    {
        SASSERT(!m_all); //we were looking for the queried property
        return m_found_what_needed;
    }

private:
    const sym_mux & m_parent;
    bool m_all;
    unsigned m_idx;

    /**
    If we check whether all muxed symbols are of given index, we look for 
    counter-examples, checking whether form contains a muxed symbol of an index, 
    we look for symbol of index m_idx.
    */
    bool m_found_what_needed;
};

bool sym_mux::contains(expr * e, unsigned idx) const
{
    formula_checker chck(*this, false, idx);
    for_each_expr(chck, m_visited, e);
    m_visited.reset();
    return chck.some_with_idx();
}

bool sym_mux::is_homogenous_formula(expr * e, unsigned idx) const
{
    formula_checker chck(*this, true, idx);
    for_each_expr(chck, m_visited, e);
    m_visited.reset();
    return chck.all_have_idx();
}

bool sym_mux::is_homogenous(const expr_ref_vector & vect, unsigned idx) const
{
    expr * const * begin = vect.c_ptr();
    expr * const * end = begin + vect.size();
    for(expr * const * it = begin; it!=end; it++) {
        if(!is_homogenous_formula(*it, idx)) {
            return false;
        }
    }
    return true;
}

class sym_mux::index_collector {
    sym_mux const& m_parent;
    svector<bool> m_indices;
public:
    index_collector(sym_mux const& s): 
      m_parent(s) {}

    void operator()(expr * e) {    
        if (is_app(e)) {
            func_decl * sym = to_app(e)->get_decl();
            unsigned idx;
            if (m_parent.try_get_index(sym, idx)) { 
                SASSERT(idx > 0);
                --idx;
                if (m_indices.size() <= idx) {
                    m_indices.resize(idx+1, false);
                }
                m_indices[idx] = true;
            }
        }
    }

    void extract(unsigned_vector& indices) {
        for (unsigned i = 0; i < m_indices.size(); ++i) {
            if (m_indices[i]) {
                indices.push_back(i);
            }
        }
    }
};



void sym_mux::collect_indices(expr* e, unsigned_vector& indices) const {
    indices.reset();
    index_collector collector(*this);
    for_each_expr(collector, m_visited, e);
    m_visited.reset();
    collector.extract(indices);
}

class sym_mux::variable_collector {
    sym_mux const& m_parent;
    vector<ptr_vector<app> >& m_vars;
public:
    variable_collector(sym_mux const& s, vector<ptr_vector<app> >& vars): 
      m_parent(s), m_vars(vars) {}

    void operator()(expr * e) {    
        if (is_app(e)) {
            func_decl * sym = to_app(e)->get_decl();
            unsigned idx;
            if (m_parent.try_get_index(sym, idx)) { 
                SASSERT(idx > 0);
                --idx;
                if (m_vars.size() <= idx) {
                    m_vars.resize(idx+1, ptr_vector<app>());
                }
                m_vars[idx].push_back(to_app(e));
            }
        }
    }
};

void sym_mux::collect_variables(expr* e, vector<ptr_vector<app> >& vars) const {
    vars.reset();
    variable_collector collector(*this, vars);
    for_each_expr(collector, m_visited, e);
    m_visited.reset();
}

class sym_mux::hmg_checker {
    const sym_mux & m_parent;

    bool m_found_idx;
    unsigned m_idx;
    bool m_multiple_indexes;

public:
    hmg_checker(const sym_mux & parent) : 
      m_parent(parent), m_found_idx(false), m_multiple_indexes(false)
    {
    }

    void operator()(expr * e)
    {
        if(m_multiple_indexes || !is_app(e)) { return; }

        func_decl * sym = to_app(e)->get_decl();
        unsigned sym_idx;
        if(!m_parent.try_get_index(sym, sym_idx)) { return; }
        
        if(!m_found_idx) {
            m_found_idx = true;
            m_idx = sym_idx;
            return;
        }
        if(m_idx==sym_idx) { return; }
        m_multiple_indexes = true;
    }

    bool has_multiple_indexes() const
    {
        return m_multiple_indexes;
    }
};

bool sym_mux::is_homogenous_formula(expr * e) const {
    hmg_checker chck(*this);
    for_each_expr(chck, m_visited, e);
    m_visited.reset();
    return !chck.has_multiple_indexes();
}


struct sym_mux::conv_rewriter_cfg : public default_rewriter_cfg
{
private:
    ast_manager & m;
    sym_mux & m_parent;
    unsigned m_from_idx;
    unsigned m_to_idx;
    bool m_homogenous;
public:
    conv_rewriter_cfg(sym_mux & parent, unsigned from_idx, unsigned to_idx, bool homogenous) 
        : m(parent.get_manager()), 
        m_parent(parent), 
        m_from_idx(from_idx), 
        m_to_idx(to_idx),
        m_homogenous(homogenous) {}

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        if(!is_app(s)) { return false; }
        app * a = to_app(s);
        func_decl * sym = a->get_decl();
        if(!m_parent.has_index(sym, m_from_idx)) {
            SASSERT(!m_homogenous || !m_parent.is_muxed(sym));
            return false;
        }
        func_decl * tgt = m_parent.conv(sym, m_from_idx, m_to_idx);

        t = m.mk_app(tgt, a->get_args());
        return true;
    }
};

void sym_mux::conv_formula(expr * f, unsigned src_idx, unsigned tgt_idx, expr_ref & res, bool homogenous) 
{
    if(src_idx==tgt_idx) {
        res = f;
        return;
    }
    conv_rewriter_cfg r_cfg(*this, src_idx, tgt_idx, homogenous);
    rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
    rwr(f, res);
}

struct sym_mux::shifting_rewriter_cfg : public default_rewriter_cfg
{
private:
    ast_manager & m;
    sym_mux & m_parent;
    int m_shift;
public:
    shifting_rewriter_cfg(sym_mux & parent, int shift) 
        : m(parent.get_manager()), 
        m_parent(parent), 
        m_shift(shift) {}

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        if(!is_app(s)) { return false; }
        app * a = to_app(s);
        func_decl * sym = a->get_decl();

        unsigned idx;
        if(!m_parent.try_get_index(sym, idx)) {
            return false;
        }
        SASSERT(static_cast<int>(idx)+m_shift>=0);
        func_decl * tgt = m_parent.conv(sym, idx, idx+m_shift);
        t = m.mk_app(tgt, a->get_args());
        return true;
    }
};

void sym_mux::shift_formula(expr * f, int dist, expr_ref & res) 
{
    if(dist==0) {
        res = f;
        return;
    }
    shifting_rewriter_cfg r_cfg(*this, dist);
    rewriter_tpl<shifting_rewriter_cfg> rwr(m, false, r_cfg);
    rwr(f, res);
}

void sym_mux::conv_formula_vector(const expr_ref_vector & vect, unsigned src_idx, unsigned tgt_idx, 
    expr_ref_vector & res)
{
    res.reset();
    expr * const * begin = vect.c_ptr();
    expr * const * end = begin + vect.size();
    for(expr * const * it = begin; it!=end; it++) {
        expr_ref converted(m);
        conv_formula(*it, src_idx, tgt_idx, converted);
        res.push_back(converted);
    }
}

void sym_mux::filter_idx(expr_ref_vector & vect, unsigned idx) const {
    unsigned i = 0;
    while (i < vect.size()) {
        expr* e = vect[i].get();
        if (contains(e, idx) && is_homogenous_formula(e, idx)) {
            i++;
        }
        else {
            // we don't allow mixing states inside vector elements
            SASSERT(!contains(e, idx));
            vect[i] = vect.back();
            vect.pop_back();
        }
    }
}

void sym_mux::partition_o_idx(
    expr_ref_vector const& lits, 
    expr_ref_vector& o_lits,
    expr_ref_vector& other, unsigned idx) const {

    for (unsigned i = 0; i < lits.size(); ++i) {
        if (contains(lits[i], idx) && is_homogenous_formula(lits[i], idx)) {
            o_lits.push_back(lits[i]);
        }
        else {
            other.push_back(lits[i]);
        }
    }
}



class sym_mux::nonmodel_sym_checker {
    const sym_mux & m_parent;

    bool m_found;
public:
    nonmodel_sym_checker(const sym_mux & parent) : 
        m_parent(parent), m_found(false) {
    }

    void operator()(expr * e) {
        if(m_found || !is_app(e)) { return; }
        
        func_decl * sym = to_app(e)->get_decl();
        
        if(m_parent.is_non_model_sym(sym)) {
            m_found = true;
        }
    }

    bool found() const {
        return m_found;
    }
};

bool sym_mux::has_nonmodel_symbol(expr * e) const {
    nonmodel_sym_checker chck(*this);
    for_each_expr(chck, e);
    return chck.found();
}

void sym_mux::filter_non_model_lits(expr_ref_vector & vect) const {
    unsigned i = 0;
    while (i < vect.size()) {
        if (!has_nonmodel_symbol(vect[i].get())) {
            i++;
        }
        else {
            vect[i] = vect.back();
            vect.pop_back();
        }
    }
}

class sym_mux::decl_idx_comparator
{
    const sym_mux & m_parent;
public:
    decl_idx_comparator(const sym_mux & parent)
        : m_parent(parent)
    { }

    bool operator()(func_decl * sym1, func_decl * sym2)
    {
        unsigned idx1, idx2;
        if (!m_parent.try_get_index(sym1, idx1)) { idx1 = UINT_MAX; }
        if (!m_parent.try_get_index(sym2, idx2)) { idx2 = UINT_MAX; }

        if (idx1 != idx2) { return idx1<idx2; }
        return lt(sym1->get_name(), sym2->get_name());
    }
};

std::string sym_mux::pp_model(const model_core & mdl) const {
    decl_vector consts;
    unsigned sz = mdl.get_num_constants();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * d = mdl.get_constant(i);
        consts.push_back(d);
    }

    std::sort(consts.begin(), consts.end(), decl_idx_comparator(*this));

    std::stringstream res;
    
    decl_vector::iterator end = consts.end();
    for (decl_vector::iterator it = consts.begin(); it!=end; it++) {
        func_decl * d = *it;
        std::string name   = d->get_name().str();
        const char * arrow = " -> "; 
        res << name << arrow;
        unsigned indent = static_cast<unsigned>(name.length() + strlen(arrow));
        res << mk_pp(mdl.get_const_interp(d), m, indent) << "\n";

        if (it+1 != end) {
            unsigned idx1, idx2;
            if (!try_get_index(*it, idx1)) { idx1 = UINT_MAX; }
            if (!try_get_index(*(it+1), idx2)) { idx2 = UINT_MAX; }
            if (idx1 != idx2) { res << "\n"; }
        }
    }
    return res.str();
}


#if 0

class sym_mux::index_renamer_cfg : public default_rewriter_cfg{
    const sym_mux & m_parent;
    unsigned        m_idx;

public:
    index_renamer_cfg(const sym_mux & p, unsigned idx) : m_parent(p), m_idx(idx) {}

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        if (!is_app(s)) return false;
        app * a = to_app(s);
        if (a->get_family_id() != null_family_id) {
            return false;
        }
        func_decl * sym = a->get_decl();
        unsigned idx;
        if(!m_parent.try_get_index(sym, idx)) {
            return false;
        }        
        if (m_idx == idx) {
            return false;
        }
        ast_manager& m = m_parent.get_manager();
        symbol name = symbol((sym->get_name().str() + "!").c_str());
        func_decl * tgt = m.mk_func_decl(name, sym->get_arity(), sym->get_domain(), sym->get_range());
        t = m.mk_app(tgt, a->get_num_args(), a->get_args());
        return true;    
    }
};

#endif
