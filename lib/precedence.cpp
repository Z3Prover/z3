/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    precedence.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#include"precedence.h"
#include"warning.h"

lex_precedence::lex_precedence(unsigned n, precedence ** ps):
    m_precedences(n, ps) {
}

lex_precedence::~lex_precedence() {
    std::for_each(m_precedences.begin(), m_precedences.end(), delete_proc<precedence>());
}

int lex_precedence::compare(func_decl * f, func_decl * g) {
    int r = 0;
    ptr_vector<precedence>::iterator it  = m_precedences.begin();
    ptr_vector<precedence>::iterator end = m_precedences.end();
    for (; it != end; ++it) {
        r = (*it)->compare(f, g);
        if (r != 0)
            return r;
    }
    return r;
}

inv_precedence::inv_precedence(precedence * p):
    m_precedence(p) {
    SASSERT(p);
}

inv_precedence::~inv_precedence() {
    dealloc(m_precedence);
}

int inv_precedence::compare(func_decl * f, func_decl * g) {
    return m_precedence->compare(g, f);
}

int arbitrary_precedence::compare(func_decl * f, func_decl * g) { 
    return static_cast<int>(f->get_decl_id()) - static_cast<int>(g->get_decl_id()); 
}

int arity_precedence::compare(func_decl * f, func_decl * g) { 
    return static_cast<int>(f->get_arity()) - static_cast<int>(g->get_arity());
}

int interpreted_precedence::compare(func_decl * f, func_decl * g) {
    return static_cast<int>(f->get_family_id() == null_family_id) - static_cast<int>(g->get_family_id() == null_family_id);
}

inline int ext_precedence::get_func_pos(func_decl * f) {
    unsigned id = f->get_decl_id();
    return m_cached.get(id, m_undefined);
}

int ext_precedence::compare(func_decl * f, func_decl * g) {
    return get_func_pos(f) - get_func_pos(g);
}

ext_precedence::ext_precedence(ast_manager & m, unsigned num_decls, func_decl ** decls):
    m_undefined(num_decls),
    m_cached_domain(m) {
    for (unsigned i = 0; i < num_decls; i++) {
        m_cached.setx(decls[i]->get_decl_id(), i, m_undefined);
        m_cached_domain.push_back(decls[i]);
    }
}

ext_precedence::~ext_precedence() {
}

int abstract_user_precedence::get_decl_pos(decl * d) {
    unsigned id = d->get_decl_id();
    int pos = m_cached.get(id, -1);
    if (pos == -1) {
        if (!m_symbol2pos.find(d->get_name(), pos))
            pos = m_undefined;
        m_cached.setx(id, pos, -1);
        SASSERT(pos != -1);
    }
    return pos;
}

abstract_user_precedence::abstract_user_precedence(ast_manager & m, unsigned num_syms, symbol * syms):
    m_undefined(num_syms),
    m_cached_domain(m) {
    for (unsigned i = 0; i < num_syms; i++)
        m_symbol2pos.insert(syms[i], i);
}

abstract_user_precedence::~abstract_user_precedence() {
}

int user_precedence::compare(func_decl * f, func_decl * g) {
    return get_decl_pos(f) - get_decl_pos(g);
}

int user_sort_precedence::compare(func_decl * f, func_decl * g) {
    return get_decl_pos(f->get_range()) - get_decl_pos(g->get_range());
}

static precedence * mk_default_precedence(ast_manager & m, order_params const & params) {
    ptr_buffer<precedence> ps;
    if (!params.m_order_precedence.empty())
        ps.push_back(alloc(user_precedence, m, params.m_order_precedence.size(), params.m_order_precedence.c_ptr()));
    ps.push_back(alloc(interpreted_precedence));
    ps.push_back(alloc(arity_precedence));
    ps.push_back(alloc(arbitrary_precedence));
    return alloc(lex_precedence, ps.size(), ps.c_ptr());
}

static precedence * mk_inv_precedence(bool inv, precedence * p) {
    return inv ? alloc(inv_precedence,p) : p;
}

static precedence * mk_lex_precedence(ptr_buffer<precedence> const & ps) {
    unsigned sz = ps.size();
    if (sz == 0)
        return alloc(arbitrary_precedence);
    else if (sz == 1)
        return ps[0];
    else 
        return alloc(lex_precedence, sz, ps.c_ptr());
}

precedence * mk_precedence(ast_manager & m, order_params const & params) {
    if (params.m_order_precedence_gen.empty())
        return mk_default_precedence(m, params);

    symbol user("user");
    symbol definition("definition");
    symbol interpreted("interpreted");
    symbol frequency("frequency");
    symbol arity("arity");
    symbol arbitrary("arbitrary");
    symbol inv("-");

    ptr_buffer<precedence> ps;

    svector<symbol>::const_iterator it  =  params.m_order_precedence_gen.begin();
    svector<symbol>::const_iterator end =  params.m_order_precedence_gen.end();
    bool prev_inv = false;
    for (; it != end; ++it) {
        symbol curr = *it;
        if (curr == user) {
            if (params.m_order_precedence.empty())
                ps.push_back(mk_inv_precedence(prev_inv, alloc(user_precedence, m, params.m_order_precedence.size(), params.m_order_precedence.c_ptr())));
        }
        else if (curr == definition) {
            warning_msg("definition precedence was not implement yet.");
        }
        else if (curr == interpreted) {
            ps.push_back(mk_inv_precedence(prev_inv, alloc(interpreted_precedence)));
        }
        else if (curr == frequency) {
            warning_msg("frequency precedence was not implement yet.");
        }
        else if (curr == arity) {
            ps.push_back(mk_inv_precedence(prev_inv, alloc(arity_precedence)));
        }
        else if (curr == arbitrary) {
            ps.push_back(mk_inv_precedence(prev_inv, alloc(arbitrary_precedence)));
            // it is pointless to continue, arbitrary_precedence is a total order
            return mk_lex_precedence(ps);
        }
        else if (curr == inv) {
            prev_inv = true;
        }
        else {
            warning_msg("invalid precedence generator: ignoring atom '%s'.", curr.bare_str());
        }
    }
    
    return mk_lex_precedence(ps);
}
