/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    maximise_ac_sharing.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-22.

Revision History:

--*/

#include"maximise_ac_sharing.h"
#include"ast_pp.h"
#include"basic_simplifier_plugin.h"

maximise_ac_sharing::ac_plugin::ac_plugin(symbol const & fname, ast_manager & m, maximise_ac_sharing & owner):
    simplifier_plugin(fname, m),
    m_owner(owner) {
}

void maximise_ac_sharing::ac_plugin::register_kind(decl_kind k) {
    m_kinds.push_back(k);
}

maximise_ac_sharing::ac_plugin::~ac_plugin() {
}

bool maximise_ac_sharing::ac_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    decl_kind k = f->get_kind();
    if (!f->is_associative())
        return false;
    if (num_args <= 2)
        return false;
    if (std::find(m_kinds.begin(), m_kinds.end(), k) == m_kinds.end())
        return false;
    ptr_buffer<expr, 128> _args;
    expr * numeral = 0;
    if (m_owner.is_numeral(args[0])) {
        numeral = args[0];
        for (unsigned i = 1; i < num_args; i++) 
            _args.push_back(args[i]);
        num_args--;
    }
    else {
        _args.append(num_args, args);
    }

    TRACE("ac_sharing_detail", tout << "before-reuse: num_args: " << num_args << "\n";);

#define MAX_NUM_ARGS_FOR_OPT 128

    // Try to reuse already created circuits.
    TRACE("ac_sharing_detail", tout << "args: "; for (unsigned i = 0; i < num_args; i++) tout << mk_pp(_args[i], m_manager) << "\n";);
    try_to_reuse:
    if (num_args > 1 && num_args < MAX_NUM_ARGS_FOR_OPT) {
        for (unsigned i = 0; i < num_args - 1; i++) {
            for (unsigned j = i + 1; j < num_args; j++) {
                if (m_owner.contains(f, _args[i], _args[j])) {
                    TRACE("ac_sharing_detail", tout << "reusing args: " << i << " " << j << "\n";);
                    _args[i] = m_manager.mk_app(f, _args[i], _args[j]);
                    SASSERT(num_args > 1);
                    for (unsigned w = j; w < num_args - 1; w++) {
                        _args[w] = _args[w+1];
                    }
                    num_args--;
                    goto try_to_reuse;
                }
            }
        }
    }

    
    // Create "tree-like circuit"
    while (true) {
        TRACE("ac_sharing_detail", tout << "tree-loop: num_args: " << num_args << "\n";);
        unsigned j  = 0;
        for (unsigned i = 0; i < num_args; i += 2, j++) {
            if (i == num_args - 1) {
                _args[j] = _args[i];
            }
            else {
                m_owner.insert(f, _args[i], _args[i+1]);
                _args[j] = m_manager.mk_app(f, _args[i], _args[i+1]);
            }
        }
        num_args = j;
        if (num_args == 1) {
            if (numeral == 0) { 
                result = _args[0];
            }
            else {
                result = m_manager.mk_app(f, numeral, _args[0]);
            }
            TRACE("ac_sharing_detail", tout << "result: " << mk_pp(result, m_manager) << "\n";);
            return true;
        }
    }

    UNREACHABLE();
    return false;
}

bool maximise_ac_sharing::contains(func_decl * f, expr * arg1, expr * arg2) {
    entry e(f, arg1, arg2);
    return m_cache.contains(&e);
}

void maximise_ac_sharing::insert(func_decl * f, expr * arg1, expr * arg2) {
    entry * e = new (m_region) entry(f, arg1, arg2);
    m_entries.push_back(e);
    m_cache.insert(e);
    m_manager.inc_ref(arg1);
    m_manager.inc_ref(arg2);
}
    
maximise_ac_sharing::maximise_ac_sharing(ast_manager & m):
    m_manager(m),
    m_simplifier(m),
    m_init(false) {
    basic_simplifier_plugin* basic_simp = alloc(basic_simplifier_plugin,m);
    m_simplifier.register_plugin(basic_simp);
}

maximise_ac_sharing::~maximise_ac_sharing() {
    restore_entries(0);
}

void maximise_ac_sharing::operator()(expr * s, expr_ref & r, proof_ref & p) {
    init();
    m_simplifier.operator()(s, r, p);
}

void maximise_ac_sharing::push_scope() {
    init();
    m_scopes.push_back(m_entries.size());
    m_region.push_scope();
}

void maximise_ac_sharing::pop_scope(unsigned num_scopes) {
    SASSERT(num_scopes <= m_scopes.size());
    unsigned new_lvl    = m_scopes.size() - num_scopes;
    unsigned old_lim    = m_scopes[new_lvl];
    restore_entries(old_lim);
    m_region.pop_scope(num_scopes);
    m_scopes.shrink(new_lvl);
}

void maximise_ac_sharing::restore_entries(unsigned old_lim) {
    unsigned i = m_entries.size();
    while (i != old_lim) {
        --i;
        entry * e = m_entries[i];
        m_manager.dec_ref(e->m_arg1);
        m_manager.dec_ref(e->m_arg2);
    }
    m_entries.shrink(old_lim);
}

void maximise_ac_sharing::reset() {
    restore_entries(0);
    m_entries.reset();
    m_cache.reset();
    m_simplifier.reset();
    m_region.reset();
    m_scopes.reset();
}

void maximise_bv_sharing::init_core() {
    maximise_ac_sharing::ac_plugin * p = alloc(maximise_ac_sharing::ac_plugin, symbol("bv"), get_manager(), *this);
    p->register_kind(OP_BADD);
    p->register_kind(OP_BMUL);
    p->register_kind(OP_BOR);
    p->register_kind(OP_BAND);
    register_plugin(p);
}

bool maximise_bv_sharing::is_numeral(expr * n) const {
    return m_util.is_numeral(n);
}

maximise_bv_sharing::maximise_bv_sharing(ast_manager & m):
    maximise_ac_sharing(m),
    m_util(m) {
}
