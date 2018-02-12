/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    maximize_ac_sharing.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-22.

Revision History:

--*/

#include "ast/rewriter/maximize_ac_sharing.h"
#include "ast/ast_pp.h"


void maximize_ac_sharing::register_kind(decl_kind k) {
    m_kinds.push_back(k);
}


br_status maximize_ac_sharing::reduce_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result, proof_ref& result_pr) {
    decl_kind k = f->get_kind();
    if (!f->is_associative())
        return BR_FAILED;
    if (num_args <= 2)
        return BR_FAILED;
    if (std::find(m_kinds.begin(), m_kinds.end(), k) == m_kinds.end())
        return BR_FAILED;
    ptr_buffer<expr, 128> _args;
    expr * numeral = nullptr;
    if (is_numeral(args[0])) {
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
    TRACE("ac_sharing_detail", tout << "args: "; for (unsigned i = 0; i < num_args; i++) tout << mk_pp(_args[i], m) << "\n";);
    try_to_reuse:
    if (num_args > 1 && num_args < MAX_NUM_ARGS_FOR_OPT) {
        for (unsigned i = 0; i + 1 < num_args; i++) {
            for (unsigned j = i + 1; j < num_args; j++) {
                if (contains(f, _args[i], _args[j])) {
                    TRACE("ac_sharing_detail", tout << "reusing args: " << i << " " << j << "\n";);
                    _args[i] = m.mk_app(f, _args[i], _args[j]);
                    SASSERT(num_args > 1);
                    for (unsigned w = j; w + 1 < num_args; w++) {
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
                insert(f, _args[i], _args[i+1]);
                _args[j] = m.mk_app(f, _args[i], _args[i+1]);
            }
        }
        num_args = j;
        if (num_args == 1) {
            if (numeral == nullptr) {
                result = _args[0];
            }
            else {
                result = m.mk_app(f, numeral, _args[0]);
            }
            TRACE("ac_sharing_detail", tout << "result: " << mk_pp(result, m) << "\n";);
            return BR_DONE;
        }
    }

    UNREACHABLE();
    return BR_FAILED;
}

bool maximize_ac_sharing::contains(func_decl * f, expr * arg1, expr * arg2) {
    entry e(f, arg1, arg2);
    return m_cache.contains(&e);
}

void maximize_ac_sharing::insert(func_decl * f, expr * arg1, expr * arg2) {
    entry * e = new (m_region) entry(f, arg1, arg2);
    m_entries.push_back(e);
    m_cache.insert(e);
    m.inc_ref(arg1);
    m.inc_ref(arg2);
}
    
maximize_ac_sharing::maximize_ac_sharing(ast_manager & m):
    m(m),
    m_init(false) {
}

maximize_ac_sharing::~maximize_ac_sharing() {
    restore_entries(0);
}


void maximize_ac_sharing::push_scope() {
    init();
    m_scopes.push_back(m_entries.size());
    m_region.push_scope();
}

void maximize_ac_sharing::pop_scope(unsigned num_scopes) {
    SASSERT(num_scopes <= m_scopes.size());
    unsigned new_lvl    = m_scopes.size() - num_scopes;
    unsigned old_lim    = m_scopes[new_lvl];
    restore_entries(old_lim);
    m_region.pop_scope(num_scopes);
    m_scopes.shrink(new_lvl);
}

void maximize_ac_sharing::restore_entries(unsigned old_lim) {
    unsigned i = m_entries.size();
    while (i != old_lim) {
        --i;
        entry * e = m_entries[i];
        m_cache.remove(e);
        m.dec_ref(e->m_arg1);
        m.dec_ref(e->m_arg2);
    }
    m_entries.shrink(old_lim);
}

void maximize_ac_sharing::reset() {
    m_cache.reset();
}

void maximize_bv_sharing::init_core() {
    register_kind(OP_BADD);
    register_kind(OP_BMUL);
    register_kind(OP_BOR);
    register_kind(OP_BAND);
}

bool maximize_bv_sharing::is_numeral(expr * n) const {
    return m_util.is_numeral(n);
}

maximize_bv_sharing::maximize_bv_sharing(ast_manager & m):
    maximize_ac_sharing(m),
    m_util(m) {
}
