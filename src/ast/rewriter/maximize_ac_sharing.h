/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    maximize_ac_sharing.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-22.

Revision History:

--*/
#pragma once

#include "util/hashtable.h"
#include "util/region.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/rewriter.h"

/**
   \brief Functor used to maximize the amount of shared terms in an expression.
   The idea is to rewrite AC terms to maximize sharing.
   Example:

   (f (bvadd a (bvadd b c)) (bvadd a (bvadd b d)))

   is rewritten to:

   (f (bvadd (bvadd a b) c) (bvadd (bvadd a b) d))

   \warning This class uses an opportunistic heuristic to maximize sharing.
   There is no guarantee that the optimal expression will be produced.
*/
class maximize_ac_sharing : public default_rewriter_cfg {
    
    struct entry {
        func_decl * m_decl;
        expr *      m_arg1;
        expr *      m_arg2;

        entry(func_decl * d = nullptr, expr * arg1 = nullptr, expr * arg2 = nullptr):m_decl(d), m_arg1(arg1), m_arg2(arg2) {
            SASSERT((d == 0 && arg1 == 0 && arg2 == 0) || (d != 0 && arg1 != 0 && arg2 != 0));
            if (arg1->get_id() > arg2->get_id())
                std::swap(m_arg1, m_arg2);
        }

        unsigned hash() const {
            unsigned a = m_decl->get_id();
            unsigned b = m_arg1->get_id();
            unsigned c = m_arg2->get_id();
            mix(a,b,c);
            return c;
        }

        bool operator==(entry const & e) const {
            return m_decl == e.m_decl && m_arg1 == e.m_arg1 && m_arg2 == e.m_arg2;
        }
    };

    typedef ptr_hashtable<entry, obj_ptr_hash<entry>, deref_eq<entry> > cache;

protected:
    void register_kind(decl_kind k);

private:
    ast_manager &     m;
    bool              m_init;
    region            m_region;
    cache             m_cache;
    ptr_vector<entry> m_entries;
    unsigned_vector   m_scopes;
    svector<decl_kind>    m_kinds; //!< kinds to be processed

    bool contains(func_decl * f, expr * arg1, expr * arg2);
    void insert(func_decl * f, expr * arg1, expr * arg2);
    void restore_entries(unsigned old_lim);
    void init() {
        if (!m_init) {
            init_core();
            m_init = true;
        }
    }
protected:
    virtual void init_core() = 0; 
    virtual bool is_numeral(expr * n) const = 0;
public:
    maximize_ac_sharing(ast_manager & m);
    virtual ~maximize_ac_sharing();
    void push_scope();
    void pop_scope(unsigned num_scopes);
    void reset();
    br_status reduce_app(func_decl* f, unsigned n, expr * const* args, expr_ref& result, proof_ref& result_pr);

};

class maximize_bv_sharing : public maximize_ac_sharing {
    bv_util m_util;
protected:
    void init_core() override;
    bool is_numeral(expr * n) const override;
public:
    maximize_bv_sharing(ast_manager & m);
};

class maximize_bv_sharing_rw : public rewriter_tpl<maximize_bv_sharing> {
    maximize_bv_sharing m_cfg;
public:
    maximize_bv_sharing_rw(ast_manager& m):
        rewriter_tpl<maximize_bv_sharing>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m)
    {} 
    void push_scope() { m_cfg.push_scope(); }
    void pop_scope(unsigned n) { m_cfg.pop_scope(n); }
    void reset() { m_cfg.reset(); }
};


