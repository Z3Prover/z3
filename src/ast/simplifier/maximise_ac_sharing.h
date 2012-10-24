/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    maximise_ac_sharing.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-22.

Revision History:

--*/
#ifndef _MAXIMISE_AC_SHARING_H_
#define _MAXIMISE_AC_SHARING_H_

#include"simplifier.h"
#include"hashtable.h"
#include"bv_decl_plugin.h"
#include"region.h"

/**
   \brief Functor used to maximise the amount of shared terms in an expression.
   The idea is to rewrite AC terms to maximise sharing.
   Example:

   (f (bvadd a (bvadd b c)) (bvadd a (bvadd b d)))

   is rewritten to:

   (f (bvadd (bvadd a b) c) (bvadd (bvadd a b) d))

   \warning This class uses an opportunistic heuristic to maximise sharing.
   There is no guarantee that the optimal expression will be produced.
*/
class maximise_ac_sharing {
    
    struct entry {
        func_decl * m_decl;
        expr *      m_arg1;
        expr *      m_arg2;

        entry(func_decl * d = 0, expr * arg1 = 0, expr * arg2 = 0):m_decl(d), m_arg1(arg1), m_arg2(arg2) {
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
    class ac_plugin : public simplifier_plugin {
        maximise_ac_sharing & m_owner;
        svector<decl_kind>    m_kinds; //!< kinds to be processed
    public:
        ac_plugin(symbol const & fname, ast_manager & m, maximise_ac_sharing & owner);
        void register_kind(decl_kind k);
        virtual ~ac_plugin();
        virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    };

    friend class ac_plugin;

private:
    ast_manager &     m_manager;
    simplifier        m_simplifier;
    bool              m_init;
    region            m_region;
    cache             m_cache;
    ptr_vector<entry> m_entries;
    unsigned_vector   m_scopes;

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
    void register_plugin(ac_plugin * p) { m_simplifier.register_plugin(p); }
public:
    maximise_ac_sharing(ast_manager & m);
    virtual ~maximise_ac_sharing();
    void operator()(expr * s, expr_ref & r, proof_ref & p);
    void push_scope();
    void pop_scope(unsigned num_scopes);
    void reset();
    ast_manager & get_manager() { return m_manager; }
};

class maximise_bv_sharing : public maximise_ac_sharing {
    bv_util m_util;
protected:
    virtual void init_core();
    virtual bool is_numeral(expr * n) const;
public:
    maximise_bv_sharing(ast_manager & m);
};

#endif /* _MAXIMISE_AC_SHARING_H_ */

