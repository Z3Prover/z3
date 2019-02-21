/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    shared_occs.h

Abstract:

    Functor for computing the shared subterms in a given
    term.

Author:

    Leonardo de Moura (leonardo) 2011-04-01.

Revision History:
--*/
#ifndef SHARED_OCCS_H_
#define SHARED_OCCS_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"

class shared_occs_mark {
    ptr_buffer<ast> m_to_unmark;
public:
    shared_occs_mark() {}
 
    ~shared_occs_mark() {
        reset();
    }
    
    bool is_marked(ast * n) { return n->is_marked_so(); }
    void reset_mark(ast * n) { n->reset_mark_so(); }
    void mark(ast * n) { if (is_marked(n)) return; n->mark_so(true); m_to_unmark.push_back(n); }
    void reset() {
        ptr_buffer<ast>::iterator it  = m_to_unmark.begin();
        ptr_buffer<ast>::iterator end = m_to_unmark.end();
        for (; it != end; ++it) {
            reset_mark(*it);
        }
        m_to_unmark.reset();
    }
    void mark(ast * n, bool flag) { if (flag) mark(n); else reset_mark(n); } 
};

/**
   \brief Functor for computing the shared subterms in a given term.
*/
class shared_occs {
    ast_manager &       m;
    bool                m_track_atomic;
    bool                m_visit_quantifiers;
    bool                m_visit_patterns;
    expr_ref_vector     m_shared;
    typedef std::pair<expr*, unsigned> frame;
    svector<frame>      m_stack;
    bool process(expr * t, shared_occs_mark & visited);
    void insert(expr * t);
public:
    typedef obj_hashtable<expr>::iterator iterator;
    shared_occs(ast_manager & _m, bool track_atomic = false, bool visit_quantifiers = true, bool visit_patterns = false):
        m(_m),
        m_track_atomic(track_atomic),
        m_visit_quantifiers(visit_quantifiers),
        m_visit_patterns(visit_patterns),
        m_shared(m) {
    }
    ~shared_occs();
    void operator()(expr * t);
    void operator()(expr * t, shared_occs_mark & visited);
    bool is_shared(expr * t) const { return m_shared.get(t->get_id(), nullptr) != nullptr; }
    unsigned num_shared() const;
    void reset();
    void cleanup();
    void display(std::ostream & out, ast_manager & mgr) const;
};

#endif
