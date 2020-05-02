/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    shared_occs.cpp

Abstract:

    Functor for computing the shared subterms in a given
    term.

Author:

    Leonardo de Moura (leonardo) 2011-04-01.

Revision History:
--*/
#include "ast/shared_occs.h"
#include "ast/ast_smt2_pp.h"
#include "util/ref_util.h"

inline void shared_occs::insert(expr * t) {
    m_shared.reserve(t->get_id() + 1);
    m_shared[t->get_id()] = t;
}

void shared_occs::reset() { 
    m_shared.reset(); 
}

void shared_occs::cleanup() { 
    reset();
    m_shared.finalize();
    m_stack.finalize(); 
}

shared_occs::~shared_occs() {
    reset();
}

inline bool shared_occs::process(expr * t, shared_occs_mark & visited) {
    switch (t->get_kind()) {
    case AST_APP: {
        unsigned num_args = to_app(t)->get_num_args();
        if (t->get_ref_count() > 1 && (m_track_atomic || num_args > 0)) {
            if (visited.is_marked(t)) {
                insert(t);
                return true;
            }
            visited.mark(t);
        }
        if (num_args == 0)
            return true; // done with t
        m_stack.push_back(frame(t, 0)); // need to create frame if num_args > 0
        return false; 
    }
    case AST_VAR:
        if (m_track_atomic && t->get_ref_count() > 1) {
            if (visited.is_marked(t))
                insert(t);
            else
                visited.mark(t);
        }
        return true; // done with t
    case AST_QUANTIFIER:
        if (t->get_ref_count() > 1) {
            if (visited.is_marked(t)) {
                insert(t);
                return true; // done with t
            }
            visited.mark(t);
        }
        if (!m_visit_quantifiers)
            return true; 
        m_stack.push_back(frame(t, 0));
        return false; 
    default:
        UNREACHABLE();
        return true;
    }
}

void shared_occs::operator()(expr * t, shared_occs_mark & visited) {
    SASSERT(m_stack.empty());
    if (process(t, visited)) {
        return;
    }
    SASSERT(!m_stack.empty());
    while (!m_stack.empty()) {
    start:
        frame & fr  = m_stack.back();
        expr * curr = fr.first;
        switch (curr->get_kind()) {
        case AST_APP: {
			
            unsigned num_args = to_app(curr)->get_num_args();
			
            while (fr.second < num_args) {
                expr * arg = to_app(curr)->get_arg(fr.second);
                fr.second++;
                if (!process(arg, visited))
                    goto start;
            }
            break;
        }
        case AST_QUANTIFIER: {
            SASSERT(m_visit_quantifiers);
            unsigned num_children = m_visit_patterns ? to_quantifier(curr)->get_num_children() : 1;
            while (fr.second < num_children) {
                expr * child = to_quantifier(curr)->get_child(fr.second);
                fr.second++;
                if (!process(child, visited))
                    goto start;
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
        m_stack.pop_back();
    }
}


void shared_occs::operator()(expr * t) {
    SASSERT(m_stack.empty());
    shared_occs_mark visited;
    reset();
    operator()(t, visited);
}

void shared_occs::display(std::ostream & out, ast_manager & m) const {
    for (expr* s : m_shared) {
        if (s) {
            out << mk_ismt2_pp(s, m) << "\n";
        }
    }
}

unsigned shared_occs::num_shared() const{ 
    unsigned count = 0;
    for (expr* s : m_shared) if (s) count++;
    return count;
}
