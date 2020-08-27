/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_smt.h

Abstract:

    Header for SMT theories over SAT solver

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once


#pragma once
#include "ast/ast.h"
#include "sat/sat_solver.h"

namespace sat {
    
    struct frame {
        expr* m_e;
        unsigned m_idx;
        frame(expr* e) : m_e(e), m_idx(0) {}
    };

    struct scoped_stack {
        svector<frame>& s;
        unsigned sz;
        scoped_stack(svector<frame>& s):s(s), sz(s.size()) {}
        ~scoped_stack() { s.shrink(sz); }
    };

    class sat_internalizer {
    public:
        virtual bool is_bool_op(expr* e) const = 0;
        virtual sat::literal internalize(expr* e) = 0;
        virtual sat::bool_var add_bool_var(expr* e)  = 0;
        virtual void mk_clause(literal a, literal b) = 0;
        virtual void mk_clause(literal l1, literal l2, literal l3, bool is_lemma = false) = 0;
        virtual void cache(app* t, literal l) = 0;
    };
    
    class index_base {
        extension* ex;
    public:
        index_base(extension* e): ex(e) {}
        static extension* to_extension(size_t s) { return from_index(s)->ex; }
        static index_base* from_index(size_t s) { return reinterpret_cast<index_base*>(s); }
        size_t to_index() const { return reinterpret_cast<size_t>(this); }
    };
}
