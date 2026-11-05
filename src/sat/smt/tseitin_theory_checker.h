/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    tseitin_theory_checker.h

Abstract:

    Plugin for checking tseitin internalization

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07


--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/ast_util.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>

namespace tseitin {

    class theory_checker : public euf::theory_checker_plugin {
        ast_manager& m;

        expr_fast_mark1 m_mark;
        expr_fast_mark2 m_nmark;
        bool equiv(expr* a, expr* b);
        bool xor_holds(app* x, bool expected);
        
        // A marked term is false under the assignment that falsifies every
        // clause literal; the constants false and (not true) are false under
        // any assignment, so a gate over a constant needs no clause literal
        // for it.
        bool is_false_value(expr* a) {
            return m.is_false(a) || (m.is_not(a, a) && m.is_true(a));
        }

        void mark(expr* a) { m_mark.mark(a); }
        bool is_marked(expr* a) { return m_mark.is_marked(a) || is_false_value(a); }

        void nmark(expr* a) { m_nmark.mark(a); }
        bool is_nmarked(expr* a) { return m_nmark.is_marked(a); }

        void complement_mark(expr* a) {
            m_mark.mark(a);
            if (m.is_not(a, a))
                m_nmark.mark(a);
        }

        // a is true under that assignment.
        bool is_complement(expr* a) {
            if (m.is_not(a, a))
                return is_marked(a);
            else
                return is_nmarked(a) || m.is_true(a);
        }

        struct scoped_mark {
            theory_checker& pc;
            scoped_mark(theory_checker& pc): pc(pc) {}
            ~scoped_mark() { pc.m_mark.reset(); pc.m_nmark.reset(); }
        };
    public:
        theory_checker(ast_manager& m): 
            m(m) {
        }

        expr_ref_vector clause(app* jst) override;
        
        bool check(app* jst) override;

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(symbol("tseitin"), this);
        }
        
    };

}
