/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_offset_eq.h

Abstract:

    Container for maintaining equalities between lengths of sequences.

Author:

    Thai Minh Trinh 2017
    Nikolaj Bjorner (nbjorner) 2020-4-16

--*/
#pragma once

#include "util/obj_pair_hashtable.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "smt/smt_theory.h"

namespace smt {

    class seq_offset_eq {
        theory&        th;
        ast_manager&   m;
        seq_util       seq;
        arith_util     a;
        obj_hashtable<enode>             m_has_offset_equality;
        obj_pair_map<enode, enode, int>  m_offset_equalities;
        int                              m_propagation_level;

        bool match_x_minus_y(expr* e, expr*& x, expr*& y) const;
        void len_offset(expr* e, int val);
        void prop_arith_to_len_offset();

    public:

        seq_offset_eq(theory& th, ast_manager& m);
        bool empty() const { return m_offset_equalities.empty(); }
        /**
           \breif determine if r1 = r2 + offset
         */
        bool find(enode* r1, enode* r2, int& offset) const;
        bool contains(enode* r1, enode* r2) const { int offset = 0; return find(r1, r2, offset); }
        bool contains(enode* r);
        bool propagate();
        void pop_scope_eh(unsigned num_scopes);
    };

};

