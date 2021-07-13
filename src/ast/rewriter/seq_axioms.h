/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_axioms.h

Abstract:

    Axiomatize string operations that can be reduced to 
    more basic operations.

Author:

    Nikolaj Bjorner (nbjorner) 2020-4-16

Revision History:

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_skolem.h"

namespace seq {

    class axioms {
        ast_manager&    m;
        th_rewriter&    m_rewrite;
        arith_util      a;
        seq_util        seq;
        skolem          m_sk;
        expr_ref_vector m_clause;
        expr_ref_vector m_trail;
        obj_map<expr, expr*> m_purified;
        std::function<void(expr_ref_vector const&)> m_add_clause;
        std::function<void(expr*)> m_set_phase;
        std::function<void(void)>  m_ensure_digits;

        expr_ref mk_len(expr* s);
        expr_ref mk_sub(expr* x, expr* y);
        expr_ref mk_concat(expr* e1, expr* e2, expr* e3) { return expr_ref(seq.str.mk_concat(e1, e2, e3), m); }
        expr_ref mk_concat(expr* e1, expr* e2) { return expr_ref(seq.str.mk_concat(e1, e2), m); }
        expr_ref mk_nth(expr* e, unsigned i) { return expr_ref(seq.str.mk_nth_i(e, a.mk_int(i)), m); }
        expr_ref mk_eq(expr* a, expr* b) { return expr_ref(m.mk_eq(a, b), m); }
        expr_ref mk_seq_eq(expr* a, expr* b);
        expr_ref mk_eq_empty(expr* e);

        expr_ref mk_ge_e(expr* x, expr* y);
        expr_ref mk_le_e(expr* x, expr* y);

        void gc_purify();

        expr_ref purify(expr* e);
        expr_ref mk_digit2int(expr* ch);

        void add_clause(expr_ref const& a);
        void add_clause(expr_ref const& a, expr_ref const& b);
        void add_clause(expr_ref const& a, expr_ref const& b, expr_ref const& c);
        void add_clause(expr_ref const& a, expr_ref const& b, expr_ref const& c, expr_ref const & d);
        void add_clause(expr_ref const& a, expr_ref const& b, expr_ref const& c, expr_ref const & d, expr_ref const& e);

        bool is_drop_last(expr* s, expr* i, expr* l);
        bool is_tail(expr* s, expr* i, expr* l);
        bool is_extract_prefix(expr* s, expr* i, expr* l);
        bool is_extract_suffix(expr* s, expr* i, expr* l);

        void tail_axiom(expr* e, expr* s);
        void drop_last_axiom(expr* e, expr* s);
        bool small_segment_axiom(expr* e, expr* s, expr* i, expr* l);
        void extract_prefix_axiom(expr* e, expr* s, expr* l);
        void extract_suffix_axiom(expr* e, expr* s, expr* l);
        void tightest_prefix(expr* s, expr* x);

    public:

        axioms(th_rewriter& rw);

        void set_add_clause(std::function<void(expr_ref_vector const&)>& ac) { m_add_clause = ac; }
        void set_phase(std::function<void(expr*)>& sp) { m_set_phase = sp; }
        void set_ensure_digits(std::function<void(void)>& ed) { m_ensure_digits = ed; }

        void suffix_axiom(expr* n);
        void prefix_axiom(expr* n);
        void extract_axiom(expr* n);
        void indexof_axiom(expr* n);
        void last_indexof_axiom(expr* n);
        void replace_axiom(expr* n);
        void at_axiom(expr* n);
        void nth_axiom(expr* n);
        void itos_axiom(expr* n);
        void stoi_axiom(expr* n);
        void stoi_axiom(expr* e, unsigned k);
        void itos_axiom(expr* s, unsigned k);
        void ubv2s_axiom(expr* b, unsigned k);
        void ubv2s_len_axiom(expr* b, unsigned k);
        void ubv2ch_axiom(sort* bv_sort);
        void lt_axiom(expr* n);
        void le_axiom(expr* n);
        void is_digit_axiom(expr* n);
        void str_to_code_axiom(expr* n);
        void str_from_code_axiom(expr* n);
        void unit_axiom(expr* n);
        void length_axiom(expr* n);
        void unroll_not_contains(expr* e);

        expr_ref length_limit(expr* s, unsigned k);
        expr_ref is_digit(expr* ch);

        expr_ref mk_ge(expr* x, int n) { return mk_ge_e(x, a.mk_int(n)); }
        expr_ref mk_le(expr* x, int n) { return mk_le_e(x, a.mk_int(n)); }
        expr_ref mk_ge(expr* x, rational const& n) { return mk_ge_e(x, a.mk_int(n)); }
        expr_ref mk_le(expr* x, rational const& n) { return mk_le_e(x, a.mk_int(n)); }

        void rewrite(expr_ref& e) { m_rewrite(e); }
        skolem& sk() { return m_sk; }

    };

};

