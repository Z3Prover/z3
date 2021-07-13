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
#include "ast/rewriter/seq_axioms.h"
#include "smt/smt_theory.h"

namespace smt {

    class seq_axioms {
        theory&        th;
        th_rewriter&   m_rewrite;
        ast_manager&   m;
        arith_util     a;
        seq_util       seq;
        seq::skolem    m_sk;
        seq::axioms    m_ax;
        bool           m_digits_initialized;

        literal mk_eq_empty(expr* e, bool phase = true) { return mk_eq_empty2(e, phase); }
        context& ctx() { return th.get_context(); }
        literal mk_eq(expr* a, expr* b);
        literal mk_literal(expr* e);
        literal mk_seq_eq(expr* a, expr* b) { SASSERT(seq.is_seq(a) && seq.is_seq(b)); return mk_literal(m_sk.mk_eq(a, b)); }

        expr_ref mk_len(expr* s);
        expr_ref mk_sub(expr* x, expr* y);
        expr_ref mk_concat(expr* e1, expr* e2, expr* e3) { return expr_ref(seq.str.mk_concat(e1, e2, e3), m); }
        expr_ref mk_concat(expr* e1, expr* e2) { return expr_ref(seq.str.mk_concat(e1, e2), m); }
        expr_ref mk_nth(expr* e, unsigned i) { return expr_ref(seq.str.mk_nth_i(e, a.mk_int(i)), m); }
        literal mk_ge_e(expr* x, expr* y) { return mk_literal(a.mk_ge(x, y)); }
        literal mk_le_e(expr* x, expr* y) { return mk_literal(a.mk_le(x, y)); }
        void add_axiom(literal l1, literal l2 = null_literal, literal l3 = null_literal, 
                       literal l4 = null_literal, literal l5 = null_literal) { add_axiom5(l1, l2, l3, l4, l5); }

        void ensure_digit_axiom();
        void add_clause(expr_ref_vector const& lits);
        void set_phase(expr* e);


    public:

        seq_axioms(theory& th, th_rewriter& r);

        // we rely on client to supply the following functions:
        std::function<void(literal l1, literal l2, literal l3, literal l4, literal l5)> add_axiom5;
        std::function<literal(expr*,bool)> mk_eq_empty2;

        void add_suffix_axiom(expr* n) { m_ax.suffix_axiom(n); }
        void add_prefix_axiom(expr* n) { m_ax.prefix_axiom(n); }
        void add_extract_axiom(expr* n) { m_ax.extract_axiom(n); }
        void add_indexof_axiom(expr* n) { m_ax.indexof_axiom(n); }
        void add_last_indexof_axiom(expr* n) { m_ax.last_indexof_axiom(n); }
        void add_replace_axiom(expr* n) { m_ax.replace_axiom(n); }
        void add_at_axiom(expr* n) { m_ax.at_axiom(n); }
        void add_nth_axiom(expr* n) { m_ax.nth_axiom(n); }
        void add_itos_axiom(expr* n) { m_ax.itos_axiom(n); }
        void add_stoi_axiom(expr* n) { m_ax.stoi_axiom(n); }
        void add_stoi_axiom(expr* e, unsigned k) { m_ax.stoi_axiom(e, k); }
        void add_itos_axiom(expr* s, unsigned k) { m_ax.itos_axiom(s, k); }
        void add_ubv2s_axiom(expr* b, unsigned k) { m_ax.ubv2s_axiom(b, k); }
        void add_ubv2s_len_axiom(expr* b, unsigned k) { m_ax.ubv2s_len_axiom(b, k); }
        void add_ubv2ch_axioms(sort* s) { m_ax.ubv2ch_axiom(s); }
        void add_lt_axiom(expr* n) { m_ax.lt_axiom(n); }
        void add_le_axiom(expr* n) { m_ax.le_axiom(n); }
        void add_is_digit_axiom(expr* n) { m_ax.is_digit_axiom(n); }
        void add_str_to_code_axiom(expr* n) { m_ax.str_to_code_axiom(n); }
        void add_str_from_code_axiom(expr* n) { m_ax.str_from_code_axiom(n); }
        void add_unit_axiom(expr* n) { m_ax.unit_axiom(n); }
        void add_length_axiom(expr* n) { m_ax.length_axiom(n); }
        void unroll_not_contains(expr* n) { m_ax.unroll_not_contains(n); }

        literal is_digit(expr* ch) { return mk_literal(m_ax.is_digit(ch)); }
        expr_ref add_length_limit(expr* s, unsigned k) { return m_ax.length_limit(s, k); }

        literal mk_ge(expr* e, int k) { return mk_ge_e(e, a.mk_int(k)); }
        literal mk_le(expr* e, int k) { return mk_le_e(e, a.mk_int(k)); }
        literal mk_ge(expr* e, rational const& k) { return mk_ge_e(e, a.mk_int(k)); }
        literal mk_le(expr* e, rational const& k) { return mk_le_e(e, a.mk_int(k)); }

        seq::axioms& ax() { return m_ax; }

    };

};

