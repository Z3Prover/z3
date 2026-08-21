/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_witness.cpp

Abstract:

    Unit tests for seq::regex_witness (ast/rewriter/seq_regex_witness.cpp): witness
    extraction, non-emptiness, and non-emptiness of an intersection.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_regex_witness.h"
#include <iostream>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class regex_witness_test {
    ast_manager      m;
    plugin_registrar m_reg;
    seq_rewriter     m_rw;
    seq::regex_witness m_wit;
    seq_util         u;
    sort_ref         m_str;
    sort_ref         m_re;
    seq::transition_mode m_mode;
    unsigned         m_fail = 0;

    seq_util::rex& re() { return u.re; }

    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref word(zstring const& s) { return expr_ref(re().mk_to_re(u.str.mk_string(s)), m); }
    expr_ref cat(expr* a, expr* b) { return expr_ref(re().mk_concat(a, b), m); }
    expr_ref alt(expr* a, expr* b) { return expr_ref(re().mk_union(a, b), m); }
    expr_ref star(expr* a) { return expr_ref(re().mk_star(a), m); }
    expr_ref comp(expr* a) { return expr_ref(re().mk_complement(a), m); }
    expr_ref inter(expr* a, expr* b) { return expr_ref(re().mk_inter(a, b), m); }
    expr_ref dotstar() { return expr_ref(re().mk_full_seq(m_re), m); }
    expr_ref none() { return expr_ref(re().mk_empty(m_re), m); }

    static char const* s(lbool l) { return l == l_true ? "true" : l == l_false ? "false" : "undef"; }

    char const* mode_name() const {
        switch (m_mode) {
        case seq::transition_mode::brzozowski_tm: return "brz";
        case seq::transition_mode::light_antimirov_tm: return "light-ant";
        }
        UNREACHABLE();
        return "";
    }

    void report(char const* name, lbool got, lbool expected) {
        bool ok = got == expected;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << mode_name() << " " << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    // The witness is checked by membership rather than by spelling: which element a
    // guard contributes is up to the guard algebra, but its length is the distance to
    // the nearest accepting state, and the word itself must be in the language.
    void check_witness(char const* name, expr* r, unsigned expected_len) {
        zstring w;
        lbool got = m_wit.get_witness(r, w);
        bool ok = got == l_true && w.length() == expected_len &&
                  m_wit.intersect_nonempty(r, word(w)) == l_true;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << mode_name() << " " << name
                  << "  witness=\"" << w.encode() << "\" (" << s(got) << ") expected length "
                  << expected_len << "\n";
    }

    void check_empty(char const* name, expr* r) {
        zstring w;
        report(name, m_wit.get_witness(r, w), l_false);
        report(name, m_wit.nonempty(r), l_false);          // must agree with the witness search
    }

public:

    regex_witness_test(seq::transition_mode mode) :
        m_reg(m), m_rw(m), m_wit(m_rw, mode), u(m),
        m_str(u.str.mk_string_sort(), m), m_re(re().mk_re(m_str), m), m_mode(mode) {}

    void run() {
        expr_ref a = word("a"), b = word("b"), ab = word("ab");

        std::cout << "=== regex_witness: witnesses ===\n";
        check_witness("abc", word("abc"), 3);
        check_witness("a*", star(a), 0);                     // the root is nullable
        check_witness("Sigma*.ab", cat(dotstar(), ab), 2);
        check_witness("a.a.b*", cat(a, cat(a, star(b))), 2);
        check_witness("(ab)*|b", alt(star(ab), b), 0);
        check_witness("~(a*)", comp(star(a)), 1);            // any single non-a character
        check_witness("(aa)* & a*", inter(star(cat(a, a)), star(a)), 0);

        std::cout << "=== regex_witness: empty languages ===\n";
        check_empty("re.none", none());
        check_empty("a* & ~(a*)", inter(star(a), comp(star(a))));
        check_empty("(aa)* & a(aa)*", inter(star(cat(a, a)), cat(a, star(cat(a, a)))));
        check_empty("~(Sigma*)", comp(dotstar()));

        std::cout << "=== regex_witness: intersections ===\n";
        report("a* & ~(a*)", m_wit.intersect_nonempty(star(a), comp(star(a))), l_false);
        report("(a|b)* & ~(a*)", m_wit.intersect_nonempty(star(alt(a, b)), comp(star(a))), l_true);
        report("Sigma*.ab & ab.Sigma*",
               m_wit.intersect_nonempty(cat(dotstar(), ab), cat(ab, dotstar())), l_true);
        report("a.Sigma* & Sigma*.b & b.Sigma*",
               m_wit.intersect_nonempty(cat(a, dotstar()), cat(b, dotstar())), l_false);
        std::cout << "=== regex_witness: state bound ===\n";
        {
            unsigned const saved = m_wit.max_states();
            m_wit.set_max_states(1);
            zstring w;
            // the root is not accepting and its expansion is already out of budget
            report("abc, max_states=1", m_wit.get_witness(word("abc"), w), l_undef);
            report("abc, max_states=1 (nonempty)", m_wit.nonempty(word("abc")), l_undef);
            // a nullable root is decided before the bound is consulted
            report("a*, max_states=1", m_wit.nonempty(star(a)), l_true);
            m_wit.set_max_states(saved);
            report("abc, bound restored", m_wit.nonempty(word("abc")), l_true);
        }

        std::cout << "=== regex_witness: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_regex_witness() {
    regex_witness_test brz(seq::transition_mode::brzozowski_tm);
    brz.run();
    regex_witness_test light_ant(seq::transition_mode::light_antimirov_tm);
    light_ant.run();
}
