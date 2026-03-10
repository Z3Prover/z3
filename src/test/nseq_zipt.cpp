/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_zipt.cpp

Abstract:

    Unit tests for theory_nseq ported from the ZIPT test suite.
    Source: https://github.com/CEisenhofer/ZIPT/blob/parikh/Test/Test.cs

    Naming convention for strings/regexes (matching ZIPT's ParseStr/ParseRegex):
      - Uppercase ASCII letters (A-Z) denote string variables.
      - Lowercase letters and digits denote concrete characters.
      - Regex syntax: * (Kleene star), + (one-or-more), | (union),
        & (intersection), ~ (complement), ( ) (grouping).

--*/
#include "util/util.h"
#include "ast/reg_decl_plugins.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "ast/seq_decl_plugin.h"
#include "ast/ast_pp.h"
#include <iostream>
#include <cassert>
#include <functional>
#include <chrono>

// Trivial solver that always returns sat and ignores all assertions.
class nseq_zipt_dummy_solver : public seq::simple_solver {
public:
    void push() override {}
    void pop(unsigned) override {}
    void assert_expr(expr*) override {}
    lbool check() override { return l_true; }
};

// -----------------------------------------------------------------------
// Trivial simple_solver stub: optimistically assumes integer constraints
// are always feasible (returns l_true without actually checking).
// -----------------------------------------------------------------------
class zipt_dummy_simple_solver : public seq::simple_solver {
public:
    void push() override {}
    void pop(unsigned) override {}
    void assert_expr(expr*) override {}
    lbool check() override { return l_true; }
};

// -----------------------------------------------------------------------
// Helper: build a string snode from a notation string.
// Uppercase = fresh variable, lowercase/digit = concrete character.
// Variables with the same letter share the same snode (memoised per call).
// -----------------------------------------------------------------------
struct str_builder {
    euf::sgraph& sg;
    euf::snode* vars[26] = {};      // vars['A'-'A'] .. vars['Z'-'A']

    explicit str_builder(euf::sgraph& sg) : sg(sg) {}

    euf::snode* var(char c) {
        int idx = c - 'A';
        if (!vars[idx])
            vars[idx] = sg.mk_var(symbol(std::string(1, c).c_str()));
        return vars[idx];
    }

    euf::snode* parse(const char* s) {
        euf::snode* result = nullptr;
        for (const char* p = s; *p; ++p) {
            euf::snode* tok = (*p >= 'A' && *p <= 'Z')
                ? var(*p)
                : sg.mk_char((unsigned)(unsigned char)*p);
            result = result ? sg.mk_concat(result, tok) : tok;
        }
        return result ? result : sg.mk_empty();
    }
};

// -----------------------------------------------------------------------
// Helper: build a regex snode from a notation string.
// Parses: union (|), intersection (&), concatenation, postfix * and +,
//         prefix complement ~, parentheses, lowercase chars, () for epsilon.
// -----------------------------------------------------------------------
struct regex_builder {
    ast_manager& m;
    seq_util& su;
    euf::sgraph& sg;
    sort* re_sort;

    regex_builder(ast_manager& m, seq_util& su, euf::sgraph& sg)
        : m(m), su(su), sg(sg) {
        re_sort = su.re.mk_re(su.str.mk_string_sort());
    }

    euf::snode* parse(const char* s) {
        int pos = 0;
        expr_ref e = parse_union(s, pos, (int)strlen(s));
        SASSERT(pos == (int)strlen(s));
        return sg.mk(e.get());
    }

private:
    expr_ref mk_char_re(char c) {
        zstring zs(std::string(1, c).c_str());
        return expr_ref(su.re.mk_to_re(su.str.mk_string(zs)), m);
    }

    expr_ref parse_union(const char* s, int& pos, int len) {
        expr_ref left = parse_inter(s, pos, len);
        while (pos < len && s[pos] == '|') {
            ++pos;
            expr_ref right = parse_inter(s, pos, len);
            left = expr_ref(su.re.mk_union(left.get(), right.get()), m);
        }
        return left;
    }

    expr_ref parse_inter(const char* s, int& pos, int len) {
        expr_ref left = parse_concat(s, pos, len);
        while (pos < len && s[pos] == '&') {
            ++pos;
            expr_ref right = parse_concat(s, pos, len);
            left = expr_ref(su.re.mk_inter(left.get(), right.get()), m);
        }
        return left;
    }

    expr_ref parse_concat(const char* s, int& pos, int len) {
        expr_ref acc(m);
        while (pos < len && s[pos] != ')' && s[pos] != '|' && s[pos] != '&') {
            expr_ref tok = parse_repeat(s, pos, len);
            acc = acc ? expr_ref(su.re.mk_concat(acc.get(), tok.get()), m) : tok;
        }
        return acc ? acc : expr_ref(su.re.mk_to_re(su.str.mk_string(zstring(""))), m);
    }

    expr_ref parse_repeat(const char* s, int& pos, int len) {
        // collect leading tildes (complement)
        int tildes = 0;
        while (pos < len && s[pos] == '~') { ++tildes; ++pos; }
        expr_ref base = parse_primary(s, pos, len);
        // postfix * and +
        while (pos < len && (s[pos] == '*' || s[pos] == '+')) {
            if (s[pos] == '*')
                base = expr_ref(su.re.mk_star(base.get()), m);
            else
                base = expr_ref(su.re.mk_plus(base.get()), m);
            ++pos;
        }
        // apply complements
        for (int i = 0; i < tildes; ++i)
            base = expr_ref(su.re.mk_complement(base.get()), m);
        return base;
    }

    expr_ref parse_primary(const char* s, int& pos, int len) {
        if (pos >= len)
            return expr_ref(su.re.mk_to_re(su.str.mk_string(zstring(""))), m);
        char c = s[pos];
        if (c == '(') {
            ++pos;
            expr_ref inner = parse_union(s, pos, len);
            SASSERT(pos < len && s[pos] == ')');
            ++pos;
            return inner;
        }
        ++pos;
        return mk_char_re(c);
    }
};

// -----------------------------------------------------------------------
// Test fixture: shared setup
// -----------------------------------------------------------------------
struct nseq_fixture {
    ast_manager m;
    euf::egraph eg;
    euf::sgraph sg;
    zipt_dummy_simple_solver dummy_solver;
    seq::nielsen_graph ng;
    seq_util su;
    str_builder sb;
    regex_builder rb;

    // Registers plugins on m and returns it so eg can be initialized after plugins are ready.
    static ast_manager& init(ast_manager& m) { reg_decl_plugins(m); return m; }

    nseq_fixture()
        : eg(init(m)), sg(m, eg), ng(sg, dummy_solver), su(m), sb(sg), rb(m, su, sg)
    {}

    euf::snode* S(const char* s) { return sb.parse(s); }
    euf::snode* R(const char* s) { return rb.parse(s); }
};

static constexpr int TEST_TIMEOUT_SEC = 2;

static void set_timeout(nseq_fixture& f) {
    auto start = std::chrono::steady_clock::now();
    f.ng.set_cancel_fn([start]() {
        auto elapsed = std::chrono::steady_clock::now() - start;
        return std::chrono::duration_cast<std::chrono::seconds>(elapsed).count() >= TEST_TIMEOUT_SEC;
    });
}

static bool eq_sat(const char* lhs, const char* rhs) {
    std::cout << "Checking equation: " << lhs << " = " << rhs << std::endl;
    nseq_fixture f;
    set_timeout(f);
    f.ng.add_str_eq(f.S(lhs), f.S(rhs));
    return f.ng.solve() == seq::nielsen_graph::search_result::sat;
}
static bool eq_unsat(const char* lhs, const char* rhs) {
    std::cout << "Checking equation: " << lhs << " = " << rhs << std::endl;
    nseq_fixture f;
    set_timeout(f);
    f.ng.add_str_eq(f.S(lhs), f.S(rhs));
    return f.ng.solve() == seq::nielsen_graph::search_result::unsat;
}
static bool mem_sat(std::initializer_list<std::pair<const char*, const char*>> mems) {
    nseq_fixture f;
    set_timeout(f);
    for (auto& [str, re] : mems)
        f.ng.add_str_mem(f.S(str), f.R(re));
    return f.ng.solve() == seq::nielsen_graph::search_result::sat;
}
static bool mem_unsat(std::initializer_list<std::pair<const char*, const char*>> mems) {
    nseq_fixture f;
    set_timeout(f);
    for (auto& [str, re] : mems)
        f.ng.add_str_mem(f.S(str), f.R(re));
    return f.ng.solve() == seq::nielsen_graph::search_result::unsat;
}

// -----------------------------------------------------------------------
// String equation tests  (ZIPT: CheckStrEquations)
// -----------------------------------------------------------------------
static void test_zipt_str_equations() {
    std::cout << "test_zipt_str_equations:" << std::endl;

    VERIFY(eq_sat  ("abab", "XX"));       // abab = XX  (X="ab")
    VERIFY(eq_sat  ("aX",   "YX"));       // aX = YX    (Y="a")
    VERIFY(eq_sat  ("aX",   "Xa"));       // aX = Xa
    VERIFY(eq_unsat("aX",   "Xb"));       // aX = Xb  — UNSAT
    VERIFY(eq_sat  ("abX",  "Xba"));      // abX = Xba
    VERIFY(eq_sat  ("XabY", "YbaX"));     // XabY = YbaX
    VERIFY(eq_unsat("abcX", "Xbac"));     // abcX = Xbac — UNSAT
    VERIFY(eq_unsat("aaX",  "Xa"));       // aaX = Xa   — UNSAT
    VERIFY(eq_unsat("aa",   "XXX"));      // aa = XXX   — UNSAT
    VERIFY(eq_sat  ("aX",   "XY"));       // aX = XY

    std::cout << "  ok\n";
}

// -----------------------------------------------------------------------
// Ground regex matching tests  (ZIPT: CheckRegexMatching)
// No string variables — all concrete inputs.
// -----------------------------------------------------------------------
static void test_zipt_regex_ground() {
    std::cout << "test_zipt_regex_ground\n";

    VERIFY(mem_sat  ({{"", ""}}));                          // "" ∈ ε
    VERIFY(mem_unsat({{"a", ""}}));                         // "a" ∉ ε

    VERIFY(mem_sat  ({{"", "a*"}}));                        // "" ∈ a*
    VERIFY(mem_sat  ({{"aaaa", "a*"}}));                    // "aaaa" ∈ a*
    VERIFY(mem_unsat({{"b", "a*"}}));                       // "b" ∉ a*
    VERIFY(mem_sat  ({{"abbb", "ab*"}}));                   // "abbb" ∈ ab*

    VERIFY(mem_sat  ({{"ab", "(ab)+"}}));                   // "ab" ∈ (ab)+
    VERIFY(mem_sat  ({{"ababab", "(ab)+"}}));               // "ababab" ∈ (ab)+
    VERIFY(mem_unsat({{"", "(ab)+"}}));                     // "" ∉ (ab)+

    VERIFY(mem_sat  ({{"", "()"}}));                        // "" ∈ ()
    VERIFY(mem_sat  ({{"", "()*"}}));                       // "" ∈ ()*
    VERIFY(mem_unsat({{"a", "()*"}}));                      // "a" ∉ ()*

    VERIFY(mem_unsat({{"a", "~a"}}));                       // "a" ∉ ~a
    VERIFY(mem_sat  ({{"b", "~a"}}));                       // "b" ∈ ~a
    VERIFY(mem_sat  ({{"a", "~(~a)"}}));                    // "a" ∈ ~~a

    VERIFY(mem_unsat({{"a", "a&(~a)"}}));                   // "a" ∉ a & ~a
    VERIFY(mem_unsat({{"a", "(a|b)&(~a)"}}));               // "a" ∉ (a|b) & ~a
    VERIFY(mem_sat  ({{"b", "(a|b)&(~a)"}}));               // "b" ∈ (a|b) & ~a

    VERIFY(mem_sat  ({{"ab", "ab"}}));
    VERIFY(mem_sat  ({{"a", "a|b"}}));
    VERIFY(mem_sat  ({{"b", "a|b"}}));
    VERIFY(mem_unsat({{"ab", "a|b"}}));

    VERIFY(mem_sat  ({{"b", "(a|b)|(c|d)"}}));
    VERIFY(mem_sat  ({{"c", "(a|b)|(c|d)"}}));
    VERIFY(mem_unsat({{"e", "(a|b)|(c|d)"}}));
    VERIFY(mem_sat  ({{"b", "(a|b)&(~a|b)"}}));
    VERIFY(mem_unsat({{"a", "(a|b)&(~a|b)"}}));

    VERIFY(mem_sat  ({{"abababab", "(ab)*"}}));
    VERIFY(mem_sat  ({{"abab", "(ab)*"}}));
    VERIFY(mem_unsat({{"aba", "(ab)*"}}));

    VERIFY(mem_sat  ({{"c", "(a|b|c)&(c|d)"}}));
    VERIFY(mem_unsat({{"b", "(a|b|c)&(c|d)"}}));

    VERIFY(mem_sat  ({{"abab", "((ab)|(ba))+"}}));
    VERIFY(mem_unsat({{"a", "((ab)|(ba))+"}}));

    VERIFY(mem_sat  ({{"c", "(~a)&(c|b)"}}));

    VERIFY(mem_unsat({{"a", "~(a|b)"}}));
    VERIFY(mem_sat  ({{"c", "~(a|b)"}}));

    std::cout << "  ok\n";
}

// -----------------------------------------------------------------------
// String membership tests  (ZIPT: CheckStrMembership)
// String variables (uppercase) combined with regex constraints.
// -----------------------------------------------------------------------
static void test_zipt_str_membership() {
    std::cout << "test_zipt_str_membership\n";

    // X ∈ (~(ab))*cab
    VERIFY(mem_sat({{"X", "(~(ab))*cab"}}));

    // X ∈ a* && X ∈ a* && X ∈ b+  → UNSAT
    VERIFY(mem_unsat({{"X","a*"}, {"X","a*"}, {"X","b+"}}));

    // X ∈ a*b* && Y ∈ a*b*  → SAT (independent)
    VERIFY(mem_sat({{"X","a*b*"}, {"Y","a*b*"}}));

    // X ∈ a* && Y ∈ (ab)+  → SAT (independent)
    VERIFY(mem_sat({{"X","a*"}, {"Y","(ab)+"}}));

    // X ∈ (ab)+ && X ∈ a*  → UNSAT
    VERIFY(mem_unsat({{"X","(ab)+"}, {"X","a*"}}));

    // XaX ∈ (aa)*  → UNSAT
    VERIFY(mem_unsat({{"XaX", "(aa)*"}}));

    // aX ∈ aa*
    VERIFY(mem_sat({{"aX", "aa*"}}));

    // X ∈ (aa)*a && X ∈ (aa)*  → UNSAT
    VERIFY(mem_unsat({{"X","(aa)*a"}, {"X","(aa)*"}}));

    // X ∈ (aa)*aa && X ∈ (aa)*  → SAT
    VERIFY(mem_sat({{"X","(aa)*aa"}, {"X","(aa)*"}}));

    // Xa ∈ aa*
    VERIFY(mem_sat({{"Xa", "aa*"}}));

    // Xa ∈ aa*a
    VERIFY(mem_sat({{"Xa", "aa*a"}}));

    // bX ∉ a*a
    VERIFY(mem_unsat({{"bX", "a*a"}}));

    // bX ∉ a*
    VERIFY(mem_unsat({{"bX", "a*"}}));

    // bX ∉ a*a
    VERIFY(mem_unsat({{"bX", "a*a"}}));

    // bX ∈ b*a
    VERIFY(mem_sat({{"bX", "b*a"}}));

    // bXb ∈ b*ab*
    VERIFY(mem_sat({{"bXb", "b*ab*"}}));

    // bXbb ∈ b*ab*
    VERIFY(mem_sat({{"bXbb", "b*ab*"}}));

    // XX ∈ aa*
    VERIFY(mem_sat({{"XX", "aa*"}}));

    // XaX ∈ aaa*
    VERIFY(mem_sat({{"XaX", "aaa*"}}));

    // XX ∈ aaaa*
    VERIFY(mem_sat({{"XX", "aaaa*"}}));

    // XbX ∉ a*
    VERIFY(mem_unsat({{"XbX", "a*"}}));

    // XbX ∈ a*b*
    VERIFY(mem_sat({{"XbX", "a*b*"}}));

    // XbX ∈ a*b*a*a
    VERIFY(mem_sat({{"XbX", "a*b*a*a"}}));

    // XabX ∉ (aba)*
    VERIFY(mem_unsat({{"XabX", "(aba)*"}}));

    // XaX ∉ (ab)*
    VERIFY(mem_unsat({{"XaX", "(ab)*"}}));

    // X ∈ a|b
    VERIFY(mem_sat({{"X", "a|b"}}));

    // XX ∉ a|b
    VERIFY(mem_unsat({{"XX", "a|b"}}));

    // XX ∉ (ab)|(ba)
    VERIFY(mem_unsat({{"XX", "(ab)|(ba)"}}));

    // XX ∈ (ab|ba)(ba|ab)
    VERIFY(mem_sat({{"XX", "(ab|ba)(ba|ab)"}}));

    // XX ∉ (ab|ba)(aa|bb)
    VERIFY(mem_unsat({{"XX", "(ab|ba)(aa|bb)"}}));

    // bXbX ∉ a*b*a*a
    VERIFY(mem_unsat({{"bXbX", "a*b*a*a"}}));

    // XdX ∈ (a|b)*da(a|c)*
    VERIFY(mem_sat({{"XdX", "(a|b)*da(a|c)*"}}));

    // XbX ∉ (ab)*
    VERIFY(mem_unsat({{"XbX", "(ab)*"}}));

    // XabX ∉ (ab)* && XbabX ∉ a(ba)*
    VERIFY(mem_unsat({{"XabX","(ab)*"}, {"XbabX","a(ba)*"}}));

    // XX ∉ (aba)*a
    VERIFY(mem_unsat({{"XX", "(aba)*a"}}));

    // XX ∈ (((ab)|(ba)))+aa
    VERIFY(mem_sat({{"XX", "((ab)|(ba))+aa"}}));

    // XX ∉ (ab)*a
    VERIFY(mem_unsat({{"XX", "(ab)*a"}}));

    // XX ∉ (a(a|b))*a
    VERIFY(mem_unsat({{"XX", "(a(a|b))*a"}}));

    // XX ∉ (a(a|(aaa)))*a
    VERIFY(mem_unsat({{"XX", "(a(a|(aaa)))*a"}}));

    // XX ∈ (((ab)|(ba)))+aa  (duplicate from ZIPT)
    VERIFY(mem_sat({{"XX", "((ab)|(ba))+aa"}}));

    // XX ∉ (((ab)|(ba)))+aaaa
    VERIFY(mem_unsat({{"XX", "((ab)|(ba))+aaaa"}}));

    // XX ∈ (((ab)|(ba)))*aaaa
    VERIFY(mem_sat({{"XX", "((ab)|(ba))*aaaa"}}));

    // X ∈ a+ && X ∈ b+  → UNSAT
    VERIFY(mem_unsat({{"X","a+"}, {"X","b+"}}));

    // X ∈ (a|b) && XX ∈ (a|b)  → UNSAT
    VERIFY(mem_unsat({{"X","a|b"}, {"XX","a|b"}}));

    // X ∈ (ab)+ && XX ∈ a*  → UNSAT
    VERIFY(mem_unsat({{"X","(ab)+"}, {"XX","a*"}}));

    // X ∈ a* && Y ∈ b* && XY ∈ (ab)+  → SAT
    VERIFY(mem_sat({{"X","a*"}, {"Y","b*"}, {"XY","(ab)+"}}));

    // X ∈ a* && X ∈ ~(a*)  → UNSAT
    VERIFY(mem_unsat({{"X","a*"}, {"X","~(a*)"}}));

    // X ∈ (ab)* && X ∈ (ab)+  → SAT
    VERIFY(mem_sat({{"X","(ab)*"}, {"X","(ab)+"}}));

    // X ∈ ~(a|b) && X ∈ (c|d)  → SAT
    VERIFY(mem_sat({{"X","~(a|b)"}, {"X","c|d"}}));

    // X ∈ (a|b)* && XX ∈ (ab)+  → SAT
    VERIFY(mem_sat({{"X","(a|b)*"}, {"XX","(ab)+"}}));

    // X ∈ a+ && Y ∈ b* && XYYX ∈ (ab)*(ba)*  → SAT
    VERIFY(mem_sat({{"X","a+"}, {"Y","b*"}, {"XYYX","(ab)*(ba)*"}}));

    // X ∈ (ab)+ && XXX ∈ (ab)+  → SAT
    VERIFY(mem_sat({{"X","(ab)+"}, {"XXX","(ab)+"}}));

    // X ∈ (a|b) && X ∈ ~(a|b)  → UNSAT
    VERIFY(mem_unsat({{"X","a|b"}, {"X","~(a|b)"}}));

    // X ∈ a+ && Y ∈ b+ && XY ∈ (ab)+  → SAT
    VERIFY(mem_sat({{"X","a+"}, {"Y","b+"}, {"XY","(ab)+"}}));

    // XbX ∈ a*b*  (note: same snode X shared)
    VERIFY(mem_sat({{"XbX", "a*b*"}}));

    // X ∈ a+ && XbX ∈ b*  → UNSAT
    VERIFY(mem_unsat({{"X","a+"}, {"XbX","b*"}}));

    // aXb ∈ a(a|b)*b
    VERIFY(mem_sat({{"aXb", "a(a|b)*b"}}));

    // X ∈ a+ && Y ∈ b+ && XYX ∈ (ab)*(ba)*  → SAT
    VERIFY(mem_sat({{"X","a+"}, {"Y","b+"}, {"XYX","(ab)*(ba)*"}}));

    // XX ∈ (ab|ba)+ && X ∈ (a|b)+  → SAT
    VERIFY(mem_sat({{"XX","(ab|ba)+"}, {"X","(a|b)+"}}));

    // X ∈ a* && X ∈ a+  → SAT
    VERIFY(mem_sat({{"X","a*"}, {"X","a+"}}));

    // X ∈ "" && XbX ∈ a*baa*  → UNSAT
    VERIFY(mem_unsat({{"X",""}, {"XbX","a*baa*"}}));

    // XXXX ∈ aaaaa*
    VERIFY(mem_sat({{"XXXX", "aaaaa*"}}));

    // XXXX ∉ aaa(aa)*
    VERIFY(mem_unsat({{"XXXX", "aaa(aa)*"}}));

    // XXXX ∉ ab
    VERIFY(mem_unsat({{"XXXX", "ab"}}));

    // XXXX ∉ abab
    VERIFY(mem_unsat({{"XXXX", "abab"}}));

    // XXXX ∈ a(ba)*b
    VERIFY(mem_sat({{"XXXX", "a(ba)*b"}}));

    // XXXX ∉ a(ab)*b
    VERIFY(mem_unsat({{"XXXX", "a(ab)*b"}}));

    // XYYX ∉ ab
    VERIFY(mem_unsat({{"XYYX", "ab"}}));

    // XYYX ∉ a(ab)*b
    VERIFY(mem_unsat({{"XYYX", "a(ab)*b"}}));

    // XYYX ∉ a+b+
    VERIFY(mem_unsat({{"XYYX", "a+b+"}}));

    // XaX ∈ a(a|b)*a
    VERIFY(mem_sat({{"XaX", "a(a|b)*a"}}));

    // XbY ∈ a+b* && X ∈ a* && Y ∈ b+
    VERIFY(mem_sat({{"XbY","a+b*"}, {"X","a*"}, {"Y","b+"}}));

    // X ∈ a+ && Y ∈ b+ && XbY ∉ (ab)+
    VERIFY(mem_unsat({{"X","a+"}, {"Y","b+"}, {"XbY","(ab)+"}}));

    // X ∈ ((()|a)b)* && Y ∈ (a(()|b))* && XbY ∉ (ab)*
    VERIFY(mem_unsat({{"X","((()|a)b)*"}, {"Y","(a(()|b))*"}, {"XbY","(ab)*"}}));

    // X ∈ (a(()|b))* && Y ∈ (ab)* && XbY ∈ (ab)*
    VERIFY(mem_sat({{"X","(a(()|b))*"}, {"Y","(ab)*"}, {"XbY","(ab)*"}}));

    // X ∈ (ab)* && Y ∈ ((()|a)b)* && XbY ∉ (ab)*
    VERIFY(mem_unsat({{"X","(ab)*"}, {"Y","((()|a)b)*"}, {"XbY","(ab)*"}}));

    // X ∈ (ab)* && Y ∈ (ab)* && XbY ∉ (ab)*
    VERIFY(mem_unsat({{"X","(ab)*"}, {"Y","(ab)*"}, {"XbY","(ab)*"}}));

    // X ∈ a+ && Y ∈ b+ && Z ∈ c+ && XYZ ∈ (abc)+  → SAT
    VERIFY(mem_sat({{"X","a+"}, {"Y","b+"}, {"Z","c+"}, {"XYZ","(abc)+"}}));

    // XaYbZ ∈ a*b*c* && X ∈ a* && Y ∈ b* && Z ∈ c*  → SAT
    VERIFY(mem_sat({{"XaYbZ","a*b*c*"}, {"X","a*"}, {"Y","b*"}, {"Z","c*"}}));

    // aXbYc ∈ a(a|b|c)*c
    VERIFY(mem_sat({{"aXbYc", "a(a|b|c)*c"}}));

    // X ∈ (a|b)* && Y ∈ (b|c)* && Z ∈ (c|a)* && XYZ ∈ (abc)+  → SAT
    VERIFY(mem_sat({{"X","(a|b)*"}, {"Y","(b|c)*"}, {"Z","(c|a)*"}, {"XYZ","(abc)+"}}));

    std::cout << "  ok\n";
}

// -----------------------------------------------------------------------
// Parikh image tests  (ZIPT: CheckParikh)
// These must be UNSAT via Parikh/letter-count arguments alone.
// -----------------------------------------------------------------------
static void test_zipt_parikh() {
    std::cout << "test_zipt_parikh\n";

    VERIFY(eq_unsat("abcX",      "Xbac"));
    VERIFY(eq_unsat("XabcY",     "YbacX"));
    VERIFY(eq_unsat("XXabcYY",   "YYbacXX"));
    VERIFY(eq_unsat("XXacdYYb",  "YYabcdXX"));
    VERIFY(eq_unsat("YaXaaabbbbYX", "XYababababXY"));

    std::cout << "  ok\n";
}

// -----------------------------------------------------------------------
// Tricky string equation benchmarks (hand-crafted, beyond ZIPT suite).
//
// SAT witnesses are noted inline.  UNSAT arguments are grouped by type:
//   [first-char]   — immediate first-character mismatch
//   [after-cancel] — mismatch exposed after prefix/suffix cancellation
//   [induction]    — recursive unrolling forces a = b contradiction
//   [parity]       — length parity (odd vs even) rules out all solutions
//   [midpoint]     — equal length forced by lengths; midpoint char differs
// -----------------------------------------------------------------------
static void test_tricky_str_equations() {
    std::cout << "test_tricky_str_equations\n";

    // --- SAT: commutativity / rotation / symmetry ---

    // XY = YX   (classic commutativity; witness: X="ab", Y="abab")
    VERIFY(eq_sat("XY", "YX"));

    // Xab = abX   (X commutes with the word "ab"; witness: X="ab")
    VERIFY(eq_sat("Xab", "abX"));

    // XaY = YaX   (swap-symmetric; witness: X=Y=any, e.g. X=Y="b")
    VERIFY(eq_sat("XaY", "YaX"));

    // XYX = YXY   (Markov-type; witness: X=Y)
    VERIFY(eq_sat("XYX", "YXY"));

    // XYZ = ZYX   (reverse-palindrome; witness: X="a",Y="b",Z="a")
    VERIFY(eq_sat("XYZ", "ZYX"));

    // XabY = YabX   (rotation-like; witness: X="",Y="ab")
    VERIFY(eq_sat("XabY", "YabX"));

    // aXYa = aYXa   (cancel outer 'a'; reduces to XY=YX; witness: X=Y="")
    VERIFY(eq_sat("aXYa", "aYXa"));

    // XaXb = YaYb   (both halves share variable; witness: X=Y)
    VERIFY(eq_sat("XaXb", "YaYb"));

    // abXba = Xabba   (witness: X="" gives "abba"="abba")
    VERIFY(eq_sat("abXba", "Xabba"));

    // --- UNSAT: first-character mismatch ---

    // abXba = baXab   (LHS starts 'a', RHS starts 'b')
    VERIFY(eq_unsat("abXba", "baXab"));

    // XabX = XbaX   (cancel X prefix/suffix → "ab"="ba"; 'a'≠'b')
    VERIFY(eq_unsat("XabX",  "XbaX"));

    // --- UNSAT: mismatch exposed after cancellation ---

    // XaYb = XbYa   (cancel X prefix → aYb=bYa; first char 'a'≠'b')
    VERIFY(eq_unsat("XaYb",  "XbYa"));

    // XaYbX = XbYaX   (cancel X prefix+suffix → aYb=bYa; first char 'a'≠'b')
    VERIFY(eq_unsat("XaYbX", "XbYaX"));

    // XaXbX = XbXaX   (cancel X prefix+suffix → aXb=bXa; first char 'a'≠'b')
    VERIFY(eq_unsat("XaXbX", "XbXaX"));

    // --- UNSAT: induction ---

    // aXb = Xba   (forces X=a^n; final step requires a=b)
    VERIFY(eq_unsat("aXb",  "Xba"));

    // XaY = YbX   (a≠b; recursive unrolling forces a=b)
    VERIFY(eq_unsat("XaY",  "YbX"));

    // --- UNSAT: length parity ---

    // XaX = YY   (|XaX|=2|X|+1 is odd; |YY|=2|Y| is even)
    VERIFY(eq_unsat("XaX",  "YY"));

    // XaaX = YbY   (|XaaX|=2|X|+2 is even; |YbY|=2|Y|+1 is odd)
    VERIFY(eq_unsat("XaaX", "YbY"));

    // --- UNSAT: midpoint argument ---

    // XaX = YbY   (equal length forces |X|=|Y|; midpoint position |X|
    //              holds 'a' in LHS and 'b' in RHS, but 'a'≠'b')
    VERIFY(eq_unsat("XaX",  "YbY"));

    std::cout << "  ok\n";
}

void tst_nseq_zipt() {
    test_zipt_str_equations();
    test_tricky_str_equations();
    test_zipt_regex_ground();
    test_zipt_str_membership();
    test_zipt_parikh();
    std::cout << "nseq_zipt: all tests passed\n";
}
