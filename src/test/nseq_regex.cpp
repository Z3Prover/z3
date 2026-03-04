/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_regex.cpp

Abstract:

    Unit tests for nseq_regex: lazy regex membership processing
    for the Nielsen-based string solver.

--*/
#include "util/util.h"
#include "ast/reg_decl_plugins.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/nseq_regex.h"
#include <iostream>

// Test 1: nseq_regex instantiation
static void test_nseq_regex_instantiation() {
    std::cout << "test_nseq_regex_instantiation\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    smt::nseq_regex nr(sg);
    SASSERT(&nr.sg() == &sg);
    std::cout << "  ok\n";
}

// Test 2: is_empty_regex on an empty-language node
static void test_nseq_regex_is_empty() {
    std::cout << "test_nseq_regex_is_empty\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    smt::nseq_regex nr(sg);

    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    // re.none is the empty language
    expr_ref none_e(su.re.mk_empty(su.re.mk_re(str_sort)), m);
    euf::snode* none_n = sg.mk(none_e.get());
    SASSERT(nr.is_empty_regex(none_n));
    std::cout << "  ok: re.none recognized as empty\n";
}

// Test 3: is_empty_regex on a full-match regex (not empty)
static void test_nseq_regex_is_full() {
    std::cout << "test_nseq_regex_is_full\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    smt::nseq_regex nr(sg);

    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    // re.all (full sequence regex) is not empty
    expr_ref full_e(su.re.mk_full_seq(su.re.mk_re(str_sort)), m);
    euf::snode* full_n = sg.mk(full_e.get());
    SASSERT(!nr.is_empty_regex(full_n));
    std::cout << "  ok: re.all not recognized as empty\n";
}

void tst_nseq_regex() {
    test_nseq_regex_instantiation();
    test_nseq_regex_is_empty();
    test_nseq_regex_is_full();
    std::cout << "nseq_regex: all tests passed\n";
}
