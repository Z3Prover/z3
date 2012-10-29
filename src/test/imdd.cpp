/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    imdd.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-10-14.

Revision History:

--*/
#include"imdd.h"

#if !defined(_AMD64_) && defined(Z3DEBUG)

static void tst0() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m), d4(m);
    d1 = m.mk_empty(1);
    d2 = m.mk_empty(1);
    m.insert_dupdt(d1, 10, 20);
    m.insert_dupdt(d1, 31, 50);
    m.insert_dupdt(d2, 1,  5);
    m.insert_dupdt(d2, 11,  13);
    m.mk_product(d1, d2, d4);
    m.mk_product(d4, d2, d4);
    m.mk_product_dupdt(d1, d2);
    std::cout << "d1:\n" << mk_ll_pp(d1, m) << "\n-------\n";
    m.mk_product_dupdt(d1, d2);
    std::cout << "d4:\n" << mk_ll_pp(d4, m) << "\nd1:\n" << mk_ll_pp(d1, m) << "\nd2:\n" << mk_ll_pp(d2, m) << "\n";
    std::cout << d1 << "\n" << d2 << "\n";
    m.mk_product_dupdt(d1, d1);
    std::cout << "d1 X d1:\n" << mk_ll_pp(d1, m) << "\n";
}

static void add_triple(imdd_manager & m, imdd_ref & d, unsigned l1, unsigned u1, unsigned l2, unsigned u2, unsigned l3, unsigned u3,
                       bool destructive = false, bool memoize = true) {
    unsigned lowers[3] = {l1, l2, l3};
    unsigned uppers[3] = {u1, u2, u3};
    if (destructive)
        m.add_facts_dupdt(d, 3, lowers, uppers, memoize);
    else
        m.add_facts(d, d, 3, lowers, uppers, memoize);
    // std::cout << mk_ll_pp(d, m) << "\n";
}

static void add_pair(imdd_manager & m, imdd_ref & d, unsigned l1, unsigned u1, unsigned l2, unsigned u2, bool destructive = false, bool memoize = true) {
    unsigned lowers[2] = {l1, l2};
    unsigned uppers[2] = {u1, u2};
    if (destructive)
        m.add_facts_dupdt(d, 2, lowers, uppers, memoize);
    else
        m.add_facts(d, d, 2, lowers, uppers, memoize);
    // std::cout << mk_ll_pp(d, m) << "\n";
}

static void add_some_facts(imdd_manager & m, imdd_ref & d, bool destructive = false, bool memoize = true) {
    std::cout << "destructive: " << destructive << ", memoize: " << memoize << std::endl;
    add_triple(m, d, 1, 10,  3, 3,  0, 100, destructive, memoize);
    std::cout << mk_ll_pp(d, m) << std::endl;
    SASSERT(m.contains(d, 2, 3, 20));
    SASSERT(!m.contains(d, 2, 4, 20));
    SASSERT(!m.contains(d, 2, 3, 200));
    SASSERT(!m.contains(d, 0, 3, 200));
    SASSERT(m.contains(d,1,3,0));
    add_triple(m, d, 3, 6,   3, 4,  7, 101, destructive, memoize);
    std::cout << mk_ll_pp(d, m) << std::endl;
    add_triple(m, d, 3, 6,   2, 2,  7, 101, destructive, memoize);
    std::cout << mk_ll_pp(d, m) << std::endl;
    add_triple(m, d, 3, 6,   5, 6,  7, 101, destructive, memoize);
    SASSERT(m.contains(d, 2, 3, 20));
    std::cout << mk_ll_pp(d, m) << std::endl;
    SASSERT(!m.contains(d, 2, 4, 20));
    SASSERT(m.contains(d, 3, 4, 20));
    SASSERT(!m.contains(d, 2, 3, 200));
    SASSERT(!m.contains(d, 0, 3, 200));
    SASSERT(m.contains(d,1,3,0));
}

static void tst1() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    {
        imdd_ref d(m);
        d = m.mk_empty(3);
        add_some_facts(m, d);
    }
    {
        imdd_ref d(m);
        d = m.mk_empty(3);
        add_some_facts(m, d, true, false);
        m.defrag(d);
        std::cout << mk_ll_pp(d, m) << "\n";
    }
}

static void tst2() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 10, 20, 11, 21, 12, 22);
    add_triple(m, d1, 30, 40, 31, 41, 32, 42);
    d2 = m.mk_empty(3);
    add_triple(m, d2, 15, 22, 15, 23, 7, 18);
    add_triple(m, d2, 28, 42, 29, 39, 34, 46);
    add_triple(m, d2, 28, 42, 29, 39, 100, 200);
    add_triple(m, d2, 28, 42, 50, 60, 100, 200);
    std::cout << mk_ll_pp(d1, m) << "\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
    m.mk_union(d1, d2, d3);
    SASSERT(m.subsumes(d3, d1));
    SASSERT(m.subsumes(d3, d2));
    SASSERT(!m.subsumes(d1, d3));
    SASSERT(!m.subsumes(d2, d3));
    std::cout << "d3: " << d3.get() << "\n" << mk_ll_pp(d3, m) << "\n";
    m.mk_union_dupdt(d1, d2, false);
    std::cout << "d1: " << d1.get() << "\n" << mk_ll_pp(d1, m) << "\n";
    SASSERT(m.is_equal(d1, d3));
    SASSERT(!m.is_equal(d2, d3));
    SASSERT(!m.is_equal(d2, d1));
    std::cout << "memory(d1): " << m.memory(d1) << "\n";
}

static void tst3() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m);
    d1 = m.mk_empty(3);
    unsigned mins[3] = {0,0,0};
    unsigned maxs[3] = {127, 511, 255};
    
    m.mk_complement(d1, d1, 3, mins, maxs);
    std::cout << d1 << "\n";
    m.mk_complement(d1, d1, 3, mins, maxs);
    std::cout << d1 << "\n";
    SASSERT(d1->empty());

    d1 = m.mk_empty(3);
    add_triple(m, d1, 10, 20, 11, 21, 12, 22);
    add_triple(m, d1, 30, 40, 31, 41, 32, 42);
    std::cout << d1 << "\n";
    m.mk_complement(d1, d1, 3, mins, maxs);
    std::cout << mk_ll_pp(d1,m) << "\n";
    m.mk_filter_equal(d1, d1, 1, 15);
    std::cout << "after selecting second column = 15\n" << mk_ll_pp(d1,m) << "\n";
}

static void tst4() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 1, 2, 2, 5, 4, 4);
    add_triple(m, d1, 3, 4, 3, 4, 2, 5);
    std::cout << "testing iterator:\n";
    imdd_manager::iterator it  = m.begin(d1);
    imdd_manager::iterator end = m.end(d1);
    for (; it != end; ++it) {
        unsigned * tuple = *it;
        std::cout << "[";
        for (unsigned i = 0; i < d1->get_arity(); i++) {
            if (i > 0)
                std::cout << ", ";
            std::cout << tuple[i];
        }
        std::cout << "]\n";
    }
}

static void tst5() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    std::cout.flush();
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 100, 10, 20, 3, 10);
    std::cout << mk_ll_pp(d1,m) << std::endl;
    add_triple(m, d1, 5, 100, 34, 50, 98, 110);
    std::cout << mk_ll_pp(d1,m) << std::endl;
    unsigned vals[3] = {6, 8, 3};
    SASSERT(!m.contains(d1, 3, vals));
    add_triple(m, d1, 6, 25, 8, 30, 14, 50);
    std::cout << mk_ll_pp(d1,m) << std::endl;
    SASSERT(!m.contains(d1, 3, vals));
    unsigned vars[2] = {0, 2};
    d2 = d1;
    d3 = d1;
    m.mk_filter_identical(d1, d1, 2, vars);
    vars[1] = 1;
    std::cout << "d1:\n" << mk_ll_pp(d1,m) << "\n";
    m.mk_filter_identical(d2, d2, 2, vars);
    std::cout << "d2:\n" << mk_ll_pp(d2,m) << "\n";
    vars[0] = 1;
    vars[1] = 2;
    m.mk_filter_identical(d3, d3, 2, vars);
    std::cout << "d3:\n" << mk_ll_pp(d3,m) << "\n";
}

static void add_5tuple(imdd_manager & m, imdd_ref & d, unsigned l1, unsigned u1, unsigned l2, unsigned u2, unsigned l3, unsigned u3,
                       unsigned l4, unsigned u4, unsigned l5, unsigned u5, bool destructive = false, bool memoize = true) {
    unsigned lowers[5] = {l1, l2, l3, l4, l5};
    unsigned uppers[5] = {u1, u2, u3, u4, u5};
    if (destructive) 
        m.add_facts_dupdt(d, 5, lowers, uppers, memoize);
    else
        m.add_facts(d, d, 5, lowers, uppers, memoize);
    // std::cout << mk_ll_pp(d, m) << "\n";
}

static void tst6() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m);
    std::cout.flush();
    d1 = m.mk_empty(5);
    // TODO: make a more complicated mk_filter_identical example
}

static void tst7() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d2(m), d3(m);
    d2 = m.mk_empty(3);
    add_triple(m, d2, 15, 22, 15, 23, 7, 18);
    add_triple(m, d2, 28, 42, 29, 39, 34, 46);
    add_triple(m, d2, 28, 42, 29, 39, 100, 200);
    add_triple(m, d2, 28, 42, 50, 60, 100, 200);
    std::cout << "mk_project\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
    unsigned vars[1] = {1};
    m.mk_project(d2, d3, 1, vars);
    std::cout << mk_ll_pp(d3, m) << "\n";
}

static void tst8() {
    std::cout << "--------------------------------\n";    
    // enable_trace("mk_swap_bug");
    imdd_manager m;
    imdd_ref d2(m), d3(m);
    d2 = m.mk_empty(3);
    add_triple(m, d2, 15, 22, 15, 23, 7, 18);
    add_triple(m, d2, 28, 42, 29, 39, 34, 46);
    add_triple(m, d2, 28, 42, 29, 39, 100, 200);
    add_triple(m, d2, 28, 42, 50, 60, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    m.mk_swap(d2, d3, 0);
    std::cout << "after swap 0<->1\n";    
    std::cout << mk_ll_pp(d3, m) << "\n";
    m.mk_swap(d2, d3, 1);
    std::cout << "after swap 1<->2\n";    
    std::cout << mk_ll_pp(d3, m) << "\n";
}

static void tst9() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d2(m), d3(m);
    d2 = m.mk_empty(5);
    add_5tuple(m, d2, 2,2, 3,3, 1, 1,  5, 10, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    add_5tuple(m, d2, 2,2, 3,3, 1, 1, 15, 20, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    add_5tuple(m, d2, 4,4, 5,5, 1, 1,  5, 10, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    add_5tuple(m, d2, 4,4, 5,5, 1, 1, 15, 20, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    m.mk_swap(d2, d3, 2);
    std::cout << "after swap 2<->3\n";    
    std::cout << mk_ll_pp(d3, m) << "\n";
}

static void tst10() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 100, 10, 20, 3, 10);
    add_triple(m, d1, 5, 100, 34, 50, 98, 110);
    m.add_bounded_var(d1, d2, 0, 66, 72);
    std::cout << mk_ll_pp(d1, m) << "\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
    m.add_bounded_var(d1, d3, 1, 64, 73);
    std::cout << mk_ll_pp(d3, m) << "\n";
}

static void tst11() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 100, 10, 20, 3, 10);
    add_triple(m, d1, 5, 100, 34, 50, 98, 110);
    add_triple(m, d1, 20, 30, 5, 25, 11, 13);
    m.mk_filter_distinct(d1, d2, 1, 2);
    std::cout << mk_ll_pp(d1, m) << "\n";
    std::cout << "filter_distinct(1,2):\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst12() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 1, 10, 5, 25, 10, 13);
    m.mk_filter_distinct(d1, d2, 1, 2);
    std::cout << mk_ll_pp(d1, m) << "\n";
    std::cout << "filter_distinct(1,2):\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst13() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 25, 1, 10, 10, 13);
    add_triple(m, d1, 5, 25, 20, 30, 10, 13);
    m.mk_filter_distinct(d1, d2, 0, 2);
    std::cout << mk_ll_pp(d1, m) << "\n";
    std::cout << "filter_distinct(0,2):\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst14() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 25, 1, 10, 10, 13);
    add_triple(m, d1, 5, 25, 20, 30, 15, 18);
    std::cout << "destructive version\n";
    std::cout << mk_ll_pp(d1, m) << "\n";
    m.mk_filter_distinct_dupdt(d1, 0, 2);
    std::cout << "filter_distinct(0,2):\n";
    std::cout << mk_ll_pp(d1, m) << "\n";
}

static void tst15() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 5, 1, 10, 5, 5);
    std::cout << mk_ll_pp(d1, m) << "\n";
    m.mk_filter_distinct(d1, d2, 0, 2);
    std::cout << "filter_distinct(0,2):\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst16() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 15, 1, 10, 50, 500);
    std::cout << mk_ll_pp(d1, m) << "\n";
    m.mk_filter_disequal(d1, d2, 1, 4);
    std::cout << "filter_disequal(var1,4):\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst17() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(3);
    add_triple(m, d1, 5, 15, 10, 10, 50, 500);
    std::cout << mk_ll_pp(d1, m) << "\n";
    m.mk_filter_disequal(d1, d2, 1, 10);
    std::cout << "filter_disequal(var1,10):\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst18() {
    std::cout << "--------------------------------\n";    
    imdd_manager m;
    imdd_ref d1(m), d2(m), d3(m);
    d1 = m.mk_empty(2);
    add_pair(m, d1, 1112, 1290, 1302, 1302);
    std::cout << mk_ll_pp(d1, m) << "\n";
    m.mk_swap(d1, d2, 0);
    std::cout << "mk_swap 0:\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void tst19() {
    std::cout << "--------------------------------\n";
    imdd_manager m;
    imdd_ref d2(m), d3(m);
    d2 = m.mk_empty(3);
    add_triple(m, d2, 15, 22, 15, 23, 7, 18);
    add_triple(m, d2, 28, 42, 29, 39, 34, 46);
    add_triple(m, d2, 28, 42, 29, 39, 100, 200);
    add_triple(m, d2, 28, 42, 50, 60, 100, 200);
    std::cout << "mk_project_dupdt\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
    unsigned vars[1] = {1};
    m.mk_project_dupdt(d2, 1, vars);
    std::cout << "new table\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
}

static void init(unsigned* v, unsigned a, unsigned b, unsigned c) {
    v[0] = a;
    v[1] = b;
    v[2] = c;
}

static void tst20() {
    std::cout << "--------------------------------\n";
    std::cout << "remove_facts\n";
    imdd_manager m;
    imdd_ref d2(m), d3(m);
    d2 = m.mk_empty(3);
    add_triple(m, d2, 15, 22, 15, 23, 7, 18);
    add_triple(m, d2, 28, 42, 29, 39, 34, 46);
    add_triple(m, d2, 28, 42, 29, 39, 100, 200);
    add_triple(m, d2, 28, 42, 50, 60, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    //
    // [15, 22] -> #1:{
    //     [15, 23] -> {[7, 18]}*$80}*$80
    // [28, 42] -> #2:{
    //     [29, 39] -> {[34, 46], [100, 200]}*$160
    //     [50, 60] -> {[100, 200]}*$80}*$80}$80
    //
    unsigned lowers[3] = {23,1,1};
    unsigned uppers[3] = {24,1,1};

    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (no change)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    lowers[0] = 22;
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (no change)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    init(lowers, 22, 15, 0);
    init(uppers, 24, 23, 0);
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (no change)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    init(lowers, 22, 15, 7);
    init(uppers, 24, 23, 18);
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (narrow first interval)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    init(lowers, 22, 15, 8);
    init(uppers, 24, 23, 18);
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (split first interval)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    init(lowers, 22, 15, 8);
    init(uppers, 24, 23, 17);
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (split first interval)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    init(lowers, 22, 15, 8);
    init(uppers, 24, 23, 19);
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (split first interval)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";

    init(lowers, 30, 20, 120);
    init(uppers, 40, 60, 140);
    m.remove_facts(d2, d3, 3, lowers, uppers);
    std::cout << "new table (split second interval)\n";
    std::cout << mk_ll_pp(d3, m) << "\n";       
}


static void tst21() {
    std::cout << "--------------------------------\n";
    std::cout << "remove_facts\n";
    imdd_manager m;
    imdd_ref d2(m), d3(m);
    d2 = m.mk_empty(3);
    add_triple(m, d2, 15, 22, 15, 23, 7, 18);
    add_triple(m, d2, 28, 42, 29, 39, 34, 46);
    add_triple(m, d2, 28, 42, 29, 39, 100, 200);
    add_triple(m, d2, 28, 42, 50, 60, 100, 200);
    std::cout << mk_ll_pp(d2, m) << "\n";
    //
    // [15, 22] -> #1:{
    //     [15, 23] -> {[7, 18]}*$80}*$80
    // [28, 42] -> #2:{
    //     [29, 39] -> {[34, 46], [100, 200]}*$160
    //     [50, 60] -> {[100, 200]}*$80}*$80}$80
    //
    unsigned lowers[3] = {23,1,1};
    unsigned uppers[3] = {24,1,1};

    d3 = d2;
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (no change)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";
    d2 = d3;

    lowers[0] = 22;
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (no change)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";

    init(lowers, 22, 15, 0);
    init(uppers, 24, 23, 0);
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (no change)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";

    init(lowers, 22, 15, 7);
    init(uppers, 24, 23, 18);
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (narrow first interval)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";

    init(lowers, 22, 15, 8);
    init(uppers, 24, 23, 18);
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (split first interval)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";

    init(lowers, 22, 15, 8);
    init(uppers, 24, 23, 17);
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (split first interval)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";

    init(lowers, 22, 15, 8);
    init(uppers, 24, 23, 19);
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (split first interval)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";

    init(lowers, 30, 20, 120);
    init(uppers, 40, 60, 140);
    m.remove_facts_dupdt(d2, 3, lowers, uppers);
    std::cout << "new table (split second interval)\n";
    std::cout << mk_ll_pp(d2, m) << "\n";       
}

static void tst22() {
    std::cout << "--------------------------------\n";
    std::cout << "swap\n";
    imdd_manager m;
    imdd_ref d2(m), d3(m), d4(m);

    d2 = m.mk_empty(3);
    random_gen rand;
    for (unsigned i = 0; i < 130; ++i) {
        unsigned a = rand(20);
        unsigned b = rand(20);
        unsigned c = rand(20);
        add_triple(m, d2, a, a, b, b, c, c);
    }
    std::cout << mk_ll_pp(d2, m) << "\n";

    m.mk_swap(d2, d3, 0, true);
    std::cout << mk_ll_pp(d3, m) << "\n";

    m.mk_swap(d3, d4, 0, true);
    std::cout << mk_ll_pp(d4, m) << "\n";
    SASSERT(m.is_subset(d2, d4));
    SASSERT(m.is_subset(d4, d2));
}

void tst_imdd() {
    // enable_trace("imdd_add_bug");
    // enable_trace("add_facts_bug");
    enable_trace("mk_distinct_imdd");
    enable_trace("mk_union_core");
    tst22();
    tst0();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst19();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    tst14();
    tst15();
    tst16();
    tst17();
    tst18();
    tst20();
    tst21();

}

#else

void tst_imdd() {
}

#endif
