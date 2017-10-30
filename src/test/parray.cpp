/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    parray.cpp

Abstract:

    Test persistent arrays.

Author:

    Leonardo de Moura (leonardo) 2011-02-23.

Revision History:

--*/
#include "util/parray.h"
#include "util/small_object_allocator.h"
#include "ast/ast.h"

template<bool PRESERVE_ROOTS>
struct int_parray_config {
    typedef int                      value;
    typedef dummy_value_manager<int> value_manager;
    typedef small_object_allocator   allocator;
    static const bool ref_count        = false;
    static const bool preserve_roots   = PRESERVE_ROOTS;
    static const unsigned max_trail_sz = 8;
    static const unsigned factor       = 2;
};


template<bool PRESERVE_ROOTS>
static void tst1() {
    typedef parray_manager<int_parray_config<PRESERVE_ROOTS> > int_parray_manager;
    typedef typename int_parray_manager::ref int_array;
    
    dummy_value_manager<int> vm;
    small_object_allocator   a;
    int_parray_manager m(vm, a);
    
    int_array a1;
    int_array a2;
    int_array a3;

    m.mk(a1);
    ENSURE(m.size(a1) == 0);
    m.push_back(a1, 10, a2);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";);
    ENSURE(m.size(a1) == 0);
    ENSURE(m.size(a2) == 1);
    m.push_back(a1, 20, a1);
    m.push_back(a1, 30, a1);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";);
    ENSURE(m.get(a1, 0) == 20);
    ENSURE(m.get(a1, 1) == 30);
    ENSURE(m.get(a2, 0) == 10);
    ENSURE(m.size(a1) == 2);
    ENSURE(m.size(a2) == 1);
    ENSURE(m.size(a3) == 0);
    m.push_back(a2, 100, a3);
    ENSURE(m.size(a3) == 2);
    ENSURE(m.get(a3, 0) == 10);
    ENSURE(m.get(a3, 1) == 100);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";);
    m.push_back(a2, 50);
    ENSURE(m.get(a2, 0) == 10);
    ENSURE(m.get(a2, 1) == 50);
    ENSURE(m.size(a2) == 2);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";);
    m.del(a1);
    m.del(a2);
    m.del(a3);
}

template<bool PRESERVE_ROOTS>
static void tst2() {
    typedef parray_manager<int_parray_config<PRESERVE_ROOTS> > int_parray_manager;
    typedef typename int_parray_manager::ref int_array;
    
    TRACE("parray", tout << "tst2\n";);
    dummy_value_manager<int> vm;
    small_object_allocator   a;
    int_parray_manager m(vm, a);

    int_array a1;
    int_array a2;
 
    for (unsigned i = 0; i < 100; i++) 
        m.push_back(a1, i);
    ENSURE(m.size(a1) == 100);
    m.push_back(a1, 100, a2);
    for (unsigned i = 0; i < 10; i++) 
        m.push_back(a2, i+101);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";);
    ENSURE(m.get(a1, 0) == 0);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";);
    for (unsigned i = 0; i < m.size(a1); i++) {
        ENSURE(static_cast<unsigned>(m.get(a1, i)) == i);
    }
    for (unsigned i = 0; i < m.size(a2); i++) {
        ENSURE(static_cast<unsigned>(m.get(a2, i)) == i);
    }
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";);
    m.unshare(a1);
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";);
    m.del(a1);
    m.del(a2);
}    

template<bool PRESERVE_ROOTS>
static void tst3() {
    typedef parray_manager<int_parray_config<PRESERVE_ROOTS> > int_parray_manager;
    typedef typename int_parray_manager::ref int_array;

    TRACE("parray", tout << "tst3\n";);
    dummy_value_manager<int> vm;
    small_object_allocator   a;
    int_parray_manager m(vm, a);

    int_array a1;
    int_array a2;
    int_array a3;
    int_array a4;
 
    for (unsigned i = 0; i < 20; i++) 
        m.push_back(a1, i);
    ENSURE(m.size(a1) == 20);
    m.set(a1, 0, 1, a2);
    for (unsigned i = 1; i < 20; i++) {
        if (i == 6) {
            m.copy(a2, a3);
            m.pop_back(a3);
            m.pop_back(a3);
            m.push_back(a3, 40);
        }
        m.set(a2, i, i+1);
    }
    m.pop_back(a2, a4);
    m.pop_back(a4);
    m.push_back(a4, 30);
    
    for (unsigned i = 0; i < 20; i++) {
        ENSURE(static_cast<unsigned>(m.get(a2, i)) == i+1);
    }
    TRACE("parray", 
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";
          m.display_info(tout, a4); tout << "\n";
          );
    ENSURE(m.get(a1, 10) == 10);
    TRACE("parray", 
          tout << "after rerooting...\n";
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";
          m.display_info(tout, a4); tout << "\n";
          );
    ENSURE(m.size(a1) == 20);
    ENSURE(m.size(a2) == 20);
    ENSURE(m.size(a3) == 19);
    ENSURE(m.size(a4) == 19);
    for (unsigned i = 0; i < 20; i++) {
        ENSURE(static_cast<unsigned>(m.get(a1, i)) == i);
        ENSURE(static_cast<unsigned>(m.get(a2, i)) == i+1);
        ENSURE(i >= 18 || static_cast<unsigned>(m.get(a4, i)) == i+1);
        ENSURE(i >= 6 ||  static_cast<unsigned>(m.get(a3, i)) == i+1);
        ENSURE(!(6 <= i && i <= 17) || static_cast<unsigned>(m.get(a3, i)) == i);
    }
    ENSURE(m.get(a4, 18) == 30);
    ENSURE(m.get(a3, 18) == 40);
    TRACE("parray", 
          tout << "after many gets...\n";
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";
          m.display_info(tout, a4); tout << "\n";
          );
    m.unshare(a1);
    TRACE("parray", 
          tout << "after unshare...\n";
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";
          m.display_info(tout, a4); tout << "\n";
          );
    m.reroot(a4);
    TRACE("parray", 
          tout << "after reroot...\n";
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";
          m.display_info(tout, a4); tout << "\n";
          );
    m.unshare(a2);
    TRACE("parray", 
          tout << "after second unshare...\n";
          m.display_info(tout, a1); tout << "\n";
          m.display_info(tout, a2); tout << "\n";
          m.display_info(tout, a3); tout << "\n";
          m.display_info(tout, a4); tout << "\n";
          );
    m.del(a1);
    m.del(a2);
    m.del(a3);
    m.del(a4);
}

#if 0
// Moved to ast.cpp
struct expr_array_config {
    typedef expr *                   value;
    typedef ast_manager              value_manager;
    typedef small_object_allocator   allocator;
    static const bool ref_count        = true;
    static const bool preserve_roots   = true;
    static const unsigned max_trail_sz = 8;
    static const unsigned factor       = 2;
};

typedef parray_manager<expr_array_config> expr_array_manager;
typedef expr_array_manager::ref expr_array;

static void tst4() {
    TRACE("parray", tout << "tst4\n";);
    ast_manager m;
    expr_array_manager m2(m, m.get_allocator());
    
    expr_array a1;
    expr_array a2;

    expr * v0 = m.mk_var(0, m.mk_bool_sort());
    expr * v1 = m.mk_var(1, m.mk_bool_sort());
    expr * v2 = m.mk_var(2, m.mk_bool_sort());
    expr * v3 = m.mk_var(3, m.mk_bool_sort());

    m2.push_back(a1, v0);
    m2.push_back(a1, v1);
    m2.push_back(a1, v2, a2);
    m2.push_back(a1, v3);
    m2.push_back(a2, v2);
    m2.pop_back(a1);
    TRACE("parray", 
          m2.display_info(tout, a1); tout << "\n";
          m2.display_info(tout, a2); tout << "\n";
          );
    m2.reroot(a1);
    TRACE("parray", 
          m2.display_info(tout, a1); tout << "\n";
          m2.display_info(tout, a2); tout << "\n";
          );
    m2.del(a1);
    m2.del(a2);
}
#endif

static void tst5() {
    ast_manager m;
    expr_array  a1;
    expr_array  a2;

    m.mk(a1);
    for (unsigned i = 0; i < 100; i++) {
        m.push_back(a1, m.mk_var(i, m.mk_bool_sort()));
    }

    unsigned long long mem = memory::get_max_used_memory();
    std::cout << "max. heap size: " << static_cast<double>(mem)/static_cast<double>(1024*1024) << " Mbytes\n";

    m.copy(a1, a2);
    
    for (unsigned i = 0; i < 1000000; i++) {
        m.set(a1, i % 100, m.mk_var(rand() % 100, m.mk_bool_sort()));
    }

    mem = memory::get_max_used_memory();
    std::cout << "max. heap size: " << static_cast<double>(mem)/static_cast<double>(1024*1024) << " Mbytes\n";
    
    m.del(a2);
    m.del(a1);
}

void tst_parray() {
    // enable_trace("parray_mem");
    tst1<true>();
    tst2<true>();
    tst3<true>();
    tst1<false>();
    tst2<false>();
    tst3<false>();
    // tst4();
    tst5();
}
