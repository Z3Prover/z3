/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    object_allocator.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-09.

Revision History:

--*/

#include "util/rational.h"
#include "util/object_allocator.h"

struct cell {
    rational m_coeff;
    unsigned m_i;
    unsigned m_j;
    cell *   m_next_row;
    cell *   m_next_col;
public:
    static unsigned g_num_allocated_cells;
    static unsigned g_num_deallocated_cells;
    static unsigned g_num_recycled_cells;
    
    cell() {
        g_num_allocated_cells++;
    }

    ~cell() {
        g_num_deallocated_cells++;
    }

    void reset() {
        m_coeff.reset();
        g_num_recycled_cells++;
    }
};

unsigned cell::g_num_allocated_cells = 0;
unsigned cell::g_num_deallocated_cells = 0;
unsigned cell::g_num_recycled_cells = 0;

typedef object_allocator<cell, true, simple_reset_proc<cell> > cell_allocator;

static void tst1() {
    cell_allocator m;
    
    cell * c1 = m.allocate<true>();
    /* cell * c2 = */ m.allocate<true>();

    c1->m_coeff = rational(10);
    m.recycle(c1);
    
    cell * c3 = m.allocate<true>();
    (void)c3;
    ENSURE(c3->m_coeff.is_zero());
}

static void tst2() {
    cell_allocator m;
    ENSURE(m.capacity() >= 2);
    cell_allocator::worker_object_allocator m1 = m.get_worker_allocator(0);
    cell_allocator::worker_object_allocator m2 = m.get_worker_allocator(1);
    m.enable_concurrent(true);

    vector<std::pair<cell *, int> > object_coeff_pairs;
    unsigned num_resets = 0;

    for (unsigned i = 0; i < 100000; i++) {
        unsigned idx = rand() % 6;
        if (idx < 4) {
            cell * c;
            if (idx < 2) 
                c = m1.allocate<true>();
            else 
                c = m2.allocate<true>();
            ENSURE(c->m_coeff.is_zero());
            int val = rand();
            c->m_coeff = rational(val);
            object_coeff_pairs.push_back(std::make_pair(c, val));
        }
        else {
            if (!object_coeff_pairs.empty()) {
                unsigned idx = rand() % object_coeff_pairs.size();
                cell * c = object_coeff_pairs[idx].first;
                CTRACE("object_allocator", c->m_coeff != rational(object_coeff_pairs[idx].second), tout << c->m_coeff << " != " << rational(object_coeff_pairs[idx].second) << "\n";);
                ENSURE(c->m_coeff == rational(object_coeff_pairs[idx].second));
                if (idx < 5)
                    m1.recycle(c);
                else 
                    m2.recycle(c);
                object_coeff_pairs.erase(object_coeff_pairs.begin() + idx);
            }
        }

        if (rand() % 5000 == 0) {
            m.enable_concurrent(false);
            m.reset();
            object_coeff_pairs.reset();
            m.enable_concurrent(true);
            num_resets++;
        }
    }
    TRACE("object_allocator", tout << "num. resets: " << num_resets << "\n";);
}

void tst_object_allocator() {
    tst1();
    tst2();
    TRACE("object_allocator", tout << "num. allocated cells: " << cell::g_num_allocated_cells << "\nnum. deallocated cells: " << cell::g_num_deallocated_cells << 
          "\nnum. recycled cells: " << cell::g_num_recycled_cells << "\n";);
    ENSURE(cell::g_num_allocated_cells == cell::g_num_deallocated_cells);
}
