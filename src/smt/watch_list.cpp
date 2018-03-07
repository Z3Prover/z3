/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    watch_list.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-23.

Revision History:

--*/
#include "smt/watch_list.h"

namespace smt {

#define DEFAULT_WATCH_LIST_SIZE (sizeof(clause *) * 4)
#ifdef _AMD64_
// make sure data is aligned in 64 bit machines
#define HEADER_SIZE (4 * sizeof(unsigned)) 
#else
#define HEADER_SIZE (3 * sizeof(unsigned))
#endif

    void watch_list::destroy() {
        if (m_data) {
            dealloc_svect(reinterpret_cast<char*>(m_data) - HEADER_SIZE);
        }
    }
    
    void watch_list::expand() {
        if (m_data == nullptr) {
        unsigned size       = DEFAULT_WATCH_LIST_SIZE + HEADER_SIZE;
            unsigned * mem      = reinterpret_cast<unsigned*>(alloc_svect(char, size));
#ifdef _AMD64_
        ++mem;  // make sure data is aligned in 64 bit machines
#endif
            *mem                = 0;
            ++mem;
            *mem                = DEFAULT_WATCH_LIST_SIZE;
            ++mem;
            *mem                = DEFAULT_WATCH_LIST_SIZE;
            ++mem;
            m_data              = reinterpret_cast<char*>(mem); 
            SASSERT( begin_lits_core() % sizeof(literal) == 0 );
        }
        else {
            unsigned curr_begin_bin = begin_lits_core();
            unsigned curr_capacity  = end_lits_core();
            unsigned bin_bytes      = curr_capacity - curr_begin_bin;
            /* dvitek: Added +3&~3U to fix alignment issues on
             * sparc64/solaris. ("literal"s must be 4-byte aligned).  Should
             * also help performance elsewhere.
             */
            unsigned new_capacity   = (((curr_capacity * 3 + sizeof(clause *)) >> 1)+3)&~3U;
            unsigned * mem          = reinterpret_cast<unsigned*>(alloc_svect(char, new_capacity + HEADER_SIZE));
            unsigned curr_end_cls   = end_cls_core();
#ifdef _AMD64_
        ++mem;  // make sure data is aligned in 64 bit machines
#endif
        *mem                    = curr_end_cls;
            ++mem;
            SASSERT(bin_bytes <= new_capacity);
            unsigned new_begin_bin  = new_capacity - bin_bytes;
            *mem                    = new_begin_bin;
            ++mem; 
            *mem                    = new_capacity;
            ++mem;
            memcpy(mem, m_data, curr_end_cls);
            memcpy(reinterpret_cast<char *>(mem) + new_begin_bin, m_data + curr_begin_bin, bin_bytes);
            destroy();
            m_data = reinterpret_cast<char *>(mem);
            SASSERT( begin_lits_core() % sizeof(literal) == 0 );
        }
    }
    
    void watch_list::remove_clause(clause * c) {
        clause_iterator begin = begin_clause();
        clause_iterator end   = end_clause();
        clause_iterator it    = std::find(begin, end, c);
        if (it == end) {
            return;
        }
        clause_iterator prev  = it;
        ++it;
        for(; it != end; ++it, ++prev) {
            *prev = *it;
        }
        end_cls_core() -= sizeof(clause *);
    }
    
    void watch_list::remove_literal(literal l) {
        literal * begin = begin_literals();
        literal * end   = end_literals();
        literal * it    = std::find(begin, end, l);
        if (it == end) {
            return;
        }
        literal * prev  = it;
        while (it != begin) {
            SASSERT(it == prev);
            --it;
            *prev = *it;
            --prev;
        }
        SASSERT(prev == begin);
        begin_lits_core() += sizeof(literal);
    }
    
};
