/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_ackerman.h

Abstract:

    Ackerman reduction plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once

#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"

namespace bv {

    class solver;

    class ackerman {

        struct vv {
            euf::theory_var v1, v2;
            vv* m_next{ nullptr };
            vv* m_prev{ nullptr };
            unsigned   m_count{ 0 };
            vv():v1(euf::null_theory_var), v2(euf::null_theory_var) {}
            vv(euf::theory_var v1, euf::theory_var v2):v1(v1), v2(v2) {}
        };

        struct vv_eq {
            bool operator()(vv const* a, vv const* b) const {
                return a->v1 == b->v1 && a->v2 == b->v2;
            }
        };
        
        struct vv_hash {
            unsigned operator()(vv const* a) const {
                return mk_mix(a->v1, a->v2, 0);
            }
        };

        typedef hashtable<vv*, vv_hash, vv_eq> table_t;

        solver&       s;
        table_t       m_table;
        vv*    m_queue { nullptr };
        vv*    m_tmp_vv { nullptr };
        unsigned      m_gc_threshold { 1 };
        unsigned      m_num_propagations_since_last_gc { 0 };
 
        void reset();
        void new_tmp();
        void remove(vv* inf);
        void gc();
        void push_to_front(vv* inf);        
        void remove_from_queue(vv* inf);
        void add_cc(euf::theory_var v1, euf::theory_var v2);

    public:
        ackerman(solver& s);
        ~ackerman();

        void used_eq_eh(euf::theory_var v1, euf::theory_var v2);

        void propagate();
    };

};
