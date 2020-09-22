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

#include "util/dlist.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"

namespace bv {

    class solver;

    class ackerman {

        struct vv : dll_base<vv> {
            euf::theory_var v1, v2;
            unsigned   m_count{ 0 };
            unsigned   m_glue{ UINT_MAX };
            vv():v1(euf::null_theory_var), v2(euf::null_theory_var) {}
            vv(euf::theory_var v1, euf::theory_var v2):v1(v1), v2(v2) {}
            void set_var(euf::theory_var x, euf::theory_var y) { v1 = x; v2 = y; m_count = 0; m_glue = UINT_MAX; }
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
        vv*           m_queue { nullptr };
        vv*           m_tmp_vv { nullptr };

        unsigned      m_gc_threshold { 100 };
        unsigned      m_propagate_high_watermark { 10000 };
        unsigned      m_propagate_low_watermark { 10 };
        unsigned      m_num_propagations_since_last_gc { 0 };
        bool_vector   m_diff_levels;

        void update_glue(vv& v);
        void reset();
        void new_tmp();
        void remove(vv* inf);
        void gc();
        void add_cc(euf::theory_var v1, euf::theory_var v2);

    public:
        ackerman(solver& s);
        ~ackerman();

        void used_eq_eh(euf::theory_var v1, euf::theory_var v2);

        void used_diseq_eh(euf::theory_var v1, euf::theory_var v2);

        void propagate();
    };

};
