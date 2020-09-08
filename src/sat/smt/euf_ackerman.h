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
#include "ast/euf/euf_egraph.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"

namespace euf {

    class solver;


    class ackerman {

        struct inference : dll_base<inference>{
            bool is_cc;
            expr* a, *b, *c;
            unsigned   m_count{ 0 };
            inference():is_cc(false), a(nullptr), b(nullptr), c(nullptr) {}
            inference(app* a, app* b):is_cc(true), a(a), b(b), c(nullptr) {}
            inference(expr* a, expr* b, expr* c):is_cc(false), a(a), b(b), c(c) {}
        };

        struct inference_eq {
            bool operator()(inference const* a, inference const* b) const {
                return a->is_cc == b->is_cc && a->a == b->a && a->b == b->b && a->c == b->c;
            }
        };
        
        struct inference_hash {
            unsigned operator()(inference const* a) const {
                SASSERT(a->a && a->b);
                return mk_mix(a->a->get_id(), a->b->get_id(), a->c ? a->c->get_id() : 0);
            }
        };

        typedef hashtable<inference*, inference_hash, inference_eq> table_t;

        solver&       s;
        ast_manager&  m;
        table_t       m_table;
        inference*    m_queue { nullptr };
        inference*    m_tmp_inference { nullptr };
        unsigned      m_gc_threshold { 100 };
        unsigned      m_high_watermark { 1000 };
        unsigned      m_num_propagations_since_last_gc { 0 };
 
        void reset();
        void new_tmp();
        void insert(expr* a, expr* b, expr* lca);
        void insert(app* a, app* b);
        void insert();
        void remove(inference* inf);
        void add_cc(expr* a, expr* b);
        void add_eq(expr* a, expr* b, expr* c);        
        void gc();

    public:
        ackerman(solver& s, ast_manager& m);
        ~ackerman();

        void cg_conflict_eh(expr * n1, expr * n2);
                   
        void used_eq_eh(expr* a, expr* b, expr* lca);
        
        void used_cc_eh(app* a, app* b);

        void propagate();
    };

};
