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
            expr* a, *b, *c;
            unsigned   m_count{ 0 };
            bool is_cc;
            inference(): a(nullptr), b(nullptr), c(nullptr), is_cc(false) {}
            inference(app* a, app* b): a(a), b(b), c(nullptr), is_cc(true) {}
            inference(expr* a, expr* b, expr* c): a(a), b(b), c(c), is_cc(false) {}
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

        solver&       ctx;
        ast_manager&  m;
        table_t       m_table;
        inference*    m_queue = nullptr;
        inference*    m_tmp_inference = nullptr;
        unsigned      m_gc_threshold = 100;
        unsigned      m_high_watermark = 1000 ;
        unsigned      m_num_propagations_since_last_gc = 0;
 
        void reset();
        void new_tmp();
        void insert(expr* a, expr* b, expr* lca);
        void insert(app* a, app* b);
        void insert();
        void remove(inference* inf);
        void add_cc(expr* a, expr* b);
        void add_eq(expr* a, expr* b, expr* c);        
        void gc();
        bool enable_cc(app* a, app* b);
        bool enable_eq(expr* a, expr* b, expr* c);


    public:
        ackerman(solver& ctx, ast_manager& m);
        ~ackerman();

        void cg_conflict_eh(expr * n1, expr * n2);
                   
        void used_eq_eh(expr* a, expr* b, expr* lca);
        
        void used_cc_eh(app* a, app* b);

        void propagate();
    };

};
