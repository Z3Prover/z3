/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_unsat_core_learner.h

Abstract:

    itp cores

Author:
    Bernhard Gleiss

Revision History:


--*/
#pragma once

#include "ast/ast.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_proof_utils.h"
#include "muz/spacer/spacer_iuc_proof.h"

namespace spacer {


    class unsat_core_plugin;
    class iuc_proof;
    class unsat_core_learner {
        typedef obj_hashtable<expr> expr_set;

        ast_manager& m;
        iuc_proof&   m_pr;

        ptr_vector<unsat_core_plugin> m_plugins;
        ast_mark m_closed;

        expr_ref_vector m_unsat_core;

    public:
        unsat_core_learner(ast_manager& m, iuc_proof& pr) :
            m(m), m_pr(pr), m_unsat_core(m) {};
        virtual ~unsat_core_learner();

        ast_manager& get_manager() {return m;}


        bool is_a(proof *pr) {
            // AG: treat hypotheses as A
            // AG: assume that all B-hyp have been eliminated
            // AG: this is not yet true in case of arithmetic eq_prop
            return m_pr.is_a_marked(pr) || is_h(pr);
        }
        bool is_b(proof *pr) {return m_pr.is_b_marked(pr);}
        bool is_h(proof *pr) {return m_pr.is_h_marked(pr);}
        bool is_b_pure(proof *pr) { return m_pr.is_b_pure(pr);}
        bool is_b_open(proof *p) {return m_pr.is_b_marked(p) && !is_closed (p);}

        /*
         * register a plugin for computation of partial unsat cores
         * currently plugins are called in the order they have been registered
         */
        void register_plugin(unsat_core_plugin* plugin);

        /*
         * compute unsat core using the registered unsat-core-plugins
         */
        void compute_unsat_core(expr_ref_vector& unsat_core);

        /*
         * getter/setter methods for data structures exposed to plugins
         * the following invariant can be assumed and need to be maintained by the plugins:
         *  - a node is closed, iff it has already been interpolated, i.e. its contribution is
         *    already covered by the unsat-core.
         */
        bool is_closed(proof* p);
        void set_closed(proof* p, bool value);


        /*
         * adds a lemma to the unsat core
         */
        void add_lemma_to_core(expr* lemma);

    private:

        /*
         * computes partial core for step by delegating computation to plugins
         */
        void compute_partial_core(proof* step);

        /*
         * finalize computation of unsat-core
         */
        void finalize();
    };
}

