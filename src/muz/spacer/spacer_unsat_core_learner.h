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
#ifndef _SPACER_UNSAT_CORE_LEARNER_H_
#define _SPACER_UNSAT_CORE_LEARNER_H_

#include "ast/ast.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_proof_utils.h"

namespace spacer {


    class unsat_core_plugin;
    class iuc_proof;
    class unsat_core_learner
    {
        typedef obj_hashtable<expr> expr_set;

    public:
        unsat_core_learner(ast_manager& m, iuc_proof& pr, bool print_farkas_stats = false, bool iuc_debug_proof = false) : m(m), m_pr(pr), m_unsat_core(m), m_print_farkas_stats(print_farkas_stats), m_iuc_debug_proof(iuc_debug_proof) {};
        virtual ~unsat_core_learner();

        ast_manager& m;
        iuc_proof& m_pr;

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

        bool is_b_open (proof *p);
        
        /*
         * adds a lemma to the unsat core
         */
        void add_lemma_to_core(expr* lemma);



    private:
        ptr_vector<unsat_core_plugin> m_plugins;
        ast_mark m_closed;

        expr_ref_vector m_unsat_core; // collects the lemmas of the unsat-core, will at the end be inserted into unsat_core.

        /*
         * computes partial core for step by delegating computation to plugins
         */
        void compute_partial_core(proof* step);

        /*
         * finalize computation of unsat-core
         */
        void finalize();
        
        bool m_print_farkas_stats;
        bool m_iuc_debug_proof;
    };

}

#endif
