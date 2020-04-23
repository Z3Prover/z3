/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_unsat_core_learner.cpp

Abstract:
   itp cores

Author:
    Bernhard Gleiss

Revision History:


--*/

#include "ast/for_each_expr.h"
#include "ast/proofs/proof_utils.h"
#include "muz/spacer/spacer_unsat_core_learner.h"
#include "muz/spacer/spacer_unsat_core_plugin.h"
#include "muz/spacer/spacer_iuc_proof.h"
#include "muz/spacer/spacer_util.h"


namespace spacer {

unsat_core_learner::~unsat_core_learner() {
    std::for_each(m_plugins.begin(), m_plugins.end(), delete_proc<unsat_core_plugin>());
}

void unsat_core_learner::register_plugin(unsat_core_plugin* plugin) {
    m_plugins.push_back(plugin);
}

void unsat_core_learner::compute_unsat_core(expr_ref_vector& unsat_core) {
    proof_post_order it(m_pr.get(), m);
    while (it.hasNext()) {
        proof* curr = it.next();

        bool done = is_closed(curr);
        if (done) continue;

        if (m.get_num_parents(curr) > 0) {
            done = true;
            for (proof* p : m.get_parents(curr)) done &= !is_b_open(p);
            set_closed(curr, done);
        }

        // we have now collected all necessary information,
        // so we can visit the node
        // if the node mixes A-reasoning and B-reasoning
        // and contains non-closed premises
        if (!done) {
            if (is_a(curr) && is_b(curr)) {
                compute_partial_core(curr);
            }
        }
    }

    // give plugins chance to finalize their unsat-core-computation
    finalize();

    // TODO: remove duplicates from unsat core?

    // move all lemmas into vector
    for (expr* e : m_unsat_core) {
        unsat_core.push_back(e);
    }
}

void unsat_core_learner::compute_partial_core(proof* step) {
    for (unsat_core_plugin* plugin : m_plugins) {
        if (is_closed(step)) break;
        plugin->compute_partial_core(step);
    }
}

void unsat_core_learner::finalize() {
    for (unsat_core_plugin* plugin : m_plugins) {
        plugin->finalize();
    }
}

bool unsat_core_learner::is_closed(proof* p) {
    return m_closed.is_marked(p);
}

void unsat_core_learner::set_closed(proof* p, bool value) {
    m_closed.mark(p, value);
}


void unsat_core_learner::add_lemma_to_core(expr* lemma) {
    m_unsat_core.push_back(lemma);
}

}
