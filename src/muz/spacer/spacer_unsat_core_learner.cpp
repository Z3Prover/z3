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
#include <unordered_map>

#include "muz/spacer/spacer_unsat_core_learner.h"
#include "muz/spacer/spacer_unsat_core_plugin.h"
#include "muz/spacer/spacer_iuc_proof.h"
#include "ast/for_each_expr.h"

#include "muz/spacer/spacer_util.h"


namespace spacer
{

unsat_core_learner::~unsat_core_learner()
{
    std::for_each(m_plugins.begin(), m_plugins.end(), delete_proc<unsat_core_plugin>());
}

void unsat_core_learner::register_plugin(unsat_core_plugin* plugin)
{
    m_plugins.push_back(plugin);
}

void unsat_core_learner::compute_unsat_core(expr_ref_vector& unsat_core)
{
    // traverse proof
    proof_post_order it(m_pr.get(), m);
    while (it.hasNext())
    {
        proof* currentNode = it.next();

        if (m.get_num_parents(currentNode) > 0)
        {
            bool need_to_mark_closed = true;

            for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i)
            {
                SASSERT(m.is_proof(currentNode->get_arg(i)));
                proof* premise = to_app(currentNode->get_arg(i));
                
                need_to_mark_closed = need_to_mark_closed && (!m_pr.is_b_marked(premise) || m_closed.is_marked(premise));
            }

            // save result
            m_closed.mark(currentNode, need_to_mark_closed);
        }

        // we have now collected all necessary information, so we can visit the node
        // if the node mixes A-reasoning and B-reasoning and contains non-closed premises
        if (m_pr.is_a_marked(currentNode) && m_pr.is_b_marked(currentNode) && !m_closed.is_marked(currentNode))
        {
            compute_partial_core(currentNode); // then we need to compute a partial core
        }
    }

    // give plugins chance to finalize their unsat-core-computation
    finalize();

    // TODO: remove duplicates from unsat core?

    verbose_stream() << std::endl;
    // move all lemmas into vector
    for (expr* const* it = m_unsat_core.begin(); it != m_unsat_core.end(); ++it)
    {
        unsat_core.push_back(*it);
    }
}

void unsat_core_learner::compute_partial_core(proof* step)
{
    for (unsat_core_plugin** it=m_plugins.begin(), **end = m_plugins.end (); it != end && !m_closed.is_marked(step); ++it)
    {
        unsat_core_plugin* plugin = *it;
        plugin->compute_partial_core(step);
    }
}

void unsat_core_learner::finalize()
{
    for (unsat_core_plugin** it=m_plugins.begin(); it != m_plugins.end(); ++it)
    {
        unsat_core_plugin* plugin = *it;
        plugin->finalize();
    }
}

bool unsat_core_learner::is_closed(proof*p)
{
    return m_closed.is_marked(p);
}
void unsat_core_learner::set_closed(proof* p, bool value)
{
    m_closed.mark(p, value);
}
  
bool unsat_core_learner::is_b_open(proof *p)
{
     return m_pr.is_b_marked(p) && !is_closed (p);
}

void unsat_core_learner::add_lemma_to_core(expr* lemma)
{
    m_unsat_core.push_back(lemma);
}
}
