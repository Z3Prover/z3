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
#include "ast/for_each_expr.h"

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

void unsat_core_learner::compute_unsat_core(proof *root, expr_set& asserted_b, expr_ref_vector& unsat_core)
{
    // transform proof in order to get a proof which is better suited for unsat-core-extraction
    proof_ref pr(root, m);

    reduce_hypotheses(pr);
    STRACE("spacer.unsat_core_learner",
           verbose_stream() << "Reduced proof:\n" << mk_ismt2_pp(pr, m) << "\n";
    );

    // compute symbols occurring in B
    collect_symbols_b(asserted_b);

    // traverse proof
    proof_post_order it(root, m);
    while (it.hasNext())
    {
        proof* currentNode = it.next();

        if (m.get_num_parents(currentNode) == 0)
        {
            switch(currentNode->get_decl_kind())
            {

                case PR_ASSERTED: // currentNode is an axiom
                {
                    if (asserted_b.contains(m.get_fact(currentNode)))
                    {
                        m_b_mark.mark(currentNode, true);
                    }
                    else
                    {
                        m_a_mark.mark(currentNode, true);
                    }
                    break;
                }
                    // currentNode is a hypothesis:
                case PR_HYPOTHESIS:
                {
                    m_h_mark.mark(currentNode, true);
                    break;
                }
                default:
                {
                    break;
                }
            }
        }
        else
        {
            // collect from parents whether derivation of current node contains A-axioms, B-axioms and hypothesis
            bool need_to_mark_a = false;
            bool need_to_mark_b = false;
            bool need_to_mark_h = false;
            bool need_to_mark_closed = true;

            for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i)
            {
                SASSERT(m.is_proof(currentNode->get_arg(i)));
                proof* premise = to_app(currentNode->get_arg(i));

                need_to_mark_a = need_to_mark_a || m_a_mark.is_marked(premise);
                need_to_mark_b = need_to_mark_b || m_b_mark.is_marked(premise);
                need_to_mark_h = need_to_mark_h || m_h_mark.is_marked(premise);
                need_to_mark_closed = need_to_mark_closed && (!m_b_mark.is_marked(premise) || m_closed.is_marked(premise));
            }

            // if current node is application of lemma, we know that all hypothesis are removed
            if(currentNode->get_decl_kind() == PR_LEMMA)
            {
                need_to_mark_h = false;
            }

            // save results
            m_a_mark.mark(currentNode, need_to_mark_a);
            m_b_mark.mark(currentNode, need_to_mark_b);
            m_h_mark.mark(currentNode, need_to_mark_h);
            m_closed.mark(currentNode, need_to_mark_closed);
        }

        // we have now collected all necessary information, so we can visit the node
        // if the node mixes A-reasoning and B-reasoning and contains non-closed premises
        if (m_a_mark.is_marked(currentNode) && m_b_mark.is_marked(currentNode) && !m_closed.is_marked(currentNode))
        {
            compute_partial_core(currentNode); // then we need to compute a partial core
            // SASSERT(!(m_a_mark.is_marked(currentNode) && m_b_mark.is_marked(currentNode)) || m_closed.is_marked(currentNode)); TODO: doesn't hold anymore if we do the mincut-thing!
        }
    }

    // give plugins chance to finalize their unsat-core-computation
    finalize();

    // TODO: remove duplicates from unsat core?

    bool debug_proof = false;
    if(debug_proof)
    {
        // print proof for debugging
        verbose_stream() << "\n\nProof:\n";
        std::unordered_map<unsigned, unsigned> id_to_small_id;
        unsigned counter = 0;

        proof_post_order it2(root, m);
        while (it2.hasNext())
        {
            proof* currentNode = it2.next();

            SASSERT(id_to_small_id.find(currentNode->get_id()) == id_to_small_id.end());
            id_to_small_id.insert(std::make_pair(currentNode->get_id(), counter));

            verbose_stream() << counter << " ";
            verbose_stream() << "[";
            if (is_a_marked(currentNode))
            {
                verbose_stream() << "a";
            }
            if (is_b_marked(currentNode))
            {
                verbose_stream() << "b";
            }
            if (is_h_marked(currentNode))
            {
                verbose_stream() << "h";
            }
            if (is_closed(currentNode))
            {
                verbose_stream() << "c";
            }
            verbose_stream() << "] ";

            if (m.get_num_parents(currentNode) == 0)
            {
                switch (currentNode->get_decl_kind())
                {
                    case PR_ASSERTED:
                        verbose_stream() << "asserted";
                        break;
                    case PR_HYPOTHESIS:
                        verbose_stream() << "hypothesis";
                        break;
                    default:
                        verbose_stream() << "unknown axiom-type";
                        break;
                }
            }
            else
            {
                if (currentNode->get_decl_kind() == PR_LEMMA)
                {
                    verbose_stream() << "lemma";
                }
                else if (currentNode->get_decl_kind() == PR_TH_LEMMA)
                {
                    verbose_stream() << "th_lemma";
                    func_decl* d = currentNode->get_decl();
                    symbol sym;
                    if (d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
                        d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
                        d->get_parameter(1).is_symbol(sym) && sym == "farkas")
                    {
                        verbose_stream() << "(farkas)";
                    }
                    else
                    {
                        verbose_stream() << "(other)";
                    }
                }
                else
                {
                    verbose_stream() << "step";
                }
                verbose_stream() << " from ";
                for (int i = m.get_num_parents(currentNode) - 1; i >= 0  ; --i)
                {
                    proof* premise = to_app(currentNode->get_arg(i));
                    unsigned premise_small_id = id_to_small_id[premise->get_id()];
                    if (i > 0)
                    {
                        verbose_stream() << premise_small_id << ", ";
                    }
                    else
                    {
                        verbose_stream() << premise_small_id;
                    }

                }
            }
            if (currentNode->get_decl_kind() == PR_TH_LEMMA || (is_a_marked(currentNode) && is_b_marked(currentNode)) || is_h_marked(currentNode) || (!is_a_marked(currentNode) && !is_b_marked(currentNode)))
            {
                verbose_stream() << std::endl;
            }
            else
            {
                verbose_stream() << ": " << mk_pp(m.get_fact(currentNode), m) << std::endl;
            }
            ++counter;
        }
    }
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


bool unsat_core_learner::is_a_marked(proof* p)
{
    return m_a_mark.is_marked(p);
}
bool unsat_core_learner::is_b_marked(proof* p)
{
    return m_b_mark.is_marked(p);
}
bool unsat_core_learner::is_h_marked(proof* p)
{
    return m_h_mark.is_marked(p);
}
bool unsat_core_learner::is_closed(proof*p)
{
    return m_closed.is_marked(p);
}
void unsat_core_learner::set_closed(proof* p, bool value)
{
    m_closed.mark(p, value);
}

    void unsat_core_learner::add_lemma_to_core(expr* lemma)
    {
        m_unsat_core.push_back(lemma);
    }


class collect_pure_proc {
    func_decl_set& m_symbs;
public:
    collect_pure_proc(func_decl_set& s):m_symbs(s) {}

    void operator()(app* a) {
        if (a->get_family_id() == null_family_id) {
            m_symbs.insert(a->get_decl());
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};

void unsat_core_learner::collect_symbols_b(const expr_set& axioms_b)
{
    expr_mark visited;
    collect_pure_proc proc(m_symbols_b);
    for (expr_set::iterator it = axioms_b.begin(); it != axioms_b.end(); ++it)
    {
        for_each_expr(proc, visited, *it);
    }
}

class is_pure_expr_proc {
    func_decl_set const& m_symbs;
    array_util           m_au;
public:
    struct non_pure {};

    is_pure_expr_proc(func_decl_set const& s, ast_manager& m):
    m_symbs(s),
    m_au (m)
    {}

    void operator()(app* a) {
        if (a->get_family_id() == null_family_id) {
            if (!m_symbs.contains(a->get_decl())) {
                throw non_pure();
            }
        }
        else if (a->get_family_id () == m_au.get_family_id () &&
                 a->is_app_of (a->get_family_id (), OP_ARRAY_EXT)) {
            throw non_pure();
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};

bool unsat_core_learner::only_contains_symbols_b(expr* expr) const
{
    is_pure_expr_proc proc(m_symbols_b, m);
    try {
        for_each_expr(proc, expr);
    }
    catch (is_pure_expr_proc::non_pure)
    {
        return false;
    }
    return true;
}



}
