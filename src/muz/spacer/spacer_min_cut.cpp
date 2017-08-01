/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_min_cut.cpp

Abstract:
    min cut solver

Author:
    Bernhard Gleiss

Revision History:


--*/
#include "muz/spacer/spacer_min_cut.h"

namespace spacer {

    spacer_min_cut::spacer_min_cut()
    {
        m_n = 2;

        // push back two empty vectors for source and sink
        m_edges.push_back(vector<std::pair<unsigned, unsigned>>());
        m_edges.push_back(vector<std::pair<unsigned, unsigned>>());
    }

    unsigned spacer_min_cut::new_node()
    {
        return m_n++;
    }

    void spacer_min_cut::add_edge(unsigned int i, unsigned int j, unsigned int capacity)
    {
        if (i >= m_edges.size())
        {
            m_edges.resize(i + 1);
        }
        m_edges[i].insert(std::make_pair(j, 1));
        STRACE("spacer.mincut",
               verbose_stream() << "adding edge (" << i << "," << j << ")\n";
        );

    }

    void spacer_min_cut::compute_min_cut(vector<unsigned>& cut_nodes)
    {
        if (m_n == 2)
        {
            return;
        }

        m_d.resize(m_n);
        m_pred.resize(m_n);

        // compute initial distances and number of nodes
        compute_initial_distances();

        unsigned i = 0;

        while (m_d[0] < m_n)
        {
            unsigned j = get_admissible_edge(i);

            if (j < m_n)
            {
                // advance(i)
                m_pred[j] = i;
                i = j;

                // if i is the sink, augment path
                if (i == 1)
                {
                    augment_path();
                    i = 0;
                }
            }
            else
            {
                // retreat
                compute_distance(i);
                if (i != 0)
                {
                    i = m_pred[i];
                }
            }
        }

        // split nodes into reachable and unreachable ones
        vector<bool> reachable(m_n);
        compute_reachable_nodes(reachable);

        // find all edges between reachable and unreachable nodes and for each such edge, add corresponding lemma to unsat-core
        compute_cut_and_add_lemmas(reachable, cut_nodes);
    }

    void spacer_min_cut::compute_initial_distances()
    {
        vector<unsigned> todo;
        vector<bool> visited(m_n);

        todo.push_back(0); // start at the source, since we do postorder traversel

        while (!todo.empty())
        {
            unsigned current = todo.back();

            // if we haven't already visited current
            if (!visited[current]) {
                bool existsUnvisitedParent = false;

                // add unprocessed parents to stack for DFS. If there is at least one unprocessed parent, don't compute the result
                // for current now, but wait until those unprocessed parents are processed.
                for (unsigned i = 0, sz = m_edges[current].size(); i < sz; ++i)
                {
                    unsigned parent = m_edges[current][i].first;

                    // if we haven't visited the current parent yet
                    if(!visited[parent])
                    {
                        // add it to the stack
                        todo.push_back(parent);
                        existsUnvisitedParent = true;
                    }
                }

                // if we already visited all parents, we can visit current too
                if (!existsUnvisitedParent) {
                    visited[current] = true;
                    todo.pop_back();

                    compute_distance(current); // I.H. all parent distances are already computed
                }
            }
            else {
                todo.pop_back();
            }
        }
    }

    unsigned spacer_min_cut::get_admissible_edge(unsigned i)
    {
        for (const auto& pair : m_edges[i])
        {
            if (pair.second > 0 && m_d[i] == m_d[pair.first] + 1)
            {
                return pair.first;
            }
        }
        return m_n; // no element found
    }

    void spacer_min_cut::augment_path()
    {
        // find bottleneck capacity
        unsigned max = std::numeric_limits<unsigned int>::max();
        unsigned k = 1;
        while (k != 0)
        {
            unsigned l = m_pred[k];
            for (const auto& pair : m_edges[l])
            {
                if (pair.first == k)
                {
                    if (max > pair.second)
                    {
                        max = pair.second;
                    }
                }
            }
            k = l;
        }

        k = 1;
        while (k != 0)
        {
            unsigned l = m_pred[k];

            // decrease capacity
            for (auto& pair : m_edges[l])
            {
                if (pair.first == k)
                {
                    pair.second -= max;
                }
            }
            // increase reverse flow
            bool already_exists = false;
            for (auto& pair : m_edges[k])
            {
                if (pair.first == l)
                {
                    already_exists = true;
                    pair.second += max;
                }
            }
            if (!already_exists)
            {
                m_edges[k].insert(std::make_pair(l, max));
            }
            k = l;
        }
    }

    void spacer_min_cut::compute_distance(unsigned i)
    {
        if (i == 1) // sink node
        {
            m_d[1] = 0;
        }
        else
        {
            unsigned min = std::numeric_limits<unsigned int>::max();

            // find edge (i,j) with positive residual capacity and smallest distance
            for (const auto& pair : m_edges[i])
            {
                if (pair.second > 0)
                {
                    unsigned tmp = m_d[pair.first] + 1;
                    if (tmp < min)
                    {
                        min = tmp;
                    }
                }
            }
            m_d[i] = min;
        }
    }

    void spacer_min_cut::compute_reachable_nodes(vector<bool>& reachable)
    {
        vector<unsigned> todo;

        todo.push_back(0);
        while (!todo.empty())
        {
            unsigned current = todo.back();
            todo.pop_back();

            if (!reachable[current])
            {
                reachable[current] = true;

                for (const auto& pair : m_edges[current])
                {
                    if (pair.second > 0)
                    {
                        todo.push_back(pair.first);
                    }
                }
            }
        }
    }

    void spacer_min_cut::compute_cut_and_add_lemmas(vector<bool>& reachable, vector<unsigned>& cut_nodes)
    {
        vector<unsigned> todo;
        vector<bool> visited(m_n);

        todo.push_back(0);
        while (!todo.empty())
        {
            unsigned current = todo.back();
            todo.pop_back();

            if (!visited[current])
            {
                visited[current] = true;

                for (const auto& pair : m_edges[current])
                {
                    unsigned successor = pair.first;
                    if (reachable[successor])
                    {
                        todo.push_back(successor);
                    }
                    else
                    {
                        cut_nodes.push_back(successor);
                    }
                }
            }
        }
    }
}
