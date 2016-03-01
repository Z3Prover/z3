/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    symbolic_automata_def.h

Abstract:

    Symbolic Automata over Boolean Algebras, a la Margus Veanes Automata library.

Author:

    Nikolaj Bjorner (nbjorner) 2016-02-27.

Revision History:


--*/

#ifndef SYMBOLIC_AUTOMATA_DEF_H_
#define SYMBOLIC_AUTOMATA_DEF_H_


#include "symbolic_automata.h"
#include "hashtable.h"

typedef std::pair<unsigned, unsigned> unsigned_pair;



template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_total(automaton_t& a) {
    unsigned dead_state = a.num_states();
    moves_t mvs, new_mvs;
    for (unsigned i = 0; i < dead_state; ++i) {
        mvs.reset();
        a.get_moves(i, mvs, true);
        refs_t vs(m);
        
        for (unsigned j = 0; j < mvs.size(); ++j) {
            vs.push_back(mvs[j].t());
        }
        ref_t cond(m_ba.mk_not(m_ba.mk_or(vs.size(), vs.c_ptr())), m);
        lbool is_sat = m_ba.is_sat(cond);
        if (is_sat == l_undef) {
            return 0;
        }
        if (is_sat == l_true) {
            new_mvs.push_back(move_t(m, i, dead_state, cond));
        }
    }
    if (new_mvs.empty()) {
        return a.clone();
    }
    new_mvs.push_back(move_t(m, dead_state, dead_state, m_ba.mk_true()));
    automaton_t::append_moves(0, a, new_mvs);
    
    return alloc(automaton_t, m, a.init(), a.final_states(), new_mvs);        
}

template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_minimize(automaton_t& a) {
    if (a.is_empty()) {
        return a.clone();
    }

    if (a.is_epsilon()) {
        return a.clone();
    }
    // SASSERT(a.is_deterministic());
    
    scoped_ptr<automaton_t> fa = mk_total(a);
    if (!fa) {
        return 0;
    }
    return mk_minimize_total(*fa.get());
}


template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_minimize_total(automaton_t& a) {    
    vector<block> pblocks;
    unsigned_vector blocks;
    pblocks.push_back(block(fa->final_states()));     // 0 |-> final states
//    pblocks.push_back(block(fa->non_final_states());  // 1 |-> non-final states
    for (unsigned i = 0; i < fa->num_states(); ++i) {
        if (fa->is_final_state(i)) {            
            blocks.push_back(0);
        }
        else {
            blocks.push_back(1);
        }
    }
    vector<block> W;
    if (final_block.size() > non_final_block.size()) {
        W.push_back(1);
    }
    else {
        W.push_back(0);
    }
    
#if 0
    
    refs_t trail(m);
    u_map<T*> gamma;
    moves_t mvs;
    while (!W.empty()) {
        block R(pblocks[W.back()]);
        W.pop_back();
        block Rcopy(R);
        gamma.reset();
        uint_set::iterator it = Rcopy.begin(), end = Rcopy.end();
        for (; it != end; ++it) {
            unsigned q = *it;
            mvs.reset();
            fa->get_moves_to(q, mvs);
            for (unsigned i = 0; i < mvs.size(); ++i) {
                unsigned src = mvs[i].src();
                if (pblocks[src].size() > 1) {
                    T* t = mvs[i]();
                    if (gamma.find(src, t1)) {
                        t = m_ba.mk_or(t, t1);
                        trail.push_back(t);
                    }
                    gamma.insert(src, t);
                }
            }
        }
        uint_set relevant;
        u_map<T*>::iterator gend = gamma.end();
        for (u_map<T*>::iterator it = gamma.begin(); it != gend; ++it) {
            relevant.insert(blocks[it->m_key]);
        }
        uint_set::iterator uit = relevant.begin(), uend = relevant.end();
        for (; uit != uend; ++uit) {
            unsigned p0_index = *uit;
            block& p0 = pblocks[p0_index];
            block p1;
            for (u_map<T*>::iterator it = gamma.begin(); it != gend; ++it) {
                if (p0.contains(*it)) p1.push_back(*it);
            }
            if (p1.size() < p0.size()) {
                unsigned p1_index = pblocks.size();
                pblocks.push_back(p1);
                for (uint_set::iterator it = p1.begin(), end = p1.end(); it != end; ++it) {
                    p0.remove(*it);
                    blocks[*it] = p1_index;
                }
                if (W.contains(p0_index)) {
                    W.push_back(p1_index);
                }
                else if (p0.size() <= p1.size()) {
                    W.push_back(p0_index);
                }
                else {
                    W.push_back(p1_index);
                }
            }            
            bool iterate = true;
            while (iterate) {
                iterate = false;
                uint_set relevant;
                for (u_map<T*>::iterator it = gamma.begin(); it != gend; ++it) {
                    if (pblocks[blocks[it->m_key]].size() > 1) { 
                        relevant.insert(blocks[it->m_key]);
                    }
                }
                uint_set::iterator it = relevant.begin(), end = relevant.end();
                for (; it != end; ++it) {
                    block const& p = pblocks[*it];
                    uint_set::iterator bi = p.begin(), be = p.end();

                    block p1;
                    p1.insert(*bi);
                    // psi = gamma[*bi]; // name of key or block?
                    ++bi;
                    for (; bi != be; ++bi) {
                        
                    }
                }
            }
        }
    }
#endif

#if 0
            Func<T, T, T> MkDiff = (x, y) => solver.MkAnd(x, solver.MkNot(y));

            while (!W.IsEmpty)
            {
                //keep using Bcopy until no more changes occur
                //effectively, this replaces the loop over characters
                bool iterate = true; 
                    //in each relevant block all states lead to B due to the initial splitting

                    //only relevant blocks are potentially split
                    foreach (var P in relevant2)
                    {
                        var PE = P.GetEnumerator();
                        PE.MoveNext();

                        var P1 = new Block();
                        bool splitFound = false;

                        var psi = Gamma[PE.Current];
                        P1.Add(PE.Current); //C has at least 2 elements

                        #region compute C1 as the new sub-block of C
                        while (PE.MoveNext())
                        {
                            var q = PE.Current;
                            var phi = Gamma[q];
                            if (splitFound)
                            {
                                var psi_and_phi = solver.MkAnd(psi, phi);
                                if (solver.IsSatisfiable(psi_and_phi))
                                    P1.Add(q);
                            }
                            else
                            {
                                var psi_min_phi = MkDiff(psi, phi);
                                if (solver.IsSatisfiable(psi_min_phi))
                                {
                                    psi = psi_min_phi;
                                    splitFound = true;
                                }
                                else // [[psi]] is subset of [[phi]]
                                {
                                    var phi_min_psi = MkDiff(phi, psi);
                                    if (!solver.IsSatisfiable(phi_min_psi))
                                        P1.Add(q); //psi and phi are equivalent
                                    else
                                    {
                                        //there is some a: q --a--> B and p --a--> compl(B) for all p in C1
                                        P1.Clear();
                                        P1.Add(q);
                                        psi = phi_min_psi;
                                        splitFound = true;
                                    }
                                }
                            }
                        }
                        #endregion

                        #region split P
                        if (P1.Count < P.Count)
                        {
                            iterate = (iterate || (P.Count > 2)); //otherwise C was split into singletons
                            foreach (var p in P1)
                            {
                                P.Remove(p);
                                Blocks[p] = P1;
                            }

                            if (W.Contains(P))
                                W.Push(P1);
                            else if (P.Count <= P1.Count)
                                W.Push(P);
                            else
                                W.Push(P1);
                        }
                        #endregion
                    }
                }
            }

            Dictionary<Pair<int, int>, HashSet<T>> condMap = new Dictionary<Pair<int, int>, HashSet<T>>();
            foreach (var move in GetMoves())
            {
                int s = Blocks[move.SourceState].GetRepresentative();
                int t = Blocks[move.TargetState].GetRepresentative();
                var st = new Pair<int, int>(s, t);
                HashSet<T> condSet;
                if (!condMap.TryGetValue(st, out condSet))
                {
                    condSet = new HashSet<T>();
                    condSet.Add(move.Label);
                    condMap[st] = condSet;
                }
                else
                    condSet.Add(move.Label);
            }
            int newInitState = Blocks[fa.InitialState].GetRepresentative();
            var newMoves = new List<Move<T>>();
            var newFinals = new HashSet<int>();
            foreach (var entry in condMap)
                newMoves.Add(Move<T>.Create(entry.Key.First, entry.Key.Second, solver.MkOr(entry.Value)));
            foreach (var f in GetFinalStates())
                newFinals.Add(Blocks[f].GetRepresentative());

            var res = Create(newInitState, newFinals, newMoves);
            res.isDeterministic = true;
            res.isEpsilonFree = true;
            //res.EliminateDeadStates();
            return res;
#endif
    
    return 0;
        
}

template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_product(automaton_t& a, automaton_t& b) {
    map<unsigned_pair, unsigned, pair_hash<unsigned_hash, unsigned_hash>, default_eq<unsigned_pair> > state_ids;
    unsigned_pair init_pair(a.init(), b.init());
    svector<unsigned_pair> todo;
    todo.push_back(init_pair);
    state_ids.insert(init_pair, 0);
    moves_t mvs;
    unsigned_vector final;
    if (a.is_final_state(a.init()) && b.is_final_state(b.init())) {
        final.push_back(0);
    }
    unsigned n = 1;
    moves_t mvsA, mvsB;
    while (!todo.empty()) {
        unsigned_pair curr_pair = todo.back();
        todo.pop_back();
        unsigned src = state_ids[curr_pair];
        mvsA.reset(); mvsB.reset();
        a.get_moves_from(curr_pair.first,  mvsA, true);
        b.get_moves_from(curr_pair.second, mvsB, true);
        for (unsigned i = 0; i < mvsA.size(); ++i) {
            for (unsigned j = 0; j < mvsB.size(); ++j) {
                ref_t ab(m_ba.mk_and(mvsA[i].t(), mvsB[j].t()), m);   
                lbool is_sat = m_ba.is_sat(ab);
                if (is_sat == l_false) {
                    continue;
                }
                else if (is_sat == l_undef) {
                    return 0;
                }
                unsigned_pair tgt_pair(mvsA[i].dst(), mvsB[j].dst());
                unsigned tgt;
                if (!state_ids.find(tgt_pair, tgt)) {
                    tgt = n++;
                    state_ids.insert(tgt_pair, tgt);
                    todo.push_back(tgt_pair);
                    if (a.is_final_state(tgt_pair.first) && b.is_final_state(tgt_pair.second)) {
                        final.push_back(tgt);
                    }
                }
                mvs.push_back(move_t(m, src, tgt, ab));
            }
        }
    }
    
    if (final.empty()) {
        return alloc(automaton_t, m);
    }
    vector<moves_t> inv(n, moves_t());
    for (unsigned i = 0; i < mvs.size(); ++i) {
        move_t const& mv = mvs[i];
        inv[mv.dst()].push_back(move_t(m, mv.dst(), mv.src(), mv.t())); 
    }
    
    svector<bool> back_reachable(n, false);
    for (unsigned i = 0; i < final.size(); ++i) {
        back_reachable[final[i]] = true;
    }
    
    unsigned_vector stack(final);
    while (!stack.empty()) {
        unsigned state = stack.back();
        stack.pop_back();
        moves_t const& mv = inv[state];
        for (unsigned i = 0; i < mv.size(); ++i) {
            state = mv[i].dst();
            if (!back_reachable[state]) {
                back_reachable[state] = true;
                stack.push_back(state);
            }
        }
    }
    
    moves_t mvs1;
    for (unsigned i = 0; i < mvs.size(); ++i) {
        move_t const& mv = mvs[i];
        if (back_reachable[mv.dst()]) {
            mvs1.push_back(mv);
        }
    }
    if (mvs1.empty()) {
        return alloc(automaton_t, m);
    }
    else {
        return alloc(automaton_t, m, 0, final, mvs1);
    }
} 



#endif 
