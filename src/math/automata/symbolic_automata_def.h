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




template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_total(automaton_t& a) {
    unsigned dead_state = a.num_states();
    moves_t mvs, new_mvs;
    for (unsigned i = 0; i < dead_state; ++i) {
        mvs.reset();
        a.get_moves_from(i, mvs, true);
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

    // TBD private: automaton_t::append_moves(0, a, new_mvs);
    
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
void symbolic_automata<T, M>::add_block(block const& p1, unsigned p0_index, unsigned_vector& blocks, vector<block>& pblocks, unsigned_vector& W) {
    block& p0 = pblocks[p0_index];
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
}

template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_minimize_total(automaton_t& a) {    
    vector<block> pblocks;
    unsigned_vector blocks;
    unsigned_vector non_final;
    for (unsigned i = 0; i < a.num_states(); ++i) {
        if (!a.is_final_state(i)) {
            non_final.push_back(i);
            blocks.push_back(1);
        }
        else {
            blocks.push_back(0);
        }
    }
    pblocks.push_back(block(a.final_states()));      // 0 |-> final states
    pblocks.push_back(block(non_final));             // 1 |-> non-final states

    unsigned_vector W;
    W.push_back(pblocks[0].size() > pblocks[1].size() ? 1 : 0);
        
    refs_t trail(m);
    u_map<T*> gamma;
    moves_t mvs;
    while (!W.empty()) {
        block R(pblocks[W.back()]);
        W.pop_back();
        gamma.reset();
        uint_set::iterator it = R.begin(), end = R.end();
        for (; it != end; ++it) {
            unsigned dst = *it;
            mvs.reset();
            a.get_moves_to(dst, mvs);
            for (unsigned i = 0; i < mvs.size(); ++i) {
                unsigned src = mvs[i].src();
                if (pblocks[src].size() > 1) {
                    T* t = mvs[i].t();
                    T* t1;
                    if (gamma.find(src, t1)) {
                        t = m_ba.mk_or(t, t1);
                        trail.push_back(t);
                    }
                    gamma.insert(src, t);
                }
            }
        }
        uint_set relevant1;
        typedef typename u_map<T*>::iterator gamma_iterator;
        gamma_iterator gend = gamma.end();
        for (gamma_iterator git = gamma.begin(); git != gend; ++git) {
            unsigned p0A_index = blocks[git->m_key];
            if (relevant1.contains(p0A_index)) {
                continue;
            }
            relevant1.insert(p0A_index);
            block& p0A = pblocks[p0A_index];
            block p1;
            for (gamma_iterator it = gamma.begin(); it != gend; ++it) {
                if (p0A.contains(it->m_key)) p1.insert(it->m_key);
            }
            
            add_block(p1, p0A_index, blocks, pblocks, W);

            bool iterate = true;
            while (iterate) {
                iterate = false;
                uint_set relevant2;
                for (gamma_iterator it = gamma.begin(); it != gend; ++it) {
                    unsigned p0B_index = blocks[it->m_key];
                    if (pblocks[p0B_index].size() <= 1 || relevant2.contains(p0B_index)) {
                        continue;
                    }
                    relevant2.insert(p0B_index);
                    block const& p0B = pblocks[p0B_index];
                    uint_set::iterator bi = p0B.begin(), be = p0B.end();

                    block p1;
                    p1.insert(*bi);
                    bool split_found = false;
                    ref_t psi(gamma[*bi], m); 
                    ++bi;
                    for (; bi != be; ++bi) {
                        unsigned q = *bi;
                        ref_t phi(gamma[q], m);
                        if (split_found) {
                            ref_t phi_and_psi(m_ba.mk_and(phi, psi), m);
                            switch (m_ba.is_sat(phi_and_psi)) {
                            case l_true:
                                p1.insert(q);
                                break;
                            case l_undef:
                                return 0;
                            default:
                                break;
                            }                            
                        }
                        else {
                            ref_t psi_min_phi(m_ba.mk_and(psi, m_ba.mk_not(phi)), m);
                            lbool is_sat = m_ba.is_sat(psi_min_phi);
                            if (is_sat == l_undef) {
                                return 0;
                            }
                            if (is_sat == l_true) {
                                psi = psi_min_phi;
                                split_found = true;
                                continue;
                            }
                            // psi is a subset of phi
                            ref_t phi_min_psi(m_ba.mk_and(phi, m_ba.mk_not(psi)), m);
                            is_sat = m_ba.is_sat(phi_min_psi);
                            if (is_sat == l_undef) {
                                return 0;
                            }
                            else if (is_sat == l_false) {
                                p1.insert(q); // psi and phi are equivalent
                            }
                            else {
                                p1.clear();
                                p1.insert(q);
                                psi = phi_min_psi;
                                split_found = true;
                            }
                        }
                    }
                    if (p1.size() < p0B.size() && p0B.size() > 2) iterate = true;
                    add_block(p1, p0B_index, blocks, pblocks, W);
                }
            }
        }
    }

    unsigned new_init = pblocks[blocks[a.init()]].get_representative();

    // set moves
    u2_map<T*> conds;
    svector<unsigned_pair> keys;
    moves_t new_moves;

    for (unsigned i = 0; i < a.num_states(); ++i) {
        unsigned src = pblocks[blocks[i]].get_representative();
        typename automaton_t::moves const& mvs = a.get_moves_from(i);
        for (unsigned j = 0; j < mvs.size(); ++j) {
            unsigned dst = pblocks[blocks[mvs[j].dst()]].get_representative();
            unsigned_pair st(src, dst);
            T* t = 0;
            if (conds.find(st, t)) {
                t = m_ba.mk_or(t, mvs[j].t());
                trail.push_back(t);
                conds.insert(st, t);
            }
            else {
                conds.insert(st, mvs[j].t());
                keys.push_back(st);
            }
        }
    }    
    for (unsigned i = 0; i < keys.size(); ++i) {
        unsigned_pair st = keys[i];
        new_moves.push_back(move_t(m, st.first, st.second, conds[st]));
    }
    // set final states.
    unsigned_vector new_final;
    uint_set new_final_set;
    for (unsigned i = 0; i < a.final_states().size(); ++i) {
        unsigned f = pblocks[blocks[a.final_states()[i]]].get_representative();
        if (!new_final_set.contains(f)) {
            new_final_set.insert(f);
            new_final.push_back(f);
        }
    }

    return alloc(automaton_t, m, new_init, new_final, new_moves);
}

template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_product(automaton_t& a, automaton_t& b) {
    u2_map<unsigned> pair2id;
    unsigned_pair init_pair(a.init(), b.init());
    svector<unsigned_pair> todo;
    todo.push_back(init_pair);
    pair2id.insert(init_pair, 0);
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
        unsigned src = pair2id[curr_pair];
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
                if (!pair2id.find(tgt_pair, tgt)) {
                    tgt = n++;
                    pair2id.insert(tgt_pair, tgt);
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

#if 0
template<class T, class M>
unsigned symbolic_automata<T, M>::get_product_state_id(u2_map<unsigned>& pair2id, unsigned_pair const& p, unsigned& id) {
    unsigned result = 0;
    if (!pair2id.find(p, result)) {
        result = id++;
        pair2id.insert(p, result);
    }
    return result;
}
#endif

template<class T, class M>
typename symbolic_automata<T, M>::automaton_t* symbolic_automata<T, M>::mk_difference(automaton_t& a, automaton_t& b) {
#if 0
    map<uint_set, unsigned, uint_set_hash, uint_set_eq> bs2id;   // set of b-states to unique id
    vector<uintset> id2bs;                                       // unique id to set of b-states
    u2_map<unsigned> pair2id;                                    // pair of states to new state id
    unsigned sink_state = UINT_MAX;
    uint_set bset;
    moves_t new_moves;                                           // moves in the resulting automaton
    unsigned_vector new_final_states;                            // new final states
    unsigned p_state_id = 0;                                     // next state identifier
    bs2id.insert(uint_set(), sink_state);                        // the sink state has no b-states
    bset.insert(b.init());                                       // the initial state has a single initial b state
    bs2id.insert(bset, 0);                                       // the index to the initial b state is 0
    id2bs.push_back(bset);
    if (!b.is_final_state(b.init()) && a.is_final_state(a.init())) {
        new_final_states.push_back(p_state_id);
    }

    svector<unsigned_pair> todo;
    unsigned_pair state(a.init(), 0);
    todo.push_back(state);
    pair2id.insert(state, p_state_id++);

    // or just make todo a vector whose indices coincide with state_id.
    while (!todo.empty()) {
        state = todo.back();
        unsigned state_id = pair2id[state];
        todo.pop_back();
        mvsA.reset();
        a.get_moves_from(state.first, mvsA, true);
        if (state.second == sink_state) {
            for (unsigned i = 0; i < mvsA.size(); ++i) {
                unsigned_pair dst(mvsA[i].dst(), sink_state);
                bool is_new = !pair2id.contains(dst);
                unsigned dst_id = get_product_state_id(pair2id, dst, p_state_id);
                new_moves.push_back(move_t(m, state_id, dst_id, mvsA[i].t()));
                if (is_new && a.is_final_state(mvsA[i].dst())) {
                    new_final_states.push_back(dst_id);
                    todo.push_back(dst);
                }
            }
        }
        else {
            get_moves_from(b, id2bs[state.second], mvsB);
            generate_min_terms(mvsB, min_terms);
            for (unsigned j = 0; j < min_terms.size(); ++j) {
                for (unsigned i = 0; i < mvsA.size(); ++i) {
                    ref_t cond(m_ba.mk_and(mvsA[i].t(), min_terms[j].second), m);
                    switch (m_ba.is_sat(cond)) {
                    case l_false:
                        break;
                    case l_true:
                        ab_combinations.push_back(ab_comb(i, min_terms[j].first, cond));
                        break;
                    case l_undef:
                        return 0;
                    }
                }
            }

            for (unsigned i = 0; i < ab_combinations.size(); ++i) {
                move_t const& mvA = mvsA[ab_combinations[i].A];
                bset.reset();
                bool is_final = a.is_final_state(mvA.dst());
                for (unsigned j = 0; j < mvsB.size(); ++j) {
                    if (ab_combinations[i].B[j]) {
                        bset.insert(mvsB[j].dst());
                        is_final &= !b.is_final_state(mvsB[j].dst());
                    }
                }
                unsigned new_b;
                if (bset.empty()) {
                    new_b = sink_state;
                }
                else if (!bs2id.find(bset, new_b)) {
                    new_b = id2bs.size();
                    id2bs.push_back(bset);
                    bs2id.insert(bset, new_b);
                }
                unsigned_pair dst(mvA.dst(), new_b);
                bool is_new = !pair2id.contains(dst);
                dst_id = get_product_state_id(pair2id, dst, p_state_id);
                move_t new_move(m, state_id, dst_id, ab_combinations[i].cond);
                new_moves.push_back(new_move);
                if (is_new) {
                    if (is_final) {
                        new_final_states.push_back(dst_id);
                    }
                    todo.push_back(dst);
                }   
            }
        }
    }
    
    
    if (new_final_states.empty()) {
        return alloc(automaton_t, m);
    }

    automaton_t* result = alloc(automaton_t, m, 0, new_final_states, new_moves); 

#if 0
    result->isEpsilonFree = true;
    if (A.IsDeterministic)
        result->isDeterministic = true;    
    result->EliminateDeadStates();
#endif
    return result;

#endif
    return 0;
}

#endif 
