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
    map<unsigned_pair, T*, pair_hash<unsigned_hash, unsigned_hash>, default_eq<unsigned_pair> > conds;
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
    if (false) {
        mk_minimize(a);
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
