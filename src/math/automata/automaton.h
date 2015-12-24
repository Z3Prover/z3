/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    automaton.h

Abstract:

    Symbolic Automaton, a la Margus Veanes Automata library.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-23.

Revision History:


--*/

#ifndef AUTOMATON_H_
#define AUTOMATON_H_


#include "util.h"
#include "vector.h"
#include "uint_set.h"

template<class T>
class automaton {
    class move {
        T*       m_t;
        unsigned m_src;
        unsigned m_dst;        
    public:
        move(unsigned s, unsigned d, T* t = 0): m_t(t), m_src(s), m_dst(d) {}

        unsigned dst() const { return m_dst; }
        unsigned src() const { return m_src; }
        T* t() const { return m_t; }

        bool is_epsilon() const { return m_t == 0; }
    };
    typedef svector<move> moves;


    svector<moves>  m_delta;
    svector<moves>  m_delta_inv;
    unsigned        m_init;
    uint_set        m_final_set;
    unsigned_vector m_final_states;
    bool            m_is_epsilon_free;
    bool            m_is_deterministic;
    

    // local data-structures
    mutable uint_set        m_visited;
    mutable unsigned_vector m_todo;


public:

    // The empty automaton:
    automaton():
        m_init(0),
        m_is_epsilon_free(true),
        m_is_deterministic(true)
    {
        m_delta.push_back(moves());
        m_delta_inv.push_back(moves());
    }


    // create an automaton from initial state, final states, and moves
    automaton(unsigned init, unsigned_vector const& final, moves const& mvs) {
        m_is_epsilon_free = true;
        m_is_deterministic = true;
        m_init = init;
        for (unsigned i = 0; i < final.size(); ++i) {
            m_final_states.push_back(final[i]);
            m_final_set.insert(final[i]);
        }
        for (unsigned i = 0; i < mvs.size(); ++i) {
            move const& mv = mvs[i];
            unsigned n = std::max(mv.src(), mv.dst());
            if (n >= m_delta.size()) {
                m_delta.resize(n+1, moves());
                m_delta_inv.resize(n+1, moves());
            }
            m_delta[mv.src()].push_back(mv);
            m_delta_inv[mv.dst()].push_back(mv);
            m_is_deterministic &= m_delta[mv.src()].size() < 2;
            m_is_epsilon_free &= !mv.is_epsilon();
        }
    }

    // create an automaton that accepts a sequence.
    automaton(ptr_vector<T> const& seq):
        m_init(0),
        m_is_epsilon_free(true), 
        m_is_deterministic(true) {
        m_delta.resize(seq.size()+1, moves());
        m_delta_inv.resize(seq.size()+1, moves());
        for (unsigned i = 0; i < seq.size(); ++i) {
            m_delta[i].push_back(move(i, i + 1, seq[i]));
            m_delta[i + 1].push_back(move(i, i + 1, seq[i]));
        }
        m_final_states.push_back(seq.size());
        m_final_set.insert(seq.size());        
    }

    // The automaton with a single state that is also final.
    automaton(T* t):
        m_init(0) {
        unsigned s = 0;
        m_delta.resize(s+1, moves());
        m_delta_inv.resize(s+1, moves());
        m_final_set.insert(s);
        m_final_states.push_back(s);
        m_delta[s].push_back(move(s, s, t));
        m_delta_inv[s].push_back(move(s, s, t));
    }    

    automaton(automaton const& other):
        m_delta(other.m_delta),
        m_delta_inv(other.m_delta_inv),        
        m_init(other.m_init),
        m_final_set(other.m_final_set),
        m_final_states(other.m_final_states),
        m_is_epsilon_free(other.m_is_epsilon_free),
        m_is_deterministic(other.m_is_deterministic)
    {}

    // create the automaton that accepts the empty string only.
    static automaton mk_epsilon() {
        moves mvs;
        unsigned_vector final;
        final.push_back(0);        
        return automaton(0, final, mvs);
    }

    // create the automaton with a single state on condition t.
    static automaton mk_loop(T* t) {
        moves mvs;
        unsigned_vector final;
        final.push_back(0);       
        mvs.push_back(move(0, 0, t));
        return automaton(0, final, mvs);
    }

    // create the sum of disjoint automata
    static automaton mk_union(automaton const& a, automaton const& b) {
        moves mvs;
        unsigned_vector final;
        unsigned offset1 = 1;
        unsigned offset2 = a.num_states() + 1;
        mvs.push_back(move(0, a.init() + offset1, 0));
        mvs.push_back(move(0, b.init() + offset2, 0));
        append_moves(offset1, a, mvs);
        append_moves(offset2, b, mvs);
        append_final(offset1, a, final);
        append_final(offset2, b, final);
        return automaton(0, final, mvs);
    }

    static automaton mk_reverse(automaton const& a) {
        if (a.is_empty()) {
            return automaton();
        }
        moves mvs;
        for (unsigned i = 0; i < a.m_delta.size(); ++i) {
            moves const& mvs1 = a.m_delta[i];
            for (unsigned j = 0; j < mvs1.size(); ++j) {
                move const& mv = mvs1[j];
                mvs.push_back(move(mv.dst(), mv.src(), mv.t()));
            }
        }
        unsigned_vector final;
        unsigned init;
        final.push_back(a.init());
        if (a.m_final_states.size() == 1) {
            init = a.m_final_states[0];
        }
        else {
            init = a.num_states();
            for (unsigned i = 0; i < a.m_final_states.size(); ++i) {
                mvs.push_back(move(init, a.m_final_states[i]));
            }
        }
        return automaton(init, final, mvs);        
    }
    
    bool is_sequence(unsigned& length) const {
        if (is_final_state(m_init) && (out_degree(m_init) == 0 || (out_degree(m_init) == 1 && is_loop_state(m_init)))) {
            length = 0;
            return true;
        }
        if (is_empty() || in_degree(m_init) != 0 || out_degree(m_init) != 1) {
            return false;
        }
        
        length = 1;
        unsigned s = get_move_from(m_init).dst();
        while (!is_final_state(s)) {  
            if (out_degree(s) != 1 || in_degree(s) != 1) {
                return false;
            }
            s = get_move_from(s).dst();
            ++length;
        }
        return out_degree(s) == 0 || (out_degree(s) == 1 && is_loop_state(s));
    }

    unsigned init() const { return m_init; }
    unsigned in_degree(unsigned state) const { return m_delta_inv[state].size(); }
    unsigned out_degree(unsigned state) const { return m_delta[state].size(); }
    move const& get_move_from(unsigned state) const { SASSERT(m_delta[state].size() == 1); return m_delta[state][0]; }
    move const& get_move_to(unsigned state) const { SASSERT(m_delta_inv[state].size() == 1); return m_delta_inv[state][0]; }
    moves const& get_moves_from(unsigned state) const { return m_delta[state]; }
    moves const& get_moves_to(unsigned state) const { return m_delta_inv[state]; }
    bool initial_state_is_source() const { return m_delta_inv[m_init].empty(); }
    bool is_final_state(unsigned s) const { return m_final_set.contains(s); }
    bool is_epsilon_free() const { return m_is_epsilon_free; }
    bool is_deterministic() const { return m_is_deterministic; }
    bool is_empty() const { return m_final_states.empty(); }
    unsigned final_state() const { return m_final_states[0]; }
    bool has_single_final_sink() const { return m_final_states.size() == 1 && m_delta[final_state()].empty(); }
    unsigned num_states() const { return m_delta.size(); }
    bool is_loop_state(unsigned s) const {
        moves mvs;
        get_moves_from(s, mvs);
        for (unsigned i = 0; i < mvs.size(); ++i) {
            if (s == mvs[i].dst()) return true;
        }
        return false;
    }

    unsigned move_count() const {
        unsigned result = 0;
        for (unsigned i = 0; i < m_delta.size(); result += m_delta[i].size(), ++i) {}
        return result;
    }
    void get_epsilon_closure(unsigned state, unsigned_vector& states) {
        get_epsilon_closure(state, m_delta, states);
    }
    void get_inv_epsilon_closure(unsigned state, unsigned_vector& states) {
        get_epsilon_closure(state, m_delta_inv, states);
    }
    void get_moves_from(unsigned state, moves& mvs) const {
        get_moves(state, m_delta, mvs);
    }
    void get_moves_to(unsigned state, moves& mvs) {
        get_moves(state, m_delta_inv, mvs);
    }
private:
    void get_moves(unsigned state, svector<moves> const& delta, moves& mvs) const {
        unsigned_vector states;
        get_epsilon_closure(state, delta, states);
        for (unsigned i = 0; i < states.size(); ++i) {
            state = states[i];
            moves const& mv1 = delta[state];
            for (unsigned j = 0; j < mv1.size(); ++j) {
                if (!mv1[j].is_epsilon()) {
                    mvs.push_back(mv1[j]);
                }
            }
        }
    }

    void get_epsilon_closure(unsigned state, svector<moves> const& delta, unsigned_vector& states) const {
        m_todo.push_back(state);
        m_visited.insert(state);
        while (!m_todo.empty()) {
            state = m_todo.back();
            states.push_back(state);
            m_todo.pop_back();
            moves const& mvs = delta[state];
            for (unsigned i = 0; i < mvs.size(); ++i) {
                unsigned tgt = mvs[i].dst();
                if (mvs[i].is_epsilon() && !m_visited.contains(tgt)) {
                    m_visited.insert(tgt);
                    m_todo.push_back(tgt);
                }
            }
        }
        m_visited.reset();
        SASSERT(m_todo.empty());   
    }

    static void append_moves(unsigned offset, automaton const& a, moves& mvs) {
        for (unsigned i = 0; i < a.num_states(); ++i) {
            moves const& mvs1 = a.m_delta[i];
            for (unsigned j = 0; j < mvs1.size(); ++j) {
                move const& mv = mvs1[j];
                mvs.push_back(move(mv.src() + offset, mv.dst() + offset, mv.t()));
            }
        }
    }

    static void append_final(unsigned offset, automaton const& a, unsigned_vector& final) {
        for (unsigned i = 0; i < a.m_final_states.size(); ++i) {
            final.push_back(a.m_final_states[i]+offset);
        }
    }
 
};

typedef automaton<unsigned> uautomaton;


#endif 
