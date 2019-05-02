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


#include "util/util.h"
#include "util/vector.h"
#include "util/uint_set.h"
#include "util/trace.h"

template<class T>
class default_value_manager {
public:
    void inc_ref(T* t) {}
    void dec_ref(T* t) {}
};

template<class T, class M = default_value_manager<T> >
class automaton {
public:
    class move {
        M&       m;
        T*       m_t;
        unsigned m_src;
        unsigned m_dst;        
    public:
        move(M& m, unsigned s, unsigned d, T* t = nullptr): m(m), m_t(t), m_src(s), m_dst(d) {
            if (t) m.inc_ref(t);
        }
        ~move() {
            if (m_t) m.dec_ref(m_t);
        }

        move(move const& other): m(other.m), m_t(other.m_t), m_src(other.m_src), m_dst(other.m_dst) {
            if (m_t) m.inc_ref(m_t);
        }

        move& operator=(move const& other) {
            SASSERT(&m == &other.m);
            T* t = other.m_t;
            if (t) m.inc_ref(t);
            if (m_t) m.dec_ref(m_t);
            m_t = t;
            m_src = other.m_src;
            m_dst = other.m_dst;
            return *this;
        }

        unsigned dst() const { return m_dst; }
        unsigned src() const { return m_src; }
        T* t() const { return m_t; }

        bool is_epsilon() const { return m_t == nullptr; }
    };
    typedef vector<move> moves;
private:
    M&              m;
    vector<moves>   m_delta;
    vector<moves>   m_delta_inv;
    unsigned        m_init;
    uint_set        m_final_set;
    unsigned_vector m_final_states;
    

    // local data-structures
    mutable uint_set        m_visited;
    mutable unsigned_vector m_todo;

    struct default_display {
        std::ostream& display(std::ostream& out, T* t) {
            return out << t;
        }
    };

public:

    // The empty automaton:
    automaton(M& m):
        m(m), 
        m_init(0)
    {
        m_delta.push_back(moves());
        m_delta_inv.push_back(moves());
    }


    // create an automaton from initial state, final states, and moves
    automaton(M& m, unsigned init, unsigned_vector const& final, moves const& mvs): m(m) {
        m_init = init;
        m_delta.push_back(moves());
        m_delta_inv.push_back(moves());
        for (unsigned f : final) {
            add_to_final_states(f);
        }
        for (move const& mv : mvs) {
            unsigned n = std::max(mv.src(), mv.dst());
            if (n >= m_delta.size()) {
                m_delta.resize(n+1, moves());
                m_delta_inv.resize(n+1, moves());
            }
            add(mv);
        }
    }

    // create an automaton that accepts a sequence.
    automaton(M& m, ptr_vector<T> const& seq):
        m(m),
        m_init(0) {
        m_delta.resize(seq.size()+1, moves());
        m_delta_inv.resize(seq.size()+1, moves());
        for (unsigned i = 0; i < seq.size(); ++i) {
            m_delta[i].push_back(move(m, i, i + 1, seq[i]));
            m_delta[i + 1].push_back(move(m, i, i + 1, seq[i]));
        }
        add_to_final_states(seq.size());
    }

    // The automaton that accepts t
    automaton(M& m, T* t):
        m(m), 
        m_init(0) {
        m_delta.resize(2, moves());
        m_delta_inv.resize(2, moves());
        add_to_final_states(1);
        add(move(m, 0, 1, t));
    }    

    automaton(automaton const& other):
        m(other.m), 
        m_delta(other.m_delta),
        m_delta_inv(other.m_delta_inv),        
        m_init(other.m_init),
        m_final_set(other.m_final_set),
        m_final_states(other.m_final_states)
    {}

    // create the automaton that accepts the empty string/sequence only.
    static automaton* mk_epsilon(M& m) {
        moves mvs;
        unsigned_vector final;
        final.push_back(0);        
        return alloc(automaton, m, 0, final, mvs);
    }

    // create the automaton with a single state on condition t.
    static automaton* mk_loop(M& m, T* t) {
        moves mvs;
        unsigned_vector final;
        final.push_back(0);       
        mvs.push_back(move(m, 0, 0, t));
        return alloc(automaton, m, 0, final, mvs);
    }

    static automaton* clone(automaton const& a) {
        moves mvs;
        unsigned_vector final;
        append_moves(0, a, mvs);
        append_final(0, a, final);
        return alloc(automaton, a.m, a.init(), final, mvs);
    }

    automaton* clone() const {
        return clone(*this);
    }

    // create the sum of disjoint automata
    static automaton* mk_union(automaton const& a, automaton const& b) {
        SASSERT(&a.m == &b.m);
        M& m = a.m;
        if (a.is_empty()) {
            return b.clone();
        }
        if (b.is_empty()) {
            return a.clone();
        }
        moves mvs;
        unsigned_vector final;
        unsigned offset1 = 1;
        unsigned offset2 = a.num_states() + 1;
        mvs.push_back(move(m, 0, a.init() + offset1));
        mvs.push_back(move(m, 0, b.init() + offset2));
        append_moves(offset1, a, mvs);
        append_moves(offset2, b, mvs);
        append_final(offset1, a, final);
        append_final(offset2, b, final);
        return alloc(automaton, m, 0, final, mvs);
    }

    static automaton* mk_opt(automaton const& a) {       
        M& m = a.m;
        moves mvs;
        unsigned_vector final;
        unsigned offset = 0;
        unsigned init = a.init();
        if (!a.initial_state_is_source()) {
            offset = 1;
            init = 0;
            mvs.push_back(move(m, 0, a.init() + offset));
        }
        if (a.is_empty()) {
            return a.clone();
        }

        mvs.push_back(move(m, init, a.final_state() + offset));
        append_moves(offset, a, mvs);
        append_final(offset, a, final);
        return alloc(automaton, m, init, final, mvs);        
    }

    // concatenate accepting languages
    static automaton* mk_concat(automaton const& a, automaton const& b) {
        SASSERT(&a.m == &b.m);
        M& m = a.m;
        if (a.is_empty()) {
            return a.clone();
        }
        if (b.is_empty()) {
            return b.clone();
        }
        if (a.is_epsilon()) {
            return b.clone();
        }
        if (b.is_epsilon()) {
            return a.clone();
        }

        moves mvs;
        unsigned_vector final;
        unsigned init = 0;
        unsigned offset1 = 1;
        unsigned offset2 = a.num_states() + offset1;
        mvs.push_back(move(m, 0, a.init() + offset1));
        append_moves(offset1, a, mvs);
        for (unsigned i = 0; i < a.m_final_states.size(); ++i) {
            mvs.push_back(move(m, a.m_final_states[i] + offset1, b.init() + offset2));
        }
        append_moves(offset2, b, mvs);
        append_final(offset2, b, final);
        
        return alloc(automaton, m, init, final, mvs);
    }

    static automaton* mk_reverse(automaton const& a) {
        M& m = a.m;
        if (a.is_empty()) {
            return alloc(automaton, m);
        }
        moves mvs;
        for (unsigned i = 0; i < a.m_delta.size(); ++i) {
            moves const& mvs1 = a.m_delta[i];
            for (unsigned j = 0; j < mvs1.size(); ++j) {
                move const& mv = mvs1[j];
                mvs.push_back(move(m, mv.dst(), mv.src(), mv.t()));
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
            for (unsigned st : a.m_final_states) {
                mvs.push_back(move(m, init, st));
            }
        }
        return alloc(automaton, m, init, final, mvs);        
    }

    void add_to_final_states(unsigned s) {
        if (!is_final_state(s)) {
            m_final_set.insert(s);
            m_final_states.push_back(s);
        }
    }

    void remove_from_final_states(unsigned s) {
        if (is_final_state(s)) {
            m_final_set.remove(s);
            m_final_states.erase(s);
        }
    }

    bool is_sink_state(unsigned s) const {
        if (is_final_state(s)) return false;
        moves mvs;
        get_moves_from(s, mvs);
        for (move const& m : mvs) {
            if (s != m.dst()) return false;
        }
        return true;
    }

    void add_init_to_final_states() {
        add_to_final_states(init());
    }

    void add_final_to_init_moves() {
        for (unsigned i = 0; i < m_final_states.size(); ++i) {
            unsigned state = m_final_states[i];
            bool found = false;
            moves const& mvs = m_delta[state];
            for (unsigned j = 0; found && j < mvs.size(); ++j) {
                found = (mvs[j].dst() == m_init) && mvs[j].is_epsilon();
            }
            if (!found && state != m_init) {
                add(move(m, state, m_init));
            }
        }
    }

    // remove epsilon transitions
    // src - e -> dst
    // in_degree(src) = 1, final(src) => final(dst), src0 != src
    //    src0 - t -> src - e -> dst => src0 - t -> dst
    // out_degree(dst) = 1, final(dst) => final(src), dst != dst1
    //    src - e -> dst - t -> dst1 => src - t -> dst1

    // Generalized: 
    // Src - E -> dst - t -> dst1 => Src - t -> dst1   if dst is final => each Src is final
    //
    // src - e -> dst - ET -> Dst1 => src - ET -> Dst1  if in_degree(dst) = 1, src != dst
    // Src - E -> dst - et -> dst1 => Src - et -> dst1  if out_degree(dst) = 1, src != dst
    // 
    // Some missing: 
    //  src - et -> dst - E -> Dst1 => src - et -> Dst1   if in_degree(dst) = 1
    //  Src - ET -> dst - e -> dst1 => Src - ET -> dst1  if out_degree(dst) = 1, 
    //
    void compress() {
        SASSERT(!m_delta.empty());
        TRACE("seq", display(tout););
        for (unsigned i = 0; i < m_delta.size(); ++i) {
            for (unsigned j = 0; j < m_delta[i].size(); ++j) {
                move const& mv = m_delta[i][j];
                unsigned src = mv.src();
                unsigned dst = mv.dst();
                SASSERT(src == i);
                if (mv.is_epsilon()) {
                    if (src == dst) {
                        // just remove this edge.                        
                    }
                    else if (1 == in_degree(src) && 1 == out_degree(src) && init() != src && (!is_final_state(src) || is_final_state(dst))) {
                        move const& mv0 = m_delta_inv[src][0];
                        unsigned src0 = mv0.src();                        
                        T* t = mv0.t();
                        SASSERT(mv0.dst() == src);
                        if (src0 == src) {
                            continue;
                        }
                        add(move(m, src0, dst, t));
                        remove(src0, src, t);

                    }
                    else if (1 == out_degree(dst) && 1 == in_degree(dst) && init() != dst && (!is_final_state(dst) || is_final_state(src))) {
                        move const& mv1 = m_delta[dst][0];
                        unsigned dst1 = mv1.dst();
                        T* t = mv1.t();
                        SASSERT(mv1.src() == dst);
                        if (dst1 == dst) {
                            continue;
                        }
                        add(move(m, src, dst1, t));
                        remove(dst, dst1, t);
                    }
                    else if (1 == in_degree(dst) && (!is_final_state(dst) || is_final_state(src)) && init() != dst) {
                        moves const& mvs = m_delta[dst];
                        moves mvs1;
                        for (move const& mv : mvs) {
                            mvs1.push_back(move(m, src, mv.dst(), mv.t()));
                        }
                        for (move const& mv : mvs1) {
                            remove(dst, mv.dst(), mv.t());
                            add(mv);
                        }
                    }
                    //
                    // Src - E -> dst - et -> dst1 => Src - et -> dst1  if out_degree(dst) = 1, src != dst
                    //
                    else if (1 == out_degree(dst) && all_epsilon_in(dst) && init() != dst && !is_final_state(dst)) {
                        move const& mv = m_delta[dst][0];
                        unsigned dst1 = mv.dst();
                        T* t = mv.t();
                        unsigned_vector src0s;
                        moves const& mvs = m_delta_inv[dst];
                        moves mvs1;
                        for (move const& mv1 : mvs) {
                            SASSERT(mv1.is_epsilon());
                            mvs1.push_back(move(m, mv1.src(), dst1, t));
                        }
                        for (move const& mv1 : mvs1) {
                            remove(mv1.src(), dst, nullptr);
                            add(mv1);
                        }
                        remove(dst, dst1, t);    
                        --j;
                        continue;
                    }
                    //
                    // Src1 - ET -> src - e -> dst => Src1 - ET -> dst  if out_degree(src) = 1, src != init() 
                    //
                    else if (1 == out_degree(src) && init() != src && (!is_final_state(src) || is_final_state(dst))) {
                        moves const& mvs = m_delta_inv[src];
                        moves mvs1;
                        for (move const& mv : mvs) {
                            mvs1.push_back(move(m, mv.src(), dst, mv.t()));
                        }
                        for (move const& mv : mvs1) {
                            remove(mv.src(), src, mv.t());
                            add(mv);
                        }
                    }
                    else if (1 == out_degree(src) && (is_final_state(src) || !is_final_state(dst))) {
                        moves const& mvs = m_delta[dst];
                        moves mvs1;
                        for (move const& mv : mvs) {
                            mvs1.push_back(move(m, src, mv.dst(), mv.t()));
                        }
                        for (move const& mv : mvs1) {
                            add(mv);
                        }
                    }
                    else {
                        TRACE("seq", tout << "epsilon not removed " << out_degree(src) << " " << is_final_state(src) << " " << is_final_state(dst) << "\n";);
                        continue;
                    }                    
                    remove(src, dst, nullptr);
                    --j;
                }
            }
        }
        SASSERT(!m_delta.empty());
        while (true) {
            SASSERT(!m_delta.empty());
            unsigned src = m_delta.size() - 1;            
            if (in_degree(src) == 0 && init() != src) {
                remove_from_final_states(src);
                m_delta.pop_back();
            }
            else {
                break;
            }
        }
        sinkify_dead_states();
        TRACE("seq", display(tout););
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
    unsigned_vector const& final_states() const { return m_final_states; }
    unsigned in_degree(unsigned state) const { return m_delta_inv[state].size(); }
    unsigned out_degree(unsigned state) const { return m_delta[state].size(); }
    move const& get_move_from(unsigned state) const { SASSERT(m_delta[state].size() == 1); return m_delta[state][0]; }
    move const& get_move_to(unsigned state) const { SASSERT(m_delta_inv[state].size() == 1); return m_delta_inv[state][0]; }
    moves const& get_moves_from(unsigned state) const { return m_delta[state]; }
    moves const& get_moves_to(unsigned state) const { return m_delta_inv[state]; }
    bool initial_state_is_source() const { return m_delta_inv[m_init].empty(); }
    bool is_final_state(unsigned s) const { return m_final_set.contains(s); }
    bool is_final_configuration(uint_set s) const {
        for (unsigned i : s) {
            if (is_final_state(i))
                return true;
        }
        return false; 
    }
    bool is_epsilon_free() const {
        for (moves const& mvs : m_delta) {
            for (move const & m : mvs) {
                if (!m.t()) return false;
            }
        }
        return true;
    }

    bool all_epsilon_in(unsigned s) {
        moves const& mvs = m_delta_inv[s];
        for (move const& m : mvs) {
            if (m.t()) return false;
        }
        return true;
    }

    bool is_empty() const { return m_final_states.empty(); }
    bool is_epsilon() const { return m_final_states.size() == 1 && m_final_states.back() == init() && m_delta.empty(); }
    unsigned final_state() const { return m_final_states[0]; }
    bool has_single_final_sink() const { return m_final_states.size() == 1 && m_delta[final_state()].empty(); }
    unsigned num_states() const { return m_delta.size(); }
    bool is_loop_state(unsigned s) const {
        moves mvs;
        get_moves_from(s, mvs);
        for (move const& m : mvs) {
            if (s == m.dst()) return true;
        }
        return false;
    }

    unsigned move_count() const {
        unsigned result = 0;
        for (moves const& mvs : m_delta) result += mvs.size();
        return result;
    }
    void get_epsilon_closure(unsigned state, unsigned_vector& states) {
        get_epsilon_closure(state, m_delta, states);
    }
    void get_inv_epsilon_closure(unsigned state, unsigned_vector& states) {
        get_epsilon_closure(state, m_delta_inv, states);
    }
    void get_moves_from(unsigned state, moves& mvs, bool epsilon_closure = true) const {
        get_moves(state, m_delta, mvs, epsilon_closure);
    }
    void get_moves_from_states(uint_set states, moves& mvs, bool epsilon_closure = true) const {
        for (unsigned i : states) {
            moves curr;
            get_moves(i, m_delta, curr, epsilon_closure);
            mvs.append(curr);
        }
    }
    void get_moves_to(unsigned state, moves& mvs, bool epsilon_closure = true) {
        get_moves(state, m_delta_inv, mvs, epsilon_closure);
    }

    template<class D>
    std::ostream& display(std::ostream& out, D& displayer = D()) const {
        out << "init: " << init() << "\n";
        out << "final: " << m_final_states << "\n";

        for (unsigned i = 0; i < m_delta.size(); ++i) {
            moves const& mvs = m_delta[i];
            for (move const& mv : mvs) {
                out << i << " -> " << mv.dst() << " ";
                if (mv.t()) {
                    out << "if "; 
                    displayer.display(out, mv.t());
                }
                out << "\n";
            }
        }
        return out;
    }
private:

    std::ostream& display(std::ostream& out) const {
        out << "init: " << init() << "\n";
        out << "final: " << m_final_states << "\n";

        for (unsigned i = 0; i < m_delta.size(); ++i) {
            moves const& mvs = m_delta[i];
            for (move const& mv : mvs) {
                out << i << " -> " << mv.dst() << " ";
                if (mv.t()) {
                    out << "if *** "; 
                }
                out << "\n";
            }
        }
        return out;
    }
    void sinkify_dead_states() {
        uint_set dead_states;
        for (unsigned i = 0; i < m_delta.size(); ++i) {
            if (!m_final_states.contains(i)) {
                dead_states.insert(i);
            }
        }
        bool change = true;
        unsigned_vector to_remove;
        while (change) {
            change = false;
            to_remove.reset();
            for (unsigned s : dead_states) {
                moves const& mvs = m_delta[s];
                for (move const& mv : mvs) {
                    if (!dead_states.contains(mv.dst())) {
                        to_remove.push_back(s);
                        break;
                    }
                }
            }
            change = !to_remove.empty();
            for (unsigned s : to_remove) {
                dead_states.remove(s);
            }
            to_remove.reset();
        }
        TRACE("seq", tout << "remove: " << dead_states << "\n"; 
              tout << "final: " << m_final_states << "\n";
              );
        for (unsigned s : dead_states) {
            CTRACE("seq", !m_delta[s].empty(), tout << "live state " << s << "\n";); 
            m_delta[s].reset();
        }
    }

#if 0
    void remove_dead_states() {
        unsigned_vector remap;
        for (unsigned i = 0; i < m_delta.size(); ++i) {
            
        }
    }    
#endif

    void add(move const& mv) {
        if (!is_duplicate_cheap(mv)) {
            m_delta[mv.src()].push_back(mv);
            m_delta_inv[mv.dst()].push_back(mv);
        }
    }

    bool is_duplicate_cheap(move const& mv) const {
        if (m_delta[mv.src()].empty()) return false;
        move const& mv0 = m_delta[mv.src()].back();
        return mv0.src() == mv.src() && mv0.dst() == mv.dst() && mv0.t() == mv.t();
    }


    unsigned find_move(unsigned src, unsigned dst, T* t, moves const& mvs) {
        for (unsigned i = 0; i < mvs.size(); ++i) {
            move const& mv = mvs[i];
            if (mv.src() == src && mv.dst() == dst && t == mv.t()) {
                return i;
            }
        }
        UNREACHABLE();
        return UINT_MAX;
    }

    void remove(unsigned src, unsigned dst, T* t, moves& mvs) {
        remove(find_move(src, dst, t, mvs), mvs);
    }

    void remove(unsigned src, unsigned dst, T* t) {
        remove(src, dst, t, m_delta[src]);
        remove(src, dst, t, m_delta_inv[dst]);
    }

    void remove(unsigned index, moves& mvs) {
        mvs[index] = mvs.back();
        mvs.pop_back();
    }     

    mutable unsigned_vector m_states1, m_states2;
    
    void get_moves(unsigned state, vector<moves> const& delta, moves& mvs, bool epsilon_closure) const {
        m_states1.reset(); 
        m_states2.reset();
        get_epsilon_closure(state, delta, m_states1);
        for (unsigned i = 0; i < m_states1.size(); ++i) {
            state = m_states1[i];
            moves const& mv1 = delta[state];
            for (unsigned j = 0; j < mv1.size(); ++j) {
                move const& mv = mv1[j];
                if (!mv.is_epsilon()) {
                    if (epsilon_closure) {
                        m_states2.reset();
                        get_epsilon_closure(mv.dst(), delta, m_states2);
                        for (unsigned k = 0; k < m_states2.size(); ++k) {
                            mvs.push_back(move(m, state, m_states2[k], mv.t()));                            
                        }
                    }
                    else {
                        mvs.push_back(move(m, state, mv.dst(), mv.t()));
                    }
                }
            }
        }
    }

    void get_epsilon_closure(unsigned state, vector<moves> const& delta, unsigned_vector& states) const {
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
                mvs.push_back(move(a.m, mv.src() + offset, mv.dst() + offset, mv.t()));
            }
        }
    }

    static void append_final(unsigned offset, automaton const& a, unsigned_vector& final) {
        for (unsigned s : a.m_final_states) {
            final.push_back(s+offset);
        }
    }
 
};

typedef automaton<unsigned> uautomaton;


#endif 
