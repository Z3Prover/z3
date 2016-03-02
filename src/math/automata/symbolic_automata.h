/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    symbolic_automata.h

Abstract:

    Symbolic Automata over Boolean Algebras, a la Margus Veanes Automata library.

Author:

    Nikolaj Bjorner (nbjorner) 2016-02-27.

Revision History:


--*/

#ifndef SYMBOLIC_AUTOMATA_H_
#define SYMBOLIC_AUTOMATA_H_


#include "automaton.h"
#include "boolean_algebra.h"


template<class T, class M = default_value_manager<T> >
class symbolic_automata {
    typedef automaton<T, M>    automaton_t;
    typedef boolean_algebra<T*> ba_t;
    typedef typename automaton_t::move  move_t;
    typedef vector<move_t>     moves_t;
    typedef obj_ref<T, M>      ref_t;
    typedef ref_vector<T, M>   refs_t;
    typedef std::pair<unsigned, unsigned> unsigned_pair;
    template<class V> class u2_map : public map<unsigned_pair, V, pair_hash<unsigned_hash, unsigned_hash>, default_eq<unsigned_pair> > {};


    M&    m;
    ba_t& m_ba;


    class block {
        uint_set m_set;
        unsigned m_rep;
        bool     m_rep_chosen;
    public:

        block(): m_rep(0), m_rep_chosen(false) {}

        block(uint_set const& s):
            m_set(s),
            m_rep(0),
            m_rep_chosen(false) {
        }

        block(unsigned_vector const& vs) {
            for (unsigned i = 0; i < vs.size(); ++i) {
                m_set.insert(vs[i]);               
            }
            m_rep_chosen = false;
            m_rep = 0;
        }

        block& operator=(block const& b) {
            m_set = b.m_set;
            m_rep = 0;
            m_rep_chosen = false;
            return *this;
        }

        unsigned get_representative() {
            if (!m_rep_chosen) {
                uint_set::iterator it = m_set.begin();
                if (m_set.end() != it) {
                    m_rep = *it;                    
                }
                m_rep_chosen = true;
            }
            return m_rep;
        }

        void insert(unsigned i) { m_set.insert(i); }
        bool contains(unsigned i) const { return m_set.contains(i); }        
        bool is_empty() const { return m_set.empty(); }
        unsigned size() const { return m_set.num_elems(); }
        void remove(unsigned i) { m_set.remove(i); m_rep_chosen = false; }        
        void clear() { m_set.reset(); m_rep_chosen = false; }
        uint_set::iterator begin() const { return m_set.begin(); }
        uint_set::iterator end() const { return m_set.end(); }
    };

    void add_block(block const& p1, unsigned p0_index, unsigned_vector& blocks, vector<block>& pblocks, unsigned_vector& W);

public:
    symbolic_automata(M& m, ba_t& ba): m(m), m_ba(ba) {}
    automaton_t* mk_determinstic(automaton_t& a);
    automaton_t* mk_complement(automaton_t& a);
    automaton_t* remove_epsilons(automaton_t& a);
    automaton_t* mk_total(automaton_t& a);
    automaton_t* mk_minimize(automaton_t& a);
    automaton_t* mk_minimize_total(automaton_t& a);
    automaton_t* mk_difference(automaton_t& a, automaton_t& b);
    automaton_t* mk_product(automaton_t& a, automaton_t& b);
};



#endif 
