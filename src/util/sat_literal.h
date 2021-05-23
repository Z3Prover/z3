/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_literal.h

Abstract:

    Literal datatype

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

--*/
#pragma once

#include "util/lbool.h"
#include "util/approx_set.h"
#include "util/vector.h"
#include "util/uint_set.h"

namespace sat {

    /**
       \brief A boolean variable is just an integer.
    */
    typedef unsigned bool_var;

    typedef svector<bool_var> bool_var_vector;

    const bool_var null_bool_var  = UINT_MAX >> 1;

    /**
       \brief The literal b is represented by the value 2*b, and
       the literal (not b) by the value 2*b + 1
    */
    class literal {
        unsigned  m_val;
    public:
        literal():m_val(null_bool_var << 1) {
            SASSERT(var() == null_bool_var && !sign());
        }

        explicit literal(bool_var v, bool _sign = false):
            m_val((v << 1) + static_cast<unsigned>(_sign)) {
            SASSERT(var() == v);
            SASSERT(sign() == _sign);
        }

        bool_var var() const {
            return m_val >> 1;
        }

        bool sign() const {
            return m_val & 1ul;
        }

        literal unsign() const {
            literal l;
            l.m_val = m_val & ~1;
            return l;
        }

        unsigned index() const {
            return m_val;
        }

        void neg() {
            m_val = m_val ^ 1;
        }

        friend literal operator~(literal l) {
            l.m_val = l.m_val ^1;
            return l;
        }

        unsigned to_uint() const { return m_val; }

        unsigned hash() const { return to_uint(); }

        friend literal to_literal(unsigned x);
        friend bool operator<(literal const & l1, literal const & l2);
        friend bool operator==(literal const & l1, literal const & l2);
        friend bool operator!=(literal const & l1, literal const & l2);
    };

    const literal null_literal;
    using literal_hash = obj_hash<literal>;

    inline literal to_literal(unsigned x) { literal l; l.m_val = x; return l; }
    inline bool operator<(literal const & l1, literal const & l2) { return l1.m_val < l2.m_val;  }
    inline bool operator==(literal const & l1, literal const & l2) { return l1.m_val == l2.m_val; }
    inline bool operator!=(literal const & l1, literal const & l2) { return l1.m_val != l2.m_val; }

    inline std::ostream & operator<<(std::ostream & out, sat::literal l) { if (l == sat::null_literal) out << "null"; else out << (l.sign() ? "-" : "") << l.var(); return out; }


    typedef svector<literal> literal_vector;
    typedef std::pair<literal, literal> literal_pair;

    struct literal2unsigned { unsigned operator()(literal l) const { return l.to_uint(); } };

    typedef approx_set_tpl<literal, literal2unsigned, unsigned> literal_approx_set;

    typedef approx_set_tpl<bool_var, u2u, unsigned> var_approx_set;


    inline void negate(literal_vector& ls) { for (unsigned i = 0; i < ls.size(); ++i) ls[i].neg(); }

    typedef tracked_uint_set uint_set;

    typedef uint_set bool_var_set;

    class literal_set {
        uint_set m_set;
    public:
        literal_set(literal_vector const& v) {
            for (unsigned i = 0; i < v.size(); ++i) insert(v[i]);
        }
        literal_set() {}
        literal_vector to_vector() const {
            literal_vector result;
            for (literal lit : *this) result.push_back(lit);
            return result;
        }
        literal_set& operator=(literal_vector const& v) {
            reset();
            for (unsigned i = 0; i < v.size(); ++i) insert(v[i]);
            return *this;
        }

        void insert(literal l) { m_set.insert(l.index()); }
        void remove(literal l) { m_set.remove(l.index()); }
        literal pop() { return to_literal(m_set.erase()); }
        bool contains(literal l) const { return m_set.contains(l.index()); }
        bool empty() const { return m_set.empty(); }
        unsigned size() const { return m_set.size(); }
        void reset() { m_set.reset(); }
        void finalize() { m_set.finalize(); }
        class iterator {
            uint_set::iterator m_it;
        public:
            iterator(uint_set::iterator it):m_it(it) {}
            literal operator*() const { return to_literal(*m_it); }
            iterator& operator++() { ++m_it; return *this; }
            iterator operator++(int) { iterator tmp = *this; ++m_it; return tmp; }
            bool operator==(iterator const& it) const { return m_it == it.m_it; }
            bool operator!=(iterator const& it) const { return m_it != it.m_it; }
        };
        iterator begin() const { return iterator(m_set.begin()); }
        iterator end() const { return iterator(m_set.end()); }
        literal_set& operator&=(literal_set const& other) {
            m_set &= other.m_set;
            return *this;
        }
        literal_set& operator|=(literal_set const& other) {
            m_set |= other.m_set;
            return *this;
        }
    };

    struct dimacs_lit {
        literal m_lit;
        explicit dimacs_lit(literal l):m_lit(l) {}
    };

    inline std::ostream & operator<<(std::ostream & out, dimacs_lit const & dl) {
        literal l = dl.m_lit;
        if (l.sign()) out << "-" << (l.var() + 1);
        else out << (l.var() + 1);
        return out;
    }

    struct mk_lits_pp {
        unsigned        m_num;
        literal const * m_lits;
        mk_lits_pp(unsigned num, literal const * ls):m_num(num), m_lits(ls) {}
    };

    inline std::ostream & operator<<(std::ostream & out, mk_lits_pp const & ls) {
        for (unsigned i = 0; i < ls.m_num; i++) {
            if (i > 0) out << " ";
            out << ls.m_lits[i];
        }
        return out;
    }

    inline std::ostream & operator<<(std::ostream & out, literal_vector const & ls) {
        return out << mk_lits_pp(ls.size(), ls.data());
    }

};
