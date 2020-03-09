/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
#include <utility>
#include <string>
#include <algorithm>

#include "util/vector.h"
#include "util/region.h"
#include "math/lp/lp_utils.h"
#include "math/lp/ul_pair.h"
#include "math/lp/lar_term.h"
#include "math/lp/column_namer.h"
#include "math/lp/stacked_value.h"
namespace lp {
inline lconstraint_kind flip_kind(lconstraint_kind t) {
    return static_cast<lconstraint_kind>( - static_cast<int>(t));
}

inline std::string lconstraint_kind_string(lconstraint_kind t) {
    switch (t) {
    case LE: return std::string("<=");
    case LT: return std::string("<");
    case GE: return std::string(">=");
    case GT: return std::string(">");
    case EQ: return std::string("=");
    case NE: return std::string("!=");
    }
    lp_unreachable();
    return std::string(); // it is unreachable
}

class lar_base_constraint {
    lconstraint_kind m_kind;
    mpq              m_right_side;
    bool             m_active;
    unsigned         m_j;
public:

    virtual vector<std::pair<mpq, var_index>> coeffs() const = 0;
    lar_base_constraint(unsigned j, lconstraint_kind kind, const mpq& right_side) :m_kind(kind), m_right_side(right_side), m_active(false), m_j(j) {}
    virtual ~lar_base_constraint() {}

    lconstraint_kind kind() const { return m_kind; }
    mpq const& rhs() const { return m_right_side; }
    unsigned column() const { return m_j; }

    void activate() { m_active = true; }
    void deactivate() { m_active = false; }
    bool is_active() const { return m_active; }

    virtual unsigned size() const = 0;
    virtual mpq get_free_coeff_of_left_side() const { return zero_of_type<mpq>();}
};

class lar_var_constraint: public lar_base_constraint {
public:
    lar_var_constraint(unsigned j, lconstraint_kind kind, const mpq& right_side) : 
        lar_base_constraint(j, kind, right_side) {}

    vector<std::pair<mpq, var_index>> coeffs() const override {
        vector<std::pair<mpq, var_index>> ret;
        ret.push_back(std::make_pair(one_of_type<mpq>(), column()));
        return ret;
    }
    unsigned size() const override { return 1;}
};


class lar_term_constraint: public lar_base_constraint {
    const lar_term * m_term;
public:
    lar_term_constraint(unsigned j, const lar_term *t, lconstraint_kind kind, const mpq& right_side) : 
        lar_base_constraint(j, kind, right_side), m_term(t) {}

    vector<std::pair<mpq, var_index>> coeffs() const override { return m_term->coeffs_as_vector(); }
    unsigned size() const override { return m_term->size();}
};


class constraint_set {
    region                         m_region;
    column_namer&                  m_namer;
    vector<lar_base_constraint*>   m_constraints;
    stacked_value<unsigned>        m_constraint_count;
    unsigned_vector                m_active;
    stacked_value<unsigned>        m_active_lim;

    constraint_index add(lar_base_constraint* c) {
        constraint_index ci = m_constraints.size();
        m_constraints.push_back(c);
        return ci;
    }

    std::ostream& print_left_side_of_constraint(const lar_base_constraint & c, std::ostream & out) const {
        m_namer.print_linear_combination_of_column_indices(c.coeffs(), out);
        mpq free_coeff = c.get_free_coeff_of_left_side();
        if (!is_zero(free_coeff))
            out << " + " << free_coeff;
        return out;
    }

    std::ostream& print_left_side_of_constraint_indices_only(const lar_base_constraint & c, std::ostream & out) const {
        print_linear_combination_of_column_indices_only(c.coeffs(), out);
        mpq free_coeff = c.get_free_coeff_of_left_side();
        if (!is_zero(free_coeff))
            out << " + " << free_coeff;
        return out;
    }

    std::ostream& print_left_side_of_constraint(const lar_base_constraint & c, std::function<std::string (unsigned)>& var_str, std::ostream & out) const {
        print_linear_combination_customized(c.coeffs(), var_str, out);
        mpq free_coeff = c.get_free_coeff_of_left_side();
        if (!is_zero(free_coeff))
            out << " + " << free_coeff;
        return out;
    }

    std::ostream& out_of_bounds(std::ostream& out, constraint_index ci) const {
        return out << "constraint " << T_to_string(ci) << " is not found" << std::endl;
    }

public:
    constraint_set(column_namer& cn): 
        m_namer(cn) {}

    ~constraint_set() {
        for (auto* c : m_constraints) 
            c->~lar_base_constraint();
    }

    void push() {
        m_constraint_count = m_constraints.size();
        m_constraint_count.push();
        m_region.push_scope();
#if 1
        m_active_lim = m_active.size();
        m_active_lim.push();
#endif
    }

    void pop(unsigned k) {
#if 1
        m_active_lim.pop(k);
        for (unsigned i = m_active.size(); i-- > m_active_lim; ) {
            m_constraints[m_active[i]]->deactivate();
        }
        m_active.shrink(m_active_lim);
#endif
        m_constraint_count.pop(k);        
        for (unsigned i = m_constraints.size(); i-- > m_constraint_count; )
            m_constraints[i]->~lar_base_constraint();        
        m_constraints.shrink(m_constraint_count);

        m_region.pop_scope(k);
    }

    constraint_index add_var_constraint(var_index j, lconstraint_kind k, mpq const& rhs) {
        return add(new (m_region) lar_var_constraint(j, k, rhs));
    }

    constraint_index add_term_constraint(unsigned j, const lar_term* t, lconstraint_kind k, mpq const& rhs) {
        return add(new (m_region) lar_term_constraint(j, t, k, rhs));
    }

#if 0
    bool is_active(constraint_index ci) const { return true; }

    void activate(constraint_index ci) {}

#else
    // future behavior uses activation bit.
    bool is_active(constraint_index ci) const { return m_constraints[ci]->is_active(); }

    void activate(constraint_index ci) { auto& c = *m_constraints[ci]; if (!c.is_active()) { c.activate(); m_active.push_back(ci); } }
#endif

    lar_base_constraint const& operator[](constraint_index ci) const { return *m_constraints[ci]; }    

    bool valid_index(constraint_index ci) const { return ci < m_constraints.size(); }

    class active_constraints {
        friend class constraint_set;
        constraint_set const& cs;
    public:
        active_constraints(constraint_set const& cs): cs(cs) {}
        class iterator {
            friend class constraint_set;
            constraint_set const& cs;
            unsigned m_index;
            iterator(constraint_set const& cs, unsigned idx): cs(cs), m_index(idx) { forward(); }
            void next() { ++m_index; forward(); }
            void forward() { for (; m_index < cs.m_constraints.size() && !cs.is_active(m_index); m_index++) ; }
        public:
            lar_base_constraint const& operator*() { return cs[m_index]; }
            lar_base_constraint const* operator->() const { return &cs[m_index]; }
            iterator& operator++() { next(); return *this; }
            iterator operator++(int) { auto tmp = *this; next(); return tmp; }
            bool operator==(iterator const& other) const { return m_index == other.m_index; }
            bool operator!=(iterator const& other) const { return m_index != other.m_index; }
        };
        iterator begin() const { return iterator(cs, 0); }
        iterator end() const { return iterator(cs, cs.m_constraints.size()); }
    };

    active_constraints active() const { return active_constraints(*this); }

    class active_indices {
        friend class constraint_set;
        constraint_set const& cs;
    public:
        active_indices(constraint_set const& cs): cs(cs) {}
        class iterator {
            friend class constraint_set;
            constraint_set const& cs;
            unsigned m_index;
            iterator(constraint_set const& cs, unsigned idx): cs(cs), m_index(idx) { forward(); }
            void next() { ++m_index; forward(); }
            void forward() { for (; m_index < cs.m_constraints.size() && !cs.is_active(m_index); m_index++) ; }
        public:
            constraint_index operator*() { return m_index; }
            constraint_index const* operator->() const { return &m_index; }
            iterator& operator++() { next(); return *this; }
            iterator operator++(int) { auto tmp = *this; next(); return tmp; }
            bool operator==(iterator const& other) const { return m_index == other.m_index; }
            bool operator!=(iterator const& other) const { return m_index != other.m_index; }
        };
        iterator begin() const { return iterator(cs, 0); }
        iterator end() const { return iterator(cs, cs.m_constraints.size()); }
    };

    active_indices indices() const { return active_indices(*this); }
        
    std::ostream& display(std::ostream& out) const {
        out << "number of constraints = " << m_constraints.size() << std::endl;
        for (auto const& c : active()) {
            display(out, c);
        }
        return out;
    }

    std::ostream& display(std::ostream& out, constraint_index ci) const {
        return (ci >= m_constraints.size()) ? out_of_bounds(out, ci) : display(out, (*this)[ci]);
    }

    std::ostream& display(std::ostream& out, lar_base_constraint const& c) const {
        print_left_side_of_constraint(c, out);
        return out << " " << lconstraint_kind_string(c.kind()) << " " << c.rhs() << std::endl;
    }

    std::ostream& display_indices_only(std::ostream& out, constraint_index ci) const {
        return (ci >= m_constraints.size()) ? out_of_bounds(out, ci) : display_indices_only(out, (*this)[ci]);
    }

    std::ostream& display_indices_only(std::ostream& out, lar_base_constraint const& c) const {
        print_left_side_of_constraint_indices_only(c, out);
        return out << " " << lconstraint_kind_string(c.kind()) << " " << c.rhs() << std::endl;
    }

    std::ostream& display(std::ostream& out, std::function<std::string (unsigned)> var_str, constraint_index ci) const {
        return (ci >= m_constraints.size()) ? out_of_bounds(out, ci) : display(out, var_str, (*this)[ci]);
    }

    std::ostream& display(std::ostream& out, std::function<std::string (unsigned)>& var_str, lar_base_constraint const& c) const {
        print_left_side_of_constraint(c, var_str, out); 
        return out << " " << lconstraint_kind_string(c.kind()) << " " << c.rhs() << std::endl;
    }

    
    
};

inline std::ostream& operator<<(std::ostream& out, constraint_set const& cs) { 
    return cs.display(out); 
}

}
