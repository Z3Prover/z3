/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_types.h

Abstract:

    Basic types used in the nonlinear arithmetic satisfiability procedure.

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#pragma once

#include "math/polynomial/polynomial.h"
#include "util/buffer.h"
#include "sat/sat_types.h"
#include "util/z3_exception.h"
#include <vector>
namespace algebraic_numbers {
    class anum;
    class manager;
};

namespace nlsat {
#define NLSAT_VB_LVL 10
    typedef void *                     assumption;
    typedef void *                     assumption_set;
    typedef void *                     internal_assumption;

    typedef sat::bool_var              bool_var;
    typedef sat::bool_var_vector       bool_var_vector;
    const bool_var null_bool_var = sat::null_bool_var;
    typedef sat::literal               literal;
    const literal null_literal = sat::null_literal;
    typedef sat::literal_vector        literal_vector;

    inline literal to_literal(unsigned x) { return sat::to_literal(x); }
    
    typedef polynomial::var            var;
    typedef polynomial::var_vector     var_vector;
    typedef polynomial::manager        pmanager;
    typedef polynomial::polynomial     poly;
    typedef polynomial::monomial       monomial;
    typedef polynomial::numeral        numeral;
    const var null_var = polynomial::null_var;
    
    const var true_bool_var = 0;
    const literal true_literal(true_bool_var, false);
    const literal false_literal(true_bool_var, true);

    typedef polynomial::display_var_proc display_var_proc;

    class atom;
    class ineq_atom; // atoms of the form: p=0, p>0, p<0,  where p is a product of polynomials
    class root_atom; // atoms of the form: x=root[i](p), x<root[i](p), x>root[i](p), where x is a variable and p a polynomial.
    
    class clause; 
    class solver;

    class atom {
    public:
        enum kind { EQ=0, LT, GT, ROOT_EQ=10, ROOT_LT, ROOT_GT, ROOT_LE, ROOT_GE };
        static kind flip(kind k) {
            SASSERT(k == EQ || k == LT || k == GT);
            if (k == LT) return GT;
            if (k == GT) return LT;
            return EQ;
        }
    protected:
        friend class solver;
        friend class simplify;
        kind     m_kind;
        unsigned m_ref_count;
        bool_var m_bool_var;
        var      m_max_var;
    public:
        atom(kind k, var max_var):m_kind(k), m_ref_count(0), m_bool_var(null_bool_var), m_max_var(max_var) {}
        bool is_eq() const { return m_kind == EQ || m_kind == ROOT_EQ; }

        bool is_ineq_atom() const { return m_kind <= GT; }
        bool is_root_atom() const { return m_kind >= ROOT_EQ; }
        kind get_kind() const { return m_kind; }
        bool_var bvar() const { return m_bool_var; }
        var max_var() const { return m_max_var; }
        unsigned ref_count() const { return m_ref_count; }
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; }
    };

    typedef std_vector<atom*> atom_vector;

    class ineq_atom : public atom {
        friend class solver;
        unsigned     m_size;
        poly *       m_ps[0];
        ineq_atom(kind k, unsigned sz, poly * const * ps, bool const * is_even, var max_var);
        static unsigned get_obj_size(unsigned sz) { return sizeof(ineq_atom) + sizeof(poly*)*sz; }
    public:
        unsigned size() const { return m_size; }
        poly * p(unsigned i) const { SASSERT(i < size()); return UNTAG(poly*, m_ps[i]); }
        // Return true if i-th factor has odd degree
        bool is_odd(unsigned i) const { SASSERT(i < size()); return GET_TAG(m_ps[i]) == 0; }
        bool is_even(unsigned i) const { return !is_odd(i); }
        struct khasher { unsigned operator()(ineq_atom const * a) const { return a->m_kind; } };
        struct chasher { unsigned operator()(ineq_atom const * a, unsigned idx) const { return polynomial::manager::id(a->p(idx)); } };
        struct hash_proc { unsigned operator()(ineq_atom const * a) const; };
        struct eq_proc { bool operator()(ineq_atom const * a1, ineq_atom const * a2) const; };
    };

    inline std::ostream& operator<<(std::ostream& out, atom::kind k) {
        switch (k) {
        case atom::EQ: return out << "=";
        case atom::LT: return out << "<";
        case atom::GT: return out << ">";
        case atom::ROOT_EQ: return out << "= root";
        case atom::ROOT_LT: return out << "< root";
        case atom::ROOT_LE: return out << "<= root";
        case atom::ROOT_GT: return out << "> root";
        case atom::ROOT_GE: return out << ">= root";
        default: return out << (int)k;
        }
        return out;
    }

    class root_atom : public atom {
        friend class solver;
        var      m_x;
        unsigned m_i;
        poly *   m_p;
        root_atom(kind k, var x, unsigned i, poly * p);
    public:
        var x() const { return m_x; }
        unsigned i() const { return m_i; }
        poly * p() const { return m_p; }
        struct hash_proc { unsigned operator()(root_atom const * a) const; };
        struct eq_proc { bool operator()(root_atom const * a1, root_atom const * a2) const; };
    };

    /**
       \brief An indexed root expression designates the i-th real root of a (square-free) polynomial p when regarded as
       a univariate over its maximal variable x after substituting the current values for variables < x.

       It is a lightweight value object used by projection / sample-cell algorithms. It does not own the polynomial.
    */
    struct indexed_root {
        poly *   m_p;      // polynomial whose root is referenced (assumed non-null)
        unsigned m_index;  // root index (0-based internally; corresponds to paper's i)
        var      m_var;    // the main variable of m_p when treated as univariate
        indexed_root(): m_p(nullptr), m_index(0), m_var(null_var) {}
        indexed_root(poly* p, unsigned i, var x): m_p(p), m_index(i), m_var(x) {}
        poly * p() const { return m_p; }
        unsigned index() const { return m_index; }
        var x() const { return m_var; }
        bool is_null() const { return m_p == nullptr; }
        // ordering helper (by variable then polynomial id then index) - total but arbitrary
        struct lt {
            pmanager & m_pm;
            lt(pmanager & pm): m_pm(pm) {}
            bool operator()(indexed_root const & a, indexed_root const & b) const {
                if (a.m_var != b.m_var) return a.m_var < b.m_var;
                if (a.m_p != b.m_p) return m_pm.id(a.m_p) < m_pm.id(b.m_p);
                return a.m_index < b.m_index;
            }
        };
        struct hash_proc {
            pmanager & m_pm;
            hash_proc(pmanager & pm): m_pm(pm) {}
            unsigned operator()(indexed_root const & r) const {
                return combine(combine(m_pm.id(r.m_p), r.m_index), r.m_var);
            }
            static unsigned combine(unsigned a, unsigned b) { return a * 1315423911u + b + (a<<5) + (b>>2); }
        };
        struct eq_proc {
            pmanager & m_pm;
            eq_proc(pmanager & pm): m_pm(pm) {}
            bool operator()(indexed_root const & a, indexed_root const & b) const {
                return a.m_var == b.m_var && a.m_index == b.m_index && a.m_p == b.m_p; }
        };
    };

    typedef std::vector<indexed_root> indexed_root_vector;

    inline ineq_atom * to_ineq_atom(atom * a) { SASSERT(a->is_ineq_atom()); return static_cast<ineq_atom*>(a); }
    inline root_atom * to_root_atom(atom * a) { SASSERT(a->is_root_atom()); return static_cast<root_atom*>(a); }
    inline ineq_atom const * to_ineq_atom(atom const * a) { SASSERT(a->is_ineq_atom()); return static_cast<ineq_atom const *>(a); }
    inline root_atom const * to_root_atom(atom const * a) { SASSERT(a->is_root_atom()); return static_cast<root_atom const *>(a); }

    typedef algebraic_numbers::anum    anum;
    typedef algebraic_numbers::manager anum_manager;

    typedef default_exception solver_exception;

    class assignment;
    
    inline int normalize_sign(int s) {
        if (s < 0)  return -1;
        if (s == 0) return 0;
        return 1;
    }
};

