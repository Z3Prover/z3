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
#ifndef NLSAT_TYPES_H_
#define NLSAT_TYPES_H_

#include"polynomial.h"
#include"buffer.h"
#include"sat_types.h"
#include"z3_exception.h"

namespace algebraic_numbers {
    class anum;
    class manager;
};

namespace nlsat {
#define NLSAT_VB_LVL 10
    typedef void *                     assumption;
    typedef void *                     assumption_set;

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

    typedef ptr_vector<atom> atom_vector;

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
        case atom::kind::EQ: return out << "=";
        case atom::kind::LT: return out << "<";
        case atom::kind::ROOT_EQ: return out << "= root";
        case atom::kind::ROOT_LT: return out << "< root";
        case atom::kind::ROOT_LE: return out << "<= root";
        case atom::kind::ROOT_GT: return out << "> root";
        case atom::kind::ROOT_GE: return out << ">= root";
        default: UNREACHABLE();
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

    inline ineq_atom * to_ineq_atom(atom * a) { SASSERT(a->is_ineq_atom()); return static_cast<ineq_atom*>(a); }
    inline root_atom * to_root_atom(atom * a) { SASSERT(a->is_root_atom()); return static_cast<root_atom*>(a); }
    inline ineq_atom const * to_ineq_atom(atom const * a) { SASSERT(a->is_ineq_atom()); return static_cast<ineq_atom const *>(a); }
    inline root_atom const * to_root_atom(atom const * a) { SASSERT(a->is_root_atom()); return static_cast<root_atom const *>(a); }

    typedef algebraic_numbers::anum    anum;
    typedef algebraic_numbers::manager anum_manager;

    class solver_exception : public default_exception {
    public:
        solver_exception(char const * msg):default_exception(msg) {}
    };

    class assignment;
    
    inline int normalize_sign(int s) {
        if (s < 0)  return -1;
        if (s == 0) return 0;
        return 1;
    }
};

#endif
