/*++
Copyright (c) 2021 Microsoft Corporation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include <variant>



#include "math/dd/dd_pdd.h"
#include "util/trail.h"
#include "util/sat_literal.h"

namespace polysat {

    using pdd = dd::pdd;
    using pvar = unsigned;
    using theory_var = unsigned;
    struct constraint_id {
        unsigned id; bool is_null() const { return id == UINT_MAX; }
        static constraint_id null() { return constraint_id{ UINT_MAX }; }
    };

    using pvar_vector = unsigned_vector;
    using theory_var_pair = std::pair<theory_var, theory_var>;
    
    inline const pvar null_var = UINT_MAX;

    class signed_constraint;

    struct fixed_slice {
        unsigned hi = 0;
        unsigned lo = 0;
        rational value;
        fixed_slice() = default;
        fixed_slice(unsigned hi, unsigned lo, rational value) : hi(hi), lo(lo), value(value) {}
    };

    struct fixed_claim : public fixed_slice {
        pvar v;
        fixed_claim() = default;
        fixed_claim(pvar v, unsigned hi, unsigned lo, rational value) : fixed_slice(hi, lo, value), v(v) {}
        fixed_claim(pvar, fixed_slice const& s) : fixed_slice(s), v(v) {}
    };

    struct offset_slice {
        pvar v;
        unsigned offset;
    };

    struct offset_claim : public offset_slice {
        pvar w;
        offset_claim() = default;
        offset_claim(pvar w, offset_slice const& s) : offset_slice(s), w(w) {}
    };

    class dependency {
        struct axiom_t {};
        std::variant<axiom_t, sat::bool_var, theory_var_pair, offset_claim, fixed_claim> m_data;
        dependency(): m_data(axiom_t()) {}
    public:
        dependency(sat::bool_var v) : m_data(v){}
        dependency(theory_var v1, theory_var v2) : m_data(std::make_pair(v1, v2)) {}         
        dependency(offset_claim const& c) : m_data(c) {}
        dependency(fixed_claim const& c): m_data(c) {}
        static dependency axiom() { return dependency(); } 
        bool is_null() const { return is_bool_var() && *std::get_if<sat::bool_var>(&m_data) == sat::null_bool_var; }
        bool is_axiom() const { return std::holds_alternative<axiom_t>(m_data); }
        bool is_eq() const { return std::holds_alternative<theory_var_pair>(m_data); }
        bool is_bool_var() const { return std::holds_alternative<sat::bool_var>(m_data); }
        bool is_offset_claim() const { return std::holds_alternative<offset_claim>(m_data); }
        bool is_fixed_claim() const { return std::holds_alternative<fixed_claim>(m_data); }
        sat::bool_var bool_var() const { SASSERT(is_bool_var()); return *std::get_if<sat::bool_var>(&m_data); }
        theory_var_pair eq() const { SASSERT(is_eq()); return *std::get_if<theory_var_pair>(&m_data); }
        offset_claim offset() const { return *std::get_if<offset_claim>(&m_data); }
        fixed_claim fixed() const { return *std::get_if<fixed_claim>(&m_data); }
    };

    inline const dependency null_dependency = dependency(sat::null_bool_var);

    inline std::ostream& operator<<(std::ostream& out, dependency d) {
        if (d.is_null())
            return out << "null";
        else if (d.is_axiom())
            return out << "axiom";
        else if (d.is_bool_var())
            return out << d.bool_var();
        else if (d.is_eq())
            return out << "v" << d.eq().first << " == v" << d.eq().second;
        else if (d.is_offset_claim()) {
            auto offs = d.offset();
            return out << "v" << offs.v << " == v" << offs.w << " offset " << offs.offset;
        }
        else if (d.is_fixed_claim()) {
            auto fixed = d.fixed();
            return out << fixed.value << " == v" << fixed.v << " [" << fixed.hi << ":" << fixed.lo << "]";
        }
        else {
            UNREACHABLE();
            return out;
        }
    }



    inline std::ostream& operator<<(std::ostream& out, offset_slice const& js) {
        if (js.offset == 0)
            return out << "v" << js.v;
        return out << "v" << js.v << " at offset " << js.offset;
    }

    using fixed_bits_vector = svector<fixed_slice>;

    using dependency_vector = vector<dependency>;
    using constraint_or_dependency = std::variant<signed_constraint, dependency>;
    using constraint_id_or_constraint = std::variant<constraint_id, signed_constraint>;
    using constraint_id_or_dependency = std::variant<constraint_id, dependency>;

    using constraint_or_dependency_list = std::initializer_list<constraint_or_dependency>;
    using constraint_id_vector = svector<constraint_id>;
    using constraint_id_list = std::initializer_list<constraint_id>;
    using offset_slices = vector<offset_slice>;

    //
    // The interface that PolySAT uses to the SAT/SMT solver.
    //

    class solver_interface {
    public:
        virtual ~solver_interface() {}
        virtual lbool add_eq_literal(pvar v, rational const& val, dependency& d) = 0;
        virtual bool add_axiom(char const* name, constraint_or_dependency const* begin, constraint_or_dependency const* end, bool redundant) = 0;
        virtual void set_conflict(dependency_vector const& core) = 0;
        virtual dependency propagate(signed_constraint sc, dependency_vector const& deps) = 0;
        virtual void propagate(dependency const& d, bool sign, dependency_vector const& deps) = 0;
        virtual trail_stack& trail() = 0;
        virtual bool inconsistent() const = 0;
        virtual void get_bitvector_suffixes(pvar v, offset_slices& out) = 0;
        virtual void get_bitvector_sub_slices(pvar v, offset_slices& out) = 0;
        virtual void get_bitvector_super_slices(pvar v, offset_slices& out) = 0;
        virtual void get_fixed_bits(pvar v, fixed_bits_vector& fixed_slice) = 0;
        virtual unsigned level(dependency const& d) = 0;
    };

}
