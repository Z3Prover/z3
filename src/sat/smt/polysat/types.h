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

namespace euf {
    class enode;
}

namespace polysat {

    using pdd = dd::pdd;
    using pvar = unsigned;
    using theory_var = int;
    using enode_pair = std::pair<euf::enode*, euf::enode*>;

    struct constraint_id {
        unsigned id = UINT_MAX; 
        bool is_null() const { return id == UINT_MAX; }
        static constraint_id null() { return constraint_id{ UINT_MAX }; }
    };

    using pvar_vector = unsigned_vector;
    using theory_var_pair = std::pair<theory_var, theory_var>;
    
    inline const pvar null_var = UINT_MAX;

    class signed_constraint;

    struct fixed_slice {
        pvar child;
        unsigned offset = 0;
        unsigned length = 0;
        rational value;
        fixed_slice() = default;
        fixed_slice(pvar child, rational value, unsigned offset, unsigned length) : 
            child(child), offset(offset), length(length), value(std::move(value)) {}
        unsigned end() const { return offset + length; }
    };

    struct fixed_claim : public fixed_slice {
        pvar parent;
        fixed_claim() = default;
        fixed_claim(pvar parent, pvar child, rational value, unsigned offset, unsigned length) : fixed_slice(child, std::move(value), offset, length), parent(parent) {}
        fixed_claim(pvar parent, fixed_slice const& s) : fixed_slice(s), parent(parent) {}
    };

    struct offset_slice {
        pvar child;
        unsigned offset;
        offset_slice() = default;
        offset_slice(pvar child, unsigned offset) : child(child), offset(offset) {}
    };

    // parent[X:offset] = child
    // where X = offset + size(child) - 1
    struct offset_claim : public offset_slice {
        pvar parent;
        offset_claim() = default;
        offset_claim(pvar parent, offset_slice const& s) : offset_slice(s), parent(parent) {}
    };


    class dependency {
        struct axiom_t {};
        std::variant<axiom_t, sat::bool_var, theory_var_pair, enode_pair, offset_claim, fixed_claim> m_data;
        dependency(): m_data(axiom_t()) {}
    public:
        dependency(sat::bool_var v) : m_data(v){}
        dependency(theory_var v1, theory_var v2) : m_data(std::make_pair(v1, v2)) {}
        dependency(euf::enode* n1, euf::enode* n2) : m_data(std::make_pair(n1, n2)) {}
        dependency(offset_claim const& c) : m_data(c) {}
        dependency(fixed_claim const& c): m_data(c) {}
        static dependency axiom() { return dependency(); } 
        bool is_null() const { return is_bool_var() && *std::get_if<sat::bool_var>(&m_data) == sat::null_bool_var; }
        bool is_axiom() const { return std::holds_alternative<axiom_t>(m_data); }
        bool is_eq() const { return std::holds_alternative<theory_var_pair>(m_data); }
        bool is_enode_eq() const { return std::holds_alternative<enode_pair>(m_data); }
        bool is_bool_var() const { return std::holds_alternative<sat::bool_var>(m_data); }
        bool is_offset_claim() const { return std::holds_alternative<offset_claim>(m_data); }
        bool is_fixed_claim() const { return std::holds_alternative<fixed_claim>(m_data); }
        sat::bool_var bool_var() const { SASSERT(is_bool_var()); return *std::get_if<sat::bool_var>(&m_data); }
        theory_var_pair eq() const { SASSERT(is_eq()); return *std::get_if<theory_var_pair>(&m_data); }
        enode_pair enode_eq() const { SASSERT(is_enode_eq()); return *std::get_if<enode_pair>(&m_data); }
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
            return out << "tv" << d.eq().first << " == tv" << d.eq().second;
        else if (d.is_enode_eq())
            return out << "enode " << d.enode_eq().first << " == enode " << d.enode_eq().second;
        else if (d.is_offset_claim()) {
            auto offs = d.offset();
            return out << "v" << offs.child << " == v" << offs.parent << " offset " << offs.offset;
        }
        else if (d.is_fixed_claim()) {
            auto fixed = d.fixed();
            return out << fixed.value << " == v" << fixed.parent << " [" << fixed.length << "]@" << fixed.offset;
        }
        else {
            UNREACHABLE();
            return out;
        }
    }



    inline std::ostream& operator<<(std::ostream& out, offset_slice const& js) {
        if (js.offset == 0)
            return out << "v" << js.child;
        return out << "v" << js.child << " at offset " << js.offset;
    }

    using fixed_bits_vector = vector<fixed_slice>;

    struct fixed_slice_extra : public fixed_slice {
        // pvar child;
        // unsigned offset = 0;
        // unsigned length = 0;
        // rational value;
        unsigned level = 0;  // level when sub-slice was fixed to value
        dependency dep = null_dependency;
        fixed_slice_extra() = default;
        fixed_slice_extra(pvar child, rational value, unsigned offset, unsigned length, unsigned level, dependency dep) :
            fixed_slice(child, std::move(value), offset, length), level(level), dep(std::move(dep)) {}
    };
    using fixed_slice_extra_vector = vector<fixed_slice_extra>;

    struct offset_slice_extra : public offset_slice {
        // pvar child;
        // unsigned offset;
        unsigned level = 0;                 // level when child was fixed to value
        dependency dep = null_dependency;   // justification for fixed value
        rational value;                     // fixed value of child
        offset_slice_extra() = default;
        offset_slice_extra(pvar child, unsigned offset, unsigned level, dependency dep, rational value) : offset_slice(child, offset), level(level), dep(std::move(dep)), value(std::move(value)) {}
    };
    using offset_slice_extra_vector = vector<offset_slice_extra>;


    using dependency_vector = vector<dependency>;
    using constraint_or_dependency = std::variant<signed_constraint, dependency>;
    using constraint_id_or_constraint = std::variant<constraint_id, signed_constraint>;
    using constraint_id_or_dependency = std::variant<constraint_id, dependency>;

    using constraint_or_dependency_list = std::initializer_list<constraint_or_dependency>;
    using constraint_or_dependency_vector = vector<constraint_or_dependency>;
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
        virtual void set_conflict(dependency_vector const& core, char const* hint) = 0;
        virtual dependency propagate(signed_constraint sc, dependency_vector const& deps, char const* hint) = 0;
        virtual void propagate(dependency const& d, bool sign, dependency_vector const& deps, char const* hint) = 0;
        virtual void propagate_eq(pvar v, rational const& val, dependency const& d) = 0;
        virtual trail_stack& trail() = 0;
        virtual bool inconsistent() const = 0;
        virtual void get_bitvector_suffixes(pvar v, offset_slices& out) = 0;
        virtual void get_bitvector_sub_slices(pvar v, offset_slices& out) = 0;
        virtual void get_bitvector_super_slices(pvar v, offset_slices& out) = 0;
        virtual void get_fixed_bits(pvar v, fixed_bits_vector& fixed_slice) = 0;
        virtual void get_fixed_sub_slices(pvar v, fixed_slice_extra_vector& fixed_slice, offset_slice_extra_vector& subslices) = 0;
        virtual pdd mk_ite(signed_constraint const& sc, pdd const& p, pdd const& q) = 0;
        virtual pdd mk_zero_extend(unsigned sz, pdd const& p) = 0;
        virtual unsigned level(dependency const& d) = 0;
    };

}
