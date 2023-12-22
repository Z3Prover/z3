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
    inline const pvar null_var = UINT_MAX;

    class signed_constraint;

    class dependency {
        struct axiom_t {};
        std::variant<axiom_t, sat::literal, std::pair<theory_var, theory_var>> m_data;
        unsigned m_level;
        dependency(): m_data(axiom_t()), m_level(0) {}
    public:
        dependency(sat::literal lit, unsigned level) : m_data(lit), m_level(level) {}
        dependency(theory_var v1, theory_var v2, unsigned level) : m_data(std::make_pair(v1, v2)), m_level(level) {} 
        static dependency axiom() { return dependency(); } 
        bool is_null() const { return is_literal() && *std::get_if<sat::literal>(&m_data) == sat::null_literal; }
        bool is_axiom() const { return std::holds_alternative<axiom_t>(m_data); }
        bool is_eq() const { return std::holds_alternative<std::pair<theory_var, theory_var>>(m_data); }
        bool is_literal() const { return std::holds_alternative<sat::literal>(m_data); }
        sat::literal literal() const { SASSERT(is_literal()); return *std::get_if<sat::literal>(&m_data); }
        std::pair<theory_var, theory_var> eq() const { SASSERT(!is_literal()); return *std::get_if<std::pair<theory_var, theory_var>>(&m_data); }
        unsigned level() const { return m_level; }
        void set_level(unsigned level) { m_level = level; }
        dependency operator~() const { SASSERT(is_literal()); return dependency(~literal(), level()); }
    };

    inline const dependency null_dependency = dependency(sat::null_literal, UINT_MAX);

    inline std::ostream& operator<<(std::ostream& out, dependency d) {
        if (d.is_null())
            return out << "null";
        else if (d.is_axiom())
            return out << "axiom@" << d.level();
        else if (d.is_literal())
            return out << d.literal() << "@" << d.level();
        else
            return out << "v" << d.eq().first << " == v" << d.eq().second << "@" << d.level();
    }


    struct fixed_bits {
        unsigned hi = 0;
        unsigned lo = 0;
        rational value;

        /// The constraint is equivalent to setting fixed bits on a variable.
        // bool is_equivalent;

        fixed_bits() = default;
        fixed_bits(unsigned hi, unsigned lo, rational value) : hi(hi), lo(lo), value(value) {}
    };

    struct justified_fixed_bits : public fixed_bits, public dependency {};

    using dependency_vector = vector<dependency>;

    using core_vector = std::initializer_list<std::variant<signed_constraint, dependency>>;
    using constraint_id_vector = svector<constraint_id>;
    using constraint_ids = std::initializer_list<constraint_id>;


    //
    // The interface that PolySAT uses to the SAT/SMT solver.
    //

    class solver_interface {
    public:
        virtual ~solver_interface() {}
        virtual void add_eq_literal(pvar v, rational const& val) = 0;
        virtual bool add_axiom(char const* name, core_vector const& core, bool redundant) = 0;
        virtual void set_conflict(constraint_id_vector const& core) = 0;
        virtual bool propagate(signed_constraint sc, constraint_id_vector const& deps) = 0;
        virtual void propagate(dependency const& d, bool sign, constraint_id_vector const& deps) = 0;
        virtual trail_stack& trail() = 0;
        virtual bool inconsistent() const = 0;
        virtual void get_bitvector_suffixes(pvar v, pvar_vector& out) = 0;
        virtual void get_fixed_bits(pvar v, svector<justified_fixed_bits>& fixed_bits) = 0;
    };

}
