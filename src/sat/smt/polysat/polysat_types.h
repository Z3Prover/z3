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

    using pvar_vector = unsigned_vector;
    inline const pvar null_var = UINT_MAX;

    class signed_constraint;

    class dependency {
        std::variant<sat::literal, std::pair<theory_var, theory_var>> m_data;
        unsigned m_level;
    public:
        dependency(sat::literal lit, unsigned level) : m_data(lit), m_level(level) {}
        dependency(theory_var v1, theory_var v2, unsigned level) : m_data(std::make_pair(v1, v2)), m_level(level) {} 
        bool is_null() const { return is_literal() && *std::get_if<sat::literal>(&m_data) == sat::null_literal; }
        bool is_literal() const { return std::holds_alternative<sat::literal>(m_data); }
        sat::literal literal() const { SASSERT(is_literal()); return *std::get_if<sat::literal>(&m_data); }
        std::pair<theory_var, theory_var> eq() const { SASSERT(!is_literal()); return *std::get_if<std::pair<theory_var, theory_var>>(&m_data); }
        unsigned level() const { return m_level; }
    };

    inline const dependency null_dependency = dependency(sat::null_literal, UINT_MAX);

    inline std::ostream& operator<<(std::ostream& out, dependency d) {
        if (d.is_null())
            return out << "null";
        else if (d.is_literal())
            return out << d.literal() << "@" << d.level();
        else
            return out << "v" << d.eq().first << " == v" << d.eq().second << "@" << d.level();
    }

    struct trailing_bits {
        unsigned length;
        rational bits;
        bool positive;
        unsigned src_idx;
    };

    struct leading_bits {
        unsigned length;
        bool positive; // either all 0 or all 1
        unsigned src_idx;
    };

    struct single_bit {
        bool positive;
        unsigned position;
        unsigned src_idx;
    };

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

    using core_vector = vector<std::variant<signed_constraint, dependency>>;



    //
    // The interface that PolySAT uses to the SAT/SMT solver.
    //

    class solver_interface {
    public:
        virtual void add_eq_literal(pvar v, rational const& val) = 0;
        virtual void set_conflict(dependency_vector const& core) = 0;
        virtual void set_lemma(core_vector const& aux_core, unsigned level, dependency_vector const& core) = 0;
        virtual dependency propagate(signed_constraint sc, dependency_vector const& deps) = 0;
        virtual void propagate(dependency const& d, bool sign, dependency_vector const& deps) = 0;
        virtual trail_stack& trail() = 0;
        virtual bool inconsistent() const = 0;
        virtual void get_bitvector_prefixes(pvar v, pvar_vector& out) = 0;
        virtual void get_fixed_bits(pvar v, svector<justified_fixed_bits>& fixed_bits) = 0;
    };

}
