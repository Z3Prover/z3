/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat types

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/
#pragma once
#include "ast/euf/euf_egraph.h"
#include "util/trail.h"
#include "util/lbool.h"
#include "util/map.h"
#include "util/rlimit.h"
#include "util/scoped_ptr_vector.h"
#include "util/ref_vector.h"
#include "util/sat_literal.h"
#include "math/dd/dd_pdd.h"
#include "math/dd/dd_fdd.h"

namespace polysat {

    class solver;
    class constraint;
    class clause;

    using clause_ref = ref<clause>;
    using clause_ref_vector = sref_vector<clause>;

    using dd::pdd;
    using dd::pdd_monomial;
    using dd::pdd_manager;
    using dd::val_pp;

    using pvar = unsigned;
    using pvar_vector = unsigned_vector;
    inline const pvar null_var = UINT_MAX;

    enum class pvar_kind : std::uint8_t {
        external,           // regular variables (from the input formula)
        name,               // name for a polynomial term
        op,                 // result of an op_constraint
        internal,           // other internal variable
    };

    class dependency {
        unsigned m_val;
    public:
        explicit dependency(unsigned val): m_val(val) {}
        unsigned val() const { return m_val; }
        bool is_null() const { return m_val == UINT_MAX; }
        unsigned hash() const { return val(); }
    };

    inline const dependency null_dependency = dependency(UINT_MAX);
    using dependency_vector = svector<dependency>;

    inline bool operator< (dependency const& d1, dependency const& d2) { return d1.val() <  d2.val(); }
    inline bool operator<=(dependency const& d1, dependency const& d2) { return d1.val() <= d2.val(); }
    inline bool operator> (dependency const& d1, dependency const& d2) { return d1.val() >  d2.val(); }
    inline bool operator>=(dependency const& d1, dependency const& d2) { return d1.val() >= d2.val(); }
    inline bool operator==(dependency const& d1, dependency const& d2) { return d1.val() == d2.val(); }
    inline bool operator!=(dependency const& d1, dependency const& d2) { return d1.val() != d2.val(); }

    inline std::ostream& operator<<(std::ostream& out, dependency const& d) {
        out << "dep(";
        if (d.is_null())
            out << "<null>";
        else
            out << d.val();
        return out << ")";
    }


    /// x[hi:lo] = value
    struct fixed_bits {
        unsigned hi = 0;
        unsigned lo = 0;
        rational value;

        fixed_bits() = default;
        fixed_bits(unsigned hi, unsigned lo, rational value): hi(hi), lo(lo), value(value) {}
    };

    struct justified_fixed_bits : public fixed_bits {
        euf::enode* just;

        justified_fixed_bits(unsigned hi, unsigned lo, rational value, euf::enode* just): fixed_bits(hi, lo, value), just(just) {}
    };

    using justified_fixed_bits_vector = vector<justified_fixed_bits>;

    class viable_slicing_interface {
    public:
        using enode = euf::enode;
        using enode_vector = euf::enode_vector;
        using enode_pair = euf::enode_pair;
        using enode_pair_vector = euf::enode_pair_vector;

        virtual ~viable_slicing_interface() {}

        // Find hi, lo such that x = src[hi:lo].
        virtual bool is_extract(pvar x, pvar src, unsigned& out_hi, unsigned& out_lo) = 0;

        /** Collect fixed portions of the variable v */
        virtual void collect_fixed(pvar v, justified_fixed_bits_vector& out) = 0;
        virtual void explain_fixed(enode* just, std::function<void(sat::literal)> const& on_lit, std::function<void(pvar)> const& on_var) = 0;

        /** For a given variable v, find the set of variables w such that w = v[|w|:0]. */
        virtual void collect_prefixes(pvar v, pvar_vector& out) = 0;
        virtual void explain_prefix(pvar v, pvar x, std::function<void(sat::literal)> const& on_lit) = 0;
    };

}
