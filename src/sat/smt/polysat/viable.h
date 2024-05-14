/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains
    It uses the interval extraction functions from forbidden intervals.
    An empty viable set corresponds directly to a conflict that does not rely on
    the non-viable variable.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "util/rational.h"
#include "util/dlist.h"
#include "util/map.h"
#include "util/small_object_allocator.h"

#include "sat/smt/polysat/types.h"
#include "sat/smt/polysat/forbidden_intervals.h"
#include "sat/smt/polysat/project_interval.h"
#include "sat/smt/polysat/fixed_bits.h"


namespace polysat {

    enum class find_t {
        empty,
        singleton,
        multiple,
        resource_out,
    };

    std::ostream& operator<<(std::ostream& out, find_t x);

    class core;
    class constraints;


    class viable {
        core&                   c;
        constraints&            cs;
        forbidden_intervals     m_forbidden_intervals;
        project_interval        m_projection;

        struct entry final : public dll_base<entry>, public fi_record {
            /// whether the entry has been created by refinement (from constraints in 'fi_record::src')
            bool refined = false;
            /// whether the entry is part of the current set of intervals, or stashed away for backtracking     
            bool active = true;
            pvar var = null_var;
            constraint_id constraint_index;
            bool marked = false;

            void reset() {
                // dll_base<entry>::init(this);  // we never did this in alloc_entry either
                fi_record::reset();
                refined = false;
                active = true;
                var = null_var;
                constraint_index = constraint_id::null();
                marked = false;
            }
        };

        enum class entry_kind { unit_e, equal_e, diseq_e };

        struct layer final {
            entry* entries = nullptr;
            unsigned bit_width = 0;
            layer(unsigned bw) : bit_width(bw) {}
        };

        class layers final {
            svector<layer> m_layers;
        public:
            svector<layer> const& get_layers() const { return m_layers; }
            svector<layer>& get_layers() { return m_layers; }
            layer& ensure_layer(unsigned bit_width);
            layer* get_layer(unsigned bit_width);
            layer* get_layer(entry* e) { return get_layer(e->bit_width); }
            layer const* get_layer(unsigned bit_width) const;
            layer const* get_layer(entry* e) const { return get_layer(e->bit_width); }
            entry* get_entries(unsigned bit_width) const { layer const* l = get_layer(bit_width); return l ? l->entries : nullptr; }
        };

        // short for t in [lo,hi[ 
        struct explanation {
            entry* e;
            rational value;
            bool mark = false;
            bool operator==(explanation const& other) const { return e == other.e && value == other.value && mark == other.mark; }
        };
        ptr_vector<entry>       m_alloc;
        vector<layers>          m_units;        // set of viable values based on unit multipliers, layered by bit-width in descending order
        ptr_vector<entry>       m_equal_lin;    // entries that have non-unit multipliers, but are equal
        ptr_vector<entry>       m_diseq_lin;    // entries that have distinct non-zero multipliers       
        vector<explanation>     m_explain;      // entries that explain the current propagation or conflict

        bool well_formed(entry* e);
        bool well_formed(layers const& ls);

        entry* alloc_entry(pvar v, constraint_id constraint_index);

        std::ostream& display_one(std::ostream& out, entry const* e) const;
        std::ostream& display_all(std::ostream& out, entry const* e, char const* delimiter = "") const;

        struct pop_viable_trail;
        void pop_viable(entry* e, entry_kind k);
        struct push_viable_trail;
        void push_viable(entry* e);

        void insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k);

        bool intersect(pvar v, entry* e);

        // find the first non-fixed entry that overlaps with val, if any.
        entry* find_overlap(rational& val);
        entry* find_overlap(ptr_vector<layer const> const& layers, rational const& val);
        entry* find_overlap(layer const& l, rational const& val);

        bool remove_redundant_explanations();

        void update_value_to_high(rational& val, entry* e);
        bool is_conflict();
        void explain_overlap_v1(explanation const& e, explanation const& after, rational& prefix, dependency_vector& out_deps);
        void explain_overlaps_v2(explanation const* first, explanation const* last, dependency_vector& out_deps);
        void explain_overlap(explanation const& e, explanation const& after, dependency_vector& out_deps);
        void explain_hole_overlap(explanation const& before, explanation const& e, explanation const& after, dependency_vector& out_deps);
        void explain_hole_size(explanation const& before, explanation const& after, unsigned hole_bits, dependency_vector& out_deps);
        void pin(pdd& p, rational const& value, unsigned ebw, dd::pdd_manager& target, dependency_vector& out_deps);
        r_interval get_covered_interval(explanation const& e) const;

        viable::entry* find_overlap(rational const& val, entry* entries);

        bool check_disequal_lin(pvar v, rational const& val);

        bool check_equal_lin(pvar v, rational const& val);

        bool check_fixed_bits(pvar v, rational const& val);

        bool is_propagation(rational const& val);

        enum class explain_t {
            conflict,  // conflict due to overlapping intervals
            propagation,
            assignment,
            none,
            explained,
        };

        friend std::ostream& operator<<(std::ostream& out, explain_t e);

        pvar            m_var = null_var;
        explain_t       m_explain_kind = explain_t::none;
        dependency      m_assign_dep = null_dependency;
        unsigned        m_num_bits = 0;
        fixed_bits      m_fixed_bits;
        offset_slices   m_suffixes;
        void init_suffixes(pvar v);
        std::ostream& display_state(std::ostream& out) const;
        std::ostream& display_explain(std::ostream& out) const;
        std::ostream& display_explain(std::ostream& out, explanation const& e) const;

    public:
        viable(core& c);

        ~viable();

        /**
         * Find a next viable value for variable.
         */
        find_t find_viable(pvar v, rational& out_val);

        /*
         * Explain the current variable is not viable or singleton.
         */
        dependency_vector explain();

        /*
         * Register constraint at index 'idx' as unitary in v.
         */
        find_t add_unitary(pvar v, constraint_id, rational& value);

        /*
         * Ensure data-structures tracking variable v.
         */
        void ensure_var(pvar v);

        /*
         * Check if assignment is viable.
         */
        bool assign(pvar v, rational const& value, dependency dep);

        std::ostream& display(std::ostream& out) const;

    };

}
