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

#include "sat/smt/polysat/polysat_types.h"
#include "sat/smt/polysat/polysat_fi.h"

namespace polysat {

    enum class find_t {
        empty,
        singleton,
        multiple,
        resource_out,
    };

    class core;
    class constraints;

    std::ostream& operator<<(std::ostream& out, find_t x);

    class viable {
        core& c;
        constraints& cs;
        forbidden_intervals      m_forbidden_intervals;

        struct entry final : public dll_base<entry>, public fi_record {
            /// whether the entry has been created by refinement (from constraints in 'fi_record::src')
            bool refined = false;
            /// whether the entry is part of the current set of intervals, or stashed away for backtracking
            bool active = true;
            bool valid_for_lemma = true;
            pvar var = null_var;
            unsigned constraint_index = UINT_MAX;

            void reset() {
                // dll_base<entry>::init(this);  // we never did this in alloc_entry either
                fi_record::reset();
                refined = false;
                active = true;
                valid_for_lemma = true;
                var = null_var;
                constraint_index = UINT_MAX;
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
            layer& ensure_layer(unsigned bit_width);
            layer* get_layer(unsigned bit_width);
            layer* get_layer(entry* e) { return get_layer(e->bit_width); }
            layer const* get_layer(unsigned bit_width) const;
            layer const* get_layer(entry* e) const { return get_layer(e->bit_width); }
            entry* get_entries(unsigned bit_width) const { layer const* l = get_layer(bit_width); return l ? l->entries : nullptr; }
        };

        struct fixed_bits_info {
            svector<lbool> fixed;
            vector<vector<signed_constraint>> just_src;
            vector<vector<signed_constraint>> just_side_cond;
            vector<svector<justified_fixed_bits>> just_slicing;

            bool is_empty() const {
                SASSERT_EQ(fixed.empty(), just_src.empty());
                SASSERT_EQ(fixed.empty(), just_side_cond.empty());
                return fixed.empty();
            }

            bool is_empty_at(unsigned i) const {
                return fixed[i] == l_undef && just_src[i].empty() && just_side_cond[i].empty();
            }

            void reset(unsigned num_bits) {
                fixed.reset();
                fixed.resize(num_bits, l_undef);
                just_src.reset();
                just_src.resize(num_bits);
                just_side_cond.reset();
                just_side_cond.resize(num_bits);
                just_slicing.reset();
                just_slicing.resize(num_bits);
            }

            void reset_just(unsigned i) {
                just_src[i].reset();
                just_side_cond[i].reset();
                just_slicing[i].reset();
            }

            void set_just(unsigned i, entry* e) {
                reset_just(i);
                push_just(i, e);
            }

            void push_just(unsigned i, entry* e) {
                just_src[i].append(e->src);
                just_side_cond[i].append(e->side_cond);
            }

            void push_from_bit(unsigned i, unsigned src) {
                just_src[i].append(just_src[src]);
                just_side_cond[i].append(just_side_cond[src]);
                just_slicing[i].append(just_slicing[src]);
            }
        };


        ptr_vector<entry>       m_alloc;
        vector<layers>          m_units;        // set of viable values based on unit multipliers, layered by bit-width in descending order
        ptr_vector<entry>       m_equal_lin;    // entries that have non-unit multipliers, but are equal
        ptr_vector<entry>       m_diseq_lin;    // entries that have distinct non-zero multipliers

        bool well_formed(entry* e);
        bool well_formed(layers const& ls);

        entry* alloc_entry(pvar v, unsigned constraint_index);

        std::ostream& display_one(std::ostream& out, pvar v, entry const* e) const;
        std::ostream& display_all(std::ostream& out, pvar v, entry const* e, char const* delimiter = "") const;
        void log();
        void log(pvar v);

        struct pop_viable_trail;
        void pop_viable(entry* e, entry_kind k);
        struct push_viable_trail;
        void push_viable(entry* e);

        void insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k);

        bool intersect(pvar v, entry* e);

        void ensure_var(pvar v);

        lbool find_viable(pvar v, rational& lo, rational& hi);

        lbool find_on_layers(
            pvar v,
            unsigned_vector const& widths,
            pvar_vector const& overlaps,
            fixed_bits_info const& fbi,
            rational const& to_cover_lo,
            rational const& to_cover_hi,
            rational& out_val);

        lbool find_on_layer(
            pvar v,
            unsigned w_idx,
            unsigned_vector const& widths,
            pvar_vector const& overlaps,
            fixed_bits_info const& fbi,
            rational const& to_cover_lo,
            rational const& to_cover_hi,
            rational& out_val,
            ptr_vector<entry>& refine_todo,
            ptr_vector<entry>& relevant_entries);


        template <bool FORWARD>
        bool refine_viable(pvar v, rational const& val, fixed_bits_info const& fbi) {
            throw default_exception("nyi");
        }

        bool refine_viable(pvar v, rational const& val) {
            throw default_exception("nyi");
        }

        template <bool FORWARD>
        bool refine_bits(pvar v, rational const& val, fixed_bits_info const& fbi) {
            throw default_exception("nyi");
        }

        template <bool FORWARD>
        entry* refine_bits(pvar v, rational const& val, unsigned num_bits, fixed_bits_info const& fbi) {
            throw default_exception("nyi");
        }

        bool refine_equal_lin(pvar v, rational const& val) {
            throw default_exception("nyi");
        }

        bool refine_disequal_lin(pvar v, rational const& val) {
            throw default_exception("nyi");
        }

        bool set_conflict_by_interval(pvar v, unsigned w, ptr_vector<entry>& intervals, unsigned first_interval) {
            throw default_exception("nyi");
        }

        std::pair<entry*, bool> find_value(rational const& val, entry* entries) {
            throw default_exception("nyi");
        }

        bool collect_bit_information(pvar v, bool add_conflict, fixed_bits_info& out_fbi);

    public:
        viable(core& c);

        ~viable();

        /**
         * Find a next viable value for variable.
         */
        find_t find_viable(pvar v, rational& out_val);

        /*
        * Explain why the current variable is not viable or signleton.
        */
        dependency_vector explain();

        /*
        * Register constraint at index 'idx' as unitary in v.
        */
        void add_unitary(pvar v, unsigned idx);

    };

}
