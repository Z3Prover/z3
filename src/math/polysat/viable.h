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

#include "util/dlist.h"
#include "util/map.h"
#include "util/small_object_allocator.h"
#include "math/polysat/types.h"
#include "math/polysat/conflict.h"
#include "math/polysat/constraint.h"
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/slicing.h"
#include <optional>

namespace polysat {

    class solver;
    class univariate_solver;
    class univariate_solver_factory;

    enum class find_t {
        empty,
        singleton,
        multiple,
        resource_out,
    };

    std::ostream& operator<<(std::ostream& out, find_t x);

    class viable {
        friend class test_fi;
        friend class test_polysat;
        friend class conflict;

        solver& s;
        forbidden_intervals      m_forbidden_intervals;

        struct entry final : public dll_base<entry>, public fi_record {
            /// whether the entry has been created by refinement (from constraints in 'fi_record::src')
            bool refined = false;
            /// whether the entry is part of the current set of intervals, or stashed away for backtracking
            bool active = true;
            bool valid_for_lemma = true;
            pvar var = null_var;

            void reset() {
                // dll_base<entry>::init(this);  // we never did this in alloc_entry either
                fi_record::reset();
                refined = false;
                active = true;
                valid_for_lemma = true;
                var = null_var;
            }
        };

        enum class entry_kind { unit_e, equal_e, diseq_e };

        struct layer final {
            entry* entries = nullptr;
            unsigned bit_width = 0;
            layer(unsigned bw): bit_width(bw) {}
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

        ptr_vector<entry>       m_alloc;
        vector<layers>          m_units;        // set of viable values based on unit multipliers, layered by bit-width in descending order
        ptr_vector<entry>       m_equal_lin;    // entries that have non-unit multipliers, but are equal
        ptr_vector<entry>       m_diseq_lin;    // entries that have distinct non-zero multipliers
        svector<std::tuple<pvar, entry_kind, entry*>>     m_trail; // undo stack

        struct reason_ptr {
            unsigned begin = 0;
            unsigned len = 0;
        };
        sat::literal_vector     m_propagation_reason_storage;
        pvar_vector             m_propagation_trail;
        svector<reason_ptr>     m_propagation_reasons;

        unsigned size(pvar v) const;

        bool well_formed(entry* e);
        bool well_formed(layers const& ls);

        entry* alloc_entry(pvar v);

        bool intersect(pvar v, entry* e);

        struct fixed_bits_info {
            svector<lbool> fixed;
            vector<sat::literal_vector> just_src;
            vector<sat::literal_vector> just_side_cond;
            vector<ptr_vector<slicing::enode>> just_slicing;

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
                for (signed_constraint c : e->src)
                    just_src[i].push_back(c.blit());
                for (signed_constraint c : e->side_cond)
                    just_side_cond[i].push_back(c.blit());
            }

            void push_from_bit(unsigned i, unsigned src) {
                for (sat::literal lit : just_src[src])
                    just_src[i].push_back(lit);
                for (sat::literal lit : just_side_cond[src])
                    just_side_cond[i].push_back(lit);
                for (slicing::enode* slice : just_slicing[src])
                    just_slicing[i].push_back(slice);
            }
        };

        // fixed_bits_info m_tmp_fbi;

        template <bool FORWARD>
        bool refine_viable(pvar v, rational const& val, fixed_bits_info const& fbi);

        bool refine_viable(pvar v, rational const& val);

        template <bool FORWARD>
        bool refine_bits(pvar v, rational const& val, fixed_bits_info const& fbi);

        template <bool FORWARD>
        entry* refine_bits(pvar v, rational const& val, unsigned num_bits, fixed_bits_info const& fbi);

        bool refine_equal_lin(pvar v, rational const& val);

        bool refine_disequal_lin(pvar v, rational const& val);

        template<bool FORWARD>
        rational extend_by_bits(unsigned num_bits, rational const& bounds, fixed_bits_info const& fbi, vector<signed_constraint>& out_src, vector<signed_constraint>& out_side_cond) const;

        bool collect_bit_information(pvar v, bool add_conflict, fixed_bits_info& out_fbi);

        std::ostream& display_one(std::ostream& out, pvar v, entry const* e) const;
        std::ostream& display_all(std::ostream& out, pvar v, entry const* e, char const* delimiter = "") const;
        std::ostream& display_all(std::ostream& out, pvar v, layers const& ls, char const* delimiter = "") const;

        void insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k);

        void propagate(pvar v, rational const& val, ptr_vector<entry> const& reason);

        /**
         * Enter conflict state when intervals cover the full domain.
         * Try to create the forbidden interval lemma for v.
         * \param w: only intervals of bit-width w or less are relevant for the conflict.
         * \pre there are no viable values for v (determined by interval reasoning)
         */
        bool set_conflict_by_interval(pvar v, unsigned w, ptr_vector<entry>& intervals, unsigned first_interval);
        bool set_conflict_by_interval_rec(pvar v, unsigned w, entry** intervals, unsigned num_intervals, conflict& core, bool& create_lemma, clause_builder& lemma, uint_set& vars_to_explain);
        bool update_interval_conflict(pvar v, pdd const& p, entry* n, conflict& core, bool& create_lemma, clause_builder& lemma, uint_set& vars_to_explain);

        /**
         * Bitblasting-based query.
         * \return l_true on success, l_false on conflict, l_undef on resource limit
         */
        lbool find_viable_fallback(pvar v, pvar_vector const& overlaps, rational& out_lo, rational& out_hi);

        /**
         * Enter conflict state after querying the univariate solver.
         * \pre there are no viable values for v (determined by fallback solver)
         */
        bool set_conflict_by_fallback(pvar v, univariate_solver& us, svector<std::pair<pvar, sat::literal>> const& deps);

        /**
         * Find a next viable value for variable. Attempts to find two different values, to distinguish propagation/decision.
         * NOTE: out_hi is set to -1 by the fallback solver.
         * \return l_true on success, l_false on conflict, l_undef on resource limit
         */
        lbool find_viable2(pvar v, rational& out_lo, rational& out_hi, ptr_vector<entry>& out_relevant_entries);

        lbool find_on_layers(
            pvar v,
            unsigned_vector const& widths,
            pvar_vector const& overlaps,
            fixed_bits_info const& fbi,
            rational const& to_cover_lo,
            rational const& to_cover_hi,
            rational& out_val,
            ptr_vector<entry>& out_relevant_entries);

        lbool find_on_layer(
            pvar v,
            unsigned w_idx,
            unsigned_vector const& widths,
            pvar_vector const& overlaps,
            fixed_bits_info const& fbi,
            rational const& to_cover_lo,
            rational const& to_cover_hi,
            rational& out_val,
            ptr_vector<entry>& out_refine_todo,
            ptr_vector<entry>& out_relevant_entries);

        std::pair<entry*, bool> find_value(rational const& val, entry* entries);

    public:
        viable(solver& s);

        ~viable();

        // declare and remove var
        void push_var(unsigned bit_width);
        void pop_var();

        // undo adding/removing of entries
        void pop_viable();
        void push_viable();

        void pop_propagation_reason();

        /**
         * update state of viable for pvar v
         * based on affine constraints.
         * Returns true if the state has been changed.
         */
        bool intersect(pvar v, signed_constraint const& c);

        /**
         * Extract remaining variable v from p and q and try updating viable state for v.
         * NOTE: does not require a particular constraint type (e.g., we call this for ule_constraint and umul_ovfl_constraint)
         */
        bool intersect(pdd const& p, pdd const& q, signed_constraint const& c);

        /**
         * Check whether variable v has any viable values left according to m_viable.
         */
        bool has_viable(pvar v);

        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(pvar v, rational const& val);

        /**
         * Query for an upper bound literal for v together with justification.
         * On success, the conjunction of out_c implies v <= out_hi.
         * @return true if a non-trivial upper bound is found, return justifying constraints.
         */
        bool has_upper_bound(pvar v, rational& out_hi, vector<signed_constraint>& out_c);

        /**
         * Query for an lower bound literal for v together with justification.
         * On success, the conjunction of out_c implies v >= out_hi.
         * @return true if a non-trivial lower bound is found, return justifying constraints.
         */
        bool has_lower_bound(pvar v, rational& out_lo, vector<signed_constraint>& out_c);

        /**
         * Query for a maximal interval based on fixed bounds where v is forbidden.
         * On success, the conjunction of out_c implies v \not\in [out_lo; out_hi[.
         */
        bool has_max_forbidden(pvar v, signed_constraint const& c, rational& out_lo, rational& out_hi, vector<signed_constraint>& out_c);

        /**
         * Find a next viable value for variable.
         * Side effect: propagate v in the solver if only a single value is viable.
         */
        find_t find_viable(pvar v, rational& out_val);

        /** Log all viable values for the given variable.
         * (Inefficient, but useful for debugging small instances.)
         */
        void log(pvar v);

        /** Like log(v) but for all variables */
        void log();

        std::ostream& display(std::ostream& out, char const* delimiter = "") const;

        class propagation_reason {
            sat::literal const* m_begin;
            sat::literal const* m_end;
            propagation_reason(sat::literal const* begin, sat::literal const* end): m_begin(begin), m_end(end) {}
            friend class viable;
        public:
            sat::literal const* begin() const { return m_begin; }
            sat::literal const* end() const { return m_end; }
        };

        propagation_reason get_propagation_reason(pvar v) const {
            auto const& r = m_propagation_reasons[v];
            SASSERT(r.len > 0);
            sat::literal const* begin = &m_propagation_reason_storage[r.begin];
            sat::literal const* end = begin + r.len;
            return { begin, end };
        }

        std::ostream& display(std::ostream& out, pvar v, char const* delimiter = "") const;

        struct var_pp {
            viable const& v;
            pvar var;
            var_pp(viable const& v, pvar var) : v(v), var(var) {}
        };

    };

    inline std::ostream& operator<<(std::ostream& out, viable const& v) {
        return v.display(out);
    }

    inline std::ostream& operator<<(std::ostream& out, viable::var_pp const& v) {
        return v.v.display(out, v.var);
    }

}
