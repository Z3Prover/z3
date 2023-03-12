/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraint manager

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/clause.h"
#include "math/polysat/constraint.h"
#include "math/polysat/op_constraint.h"

namespace polysat {

    class constraint_dedup {
    public:
        using constraint_hash = obj_ptr_hash<constraint>;
        using constraint_eq = deref_eq<constraint>;
        using constraint_table = ptr_hashtable<constraint, constraint_hash, constraint_eq>;
        constraint_table constraints;

        using op_constraint_args_eq = default_eq<op_constraint_args>;
        using op_constraint_args_hash = obj_hash<op_constraint_args>;
        using op_constraint_expr_map = map<op_constraint_args, pvar, op_constraint_args_hash, op_constraint_args_eq>;
        op_constraint_expr_map op_constraint_expr;

        using quot_rem_args = std::optional<std::pair<pdd, pdd>>;  // NOTE: this is only wrapped in optional because table2map requires a default constructor
        using quot_rem_args_eq = default_eq<quot_rem_args>;
        struct quot_rem_args_hash {
            unsigned operator()(quot_rem_args const& args) const {
                return args ? combine_hash(args->first.hash(), args->second.hash()) : 0;
            }
        };
        using quot_rem_expr_map = map<quot_rem_args, std::pair<pvar, pvar>, quot_rem_args_hash, quot_rem_args_eq>;
        quot_rem_expr_map m_quot_rem_expr;
        vector<std::tuple<pdd, pdd, pvar, pvar>> m_div_rem_list;
    };

    // Manage constraint lifetime, deduplication, and connection to boolean variables/literals.
    class constraint_manager {
        friend class constraint;

        solver& s;

        // Constraints indexed by their boolean variable
        ptr_vector<constraint> m_bv2constraint;

        scoped_ptr_vector<constraint> m_constraints;

        constraint_dedup m_dedup;

        // Clause storage per level
        vector<vector<clause_ref>> m_clauses;

        // Association to external dependency values (i.e., external names for constraints)
        u_map<constraint*> m_external_constraints;
        unsigned m_num_external = 0;

        // Manage association of constraints to boolean variables
        void assign_bv2c(sat::bool_var bv, constraint* c);
        void erase_bv2c(constraint* c);
        constraint* get_bv2c(sat::bool_var bv) const;

        void store(constraint* c);

        constraint* dedup_store(constraint* c);
        constraint* dedup_find(constraint* c) const;

        void gc_constraints();
        void gc_clauses();

        void normalize_watch(clause& cl);
        void watch(clause& cl);
        void unwatch(clause& cl);

        void register_clause(clause* cl);

        void ensure_bvar(constraint* c);
        void erase_bvar(constraint* c);
        
        signed_constraint mk_op_constraint(op_constraint::code op, pdd const& p, pdd const& q, pdd const& r);
        pdd mk_op_term(op_constraint::code op, pdd const& p, pdd const& q);

        std::pair<pdd, pdd> div_rem_op_constraint(const pdd& p, const pdd& q);
        
    public:
        constraint_manager(solver& s);
        ~constraint_manager();

        void store(clause* cl);

        /// Release clauses at the given level and above.
        void release_level(unsigned lvl);

        /// Garbage-collect temporary constraints (i.e., those that do not have a boolean variable).
        void gc();
        bool should_gc();

        constraint* lookup(sat::bool_var var) const;
        signed_constraint lookup(sat::literal lit) const;

        /** Find constraint p == 0; returns null if it doesn't exist yet */
        signed_constraint find_eq(pdd const& p) const;
        /** Find constraint p <= q; returns null if it doesn't exist yet */
        signed_constraint find_ule(pdd const& p, pdd const& q) const;
        /** Find op_constraint; returns null if it doesn't exist yet */
        signed_constraint find_op(op_constraint::code op, pdd const& p, pdd const& q) const;
        signed_constraint find_op_pseudo_inv(pdd const& p) const;

        signed_constraint eq(pdd const& p);
        signed_constraint ule(pdd const& a, pdd const& b);
        signed_constraint ult(pdd const& a, pdd const& b);
        signed_constraint sle(pdd const& a, pdd const& b);
        signed_constraint slt(pdd const& a, pdd const& b);
        signed_constraint umul_ovfl(pdd const& p, pdd const& q);
        signed_constraint smul_ovfl(pdd const& p, pdd const& q);
        signed_constraint smul_udfl(pdd const& p, pdd const& q);
        signed_constraint bit(pdd const& p, unsigned i);

        signed_constraint elem(pdd const& t, pdd const& lo, pdd const& hi);
        signed_constraint elem(pdd const& t, interval const& i);

        std::pair<pdd, pdd> quot_rem(pdd const& a, pdd const& b);

        pdd bnot(pdd const& p);
        pdd lshr(pdd const& p, pdd const& q);
        pdd shl(pdd const& p, pdd const& q);
        pdd band(pdd const& p, pdd const& q);
        pdd bor(pdd const& p, pdd const& q);
        pdd bxor(pdd const& p, pdd const& q);
        pdd bnand(pdd const& p, pdd const& q);
        pdd bnor(pdd const& p, pdd const& q);
        pdd bxnor(pdd const& p, pdd const& q);
        pdd pseudo_inv(pdd const& p);
        
        pdd udiv(pdd const& a, pdd const& b);
        pdd urem(pdd const& a, pdd const& b);

        constraint* const* begin() const { return m_constraints.data(); }
        constraint* const* end() const { return m_constraints.data() + m_constraints.size(); }

        vector<std::tuple<pdd, pdd, pvar, pvar>> const& div_constraints() const { return m_dedup.m_div_rem_list; }

        class clause_iterator {
            friend class constraint_manager;
            using storage_t = decltype(constraint_manager::m_clauses);

            using outer_iterator = storage_t::const_iterator;
            outer_iterator outer_it;
            outer_iterator outer_end;

            using inner_iterator = storage_t::data_t::const_iterator;
            inner_iterator inner_it;
            inner_iterator inner_end;

            clause_iterator(storage_t const& cls, bool begin) {
                if (begin) {
                    outer_it = cls.begin();
                    outer_end = cls.end();
                }
                else {
                    outer_it = cls.end();
                    outer_end = cls.end();
                }
                begin_inner();
            }

            void begin_inner() {
                if (outer_it == outer_end) {
                    inner_it = nullptr;
                    inner_end = nullptr;
                }
                else {
                    inner_it = outer_it->begin();
                    inner_end = outer_it->end();
                }
            }

        public:
            clause const& operator*() const {
                return *inner_it->get();
            }

            clause_iterator& operator++() {
                ++inner_it;
                while (inner_it == inner_end && outer_it != outer_end) {
                    ++outer_it;
                    begin_inner();
                }
                return *this;
            }

            bool operator==(clause_iterator const& other) const {
                return outer_it == other.outer_it && inner_it == other.inner_it;
            }

            bool operator!=(clause_iterator const& other) const {
                return !operator==(other);
            }
        };
        clause_iterator clauses_begin() const { return clause_iterator(m_clauses, true); }
        clause_iterator clauses_end() const { return clause_iterator(m_clauses, false); }

        class clauses_t {
            constraint_manager const* m_cm;
        public:
            clauses_t(constraint_manager const& cm): m_cm(&cm) {}
            auto begin() const { return m_cm->clauses_begin(); }
            auto end() const { return m_cm->clauses_end(); }
        };
        clauses_t clauses() const { return {*this}; }
    };

}
