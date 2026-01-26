/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

#include "util/scoped_ptr_vector.h"
#include "util/dependency.h"
#include "math/dd/dd_pdd.h"
#include "math/interval/dep_intervals.h"
#include "math/lp/nla_coi.h"
#include "math/lp/int_solver.h"
#include <variant>

namespace nla {

    class core; 
    class lar_solver;
    class stellensatz2 : common {

        struct external_justification {
            u_dependency *dep = nullptr;
            external_justification(u_dependency *d) : dep(d) {}
        };
        struct assumption_justification {};
        struct addition_justification {
            lp::constraint_index left, right;
        };
        struct multiplication_poly_justification {
            lp::constraint_index ci;
            dd::pdd p;
        };
        struct multiplication_justification {
            lp::constraint_index left, right;
        };
        struct division_justification {
            lp::constraint_index ci;
            lp::constraint_index divisor;
        };
        struct substitute_justification {
            lp::constraint_index ci;
            lp::constraint_index ci_eq;            
            lpvar   v;
            dd::pdd p;
        };
        struct eq_justification {
            lp::constraint_index left;
            lp::constraint_index right;
        };
        struct gcd_justification {
            lp::constraint_index ci;
        };
        struct propagation_justification {
            svector<lp::constraint_index> cs;
        };
        struct bound_propagation_justification {
            lp::constraint_index ci; // constraint that propagated the bound
            svector<lp::constraint_index> cs; // bounds constraints used for propagation
        };

        using justification = std::variant<
            external_justification, 
            assumption_justification, 
            gcd_justification, 
            substitute_justification,
            addition_justification,
            division_justification,
            eq_justification,
            propagation_justification, 
            bound_propagation_justification,
            multiplication_poly_justification, 
            multiplication_justification>;

        struct constraint {
            dd::pdd p;
            lp::lconstraint_kind k;
        };

        class monomial_factory {
            struct eq {
                bool operator()(unsigned_vector const &a, unsigned_vector const &b) const {
                    return a == b;
                }
            };
            map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
            u_map<unsigned_vector> m_mon2vars;
            bool is_mon_var(lpvar v) const {
                return m_mon2vars.contains(v);
            }

        public:
            void reset() {
                m_vars2mon.reset();
                m_mon2vars.reset();
            }

            lpvar mk_monomial(lp::lar_solver& lra, svector<lpvar> const &vars);

            lpvar get_monomial(svector<lpvar> const &vars);

            void init(lpvar v, svector<lpvar> const &_vars);
        };

        using term_offset = std::pair<lp::lar_term, rational>;

        class solver {            
            stellensatz2 &s;
            scoped_ptr<lp::lar_solver> lra_solver;
            scoped_ptr<lp::int_solver> int_solver;
            lp::explanation m_ex;
            unsigned_vector m_internal2external_constraints;
            monomial_factory m_monomial_factory;
            lbool solve_lra();
            lbool solve_lia(); 

            void init();
            term_offset to_term_offset(dd::pdd const &p);
        public:  
            solver(stellensatz2 &s) : s(s) {};                
            lbool solve(svector<lp::constraint_index>& core);
            void update_values(vector<rational>& values);
        };

        solver m_solver;


        // factor t into x^degree*p + q, such that degree(x, q) < degree, 
        struct factorization {
            unsigned degree;
            dd::pdd p, q;
        };

        struct config {
            unsigned max_degree = 3;
            unsigned max_conflicts = UINT_MAX;
            unsigned max_constraints = UINT_MAX;
            unsigned strategy = 0;
            unsigned max_splits_per_var = 2;
        };

        struct stats {
            unsigned m_num_backtracks = 0;
            void reset() { m_num_backtracks = 0; }
        };

        struct constraint_key {
            unsigned pdd;
            lp::lconstraint_kind k;
            struct eq {
                bool operator()(constraint_key const &a, constraint_key const &b) const {
                    return a.pdd == b.pdd && a.k == b.k;
                }
            };
            struct hash {
                unsigned operator()(constraint_key const &c) const {
                    return hash_u_u(c.pdd, static_cast<unsigned>(c.k));
                }
            };
        };

        struct bound_info {
            lp::lconstraint_kind m_kind;
            rational m_value;
            unsigned m_last_bound = UINT_MAX;
            u_dependency *d = nullptr;
            dd::pdd q;  // polynomial from which the bound was derived
            dd::pdd mq; // -q
        };

        struct assignment {
            lpvar    m_var;
            bool     m_is_upper;           
        };
        unsigned    m_num_scopes = 0;
        coi m_coi;
        mutable dd::pdd_manager pddm;
        config m_config;
        stats  m_stats;
        vector<constraint> m_constraints;    // ci -> polynomial x comparison x justification
        unsigned_vector    m_levels;         // ci -> decision level of constraint
        vector<justification> m_justifications;
        vector<bound_info> m_bounds;
        monomial_factory m_monomial_factory;
        vector<rational> m_values;
        svector<lp::constraint_index> m_core;
        vector<svector<lp::constraint_index>> m_max_occurs;  // map from variable to constraints they occur.
        map<constraint_key, lp::constraint_index, constraint_key::hash, constraint_key::eq> m_constraint_index;

        // 
        // there is a default interpretation of variables. 
        // The default interpretation has the invariant that the values are within the asserted bounds of variables.        
        // Every time the default interpretation changes, the set of false constraints is updated.
        // A false constraint is conflicting if the lower and upper bounds render the constraint unfixable.
        // The solver enters the conflict stage and performs backjumping.
        // If none of the constraints are unfixable, then 
        // propagation loops over false constraints and performs bounds propagation if it merits fixes.
        // if there is no propagation, perform a decision to fix the default interpretation of a constraint.
        // the side effect of decisions and propagations is that the set of false constraints are updated.
        // 
        // Extensions:
        // - we can assign priorities to variables to choose one variable to fix over another when repairing a
        //   constraint that is false.
        // - we can incorporate backtracking instead of backjumping by replaying propagations
        unsigned_vector m_idx2bound;                    // var -> index into m_bounds
        unsigned_vector m_split_count;                  // var -> number of times variable has been split

        unsigned           m_prop_qhead = 0;            // head into propagation queue
        lp::constraint_index m_conflict = lp::null_ci;
        svector<lp::constraint_index> m_conflict_dep;

        u_dependency_manager m_dm;
        dep_intervals        m_di;
        indexed_uint_set     m_conflict_marked_ci;

        void propagate();
        bool decide(); 
        bool primal_saturate();
        void dual_saturate();
        bool can_continue_search();
        lbool search();
        lbool resolve_conflict();
        std::optional<lp::constraint_index> find_backtrack_constraint();
        void backtrack(lp::constraint_index ci, svector<lp::constraint_index> const &deps);
        constraint negate_constraint(constraint const &c);

        void init_search();
        void init_levels();
        void insert_max_var(lp::constraint_index ci);
        void pop_bound();
        void mark_dependencies(lp::constraint_index ci);
        bool should_propagate() const { return m_prop_qhead < m_polynomial_queue.size(); }
        bool should_dual_saturate() { return false; }

        // assuming variables have bounds determine if polynomial has lower/upper bounds
        void calculate_interval(scoped_dep_interval &out, dep_interval const& x, dep_interval const&lo, dep_interval const&hi);

        void reset_conflict() { m_conflict = lp::null_ci; m_conflict_dep.reset(); }
        bool is_conflict() const { return !m_conflict_dep.empty(); }
        bool is_decision(justification const& j) const { return std::holds_alternative<assumption_justification>(j); }
        bool is_decision(lp::constraint_index ci) const { return is_decision(m_justifications[ci]); }
        bool is_feasible();
        bool is_linear_conflict();

        void reset();

        indexed_uint_set m_tabu;
        unsigned_vector m_var2level, m_level2var;

        // propagation 
        struct scope {
            unsigned parents_lim, factors_lim, polynomial_lim, interval_lim, parent_constraints_lim, qhead;
        };

        struct factor_prop {
            lpvar x;
            factorization f;
            lp::constraint_index ci;
        };
        vector<scope> m_scopes;
        vector<dd::pdd> m_parent_trail;
        vector<vector<dd::pdd>> m_parents;
        vector<vector<factor_prop>> m_factors;
        vector<std::pair<dd::pdd, lp::constraint_index>> m_polynomial_queue;
        mutable unsigned_vector m_interval_trail;
        unsigned_vector m_factor_trail;
        unsigned_vector m_parent_constraints_trail;
        vector<svector<lp::constraint_index>> m_parent_constraints;
        mutable vector<ptr_vector<dep_interval>> m_intervals;
        bool_vector m_is_parent;

        void push_bound(lp::constraint_index ci);

        unsigned get_lower(lpvar v) const { return get_lower(pddm.mk_var(v)); }
        unsigned get_upper(lpvar v) const { return get_upper(pddm.mk_var(v)); }
        unsigned get_lower(dd::pdd const &p) const { return m_idx2bound.get(p.index(), UINT_MAX); }
        unsigned get_upper(dd::pdd const &p) const { return m_idx2bound.get((-p).index(), UINT_MAX); }
        

        bool has_lo(dd::pdd const &p) const { return get_lower(p) != UINT_MAX; }
        bool has_hi(dd::pdd const &p) const { return get_upper(p) != UINT_MAX; }
        bool has_lo(lpvar v) const { return has_lo(pddm.mk_var(v)); }
        bool has_hi(lpvar v) const { return has_hi(pddm.mk_var(v)); }
        bound_info const& get_lo_bound(dd::pdd const &p) const {
            SASSERT(has_lo(p));
            return m_bounds[get_lower(p)];
        }
        bound_info const& get_hi_bound(dd::pdd const &p) const {
            SASSERT(has_hi(p));
            return m_bounds[get_upper(p)];
        }
        rational lo_val(dd::pdd const &p) const { return get_lo_bound(p).m_value; }
        rational hi_val(dd::pdd const &p) const { return -get_hi_bound(p).m_value; }
        rational lo_val(lpvar v) const { return lo_val(pddm.mk_var(v)); }
        rational hi_val(lpvar v) const { return hi_val(pddm.mk_var(v)); }
        bool lo_is_strict(dd::pdd const &p) const { return get_lo_bound(p).m_kind == lp::lconstraint_kind::GT; }
        bool hi_is_strict(dd::pdd const &p) const { return get_hi_bound(p).m_kind == lp::lconstraint_kind::GT; }
        bool lo_is_strict(lpvar v) const { return lo_is_strict(pddm.mk_var(v)); }
        bool hi_is_strict(lpvar v) const { return hi_is_strict(pddm.mk_var(v)); }
        lp::constraint_index lo_constraint(dd::pdd const &p) const { return get_lower(p); }        
        lp::constraint_index hi_constraint(dd::pdd const &p) const { return get_upper(p); }        
        u_dependency *lo_dep(lpvar v) const { return get_lo_bound(pddm.mk_var(v)).d; }        
        u_dependency *hi_dep(lpvar v) const { return get_hi_bound(pddm.mk_var(v)).d; }

        lp::constraint_index lo_constraint(lpvar v) const { return get_lower(v); }
        lp::constraint_index hi_constraint(lpvar v) const { return get_upper(v); }
        bool is_fixed(lpvar v) const { return has_lo(v) && has_hi(v) && lo_val(v) == hi_val(v); }
        void move_up(lpvar v);                       
       
        struct repair_var_info {
            lp::constraint_index inf = lp::null_ci, sup = lp::null_ci, vanishing = lp::null_ci;
            rational lo, hi;
        };
        repair_var_info find_bounds(lpvar v);
        unsigned max_level(constraint const &c) const;
        unsigned get_level(justification const& j) const;
        lp::constraint_index repair_variable(lpvar v);
        bool find_split(lpvar &v, rational &r, lp::lconstraint_kind &k);
        void set_in_bounds(lpvar v);
        bool in_bounds(lpvar v) { return in_bounds(v, m_values[v]); }                              
        bool in_bounds(lpvar v, rational const &value) const;

        dd::pdd to_pdd(lpvar v);
        void init_monomial(unsigned mon_var); 
        term_offset to_term_offset(dd::pdd const &p);
        bool has_term_offset(dd::pdd const &p);

        lp::constraint_index add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j);        
        lp::constraint_index add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const &rhs, justification j);
        
        unsigned_vector antecedents(u_dependency *d) const;


        justification translate_j(std::function<lp::constraint_index(lp::constraint_index)> const &f,
                                justification const &j) const;

        // initialization
        void init_solver();
        void init_vars();
        void simplify();

        lp::constraint_index factor(lp::constraint_index ci);
        void conflict(svector<lp::constraint_index> const& core);
        lp::constraint_index vanishing(lpvar x, factorization const& f, lp::constraint_index ci);
        unsigned degree_of_var_in_constraint(lpvar v, lp::constraint_index ci) const;
        factorization factor(lpvar v, lp::constraint_index ci);  
        lp::constraint_index resolve_variable(lpvar x, lp::constraint_index ci, lp::constraint_index other_ci);
        lp::constraint_index resolve(lp::constraint_index c1, lp::constraint_index c2);

        // propagation
        void push_propagation(lp::constraint_index ci);
        void insert_parents(dd::pdd const &p, lp::constraint_index ci);
        void insert_parents(dd::pdd const &p);
        void insert_child(dd::pdd const &child, dd::pdd const &parent);
        void insert_factor(dd::pdd const &p, lpvar x, factorization const &f, lp::constraint_index ci);
        void pop_propagation(lp::constraint_index ci);
        bool is_better(dep_interval const &new_iv, dep_interval const &old_iv);      
        bool strengthen_interval(dep_interval const &new_iv, dd::pdd const &p);
        bool is_bounds_conflict(dep_interval &i);
        dep_interval const &get_interval(dd::pdd const &p) const;
        void propagate_intervals(dd::pdd const &p, lp::constraint_index ci);
        void propagate_constraint(lpvar x, lp::lconstraint_kind k, rational const &value, lp::constraint_index ci, svector<lp::constraint_index> &cs);

        // constraints

        bool propagation_cycle(lpvar v, rational const& value, lp::lconstraint_kind k, lp::constraint_index ci, svector<lp::constraint_index>& cs) const;
        bool constraint_is_true(lp::constraint_index ci) const;
        bool constraint_is_true(constraint const &c) const;
        bool constraint_is_false(lp::constraint_index ci) const;
        bool constraint_is_false(constraint const &c) const { return !constraint_is_true(c); }
        bool constraint_is_conflict(lp::constraint_index ci) const;
        bool constraint_is_conflict(constraint const &c) const;
        bool constraint_is_trivial(lp::constraint_index ci) const;
        bool constraint_is_trivial(constraint const& c) const;
        bool constraint_is_bound_conflict(lp::constraint_index ci);
        bool constraint_is_bound_conflict(lp::constraint_index ci, dep_interval const &iv);
        bool var_is_bound_conflict(lpvar v);
        bool is_bound_conflict(dd::pdd const &p);

        bool constraint_is_propagating(dep_interval const &ivp, dep_interval const& ivq, lpvar x, 
                                       svector<lp::constraint_index> &cs, lp::lconstraint_kind &k, rational &value);
            
            
        lbool sign(dd::pdd const &p);

        lp::constraint_index gcd_normalize(lp::constraint_index ci);
        lp::constraint_index assume(dd::pdd const& p, lp::lconstraint_kind k);
        lp::constraint_index add(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index multiply(lp::constraint_index ci, dd::pdd p);
        lp::constraint_index multiply(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index divide(lp::constraint_index ci, lp::constraint_index divisor, dd::pdd d);
        lp::constraint_index substitute(lp::constraint_index ci, lp::constraint_index ci_eq, lpvar v, dd::pdd p);

        static unsigned num_constraints(justification const &j);
        static lp::constraint_index get_constraint_index(justification const &j, unsigned index);

        struct justification_iterator {
            justification const& j;
            unsigned sz;
            unsigned index;

        public:
            justification_iterator(justification const &j, unsigned index) : j(j), sz(num_constraints(j)), index(index) {}
            bool operator==(justification_iterator const& other) const { return index == other.index; }
            bool operator!=(justification_iterator const& other) const { return index != other.index; }
            justification_iterator& operator++() { ++index; return *this; }
            lp::constraint_index operator*() const { return get_constraint_index(j, index); }

            static justification_iterator begin(justification const& j) { return justification_iterator(j, 0); }
            static justification_iterator end(justification const& j) { return justification_iterator(j, num_constraints(j)); }
        };

        struct justification_range {
            stellensatz2 const &s;
            justification const& j;
            justification_range(stellensatz2 const &s, justification const& j) : s(s), j(j) {}
            justification_iterator begin() const { return justification_iterator::begin(j); }
            justification_iterator end() const { return justification_iterator::end(j); }
        };

        bool is_int(svector<lp::lpvar> const& vars) const;
        bool is_int(dd::pdd const &p) const;
        bool var_is_int(lp::lpvar v) const;
        rational value(dd::pdd const& p) const;
        rational value(lp::lpvar v) const { return m_values[v]; }
        unsigned num_vars() const { return m_values.size(); }
        bool set_model();

        // lemmas
        indexed_uint_set m_constraints_in_conflict;
        void explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation &ex);
        void explain_constraint(lp::constraint_index ci, svector<lp::constraint_index> &external,
                                svector<lp::constraint_index> &assumptions);

        bool well_formed();
        bool well_formed_var(lpvar v);
        bool well_formed_constraint(unsigned ci) const;
        bool well_formed_last_constraint() const { return well_formed_constraint(m_bounds.size() - 1); }

        struct pp_j {
            stellensatz2 const &s;
            lpvar j;
            pp_j(stellensatz2 const&s, lpvar j) : s(s), j(j) {}
            std::ostream &display(std::ostream &out) const {
                return s.display_var(out, j);
            }
        };
        friend std::ostream &operator<<(std::ostream &out, pp_j const &p) {
            return p.display(out);
        }
        std::ostream& display(std::ostream& out) const;
        std::ostream& display_verbose(std::ostream &out) const;
        std::ostream& display_product(std::ostream& out, svector<lpvar> const& vars) const;
        std::ostream& display_constraint(std::ostream& out, lp::constraint_index ci) const;
        std::ostream& display_constraint(std::ostream& out, constraint const& c) const;
        std::ostream &display(std::ostream &out, justification const &j) const;
        std::ostream &display_var(std::ostream &out, lpvar j) const;
        std::ostream &display_var_range(std::ostream &out, lpvar j) const;
        std::ostream &display_lemma(std::ostream &out, lp::explanation const &ex);
        std::ostream &display(std::ostream &out, term_offset const &t) const;

    public:
        stellensatz2(core* core);
        ~stellensatz2();
        lbool saturate();

        void updt_params(params_ref const &p);
    };

}
