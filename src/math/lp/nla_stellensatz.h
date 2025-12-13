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
    class stellensatz : common {

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

        using justification = std::variant<
            external_justification, 
            assumption_justification, 
            gcd_justification, 
            substitute_justification,
            addition_justification,
            division_justification,
            eq_justification,
            propagation_justification,
            multiplication_poly_justification, 
            multiplication_justification>;

        struct constraint {
            dd::pdd p;
            lp::lconstraint_kind k;
            justification j;
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
            stellensatz &s;
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
            solver(stellensatz &s) : s(s) {};                
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
            unsigned             m_var;
            lp::lconstraint_kind m_kind;
            rational             m_value;
            unsigned m_level = 0;
            unsigned             m_last_bound = UINT_MAX;
            bool                 m_is_decision = true;
            u_dependency*        m_bound_justifications = nullptr; // index into bounds
            lp::constraint_index m_constraint_justification = lp::null_ci;
            bound_info(lpvar v, lp::lconstraint_kind k, rational const &value, unsigned level, unsigned last_bound, u_dependency *d,
                       lp::constraint_index ci)
                : m_var(v), m_kind(k), m_value(value), m_level(level), m_last_bound(last_bound), m_is_decision(false),
                  m_bound_justifications(d), m_constraint_justification(ci) {}
            bound_info(lpvar v, lp::lconstraint_kind k, rational const &value, unsigned level, unsigned last_bound)
                : m_var(v), m_kind(k), m_value(value), m_level(level), m_last_bound(last_bound), m_is_decision(true) {}
        };

        struct assignment {
            lpvar    m_var;
            bool     m_is_upper;           
        };

        trail_stack m_ctrail, m_vtrail; // constraint and variable trail
        coi m_coi;
        dd::pdd_manager pddm;
        config m_config;
        vector<constraint> m_constraints;
        monomial_factory m_monomial_factory;
        vector<rational> m_values;
        svector<lp::constraint_index> m_core;
        vector<svector<lp::constraint_index>> m_occurs;  // map from variable to constraints they occur.
        bool_vector m_has_occurs;                        // is the constraint indexed already
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
        //   
        unsigned_vector m_lower, m_upper;               // var -> index into m_bounds
        vector<bound_info> m_bounds;                    // bound index -> bound meta-data

        unsigned           m_prop_qhead = 0;            // head into propagation queue
        lp::constraint_index m_conflict = lp::null_ci;
        u_dependency *m_conflict_dep = nullptr;

        u_dependency_manager m_dm;
        dep_intervals        m_di;
        indexed_uint_set     m_conflict_marked;

        void propagate();
        bool decide(); 
        lbool search();
        lbool resolve_conflict();
        void init_search();
        void pop_bound();
        void mark_dependencies(u_dependency *d);
        bool should_propagate() const { return m_prop_qhead < m_bounds.size(); }
        bool cyclic_bound_propagation(bool is_upper, lpvar v);
        indexed_uint_set m_cyclic_visited;
        svector<std::pair<lp::constraint_index, lpvar>> m_cycle;
        bool find_cycle(svector<std::pair<lp::constraint_index, lpvar>> &cycle, unsigned bound_index, unsigned top_index);

        // assuming variables have bounds determine if polynomial has lower/upper bounds
        void interval(dd::pdd p, scoped_dep_interval &iv);

        void set_conflict(lp::constraint_index ci, u_dependency *d) {
            m_conflict = ci;
            m_conflict_dep = d;
        }
        void set_conflict(lpvar v) { 
            m_conflict_dep = m_dm.mk_join(lo_dep(v), hi_dep(v));
            m_conflict = resolve_variable(v, lo_constraint(v), hi_constraint(v));
        }
        void reset_conflict() { m_conflict = lp::null_ci; }
        bool is_conflict() const { return m_conflict != lp::null_ci; }

        indexed_uint_set m_processed;
        unsigned_vector m_var2level, m_level2var;
        bool has_lo(lpvar v) const { 
            return m_lower[v] != UINT_MAX; 
        }
        bool has_hi(lpvar v) const {
            return m_upper[v] != UINT_MAX;
        }
        rational const& lo_val(lpvar v) const {
            SASSERT(has_lo(v));
            return m_bounds[m_lower[v]].m_value;
        }
        rational const& hi_val(lpvar v) const {
            SASSERT(has_hi(v));
            return m_bounds[m_upper[v]].m_value;
        }
        lp::lconstraint_kind lo_kind(lpvar v) const { 
            SASSERT(has_lo(v));
            return m_bounds[m_lower[v]].m_kind;
        }
        lp::lconstraint_kind hi_kind(lpvar v) const {
            SASSERT(has_hi(v));
            return m_bounds[m_upper[v]].m_kind;
        }
        bool lo_is_strict(lpvar v) const {
            SASSERT(has_lo(v));
            return lo_kind(v) == lp::lconstraint_kind::GT;
        }
        bool hi_is_strict(lpvar v) const {
            SASSERT(has_hi(v));
            return hi_kind(v) == lp::lconstraint_kind::LT;
        }
        u_dependency *lo_dep(lpvar v) const { 
            SASSERT(has_lo(v)); 
            return m_bounds[m_lower[v]].m_bound_justifications; 
        }
        u_dependency *hi_dep(lpvar v) const {
            SASSERT(has_hi(v));
            return m_bounds[m_upper[v]].m_bound_justifications;
        }
        lp::constraint_index lo_constraint(lpvar v) const { return m_bounds[m_lower[v]].m_constraint_justification; }
        lp::constraint_index hi_constraint(lpvar v) const { return m_bounds[m_upper[v]].m_constraint_justification; }
        bool is_fixed(lpvar v) const { return has_lo(v) && has_hi(v) && lo_val(v) == hi_val(v); }
        void move_up(lpvar v);
                
        
       
        struct repair_var_info {
            lp::constraint_index ci = lp::null_ci, vanishing = lp::null_ci;
        };
        repair_var_info find_bounds(lpvar v);
        unsigned max_level(constraint const &c) const;
        bool repair_variable(lpvar& v, rational &r, lp::lconstraint_kind& k, lp::constraint_index& ci);
        void find_split(lpvar& v, rational& r, lp::lconstraint_kind& k, lp::constraint_index ci);
        void set_in_bounds(lpvar v);
        bool in_bounds(lpvar v) { return in_bounds(v, m_values[v]); }                              
        bool in_bounds(lpvar v, rational const &value) const;

        dd::pdd to_pdd(lpvar v);
        void init_monomial(unsigned mon_var); 
        term_offset to_term_offset(dd::pdd const &p);
        bool has_term_offset(dd::pdd const &p);

        lp::constraint_index add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j);        
        lp::constraint_index add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const &rhs, justification j);
        
        mutable unsigned_vector m_deps;
        unsigned_vector const &antecedents(u_dependency *d) const;

        // initialization
        void init_solver();
        void init_vars();
        void init_occurs();
        void init_occurs(lp::constraint_index ci);
        void init_bounds();
        void pop_constraint();
        void remove_occurs(lp::constraint_index ci);

        lp::constraint_index factor(lp::constraint_index ci);
        void conflict(svector<lp::constraint_index> const& core);
        lp::constraint_index vanishing(lpvar x, factorization const& f, lp::constraint_index ci);
        unsigned degree_of_var_in_constraint(lpvar v, lp::constraint_index ci) const;
        factorization factor(lpvar v, lp::constraint_index ci);  
        lp::constraint_index resolve_variable(lpvar x, lp::constraint_index ci, lp::constraint_index other_ci);

        bool constraint_is_true(lp::constraint_index ci) const;
        bool constraint_is_true(constraint const &c) const;
        bool constraint_is_false(lp::constraint_index ci) const;
        bool constraint_is_false(constraint const &c) const { return !constraint_is_true(c); }
        bool constraint_is_conflict(lp::constraint_index ci) const;
        bool constraint_is_conflict(constraint const &c) const;
        bool constraint_is_trivial(lp::constraint_index ci) const;
        bool constraint_is_trivial(constraint const& c) const;
        bool constraint_is_bound_conflict(constraint const &c, u_dependency*& d);
        bool constraint_is_bound_conflict(lp::constraint_index ci, u_dependency*& d) { return constraint_is_bound_conflict(m_constraints[ci], d); }
        bool var_is_bound_conflict(lpvar v) const;

        bool constraint_is_propagating(lp::constraint_index ci, u_dependency *&d, lpvar &v, rational &value, lp::lconstraint_kind& k);

        lp::constraint_index gcd_normalize(lp::constraint_index ci);
        lp::constraint_index assume(dd::pdd const& p, lp::lconstraint_kind k);
        lp::constraint_index add(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index multiply(lp::constraint_index ci, dd::pdd p);
        lp::constraint_index multiply(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index divide(lp::constraint_index ci, lp::constraint_index divisor, dd::pdd d);
        lp::constraint_index substitute(lp::constraint_index ci, lp::constraint_index ci_eq, lpvar v, dd::pdd p);

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
        bool backtrack(svector<lp::constraint_index> const& core);
        bool core_is_linear(svector<lp::constraint_index> const &core);

        bool well_formed() const;
        bool well_formed_var(lpvar v) const;
        bool well_formed_bound(unsigned bound_index) const;
        bool well_formed_last_bound() const { return well_formed_bound(m_bounds.size() - 1); }

        struct pp_j {
            stellensatz const &s;
            lpvar j;
            pp_j(stellensatz const&s, lpvar j) : s(s), j(j) {}
            std::ostream &display(std::ostream &out) const {
                return s.display_var(out, j);
            }
        };
        friend std::ostream &operator<<(std::ostream &out, pp_j const &p) {
            return p.display(out);
        }
        std::ostream& display(std::ostream& out) const;
        std::ostream& display_product(std::ostream& out, svector<lpvar> const& vars) const;
        std::ostream& display_constraint(std::ostream& out, lp::constraint_index ci) const;
        std::ostream& display_constraint(std::ostream& out, constraint const& c) const;
        std::ostream &display_bound(std::ostream &out, unsigned bound_index, unsigned& level) const;
        std::ostream &display(std::ostream &out, justification const &j) const;
        std::ostream &display_var(std::ostream &out, lpvar j) const;
        std::ostream &display_lemma(std::ostream &out, lp::explanation const &ex);
        std::ostream &display(std::ostream &out, term_offset const &t) const;

    public:
        stellensatz(core* core);
        lbool saturate();

        void updt_params(params_ref const &p);
    };

}
