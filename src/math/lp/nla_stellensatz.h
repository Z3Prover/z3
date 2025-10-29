/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

#include "util/scoped_ptr_vector.h"
#include "math/lp/nla_coi.h"
#include "math/lp/int_solver.h"
#include "math/polynomial/polynomial.h"
#include <variant>

namespace nla {

    class core; 
    class lar_solver;
    class stellensatz : common {

        class solver {            
            stellensatz &s;
            scoped_ptr<lp::lar_solver> lra_solver;
            scoped_ptr<lp::int_solver> int_solver;
            lp::explanation m_ex;
            vector<ineq> m_ineqs;
            lbool solve_lra();
            lbool solve_lia(); 
            bool update_values();
            vector<std::pair<lpvar, rational>> m_to_refine;
            void saturate_basic_linearize();
        public:  
            solver(stellensatz &s) : s(s) {};                
            void init();
            lbool solve();
            lp::lar_solver &lra() { return *lra_solver; }
            lp::lar_solver const &lra() const { return *lra_solver; }
            lp::explanation &ex() { return m_ex; }
            vector<ineq> &ineqs() { return m_ineqs; }
        };

        solver m_solver;

        struct bound_assumption {
            lpvar v = lp::null_lpvar;
            lp::lconstraint_kind k;
            rational rhs;           
        };
        struct external_justification {
            u_dependency *dep = nullptr;
            external_justification(u_dependency *d) : dep(d) {}
        };
        struct internal_justification {
            u_dependency *dep = nullptr;
            internal_justification(u_dependency *d) : dep(d) {}
        };
        struct multiplication {
            lp::constraint_index ci = lp::null_ci;
            lpvar j1 = lp::null_lpvar;  // multiply ci by j1
            lpvar j2 = lp::null_lpvar;  // divide   ci by j2
            struct eq {
                bool operator()(multiplication const &a, multiplication const &b) const {
                    return a.ci == b.ci && a.j1 == b.j1 && a.j2 == b.j2;
                }
            };
            struct hash {
                unsigned operator()(multiplication const &a) const {
                    return hash_u_u(a.ci, hash_u_u(a.j1, a.j2));
                }
            };
        };
        struct multiplication_justification : public multiplication {
            vector<bound_assumption> assumptions;
        };
        struct resolvent {
            lp::constraint_index ci1 = lp::null_ci;
            lp::constraint_index ci2 = lp::null_ci;
            lpvar j = lp::null_lpvar;  // variable being resolved on
            struct eq {
                bool operator()(resolvent const &a, resolvent const &b) const {
                    return a.ci1 == b.ci1 && a.ci2 == b.ci2 && a.j == b.j;
                }
            };
            struct hash {
                unsigned operator()(resolvent const &a) const {
                    return hash_u_u(a.ci1, hash_u_u(a.ci2, a.j));
                }
            };
        };
        struct ineq_sig {
            vector<std::pair<rational, lpvar>> lhs;
            lp::lconstraint_kind k;
            rational rhs;

            struct eq {
                bool operator()(ineq_sig const &a, ineq_sig const &b) const {
                    return a.lhs == b.lhs && a.k == b.k && a.rhs == b.rhs;
                }
            };
            struct hash {

                using composite = vector<std::pair<rational, unsigned>>;

                struct khasher {
                    unsigned operator()(composite const& ) const {
                        return 12;
                    }
                };

                struct chasher {
                    unsigned operator()(composite const& c, unsigned idx) const {
                        return hash_u_u(c[idx].first.hash(), c[idx].second);
                    }
                };

                struct hash_proc {
                    unsigned operator()(composite const& c) const {
                        return get_composite_hash<composite, khasher, chasher>(c, c.size(), khasher(), chasher());
                    }
                };
                
                unsigned operator()(ineq_sig const &a) const {
                    auto h = combine_hash((unsigned)a.k, a.rhs.hash());
                    return combine_hash(h, hash_proc()(a.lhs));
                }
            };            
        };
        struct resolvent_justification : public resolvent {
            vector<bound_assumption> assumptions;
        };
        struct bound_assumptions {
            char const *rule = nullptr;
            vector<bound_assumption> bounds;
        };

        using justification = std::variant<
            external_justification, 
            internal_justification,
            multiplication_justification,
            resolvent_justification,
            bound_assumptions>;

        coi m_coi;
        scoped_ptr_vector<justification> m_justifications;
        void add_justification(lp::constraint_index ci, justification const &j) {
            VERIFY(ci == m_justifications.size());
            m_justifications.push_back(alloc(justification, j));
        }
        indexed_uint_set m_monomials_to_refine;
        indexed_uint_set m_false_constraints;  // constraints that are false in the current model
        vector<rational> m_values;
        struct eq {
            bool operator()(unsigned_vector const& a, unsigned_vector const& b) const {
                return a == b;
            }
        };
        map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
        u_map<unsigned_vector> m_mon2vars;
        bool is_mon_var(lpvar v) const { return m_mon2vars.contains(v); }
        std::pair<lpvar, rational> find_max_lex_monomial(lp::lar_term const &t) const;
        std::pair<lpvar, rational> find_max_lex_term(lp::lar_term const &t) const;
        bool is_lex_greater(svector<lpvar> const &a, svector<lpvar> const &b) const;
        bool is_subset(svector<lpvar> const &a, svector<lpvar> const &b) const;
        bool is_subset_eq(svector<lpvar> const &a, svector<lpvar> const &b) const;
        
        unsigned m_max_monomial_degree = 0;

        vector<svector<lp::constraint_index>> m_occurs; // map from variable to constraints they occur. 

        // for factoring
        small_object_allocator m_allocator;
        unsynch_mpq_manager m_qm;
        polynomial::manager m_pm;

        hashtable<multiplication, multiplication::hash, multiplication::eq> m_multiplications;
        hashtable<resolvent, resolvent::hash, resolvent::eq> m_resolvents;
        hashtable<ineq_sig, ineq_sig::hash, ineq_sig::eq> m_inequality_table;

        bool is_new_inequality(vector<std::pair<rational, lpvar>> lhs, lp::lconstraint_kind k, rational const &rhs);


        // initialization
        void init_solver();
        void init_vars();
        void init_monomial(unsigned mon_var);
        void init_occurs();
        void init_occurs(lp::constraint_index ci);

        bool constraint_is_true(lp::constraint_index ci) const;
        void insert_monomials_from_constraint(lp::constraint_index ci);

        // additional variables and monomials and constraints
        using term_offset = std::pair<lp::lar_term, rational>;  // term and its offset
        lpvar mk_monomial(svector<lp::lpvar> const& vars);
        lpvar mk_monomial(svector<lp::lpvar> const &vars, lp::lpvar j);
        lpvar mk_term(term_offset &t);

        void gcd_normalize(vector<std::pair<rational, lpvar>> &t, lp::lconstraint_kind k, rational &rhs);
        lp::constraint_index add_ineq(justification const& just, lp::lar_term &t, lp::lconstraint_kind k, rational const &rhs);
        lp::constraint_index add_ineq(justification const &just, lpvar j, lp::lconstraint_kind k,
                                      rational const &rhs);

        bool is_int(svector<lp::lpvar> const& vars) const;
        rational cvalue(lp::lar_term const &t) const;
        rational mvalue(lp::lar_term const &t) const;
        rational cvalue(svector<lpvar> const &prod) const;
        rational mvalue(svector<lpvar> const &prod) const;
        lpvar add_var(bool is_int);
        lbool add_bounds(svector<lpvar> const &vars, vector<bound_assumption> &bounds);
        void saturate_constraints();
        void saturate_constraints2();
        void eliminate(lpvar mi);
        void ext_resolve(lpvar j, lp::constraint_index lo, lp::constraint_index hi);
        std::tuple<rational, bool, bool> compute_bound(svector<lpvar> const &vars, svector<lpvar>& quot, lpvar j, rational const& coeff, lp::constraint_index ci);
        lp::constraint_index saturate_multiply(lp::constraint_index con_id, lpvar j1, lpvar j2);
        
        void resolve(lpvar j, lp::constraint_index ci1, lp::constraint_index ci2);
        void saturate_basic_linearize();
        void saturate_basic_linearize(lpvar j, rational const &val_j, svector<lpvar> const &vars,
                                      rational const &val_vars);
        void saturate_signs(lpvar j, rational const& val_j, svector<lpvar> const& vars, rational const& val_vars);
        void saturate_units(lpvar j, svector<lpvar> const &vars);
        void saturate_monotonicity(lpvar j, rational const &val_j, svector<lpvar> const &vars, rational const &val_vars);
        void saturate_monotonicity(lpvar j, rational const & val_j, lpvar x, int sign_x, lpvar y, int sign_y);
        void saturate_monotonicity(lpvar j, rational const &val_j, lpvar x, lpvar y);
        void saturate_squares(lpvar j, rational const &val_j, svector<lpvar> const &vars);

        // polynomial tricks
        uint_set m_factored_constraints;
        bool get_factors(term_offset &t, vector<std::pair<term_offset, unsigned>> &factors);
        polynomial::polynomial_ref to_poly(term_offset const &t);
        term_offset to_term(polynomial::polynomial const &p);
        bool saturate_factors(lp::constraint_index ci);
        bool saturate_factors();

        // lemmas
        void add_lemma();
        indexed_uint_set m_constraints_in_conflict;
        void explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation &ex);

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
        std::ostream& display_constraint(std::ostream& out, lp::lar_term const& lhs,
                                         lp::lconstraint_kind k, rational const& rhs) const;
        std::ostream& display(std::ostream &out, term_offset const &t) const;
        std::ostream& display(std::ostream &out, justification const &bounds) const;
        std::ostream &display_var(std::ostream &out, lpvar j) const;
        std::ostream &display_lemma(std::ostream &out, lp::explanation const &ex, vector<ineq> const &ineqs);

    public:
        stellensatz(core* core);
        lbool saturate();
    };

}
