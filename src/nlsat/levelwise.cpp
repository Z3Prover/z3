#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_assignment.h"
#include <vector>
#include <unordered_map>
#include <map>
#include <set>
#include <algorithm>
#include <memory>
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat_common.h"
namespace nlsat {

// Local enums reused from previous scaffolding
    enum class property_mapping_case : unsigned { case1 = 0, case2 = 1, case3 = 2 };    
    
    enum class prop_enum : unsigned {
        ir_ord,
        an_del,
        non_null,
        ord_inv_reducible,
        ord_inv_irreducible,
        sgn_inv_reducible,
        sgn_inv_irreducible,
        connected,
        an_sub,
        sample,
        repr,
        holds,
        _count 
    };

    unsigned prop_count() { return static_cast<unsigned>(prop_enum::_count);}
    // no score-based ordering; precedence is defined by m_p_relation only
    
    struct levelwise::impl {
        struct property {
            prop_enum prop_tag;
            polynomial_ref   poly;
            unsigned         s_idx = -1; // index of the root function, if applicable; -1 means unspecified
            unsigned         level = -1;  // -1 means unspecified
            property(prop_enum pr, polynomial_ref const & pp, int si, int lvl) : prop_tag(pr), poly(pp), s_idx(si), level(lvl) {}
            property(prop_enum pr, polynomial_ref const & pp, polynomial::manager& pm) : prop_tag(pr), poly(pp), s_idx(-1), level(pm.max_var(pp)) {}
            // have to pass polynomial::manager& to create a polynomial_ref even with a null object
            property(prop_enum pr, polynomial::manager& pm, unsigned lvl) : prop_tag(pr), poly(polynomial_ref(pm)), s_idx(-1), level(lvl) {}
            
        };
        solver& m_solver;
        polynomial_ref_vector const& m_P;
        var                          m_n;
        pmanager&                    m_pm;
        anum_manager&                m_am;
        std::vector<property>        m_Q; // the set of properties to prove
        std::vector<symbolic_interval> m_I; // intervals per level (indexed by variable/level)
        bool                         m_fail = false; 
        bool                         m_Q_changed = false; // tracks mutations to m_Q for fixed-point iteration
        // Property precedence relation stored as pairs (lesser, greater)
        std::vector<std::pair<prop_enum, prop_enum>> m_p_relation;
        // Transitive closure matrix: dom[a][b] == true iff a ▹ b (a strictly dominates b).
        // Invert edges when populating dom: greater ▹ lesser.
        std::vector<std::vector<bool>> m_prop_dom;

        assignment const & sample() const { return m_solver.sample();}
        assignment & sample() { return m_solver.sample(); }

       // max_x plays the role of n in algorith 1 of the levelwise paper.
        impl(solver& solver, polynomial_ref_vector const& ps, var max_x, assignment const& s, pmanager& pm, anum_manager& am)
            : m_solver(solver), m_P(ps), m_n(max_x),  m_pm(pm), m_am(am) {
            TRACE(levelwise, tout  << "m_n:" << m_n << "\n";);    
            init_property_relation();
        }


        // helper overload so callers can pass either raw poly* or polynomial_ref
        unsigned  max_var(poly* p) { return m_pm.max_var(p); }
        unsigned  max_var(polynomial_ref const & p) { return m_pm.max_var(p); }

        // Helper to print out m_Q
        std::ostream& display(std::ostream& out) const {
            out << "m_Q: [\n";
            for (const auto& pr : m_Q) {
                display(out, pr);
                out << "\n";
            }
            out << "]\n";
            return out;
        }
        
#ifdef Z3DEBUG
        bool check_prop_init() {
            for (unsigned k = 0; k < prop_count(); ++k)
                if (m_prop_dom[k][k])
                    return false;
            return !dominates(prop_enum::ord_inv_irreducible, prop_enum::non_null);
        }
#endif
        
        void init_property_relation() {
            m_p_relation.clear();
            auto add = [&](prop_enum lesser, prop_enum greater) { m_p_relation.emplace_back(lesser, greater); };
            // m_p_relation stores edges (lesser -> greater). 
            // The edges below follow Figure 8. Examples include: an_del -> ir_ord, sample -> ir_ord.
            add(prop_enum::holds,   prop_enum::repr);
            add(prop_enum::repr,    prop_enum::sample);
            add(prop_enum::sample,  prop_enum::an_sub);
            add(prop_enum::an_sub,  prop_enum::connected);
            // connected < sgn_inv_*
            add(prop_enum::connected, prop_enum::sgn_inv_reducible);
            add(prop_enum::connected, prop_enum::sgn_inv_irreducible);
            // sgn_inv_* < ord_inv_* (same reducibility)
            add(prop_enum::sgn_inv_reducible,   prop_enum::ord_inv_reducible);
            add(prop_enum::sgn_inv_irreducible, prop_enum::ord_inv_irreducible);
            // ord_inv_* < non_null

            add(prop_enum::ord_inv_reducible,   prop_enum::non_null);
            add(prop_enum::ord_inv_irreducible, prop_enum::non_null);
            // non_null < an_del
            add(prop_enum::non_null, prop_enum::an_del);
            // an_del < ir_ord
            add(prop_enum::an_del,    prop_enum::ir_ord);
            // Additional explicit edge from Fig 8
            add(prop_enum::sample,    prop_enum::ir_ord);

            // Build transitive closure matrix for quick comparisons
            unsigned N = prop_count();
            m_prop_dom.assign(N, std::vector<bool>(N, false));
            for (auto const& pr : m_p_relation) {
                unsigned lesser  = static_cast<unsigned>(pr.first);
                unsigned greater = static_cast<unsigned>(pr.second);
                // Build dominance relation as: greater ▹ lesser
                m_prop_dom[greater][lesser] = true;
            }
            // Floyd-Warshall style closure on a tiny fixed-size set
            for (unsigned k = 0; k < N; ++k)
                for (unsigned i = 0; i < N; ++i)
                    if (m_prop_dom[i][k])
                        for (unsigned j = 0; j < N; ++j)
                            if (m_prop_dom[k][j])
                                m_prop_dom[i][j] = true;

#ifdef Z3DEBUG
            SASSERT(check_prop_init());
#endif            
        }

        /*
          Short: build the initial property set Q so the one-cell algorithm can generalize the
          conflict around the current sample. The main goal is to eliminate raw input polynomials
          whose main variable is x_{m_n} (i.e. level == m_n) by replacing them with properties.

          Strategy:
          - For factors with level < m_n: add sgn_inv(p) to Q (sign-invariance).
          - For factors with level == m_n: add an_del(p) and isolate their indexed roots over the sample;
          sort those roots and for each adjacent pair coming from distinct polynomials add
          ord_inv(resultant(p_j, p_{j+1})) to Q.
          - If any constructed polynomial (resultant, discriminant, etc.) is nullified on the sample,
          fail immediately.

          Result: Q = { sgn_inv(p) | level(p) < m_n }
          ∪ { an_del(p)  | level(p) == m_n }
          ∪ { ord_inv(resultant(p_j,p_{j+1})) for adjacent roots }.
        */
        // Helper 1: scan input polynomials, add sgn_inv / an_del properties and collect polynomials at level m_n
        void collect_level_properties(std::vector<poly*> & ps_of_n_level) {
            for (unsigned i = 0; i < m_P.size(); ++i) {
                poly* p = m_P[i];
                unsigned level = max_var(p);
                if (level < m_n)
                    m_Q.push_back(property(prop_enum::sgn_inv_irreducible, polynomial_ref(p, m_pm), /*s_idx*/0u, /* level */ level));
                else if (level == m_n){
                    m_Q.push_back(property(prop_enum::an_del, polynomial_ref(p, m_pm), /* s_idx */ -1, level));
                    ps_of_n_level.push_back(p);
                }
                else {
                    SASSERT(level <= m_n);
                }
            }
        }

        // Helper 2: isolate and collect algebraic roots for the given polynomials
        void collect_roots_for_ps(std::vector<poly*> const & ps_of_n_level, std::vector<std::pair<scoped_anum, poly*>> & root_vals) {
            for (poly * p : ps_of_n_level) {
                scoped_anum_vector roots(m_am);
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_n), roots);
                unsigned num_roots = roots.size();
                for (unsigned k = 0; k < num_roots; ++k) {
                    scoped_anum v(m_am);
                    m_am.set(v, roots[k]);
                    root_vals.emplace_back(std::move(v), p);
                }
            }
        }

        // Helper 3: given collected roots (possibly unsorted), sort them, and add ord_inv(resultant(...))
        // for adjacent roots coming from different polynomials. Avoid adding the same unordered pair twice.
        // Returns false on failure (e.g. when encountering an ambiguous zero resultant).
        bool add_adjacent_resultants(std::vector<std::pair<scoped_anum, poly*>> & root_vals) {
            if (root_vals.size() < 2) return true;
            std::sort(root_vals.begin(), root_vals.end(), [&](auto const & a, auto const & b){ return m_am.lt(a.first, b.first); });
            std::set<std::pair<unsigned,unsigned>> added_pairs;
            TRACE(levelwise, 
                tout << "root_vals:";
                for (const auto& rv : root_vals) {
                    tout << " [";
                    m_am.display(tout, rv.first);
                    if (rv.second) {
                        tout << ", poly: ";
                        ::nlsat::display(tout, m_solver, polynomial_ref(rv.second, m_pm));
                    }
                    tout << "]";
                }
                tout << std::endl;
            );
            for (size_t j = 0; j + 1 < root_vals.size(); ++j) {
                poly* p1 = root_vals[j].second;
                poly* p2 = root_vals[j+1].second;
                if (p1 == p2) continue; // delineability of p1 handled by an_del
                unsigned id1 = polynomial::manager::id(polynomial_ref(p1, m_pm));
                unsigned id2 = polynomial::manager::id(polynomial_ref(p2, m_pm));
                std::pair<unsigned,unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
                if (added_pairs.find(key) != added_pairs.end())
                    continue;
                added_pairs.insert(key);
                polynomial_ref r(m_pm);
                r = resultant(polynomial_ref(p1, m_pm), polynomial_ref(p2, m_pm), m_n);
                if (is_const(r)) continue;
                TRACE(levelwise, tout << "resultant: "; ::nlsat::display(tout, m_solver, r); tout << std::endl;);
                if (is_zero(r)) {
                    NOT_IMPLEMENTED_YET();// ambiguous resultant - not handled yet
                    return false;
                }
                // Instead of adding property with r, add property with irreducible factors of r
                polynomial::factors factors(m_pm);
                factor(r, factors);
                for (unsigned i = 0; i < factors.distinct_factors(); ++i) {
                    polynomial_ref f(m_pm);
                    f = factors[i];
                    m_Q.push_back(property(prop_enum::ord_inv_irreducible, f, m_pm));
                }
            }
            return true;
        }

        /*
          Return Q = { sgn_inv(p) | level(p) < m_n }
          ∪ { an_del(p)  | level(p) == m_n }
          ∪ { ord_inv(resultant(p_j,p_{j+1})) for adjacent root functions }.
        */
        void seed_properties() {
            std::vector<poly*> ps_of_n_level;
            collect_level_properties(ps_of_n_level);
            std::vector<std::pair<scoped_anum, poly*>> root_vals;
            collect_roots_for_ps(ps_of_n_level, root_vals);
            if (!add_adjacent_resultants(root_vals))
                m_fail = true;
        }
        
        // Internal carrier to keep root value paired with indexed root expr
        struct root_item_t {
            scoped_anum val;
            indexed_root_expr ire;
            root_item_t(anum_manager& am, poly* p, unsigned idx, anum const& v)
                : val(am), ire{ p, idx } { am.set(val, v); }
            root_item_t(root_item_t&& other) noexcept : val(other.val.m()), ire(other.ire) { val = other.val; }
            root_item_t(root_item_t const&) = delete;
            root_item_t& operator=(root_item_t const&) = delete;
            // allow move-assignment so we can sort a vector<root_item_t>
            root_item_t& operator=(root_item_t&& other) noexcept { val = other.val; ire = other.ire; return *this; }
        };

        // Compute symbolic interval from sorted roots. Assumes roots are sorted.
        void compute_interval_from_sorted_roots(unsigned i,
                                                std::vector<root_item_t>& roots,
                                                symbolic_interval& I) {
            // default: whole line sector (-inf, +inf)
            I.section = false;
            I.l = nullptr; I.u = nullptr; I.l_index = 0; I.u_index = 0;

            var y = i;
            if (!sample().is_assigned(y))
                return;
            anum const& y_val = sample().value(y);
            if (roots.empty()) return;

            // find first index where roots[idx].val >= y_val
            size_t idx = 0;
            while (idx < roots.size() && m_am.compare(roots[idx].val, y_val) < 0) ++idx;

            if (idx < roots.size() && m_am.compare(roots[idx].val, y_val) == 0) {
                // sample matches a root value -> section
                // find start of equal-valued group
                size_t start = idx;
                while (start > 0 && m_am.compare(roots[start-1].val, roots[idx].val) == 0) --start;
                auto const& ire = roots[start].ire;
                I.section = true;
                I.l = ire.p; I.l_index = ire.i;
                I.u = nullptr; I.u_index = 0;
                return;
            }

            // sector: lower bound is last root with val < y, upper bound is first root with val > y
            if (idx > 0) {
                // find start of equal-valued group for lower bound
                size_t start = idx - 1;
                while (start > 0 && m_am.compare(roots[start-1].val, roots[start].val) == 0) --start;
                auto const& ire = roots[start].ire;
                I.l = ire.p; I.l_index = ire.i;
            }
            if (idx < roots.size()) {
                size_t start = idx;
                while (start > 0 && m_am.compare(roots[start-1].val, roots[start].val) == 0) --start;
                auto const& ire = roots[start].ire;
                I.u = ire.p; I.u_index = ire.i;
            }
        }


        // Step 1b/2: old bucket-based helpers removed. The implementation now uses
        // compute_interval_from_sorted_roots which operates
        // directly on a sorted vector<root_item_t>.
        // Part A of construct_interval: apply pre-conditions (line 8-11 scaffolding)
        bool apply_property_rules(unsigned i, prop_enum prop_to_avoid, bool has_repr) {
             // Iterate until no mutation to m_Q occurs (fixed-point). We avoid copying m_Q
             // by using a change flag that is set by mutating helpers (add_to_Q_if_new / erase_from_Q).
             if (m_fail) return false;
             do {
                 m_Q_changed = false;
                 std::vector<property> to_refine = greatest_to_refine(i, prop_to_avoid);
                 TRACE(levelwise, display(tout << "to_refine properties:", to_refine);); 
                 for (const auto& p : to_refine) {
                    apply_pre(p, has_repr);
                    if (m_fail) return false;
                 }
             } while (m_Q_changed && !m_fail);
             return !m_fail;
         }

         // Part B of construct_interval: build (I, E, ≼) representation for level i
         void build_representation(unsigned i) {
             std::vector<const poly*> p_non_null;
             for (const auto & pr: m_Q) {
                 if (pr.prop_tag == prop_enum::sgn_inv_irreducible && max_var(pr.poly) == i && 
                     !coeffs_are_zeroes_on_sample(pr.poly, m_pm, sample(), m_am ))
                     p_non_null.push_back(pr.poly.get());
             }
             std::vector<root_item_t> roots;
             std::vector<indexed_root_expr> E;
             collect_E_and_roots(p_non_null, i, E, roots);
             // Ensure m_I can hold interval for this level
             if (m_I.size() <= i) m_I.resize(i+1);
             std::sort(roots.begin(), roots.end(), [&](root_item_t const& a, root_item_t const& b){
                 return m_am.lt(a.val, b.val);
             });
             compute_interval_from_sorted_roots(i, roots, m_I[i]);
         }

         std::vector<property> greatest_to_refine(unsigned level, prop_enum prop_to_avoid) {
             // Collect candidates on current level, excluding sgn_inv_irreducible
             std::vector<property> cand;
             cand.reserve(m_Q.size());
             for (const auto& q : m_Q)
                 if (q.level == level && q.prop_tag != prop_to_avoid)
                     cand.push_back(q);
             if (cand.empty()) return {};

             // Determine maxima w.r.t. ▹ using the transitive closure matrix
             // Dominance requires the same polynomial in both compared properties
             std::vector<bool> dominated(cand.size(), false);
             for (size_t i = 0; i < cand.size(); ++i) {
                 for (size_t j = 0; j < cand.size(); ++j) {
                     if (i != j && dominates(cand[j], cand[i])) {
                         dominated[i] = true;
                         break;
                     }
                 }
             }
             auto poly_id = [cand](unsigned i) { return cand[i].poly == nullptr? UINT_MAX: polynomial::manager::id(cand[i].poly);};
             // Extract non-dominated (greatest) candidates; keep deterministic order by (poly id, prop enum)
             struct Key { unsigned pid; unsigned pprop; size_t idx; };
             std::vector<Key> keys;
             keys.reserve(cand.size());
             for (size_t i = 0; i < cand.size(); ++i) {
                 if (!dominated[i]) {
                     keys.push_back(Key{ poly_id(i), static_cast<unsigned>(cand[i].prop_tag), i });
                 }
             }
             std::sort(keys.begin(), keys.end(), [](Key const& a, Key const& b){
                 if (a.pid != b.pid) return a.pid < b.pid;
                 return a.pprop < b.pprop;
             });
             std::vector<property> ret;
             ret.reserve(keys.size());
             for (auto const& k : keys) ret.push_back(cand[k.idx]);
             return ret;
         }

         // Step 1a: collect E and root values
         void collect_E_and_roots(std::vector<const poly*> const& P_non_null,
                                  unsigned i,
                                  std::vector<indexed_root_expr>& E,
                                  std::vector<root_item_t>& roots_out) {
             var y = i;
             for (auto const* p0 : P_non_null) {
                 auto* p = const_cast<poly*>(p0);
                 if (m_pm.max_var(p) != y)
                     continue;
                 scoped_anum_vector roots(m_am);
                 m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), y), roots);

                 unsigned num_roots = roots.size();
                 TRACE(levelwise,
                       tout << "roots (" << num_roots << "):";
                       for (unsigned kk = 0; kk < num_roots; ++kk) {
                           tout << " "; m_am.display(tout, roots[kk]);
                       }
                       tout << std::endl;
                 );
                 for (unsigned k = 0; k < num_roots; ++k) {
                     E.push_back(indexed_root_expr{ p, k + 1 });
                     roots_out.emplace_back(m_am, p, k + 1, roots[k]);
                 }
             }
         }

         // Helper: add a property to m_Q if an equivalent one is not already present.
         // Equivalence: same prop_tag and same level; if pr.poly is non-null, require the same poly as well.
         void add_to_Q_if_new(const property & pr) {
             for (auto const & q : m_Q) {
                 if (q.prop_tag != pr.prop_tag) continue;
                 if (q.level != pr.level) continue;
                 if (pr.poly) {
                     if (q.poly == pr.poly) return;
                     else continue;
                 }
                 // pr.poly is null -> match by prop_tag + level only
                 return;
             }
             m_Q.push_back(pr);
             m_Q_changed = true;
         }

         void remove_level_i_from_Q(std::vector<property> & Q, unsigned i) {
             Q.erase(std::remove_if(Q.begin(), Q.end(),
                                    [i](const property &p) { return p.level == i; }),
             Q.end());
         }

         void erase_from_Q(const property& p) {
             auto it = std::find_if(m_Q.begin(), m_Q.end(), [&](const property & q) {
                 return q.prop_tag == p.prop_tag && q.poly == p.poly && q.level == p.level && q.s_idx == p.s_idx;
             });
             SASSERT(it != m_Q.end());
             m_Q.erase(it);
             m_Q_changed = true;
         }
        
        // construct_interval: compute representation for level i and apply post rules.
        // Returns true on failure.
        bool construct_interval(unsigned i) {
            if (!apply_property_rules(i, prop_enum::sgn_inv_irreducible, false)) {
                return true;
            }

            build_representation(i);
            // apply post-processing that may rely on the representation being present
            if (!apply_property_rules(i, prop_enum(prop_enum::holds), true))
                return true;

            // remove properties at level i from m_Q (they are consumed by this level)
            remove_level_i_from_Q(m_Q, i);
            return m_fail;
        }
         // Extracted helper: handle ord_inv(discriminant_{x_{i+1}}(p)) for an_del pre-processing
         void add_ord_inv_discriminant_for(const property& p) {
             polynomial_ref disc(m_pm);
             disc = discriminant(p.poly, p.level);
             TRACE(levelwise, ::nlsat::display(tout << "discriminant: ", m_solver, disc) << "\n";);
             if (!is_const(disc)) {
                 if (coeffs_are_zeroes_on_sample(disc, m_pm, sample(), m_am)) {
                     m_fail = true; // ambiguous multiplicity -- not handled yet
                     NOT_IMPLEMENTED_YET();
                     return;
                 }
                 else {
                     unsigned lvl = max_var(disc);
                     add_to_Q_if_new(property(prop_enum::ord_inv_irreducible, disc, /*s_idx*/ 0u, lvl));
                 }
             }
         }

        // Extracted helper: handle sgn_inv(leading_coefficient_{x_{i+1}}(p)) for an_del pre-processing
        void add_sgn_inv_leading_coeff_for(const property& p) {
            poly * pp = p.poly.get();
            unsigned deg = m_pm.degree(pp, p.level);
            if (deg > 0) {
                polynomial_ref lc(m_pm);
                lc = m_pm.coeff(pp, p.level, deg);
                if (!is_const(lc)) {
                    if (coeffs_are_zeroes_on_sample(lc, m_pm, sample(), m_am)) {
                        NOT_IMPLEMENTED_YET(); // leading coeff vanished as polynomial -- not handled yet
                    }
                    else {
                        unsigned lvl = max_var(lc);
                        add_to_Q_if_new(property(prop_enum::sgn_inv_irreducible, lc, /*s_idx*/ 0u, lvl));
                    }
                }
            }
        }

        // Extracted helper: check preconditions for an_del property; returns true if ok, false otherwise.
        bool precondition_on_an_del(const property& p) {
            if (!p.poly) {
                TRACE(levelwise, tout << "apply_pre: an_del with null poly -> fail" << std::endl;);
                m_fail = true;
                return false;
            }
            if (p.level == static_cast<unsigned>(-1)) {
                TRACE(levelwise, tout << "apply_pre: an_del with unspecified level -> skip" << std::endl;);
                NOT_IMPLEMENTED_YET();
                return false;
            }
            // If p is nullified on the sample for its level we must abort (Rule 4.1)
            if (coeffs_are_zeroes_on_sample(p.poly, m_pm, sample(), m_am)) {
                TRACE(levelwise, tout << "Rule 4.1: polynomial nullified at sample -> failing" << std::endl;);
                m_fail = true;
                NOT_IMPLEMENTED_YET();
                return false;
            }
            return true;
        }

        void apply_pre_an_del(const property& p) {
            if (!precondition_on_an_del(p)) return;

            // Pre-conditions for an_del(p) per Rule 4.1
            unsigned lvl = (p.level > 0) ? p.level - 1 : 0;
            add_to_Q_if_new(property(prop_enum::an_sub, m_pm, lvl));
            add_to_Q_if_new(property(prop_enum::connected, m_pm, lvl));
            add_to_Q_if_new(property(prop_enum::non_null, p.poly, p.s_idx, p.level));
            
            add_ord_inv_discriminant_for(p);
            if (m_fail) return;
            add_sgn_inv_leading_coeff_for(p);
            erase_from_Q(p);
        }

        // Pre-processing for connected(i) (Rule 4.11)
        void apply_pre_connected(const property & p, bool has_repr) {
            SASSERT(p.level != static_cast<unsigned>(-1));
            // Rule 4.11 special-case: if the connected property refers to level 0 there's nothing to refine
            // further; just remove the property from Q and return.
            if (p.level == 0) {
                TRACE(levelwise, tout << "apply_pre_connected: level 0 -> erasing connected property and returning" << std::endl;);
                erase_from_Q(p);
                return;
            }

            // p.level > 0
            // Rule 4.11 precondition: when processing connected(i) we must ensure the next lower level
            // has connected(i-1) and repr(I,s) available. Add those markers to m_Q so they propagate.

            add_to_Q_if_new(property(prop_enum::connected, m_pm, /*level*/ p.level - 1));
            add_to_Q_if_new(property(prop_enum::repr, m_pm, /*level*/ p.level - 1));            
            if (!has_repr) { 
               erase_from_Q(p);
               return; // no change since the cell representation is not available            
            }
            NOT_IMPLEMENTED_YET();
            // todo!!!! add missing preconditions
            // connected property has been processed
            erase_from_Q(p);
        }

        void apply_pre_non_null(const property& p) {
            TRACE(levelwise, tout << "apply_pre_non_null:";
                  if (p.level != static_cast<unsigned>(-1)) tout << " level=" << p.level;
                  tout << std::endl;);
            // First try subrule 1 of Rule 4.2. If it succeeds we do not apply the fallback (subrule 2).
            if (try_non_null_via_coeffs(p))
                return;
            // fallback: apply the first subrule
            apply_pre_non_null_fallback(p);
         }

        bool have_non_zero_const(const polynomial_ref& p, unsigned level) {
            unsigned deg = m_pm.degree(p, level); 
            for (unsigned j = deg; --j > 0; )
                if (m_pm.nonzero_const_coeff(p.get(), level, j))  
                    return true;

            return false;         
        }

        // Helper for Rule 4.2, subrule 2:
        // If some coefficient c_j of p is constant non-zero at the sample, or
        // if c_j evaluates non-zero at the sample and we already have sgn_inv(c_j) in m_Q,
        // then non_null(p) holds on the region represented by 'rs' (if provided).
        // Returns true if non_null was established and the property p was removed.
        bool try_non_null_via_coeffs(const property& p) {
            if (have_non_zero_const(p.poly, p.level)) {
                TRACE(levelwise, tout << "have a non-zero const coefficient\n";);
                erase_from_Q(p);
                return true;
            }
    
            poly* pp = p.poly.get();
            unsigned deg = m_pm.degree(pp, p.level);
            for (unsigned j = 0; j <= deg; ++j) {
                polynomial_ref coeff(m_pm);
                coeff = m_pm.coeff(pp, p.level, j);
                // If coefficient is constant and non-zero at sample -> non_null holds
                if (is_const(coeff)) {
                    SASSERT(m_pm.nonzero_const_coeff(pp, p.level, j));
                    continue; 
                }
                
                if (sign(coeff, sample(), m_am) == 0)
                    continue;

                polynomial::factors factors(m_pm);
                factor(coeff, factors);
                for (unsigned i = 0; i < factors.distinct_factors(); ++i) {
                    polynomial_ref f(m_pm);
                    f = factors[i];
                    add_to_Q_if_new(property(prop_enum::sgn_inv_reducible, f, m_pm));
                }
                erase_from_Q(p);
                return true;
            }
            return false;
        }

        // Helper for Rule 4.2, subrule 1: fallback when subrule 2 does not apply.
        // sample(s)(R), degx_{i+1} (p) > 1, disc(x_{i+1} (p)(s)) ̸= 0, sgn_inv(disc(x_{i+1} (p))(R) 
        void apply_pre_non_null_fallback(const property& p) {
            // basic sanity checks
            if (!p.poly) {
                TRACE(levelwise, tout << "apply_pre_non_null_fallback: null poly -> fail" << std::endl;);
                m_fail = true;
                return;
            }
            if (p.level == static_cast<unsigned>(-1)) {
                TRACE(levelwise, tout << "apply_pre_non_null_fallback: unspecified level -> skip" << std::endl;);
                return;
            }

            poly * pp = p.poly.get();
            unsigned deg = m_pm.degree(pp, p.level);
            // fallback applies only for degree > 1
            if (deg <= 1) return;

            // compute discriminant w.r.t. the variable at p.level
            polynomial_ref disc(m_pm);
            disc = discriminant(p.poly, p.level);
            TRACE(levelwise, ::nlsat::display(tout << "discriminant: ", m_solver, disc) << "\n";);

            // If discriminant evaluates to zero at the sample, we cannot proceed
            // (ambiguous multiplicity) -> fail per instruction
            if (sign(disc, sample(), m_am) == 0) {
                TRACE(levelwise, tout << "apply_pre_non_null_fallback: discriminant vanishes at sample -> failing" << std::endl;);
                m_fail = true;
                NOT_IMPLEMENTED_YET();
                return;
            }

            // If discriminant is non-constant, add sign-invariance requirement for it
            if (!is_const(disc)) {
                unsigned lvl = max_var(disc);
                add_to_Q_if_new(property(prop_enum::sgn_inv_irreducible, disc, /*s_idx*/ 0u, lvl));
            }

            // non_null is established by the discriminant being non-zero at the sample
            erase_from_Q(p);
        }

        // an_sub(R) iff R is an analitcal manifold
        // Rule 4.7
        void apply_pre_an_sub(const property& p) {
            if (p.level > 0) {
                add_to_Q_if_new(property(prop_enum::repr, m_pm, p.level)) ;
                add_to_Q_if_new(property(prop_enum::an_sub, m_pm, p.level -1)) ;
            }  
            // if p.level == 0 then an_sub holds - bcs an empty set is an analytical submanifold 
            erase_from_Q(p);             
        }

        void apply_pre(const property& p, bool has_repr) {
            TRACE(levelwise, tout << "apply_pre BEGIN m_Q:"; display(tout) << std::endl; 
                display(tout << "pre p:", p) << std::endl;);
            switch (p.prop_tag) {
                case prop_enum::an_del:
                    apply_pre_an_del(p);
                    break;
                case prop_enum::connected:
                    apply_pre_connected(p, has_repr);
                    break;
                case prop_enum::non_null:
                    apply_pre_non_null(p);
                    break;
                case prop_enum::an_sub:
                    apply_pre_an_sub(p);
                    break;
                default:
                    NOT_IMPLEMENTED_YET();
                    break;
            }
            TRACE(levelwise,  tout << "apply_pre END m_Q:"; display(tout) << std::endl;);
        }
        // return an empty vector on failure, otherwise returns the cell representations with intervals
        std::vector<symbolic_interval> single_cell() {
            TRACE(levelwise,
                   m_solver.display_assignment(tout << "sample()") << std::endl;
                   tout << "m_P:\n";
                   for (const auto & p: m_P) {
                       ::nlsat::display(tout, m_solver, polynomial_ref(p, m_pm)) << std::endl;
                       tout << "max_var:" << m_pm.max_var(p) << std::endl;
                   }
                 );
            seed_properties(); // initializes m_Q as the set of properties on level m_n
            apply_property_rules(m_n, prop_enum::_count, false); // reduce the level by one to be consumed by construct_interval
            for (unsigned i = m_n; --i > 0; ) {
                if (!construct_interval(i))
                    return std::vector<symbolic_interval>(); // return empty
            }
            
            return m_I; // the order of intervals is reversed
        }
        
        bool dominates(const property& a, const property& b) const {
            return a.poly == b.poly && dominates(a.prop_tag, b.prop_tag);
        }
        bool dominates(prop_enum a, prop_enum b) const {
            return m_prop_dom[static_cast<unsigned>(a)][static_cast<unsigned>(b)];
        }

        // Pretty-print helpers
        static const char* prop_name(prop_enum p) {
            switch (p) {
            case prop_enum::ir_ord:               return "ir_ord";
            case prop_enum::an_del:               return "an_del";
            case prop_enum::non_null:             return "non_null";
            case prop_enum::ord_inv_reducible:    return "ord_inv_reducible";
            case prop_enum::ord_inv_irreducible:  return "ord_inv_irreducible";
            case prop_enum::sgn_inv_reducible:    return "sgn_inv_reducible";
            case prop_enum::sgn_inv_irreducible:  return "sgn_inv_irreducible";
            case prop_enum::connected:            return "connected";
            case prop_enum::an_sub:               return "an_sub";
            case prop_enum::sample:               return "sample";
            case prop_enum::repr:                 return "repr";
            case prop_enum::holds:                return "holds";
            case prop_enum::_count:               return "_count";
            }
            return "?";
        }

        std::ostream& display(std::ostream& out, std::vector<property> & prs) const {
            for (const auto &pr : prs) {
                display(out, pr) << std::endl;
            }
            return out;
        }
        

        std::ostream& display(std::ostream& out, const property & pr) const {
            out << "{prop:" << prop_name(pr.prop_tag);
            if (pr.level != -1) out   << ", level:" << pr.level;
            if (pr.s_idx != -1) out   << ", s_idx:" << pr.s_idx;
            if (pr.poly) {
                out << ", poly:";
                ::nlsat::display(out, m_solver, pr.poly);
            }
            else {
                out << ", p:null";
            }
            out << "}";
            return out;
        }
    };
// constructor
    levelwise::levelwise(nlsat::solver& solver, polynomial_ref_vector const& ps, var n, assignment const& s, pmanager& pm, anum_manager& am)
        : m_impl(new impl(solver, ps, n, s, pm, am)) {}

    levelwise::~levelwise() { delete m_impl; }

    std::vector<levelwise::symbolic_interval> levelwise::single_cell() {
        return m_impl->single_cell();
    }

} // namespace nlsat
