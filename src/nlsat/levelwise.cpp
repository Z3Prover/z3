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
#include <queue>
#include "math/polynomial/polynomial_cache.h"
#include "math/polynomial/polynomial.h"
namespace nlsat {
    
    enum prop_enum {
        ir_ord,
        an_del,
        non_null,
        ord_inv,
        sgn_inv,
        connected,
        an_sub,
        sample_holds,
        repr,
        _count 
    };

    struct levelwise::impl {
        // Utility: call fn for each distinct irreducible factor of poly
        template<typename Func>
        void for_each_distinct_factor(polynomial::polynomial_ref& poly, Func&& fn) {
            polynomial::polynomial_ref_vector factors(m_pm);
            ::nlsat::factor(poly, m_cache, factors);
            for (unsigned i = 0; i < factors.size(); i++) {
                polynomial_ref pr(m_pm);
                pr = factors.get(i);
                fn(pr);
            }
        }
        template<typename Func>
        void for_first_distinct_factor(polynomial::polynomial_ref& poly, Func&& fn) {
            polynomial::polynomial_ref_vector factors(m_pm);
            ::nlsat::factor(poly, m_cache, factors);
            polynomial_ref pr(m_pm);
            pr = factors.get(0);
            fn(pr);
        }

        // todo: consider to key polynomials in a set by using m_pm.eq
        struct property {
            prop_enum m_prop_tag;
            polynomial_ref   m_poly;
            unsigned         m_root_index = -1; // index of the root function, if applicable; -1 means unspecified
            property(prop_enum pr, polynomial_ref const & pp, int si = -1) : m_prop_tag(pr), m_poly(pp), m_root_index(si) {}
            property(prop_enum pr, polynomial_ref const & pp, polynomial::manager& pm) : m_prop_tag(pr), m_poly(pp), m_root_index(-1) {}
            // have to pass polynomial::manager& to create a polynomial_ref even with a null object
            property(prop_enum pr, polynomial::manager& pm) : m_prop_tag(pr), m_poly(polynomial_ref(pm)), m_root_index(-1) {}
            
        };
        struct compare_prop_tags {
            bool operator()(const property& a, const property& b) const {
                return a.m_prop_tag < b.m_prop_tag; // ir_ord dequed first
            }
        };
        typedef std::priority_queue<property, std::vector<property>, compare_prop_tags> property_queue;

        std::vector<property> to_vector(property_queue& pq) {
            std::vector<property> result;
            while (!pq.empty()) {
                result.push_back(pq.top());
                pq.pop();
            }
            // Restore the queue
            for (const auto& item : result) {
                pq.push(item);
            }
            return result;
        }
        
        struct root_function {
            scoped_anum val;
            indexed_root_expr ire;
            root_function(anum_manager& am, poly* p, unsigned idx, anum const& v)
                : val(am), ire{ p, idx } { am.set(val, v); }
            root_function(root_function&& other) noexcept : val(other.val.m()), ire(other.ire) { val = other.val; }
            root_function(root_function const&) = delete;
            root_function& operator=(root_function const&) = delete;
            // allow move-assignment so we can sort a vector<root_function>
            root_function& operator=(root_function&& other) noexcept { val = other.val; ire = other.ire; return *this; }
        };
        solver&                      m_solver;
        polynomial_ref_vector const& m_P;
        unsigned                     m_n; // the max of max_var(p) of all the polynomials, the level of the conflict
        unsigned                     m_level;// the current level while refining the properties
        pmanager&                    m_pm;
        anum_manager&                m_am;
        std::vector<property_queue>  m_Q; // the set of properties to prove
        std::vector<property>        m_to_refine; 
        std::vector<root_function_interval> m_I; // intervals per level (indexed by variable/level)
        bool                         m_fail = false; 
        std::vector<root_function>   m_E; // the ordered root functions on a level
        assignment const & sample() const { return m_solver.sample();}
        assignment & sample() { return m_solver.sample(); }
        polynomial::cache &          m_cache; 
       // max_x plays the role of n in algorith 1 of the levelwise paper.

        impl(solver& solver, polynomial_ref_vector const& ps, var max_x, assignment const& s, pmanager& pm, anum_manager& am, polynomial::cache & cache)
            : m_solver(solver), m_P(ps),  m_n(max_x),  m_pm(pm), m_am(am), m_cache(cache) {
            TRACE(lws, tout  << "m_n:" << m_n << "\n";);
            m_I.reserve(m_n); // cannot just resize bcs of the absence of the default constructor of root_function_interval
            for (unsigned i = 0; i < m_n; ++i)
                m_I.emplace_back(m_pm);
            m_Q.resize(m_n + 1);
        }
        // end constructor


        // helper overload so callers can pass either raw poly* or polynomial_ref
        unsigned  max_var(poly* p) { return m_pm.max_var(p); }
        unsigned  max_var(polynomial_ref const & p) { return m_pm.max_var(p); }

        // Helper to print out m_Q
        std::ostream& display(std::ostream& out) {
            out << "{\n";
            unsigned level = 0;    
            for (auto &q: m_Q) {
                if (q.empty()) { level++; continue; }
                auto q_dump = to_vector(q);
                
                out << "level:" << level << "[\n";
                for (const auto& pr : q_dump) {
                    display(out, pr) << "\n";
                }
                out << "]\n";   
                level ++; 
            }
            out << "}\n";
            return out;
        }

        bool is_irreducible(poly* p) {
            polynomial_ref_vector factors(m_pm);
            polynomial_ref pref(p, m_pm);
            ::nlsat::factor(pref, m_cache, factors);
            unsigned num_factors = factors.size();
            CTRACE(lws, num_factors != 1, ::nlsat::display(tout, m_solver, p) << std::endl;
                   tout << "{";
                   tout << "num_factors:" << num_factors << "\n";
                   ::nlsat::display(tout, m_solver, factors);
                   tout << "}\n";
                );
            
            return factors.size() == 1;            
        }
        
        /*
          prepare the initial properties
        */
        // Helper 1: scan input polynomials, add sgn_inv / an_del properties and collect polynomials at level m_n
        void collect_top_level_properties(std::vector<poly*> & ps_of_n_level) {
            for (unsigned i = 0; i < m_P.size(); ++i) {
                poly* p = m_P[i];
                polynomial_ref pref(p, m_pm);
                for_each_distinct_factor( pref, [&](const polynomial_ref& f) {
                    unsigned level = max_var(f);
                    if (level < m_n)
                        m_Q[level].push(property(prop_enum::sgn_inv, f));
                    else if (level == m_n){
                        m_Q[level].push(property(prop_enum::an_del, f));
                        ps_of_n_level.push_back(f.get());
                    }
                    else {
                        UNREACHABLE();
                    }
                });
            }
        }

        // isolate and collect algebraic roots for the given polynomials
        void collect_roots_for_ps(std::vector<poly*> const & ps_of_n_level, std::vector<std::pair<scoped_anum, poly*>> & root_vals) {
            for (poly * p : ps_of_n_level) {
                scoped_anum_vector roots(m_am);
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_n), roots);
                TRACE(lws,  
                     ::nlsat::display(tout << "roots of ", m_solver, p) << ": ";
                     ::nlsat::display(tout, roots);
                );
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
            TRACE(lws, 
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
                TRACE(lws, tout << "resultant: "; ::nlsat::display(tout, m_solver, r); tout << std::endl;);
                if (is_zero(r)) {
                    NOT_IMPLEMENTED_YET();// ambiguous resultant - not handled yet
                    return false;
                }
                for_each_distinct_factor(r, [&](const polynomial::polynomial_ref &f) {
                    m_Q[max_var(f)].push(property(prop_enum::ord_inv, f, m_pm));
                });
            }
            return true;
        }

        /*
          See comment 7.1 Generating explanation for MCSAT.
          Return Q = { sgn_inv(p) | level(p) < m_n }
          ∪ { an_del(p)  | level(p) == m_n }
          ∪ { ord_inv(resultant(p_j,p_{j+1})) for adjacent root functions }.
        */
        void init_properties() {
            std::vector<poly*> ps_of_n_level;
            collect_top_level_properties(ps_of_n_level);
            std::vector<std::pair<scoped_anum, poly*>> root_vals;
            collect_roots_for_ps(ps_of_n_level, root_vals);
            if (!add_adjacent_resultants(root_vals))
                m_fail = true;
        }
        

        // Compute root function interval from sorted roots. Assumes roots are sorted.
        void compute_interval_from_sorted_roots( // works on m_level
                                                std::vector<root_function>& roots,
                                                root_function_interval& I) {
            // default: whole line sector (-inf, +inf)
            I.section = false;
            I.l = nullptr; I.u = nullptr; I.l_index = 0; I.u_index = 0;
            if (roots.empty()) return;
            if (!sample().is_assigned(m_level)) return;
            anum const& y_val = sample().value(m_level);
            
            // find first index where roots[idx].val >= y_val
            size_t idx = 0;
            while (idx < roots.size() && m_am.compare(roots[idx].val, y_val) < 0) ++idx;
            if (idx < roots.size() && m_am.compare(roots[idx].val, y_val) == 0) {
                TRACE(lws, tout << "exact match at idx=" << idx << ", it's a section\n";);
                auto const& ire = roots[idx].ire;
                I.section = true;
                I.l = ire.p; I.l_index = ire.i;
                I.u = nullptr; I.u_index = -1; // the section is defined by the I.l
                TRACE(lws, tout << "section bound -> p="; if (I.l) m_pm.display(tout, I.l); tout << ", index=" << I.l_index << "\n";);
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

        property pop(property_queue & q) {
            property r = q.top();
            q.pop();
            return r;
        }

        //works on m_level
        bool apply_property_rules(prop_enum prop_to_avoid) {
            SASSERT (!m_fail);
            std::vector<property> avoided;
            auto& q = m_Q[m_level];
            while(!q.empty()) {
                property p = pop(q);
                if (p.m_prop_tag == prop_to_avoid) {
                    avoided.push_back(p);
                    continue;
                }
                apply_pre(p);
                if (m_fail) break;
            }
            if (m_fail)
               return false;
            for (auto & p : avoided)
                q.push(p);
            return true;
        }

         // Part B of construct_interval: build (I, E, ≼) representation for level i
         void build_representation() {
             // collect non-null polynomials (up to polynomial_manager equality)
             std::vector<const poly*> p_non_null;            
             for (auto & pr: to_vector(m_Q[m_level])) {
                 SASSERT(max_var(pr.m_poly) == m_level);
                 if (pr.m_prop_tag == prop_enum::sgn_inv
                     && !coeffs_are_zeroes_on_sample(pr.m_poly, m_pm, sample(), m_am )) {
                     TRACE(lws, tout << "adding:" << pr.m_poly.get() << "\n";);
                     poly* new_p = pr.m_poly.get();
                     auto it = std::find_if(p_non_null.begin(), p_non_null.end(),
                                            [this, new_p](const poly* q){
                                                return m_pm.eq(q, new_p);
                                            });
                     if (it == p_non_null.end())
                         p_non_null.push_back(new_p);
                 }
             }

             collect_E(p_non_null);

             std::sort(m_E.begin(), m_E.end(), [&](root_function const& a, root_function const& b){
                 return m_am.lt(a.val, b.val);
             });
             CTRACE(lws, m_E.size() > 1, tout << "sorted m_E:\n";
                   for (unsigned kk = 0; kk < m_E.size(); ++kk) {
                       display(tout, m_E[kk]) << std::endl;
                   });
             compute_interval_from_sorted_roots(m_E, m_I[m_level]);
             TRACE(lws, display(tout << "m_I[" << m_level << "]:", m_I[m_level]) << std::endl;);
         }

         // Step 1a: collect E the set of root functions on m_level
         void collect_E(std::vector<const poly*> const& p_non_null) {
             TRACE(lws, tout << "enter\n";);
             m_E.clear();
             
             for (auto const* p0 : p_non_null) {
                 auto* p = const_cast<poly*>(p0);
                 if (m_pm.max_var(p) != m_level) {
                     TRACE(lws, ::nlsat::display(tout << "strange, skipping p:", m_solver, p) << "\n";);
                     continue;
                 }
                 scoped_anum_vector roots(m_am);
                 m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_level), roots);

                 unsigned num_roots = roots.size();
                 TRACE(lws, ::nlsat::display(tout << "p:", m_solver, p) << ",";
                       tout << "roots (" << num_roots << "):";
                       for (unsigned kk = 0; kk < num_roots; ++kk) {
                           tout << " "; m_am.display(tout, roots[kk]);
                       }
                       tout << std::endl;
                 );
                 for (unsigned k = 0; k < num_roots; ++k) 
                     m_E.emplace_back(m_am, p, k + 1, roots[k]);
             }
             TRACE(lws, tout << "exit\n";);
         }

         // add a property to m_Q if an equivalent one is not already present.
         // Equivalence: same m_prop_tag and same level; require the same poly as well.
        void add_to_Q_if_new(const property & pr, unsigned level) {
             
             for (auto const & q : to_vector(m_Q[level])) {
                 if (q.m_prop_tag != pr.m_prop_tag) continue;
                 if (q.m_poly != pr.m_poly) continue;
                 if (q.m_root_index != pr.m_root_index) continue;
                 TRACE(lws, display(tout << "matched q:", q) << std::endl;);
                 return;
             }
             SASSERT(!pr.m_poly || is_irreducible(pr.m_poly));
             m_Q[level].push(pr);
         }
        
        // construct_interval: compute representation for level i and apply post rules.
        // Returns false on failure.
        // works on m_level
        bool construct_interval() {
            m_E.clear();
            if (!apply_property_rules(prop_enum::sgn_inv)) {
                return false;
            }

            TRACE(lws, display(tout << "m_Q:") << std::endl;);

            build_representation();
            SASSERT(invariant());
            return apply_property_rules(prop_enum::_count);
        }
         // handle ord_inv(discriminant_{x_{i+1}}(p)) for an_del pre-processing
         void add_ord_inv_discriminant_for(const property& p) {
            polynomial::polynomial_ref disc(m_pm);
            disc = discriminant(p.m_poly, max_var(p.m_poly));
            SASSERT(disc);
            TRACE(lws, display(tout << "p:", p) << "\n"; ::nlsat::display(tout << "discriminant by x" << max_var(p.m_poly)<< ": ", m_solver, disc) << "\n";);
            if (!is_const(disc)) {
                for_each_distinct_factor(disc, [&](polynomial::polynomial_ref f) {
                    if (coeffs_are_zeroes_on_sample(f, m_pm, sample(), m_am)) {
                        m_fail = true; // ambiguous multiplicity -- not handled yet
                        return;
                    }
                    mk_prop(prop_enum::ord_inv, f);
                });
            }
         }

        //  handle sgn_inv(leading_coefficient_{x_{i+1}}(p)) for an_del pre-processing
        void add_sgn_inv_leading_coeff_for(const property& p) {
            poly * pp = p.m_poly.get();
            unsigned lvl = max_var(p.m_poly);
            unsigned deg = m_pm.degree(pp, max_var(p.m_poly));
            if (deg > 0) {
                polynomial_ref lc(m_pm);
                lc = m_pm.coeff(pp, lvl, deg);
                if (!is_const(lc)) {
                    for_each_distinct_factor(lc, [&](polynomial::polynomial_ref f) {
                        if (coeffs_are_zeroes_on_sample(f, m_pm, sample(), m_am)) {
                            m_fail = true;
                            return;
                        }
                        else
                            mk_prop(prop_enum::sgn_inv, f, max_var(f));
                        
                    });
                } else {                    
                    SASSERT(sign(lc, sample(), m_am));
                }
            }
        }

        // Extracted helper: check preconditions for an_del property; returns true if ok, false otherwise.
        // Pre-conditions for an_del(p) per Rule 4.1
        bool precondition_on_an_del(const property& p) {
            if (!p.m_poly) {
                TRACE(lws, tout << "apply_pre: an_del with null poly -> fail" << std::endl;);
                m_fail = true;
                return false;
            }
            // If p is nullified on the sample for its level we must abort (Rule 4.1)
            if (coeffs_are_zeroes_on_sample(p.m_poly, m_pm, sample(), m_am)) {
                TRACE(lws, display(tout << "p:", p) << "\n"; tout << "Rule 4.1: polynomial nullified at sample -> failing" << std::endl;);
                m_fail = true;
                return false;
            }
            return true;
        }

        void apply_pre_an_del(const property& p) {
            if (!precondition_on_an_del(p)) return;
            unsigned p_lvl = max_var(p.m_poly);
            if (p_lvl > 0) {
                mk_prop(prop_enum::an_sub, level_t(p_lvl - 1));
                mk_prop(prop_enum::connected, level_t(p_lvl - 1));
            }
            mk_prop(prop_enum::non_null, p.m_poly);
            
            add_ord_inv_discriminant_for(p);
            if (m_fail) return;
            add_sgn_inv_leading_coeff_for(p);
        }

        // Pre-processing for connected(i) (Rule 4.11)
        void apply_pre_connected(const property & p) {
            // Rule 4.11 special-case: if the connected property refers to level 0 there's nothing to refine
            // further; just remove the property from Q and return.
            if (m_level == 0) {
                TRACE(lws, tout << "apply_pre_connected: level 0 -> erasing connected property and returning" << std::endl;);
                return;
            }

            // p.level > 0
            // Rule 4.11 precondition: when processing connected(i) we must ensure the next lower level
            // has connected(i-1) and repr(I,s) available. 
            /*
               Let Q := connected(i − 1)(R) ∧ repr(I, s)(R).
               Q, I = (sector, l, u), l ̸= −∞, u ̸= ∞, l (≼t) u, add ir_ord(≼, s)
               Q, I = (sector, l, u), l= −∞ ∨ u = ∞ 
               Q, I = (section, b) ⊢ connected(i)(R)
            */
            mk_prop(prop_enum::connected, level_t(m_level - 1));
            mk_prop(prop_enum::repr, level_t(m_level - 1));            
            if (!have_representation()) 
               return; // no change since the cell representation is not available            

            const auto& I = m_I[m_level];
            TRACE(lws, display(tout << "interval m_I[" << m_level << "]\n", I) << "\n";);
            SASSERT(I.is_sector());
            if (!I.l_inf() && !I.u_inf()) {
                mk_prop(ir_ord, level_t(m_level - 1));
            }
        }

        void apply_pre_non_null(const property& p) {
            TRACE(lws, tout << "p:"; display(tout, p) << std::endl;);
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
            unsigned level = max_var(p.m_poly);
            if (have_non_zero_const(p.m_poly, level)) {
                TRACE(lws, tout << "have a non-zero const coefficient\n";);
                return true;
            }
    
            poly* pp = p.m_poly.get();
            unsigned deg = m_pm.degree(pp, level);
            for (unsigned j = 0; j <= deg; ++j) {
                polynomial_ref coeff(m_pm);
                coeff = m_pm.coeff(pp, level, j);
                // If coefficient is a non-zero constant  non_null holds
                if(m_pm.nonzero_const_coeff(pp, level, j)) 
                    return true;
            } 
            for (unsigned j = 0; j <= deg; ++j) {
                polynomial_ref coeff(m_pm);
                coeff = m_pm.coeff(pp, level, j);
                if (sign(coeff, sample(), m_am) == 0)
                    continue;

                for_first_distinct_factor(coeff, [&](const polynomial::polynomial_ref & f) {
                    mk_prop(prop_enum::sgn_inv, f);
                });
                return true;
            }
            return false;
        }

        // Helper for Rule 4.2, subrule 1: fallback when subrule 2 does not apply.
        // sample(s)(R), degx_{i+1} (p) > 1, disc(x_{i+1} (p)(s)) ̸= 0, sgn_inv(disc(x_{i+1} (p))(R) 
        void apply_pre_non_null_fallback(const property& p) {
            // basic sanity checks
            if (!p.m_poly) {
                TRACE(lws, tout << "apply_pre_non_null_fallback: null poly -> fail" << std::endl;);
                m_fail = true;
                return;
            }

            unsigned level = max_var(p.m_poly);

            poly * pp = p.m_poly.get();
            unsigned deg = m_pm.degree(pp, level);
            // fallback applies only for degree > 1
            if (deg <= 1) return;

            // compute discriminant w.r.t. the variable at p.level
            polynomial_ref disc(m_pm);
            disc = discriminant(p.m_poly, level);
            TRACE(lws, ::nlsat::display(tout << "discriminant: ", m_solver, disc) << "\n";);

            // If discriminant evaluates to zero at the sample, we cannot proceed
            // (ambiguous multiplicity) -> fail per instruction
            if (sign(disc, sample(), m_am) == 0) {
                TRACE(lws, tout << "apply_pre_non_null_fallback: discriminant vanishes at sample -> failing" << std::endl;);
                m_fail = true;
                return;
            }
            // If discriminant is non-constant, add sign-invariance requirement for it
            if (!is_const(disc)) {
                for_each_distinct_factor(disc, [&](const polynomial::polynomial_ref & f) {
                    mk_prop(prop_enum::sgn_inv, f);
                });
            }

            // non_null is established by the discriminant being non-zero at the sample
        }

        // an_sub(R) iff R is an analitical manifold
        // Rule 4.7
        void apply_pre_an_sub(const property& p) {
            if (m_level > 0) {
                mk_prop(prop_enum::repr, level_t(m_level)) ;
                mk_prop(prop_enum::an_sub, level_t(m_level -1));
            }  
            // if level == 0 then an_sub holds - bcs an empty set is an analytical submanifold 
        }

        /*
        Rule 4.13 : the precondition holds by construction
The property repr(I, s) holds on R if and only if I.l ∈ irExpr(I.l.p, s) (if I.l ̸= −∞), I.u ∈ irExpr(I.u.p, s)
(if I.u ̸= ∞) respectively I.b ∈ irExpr(I.b.p, s) and one of the following holds:
• I = (sector, l, u), dom(θl,s ) ∩ dom(θu,s ) ⊇ R ↓[i−1] and R = {(r, r′) | r ∈ R ↓[i−1], r′ ∈ (θl,s (r), θu,s (r))};
or
• I = (sector, −∞, u), dom(θu,s ) ⊇ R ↓[i−1] and R = {(r, r′) | r ∈ R ↓[i−1], r′ ∈ (−∞, θu,s (r))}; or
• I = (sector, l, ∞), dom(θl,s ) ⊇ R ↓[i−1] and R = {(r, r′) | r ∈ R ↓[i−1], r′ ∈ (θl,s (r), ∞)}; or
• I = (sector, −∞, ∞) and R = {(r, r′) | r ∈ R ↓[i−1], r′ ∈ R}; or
• I = (section, b), dom(θb,s ) ⊇ R ↓[i−1] and R = {(r, r′) | r ∈ R ↓[i−1], r′
= θb,s (r)},
         */
        void apply_pre_repr(const property& p) {
            const auto& I = m_I[m_level];
            TRACE(lws, display(tout << "interval m_I[" << m_level << "]\n", I) << "\n";);
            mk_prop(sample_holds, level_t(m_level - 1));
            if (I.is_section()) {
                /*sample(s)(R), holds(I)(R), I = (section, b), an_del(b.p)(R) */
                mk_prop(an_del, I.l);
            } else {
                /* sample(s)(R), holds(I)(R), I = (sector, l, u), l= −∞ ∨ an_del(l.p)(R), u = ∞ ∨ an_del(u.p)(R*/
                SASSERT(I.is_sector());
                
                if (!I.l_inf())
                   mk_prop(an_del, I.l);
                if (!I.u_inf())
                   mk_prop(an_del, I.u);
            }                
        }

        void apply_pre_sample(const property& p) {
            if (m_level == 0)
                return;
            mk_prop(sample_holds, level_t(m_level - 1));
            mk_prop(prop_enum::repr, level_t(m_level - 1));
        }

        struct level_t {
            unsigned val;
            explicit level_t(unsigned lvl) { val = lvl; }
        };

        void mk_prop(prop_enum pe, level_t level) {
            if ((int)level.val == -1) return; // ignore this property
            SASSERT(pe != ord_inv);
            add_to_Q_if_new(property(pe, m_pm), level.val);
        }

        void mk_prop(prop_enum pe, const polynomial_ref& poly) {
            SASSERT(poly || pe != ord_inv);
            add_to_Q_if_new(property(pe, poly), max_var(poly));
        }
        void mk_prop(prop_enum pe, const polynomial_ref& poly, unsigned level) {
            SASSERT((int)level != -1);
            SASSERT(poly || pe != ord_inv);
            add_to_Q_if_new(property(pe, poly), level);
        }

        void apply_pre_sgn_inv(const property& p) {
            SASSERT(is_irreducible(p.m_poly));
            scoped_anum_vector roots(m_am);
            SASSERT(max_var(p.m_poly) == m_level);
            m_am.isolate_roots(p.m_poly, undef_var_assignment(sample(), m_level), roots);
            if (roots.size() == 0) {
                /*  Rule 4.6. Let i ∈ N, R ⊆ Ri, s ∈ R_{i−1}, and realRoots(p(s, xi )) = ∅. 
                sample(s)(R), an_del(p)(R) ⊢ sgn_inv(p)(R) */
                mk_prop(sample_holds, level_t(m_level - 1));
                mk_prop(prop_enum::an_del, p.m_poly, m_level);
                return;
            }
            // now we have some roots at s
            const auto &I = m_I[m_level];
            TRACE(lws, display(tout << "I:", I) << std::endl;);
            if (I.section) {
            /* Rule 4.8. Let i ∈ N>0 , R ⊆ Ri
               , s ∈ R_{i−1}
               , p ∈ Q[x1, . . . , xi ], level(p) = i, and I be a root function interval
               of level i. Assume that p is irreducible, and I = (section, b).
               Let Q := an_sub(i − 1)(R) ∧ connected(i − 1)(R) ∧ repr(I, s)(R) ∧ an_del(b.p)(R).
               Q, b.p= p ⊢ sgn_inv(p)(R)
               Q, b.p ̸= p, ord_inv(resxi (b.p, p))(R) ⊢ sgn_inv(p)(R)
            */
                mk_prop(prop_enum::an_sub, level_t(m_level - 1));
                mk_prop(prop_enum::connected, level_t(m_level - 1));
                mk_prop(prop_enum::repr, level_t(m_level - 1)); 
                mk_prop(prop_enum::an_del, polynomial_ref(m_I[m_level].l, m_pm));
                if (I.l == p.m_poly.get()) {
                    // nothing is added
                } else {
                    polynomial_ref res = resultant(polynomial_ref(I.l, m_pm), p.m_poly, m_level);
                    if (res) {
                        // Factor the resultant and add ord_inv for each distinct non-constant factor
                        for_each_distinct_factor(res, [&](polynomial::polynomial_ref f) {
                            mk_prop(prop_enum::ord_inv, f);
                        });
                    }
                }
            } else {
            /*
              Rule 4.10. Let i ∈ N>0 , R ⊆ Ri
              , s ∈ Ri−1
              , p ∈ Q[x1, . . . , xi ], level(p) = i, I be a root function interval of
              level i, ≼ be an indexed root ordering of level i, and ≼t be the reflexive and transitive closure of ≼.
              We choose l, u such that either I = (sector, l, u) or (I = (section, b) for b = l = u).
              Assume that p is irreducible, irExpr(p, s) ̸= ∅, ξ.p is irreducible for all ξ ∈ dom(≼), ≼ matches s,
              and for all ξ ∈ irExpr(p, s) it holds either ξ ≼t l or u ≼t ξ.
              sample(s)(R), repr(I, s)(R), ir_ord(≼, s)(R), an_del(p)(R) ⊢ sgn_inv(p)(R)
            */
                mk_prop(sample_holds, level_t(m_level - 1)); 
                mk_prop(repr, level_t(m_level - 1));
                mk_prop(ir_ord, level_t(m_level));
                mk_prop(an_del, p.m_poly);
            }
        }

        /*
          Rule 4.5. Let i ∈ N>0 , R ⊆ Ri
          , s ∈ Ri
          , and p ∈ Q[x1, . . . , xi ], level(p) = i. Assume that p is irreducible.
          p(s) ̸= 0, sample(s)(R), sgn_inv(p)(R) ⊢ ord_inv(p)(R)
          p(s)= 0, sample(s)(R), an_sub(i− 1)(R), connected(i)(R), sgn_inv(p)(R), an_del(p)(R) ⊢ ord_inv(p)(R)
        */
        void apply_pre_ord_inv(const property& p) {
            SASSERT(p.m_prop_tag == prop_enum::ord_inv && is_irreducible(p.m_poly));
            unsigned level = max_var(p.m_poly);
            auto sign_on_sample = sign(p.m_poly, sample(), m_am);
            mk_prop(sample_holds, level_t(level));
            if (sign_on_sample) {
                mk_prop(prop_enum::sgn_inv, p.m_poly);
            } else { // sign is zero
                mk_prop(prop_enum::an_sub, level_t(level - 1));
                mk_prop(prop_enum::connected, level_t(level));                
                mk_prop(prop_enum::sgn_inv, p.m_poly);
                mk_prop(prop_enum::an_del, p.m_poly);
            }
        }
        
        void apply_pre(const property& p) {
            TRACE(lws, tout << "apply_pre BEGIN m_Q:"; display(tout) << std::endl; 
                  display(tout << "pre p:", p) << std::endl;);
            switch (p.m_prop_tag) {
            case prop_enum::an_del:
                apply_pre_an_del(p);
                break;
            case prop_enum::connected:
                apply_pre_connected(p);
                break;
            case prop_enum::non_null:
                apply_pre_non_null(p);
                break;
            case prop_enum::an_sub:
                apply_pre_an_sub(p);
                break;
            case prop_enum::repr:
                apply_pre_repr(p);
                break;
            case sample_holds:
                apply_pre_sample(p);
                break;
            case prop_enum::sgn_inv:
                apply_pre_sgn_inv(p);
                break;
            case prop_enum::ord_inv:
                apply_pre_ord_inv(p);
                break;
            case prop_enum::ir_ord:
                apply_pre_ir_ord(p);
                break;
            default:
                display(std::cout << "not impl: p", p);
                TRACE(lws, display(tout << "not impl: p", p));
                NOT_IMPLEMENTED_YET();
                break;
            }
            TRACE(lws,  tout << "apply_pre END m_Q:"; display(tout) << std::endl;);
            SASSERT(invariant());
        }

        bool have_representation() const { return m_E.size() > 0; }
        
        void apply_pre_ir_ord(const property& p) {
            /*Rule 4.9. Let i ∈ N, R ⊆ Ri, s ∈ Ri, and ≼ be an indexed root ordering of level i + 1.
              Assume that ξ.p is irreducible for all ξ ∈ dom(≼), and that ≼ matches s.
              sample(s)(R), an_sub(i)(R), connected(i)(R), ∀ξ ∈ dom(≼). an_del(ξ.p)(R), ∀(ξ,ξ′) ∈≼. ord_inv(resx_{i+1} (ξ.p, ξ′.p))(R) ⊢ ir_ord(≼, s)(R)
             */
             if (m_level > 0) {
                mk_prop(sample_holds, level_t(m_level -1 ));
                mk_prop(an_sub, level_t(m_level - 1));
                mk_prop(connected, level_t(m_level - 1));
             }
             for (unsigned i = 0; i + 1 < m_E.size(); i++) {
                 SASSERT(max_var(m_E[i].ire.p) == max_var(m_E[i + 1].ire.p));
                 SASSERT(max_var(m_E[i].ire.p) == m_level);
                 polynomial_ref r(m_pm);
                 r = resultant(polynomial_ref(m_E[i].ire.p, m_pm), polynomial_ref(m_E[i+1].ire.p, m_pm), max_var(m_E[i].ire.p));
                 TRACE(lws, tout << "resultant of m_E[" << i<< "] and m_E[" << i+1 << "]\n"; display(tout, m_E[i]) << "\n"; display(tout, m_E[i+1])<< "\nresultant:"; 
                       ::nlsat::display(tout, m_solver, r) << "\n");
                 for_each_distinct_factor(r, [this](const polynomial_ref& f) {mk_prop(ord_inv, f);});                 
             }
        }
        
        bool invariant() {
            for (unsigned i = 0; i < m_Q.size(); i++) {
                auto qv = to_vector(m_Q[i]);
                bool level_is_ok = std::all_of(qv.begin(), qv.end(), [this, i](const property& p){
                    
                    bool r = !(p.m_poly) || (max_var(p.m_poly) == i); 
                    if (!r) {
                        display(std::cout << "bad property:", p) << std::endl;
                    }
                    return r;
                });
                if (! level_is_ok)
                    return false;
            }
            return true;
        }

        // return an empty vector on failure, otherwise returns the cell representations with intervals
        std::vector<root_function_interval> single_cell() {
            TRACE(lws, m_solver.display_assignment(tout << "sample():\n") << std::endl; ::nlsat::display(tout << "m_P:\n", m_solver, m_P) << "\n";);
            if (m_n == 0) return m_I; // we have an empty sample
            m_level = m_n;
            
            init_properties(); // initializes m_Q as a queue of properties on levels <= m_n
            SASSERT(m_E.size() == 0);
            apply_property_rules(prop_enum::_count); // reduce the level from m_n to m_n - 1 to be consumed by construct_interval
            SASSERT(m_level == m_n); 
            do {  // m_level changes from m_n - 1 to 0
                m_level--;
                if (m_fail || !construct_interval())
                    return std::vector<root_function_interval>(); // return empty
            } while (m_level != 0);
            return m_I; // the order of intervals is reversed
        }
        
        // Pretty-print helpers
        static const char* prop_name(prop_enum p) {
            switch (p) {
            case prop_enum::ir_ord:               return "ir_ord";
            case prop_enum::an_del:               return "an_del";
            case prop_enum::non_null:             return "non_null";
            case prop_enum::ord_inv:              return "ord_inv";
            case prop_enum::sgn_inv:              return "sgn_inv";
            case prop_enum::connected:            return "connected";
            case prop_enum::an_sub:               return "an_sub";
            case sample_holds:                    return "sample";
            case prop_enum::repr:                 return "repr";
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
            out << "{prop:" << prop_name(pr.m_prop_tag);
            if ((int)pr.m_root_index != -1) out   << ", m_root_index:" << pr.m_root_index;
            if (pr.m_poly) {
                out << ", poly:";
                ::nlsat::display(out, m_solver, pr.m_poly);
            }
            else {
                out << ", p:null";
            }
            out << "}";
            return out;
        }
       
        std::ostream& display(std::ostream& out, const indexed_root_expr& ire ) const {
            out << "RootExpr: p=";
            ::nlsat::display(out, m_solver, ire.p);
            out << ", root_index:" << ire.i;
            return out;
        }

        // Print the indexed root function's value. If print_approx is true print a decimal
        // approximation, otherwise print the full representation.
        std::ostream& display(std::ostream& out, const root_function& f, bool print_approx = true ) const {
            display(out << "indexed_root_function:", f.ire) << "\n" << "val:";
            if (print_approx)
                m_am.display_decimal(out, f.val);
            else
                m_am.display(out, f.val);
            return out;
        }
        
        std::ostream& display(std::ostream& out, const root_function_interval& I) const {
            return ::nlsat::display(out, m_solver, I);
        }
    };
// constructor
    levelwise::levelwise(nlsat::solver& solver, polynomial_ref_vector const& ps, var n, assignment const& s, pmanager& pm, anum_manager& am, polynomial::cache& cache)
        : m_impl(new impl(solver, ps, n, s, pm, am, cache)) {}

    levelwise::~levelwise() { delete m_impl; }

    std::vector<levelwise::root_function_interval> levelwise::single_cell() {
        return m_impl->single_cell();
    }

    bool levelwise::failed() const { return m_impl->m_fail; }
} // namespace nlsat

// Free pretty-printer for symbolic_interval
std::ostream& nlsat::display(std::ostream& out, solver& s, levelwise::root_function_interval const& I) {
    if (I.section) {
        out << "Section: ";
        if (I.l == nullptr)
            out << "(undef)";
        else {
            ::nlsat::display(out, s, I.l);
            out << "[root_index:" << I.l_index << "]";
        }
    }
    else {
        out << "Sector: (";
        if (I.l_inf())
            out << "-oo";
        else {
            ::nlsat::display(out, s, I.l);
            out << "[root_index:" << I.l_index << "]";
        }
        out << ", ";
        if (I.u_inf())
            out << "+oo";
        else {
            ::nlsat::display(out, s, I.u);
            out << "[root_index:" << I.u_index << "]";
        }
        out << ")";
    }
    return out;
}
