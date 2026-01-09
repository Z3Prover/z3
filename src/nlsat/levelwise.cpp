#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_assignment.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "nlsat_common.h"
#include "util/z3_exception.h"

#include <algorithm>
#include <set>
#include <utility>
#include <vector>

static bool is_set(unsigned k) { return static_cast<int>(k) != -1; }

namespace nlsat {

enum relation_mode {
    biggest_cell,
    chain,
    lowest_degree
};

struct nullified_poly_exception {};

struct levelwise::impl {
    solver&                      m_solver;
    polynomial_ref_vector const& m_P;
    unsigned                     m_n;        // maximal variable we project from
    pmanager&                    m_pm;
    anum_manager&                m_am;
    polynomial::cache&           m_cache;
    std::vector<root_function_interval> m_I; // intervals for variables 0..m_n-1

    unsigned               m_level = 0;      // current level being processed
    relation_mode          m_relation_mode = chain;

    polynomial_ref_vector  m_psc_tmp;        // scratch for PSC chains
    bool                   m_fail = false;

    assignment const& sample() const { return m_solver.sample(); }

    // Utility: call fn for each distinct irreducible factor of poly
    template <typename Func>
    void for_each_distinct_factor(polynomial_ref const& poly_in, Func&& fn) {
        if (!poly_in || is_zero(poly_in) || is_const(poly_in))
            return;
        polynomial_ref poly(poly_in);
        polynomial_ref_vector factors(m_pm);
        ::nlsat::factor(poly, m_cache, factors);
        for (unsigned i = 0; i < factors.size(); ++i) {
            polynomial_ref f(factors.get(i), m_pm);
            if (!f || is_zero(f) || is_const(f))
                continue;
            fn(f);
        }
    }

    struct root_function {
        scoped_anum      val;
        indexed_root_expr ire;
        root_function(anum_manager& am, poly* p, unsigned idx, anum const& v)
            : val(am), ire{ p, idx } { am.set(val, v); }
        root_function(root_function&& other) noexcept : val(other.val.m()), ire(other.ire) { val = other.val; }
        root_function(root_function const&) = delete;
        root_function& operator=(root_function const&) = delete;
        root_function& operator=(root_function&& other) noexcept {
            val = other.val;
            ire = other.ire;
            return *this;
        }
    };

    // Root functions (Theta) and the chosen relation (≼) on a given level.
    struct relation_E {
        std::vector<root_function>              m_rfunc; // Θ: root functions on current level
        std::vector<std::pair<unsigned, unsigned>> m_pairs; // ≼ relation on indices into m_rfunc
        bool empty() const { return m_rfunc.empty() && m_pairs.empty(); }
        void clear() {
            m_pairs.clear();
            m_rfunc.clear();
        }
        void add_pair(unsigned j, unsigned k) { m_pairs.emplace_back(j, k); }
    };

    relation_E m_rel;

    impl(
        solver& solver,
        polynomial_ref_vector const& ps,
        var max_x,
        assignment const&,
        pmanager& pm,
        anum_manager& am,
        polynomial::cache& cache)
        : m_solver(solver),
          m_P(ps),
          m_n(max_x),
          m_pm(pm),
          m_am(am),
          m_cache(cache),
          m_psc_tmp(m_pm) {
        m_I.reserve(m_n);
        for (unsigned i = 0; i < m_n; ++i)
            m_I.emplace_back(m_pm);
    }

    void fail() { throw nullified_poly_exception(); }

    static void reset_interval(root_function_interval& I) {
        I.section = false;
        I.l = nullptr;
        I.u = nullptr;
        I.l_index = 0;
        I.u_index = 0;
    }

    // PSC-based discriminant: returns the first non-zero, non-constant element from the PSC chain.
    polynomial_ref psc_discriminant(polynomial_ref const& p_in, unsigned x) {
        if (!p_in || is_zero(p_in) || is_const(p_in))
            return polynomial_ref(m_pm);
        if (m_pm.degree(p_in, x) < 2)
            return polynomial_ref(m_pm);
        polynomial_ref p(p_in);
        polynomial_ref d = derivative(p, x);
        polynomial_ref_vector& chain = m_psc_tmp;
        chain.reset();
        m_cache.psc_chain(p, d, x, chain);
        polynomial_ref disc(m_pm);
        // Iterate forward: S[0] is the resultant (after reverse in psc_chain)
        for (unsigned i = 0; i < chain.size(); ++i) {
            disc = polynomial_ref(chain.get(i), m_pm);
            if (!disc || is_zero(disc))
                continue;
            if (is_const(disc))
                return polynomial_ref(m_pm);  // constant means discriminant is non-zero constant
            return disc;
        }
        return polynomial_ref(m_pm);
    }

    // PSC-based resultant: returns the first non-zero, non-constant element from the PSC chain.
    polynomial_ref psc_resultant(poly* a, poly* b, unsigned x) {
        if (!a || !b)
            return polynomial_ref(m_pm);
        polynomial_ref pa(a, m_pm);
        polynomial_ref pb(b, m_pm);
        polynomial_ref_vector& chain = m_psc_tmp;
        chain.reset();
        m_cache.psc_chain(pa, pb, x, chain);
        polynomial_ref r(m_pm);
        // Iterate forward: S[0] is the resultant (after reverse in psc_chain)
        for (unsigned i = 0; i < chain.size(); ++i) {
            r = polynomial_ref(chain.get(i), m_pm);
            if (!r || is_zero(r))
                continue;
            if (is_const(r))
                return polynomial_ref(m_pm);  // constant means polynomials are coprime
            return r;
        }
        return polynomial_ref(m_pm);
    }

    void insert_factorized(todo_set& P, polynomial_ref const& poly) {
        for_each_distinct_factor(poly, [&](polynomial_ref const& f) {
            P.insert(f.get());
        });
    }

    // Select a coefficient c of p (wrt x) such that c(s) != 0, or return null.
    polynomial_ref choose_nonzero_coeff(polynomial_ref const& p, unsigned x) {
        unsigned deg = m_pm.degree(p, x);
        polynomial_ref coeff(m_pm);
        for (int j = static_cast<int>(deg); j >= 0; --j) {
            coeff = m_pm.coeff(p, x, static_cast<unsigned>(j));
            if (!coeff || is_zero(coeff))
                continue;

            if (m_am.eval_sign_at(coeff, sample()) != 0)
                return coeff;
        }
        return polynomial_ref(m_pm);
    }

    void add_projections_for(todo_set& P, polynomial_ref const& p, unsigned x, polynomial_ref const& nonzero_coeff) {
        // Line 11 (non-null witness coefficient)
        if (nonzero_coeff && !is_const(nonzero_coeff))
            insert_factorized(P, nonzero_coeff);

        // Line 12 (disc + leading coefficient)
        insert_factorized(P, psc_discriminant(p, x));

        unsigned deg = m_pm.degree(p, x);
        polynomial_ref lc(m_pm);
        lc = m_pm.coeff(p, x, deg);
        insert_factorized(P, lc);
    }

    // Relation construction heuristics (same intent as previous implementation).
    void fill_relation_with_biggest_cell_heuristic(unsigned l, unsigned u) {
        if (is_set(l))
            for (unsigned j = 0; j < l; ++j)
                m_rel.add_pair(j, l);

        if (is_set(u))
            for (unsigned j = u + 1; j < m_rel.m_rfunc.size(); ++j)
                m_rel.add_pair(u, j);

        if (is_set(l) && is_set(u)) {
            SASSERT(l + 1 == u);
            m_rel.add_pair(l, u);
        }
    }

    void fill_relation_with_chain_heuristic(unsigned l, unsigned u) {
        if (is_set(l))
            for (unsigned j = 0; j < l; ++j)
                m_rel.add_pair(j, j + 1);

        if (is_set(u))
            for (unsigned j = u + 1; j < m_rel.m_rfunc.size(); ++j)
                m_rel.add_pair(j - 1, j);

        if (is_set(l) && is_set(u)) {
            SASSERT(l + 1 == u);
            m_rel.add_pair(l, u);
        }
    }

    void fill_relation_with_min_degree_resultant_sum(unsigned l, unsigned u) {
        auto const& rfs = m_rel.m_rfunc;
        unsigned n = rfs.size();
        if (n == 0)
            return;

        std::vector<unsigned> degs;
        degs.reserve(n);
        for (unsigned i = 0; i < n; ++i)
            degs.push_back(m_pm.degree(rfs[i].ire.p, m_level));

        if (is_set(l)) {
            unsigned min_idx = l;
            unsigned min_deg = degs[l];
            for (int j = static_cast<int>(l) - 1; j >= 0; --j) {
                unsigned jj = static_cast<unsigned>(j);
                m_rel.add_pair(jj, min_idx);
                if (degs[jj] < min_deg) {
                    min_deg = degs[jj];
                    min_idx = jj;
                }
            }
        }

        if (is_set(u)) {
            unsigned min_idx = u;
            unsigned min_deg = degs[u];
            for (unsigned j = u + 1; j < n; ++j) {
                m_rel.add_pair(min_idx, j);
                if (degs[j] < min_deg) {
                    min_deg = degs[j];
                    min_idx = j;
                }
            }
        }

        if (is_set(l) && is_set(u)) {
            SASSERT(l + 1 == u);
            m_rel.add_pair(l, u);
        }
    }

    void fill_relation_for_section(unsigned l) {
        auto const& rfs = m_rel.m_rfunc;
        unsigned n = rfs.size();
        if (n == 0)
            return;
        SASSERT(is_set(l));
        SASSERT(l < n);

        switch (m_relation_mode) {
        case biggest_cell:
            for (unsigned j = 0; j < l; ++j)
                m_rel.add_pair(j, l);
            for (unsigned j = l + 1; j < n; ++j)
                m_rel.add_pair(l, j);
            break;
        case chain:
            for (unsigned j = 0; j < l; ++j)
                m_rel.add_pair(j, j + 1);
            for (unsigned j = l + 1; j < n; ++j)
                m_rel.add_pair(j - 1, j);
            break;
        case lowest_degree: {
            std::vector<unsigned> degs;
            degs.reserve(n);
            for (unsigned i = 0; i < n; ++i)
                degs.push_back(m_pm.degree(rfs[i].ire.p, m_level));

            // For roots below l: connect each to the minimum-degree root seen so far
            unsigned min_idx_below = l;
            unsigned min_deg_below = degs[l];
            for (int j = static_cast<int>(l) - 1; j >= 0; --j) {
                unsigned jj = static_cast<unsigned>(j);
                m_rel.add_pair(jj, min_idx_below);
                if (degs[jj] < min_deg_below) {
                    min_deg_below = degs[jj];
                    min_idx_below = jj;
                }
            }

            // For roots above l: connect minimum-degree root to each subsequent root
            unsigned min_idx_above = l;
            unsigned min_deg_above = degs[l];
            for (unsigned j = l + 1; j < n; ++j) {
                m_rel.add_pair(min_idx_above, j);
                if (degs[j] < min_deg_above) {
                    min_deg_above = degs[j];
                    min_idx_above = j;
                }
            }
            break;
        }
        default:
            NOT_IMPLEMENTED_YET();
        }
    }

    void fill_relation_pairs(unsigned l, unsigned u) {
        auto const& I = m_I[m_level];
        if (I.section) {
            fill_relation_for_section(l);
            return;
        }
        switch (m_relation_mode) {
        case biggest_cell:
            fill_relation_with_biggest_cell_heuristic(l, u);
            break;
        case chain:
            fill_relation_with_chain_heuristic(l, u);
            break;
        case lowest_degree:
            fill_relation_with_min_degree_resultant_sum(l, u);
            break;
        default:
            NOT_IMPLEMENTED_YET();
        }
    }

    // Build Θ (root functions), pick I_level around sample(level), and build relation ≼.
    void build_interval_and_relation(unsigned level, polynomial_ref_vector const& level_ps) {
        m_level = level;
        m_rel.clear();
        reset_interval(m_I[level]);

        for (unsigned i = 0; i < level_ps.size(); ++i) {
            poly* p = level_ps.get(i);
            scoped_anum_vector roots(m_am);
            m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), level), roots);
            for (unsigned k = 0; k < roots.size(); ++k)
                m_rel.m_rfunc.emplace_back(m_am, p, k + 1, roots[k]);
        }

        if (m_rel.m_rfunc.empty())
            return;

        anum const& v = sample().value(level);

        // Comparator for sorting roots by value (with deterministic tie-breaking)
        auto cmp = [&](root_function const& a, root_function const& b) {
            if (a.ire.p == b.ire.p) // compare pointers
                return a.ire.i < b.ire.i; // compare root indices in the same polynomial
            auto r = m_am.compare(a.val, b.val);
            if (r)
                return r == sign_neg;            
            // Tie-break: same value - use polynomial id
            unsigned ida = m_pm.id(a.ire.p);
            unsigned idb = m_pm.id(b.ire.p);
            return ida < idb;
        };

        // Partition: roots <= v come first, then roots > v
        auto& rfs = m_rel.m_rfunc;
        auto mid = std::partition(rfs.begin(), rfs.end(), [&](root_function const& f) {
            return m_am.compare(f.val, v) <= 0;
        });
        // Sort each partition separately - O(n log n) comparisons between roots only
        std::sort(rfs.begin(), mid, cmp);
        std::sort(mid, rfs.end(), cmp);

        unsigned l_index = static_cast<unsigned>(-1);
        unsigned u_index = static_cast<unsigned>(-1);

        if (mid != rfs.begin()) {
            l_index = static_cast<unsigned>((mid - rfs.begin()) - 1);
            auto& r = *(mid - 1);
            if (m_am.eq(r.val, v)) {
                m_I[level].section = true;
                m_I[level].l = r.ire.p;
                m_I[level].l_index = r.ire.i;
            }
            else {
                m_I[level].l = r.ire.p;
                m_I[level].l_index = r.ire.i;
                if (mid != rfs.end()) {
                    u_index = l_index + 1;
                    m_I[level].u = mid->ire.p;
                    m_I[level].u_index = mid->ire.i;
                }
            }
        }
        else {
            // sample is below all roots: I = (-oo, theta_1)
            u_index = 0;
            auto& r = *mid;
            m_I[level].u = r.ire.p;
            m_I[level].u_index = r.ire.i;
        }

        fill_relation_pairs(l_index, u_index);
    }

    void add_relation_resultants(todo_set& P, unsigned level) {
        std::set<std::pair<unsigned, unsigned>> added_pairs;
        for (auto const& pr : m_rel.m_pairs) {
            poly* a = m_rel.m_rfunc[pr.first].ire.p;
            poly* b = m_rel.m_rfunc[pr.second].ire.p;
            if (!a || !b)
                continue;
            unsigned id1 = m_pm.id(a);
            unsigned id2 = m_pm.id(b);
            if (id1 == id2)
                continue;
            std::pair<unsigned, unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
            if (!added_pairs.insert(key).second)
                continue;
            insert_factorized(P, psc_resultant(a, b, level));
        }
    }

    // Top level (m_n): add resultants between adjacent roots of different polynomials.
    void add_adjacent_root_resultants(todo_set& P, polynomial_ref_vector const& top_ps) {
        std::vector<std::pair<scoped_anum, poly*>> root_vals;
        for (unsigned i = 0; i < top_ps.size(); ++i) {
            poly* p = top_ps.get(i);
            scoped_anum_vector roots(m_am);
            m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_n), roots);
            for (unsigned k = 0; k < roots.size(); ++k) {
                scoped_anum v(m_am);
                m_am.set(v, roots[k]);
                root_vals.emplace_back(std::move(v), p);
            }
        }
        if (root_vals.size() < 2)
            return;
        std::sort(root_vals.begin(), root_vals.end(), [&](auto const& a, auto const& b) {
            return m_am.lt(a.first, b.first);
        });
        std::set<std::pair<unsigned, unsigned>> added_pairs;
        for (unsigned j = 0; j + 1 < root_vals.size(); ++j) {
            poly* p1 = root_vals[j].second;
            poly* p2 = root_vals[j + 1].second;
            if (!p1 || !p2)
                continue;
            unsigned id1 = m_pm.id(p1);
            unsigned id2 = m_pm.id(p2);
            if (id1 == id2)
                continue;
            std::pair<unsigned, unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
            if (!added_pairs.insert(key).second)
                continue;
            insert_factorized(P, psc_resultant(p1, p2, m_n));
        }
    }

    void process_level(todo_set& P, unsigned level, polynomial_ref_vector const& level_ps) {
        // Line 10/11: detect nullification + pick a non-zero coefficient witness per p.
        std::vector<polynomial_ref> witnesses;
        witnesses.reserve(level_ps.size());
        for (unsigned i = 0; i < level_ps.size(); ++i) {
            polynomial_ref p(level_ps.get(i), m_pm);
            polynomial_ref w = choose_nonzero_coeff(p, level);
            if (!w)
                fail();
            witnesses.push_back(w);
        }

        // Lines 3-8: Θ + I_level + relation ≼
        build_interval_and_relation(level, level_ps);

        // Lines 11-12 (Algorithm 1): add projections for each p
        // Note: Algorithm 1 adds disc + ldcf for ALL polynomials (classical delineability)
        // Algorithm 2 (projective delineability) would only add ldcf for bound-defining polys
        for (unsigned i = 0; i < level_ps.size(); ++i) {
            polynomial_ref p(level_ps.get(i), m_pm);
            add_projections_for(P, p, level, witnesses[i]);
        }

        // Line 14 (Algorithm 1): add resultants for chosen relation pairs
        add_relation_resultants(P, level);
    }

    void process_top_level(todo_set& P, polynomial_ref_vector const& top_ps) {
        std::vector<polynomial_ref> witnesses;
        witnesses.reserve(top_ps.size());
        for (unsigned i = 0; i < top_ps.size(); ++i) {
            polynomial_ref p(top_ps.get(i), m_pm);
            polynomial_ref w = choose_nonzero_coeff(p, m_n);
            if (!w)
                fail();
            witnesses.push_back(w);
        }

        // Resultants between adjacent root functions (a lightweight ordering for the top level).
        add_adjacent_root_resultants(P, top_ps);

        // Projections (coeff witness, disc, leading coeff).
        for (unsigned i = 0; i < top_ps.size(); ++i) {
            polynomial_ref p(top_ps.get(i), m_pm);
            add_projections_for(P, p, m_n, witnesses[i]);
        }
    }

    std::vector<root_function_interval> single_cell_work() {
        if (m_n == 0)
            return m_I;

        todo_set P(m_cache, true);

        // Initialize P with distinct irreducible factors of the input polynomials.
        for (unsigned i = 0; i < m_P.size(); ++i) {
            polynomial_ref pi(m_P.get(i), m_pm);
            for_each_distinct_factor(pi, [&](polynomial_ref const& f) {
                P.insert(f.get());
            });
        }

        if (P.empty())
            return m_I;

        // Process top level m_n (we project from x_{m_n} and do not return an interval for it).
        if (P.max_var() == m_n) {
            polynomial_ref_vector top_ps(m_pm);
            P.extract_max_polys(top_ps);
            process_top_level(P, top_ps);
        }

        // Now iteratively process remaining levels (descending).
        while (!P.empty()) {
            polynomial_ref_vector level_ps(m_pm);
            var level = P.extract_max_polys(level_ps);
            SASSERT(level < m_n);
            process_level(P, level, level_ps);
        }

        return m_I;
    }

    std::vector<root_function_interval> single_cell() {
        try {
            return single_cell_work();
        }
        catch (nullified_poly_exception&) {
            m_fail = true;
            return m_I;
        }
    }
};

levelwise::levelwise(
    nlsat::solver& solver,
    polynomial_ref_vector const& ps,
    var n,
    assignment const& s,
    pmanager& pm,
    anum_manager& am,
    polynomial::cache& cache)
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
