#include "math/lp/dioph_eq.h"

#include <algorithm>
#include <limits>
#include <list>
#include <numeric>
#include <queue>

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include "math/lp/var_register.h"
/*
  Following paper: "A Practical Approach to Satisfiability  Modulo Linear
  Integer Arithmetic" by Alberto Griggio(griggio@fbk.eu).
  Data structures are:
  -- term_o: inherits lar_term and differs from it by having a constant, while
  lar_term is just a sum of monomials
  -- lra: pointer to lar_solver.
  -- lia: point to int_solver.
  -- m_sum_of_fixed: it keeps the contribution of the fixed variables to the row
  -- m_e_matrix: i-th row of this matrix keeps the term corresponding to i-ith entry
  -- m_l_matrix: the m_l_matrix[i] produces m_e_matrix[i] by using the terms definitions of lar_solver
  -- m_k2s: when the variable k is substituted in the row s of m_e_matrix, the pair (k,s) is added to m_k2s.
  m_k2s is a one to one mapping.
  -- m_fresh_k2xt_terms: when a fresh definitions is created for a variable k in row s then the triple
  (k,xt,(t,s)) is added to m_fresh_k2xt_terms, where xt is the fresh variable, and t it the term defining the substitution: something like k - xt + 5z + 6y = 0.
  The set of pairs (k, xt) is a one to one mapping
  m_row2fresh_defs[i]: is the list of all xt that were defined for row m_e_matrix[i].
  Invariant: Every xt in m_row2fresh[i] must have a corresponding entry in m_fresh_k2xt_terms

  The mapping between the columns of lar_solver and m_e_matrix is controlled by m_var_register.
  local_to_lar_solver(lar_solver_to_local(j)) == j. If local_to_lar_solver(j) == -1
  then j is a fresh variable, that is such that got introduced when normalizing a term like 3x-6y + 5z +11 = 0,
  when no variable has a coefficient +-1.

  -- get_term_from_entry(unsigned i) returns a term corresponding i-th entry.
  If t = get_term_from_entry(i) then we have equality t = 0. Initially
  get_term_from_entry(i) is set to initt(j) = lra.get_term(j) - j, for some
  column j,where all fixed variables are replaced by their values. To track the
  explanations of equality t = 0 we initially set m_l_matrix[i] = {(1,j)}. The
  explanation is obtained by replacing term of the m_l_matrix[i] = sum(aj*j) by the linear
  combination sum (aj*initt(j)) and joining the explanations of all fixed
  variables in the latter sum. entry_invariant(i) guarantees the validity of
  the i-th entry.
*/
namespace lp {
    template <typename T, typename K>
    bool contains(const T& t, K j) {
        return t.find(j) != t.end();
    }

    struct iv {
        mpq m_coeff;
        unsigned m_j;
        lpvar var() const { return m_j; }
        const mpq& coeff() const { return m_coeff; }
        mpq& coeff() { return m_coeff; }
        iv() {}
        iv(const mpq& v, unsigned j) : m_coeff(v), m_j(j) {}
    };

    class bijection {
        std::unordered_map<unsigned, unsigned> m_map;
        std::unordered_map<unsigned, unsigned> m_rev_map;
        auto map_begin() const { return m_map.begin(); }
        auto map_end() const { return m_map.end(); }
    public:

    
        // Iterator helper
        struct map_it {
            const bijection& m_bij;
            auto begin() const { return m_bij.map_begin(); }
            auto end() const { return m_bij.map_end(); }
        };

        
        // Add a method to get iterators over the key->val map (complementing key_val)
        map_it key_val_pairs() const { return {*this}; }
        void add(unsigned a, unsigned b) {
            SASSERT(!contains(m_map, a) && !contains(m_rev_map, b));
            m_map[a] = b;
            m_rev_map[b] = a;
        }

        unsigned get_key(unsigned b) const {
            SASSERT(has_val(b));
            return m_rev_map.find(b)->second;
        }

        unsigned size() const { return static_cast<unsigned>(m_map.size()); }

        void erase_val(unsigned b) {
            VERIFY(contains(m_rev_map, b) && contains(m_map, m_rev_map[b]));
            auto it = m_rev_map.find(b);
            if (it == m_rev_map.end()) return;
            unsigned key = it->second;
            m_rev_map.erase(it);
            VERIFY(has_key(key));
            m_map.erase(key);
        }
        bool has_val(unsigned b) const {
            return m_rev_map.find(b) != m_rev_map.end();
        }

        bool has_key(unsigned a) const {
            return m_map.find(a) != m_map.end();
        }

        void transpose_val(unsigned b0, unsigned b1) {
            bool has_b0 = has_val(b0);
            bool has_b1 = has_val(b1);

            // Both b0 and b1 exist
            if (has_b0 && has_b1) {
                unsigned a0 = m_rev_map.at(b0);
                unsigned a1 = m_rev_map.at(b1);

                erase_val(b0);
                erase_val(b1);

                add(a1, b0);
                add(a0, b1);
            }
            // Only b0 exists
            else if (has_b0) {
                unsigned a0 = m_rev_map.at(b0);                
                erase_val(b0);
                add(a0, b1);
            }
            // Only b1 exists
            else if (has_b1) {
                unsigned a1 = m_rev_map.at(b1);                
                erase_val(b1);
                add(a1, b0);
            }
            // Neither b0 nor b1 exists; do nothing
        }
        unsigned operator[](unsigned i) const {
            auto it = m_map.find(i);
            VERIFY(it != m_map.end());
            return it->second;
        }
    };

    template <typename T>
    struct bij_map {
        // We store T indexed by 'b' in an std::unordered_map, and use bijection to map from 'a' to 'b'.

        bijection m_bij;
        std::unordered_map<unsigned, T> m_data;
        // Adds a->b in m_bij, associates val with b.
        void add(unsigned a, unsigned b, const T& val) {
            // You might have some method in bijection such as 'insert(a, b)'
            // or possibly you'd do:
            // m_bij.add_key_val(a, b);
            // For example:
            m_bij.add(a, b);
            m_data[b] = val;
        }

        unsigned get_second_of_key(unsigned a) const {
            return m_bij[a];
        }

        void erase_by_second_key(unsigned b) {
            SASSERT(m_bij.has_val(b));
            m_bij.erase_val(b);
            auto it = m_data.find(b);
            VERIFY(it != m_data.end());
            m_data.erase(it);
        }

        bool has_key(unsigned j) const { return m_bij.has_key(j); }
        bool has_second_key(unsigned j) const { return m_bij.has_val(j); }
        // Get the data by 'a', look up b in m_bij, then read from m_data
        const T& get_by_key(unsigned a) const {
            unsigned b = m_bij[a];  // relies on operator[](unsigned) from bijection
            return get_by_val(b);
        }

        // Get the data by 'b' directly
        const T& get_by_val(unsigned b) const {
            auto it = m_data.find(b);
            VERIFY(it != m_data.end());
            return it->second;
        }
    };
    class dioph_eq::imp {
        // This class represents a term with an added constant number c, in form sum
        // {x_i*a_i} + c.
        class term_o : public lar_term {
            mpq m_c;

        public:
            term_o clone() const {
                term_o ret;
                for (const auto& p : *this) {
                    ret.add_monomial(p.coeff(), p.j());
                }
                ret.c() = c();
                ret.set_j(j());
                return ret;
            }
            term_o(const lar_term& t) : lar_term(t), m_c(0) {
                SASSERT(m_c.is_zero());
            }
            const mpq& c() const {
                return m_c;
            }
            mpq& c() {
                return m_c;
            }
            term_o() : m_c(0) {}

            friend term_o operator*(const mpq& k, const term_o& term) {
                term_o r;
                for (const auto& p : term)
                    r.add_monomial(p.coeff() * k, p.j());
                r.c() = k * term.c();
                return r;
            }

            friend term_o operator+(const term_o& a, const term_o& b) {
                term_o r = a.clone();
                for (const auto& p : b) {
                    r.add_monomial(p.coeff(), p.j());
                }
                r.c() += b.c();
                return r;
            }

            friend term_o operator-(const term_o& a, const term_o& b) {
                term_o r = a.clone();
                for (const auto& p : b)
                    r.sub_monomial(p.coeff(), p.j());
                r.c() -= b.c();
                return r;
            }
#if Z3DEBUG
            friend bool operator==(const term_o& a, const term_o& b) {
                term_o t = a.clone();
                t += mpq(-1) * b;
                return t.c() == mpq(0) && t.size() == 0;
            }

            friend bool operator!=(const term_o& a, const term_o& b) {
                return ! (a  == b);
            }

#endif
            term_o& operator+=(const term_o& t) {
                for (const auto& p : t) {
                    add_monomial(p.coeff(), p.j());
                }
                m_c += t.c();
                return *this;
            }
        };

        std::ostream& print_S(std::ostream& out) {
            out << "S:\n";
            for (unsigned ei = 0 ; ei < m_e_matrix.row_count(); ei++) {
                print_entry(ei, out, false, false, true);
            }
            return out;
        }
            
        std::ostream& print_bounds(std::ostream& out) {
            out << "bounds:\n";
            for (unsigned v = 0; v < lra.column_count(); ++v) {
                lra.print_column_info(v, out);
            }
            return out;
        }

        std::ostream& print_lar_term_L(const lar_term& t, std::ostream& out) const {
            return print_linear_combination_customized(
                t.coeffs_as_vector(),
                [](int j) -> std::string { return "x" + std::to_string(j); }, out);
        }

        // used for debug only
        std::ostream& print_lar_term_L(const std_vector<iv>& t, std::ostream& out) const {
            vector<std::pair<mpq, unsigned>> tp;
            for (const auto& p : t) {
                tp.push_back(std::make_pair(p.coeff(), p.var()));
            }
            return print_linear_combination_customized(
                tp, [](int j) -> std::string { return "x" + std::to_string(j); }, out);
        }

        std::ostream& print_espace(std::ostream & out) const {
            out << "m_espace:";
            print_term_o(create_term_from_espace(), out) << std::endl;
            return out;
        }
        
        std::ostream& print_term_o(term_o const& term, std::ostream& out) const {
            if (term.size() == 0 && term.c().is_zero()) {
                out << "0";
                return out;
            }
            bool first = true;
            // Copy term to a std_vector and sort by p.j()
            std_vector<std::pair<mpq, unsigned>> sorted_term;
            sorted_term.reserve(term.size());
            for (const auto& p : term) {
                sorted_term.emplace_back(p.coeff(), p.j());
            }
            std::sort(
                sorted_term.begin(), sorted_term.end(),
                [](const auto& a, const auto& b) {
                    return a.second < b.second;
                });

            // Print the sorted term
            for (auto& [val, j] : sorted_term) {
                if (first) {
                    first = false;
                }
                else if (is_pos(val)) {
                    out << " + ";
                }
                else {
                    out << " - ";
                    val = -val;
                }
                if (val == -numeric_traits<mpq>::one())
                    out << " - ";
                else if (val != numeric_traits<mpq>::one())
                    out << T_to_string(val);
                out << "x";
                out << j;
            }

            // Handle the constant term separately
            if (!term.c().is_zero()) {
                if (!first) {
                    if (term.c().is_pos())
                        out << " + ";
                    else
                        out << " - ";
                }
                out << abs(term.c());
            }

            return out;
        }

        // the maximal size of the term to try to tighten the bounds:
        // if the size of the term is large than the chances are that the GCD of the coefficients is one
        unsigned m_tighten_size_max = 10;
        bool m_some_terms_are_ignored = false;
        std_vector<mpq> m_sum_of_fixed;
        // we have to use m_var_register because of the fresh variables: otherwise they clash with the existing lar_solver column indices
        var_register m_var_register;
        // the terms are stored in m_A and m_c
        static_matrix<mpq, mpq> m_e_matrix;  // the rows of the matrix are the terms,
        static_matrix<mpq, mpq> m_l_matrix;  // the rows of the matrix are the l_terms providing the certificate to the entries modulo the constant part: look an entry_invariant that assures that the each two rows are in sync.
        int_solver& lia;
        lar_solver& lra;
        explanation m_infeas_explanation;

        // set F
        // iterate over all rows from 0 to m_e_matrix.row_count() - 1 and return those i such !m_k2s.has_val(i)
        // set S - iterate over bijection m_k2s
        mpq m_c;  // the constant of the equation
        struct term_with_index {
            // The invariant is
            // 1)  m_index[m_data[k].var()] = k, for each 0 <= k < m_data.size(), and
            // 2)  m_index[j] = -1, or m_data[m_index[j]].var() = j, for every 0 <= j < m_index.size().
            // For example m_data = [(coeff, 5), (coeff, 3)]
            // then m_index = [-1,-1, -1, 1, -1, 0, -1, ....].
            std_vector<iv> m_data;
            std_vector<int> m_index;
            // used for debug only
            lar_term to_term() const {
                lar_term r;
                for (const auto& p : m_data) {
                    r.add_monomial(p.coeff(), p.var());
                }
                return r;
            }
             // Deep‑copy this term_with_index into 'target'
            void copy(term_with_index& target) const {
                if (&target == this)
                    return;
                // Clear target's data and index
                target.clear();
                // Copy monomial data verbatim.
                target.m_data = m_data;

                // Re‑create a compact m_index that tracks only the used variables.
                unsigned max_var = 0;
                for (auto const& iv : m_data)
                    max_var = std::max(max_var, iv.var());

                target.m_index.assign(max_var + 1, -1);
                for (unsigned idx = 0; idx < m_data.size(); ++idx)
                    target.m_index[m_data[idx].var()] = static_cast<int>(idx);

#if Z3DEBUG
                SASSERT(target.invariant());
#endif
            }

            auto size() const { return m_data.size(); }
            
            bool has(unsigned k) const {
                return k < m_index.size() && m_index[k] >= 0;
            }

            const mpq& operator[](unsigned j) const {
                SASSERT(j >= 0 && j < m_index.size());
                SASSERT(m_index[j] >= 0 && m_index[j] < (int)m_data.size());
                return m_data[m_index[j]].coeff();
            }

            void erase(unsigned k) {
                if (k >= m_index.size() || m_index[k] == -1)
                    return;

                unsigned idx = m_index[k];
                // If not last element, move last element to idx position
                if (idx != m_data.size() - 1) {
                    m_data[idx] = m_data.back();
                    m_index[m_data[idx].var()] = idx;
                }

                m_data.pop_back();
                m_index[k] = -1;
                SASSERT(invariant());
            }
            void add(const mpq& a, unsigned j) {
                SASSERT(!a.is_zero());
                // Expand m_index if needed
                if (j >= m_index.size()) {
                    m_index.resize(j + 1, -1);
                }

                int idx = m_index[j];
                if (idx == -1) {
                    // Insert a new monomial { a, j } into m_data
                    m_data.push_back({a, j});
                    m_index[j] = static_cast<int>(m_data.size() - 1);
                }
                else {
                    // Accumulate the coefficient
                    m_data[idx].coeff() += a;
                    // If the coefficient becomes zero, remove the entry
                    if (m_data[idx].coeff().is_zero()) {
                        int last = static_cast<int>(m_data.size() - 1);
                        // Swap with the last element for efficient removal
                        if (idx != last) {
                            auto tmp = m_data[last];
                            m_data[idx] = tmp;
                            m_index[tmp.var()] = idx;
                        }
                        m_data.pop_back();
                        m_index[j] = -1;
                    }
                }
                SASSERT(invariant());
            }

            bool invariant() const {
                // 1. For each j in [0..m_index.size()), if m_index[j] = -1, ensure no m_data[k].var() == j
                //    otherwise verify m_data[m_index[j]].var() == j
                for (unsigned j = 0; j < m_index.size(); j++) {
                    int idx = m_index[j];
                    if (idx == -1) {
                        // Check that j is not in m_data
                        for (unsigned k = 0; k < m_data.size(); ++k) {
                            if (m_data[k].var() == j) {
                                return false;
                            }
                        }
                    }
                    else {
                        // Check that var() in m_data[idx] matches j
                        if (idx < 0 || static_cast<unsigned>(idx) >= m_data.size()) {
                            return false;
                        }
                        if (m_data[idx].var() != j || m_data[idx].coeff().is_zero()) {
                            return false;
                        }
                    }
                }
                // 2. For each item in m_data, check that m_index[m_data[k].var()] == k
                //    and that the coeff() is non-zero
                for (unsigned k = 0; k < m_data.size(); ++k) {
                    unsigned var = m_data[k].var();
                    if (var >= m_index.size()) {
                        return false;
                    }
                    if (m_index[var] != static_cast<int>(k)) {
                        return false;
                    }
                    if (m_data[k].coeff().is_zero()) {
                        return false;
                    }
                }

                return true;
            }
            void clear() {
                for (const auto& p : m_data) {
                    m_index[p.var()] = -1;
                }
                m_data.clear();
                SASSERT(invariant());
            }
            auto begin() const { return m_data.begin();}
            auto end() const { return m_data.end(); }

        };

        // m_lspace is for operations on l_terms - m_e_matrix rows
        term_with_index m_lspace;
        // m_espace is for operations on m_e_matrix rows
        term_with_index m_espace;
        
        bijection m_k2s;
        bij_map<std::pair<lar_term, unsigned>> m_fresh_k2xt_terms;
        // m_row2fresh_defs[i] is the set of all fresh variables xt
        // such that pairs (xt, m_fresh_k2xt_terms[xt]) is a fresh definition introduced for row i
        // When row i is changed all entries depending on m_fresh_k2xt_terms[xt] should be recalculated,
        // and the corresponding fresh definitions removed.
        std::unordered_map<unsigned, std_vector<unsigned>> m_row2fresh_defs;

        indexed_uint_set m_changed_rows;
        // m_changed_f_columns are the columns that just became fixed, or those that just stopped being fixed.
        // If such a column appears in an entry it has to be recalculated.
        indexed_uint_set m_changed_f_columns;
        indexed_uint_set m_changed_terms; // represented by term columns
        indexed_uint_set m_terms_to_tighten; // represented by term columns
        // m_column_to_terms[j] is the set of all k such lra.get_term(k) depends on j
        std::unordered_map<unsigned, std::unordered_set<unsigned>> m_columns_to_terms;

        unsigned m_normalize_conflict_index = UINT_MAX;  // the row index of the conflict
        mpq      m_normalize_conflict_gcd; // the gcd of the coefficients of m_e_matrix[m_normalize_conflict_gcd].
        void reset_conflict() { m_normalize_conflict_index = UINT_MAX; }
        bool has_conflict_index() const { return m_normalize_conflict_index != UINT_MAX; }
        void set_rewrite_conflict(unsigned idx, const mpq& gcd) {
            SASSERT(idx != UINT_MAX);
            m_normalize_conflict_index = idx;
            m_normalize_conflict_gcd = gcd;
            lra.stats().m_dio_rewrite_conflicts++;
        }

        void undo_add_term_method(const lar_term* t) {
            TRACE("d_undo", tout << "t:" << t << ", t->j():" << t->j() << std::endl;);
            TRACE("dio", lra.print_term(*t, tout); tout << ", t->j() =" << t->j() << std::endl;);
            if (!contains(m_active_terms, t)) {
                for (auto i = m_added_terms.size(); i-- > 0; ) {
                    if (m_added_terms[i] != t)
                        continue;
                    m_added_terms[i] = m_added_terms.back();
                    m_added_terms.pop_back();
                    break;  // all is done since the term has not made it to m_active_terms
                }
                return;
            }
            // deregister the term that has been activated
            for (const auto& p : t->ext_coeffs()) {
                TRACE("dio_reg", tout << "derigister p.var():" << p.var() << "->" << t->j() << std::endl;);
                auto it = m_columns_to_terms.find(p.var());
                SASSERT(it != m_columns_to_terms.end());
                it->second.erase(t->j());
                if (it->second.size() == 0) {
                    m_columns_to_terms.erase(it);
                }
            }
            SASSERT(std::find(m_added_terms.begin(), m_added_terms.end(), t) == m_added_terms.end());
            SASSERT(contains(m_active_terms, t));
            m_active_terms.erase(t);
            TRACE("dio", tout << "the deleted term column in m_l_matrix" << std::endl; for (auto p : m_l_matrix.column(t->j())) { tout << "p.coeff():" << p.coeff() << ", row " << p.var() << std::endl; } tout << "m_l_matrix has " << m_l_matrix.column_count() << " columns" << std::endl; tout << "and " << m_l_matrix.row_count() << " rows" << std::endl; print_lar_term_L(*t, tout); tout << "; t->j()=" << t->j() << std::endl;);
            shrink_matrices();
        }

        struct undo_add_term : public trail {
            imp& m_s;
            const lar_term* m_t;
            undo_add_term(imp& s, const lar_term* t) : m_s(s), m_t(t) {}

            void undo() {
                m_s.undo_add_term_method(m_t);
            }
        };

        struct protected_queue {
            std::list<unsigned> m_q;
            std::unordered_map<unsigned, std::list<unsigned>::iterator> m_positions;

            bool empty() const {
                return m_q.empty();
            }

            unsigned size() const {
                return static_cast<unsigned>(m_q.size());
            }

            void push(unsigned j) {
                if (m_positions.find(j) != m_positions.end()) return;
                m_q.push_back(j);
                m_positions[j] = std::prev(m_q.end());
            }

            unsigned pop_front() {
                unsigned j = m_q.front();
                m_q.pop_front();
                m_positions.erase(j);
                return j;
            }

            void remove(unsigned j) {
                auto it = m_positions.find(j);
                if (it != m_positions.end()) {
                    m_q.erase(it->second);
                    m_positions.erase(it);
                }
                SASSERT(invariant());
            }

            bool contains(unsigned j) const {
                return m_positions.find(j) != m_positions.end();
            }

            void reset() {
                m_q.clear();
                m_positions.clear();
            }
            // Invariant method to ensure m_q and m_positions are aligned
            bool invariant() const {
                if (m_q.size() != m_positions.size())
                    return false;

                for (auto it = m_q.begin(); it != m_q.end(); ++it) {
                    auto pos_it = m_positions.find(*it);
                    if (pos_it == m_positions.end())
                        return false;
                    if (pos_it->second != it)
                        return false;
                }

                return true;
            }
        };

        protected_queue m_q;
        
        struct undo_fixed_column : public trail {
            imp& m_imp;
            unsigned m_j;  // the column that has been added
            const mpq m_fixed_val;
            undo_fixed_column(imp& s, unsigned j) : m_imp(s), m_j(j), m_fixed_val(s.lra.get_lower_bound(j).x) {
                SASSERT(s.lra.column_is_fixed(j));
            }

            void undo() override {
                m_imp.add_changed_column(m_j);
            }
        };

        void remove_last_entry() {
            unsigned ei = static_cast<unsigned>(m_e_matrix.row_count() - 1);

            if (m_k2s.has_val(ei)) {
                remove_from_S(ei);
            }
            m_sum_of_fixed.pop_back();
        }

        void eliminate_last_term_column() {
            // change only the rows in m_l_matrix, and update m_e_matrix lazily
            unsigned j = m_l_matrix.column_count() - 1;
            make_sure_j_is_in_the_last_row_of_l_matrix();
            const auto& last_e_row = m_l_matrix.m_rows.back();
            mpq alpha;
            for (const auto& p : last_e_row) {
                if (p.var() == j) {
                    alpha = p.coeff();
                    break;
                }
            }
            unsigned last_row_index = m_l_matrix.row_count() - 1;
            m_l_matrix.divide_row(last_row_index, alpha);  // divide the last row by alpha

            auto& column = m_l_matrix.m_columns[j];
            int pivot_col_cell_index = -1;
            for (unsigned k = 0; k < column.size(); k++) {
                if (column[k].var() == last_row_index) {
                    pivot_col_cell_index = k;
                    break;
                }
            }
            SASSERT(pivot_col_cell_index >= 0);

            if (pivot_col_cell_index != 0) {
                SASSERT(column.size() > 1);
                // swap the pivot column cell with the head cell
                auto c = column[0];
                column[0] = column[pivot_col_cell_index];
                column[pivot_col_cell_index] = c;

                m_l_matrix.m_rows[last_row_index][column[0].offset()].offset() = 0;
                m_l_matrix.m_rows[c.var()][c.offset()].offset() = pivot_col_cell_index;
            }
            while (column.size() > 1) {
                auto& c = column.back();
                SASSERT(c.var() != last_row_index);
                m_l_matrix.pivot_row_to_row_given_cell(last_row_index, c, j);
                m_changed_rows.insert(c.var());
            }
        }

        void make_sure_j_is_in_the_last_row_of_l_matrix() {
            unsigned j = m_l_matrix.column_count() - 1;
            const auto& last_e_row = m_l_matrix.m_rows.back();
            if (any_of(last_e_row, [j](auto const& p) { return p.var() == j; }))
                return;
            SASSERT(m_l_matrix.m_columns.back().size() > 0);            
            unsigned i = m_l_matrix.m_columns[j][0].var();
            m_l_matrix.add_rows(mpq(1), i, m_l_matrix.row_count() - 1);
            // what is the post-condition? Is 'j' used in the post-condition or is it 'i'?
            // SASSERT(any_of(m_l_matrix.m_rows.back(), [i](auto const& p) { return p.var() == i; }));
        }

        void shrink_matrices() {
            unsigned i = m_l_matrix.row_count() - 1;
            eliminate_last_term_column();
            remove_last_row_in_matrix(m_l_matrix);
            remove_last_row_in_matrix(m_e_matrix);
            while (m_l_matrix.column_count() && m_l_matrix.m_columns.back().size() == 0) {
                m_l_matrix.m_columns.pop_back();
            }
            while (m_e_matrix.column_count() && m_e_matrix.m_columns.back().size() == 0) {
                m_e_matrix.m_columns.pop_back();
            }
            m_var_register.shrink(m_e_matrix.column_count());

            remove_irrelevant_fresh_defs_for_row(i);

            if (m_k2s.has_val(i)) 
                remove_from_S(i);

            m_sum_of_fixed.pop_back();
        }

        void remove_last_row_in_matrix(static_matrix<mpq, mpq>& m) {
            auto& last_row = m.m_rows.back();
            for (unsigned k = static_cast<unsigned>(last_row.size()); k-- > 0;) {
                m.remove_element(last_row, last_row[k]);
            }
            m.m_rows.pop_back();
        }

        void remove_entry_index(std::list<unsigned>& l, unsigned ei) {
            auto it = std::find(l.begin(), l.end(), ei);
            if (it != l.end())
                l.erase(it);
        }

        void add_changed_column(unsigned j) {
            TRACE("dio", lra.print_column_info(j, tout););
            m_changed_f_columns.insert(j);
        }
        std_vector<const lar_term*> m_added_terms;
        std::unordered_set<const lar_term*> m_active_terms;
        // it is a non-const function : it can set m_some_terms_are_ignored to true
        bool term_has_big_number(const lar_term& t) {
            for (const auto& p : t) {
                if (p.coeff().is_big() || (is_fixed(p.var()) && lra.get_lower_bound(p.var()).x.is_big())) {
                    m_some_terms_are_ignored = true;
                    return true;
                }
            }
            return false;
        }

        bool ignore_big_nums() const { return lra.settings().dio_ignore_big_nums(); }

        // we add all terms, even those with big numbers, but we might choose to non process the latter.
        void add_term_callback(const lar_term* t) {
            unsigned j = t->j();
            TRACE("dio", tout << "term column t->j():" << j << std::endl; lra.print_term(*t, tout) << std::endl;);
            if (!lra.column_is_int(j)) {
                TRACE("dio", tout << "ignored a non-integral column" << std::endl;);
                m_some_terms_are_ignored = true;
                return;
            }
            CTRACE("dio", !lra.column_has_term(j), tout << "added term that is not associated with a column yet" << std::endl;);
            m_added_terms.push_back(t);
            mark_term_change(t->j());
            auto undo = undo_add_term(*this, t);
            lra.trail().push(undo);
        }

        void mark_term_change(unsigned j) {
            TRACE("dio", tout << "marked term change j:" << j << std::endl;);
            m_changed_terms.insert(j);
        }

        void update_column_bound_callback(unsigned j) {
            if (!lra.column_is_int(j))
                return;
            if (lra.column_has_term(j))
                m_terms_to_tighten.insert(j); // the boundary of the term has changed: we can be successful to tighten this term   
            if (!lra.column_is_fixed(j))
                return;
            TRACE("dio", tout << "j:" << j << "\n"; lra.print_column_info(j, tout););
            m_changed_f_columns.insert(j);
            lra.trail().push(undo_fixed_column(*this, j));
        }

    public:
        imp(int_solver& lia, lar_solver& lra) : lia(lia), lra(lra) {
            lra.m_add_term_callback = [this](const lar_term* t) { add_term_callback(t); };
            lra.m_update_column_bound_callback = [this](unsigned j) { update_column_bound_callback(j); };
        }
        term_o get_term_from_entry(unsigned i) const {
            term_o t;
            for (const auto& p : m_e_matrix.m_rows[i]) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_sum_of_fixed[i];
            return t;
        }

        // adds variable j of lar_solver to the local diophantine handler
        unsigned add_var(unsigned j) {
            return this->m_var_register.add_var(j, true);
        }

        unsigned local_to_lar_solver(unsigned j) const {
            return m_var_register.local_to_external(j);
        }

        void register_columns_to_term(const lar_term& t) {
            CTRACE("dio_reg", t.j() == 1337, tout << "register term:"; lra.print_term(t, tout); tout << ", t.j()=" << t.j() << std::endl;);
            for (const auto& p : t.ext_coeffs()) {
                auto it = m_columns_to_terms.find(p.var());
                TRACE("dio_reg", tout << "register p.var():" << p.var() << "->" << t.j() << std::endl;);

                if (it != m_columns_to_terms.end()) {
                    it->second.insert(t.j());
                }
                else {
                    std::unordered_set<unsigned> s;
                    s.insert(t.j());
                    m_columns_to_terms[p.var()] = s;
                }
            }
        }
        // the term has form sum(a_i*x_i) - t.j() = 0,
        void fill_entry(const lar_term& t) {
            unsigned entry_index = (unsigned)m_e_matrix.row_count();
            m_sum_of_fixed.push_back(mpq(0));
            mpq& fixed_sum = m_sum_of_fixed.back();
            // fill m_l_matrix row
            m_l_matrix.add_row();
            // todo: consider to compress variables t.j() by using a devoted var_register for term columns
            m_l_matrix.add_columns_up_to(t.j());
            m_l_matrix.add_new_element(entry_index, t.j(), mpq(1));
            // fill E-entry
            m_e_matrix.add_row();

            SASSERT(m_sum_of_fixed.size() == m_l_matrix.row_count() && m_e_matrix.row_count() == m_e_matrix.row_count());

            for (const auto& p : t.ext_coeffs()) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.var()))
                    fixed_sum += p.coeff() * lia.lower_bound(p.var()).x;
                else {
                    unsigned lj = add_var(p.var());
                    m_e_matrix.add_columns_up_to(lj);
                    m_e_matrix.add_new_element(entry_index, lj, p.coeff());
                }
            }
            subs_entry(entry_index);
            SASSERT(entry_invariant(entry_index));
            TRACE("dio_entry", print_entry(entry_index, tout) << std::endl;);
        }
        void subs_entry(unsigned ei) {
            if (ei >= m_e_matrix.row_count()) return;
            // m_q is the queue of variables that can be substituted in ei
            m_q.reset();
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                if (can_substitute(p.var()))
                    m_q.push(p.var());
            }
            if (m_q.size() == 0) {
                TRACE("dio", tout << "nothing to subst on ei:" << ei << "\n";);
                return;
            }
            substitute_on_q(ei);
            SASSERT(entry_invariant(ei));
        }

        void substitute_on_q_with_entry_in_S(unsigned ei, unsigned j, const mpq& alpha) {
            unsigned ei_to_sub = m_k2s[j];
            int sign_j = get_sign_in_e_row(ei_to_sub, j);
            // we need to eliminate alpha*j in ei's row
            add_two_entries(-mpq(sign_j) * alpha, ei_to_sub, ei);
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                unsigned jj = p.var();
                if (can_substitute(jj))
                    m_q.push(jj);
            }
        }
        void substitute_with_fresh_def(unsigned ei, unsigned j, const mpq& alpha) {
            const lar_term& sub_term = m_fresh_k2xt_terms.get_by_key(j).first;
            TRACE("dio", print_lar_term_L(sub_term, tout) << std::endl;);
            SASSERT(sub_term.get_coeff(j).is_one());
            // we need to eliminate alpha*j in ei's row
            add_term_to_entry(-alpha, sub_term, ei);
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                unsigned jj = p.var();
                if (can_substitute(jj))
                    m_q.push(jj);
            }
        }

        // q is the queue of variables that can be substituted in ei
        void substitute_on_q(unsigned ei) {
            while (!m_q.empty()) {
                unsigned j = m_q.pop_front();
                mpq alpha = get_coeff_in_e_row(ei, j);
                if (alpha.is_zero()) continue;
                if (m_k2s.has_key(j)) {
                    substitute_on_q_with_entry_in_S(ei, j, alpha);
                }
                else {
                    substitute_with_fresh_def(ei, j, alpha);
                }
            }
        }
        bool term_is_in_range(const lar_term& t) const {
            for (const auto& p : t) {
                if (p.var() >= m_e_matrix.column_count())
                    return false;
            }
            return true;
        }
        // adds the term multiplied by coeff to m_e_matrix row i
        void add_term_to_entry(const mpq& coeff, const lar_term& t, unsigned i) {
            SASSERT(term_is_in_range(t));
            m_e_matrix.add_term_to_row(coeff, t, i);
        }

        // adds entry i0 multiplied by coeff to entry i1
        void add_two_entries(const mpq& coeff, unsigned i0, unsigned i1) {
            m_e_matrix.add_rows(coeff, i0, i1);
            m_l_matrix.add_rows(coeff, i0, i1);
            m_sum_of_fixed[i1] += coeff * m_sum_of_fixed[i0];
        }

        void clear_e_row(unsigned ei) {
            auto& row = m_e_matrix.m_rows[ei];
            while (row.size() > 0) {
                auto& c = row.back();
                m_e_matrix.remove_element(row, c);
            }
        }

        void recalculate_entry(unsigned ei) {
            TRACE("dio", print_entry(ei, tout) << std::endl;);
            mpq& fixed_sum = m_sum_of_fixed[ei];
            fixed_sum = mpq(0);
            open_l_term_to_espace(ei, fixed_sum);
            clear_e_row(ei);
            mpq denom(1);
            for (const auto& p : m_espace.m_data) {
                unsigned lj = add_var(p.var());
                m_e_matrix.add_columns_up_to(lj);
                m_e_matrix.add_new_element(ei, lj, p.coeff());
                if (!denominator(p.coeff()).is_one()) {
                    denom = lcm(denom, denominator(p.coeff()));
                }
            }
            if (!denom.is_one()) {
                fixed_sum *= denom;
                m_l_matrix.multiply_row(ei, denom);
                m_e_matrix.multiply_row(ei, denom);
            }
            if (belongs_to_s(ei)) {
                remove_from_S(ei);
            }
            SASSERT(entry_invariant(ei));
        }

        void find_changed_terms_and_more_changed_rows() {
            for (unsigned j : m_changed_f_columns) {
                const auto it = m_columns_to_terms.find(j);
                if (it != m_columns_to_terms.end())
                    for (unsigned k : it->second) {
                        mark_term_change(k);
                    }
                if (!m_var_register.external_is_used(j))
                    continue;
                for (const auto& p : m_e_matrix.column(this->lar_solver_to_local(j))) {
                    m_changed_rows.insert(p.var());
                }
            }
        }

        void remove_irrelevant_fresh_defs_for_row(unsigned ei) {
            auto it = m_row2fresh_defs.find(ei);
            if (it == m_row2fresh_defs.end()) return;            
            for (unsigned xt : it->second) {
                if (m_fresh_k2xt_terms.has_second_key(xt))
                    m_fresh_k2xt_terms.erase_by_second_key(xt);
            }
            m_row2fresh_defs.erase(it);
        }

        void remove_irrelevant_fresh_defs() {
            std_vector<unsigned> xt_to_remove;
            std_vector<unsigned> rows_to_remove_the_defs_from;
            for (const auto& p : m_fresh_k2xt_terms.m_bij.key_val_pairs()) {
                unsigned xt = p.second;
                if (xt >= m_e_matrix.column_count()) {
                    xt_to_remove.push_back(xt);
                    rows_to_remove_the_defs_from.push_back(m_fresh_k2xt_terms.get_by_val(xt).second);
                }
            }

            for (unsigned xt : xt_to_remove) {
                m_fresh_k2xt_terms.erase_by_second_key(xt);
            }

            for (unsigned ei : m_changed_rows) {
                remove_irrelevant_fresh_defs_for_row(ei);
            }

            for (unsigned ei : rows_to_remove_the_defs_from) {
                remove_irrelevant_fresh_defs_for_row(ei);
            }
        }

        // this is a non-const function - it can set m_some_terms_are_ignored to true
        bool is_big_term_or_no_term(unsigned j) {
            return
                j >= lra.column_count()
                ||
                !lra.column_has_term(j)
                ||
                (ignore_big_nums() && term_has_big_number(lra.get_term(j)));
        }
 
// Processes columns that have changed due to variables becoming fixed/unfixed or terms being updated.
// It identifies affected terms and rows, recalculates entries, removes irrelevant fresh definitions,
// and ensures substituted variables are properly eliminated from changed F entries, m_e_matrix.
// The function maintains internal consistency of data structures after these updates.
     void process_m_changed_f_columns(std_vector<unsigned> &f_vector) {
            find_changed_terms_and_more_changed_rows();
            for (unsigned j: m_changed_terms) {
                if (!is_big_term_or_no_term(j))
                    m_terms_to_tighten.insert(j);
                if (j < m_l_matrix.column_count())
                    for (const auto& cs : m_l_matrix.column(j)) 
                        m_changed_rows.insert(cs.var());                
            }

            // find more entries to recalculate
            std_vector<unsigned> more_changed_rows;
            for (unsigned ei : m_changed_rows) {
                auto it = m_row2fresh_defs.find(ei);
                if (it == m_row2fresh_defs.end()) continue;
                for (unsigned xt : it->second) {
                    SASSERT(var_is_fresh(xt));
                    for (const auto& p : m_e_matrix.m_columns[xt])
                        more_changed_rows.push_back(p.var());
                }
            }

            for (unsigned ei : more_changed_rows)
                m_changed_rows.insert(ei);
            
            for (unsigned ei : m_changed_rows) {
                if (ei >= m_e_matrix.row_count())
                    continue;
                if (belongs_to_s(ei))
                    f_vector.push_back(ei);

                recalculate_entry(ei);
                
                if (m_e_matrix.m_columns.back().size() == 0) {
                    m_e_matrix.m_columns.pop_back();
                    m_var_register.shrink(m_e_matrix.column_count());
                }
                if (m_l_matrix.m_columns.back().size() == 0)
                    m_l_matrix.m_columns.pop_back();
            }
            remove_irrelevant_fresh_defs();
            eliminate_substituted_in_changed_rows();
            m_changed_f_columns.reset();
            m_changed_rows.reset();
            m_changed_terms.reset();
        }

        int get_sign_in_e_row(unsigned ei, unsigned j) const {
            const auto& row = m_e_matrix.m_rows[ei];
            auto it = std::find_if(row.begin(), row.end(), [j](const auto& p) { return p.var() == j; });
            SASSERT(it != row.end() && abs(it->coeff()) == mpq(1));
            return it->coeff().is_pos() ? 1 : -1;
        }

        mpq get_coeff_in_e_row(unsigned ei, unsigned j) {
            const auto& row = m_e_matrix.m_rows[ei];
            auto it = std::find_if(row.begin(), row.end(), [j](const auto& p) { return p.var() == j; });
            if (it == row.end()) return mpq(0);
            return it->coeff();
        }

        void eliminate_substituted_in_changed_rows() {
            for (unsigned ei : m_changed_rows)
                subs_entry(ei);
        }

        // returns true if a variable j is substituted
        bool can_substitute(unsigned j) const {
            return m_k2s.has_key(j) || m_fresh_k2xt_terms.has_key(j);
        }

        bool entries_are_ok() {
            if (lra.settings().get_cancel_flag()) return true;
            for (unsigned ei = 0; ei < m_e_matrix.row_count(); ei++) {
                if (entry_invariant(ei) == false) {
                    TRACE("dio", tout << "bad entry:"; print_entry(ei, tout););
                    return false;
                }
                if (belongs_to_f(ei)) {
                    // see that all vars are substituted
                    const auto& row = m_e_matrix.m_rows[ei];
                    for (const auto& p : row) {
                        if (m_k2s.has_key(p.var())) {
                            TRACE("dio",
                              tout << "entry:" << ei << " belongs to f but depends on column " << p.var() << std::endl;
                              tout << "m_var_register.local_to_external(p.var()):" << m_var_register.local_to_external(p.var()) << std::endl;
                              print_entry(ei, tout);
                              tout << "column " << p.var() << " of m_e_matrix:";
                              for (const auto & c : m_e_matrix.m_columns[p.var()]) {
                              tout << "row:" << c.var() << ", ";
                              }

                              tout << std::endl;
                              tout << "column " << p.var() << " is subst by entry:";
                              print_entry(m_k2s[p.var()],tout)  << std::endl;);
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        void init(std_vector<unsigned> & f_vector) {
            m_infeas_explanation.clear();
            lia.get_term().clear();
            reset_conflict();

            process_m_changed_f_columns(f_vector);
            for (const lar_term* t : m_added_terms) {
                m_active_terms.insert(t);
                f_vector.push_back(m_e_matrix.row_count()); // going to add a row in fill_entry
                fill_entry(*t);
                register_columns_to_term(*t);
            }

            SASSERT(is_in_sync());
            m_added_terms.clear();
            SASSERT(entries_are_ok());
        }

        template <typename K>
        mpq gcd_of_coeffs(const K& k, bool check_for_one) {
            if (check_for_one)
                for (const auto& p : k)
                    if (p.coeff().is_one() || p.coeff().is_minus_one())
                        return mpq(1);

            mpq g(0);
            for (const auto& p : k) {
                SASSERT(p.coeff().is_int());
                if (g.is_zero())
                    g = abs(p.coeff());
                else
                    g = gcd(g, p.coeff());
                if (g.is_one())
                    break;
            }
            return g;
        }

        std::ostream& print_deps(std::ostream& out, u_dependency* dep) const {
            explanation ex(lra.flatten(dep));
            return lra.print_expl(out, ex);
        }

        bool var_is_fresh(unsigned j) const {
            bool ret = m_fresh_k2xt_terms.has_second_key(j);
            SASSERT(!ret || m_var_register.local_to_external(j) == UINT_MAX);
            return ret;
        }

        template <typename T>
        bool has_fresh_var(const T& t) const {
            return any_of(t, [&](auto const& p) { return var_is_fresh(p.var()); });
        }
        
        bool has_fresh_var(unsigned row_index) const {
            return has_fresh_var(m_e_matrix[row_index]);
        }

        // A conflict is reported when the gcd of the monomial coefficients does not divide the free coefficent.
        // If there is no conflict the entry is divided, normalized, by gcd.
        // The function returns true if and only if there is no conflict.
        bool normalize_e_by_gcd(unsigned ei, mpq& g) {
            mpq& e = m_sum_of_fixed[ei];
            TRACE("dio", print_entry(ei, tout) << std::endl;);
            g = gcd_of_coeffs(m_e_matrix.m_rows[ei], false);
            if (g.is_zero() || g.is_one()) {
                SASSERT(g.is_one() || e.is_zero());
                return true;
            }
            TRACE("dio", tout << "g:" << g << std::endl;);
            mpq c_g = e / g;
            if (c_g.is_int()) {
                for (auto& p : m_e_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }
                m_sum_of_fixed[ei] = c_g;
                // e.m_l /= g
                for (auto& p : m_l_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }

                TRACE("dio", tout << "ep_m_e:";
                      print_entry(ei, tout) << std::endl;);
                SASSERT(entry_invariant(ei));
                return true;
            }
            // c_g is not integral
            return false;
        }

        lia_move subs_qfront_by_fresh(unsigned k, protected_queue& q, unsigned j) {
            const lar_term& e = m_fresh_k2xt_terms.get_by_key(k).first;
            TRACE("dio", tout << "k:" << k << ", in ";
                  print_term_o(create_term_from_espace(), tout) << std::endl;
                  tout << "subs with e:";
                  print_lar_term_L(e, tout) << std::endl;);
            mpq coeff = -m_espace[k];  // need to copy since it will be zeroed
            m_espace.erase(k);         // m_espace[k] = 0;

            SASSERT(e.get_coeff(k).is_one());

            for (const auto& p : e) {
                unsigned j = p.var();
                if (j == k)
                    continue;
                m_espace.add(p.coeff() * coeff, j);
                // do we need to add j to the queue?
                if (m_espace.has(j) && can_substitute(j))
                    q.push(j);
            }

            // there is no change in m_l_matrix
            TRACE("dio", tout << "after subs k:" << k << "\n";
                  print_term_o(create_term_from_espace(), tout) << std::endl;
                  tout << "m_lspace:{"; print_lar_term_L(m_lspace.m_data, tout);
                  tout << "}, opened:"; print_ml(m_lspace.to_term(), tout) << std::endl;);
             return tighten_on_espace(j);
        }

        void add_l_row_to_term_with_index(const mpq& coeff, unsigned ei) {
            for (const auto& p : m_l_matrix.m_rows[ei]) {
                m_lspace.add(coeff * p.coeff(), p.var());
            }
        }

        lia_move subs_qfront_by_S(unsigned k, protected_queue& q, unsigned j) {
            const mpq& e = m_sum_of_fixed[m_k2s[k]];
            TRACE("dio", tout << "k:" << k << ", in ";
                  print_term_o(create_term_from_espace(), tout) << std::endl;
                  tout << "subs with e:";
                  print_entry(m_k2s[k], tout) << std::endl;);
            mpq coeff = m_espace[k];  // need to copy since it will be zeroed
            m_espace.erase(k);        // m_espace[k] = 0;

            const auto& e_row = m_e_matrix.m_rows[m_k2s[k]];
            auto it = std::find_if(e_row.begin(), e_row.end(),
                                   [k](const auto& c) {
                                       return c.var() == k;
                                   });
            SASSERT(it != e_row.end());
            const mpq& k_coeff_in_e = it->coeff();
            bool is_one = k_coeff_in_e.is_one();
            SASSERT(is_one || k_coeff_in_e.is_minus_one());
            if (is_one)
                coeff = -coeff;

            for (const auto& p : e_row) {
                unsigned j = p.var();
                if (j == k)
                    continue;
                m_espace.add(p.coeff() * coeff, j);
                // do we need to add j to the queue?
                if (m_espace.has(j) && can_substitute(j))
                    q.push(j);
            }
            m_c += coeff * e;
            add_l_row_to_term_with_index(coeff, sub_index(k));
            TRACE("dio", tout << "after subs k:" << k << "\n";
                  print_term_o(create_term_from_espace(), tout) << std::endl;
                  tout << "m_lspace:{"; print_lar_term_L(m_lspace.to_term(), tout);
                  tout << "}, opened:"; print_ml(m_lspace.to_term(), tout) << std::endl;);

            return tighten_on_espace(j);
        }

        bool is_substituted_by_fresh(unsigned k) const {
            return m_fresh_k2xt_terms.has_key(k);
        }

        // find a variable in q, not neccessarily at the beginning of the queue, that when substituted would create the minimal
        // number of non-zeroes
        unsigned find_var_to_substitute_on_espace(protected_queue& q) {
            // go over all q elements j
            // say j is substituted by entry ei = m_k2s[j]
            // count the number of variables i in m_e_matrix[ei] that m_espace does not contain i,
            // and choose ei where this number is minimal
            
            unsigned best_var = UINT_MAX;
            size_t min_new_vars = std::numeric_limits<size_t>::max();
            unsigned num_candidates = 0;
            std::vector<unsigned> to_remove;
            for (unsigned j : q.m_q) {
                size_t new_vars = 0;
                if (!m_espace.has(j)) {
                    to_remove.push_back(j);
                    continue;
                }
                if (m_k2s.has_key(j)) {
                    unsigned ei = m_k2s[j]; // entry index for substitution
                    for (const auto& p : m_e_matrix.m_rows[ei])
                        if (p.var() != j && !m_espace.has(p.var()))
                            ++new_vars;
                }
                else if (m_fresh_k2xt_terms.has_key(j)) {
                    const lar_term& fresh_term = m_fresh_k2xt_terms.get_by_key(j).first;
                    for (const auto& p : fresh_term)
                        if (p.var() != j && !m_espace.has(p.var()))
                            ++new_vars;
                }
                if (new_vars < min_new_vars) {
                    min_new_vars = new_vars;
                    best_var = j;
                    num_candidates = 1;
                }
                else if (new_vars == min_new_vars) {
                    ++num_candidates;
                    if ((lra.settings().random_next() % num_candidates) == 0)
                        best_var = j;
                }
            }

            if (best_var != UINT_MAX)
                q.remove(best_var);

            for (unsigned j: to_remove)
                q.remove(j);
            
            
            return best_var;
        }
        
        // The term giving the substitution is in form (+-)x_k + sum {a_i*x_i} + c = 0.
        // We substitute x_k in t by (+-)coeff*(sum {a_i*x_i} + c), where coeff is
        // the coefficient of x_k in t.
        lia_move subs_front_with_S_and_fresh(protected_queue& q, unsigned j) {
            process_fixed_in_espace();
            auto r = tighten_on_espace(j);
            if (r == lia_move::conflict)
                return lia_move::conflict;
            unsigned k = find_var_to_substitute_on_espace(q);
            if (k == UINT_MAX)
                return lia_move::undef;
            SASSERT(m_espace.has(k));
            // we might substitute with a term from S or a fresh term
            SASSERT(can_substitute(k));
            lia_move ret;
            if (is_substituted_by_fresh(k)) 
                ret = subs_qfront_by_fresh(k, q, j);
            else 
                ret = subs_qfront_by_S(k, q, j);
            return join(ret, r);
        }

        lar_term l_term_from_row(unsigned k) const {
            lar_term ret;
            for (const auto& p : m_l_matrix.m_rows[k])
                ret.add_monomial(p.coeff(), p.var());

            return ret;
        }

        bool is_fixed(unsigned j) const {
            return lra.column_is_fixed(j);
        }

        term_o fix_vars(const lar_term& t) const {
            term_o ret;
            for (const auto& p : t) {
                if (is_fixed(p.var())) {
                    ret.c() += p.coeff() * this->lra.get_lower_bound(p.var()).x;
                }
                else {
                    ret.add_monomial(p.coeff(), p.var());
                }
            }
            return ret;
        }

        term_o fix_vars(const term_o& t) const {
            term_o ret;
            ret.c() = t.c();
            for (const auto& p : t) {
                if (is_fixed(p.var())) {
                    ret.c() += p.coeff() * this->lra.get_lower_bound(p.var()).x;
                }
                else {
                    ret.add_monomial(p.coeff(), p.var());
                }
            }
            return ret;
        }

        const unsigned sub_index(unsigned k) const {
            return m_k2s[k];
        }

        template <typename T>
        T pop_front_of_queue(std::queue<T>& q) const {
            T value = q.front();
            q.pop();
            return value;
        }

        bool subs_invariant(unsigned j) const {
            term_o ls = fix_vars(term_to_lar_solver(remove_fresh_vars(create_term_from_espace())));
            term_o t0 = m_lspace.to_term();
            term_o t1 = open_ml(t0);
            t1.add_monomial(mpq(1), j);
            term_o rs = fix_vars(t1);
            if (ls != rs) {
                std::cout << "enabling trace dio\n";
                enable_trace("dio");
                TRACE("dio", tout << "ls:"; print_term_o(ls, tout) << "\n";
                      tout << "rs:"; print_term_o(rs, tout) << "\n";);
                return false;
            }
            return true;
        }
        
        lia_move subs_with_S_and_fresh(protected_queue& q, unsigned j) {
            lia_move r = lia_move::undef;
            while (!q.empty() && r != lia_move::conflict && m_espace.size() <= m_tighten_size_max) {
                lia_move ret = subs_front_with_S_and_fresh(q, j);
                r = join(ret, r);
            }
            return r;
        }

        unsigned term_weight(const lar_term& t) const {
            unsigned weight = 0;
            for (const auto& p : t) {
                // Get index j from coefficient
                unsigned j = p.var();
        
                // Look up j in columns_to_terms map
                auto it = m_columns_to_terms.find(j);
                if (it != m_columns_to_terms.end())
                    weight = std::max(weight, static_cast<unsigned>(it->second.size()));
            }
            return weight;
        }

        lia_move tighten_terms_with_S() {
            // Copy changed terms to another vector for sorting
            std_vector<unsigned> sorted_changed_terms;
            std_vector<unsigned> processed_terms;
            for (unsigned j: m_terms_to_tighten) {                
                if (j >= lra.column_count() ||
                    !lra.column_has_term(j) ||
                    lra.column_is_free(j) ||
                    !lia.column_is_int(j)) {
                    processed_terms.push_back(j);
                    continue;
                }
                sorted_changed_terms.push_back(j);
            }

            // Sort by term_weight descending
            std::sort(sorted_changed_terms.begin(), sorted_changed_terms.end(),
                      [this](unsigned j1, unsigned j2) {
                          return term_weight(lra.get_term(j1)) > term_weight(lra.get_term(j2) );
                      });
        
            lia_move r = lia_move::undef;
            // Process sorted terms
            TRACE("dio", 
                  tout << "changed terms:"; for (auto j : sorted_changed_terms) tout << j << " "; tout << std::endl;
                  print_S(tout);
                  // lra.display(tout);
                  // print_bounds(tout);
            );
            for (unsigned j : sorted_changed_terms) {
                if (is_big_term_or_no_term(j)) {
                    m_terms_to_tighten.remove(j);
                    continue;
                }
                auto ret = tighten_bounds_for_term_column(j);
                m_terms_to_tighten.remove(j);
                                
                r = join(ret, r);
                if (r == lia_move::conflict)
                    break;
            }
            for (unsigned j : processed_terms) 
                m_terms_to_tighten.remove(j);
            TRACE("dio", tout << r << "\n");
            return r;
        }

        term_o create_term_from_espace() const {
            term_o t;
            for (const auto& p : m_espace.m_data) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_c;
            return t;
        }

        // We will have lar_t, and let j is lar_t.j(), the term column. 
        // In the m_espace we have lar_t. The result of open_ml((1*j)) is lar_t - (1, j).
        // So we have "equality" m_espace = open(m_lspace) + (1*lar_t.j())
        // return false iff seen a big number and dio_ignore_big_nums() is true
        bool init_substitutions(const lar_term& lar_t, protected_queue& q) {
            m_espace.clear();
            m_c = mpq(0);
            m_lspace.clear();
            m_lspace.add(mpq(1), lar_t.j());
            bool ret = true;
            SASSERT(get_extended_term_value(lar_t).is_zero());
            for (const auto& p : lar_t) {
                if (is_fixed(p.j())) {
                    const mpq& b = lia.lower_bound(p.j()).x;
                    if (ignore_big_nums() && b.is_big()) {
                        ret = false;
                        break;
                    }
                    m_c += p.coeff() * b;
                }
                else {
                    unsigned lj = lar_solver_to_local(p.j());
                    if (ignore_big_nums() && p.coeff().is_big()) {
                        ret = false;
                        break;
                    }
                    m_espace.add(p.coeff(), lj);;
                    if (can_substitute(lj))
                        q.push(lj);
                }
            }
            SASSERT(subs_invariant(lar_t.j()));
            return ret;
        }

        unsigned lar_solver_to_local(unsigned j) const {
            return m_var_register.external_to_local(j);
        }

        void process_fixed_in_espace() {
            std_vector<unsigned> fixed_vars;
            for (const auto & p: m_espace) {
                if (!var_is_fresh(p.var()) && is_fixed(local_to_lar_solver(p.var())))
                    fixed_vars.push_back(p.var());
            }
            for (unsigned j : fixed_vars) {
                m_c += m_espace[j] * lra.get_lower_bound(local_to_lar_solver(j)).x;
                m_espace.erase(j);
            }
        }


        // returns false if all coefficients are +-1 and true otherwise
        mpq find_second_smallest_coeff_in_espace() {
            mpq a; // first smallest
            mpq b; // second smallest
            for (const auto & [c, v]: m_espace) {
                if (var_is_fresh(v))
                    return mpq(1);
                mpq ac = abs(c);
                if (a.is_zero())
                    a = ac; // first smallest init
                else if (ac < a) {
                    b = a; // init b
                    a = ac; // first smallest improved
                }
                else if (ac < b) {                    
                    b = ac; // second smallest improved
                }
            }
            return b;
        }
        
        lia_move tighten_on_espace(unsigned j) {
            mpq g = gcd_of_coeffs(m_espace.m_data, true);
            if (g.is_one())
                return lia_move::undef;
            if (g.is_zero()) {
                handle_constant_term(j);
                if (!m_infeas_explanation.empty()) 
                    return lia_move::conflict;                
                return lia_move::undef;
            }
            // g is non-trivial, trying to tighten the bounds
            auto r = tighten_bounds_for_non_trivial_gcd(g, j, true);
            if (r == lia_move::undef)
                r = tighten_bounds_for_non_trivial_gcd(g, j, false);
            if (r == lia_move::undef && m_changed_f_columns.contains(j))
                r = lia_move::continue_with_check;            
            return r;
        }
        
        /* j is the index of the column representing a term
         Return lia_move::conflict if a conflict was found, lia_move::continue_with_check if j became a fixed variable, and undef
         otherwise
         When we have a constraint x + y  <= 8 then after the substitutions with S and fresh variables
         we might have x + y = 7t - 1 <= 8, where t is a term. Then 7t <= 9, or t <= 9/7, and we can enforce t <= floor(9/7) = 1.
         Then x + y = 7*1 - 1 <= 6: the bound is strenthgened. The constraint in this example comes from the upper bound on j, where
         j is the slack variable in x + y - j = 0.
        */
        lia_move tighten_bounds_for_term_column(unsigned j) {
            // q is the queue of variables that can be substituted in term_to_tighten
            protected_queue q;
            TRACE("dio", tout << "j:" << j << " , initial term t: "; print_lar_term_L(lra.get_term(j), tout) << std::endl;
                  for( const auto& p : lra.get_term(j).ext_coeffs()) {
                      lra.print_column_info(p.var(), tout);
                  }
                );
            if (!init_substitutions(lra.get_term(j), q))
                return lia_move::undef;
         
            TRACE("dio", tout << "t:";
                  tout << "m_espace:";
                  print_term_o(create_term_from_espace(), tout) << std::endl;
                  tout << "in lar_solver indices:\n";
                  print_term_o(term_to_lar_solver(create_term_from_espace()), tout) << "\n";
                  tout << "m_lspace:";
                  print_lar_term_L(m_lspace.to_term(), tout) << std::endl;);
            if (subs_with_S_and_fresh(q, j) == lia_move::conflict)
                return lia_move::conflict;
                
            process_fixed_in_espace();
            SASSERT(subs_invariant(j));
            return tighten_on_espace(j);
        }

        void remove_fresh_from_espace() {
            protected_queue q;
            for (const auto& p : m_espace.m_data) {
                if (var_is_fresh(p.var()))
                    q.push(p.var());
            }
            while (!q.empty()) {
                unsigned xt = q.pop_front();
                // add the fresh term to m_espace
                const lar_term& e = m_fresh_k2xt_terms.get_by_val(xt).first;
                mpq coeff = m_espace[xt];  // need to copy since it will be zeroed
                m_espace.erase(xt);        // m_espace[k] = 0;
                for (const auto& p : e) {
                    unsigned j = p.var();
                    if (j == xt)
                        continue;
                    m_espace.add(p.coeff() * coeff, j);
                    // do we need to add j to the queue?
                    if (m_espace.has(j) && var_is_fresh(j))
                        q.push(j);
                }
            }
        }

        impq get_extended_term_value(const lar_term& t) const {
            impq ret;
            for (const auto& p : t.ext_coeffs()) {
                ret += p.coeff() * lra.get_column_value(p.j());
            }
            return ret;
        }

        mpq get_term_value(const term_o& t) const {
            mpq ret = t.c();
            for (const auto& p : t) {
                ret += p.coeff() * lra.get_column_value(p.var()).x;
            }
            return ret;
        }

        mpq get_value_of_espace() const {
            mpq r;
            for (const auto & p : m_espace.m_data) {
                r += p.coeff()*lra.get_column_value(local_to_lar_solver(p.var())).x;
                SASSERT(lra.get_column_value(local_to_lar_solver(p.var())).y.is_zero());
            }
            return r;
        }

        void get_expl_from_meta_term(const lar_term& t, explanation& ex, const mpq & gcd) {
            u_dependency* dep = explain_fixed_in_meta_term(t, gcd);
            for (constraint_index ci : lra.flatten(dep))
                ex.push_back(ci);
        }

        void handle_constant_term(unsigned j) {
            if (m_c.is_zero()) {
                return;
            }
            mpq rs;
            bool is_strict;
            u_dependency* b_dep = nullptr;
            if (lra.has_upper_bound(j, b_dep, rs, is_strict)) {
                if (m_c > rs || (is_strict && m_c == rs)) {
                    u_dependency* dep =
                        lra.join_deps(explain_fixed(lra.get_term(j), mpq(0)),
                                      explain_fixed_in_meta_term(m_lspace.m_data, mpq(0)));
                    dep = lra.join_deps(
                        dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                    return;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                if (m_c < rs || (is_strict && m_c == rs)) {
                    u_dependency* dep =
                        lra.join_deps(explain_fixed(lra.get_term(j), mpq(0)),
                                      explain_fixed_in_meta_term(m_lspace.m_data, mpq(0)));
                    dep = lra.join_deps(
                        dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                }
            }
        }

        
        // m_espace contains the coefficients of the term
        // m_c contains the fixed part of the term
        // m_tmp_l is the linear combination of the equations that removes the
        // substituted variables.
        // returns true iff the conflict is found
        lia_move tighten_bounds_for_non_trivial_gcd(const mpq& g, unsigned j,
                                                    bool is_upper) {
            mpq rs;
            bool is_strict = false;
            u_dependency* b_dep = nullptr;
            SASSERT(!g.is_zero() && !g.is_one());

            if (lra.has_bound_of_type(j, b_dep, rs, is_strict, is_upper)) {
                TRACE("dio", tout << "x" << j << (is_upper? " <= ":" >= ") << rs << std::endl;);
                mpq rs_g = (rs - m_c) % g;
                if (rs_g.is_neg())
                    rs_g += g;
                
                SASSERT(rs_g.is_int() && !rs_g.is_neg());

                TRACE("dio", tout << "(rs - m_c) % g:" << rs_g << std::endl;);
                if (!rs_g.is_zero()) {
                    if (tighten_bound_kind(g, j, rs, rs_g, is_upper))
                        return lia_move::conflict;
                }
                else 
                    TRACE("dio", tout << "rs_g is zero: no improvement in the bound\n";);
            }
            return lia_move::undef;
        }

        // returns true only on a conflict
        bool tighten_bound_kind(const mpq& g, unsigned j, const mpq& rs, const mpq& rs_g, bool upper) {
            /*
              Variable j corresponds to term t = lra.get_term(j). 
              At this point we substituted some variables of t with the equivalent terms 
              in S and the equivalent expressions containing fresh variables: 
              t = sum{a_i * x_i: i in K} + sum{b_i * x_i: i in P }, where P and K are 
              disjoint sets, a_i % g = 0 for each i in K, and x_i is a fixed variable 
              for each i in P. 

              In the notations of the program:
              m_espace corresponds to sum{a_i * x_i: i in K}, 
              m_c is the value of sum{b_i * x_i: i in P}, 
              open_ml(m_lspace) gives sum{a_i*x_i: i in K} + sum{b_i * x_i: i in P}.

              We can rewrite t = g*t_ + m_c, where t_ = sum{(a_i/g)*x_i: i in K}.
              Let us suppose that upper is true and rs is an upper bound of variable j, 
              or t = g*t_ + m_c <= rs.  

              Parameter rs_g is defined as (rs - m_c) % g. Notice that rs_g does not change 
              when m_c changes by a multiple of g. We also know that rs_g > 0. 
              For some integer k we have rs - m_c = k*g + rs_g.

              Starting with g*t_ + m_c <= rs, we proceed to g*t_ <= rs - m_c = k*g + rs_g. 
              We can discard rs_g on the right: g*t_ <= k*g = rs - m_c - rs_g. 
              Adding m_c to both sides gives us g*t_ + m_c <= rs - rs_g, or t <= rs - rs_g.

              In case of a lower bound we have 
              t = g*t_+ m_c >= rs
              Then g*t_ >= rs - m_c = k*g + rs_g => g*t_ >= k*g + g.
              Adding m_c to both sides gets us
              g*t_ + m_c >= k*g + g + m_c = rs - m_c - rs_g + g + m_c = rs + (g - rs_g).  

              Each fixed variable i in P such that b_i is divisible by g can be moved from P to K.
              Then we apply all arguments above, and get the same result, since m_c changes 
              by a multiple of g.
            */

            
            mpq bound = upper ? rs - rs_g : rs + g - rs_g;
            TRACE("dio", tout << "is upper:" << upper << std::endl;
                  tout << "new " << (upper ? "upper" : "lower") << " bound:" << bound << std::endl;);

            SASSERT((upper && bound < lra.get_upper_bound(j).x) ||
                    (!upper && bound > lra.get_lower_bound(j).x));
            lconstraint_kind kind = upper ? lconstraint_kind::LE : lconstraint_kind::GE;
            u_dependency* dep = upper ? lra.get_column_upper_bound_witness(j) : lra.get_column_lower_bound_witness(j);
            auto fixed_part_of_the_term = open_fixed_from_ml(m_lspace);
            TRACE("dio",
                  tout << "fixed_part_of_the_term:";
                  print_term_o(fixed_part_of_the_term.to_term(), tout);
                );
            // the right side is off by 1*j from m_espace
            if (is_fixed(j))
                fixed_part_of_the_term.add(mpq(1), j);
            for (const auto& p: fixed_part_of_the_term) {
                SASSERT(is_fixed(p.var()));                
                if (p.coeff().is_int() && (p.coeff() % g).is_zero()) {
                    // we can skip this dependency as explained above
                    TRACE("dio", tout << "skipped dep:\n"; print_deps(tout, lra.get_bound_constraint_witnesses_for_column(p.var())););
                    continue;
                }
                dep = lra.join_deps(dep, lra.get_bound_constraint_witnesses_for_column(p.var()));         
            }
            TRACE("dio", tout << "jterm:";
                  print_lar_term_L(lra.get_term(j), tout) << "\ndep:";
                  print_deps(tout, dep) << std::endl;);
            if (lra.settings().get_cancel_flag())
                return false;
            lra.update_column_type_and_bound(j, kind, bound, dep);
            lp_status st = lra.find_feasible_solution();
            if (is_sat(st) || st == lp::lp_status::CANCELLED)
                return false;
            lra.get_infeasibility_explanation(m_infeas_explanation);
            return true;
        }

        // if gcd is not zero we ignore all monomials with the coefficients divisible by gcd
        template <typename T>
        u_dependency* explain_fixed_in_meta_term(const T& t, const mpq& gcd) const {
            return explain_fixed(open_fixed_from_ml(t), gcd);
        }

        // if gcd is not zero we ignore all monomials with the coefficients divisible by gcd
        template <typename T>
        u_dependency* explain_fixed(const T& t, const mpq& gcd) const {
            u_dependency* dep = nullptr;
            if (gcd.is_zero()) {
                for (const auto& p : t) {
                    if (is_fixed(p.var())) {
                        u_dependency* bound_dep = lra.get_bound_constraint_witnesses_for_column(p.var());
                        dep = lra.join_deps(dep, bound_dep);
                    }
                }
            } else {
                for (const auto& p : t) {
                    if (is_fixed(p.var())) {
                        if ((p.coeff()/gcd).is_int()) continue;
                        
                        u_dependency* bound_dep = lra.get_bound_constraint_witnesses_for_column(p.var());
                        dep = lra.join_deps(dep, bound_dep);
                    }
                }
            }
            return dep;
        }

        void fill_f_vector(std_vector<unsigned> & f_vector) {
            for (unsigned ei = 0; ei < m_e_matrix.row_count(); ei++) {
                if (belongs_to_s(ei)) continue;
                if (m_e_matrix.m_rows[ei].size() == 0) {
                    if (m_sum_of_fixed[ei].is_zero()) {
                        continue;
                    }
                    else {
                        set_rewrite_conflict(ei, mpq(0));
                        return;
                    }
                }
                f_vector.push_back(ei);
            }
        }
        
        lia_move process_f(std_vector<unsigned>& f_vector) {
            if (has_conflict_index())
                return lia_move::conflict;
            lia_move r;
            do {
                r = rewrite_eqs(f_vector);
                if (lra.settings().get_cancel_flag()) 
                    return lia_move::undef;
                if (r == lia_move::conflict || r == lia_move::undef) 
                    break;
                SASSERT(m_changed_f_columns.size() == 0);
            }
            while (f_vector.size());

            if (r == lia_move::conflict) {
                return lia_move::conflict;                
            }
            TRACE("dio_s", print_S(tout));

            return lia_move::undef;
        }

        lia_move process_f_and_tighten_terms(std_vector<unsigned>& f_vector) {
            lia_move ret = process_f(f_vector);
            if (ret != lia_move::undef)
                return ret;
            ret = tighten_terms_with_S();
            if (ret == lia_move::conflict) 
                lra.stats().m_dio_tighten_conflicts++;
            TRACE("dio", print_S(tout););
            return ret;
        }

        lia_move check_fixing(unsigned j) const {
            // do not change entry here
            unsigned ei = m_k2s[j];  // entry index
            mpq g = mpq(0);          // gcd
            mpq c = m_sum_of_fixed[ei];
            for (const auto& p : m_e_matrix.m_rows[m_k2s[j]]) {
                if (p.var() == j) {
                    const mpq& j_coeff = p.coeff();
                    SASSERT(j_coeff.is_one() || j_coeff.is_minus_one());
                    c += j_coeff * lra.get_lower_bound(local_to_lar_solver(j)).x;
                    TRACE("dio_br", tout << "the value of the vixed var is:" << lra.get_lower_bound(local_to_lar_solver(j)).x << ", m_sum_of_fixed[" << ei << "]:" << m_sum_of_fixed[ei] << ", new free coeff c:" << c << std::endl;);
                    continue;
                }
                if (g.is_zero()) {
                    g = abs(p.coeff());
                }
                else {
                    g = gcd(g, p.coeff());
                }
                if (g.is_one()) return lia_move::undef;
            }
            if (!(c / g).is_int()) {
                return lia_move::conflict;
            }
            return lia_move::undef;
        }
        // here j is a local variable
        lia_move fix_var(unsigned j) {
            SASSERT(is_fixed(local_to_lar_solver(j)));
            /*
              We only can get a conflict when j is substituted, and the entry m_k2s[j], the entry defining the substitution  becomes infeaseable, that is the gcd of the monomial coeffitients does not divide the free coefficient. In other cases the gcd of the monomials will remain to be 1.
            */
            if (m_k2s.has_key(j)) {  // j is substituted but using an entry
                TRACE("dio_br",
                      tout << "fixed j:" << j << ", was substited by ";
                      print_entry(m_k2s[j], tout););
                if (check_fixing(j) == lia_move::conflict) {
                    return lia_move::conflict;
                }
            }
            return lia_move::undef;
        }

        unsigned get_number_of_int_inf() const {
            return (unsigned)std::count_if(
                lra.r_basis().begin(), lra.r_basis().end(),
                [this](unsigned j) {
                    return lia.column_is_int_inf(j);
                });
        }


        bool columns_to_terms_is_correct() const {
            std::unordered_map<unsigned, std::unordered_set<unsigned>> c2t;
            for (unsigned k = 0; k < lra.terms().size(); k++) {
                const lar_term* t = lra.terms()[k];
                if (!lia.column_is_int(t->j())) continue;
                SASSERT(t->j() != UINT_MAX);
                for (const auto& p : (*t).ext_coeffs()) {
                    unsigned j = p.var();
                    auto it = c2t.find(j);
                    if (it == c2t.end()) {
                        std::unordered_set<unsigned> s;
                        s.insert(t->j());
                        c2t[j] = s;
                    }
                    else {
                        it->second.insert(t->j());
                    }
                }
            }
            for (const auto& p : c2t) {
                unsigned j = p.first;
                const auto it = m_columns_to_terms.find(j);
                if (it == m_columns_to_terms.end()) {
                    TRACE("dio", tout << "column j" << j << " is not registered" << std::endl; tout << "the column belongs to the the following terms:"; for (unsigned tj : p.second) { tout << " " << tj; } tout << std::endl;);

                    return false;
                }
                if (it->second != p.second) {
                    TRACE("dioph_eq_deb", tout << "m_columns_to_terms[" << j << "] has to be "; tout << "{"; for (unsigned lll : p.second) { tout << lll << ", "; } tout << "}, \nbut it is {"; for (unsigned lll : it->second) { tout << lll << ", "; }; tout << "}" << std::endl;

                        );
                    return false;
                }
            }
            // reverse inclusion
            for (const auto& p : m_columns_to_terms) {
                unsigned j = p.first;
                const auto it = c2t.find(j);
                if (it == c2t.end()) {
                    TRACE("dio", tout << "should not be registered j " << j << std::endl;
                          lra.print_terms(tout););
                    return false;
                }
                if (it->second != p.second) {
                    return false;
                }
            }
            return true;
        }
        bool is_in_sync() const {
            for (unsigned j = 0; j < m_e_matrix.column_count(); j++) {
                unsigned external_j = m_var_register.local_to_external(j);
                if (external_j == UINT_MAX)
                    continue;
                if (external_j >= lra.column_count() && m_e_matrix.m_columns[j].size()) 
                    return false;
                // It is OK to have an empty column in m_e_matrix.

            }

            for (unsigned ei = 0; ei < m_e_matrix.row_count(); ei++) {
                auto it = m_row2fresh_defs.find(ei);
                if (it != m_row2fresh_defs.end()) {
                    for (unsigned xt : it->second) {
                        if (!m_fresh_k2xt_terms.has_second_key(xt))
                            return false;
                    }
                }
            }

            return columns_to_terms_is_correct();
        }

    public:
        lia_move check() {
            lra.stats().m_dio_calls++;
            TRACE("dio", tout << lra.stats().m_dio_calls << std::endl;);
            std_vector<unsigned> f_vector;
            lia_move ret;
            do {
                init(f_vector);
                ret = process_f_and_tighten_terms(f_vector);
            } 
            while (ret == lia_move::continue_with_check);

            return ret;
        }

    private:
        unsigned get_markovich_number(unsigned k, unsigned h) {
            size_t col_size = m_e_matrix.m_columns[k].size(); 
            size_t row_size = m_e_matrix.m_rows[h].size();
            // Subtract 1 from sizes once and multiply
            return static_cast<unsigned>((col_size - 1) * (row_size - 1));
        }
        
        std::tuple<mpq, unsigned, int, unsigned> find_minimal_abs_coeff(unsigned ei) {
            bool first = true;
            mpq ahk;
            unsigned k = -1;
            int k_sign = 0;
            mpq t;
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                t = abs(p.coeff());
                if (first || t < ahk) {
                    ahk = t;
                    k_sign = p.coeff().is_pos() ? 1 : -1;
                    k = p.var();
                    first = false;
                    if (ahk.is_one())
                        break;
                }
            }

            return std::make_tuple(ahk, k, k_sign, get_markovich_number(k, ei));
        }

        bool j_sign_is_correct(unsigned ei, unsigned j, int j_sign) {
            const auto& row = m_e_matrix.m_rows[ei];
            auto it = std::find_if(row.begin(), row.end(), [j](const auto& p) { return p.var() == j; });
            if (it == row.end()) return false;
            return (it->coeff() == mpq(1) && j_sign == 1) ||
                (it->coeff() == mpq(-1) && j_sign == -1);
        }
        // j is the variable to eliminate, or substitude, it appears in row ei of m_e_matrix with
        // a coefficient equal to j_sign which is +-1
        void eliminate_var_in_f(unsigned ei, unsigned j, int j_sign) {
            SASSERT(belongs_to_s(ei));
            const auto& e = m_sum_of_fixed[ei];
            SASSERT(j_sign_is_correct(ei, j, j_sign));
            TRACE("dio", tout << "eliminate var:" << j << " by using:";
                  print_entry(ei, tout) << std::endl;);
            auto& column = m_e_matrix.m_columns[j];
            auto it =
                std::find_if(column.begin(), column.end(),
                             [ei](const auto& cell) {
                                 return cell.var() == ei;
                             });
            unsigned pivot_col_cell_index = (unsigned)std::distance(column.begin(), it);
            if (pivot_col_cell_index != 0) {
                // swap the pivot column cell with the head cell
                auto c = column[0];
                column[0] = column[pivot_col_cell_index];
                column[pivot_col_cell_index] = c;

                m_e_matrix.m_rows[ei][column[0].offset()].offset() = 0;
                m_e_matrix.m_rows[c.var()][c.offset()].offset() =
                    pivot_col_cell_index;
            }

            for (auto cell_to_process = column.size(); cell_to_process-- > 0; ) {
                auto& c = column[cell_to_process];
                if (belongs_to_s(c.var())) 
                    continue;

                SASSERT(c.var() != ei && entry_invariant(c.var()));
                mpq coeff = m_e_matrix.get_val(c);
                unsigned i = c.var();
                TRACE("dio", tout << "before pivot entry:";
                      print_entry(i, tout) << std::endl;);
                m_sum_of_fixed[i] -= j_sign * coeff * e;
                m_e_matrix.pivot_row_to_row_given_cell_with_sign(ei, c, j, j_sign);
                // m_sum_of_fixed[i].m_l -= j_sign * coeff * e.m_l;
                m_l_matrix.add_rows(-j_sign * coeff, ei, i);
                TRACE("dio", tout << "after pivoting c_row:";
                      print_entry(i, tout););
                CTRACE(
                    "dio", !entry_invariant(i), tout << "invariant delta:"; {
                        print_term_o(get_term_from_entry(ei) -
                                     fix_vars(open_ml(m_l_matrix.m_rows[ei])),
                                     tout)
                            << std::endl;
                    });
                SASSERT(entry_invariant(i));
            }
            SASSERT(is_eliminated_from_f(j));
        }
        // j is the variable to eliminate, or substitude, it appears in term t with
        // a coefficient equal to j_sign which is +-1 ,
        // matrix m_l_matrix is not changed since it is a substitution of a fresh variable
        void eliminate_var_in_f_with_term(const lar_term& t, unsigned j, int j_sign) {
            SASSERT(abs(t.get_coeff(j)).is_one());
            TRACE("dio", tout << "eliminate var:" << j << " by using:";
                  print_lar_term_L(t, tout) << std::endl;);
            auto& column = m_e_matrix.m_columns[j];

            for (auto cell_to_process = column.size(); cell_to_process-- > 0; ) {
                auto& c = column[cell_to_process];
                if (belongs_to_s(c.var())) 
                    continue;

                mpq coeff = m_e_matrix.get_val(c);
                TRACE("dio", tout << "before pivot entry :"; print_entry(c.var(), tout) << std::endl;);
                m_e_matrix.pivot_term_to_row_given_cell(t, c, j, j_sign);
                TRACE("dio", tout << "after pivoting c_row:";
                      print_entry(c.var(), tout););
                SASSERT(entry_invariant(c.var()));
            }
            SASSERT(is_eliminated_from_f(j));
        }

        bool is_eliminated_from_f(unsigned j) const {
            for (unsigned ei = 0; ei < m_e_matrix.row_count(); ei++) {
                if (!belongs_to_f(ei))
                    continue;
                const auto& row = m_e_matrix.m_rows[ei];
                bool eliminated_in_row = all_of(row, [j](auto & p) { return p.var() != j; });
                if (!eliminated_in_row)
                    return false;
            }
            return true;
        }

        term_o term_to_lar_solver(const term_o& eterm) const {
            term_o ret;
            for (const auto& p : eterm) {
                ret.add_monomial(p.coeff(), local_to_lar_solver(p.var()));
            }
            ret.c() = eterm.c();
            return ret;
        }

        bool belongs_to_s(unsigned ei) const {
            return m_k2s.has_val(ei);
        }

        bool entry_invariant(unsigned ei) const {
            if (lra.settings().get_cancel_flag())
                return true;
            
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                if (!p.coeff().is_int()) {
                    return false;
                }
                if (var_is_fresh(p.var()))
                    continue;
                unsigned j = local_to_lar_solver(p.var());
                if (is_fixed(j)) {
                    enable_trace("dio");                    
                    TRACE("dio", tout << "x" << j << "(local: " << "x" << p.var() << ") should not be fixed\nbad entry:"; print_entry(ei, tout) << "\n";);
                    return false;
                }
            }

            term_o ls = term_to_lar_solver(remove_fresh_vars(get_term_from_entry(ei)));
            mpq ls_val = get_term_value(ls);
            if (!ls_val.is_zero()) {
                std::cout << "ls_val is not zero\n";
                enable_trace("dio");
                TRACE("dio", {
                        tout << "get_term_from_entry(" << ei << "):";
                        print_term_o(get_term_from_entry(ei), tout) << std::endl;
                        tout << "ls:";
                        print_term_o(ls, tout) << std::endl;
                        tout << "e.m_l:";
                        print_lar_term_L(l_term_from_row(ei), tout) << std::endl;
                        tout << "open_ml(e.m_l):";
                        print_lar_term_L(open_ml(l_term_from_row(ei)), tout) << std::endl;
                        tout << "rs:";
                        print_term_o(fix_vars(open_ml(m_l_matrix.m_rows[ei])), tout) << std::endl;
                    });

                return false;
            }
            bool ret = ls == fix_vars(open_ml(m_l_matrix.m_rows[ei]));
            if (!ret) {
                enable_trace("dio");
                CTRACE("dio", !ret,
                   {
                       tout << "get_term_from_entry(" << ei << "):";
                       print_term_o(get_term_from_entry(ei), tout) << std::endl;
                       tout << "ls:";
                       print_term_o(ls, tout) << std::endl;
                       tout << "e.m_l:";
                       print_lar_term_L(l_term_from_row(ei), tout) << std::endl;
                       tout << "open_ml(e.m_l):";
                       print_lar_term_L(open_ml(l_term_from_row(ei)), tout) << std::endl;
                       tout << "rs:";
                       print_term_o(fix_vars(open_ml(m_l_matrix.m_rows[ei])), tout) << std::endl;
                   });
            }
            return ret;
        }

        term_o remove_fresh_vars(const term_o& tt) const {
            term_o t = tt;
            protected_queue q;
            for (const auto& p : t) {
                if (var_is_fresh(p.j())) {
                    q.push(p.j());
                }
            }
            while (!q.empty()) {
                unsigned xt = q.pop_front();  // xt is a fresh var
                const lar_term& fresh_t = m_fresh_k2xt_terms.get_by_val(xt).first;
                TRACE("dio_remove_fresh", print_lar_term_L(fresh_t, tout););
                SASSERT(fresh_t.get_coeff(xt).is_minus_one());
                if (!t.contains(xt))
                    continue;
                mpq xt_coeff = t.get_coeff(xt);
                t += xt_coeff * fresh_t;
                SASSERT(t.contains(xt) == false);
                for (const auto& p : t) {
                    if (var_is_fresh(p.j())) {
                        q.push(p.j());
                    }
                }
            }
            return t;
        }

        std::ostream& print_ml(const lar_term& ml, std::ostream& out) const {
            term_o opened_ml = open_ml(ml);
            return print_lar_term_L(opened_ml, out);
        }

        // collect only fixed variables in a term 
        template <typename T>
        term_with_index open_fixed_from_ml(const T& ml) const {
            term_with_index r;
            for (const auto& v : ml) {
                for (const auto & p : lra.get_term(v.var()).ext_coeffs()) {
                    if (lra.column_is_fixed(p.var()))
                        r.add(v.coeff() * p.coeff(), p.var());
                }
            }
            return r;
        }
        
        
        template <typename T>
        term_o open_ml(const T& ml) const {
            term_o r;
            for (const auto& p : ml) {
                r += p.coeff() * (lra.get_term(p.var()) - lar_term(p.var()));
            }
            return r;
        }

        void open_l_term_to_espace(unsigned ei, mpq& c) {
            m_espace.clear();
            for (const auto& p : m_l_matrix.m_rows[ei]) {
                const lar_term& t = lra.get_term(p.var());
                for (const auto& q : t.ext_coeffs()) {
                    if (is_fixed(q.var())) {
                        c += p.coeff() * q.coeff() * lia.lower_bound(q.var()).x;
                    }
                    else {
                        m_espace.add(p.coeff() * q.coeff(), q.var());
                    }
                }
            }
        }

        void copy_row_to_espace(unsigned ei) {
            m_espace.clear();
            auto& row = m_e_matrix.m_rows[ei];
            for (const auto& cell : row)
                m_espace.add(cell.coeff(), cell.var());
        }

        // The idea is to be able remove this fresh definition when the row h changes.
        // The row can change if it depends on the term that is deleted, or on a variable that becomes fixed/unfixed
        // fr_j is a fresh variable
        void register_var_in_fresh_defs(unsigned h, unsigned fr_j) {
            auto it = m_row2fresh_defs.find(h);
            if (it == m_row2fresh_defs.end()) {
                m_row2fresh_defs[h].push_back(fr_j);
            }
            else {
                it->second.push_back(fr_j);
            }
        }

        // k is the variable to substitute
        void fresh_var_step(unsigned h, unsigned k, const mpq& ahk) {
            // step 7 from the paper
            // xt is the fresh variable
            unsigned xt = add_var(UINT_MAX);
            while (xt >= m_e_matrix.column_count())
                m_e_matrix.add_column();
            // Create a term the fresh variable definition: it seems needed in Debug only
            /* Let eh = sum(ai*xi) + c. For each i != k, let ai = qi*ahk + ri, and
               let c = c_q * ahk + c_r. eh = ahk*(x_k + sum{qi*xi|i != k} + c_q) +
               sum {ri*xi|i!= k} + c_r. Then -xt + x_k + sum {qi*x_i)| i != k} + c_q
               will be the fresh row eh = ahk*xt +  sum {ri*x_i | i != k} + c_r  is
               the row m_e_matrix[e.m_row_index]
            */
            mpq q, r;
            lar_term fresh_t;  // fresh term
            fresh_t.add_monomial(-mpq(1), xt);
            fresh_t.add_monomial(mpq(1), k);
            for (const auto& i : m_e_matrix.m_rows[h]) {
                const mpq& ai = i.coeff();
                if (i.var() == k)
                    continue;
                q = machine_div_rem(ai, ahk, r);
                if (!q.is_zero())
                    fresh_t.add_monomial(q, i.var());
            }

            m_fresh_k2xt_terms.add(k, xt, std::make_pair(fresh_t, h));
            SASSERT(var_is_fresh(xt));
            register_var_in_fresh_defs(h, xt);
            eliminate_var_in_f_with_term(fresh_t, k, 1);
        }

        std::ostream& print_entry(unsigned i, std::ostream& out,
                                  bool print_dep = false, bool print_in_S = true, bool print_column_info = false) const {
            unsigned j = m_k2s.has_val(i) ? m_k2s.get_key(i) : UINT_MAX;
            out << "entry " << i << ": ";
            if (j != UINT_MAX) 
                out << "x" << j << " ";               
            out << "{\n";
            
            print_term_o(get_term_from_entry(i), out << "\t") << " = 0\n";
            if (print_dep) {
                auto l_term = l_term_from_row(i);
                out << "\tm_l:{";
                print_lar_term_L(l_term, out) << "}, ";
                print_ml(l_term, out) << std::endl;
                out << "expl of fixed in m_l:{\n";
                print_deps(out, explain_fixed_in_meta_term(l_term, mpq(0)));
                out << "}\n";
            }
            if (belongs_to_f(i)) 
                out << "in F\n";
            else if (print_in_S) 
                out << "in S\n";
            
            if (print_column_info) {
                bool has_fresh = false;
                for (const auto& p : m_e_matrix[i] ) {
                    if (var_is_fresh(p.var())) {
                        has_fresh = true;
                        break;
                    }
                }
                if (!has_fresh) {
                    for (const auto& p : get_term_from_entry(i)) {
                        auto j = local_to_lar_solver(p.var());
                        out << "\tx" << p.var() << " := " << lra.get_column_value(j) << " " << lra.get_bounds_string(j) << "\n";
                    }                    
                }
                else {
                    out << "\thas fresh vars\n";
                }
            }
            out << "}\n";
            return out;
        }

        bool belongs_to_f(unsigned ei) const {
            return !m_k2s.has_val(ei);
        }

        void remove_from_S(unsigned ei) {
            m_k2s.erase_val(ei);
        }

        // k is the variable that is being substituted
        // h is the index of the entry 
        void move_entry_from_f_to_s(unsigned k, unsigned h) {
            m_k2s.add(k, h);
        }

        // this is the step 6 or 7 of the algorithm
        // returns lia_move::conflict if a conflict was found, continue_with_check if some progress has been achieved,
        // otherwise returns lia_move::undef
        lia_move rewrite_eqs(std_vector<unsigned>& f_vector) {
            if (f_vector.size() == 0)
                return lia_move::undef;
            unsigned h = -1, kh = 0; // the initial value of kh does not matter, assign to remove the warning
            unsigned n = 0;  // number of choices for a fresh variable
            mpq min_ahk;
            int kh_sign = 0; // the initial values of kh_sign and h_markovich_number do not matter, assign to remove the warning
            unsigned h_markovich_number = 0;
            unsigned ih = -1; // f_vector[ih] = h
            for (unsigned i = 0; i < f_vector.size(); i++) {
                unsigned ei = f_vector[i];
                SASSERT (belongs_to_f(ei));
                if (m_e_matrix.m_rows[ei].size() == 0) {
                    if (m_sum_of_fixed[ei].is_zero()) {
                        continue;
                    }
                    else {
                        set_rewrite_conflict(ei, mpq(0));
                        return lia_move::conflict;
                    }
                }

                auto [ahk, k, k_sign, markovich_number] = find_minimal_abs_coeff(ei);
                mpq gcd;
                if (!normalize_e_by_gcd(ei, gcd)) {
                    set_rewrite_conflict(ei, gcd);
                    return lia_move::conflict;
                }
                if (!gcd.is_one()) 
                    ahk /= gcd;

                if (n == 0 || min_ahk > ahk) {
                    ih = i;
                    n = 1;
                    min_ahk = ahk;
                    h = ei;
                    kh = k;
                    kh_sign = k_sign;
                    h_markovich_number = markovich_number;
                    continue;
                }
                if (min_ahk == ahk && h_markovich_number > markovich_number) {
                    ih = i;
                    h = ei;
                    kh = k;
                    kh_sign = k_sign;
                    h_markovich_number = markovich_number;
                }
                if (min_ahk.is_one() && h_markovich_number == 0)
                    break;
            }
            if (h == UINT_MAX) {
                TRACE("dio", tout << "done - cannot find an entry to rewrite\n");
                return lia_move::undef;
            }
            SASSERT(h == f_vector[ih]);
            if (min_ahk.is_one()) {
                TRACE("dio", tout << "push to S:\n"; print_entry(h, tout););
                move_entry_from_f_to_s(kh, h);
                eliminate_var_in_f(h, kh, kh_sign);
                f_vector[ih] = f_vector.back();                
                f_vector.pop_back();
            }
            else  {                   
                fresh_var_step(h, kh, min_ahk * mpq(kh_sign));
            }
            
            return lia_move::continue_with_check;
        }

    public:

        void explain(explanation& ex) {
            SASSERT(ex.empty());
            if (has_conflict_index()) {
                TRACE("dio", print_entry(m_normalize_conflict_index, tout << "conflict:", true) << std::endl;);
                for (auto ci : lra.flatten(explain_fixed_in_meta_term(m_l_matrix.m_rows[m_normalize_conflict_index], m_normalize_conflict_gcd)))
                    ex.push_back(ci);
            } 
            else {
                for (auto ci : m_infeas_explanation) 
                    ex.push_back(ci.ci());                
            }
            TRACE("dio", lra.print_expl(tout, ex););
        }

        // needed for the template bound_analyzer_on_row.h
        const lar_solver& lp() const { return lra; }
        lar_solver& lp() {return lra;}
        bool some_terms_are_ignored() const {
            return m_some_terms_are_ignored;
        }
    };
    // Constructor definition
    dioph_eq::dioph_eq(int_solver& lia) {
        m_imp = alloc(imp, lia, lia.lra);
    }
    dioph_eq::~dioph_eq() {
        dealloc(m_imp);
    }

    lia_move dioph_eq::check() {
        return m_imp->check();
    }

    void dioph_eq::explain(lp::explanation& ex) {
        m_imp->explain(ex);
    }

    bool dioph_eq::some_terms_are_ignored() const {
        return m_imp->some_terms_are_ignored();
    }
    

}  // namespace lp
