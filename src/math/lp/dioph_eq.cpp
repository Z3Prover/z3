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

    struct bijection {
        std::unordered_map<unsigned, unsigned> m_map;
        std::unordered_map<unsigned, unsigned> m_rev_map;

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
            for (const auto& p : m_k2s.m_map) {
                print_entry(p.second, out, false, false);
            }
            return out;
        }

        std::ostream& print_bounds(std::ostream& out) {
            out << "bounds:\n";
            for (unsigned v = 0; v < m_var_register.size(); ++v) {
                unsigned j = m_var_register.local_to_external(v);
                out << "j" << j << ":= " << lra.get_column_value(j) << ": ";
                if (lra.column_has_lower_bound(j))
                    out << lra.column_lower_bound(j).x << " <= ";
                out << "x" << v;
                if (lra.column_has_upper_bound(j))
                    out << " <= " << lra.column_upper_bound(j).x;
                out << "\n";
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

        std_vector<mpq> m_sum_of_fixed;
        var_register m_var_register;
        // the terms are stored in m_A and m_c
        static_matrix<mpq, mpq> m_e_matrix;  // the rows of the matrix are the terms,
        static_matrix<mpq, mpq> m_l_matrix;  // the rows of the matrix are the l_terms providing the certificate to the entries modulo the constant part: look an entry_invariant that assures that the each two rows are in sync.
        int_solver& lia;
        lar_solver& lra;
        explanation m_infeas_explanation;
        bool m_report_branch = false;

        // set F
        // iterate over all rows from 0 to m_e_matrix.row_count() - 1 and return those i such !m_k2s.has_val(i)
        // set S - iterate over bijection m_k2s
        mpq m_c;  // the constant of the equation
        struct term_with_index {
            // The invariant is that m_index[m_data[k].var()] = k, for each 0 <= k < m_data.size(),
            // and m_index[j] = -1, or m_tmp[m_index[j]].var() = j, for every 0 <= j < m_index.size().
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
        indexed_uint_set m_changed_columns;
        indexed_uint_set m_changed_terms;  // a term is defined by its column j, as in lar_solver.get_term(j)
        indexed_uint_set m_tightened_columns; // the column that got tightened by the tigthening phase, 
        // m_column_to_terms[j] is the set of all k such lra.get_term(k) depends on j
        std::unordered_map<unsigned, std::unordered_set<unsigned>> m_columns_to_terms;

        unsigned m_conflict_index = -1;  // the row index of the conflict
        unsigned m_max_of_branching_iterations = 0;
        unsigned m_number_of_branching_calls;
        struct branch {
            unsigned m_j = UINT_MAX;
            mpq m_rs;
            // if m_left is true, then the branch is interpreted
            // as x[j] <= m_rs
            // otherwise x[j] >= m_rs
            bool m_left;
            bool m_fully_explored = false;
            void flip() {
                SASSERT(m_fully_explored == false);
                m_left = !m_left;
                m_fully_explored = true;
            }
        };
        struct variable_branch_stats {
            std::vector<unsigned> m_ii_after_left;
            // g_right[i] - the rumber of int infeasible after taking the i-ith
            // right branch
            std::vector<unsigned> m_ii_after_right;

            double score() const {
                double avm_lefts =
                    m_ii_after_left.size()
                    ? static_cast<double>(std::accumulate(
                                              m_ii_after_left.begin(), m_ii_after_left.end(), 0)) /
                    m_ii_after_left.size()
                    : std::numeric_limits<double>::infinity();
                double avm_rights = m_ii_after_right.size()
                    ? static_cast<double>(std::accumulate(
                                              m_ii_after_right.begin(),
                                              m_ii_after_right.end(), 0)) /
                    m_ii_after_right.size()
                    : std::numeric_limits<double>::infinity();
                return std::min(avm_lefts, avm_rights);
            }
        };

        void undo_add_term_method(const lar_term* t) {
            TRACE("d_undo", tout << "t:" << t << ", t->j():" << t->j() << std::endl;);
            TRACE("dioph_eq", lra.print_term(*t, tout); tout << ", t->j() =" << t->j() << std::endl;);
            if (!contains(m_active_terms, t)) {
                for (int i = static_cast<int>(m_added_terms.size() - 1); i >= 0; --i) {
                    if (m_added_terms[i] != t) continue;
                    if ((unsigned)i != m_added_terms.size() - 1)
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
            TRACE("dioph_eq", tout << "the deleted term column in m_l_matrix" << std::endl; for (auto p : m_l_matrix.column(t->j())) { tout << "p.coeff():" << p.coeff() << ", row " << p.var() << std::endl; } tout << "m_l_matrix has " << m_l_matrix.column_count() << " columns" << std::endl; tout << "and " << m_l_matrix.row_count() << " rows" << std::endl; print_lar_term_L(*t, tout); tout << "; t->j()=" << t->j() << std::endl;);
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
            std::queue<unsigned> m_q;
            indexed_uint_set m_in_q;
            bool empty() const {
                return m_q.empty();
            }

            unsigned size() const {
                return (unsigned)m_q.size();
            }

            void push(unsigned j) {
                if (m_in_q.contains(j)) return;
                m_in_q.insert(j);
                m_q.push(j);
            }

            unsigned pop_front() {
                unsigned j = m_q.front();
                m_q.pop();
                SASSERT(m_in_q.contains(j));
                m_in_q.remove(j);
                return j;
            }
        };

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
            mpq alpha;
            for (const auto& p : last_e_row) {
                if (p.var() == j) {
                    return;
                }
            }
            SASSERT(m_l_matrix.m_columns.back().size());
            unsigned i = m_l_matrix.m_columns[j][0].var();
            m_l_matrix.add_rows(mpq(1), i, m_l_matrix.row_count() - 1);
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

            if (m_k2s.has_val(i)) {
                remove_from_S(i);
            }

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
            TRACE("dioph_eq", lra.print_column_info(j, tout););
            m_changed_columns.insert(j);
        }
        std_vector<const lar_term*> m_added_terms;
        std::unordered_set<const lar_term*> m_active_terms;
        std_vector<variable_branch_stats> m_branch_stats;
        std_vector<branch> m_branch_stack;
        std_vector<constraint_index> m_explanation_of_branches;
        void add_term_callback(const lar_term* t) {
            unsigned j = t->j();
            TRACE("dioph_eq", tout << "term column t->j():" << j << std::endl; lra.print_term(*t, tout) << std::endl;);
            if (!lra.column_is_int(j)) {
                TRACE("dioph_eq", tout << "ignored a non-integral column" << std::endl;);
                return;
            }

            CTRACE("dioph_eq", !lra.column_has_term(j), tout << "added term that is not associated with a column yet" << std::endl;);

            if (!all_vars_are_int(*t)) {
                TRACE("dioph_eq", tout << "not all vars are integrall\n";);
                return;
            }
            m_added_terms.push_back(t);
            m_changed_terms.insert(t->j());
            auto undo = undo_add_term(*this, t);
            lra.trail().push(undo);
        }

        void update_column_bound_callback(unsigned j) {
            if (!lra.column_is_int(j) || !lra.column_is_fixed(j))
                return;
            m_changed_columns.insert(j);
            auto undo = undo_fixed_column(*this, j);
            lra.trail().push(undo);
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
            TRACE("dioph_eq", tout << "register term:"; lra.print_term(t, tout); tout << ", t.j()=" << t.j() << std::endl;);
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
            TRACE("dioph_eq", print_lar_term_L(t, tout) << std::endl;);
            unsigned entry_index = (unsigned)m_e_matrix.row_count();
            m_sum_of_fixed.push_back(mpq(0));
            mpq& e = m_sum_of_fixed.back();
            SASSERT(m_l_matrix.row_count() == m_e_matrix.row_count());
            // fill m_l_matrix row
            m_l_matrix.add_row();
            // todo: consider to compress variables t.j() by using a devoted var_register for term columns
            m_l_matrix.add_columns_up_to(t.j());
            m_l_matrix.add_new_element(entry_index, t.j(), mpq(1));
            // fill E-entry
            m_e_matrix.add_row();

            SASSERT(m_e_matrix.row_count() == m_e_matrix.row_count());

            for (const auto& p : t.ext_coeffs()) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.var()))
                    e += p.coeff() * lia.lower_bound(p.var()).x;
                else {
                    unsigned lj = add_var(p.var());
                    m_e_matrix.add_columns_up_to(lj);
                    m_e_matrix.add_new_element(entry_index, lj, p.coeff());
                }
            }
            TRACE("dioph_eq", print_entry(entry_index, tout) << std::endl;);
            subs_entry(entry_index);
            SASSERT(entry_invariant(entry_index));
        }
        void subs_entry(unsigned ei) {
            if (ei >= m_e_matrix.row_count()) return;
            // q is the queue of variables that can be substituted in ei
            protected_queue q;
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                if (can_substitute(p.var()))
                    q.push(p.var());
            }
            if (q.size() == 0) return;
            substitute_on_q(q, ei);
            SASSERT(entry_invariant(ei));
        }

        void substitute_on_q_with_entry_in_S(protected_queue& q, unsigned ei, unsigned j, const mpq& alpha) {
            unsigned ei_to_sub = m_k2s[j];
            int sign_j = get_sign_in_e_row(ei_to_sub, j);
            // we need to eliminate alpha*j in ei's row
            add_two_entries(-mpq(sign_j) * alpha, ei_to_sub, ei);
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                unsigned jj = p.var();
                if (can_substitute(jj))
                    q.push(jj);
            }
        }
        void substitute_with_fresh_def(protected_queue& q, unsigned ei, unsigned j, const mpq& alpha) {
            const lar_term& sub_term = m_fresh_k2xt_terms.get_by_key(j).first;
            TRACE("dioph_eq", print_lar_term_L(sub_term, tout) << std::endl;);
            SASSERT(sub_term.get_coeff(j).is_one());
            // we need to eliminate alpha*j in ei's row
            add_term_to_entry(-alpha, sub_term, ei);
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                unsigned jj = p.var();
                if (can_substitute(jj))
                    q.push(jj);
            }
        }

        // q is the queue of variables that can be substituted in ei
        void substitute_on_q(protected_queue& q, unsigned ei) {
            while (!q.empty()) {
                unsigned j = q.pop_front();
                mpq alpha = get_coeff_in_e_row(ei, j);
                if (alpha.is_zero()) continue;
                if (m_k2s.has_key(j)) {
                    substitute_on_q_with_entry_in_S(q, ei, j, alpha);
                }
                else {
                    substitute_with_fresh_def(q, ei, j, alpha);
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

        bool all_vars_are_int(const lar_term& term) const {
            for (const auto& p : term) {
                if (!lia.column_is_int(p.var()))
                    return false;
            }
            return lia.column_is_int(term.j());
        }

        void clear_e_row(unsigned ei) {
            auto& row = m_e_matrix.m_rows[ei];
            while (row.size() > 0) {
                auto& c = row.back();
                m_e_matrix.remove_element(row, c);
            }
        }

        void recalculate_entry(unsigned ei) {
            TRACE("dioph_eq", print_entry(ei, tout) << std::endl;);
            mpq& c = m_sum_of_fixed[ei];
            c = mpq(0);
            open_l_term_to_work_vector(ei, c);
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
                c *= denom;
                m_l_matrix.multiply_row(ei, denom);
                m_e_matrix.multiply_row(ei, denom);
            }
            if (belongs_to_s(ei)) {
                remove_from_S(ei);
            }
            SASSERT(entry_invariant(ei));
        }

        void find_changed_terms_and_more_changed_rows() {
            for (unsigned j : m_changed_columns) {
                const auto it = m_columns_to_terms.find(j);
                if (it != m_columns_to_terms.end())
                    for (unsigned k : it->second) {
                        m_changed_terms.insert(k);
                    }
                if (!m_var_register.external_is_used(j))
                    continue;
                for (const auto& p : m_e_matrix.column(this->lar_solver_to_local(j))) {
                    m_changed_rows.insert(p.var());  // TODO: is it necessary?
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
            for (const auto& p : m_fresh_k2xt_terms.m_bij.m_rev_map) {
                unsigned xt = p.first;
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

        void process_changed_columns() {
            find_changed_terms_and_more_changed_rows();
            for (unsigned j : m_changed_terms) {
                if (j >= m_l_matrix.column_count()) continue;
                for (const auto& cs : m_l_matrix.column(j)) {
                    m_changed_rows.insert(cs.var());
                }
            }

            // find more entries to recalculate
            std_vector<unsigned> more_changed_rows;
            for (unsigned ei : m_changed_rows) {
                auto it = m_row2fresh_defs.find(ei);
                if (it == m_row2fresh_defs.end()) continue;
                for (unsigned xt : it->second) {
                    SASSERT(var_is_fresh(xt));
                    for (const auto& p : m_e_matrix.m_columns[xt]) {
                        more_changed_rows.push_back(p.var());
                    }
                }
            }

            for (unsigned ei : more_changed_rows) {
                m_changed_rows.insert(ei);
            }

            for (unsigned ei : m_changed_rows) {
                if (ei >= m_e_matrix.row_count())
                    continue;
                recalculate_entry(ei);
                if (m_e_matrix.m_columns.back().size() == 0) {
                    m_e_matrix.m_columns.pop_back();
                    m_var_register.shrink(m_e_matrix.column_count());
                }
                if (m_l_matrix.m_columns.back().size() == 0) {
                    m_l_matrix.m_columns.pop_back();
                }
            }

            remove_irrelevant_fresh_defs();

            eliminate_substituted_in_changed_rows();
            m_changed_columns.reset();
            SASSERT(m_changed_columns.size() == 0);
            m_changed_rows.reset();
            SASSERT(entries_are_ok());
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

        void transpose_entries(unsigned i, unsigned k) {
            SASSERT(i != k);
            m_l_matrix.transpose_rows(i, k);
            m_e_matrix.transpose_rows(i, k);
            std::swap(m_sum_of_fixed[i], m_sum_of_fixed[k]);
            m_k2s.transpose_val(i, k);

            NOT_IMPLEMENTED_YET();
            /*
            // transpose fresh definitions
            for (auto & fd: m_fresh_definitions) {
            if (fd.m_ei == i)
            fd.m_ei = k;
            else if (fd.m_ei == k)
            fd.m_ei = i;

            if (fd.m_origin == i)
            fd.m_origin = k;

            }*/
        }

        // returns true if a variable j is substituted
        bool can_substitute(unsigned j) const {
            return m_k2s.has_key(j) || m_fresh_k2xt_terms.has_key(j);
        }

        bool entries_are_ok() {
            for (unsigned ei = 0; ei < m_e_matrix.row_count(); ei++) {
                if (entry_invariant(ei) == false) {
                    TRACE("dioph_deb_eq", tout << "bad entry:"; print_entry(ei, tout););
                    return false;
                }
                if (belongs_to_f(ei)) {
                    // see that all vars are substituted
                    const auto& row = m_e_matrix.m_rows[ei];
                    for (const auto& p : row) {
                        if (m_k2s.has_key(p.var())) {
                            /*
                              std::cout << "entry:" << ei << " belongs to f but depends on column " << p.var() << std::endl;
                              std::cout << "m_var_register.local_to_external(p.var()):" << m_var_register.local_to_external(p.var()) << std::endl;
                              print_entry(ei, std::cout);
                              std::cout << "column " << p.var() << " of m_e_matrix:";
                              for (const auto & c : m_e_matrix.m_columns[p.var()]) {
                              std::cout << "row:" << c.var() << ", ";
                              }

                              std::cout << std::endl;
                              std::cout << "column " << p.var() << " is subst by entry:";
                              print_entry(m_k2s[p.var()],std::cout)  << std::endl;
                            */
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        void init() {
            m_report_branch = false;
            m_conflict_index = -1;
            m_infeas_explanation.clear();
            lia.get_term().clear();
            m_number_of_branching_calls = 0;
            m_branch_stack.clear();
            m_lra_level = 0;

            process_changed_columns();
            for (const lar_term* t : m_added_terms) {
                m_active_terms.insert(t);
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

        std::ostream& print_deps(std::ostream& out, u_dependency* dep) {
            explanation ex(lra.flatten(dep));
            return lra.print_expl(out, ex);
        }

        bool has_fresh_var(unsigned row_index) const {
            for (const auto& p : m_e_matrix.m_rows[row_index]) {
                if (var_is_fresh(p.var()))
                    return true;
            }
            return false;
        }

        // A conflict is reported when the gcd of the monomial coefficients does not divide the free coefficent.
        // If there is no conflict the entry is divided, normalized, by gcd.
        // The function returns true if and only if there is no conflict. In the case of a conflict a branch
        // can be returned as well.
        bool normalize_e_by_gcd(unsigned ei, mpq& g) {
            mpq& e = m_sum_of_fixed[ei];
            TRACE("dioph_eq", print_entry(ei, tout) << std::endl;);
            g = gcd_of_coeffs(m_e_matrix.m_rows[ei], false);
            if (g.is_zero() || g.is_one()) {
                SASSERT(g.is_one() || e.is_zero());
                return true;
            }
            TRACE("dioph_eq", tout << "g:" << g << std::endl;);
            mpq c_g = e / g;
            if (c_g.is_int()) {
                for (auto& p : m_e_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }
                m_sum_of_fixed[ei] = c_g;
                // e.m_l *= (1 / g);
                for (auto& p : m_l_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }

                TRACE("dioph_eq", tout << "ep_m_e:";
                      print_entry(ei, tout) << std::endl;);
                SASSERT(entry_invariant(ei));
                return true;
            }
            // c_g is not integral
            return false;
        }

        void init_term_from_constraint(term_o& t, const lar_base_constraint& c) {
            for (const auto& p : c.coeffs()) {
                t.add_monomial(p.first, p.second);
            }
            t.c() = -c.rhs();
        }

        void subs_qfront_by_fresh(unsigned k, protected_queue& q) {
            const lar_term& e = m_fresh_k2xt_terms.get_by_key(k).first;
            TRACE("dioph_eq", tout << "k:" << k << ", in ";
                  print_term_o(create_term_from_subst_space(), tout) << std::endl;
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
            TRACE("dioph_eq", tout << "after subs k:" << k << "\n";
                  print_term_o(create_term_from_subst_space(), tout) << std::endl;
                  tout << "m_term_with_index:{"; print_lar_term_L(m_lspace.m_data, tout);
                  tout << "}, opened:"; print_ml(m_lspace.to_term(), tout) << std::endl;);
        }

        void add_l_row_to_term_with_index(const mpq& coeff, unsigned ei) {
            for (const auto& p : m_l_matrix.m_rows[ei]) {
                m_lspace.add(coeff * p.coeff(), p.var());
            }
        }

        void subs_qfront_by_S(unsigned k, protected_queue& q) {
            const mpq& e = m_sum_of_fixed[m_k2s[k]];
            TRACE("dioph_eq", tout << "k:" << k << ", in ";
                  print_term_o(create_term_from_subst_space(), tout) << std::endl;
                  tout << "subs with e:";
                  print_entry(m_k2s[k], tout) << std::endl;);
            mpq coeff = m_espace[k];  // need to copy since it will be zeroed
            m_espace.erase(k);        // m_espace[k] = 0;

            const auto& e_row = m_e_matrix.m_rows[m_k2s[k]];
            auto it = std::find_if(e_row.begin(), e_row.end(),
                                   [k](const auto& c) {
                                       return c.var() == k;
                                   });
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
            TRACE("dioph_eq", tout << "after subs k:" << k << "\n";
                  print_term_o(create_term_from_subst_space(), tout) << std::endl;
                  tout << "m_term_with_index:{"; print_lar_term_L(m_lspace.to_term(), tout);
                  tout << "}, opened:"; print_ml(m_lspace.to_term(), tout) << std::endl;);
        }

        bool is_substituted_by_fresh(unsigned k) const {
            return m_fresh_k2xt_terms.has_key(k);
        }
        // The term giving the substitution is in form (+-)x_k + sum {a_i*x_i} + c = 0.
        // We substitute x_k in t by (+-)coeff*(sum {a_i*x_i} + c), where coeff is
        // the coefficient of x_k in t.
        void subs_front_with_S_and_fresh(protected_queue& q) {
            unsigned k = q.pop_front();
            if (!m_espace.has(k))
                return;
            // we might substitute with a term from S or a fresh term

            SASSERT(can_substitute(k));
            if (is_substituted_by_fresh(k)) {
                subs_qfront_by_fresh(k, q);
            }
            else {
                subs_qfront_by_S(k, q);
            }
        }

        lar_term l_term_from_row(unsigned k) const {
            lar_term ret;
            for (const auto& p : m_l_matrix.m_rows[k])
                ret.add_monomial(p.coeff(), p.var());

            return ret;
        }

        term_o create_term_from_l(const lar_term& l) {
            term_o ret;
            for (const auto& p : l) {
                const auto& t = lra.get_term(local_to_lar_solver(p.j()));
                ret.add_monomial(-mpq(1), p.j());
                for (const auto& q : t) {
                    ret.add_monomial(p.coeff() * q.coeff(), q.j());
                }
            }
            return ret;
        }

        bool is_fixed(unsigned j) const {
            return lra.column_is_fixed(j);
        }

        template <typename T>
        term_o fix_vars(const T& t) const {
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

        const unsigned sub_index(unsigned k) const {
            return m_k2s[k];
        }

        template <typename T>
        T pop_front_of_queue(std::queue<T>& q) const {
            T value = q.front();
            q.pop();
            return value;
        }

        void subs_with_S_and_fresh(protected_queue& q) {
            while (!q.empty())
                subs_front_with_S_and_fresh(q);
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
            std_vector<unsigned> cleanup;
            m_tightened_columns.reset();
            for (unsigned j : m_changed_terms) {
                if ( 
                    j >= lra.column_count() ||
                    !lra.column_has_term(j) ||
                    lra.column_is_free(j) ||
                    is_fixed(j) || !lia.column_is_int(j)) {
                    cleanup.push_back(j);
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
                  print_bounds(tout);
            );
            for (unsigned j : sorted_changed_terms) {
                m_changed_terms.remove(j); 
                
                r = tighten_bounds_for_term_column(j);
                if (r != lia_move::undef) {
                    break;
                }                
            }
            for (unsigned j : cleanup) {
                m_changed_terms.remove(j);
            }
            return r;
        }

        #if 0
        std::ostream& print_queue(std::queue<unsigned> q, std::ostream& out) {
            out << "qu: ";
            while (!q.empty()) {
                out << q.front() << " ";
                q.pop();
            }
            out << std::endl;
            return out;
        }
        #endif

        term_o create_term_from_subst_space() {
            term_o t;
            for (const auto& p : m_espace.m_data) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_c;
            return t;
        }

        void init_substitutions(const lar_term& lar_t, protected_queue& q) {
            m_espace.clear();
            m_c = mpq(0);
            m_lspace.clear();
            SASSERT(get_extended_term_value(lar_t).is_zero());
            TRACE("dioph_eq", tout << "t:";print_lar_term_L(lar_t, tout) << std::endl; tout << "value:" << get_extended_term_value(lar_t) << std::endl;);
            for (const auto& p : lar_t) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.j())) {
                    m_c += p.coeff() * lia.lower_bound(p.j()).x;
                    SASSERT(lia.lower_bound(p.j()).x == lra.get_column_value(p.j()).x); 
                }
                else {
                    unsigned lj = lar_solver_to_local(p.j());
                    m_espace.add(p.coeff(), lj);;
                    if (!lra.column_is_fixed(p.j()) && can_substitute(lj))
                        q.push(lar_solver_to_local(p.j()));
                }
            }
            TRACE("dioph_eq", tout << "m_espace:"; print_term_o(create_term_from_subst_space(), tout) << std::endl;
                  tout << "m_c:" << m_c << std::endl;
                  tout << "get_value_of_subs_space:" << get_value_of_espace() << std::endl;);
        }
        unsigned lar_solver_to_local(unsigned j) const {
            return m_var_register.external_to_local(j);
        }

        // j is the index of the column representing a term
        // return true if a conflict was found
        lia_move tighten_bounds_for_term_column(unsigned j) {
            term_o term_to_tighten = lra.get_term(j);  // copy the term aside
            
            SASSERT(get_extended_term_value(term_to_tighten).is_zero());
            if (!all_vars_are_int(term_to_tighten))
                return lia_move::undef;
            // q is the queue of variables that can be substituted in term_to_tighten
            protected_queue q;
            TRACE("dioph_eq", tout << "j:" << j << ", t: "; print_lar_term_L(term_to_tighten, tout) << std::endl;);
            init_substitutions(term_to_tighten, q);
            if (q.empty()) 
                return lia_move::undef;
         
            TRACE("dioph_eq", tout << "t:"; print_lar_term_L(term_to_tighten, tout) << std::endl;
                  tout << "subs_space:"; print_term_o(create_term_from_subst_space(), tout) << std::endl;
                  tout << "m_lspace:";
                  print_lar_term_L(m_lspace.to_term(), tout) << std::endl;);
            subs_with_S_and_fresh(q);
            TRACE("dioph_eq", tout << "after subs\n"; print_term_o(create_term_from_subst_space(), tout) << std::endl; tout << "m_l_term_space:"; print_lar_term_L(m_lspace.to_term(), tout) << std::endl; tout << "open_ml:"; print_lar_term_L(open_ml(m_lspace.to_term()), tout) << std::endl; tout << "term_to_tighten + open_ml:"; print_term_o(term_to_tighten + open_ml(m_lspace.to_term()), tout) << std::endl; term_o ls = fix_vars(term_to_tighten + open_ml(m_lspace.to_term())); tout << "ls:"; print_term_o(ls, tout) << std::endl; term_o rs = term_to_lar_solver(remove_fresh_vars(create_term_from_subst_space())); tout << "rs:"; print_term_o(rs, tout) << std::endl; term_o diff = ls - rs; if (!diff.is_empty()) {
                    tout << "diff:"; print_term_o(diff, tout ) << std::endl; });

            SASSERT(
                fix_vars(term_to_tighten + open_ml(m_lspace.to_term())) ==
                term_to_lar_solver(remove_fresh_vars(create_term_from_subst_space())));
            mpq g = gcd_of_coeffs(m_espace.m_data, true);
            TRACE("dioph_eq", tout << "after process_q_with_S\nt:";  print_term_o(create_term_from_subst_space(), tout) << std::endl; tout << "g:" << g << std::endl;);

            if (g.is_one())
                return lia_move::undef;
            if (g.is_zero()) {
                handle_constant_term(j);
                if (!m_infeas_explanation.empty()) {
                    return lia_move::conflict;
                }
                return lia_move::undef;
            }
            if (create_branch_report(j, g)) {
                lra.settings().stats().m_dio_branch_from_proofs++;
                return lia_move::branch;
            }
            // g is not trivial, trying to tighten the bounds
            if (tighten_bounds_for_non_trivial_gcd(g, j, true) != lia_move::undef) {
                return lia_move::conflict;
            }
            if (tighten_bounds_for_non_trivial_gcd(g, j, false) != lia_move::undef) {
                return lia_move::conflict;
            }
            return lia_move::undef;
        }

        bool should_report_branch() const {
            return (lra.settings().stats().m_dio_calls% lra.settings().dio_report_branch_with_term_tigthening_period()) == 0;
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
        impq get_term_value(const lar_term& t) const {
            impq ret;
            for (const auto& p : t) {
                ret += p.coeff() * lra.get_column_value(p.j());
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

        bool create_branch_report(unsigned j, const mpq& g) {
            if (!should_report_branch()) return false;
            if (!lia.at_bound(j)) return false;
            
            mpq rs = (lra.get_column_value(j).x - m_c) / g;
            if (rs.is_int()) return false;
            m_report_branch = true;
            remove_fresh_from_espace();
            SASSERT(get_value_of_espace() + m_c == lra.get_column_value(j).x && lra.get_column_value(j).x.is_int());
            
            lar_term& t = lia.get_term();
            t.clear();
            for (const auto& p : m_espace.m_data) {
                t.add_monomial(p.coeff() / g, local_to_lar_solver(p.var()));
            }
            lia.offset() = floor(rs);
            lia.is_upper() = true;
            m_report_branch = true;
            enable_trace("dioph_eq");
            TRACE("dioph_eq", tout << "prepare branch, t:";
                  print_lar_term_L(t, tout)
                  << " <= " << lia.offset()
                  << std::endl;
                  tout << "current value of t:" << get_term_value(t) << std::endl;
                );
            
            SASSERT(get_value_of_espace() / g > lia.offset() );
            return true;
        }
        void get_expl_from_meta_term(const lar_term& t, explanation& ex) {
            u_dependency* dep = explain_fixed_in_meta_term(t);
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
                        lra.join_deps(explain_fixed(lra.get_term(j)),
                                      explain_fixed_in_meta_term(m_lspace.m_data));
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
                        lra.join_deps(explain_fixed(lra.get_term(j)),
                                      explain_fixed_in_meta_term(m_lspace.m_data));
                    dep = lra.join_deps(
                        dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                }
            }
        }

        lia_move propagate_bounds_on_tightened_columns() {
            return lia_move::undef;
        }
        // m_espace contains the coefficients of the term
        // m_c contains the fixed part of the term
        // m_tmp_l is the linear combination of the equations that removes the
        // substituted variables.
        // returns true iff the conflict is found
        lia_move tighten_bounds_for_non_trivial_gcd(const mpq& g, unsigned j,
                                                bool is_upper) {
            mpq rs;
            bool is_strict;
            u_dependency* b_dep = nullptr;
            SASSERT(!g.is_zero());

            if (lra.has_bound_of_type(j, b_dep, rs, is_strict, is_upper)) {
                TRACE("dioph_eq", tout << "current upper bound for x" << j << ":"
                      << rs << std::endl;);
                rs = (rs - m_c) / g;
                TRACE("dioph_eq", tout << "(rs - m_c) / g:" << rs << std::endl;);
                if (!rs.is_int()) {
                    if (tighten_bound_kind(g, j, rs, is_upper, b_dep))
                        return lia_move::conflict;
                }
            }
            return lia_move::undef;
        }

        // returns true only on a conflict
        bool tighten_bound_kind(const mpq& g, unsigned j, const mpq& ub, bool upper,
                                u_dependency* prev_dep) {
            // ub = (upper_bound(j) - m_c)/g.
            // we have xj = t = g*t_+ m_c <= upper_bound(j), then
            // t_ <= floor((upper_bound(j) - m_c)/g) = floor(ub)
            //
            // so xj = g*t_+m_c <= g*floor(ub) + m_c is new upper bound
            // <= can be replaced with >= for lower bounds, with ceil instead of
            // floor
            mpq bound = g * (upper ? floor(ub) : ceil(ub)) + m_c;
            TRACE("dioph_eq", tout << "is upper:" << upper << std::endl;
                  tout << "new " << (upper ? "upper" : "lower")
                  << " bound:" << bound << std::endl;);

            SASSERT((upper && bound < lra.get_upper_bound(j).x) ||
                    (!upper && bound > lra.get_lower_bound(j).x));
            lconstraint_kind kind =
                upper ? lconstraint_kind::LE : lconstraint_kind::GE;
            u_dependency* dep = prev_dep;
            dep = lra.join_deps(dep, explain_fixed_in_meta_term(m_lspace.m_data));
            u_dependency* j_bound_dep = upper
                ? lra.get_column_upper_bound_witness(j)
                : lra.get_column_lower_bound_witness(j);
            dep = lra.join_deps(dep, j_bound_dep);
            dep = lra.join_deps(dep, explain_fixed(lra.get_term(j)));
            dep =
                lra.join_deps(dep, lra.get_bound_constraint_witnesses_for_column(j));
            TRACE("dioph_eq", tout << "jterm:";
                  print_lar_term_L(lra.get_term(j), tout) << "\ndep:";
                  print_deps(tout, dep) << std::endl;);
            lra.update_column_type_and_bound(j, kind, bound, dep);
            lp_status st = lra.find_feasible_solution();
            if ((int)st >= (int)lp::lp_status::FEASIBLE) {
                m_tightened_columns.insert(j);
                return false;
            }
            if (st == lp_status::CANCELLED) return false;
            lra.get_infeasibility_explanation(m_infeas_explanation);
            return true;
        }

        template <typename T>
        u_dependency* explain_fixed_in_meta_term(const T& t) {
            return explain_fixed(open_ml(t));
        }

        u_dependency* explain_fixed(const lar_term& t) {
            u_dependency* dep = nullptr;
            for (const auto& p : t) {
                if (is_fixed(p.j())) {
                    u_dependency* bound_dep =
                        lra.get_bound_constraint_witnesses_for_column(p.j());
                    dep = lra.join_deps(dep, bound_dep);
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
                        m_conflict_index = ei;
                        return;
                    }
                }
                f_vector.push_back(ei);
            }
        }
        
        lia_move process_f() {
            std_vector<unsigned> f_vector;
            fill_f_vector(f_vector);
            if (m_conflict_index != UINT_MAX) {
                lra.stats().m_dio_rewrite_conflicts++;
                return lia_move::conflict;
            }
            
            while (rewrite_eqs(f_vector)) {}
            
            if (m_conflict_index != UINT_MAX) {
                lra.stats().m_dio_rewrite_conflicts++;
                return lia_move::conflict;
            }
            return lia_move::undef;
        }

        lia_move process_f_and_tighten_terms() {
            lia_move ret = process_f();
            if (ret != lia_move::undef)
                return ret;
            TRACE("dioph_eq", print_S(tout););
            ret = tighten_terms_with_S();
            if (ret == lia_move::conflict) {
                lra.stats().m_dio_tighten_conflicts++;
                return lia_move::conflict;
            }
            return ret;
        }

        void collect_evidence() {
            lra.get_infeasibility_explanation(m_infeas_explanation);
            for (const auto& p : m_infeas_explanation) {
                m_explanation_of_branches.push_back(p.ci());
            }
        }

        // returns true if the left and the right branches were explored
        void undo_explored_branches() {
            TRACE("dio_br", tout << "m_branch_stack.size():" << m_branch_stack.size() << std::endl;);
            while (m_branch_stack.size() && m_branch_stack.back().m_fully_explored) {
                m_branch_stack.pop_back();
                lra_pop();
            }
            TRACE("dio_br", tout << "after pop:m_branch_stack.size():" << m_branch_stack.size() << std::endl;);
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
                    for (auto ci : lra.flatten(explain_fixed_in_meta_term(m_l_matrix.m_rows[m_k2s[j]]))) {
                        m_explanation_of_branches.push_back(ci);
                    }
                    return lia_move::conflict;
                }
            }
            return lia_move::undef;
        }

        void undo_branching() {
            while (m_lra_level--) {
                lra.pop();
            }
            lra.find_feasible_solution();
            SASSERT(lra.get_status() == lp_status::CANCELLED || lra.is_feasible());
        }
        // Returns true if a branch is created, and false if not.
        // The latter case can happen if we have a sat.
        bool push_branch() {
            branch br = create_branch();
            if (br.m_j == UINT_MAX)
                return false;
            m_branch_stack.push_back(br);
            lra.stats().m_dio_branching_depth = std::max(lra.stats().m_dio_branching_depth, (unsigned)m_branch_stack.size());
            return true;
        }

        lia_move add_var_bound_for_branch(const branch& b) {
            if (b.m_left) {
                lra.add_var_bound(b.m_j, lconstraint_kind::LE, b.m_rs);
            }
            else {
                lra.add_var_bound(b.m_j, lconstraint_kind::GE, b.m_rs + mpq(1));
            }
            TRACE("dio_br", lra.print_column_info(b.m_j, tout) << "add bound" << std::endl;);
            if (lra.column_is_fixed(b.m_j)) {
                unsigned local_bj;
                if (!m_var_register.external_is_used(b.m_j, local_bj))
                    return lia_move::undef;

                if (fix_var(local_bj) == lia_move::conflict) {
                    TRACE("dio_br", tout << "conflict in fix_var" << std::endl;);
                    return lia_move::conflict;
                }
            }
            return lia_move::undef;
        }

        unsigned m_lra_level = 0;
        void lra_push() {
            m_lra_level++;
            lra.push();
            SASSERT(m_lra_level == m_branch_stack.size());
        }
        void lra_pop() {
            m_lra_level--;
            SASSERT(m_lra_level != UINT_MAX);
            lra.pop();
            lra.find_feasible_solution();
            SASSERT(lra.get_status() == lp_status::CANCELLED || lra.is_feasible());
        }

        void transfer_explanations_from_closed_branches() {
            m_infeas_explanation.clear();
            for (auto ci : m_explanation_of_branches) {
                if (this->lra.constraints().valid_index(ci))
                    m_infeas_explanation.push_back(ci);
            }
        }

        lia_move branching_on_undef() {
            m_explanation_of_branches.clear();
            bool need_create_branch = true;
            m_number_of_branching_calls = 0;
            while (++m_number_of_branching_calls < m_max_of_branching_iterations) {
                lra.stats().m_dio_branch_iterations++;
                if (need_create_branch) {
                    if (!push_branch()) {
                        undo_branching();
                        lra.stats().m_dio_branching_sats++;
                        return lia_move::sat;
                    }
                    need_create_branch = false;
                }
                lra_push();  // exploring a new branch

                if (add_var_bound_for_branch(m_branch_stack.back()) == lia_move::conflict) {
                    undo_explored_branches();
                    if (m_branch_stack.size() == 0) {
                        lra.stats().m_dio_branching_infeasibles++;
                        transfer_explanations_from_closed_branches();
                        lra.stats().m_dio_branching_conflicts++;
                        return lia_move::conflict;
                    }
                    need_create_branch = false;
                    m_branch_stack.back().flip();
                    lra_pop();
                    continue;
                }
                auto st = lra.find_feasible_solution();
                TRACE("dio_br", tout << "st:" << lp_status_to_string(st) << std::endl;);
                if ((int)st >= (int)(lp_status::FEASIBLE)) {
                    // have a feasible solution
                    unsigned n_of_ii = get_number_of_int_inf();
                    TRACE("dio_br", tout << "n_of_ii:" << n_of_ii << "\n";);
                    if (n_of_ii == 0) {
                        undo_branching();
                        lra.stats().m_dio_branching_sats++;
                        return lia_move::sat;
                    }
                    // got to create a new branch
                    update_branch_stats(m_branch_stack.back(), n_of_ii);
                    need_create_branch = true;
                }
                else {
                    if (st == lp_status::CANCELLED) return lia_move::undef;
                    collect_evidence();
                    undo_explored_branches();
                    if (m_branch_stack.size() == 0) {
                        lra.stats().m_dio_branching_infeasibles++;
                        transfer_explanations_from_closed_branches();
                        lra.stats().m_dio_branching_conflicts++;
                        return lia_move::conflict;
                    }
                    TRACE("dio_br", tout << lp_status_to_string(lra.get_status()) << std::endl;
                          tout << "explanation:\n"; lra.print_expl(tout, m_infeas_explanation););

                    need_create_branch = false;
                    lra_pop();
                    m_branch_stack.back().flip();
                }
            }
            undo_branching();
            return lia_move::undef;
        }

        unsigned get_number_of_int_inf() const {
            return (unsigned)std::count_if(
                lra.r_basis().begin(), lra.r_basis().end(),
                [this](unsigned j) {
                    return lia.column_is_int_inf(j);
                });
        }

        double get_branch_score(unsigned j) {
            if (j >= m_branch_stats.size())
                m_branch_stats.resize(j + 1);
            return m_branch_stats[j].score();
        }

        void update_branch_stats(const branch& b, unsigned n_of_ii) {
            // Ensure the branch stats vector is large enough
            if (b.m_j >= m_branch_stats.size()) {
                m_branch_stats.resize(b.m_j + 1);
            }

            if (b.m_left) {
                m_branch_stats[b.m_j].m_ii_after_left.push_back(n_of_ii);
            }
            else {
                m_branch_stats[b.m_j].m_ii_after_right.push_back(n_of_ii);
            }
        }

        branch create_branch() {
            unsigned bj = UINT_MAX;
            double score = std::numeric_limits<double>::infinity();
            // looking for the minimal score
            unsigned n = 0;
            for (unsigned j : lra.r_basis()) {
                if (!lia.column_is_int_inf(j))
                    continue;
                double sc = get_branch_score(j);
                if (sc < score ||
                    (sc == score && lra.settings().random_next() % (++n) == 0)) {
                    score = sc;
                    bj = j;
                }
            }
            branch br;
            if (bj == UINT_MAX) {  // it the case when we cannot create a branch
                SASSERT(
                    lra.settings().get_cancel_flag() ||
                    (lra.is_feasible() && [&]() {
                        for (unsigned j = 0; j < lra.column_count(); ++j) {
                            if (lia.column_is_int_inf(j)) {
                                return false;
                            }
                        }
                        return true;
                    }()));
                return br;  // to signal that we have no ii variables
            }

            br.m_j = bj;
            br.m_left = (lra.settings().random_next() % 2 == 0);
            br.m_rs = floor(lra.get_column_value(bj).x);

            TRACE("dio_br", tout << "score:" << score << "; br.m_j:" << br.m_j << ","
                  << (br.m_left ? "left" : "right") << ", br.m_rs:" << br.m_rs << std::endl;);
            return br;
        }

        bool columns_to_terms_is_correct() const {
            std::unordered_map<unsigned, std::unordered_set<unsigned>> c2t;
            for (unsigned k = 0; k < lra.terms().size(); k++) {
                const lar_term* t = lra.terms()[k];
                if (!all_vars_are_int(*t)) continue;
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
                    TRACE("dioph_eq", tout << "column j" << j << " is not registered" << std::endl; tout << "the column belongs to the the following terms:"; for (unsigned tj : p.second) { tout << " " << tj; } tout << std::endl;);

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
                    TRACE("dioph_eq", tout << "should not be registered j " << j << std::endl;
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
                if (external_j == UINT_MAX) continue;
                if (external_j >= lra.column_count() && m_e_matrix.m_columns[j].size()) {
                    // It is OK to have an empty column in m_e_matrix.
                    return false;
                }
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
            TRACE("dioph_eq", tout << lra.stats().m_dio_calls << std::endl;);
            init();
            lia_move ret = process_f_and_tighten_terms();
            if (ret == lia_move::branch || ret == lia_move::conflict)
                return ret;
            SASSERT(ret == lia_move::undef);
            if (lra.stats().m_dio_calls % lra.settings().dio_branching_period() == 0) {
                ret = branching_on_undef();
            }
            if (ret == lia_move::sat || ret == lia_move::conflict) {
                return ret;
            }
            SASSERT(ret == lia_move::undef);
            m_max_of_branching_iterations = (unsigned)m_max_of_branching_iterations / 2;

            return lia_move::undef;
        }

    private:
        void add_operator(lar_term& t, const mpq& k, const lar_term& l) {
            for (const auto& p : l) {
                t.add_monomial(k * p.coeff(), p.j());
            }
        }

        unsigned get_markovich_number(unsigned k, unsigned h) {
            size_t col_size = m_e_matrix.m_columns[k].size(); 
            size_t row_size = m_e_matrix.m_rows[h].size();
            // Subtract 1 from sizes once and multiply
            return static_cast<unsigned>((col_size - 1) * (row_size - 1));
        }
        
        std::tuple<mpq, unsigned, int, unsigned> find_minimal_abs_coeff(unsigned ei) {
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
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


        term_o get_term_to_subst(const term_o& eh, unsigned k, int k_sign) {
            term_o t;
            for (const auto& p : eh) {
                if (p.j() == k)
                    continue;
                t.add_monomial(-k_sign * p.coeff(), p.j());
            }
            t.c() = -k_sign * eh.c();
            TRACE("dioph_eq", tout << "subst_term:";
                  print_term_o(t, tout) << std::endl;);
            return t;
        }

        std::ostream& print_e_row(unsigned i, std::ostream& out) {
            return print_term_o(get_term_from_entry(i), out);
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
            TRACE("dioph_eq", tout << "eliminate var:" << j << " by using:";
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

            unsigned cell_to_process = static_cast<unsigned>(column.size() - 1);
            while (cell_to_process > 0) {
                auto& c = column[cell_to_process];
                if (belongs_to_s(c.var())) {
                    cell_to_process--;
                    continue;
                }

                SASSERT(c.var() != ei && entry_invariant(c.var()));
                mpq coeff = m_e_matrix.get_val(c);
                unsigned i = c.var();
                TRACE("dioph_eq", tout << "before pivot entry:";
                      print_entry(i, tout) << std::endl;);
                m_sum_of_fixed[i] -= j_sign * coeff * e;
                m_e_matrix.pivot_row_to_row_given_cell_with_sign(ei, c, j, j_sign);
                // m_sum_of_fixed[i].m_l -= j_sign * coeff * e.m_l;
                m_l_matrix.add_rows(-j_sign * coeff, ei, i);
                TRACE("dioph_eq", tout << "after pivoting c_row:";
                      print_entry(i, tout););
                CTRACE(
                    "dioph_eq", !entry_invariant(i), tout << "invariant delta:"; {
                        print_term_o(get_term_from_entry(ei) -
                                     fix_vars(open_ml(m_l_matrix.m_rows[ei])),
                                     tout)
                            << std::endl;
                    });
                SASSERT(entry_invariant(i));
                cell_to_process--;
            }
            SASSERT(is_eliminated_from_f(j));
        }
        // j is the variable to eliminate, or substitude, it appears in term t with
        // a coefficient equal to j_sign which is +-1 ,
        // matrix m_l_matrix is not changed since it is a substitution of a fresh variable
        void eliminate_var_in_f_with_term(const lar_term& t, unsigned j, int j_sign) {
            SASSERT(abs(t.get_coeff(j)).is_one());
            TRACE("dioph_eq", tout << "eliminate var:" << j << " by using:";
                  print_lar_term_L(t, tout) << std::endl;);
            auto& column = m_e_matrix.m_columns[j];

            int cell_to_process = static_cast<int>(column.size() - 1);
            while (cell_to_process >= 0) {
                auto& c = column[cell_to_process];
                if (belongs_to_s(c.var())) {
                    cell_to_process--;
                    continue;
                }

                mpq coeff = m_e_matrix.get_val(c);
                TRACE("dioph_eq", tout << "before pivot entry :"; print_entry(c.var(), tout) << std::endl;);
                m_e_matrix.pivot_term_to_row_given_cell(t, c, j, j_sign);
                TRACE("dioph_eq", tout << "after pivoting c_row:";
                      print_entry(c.var(), tout););
                SASSERT(entry_invariant(c.var()));
                cell_to_process--;
            }
            SASSERT(is_eliminated_from_f(j));
        }

        bool is_eliminated_from_f(unsigned j) const {
            for (unsigned ei = 0; ei < m_e_matrix.row_count(); ei++) {
                if (!belongs_to_f(ei)) continue;
                const auto& row = m_e_matrix.m_rows[ei];
                bool eliminated_in_row = all_of(row, [j](auto & p) { return p.var() != j; });
                if (!eliminated_in_row) return false;
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
            if (belongs_to_s(ei)) {
                auto it = m_k2s.m_rev_map.find(ei);
                SASSERT(it != m_k2s.m_rev_map.end());
                unsigned j = it->second;
                get_sign_in_e_row(ei, j);
            }

            for (const auto& p : m_e_matrix.m_rows[ei]) {
                if (!p.coeff().is_int()) {
                    return false;
                }
            }

            bool ret =
                term_to_lar_solver(remove_fresh_vars(get_term_from_entry(ei))) ==
                fix_vars(open_ml(m_l_matrix.m_rows[ei]));

            CTRACE("dioph_deb_eq", !ret,
                   {
                       tout << "get_term_from_entry(" << ei << "):";
                       print_term_o(get_term_from_entry(ei), tout) << std::endl;
                       tout << "ls:";
                       print_term_o(remove_fresh_vars(get_term_from_entry(ei)), tout)
                           << std::endl;
                       tout << "e.m_l:";
                       print_lar_term_L(l_term_from_row(ei), tout) << std::endl;
                       tout << "open_ml(e.m_l):";
                       print_lar_term_L(open_ml(l_term_from_row(ei)), tout) << std::endl;
                       tout << "rs:";
                       print_term_o(fix_vars(open_ml(m_l_matrix.m_rows[ei])), tout) << std::endl;
                   });

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
                TRACE("dioph_eq", print_lar_term_L(fresh_t, tout););
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

        std::ostream& print_ml(const lar_term& ml, std::ostream& out) {
            term_o opened_ml = open_ml(ml);
            return print_lar_term_L(opened_ml, out);
        }

        template <typename T>
        term_o open_ml(const T& ml) const {
            term_o r;
            for (const auto& p : ml) {
                r += p.coeff() * (lra.get_term(p.var()) - lar_term(p.var()));
            }
            return r;
        }

        void open_l_term_to_work_vector(unsigned ei, mpq& c) {
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

        // it clears the row, and puts the term in the work vector
        void move_row_espace(unsigned ei) {
            m_espace.clear();
            auto& row = m_e_matrix.m_rows[ei];
            for (const auto& cell : row)
                m_espace.add(cell.coeff(), cell.var());
            clear_e_row(ei);
        }

        // The idea is to remove this fresh definition when the row h changes.
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
                                  bool print_dep = false, bool print_in_S = true) {
            unsigned j = m_k2s.has_val(i) ? m_k2s.get_key(i) : UINT_MAX;
            out << "entry " << i << ": ";
            if (j != UINT_MAX) 
                out << "x" << j << " ";               
            out << "{\n";
            print_term_o(get_term_from_entry(i), out << "\t") << ",\n";
            // out << "\tstatus:" << (int)e.m_entry_status;
            if (print_dep) {
                auto l_term = l_term_from_row(i);
                out << "\tm_l:{";
                print_lar_term_L(l_term, out) << "}, ";
                print_ml(l_term, out) << std::endl;
                out << "expl of fixed in m_l:{\n";
                print_deps(out, explain_fixed_in_meta_term(l_term));
                out << "}\n";
            }
            if (belongs_to_f(i)) {
                out << "in F\n";
            }
            else {
                if (local_to_lar_solver(j) == UINT_MAX) {
                    out << "FRESH\n";
                }
                else if (print_in_S) {
                    out << "in S\n";
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
        // returns true if an equlity was rewritten and false otherwise
        bool rewrite_eqs(std_vector<unsigned>& f_vector) {
            if (f_vector.size() == 0)
                return false;
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
                        m_conflict_index = ei;
                        return false;
                    }
                }

                auto [ahk, k, k_sign, markovich_number] = find_minimal_abs_coeff(ei);
                mpq gcd;
                if (!normalize_e_by_gcd(ei, gcd)) {
                    m_conflict_index = ei;
                    return false;
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
            if (h == UINT_MAX) return false;
            SASSERT(h == f_vector[ih]);
            if (min_ahk.is_one()) {
                TRACE("dioph_eq", tout << "push to S:\n"; print_entry(h, tout););
                move_entry_from_f_to_s(kh, h);
                eliminate_var_in_f(h, kh, kh_sign);
                if (ih != f_vector.size() - 1) {
                    f_vector[ih] = f_vector.back();
                }
                f_vector.pop_back();
            }
            else                     
                fresh_var_step(h, kh, min_ahk * mpq(kh_sign));
            return true;
        }

    public:
        void explain(explanation& ex) {
            if (m_conflict_index == UINT_MAX) {
                for (auto ci : m_infeas_explanation) {
                    ex.push_back(ci.ci());
                }
                TRACE("dioph_eq", lra.print_expl(tout, ex););
                return;
            }
            SASSERT(ex.empty());
            TRACE("dioph_eq", tout << "conflict:";
                  print_entry(m_conflict_index, tout, true) << std::endl;);
            for (auto ci : lra.flatten(explain_fixed_in_meta_term(m_l_matrix.m_rows[m_conflict_index]))) {
                ex.push_back(ci);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }

        bool var_is_fresh(unsigned j) const {
            bool ret = m_fresh_k2xt_terms.has_second_key(j);
            SASSERT(!ret || m_var_register.local_to_external(j) == UINT_MAX);
            return ret;
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

}  // namespace lp
