#include "math/lp/dioph_eq.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include <list>
#include <queue>
namespace lp {
    // This class represents a term with an added constant number c, in form sum {x_i*a_i} + c.
    class dioph_eq::imp {
        class term_o:public lar_term {
            mpq m_c;
        public:
            term_o clone() const {
                term_o ret;
                for (const auto & p: *this) {
                    ret.add_monomial(p.coeff(), p.j());
                }
                ret.c() = c();
                ret.j() = j();
                return ret;
            }
            term_o(const lar_term& t):lar_term(t), m_c(0) {
                SASSERT(m_c.is_zero());                
            }
            const mpq& c() const { return m_c; }
            mpq& c() { return m_c; }
            term_o():m_c(0) {}
            void substitute_var_with_term(const term_o& t, unsigned col_to_subs) {
                mpq a = get_coeff(col_to_subs);  // need to copy it becase the pointer value can be changed during the next loop
                const mpq& coeff = t.get_coeff(col_to_subs);
                SASSERT(coeff.is_one() || coeff.is_minus_one());
                if (coeff.is_one()) {
                    a = -a;
                }
                for (auto p : t) {
                    if (p.j() == col_to_subs)
                        continue;
                    this->add_monomial(a * p.coeff(), p.j());
                }
                this->c() += a * t.c();
                this->m_coeffs.erase(col_to_subs);
            }

            friend term_o operator*(const mpq& k, const term_o& term) {
                term_o r;
                for (const auto& p : term)
                    r.add_monomial(p.coeff()*k, p.j());
                r.c() = k*term.c();
                return r;
            }
            
            friend term_o operator+(const term_o& a, const term_o& b) {
                term_o r = a.clone();
                for(const auto& p : b) {
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
            friend bool operator== (const term_o & a, const term_o& b) {
                term_o t = a.clone();
                t += mpq(-1)*b;
                return t.c() == mpq(0) && t.size() == 0;
            }
#endif
            term_o& operator += (const term_o& t) {
                for (const auto & p: t) {
                    add_monomial(p.coeff(), p.j());
                }
                m_c += t.c();
                return *this;
            }

        };

        std::ostream& print_S(std::ostream & out) {
            out << "S:\n";
            for (unsigned i : m_s) {
                print_eprime_entry(i, out);
            }
            return out;
        }

        std::ostream& print_lar_term_L(const lar_term & t, std::ostream & out) const {
            return print_linear_combination_customized(t.coeffs_as_vector(), 
            [](int j)->std::string {return "x"+std::to_string(j);}, out );
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
            std::sort(sorted_term.begin(), sorted_term.end(), 
                      [](const auto& a, const auto& b) { return a.second < b.second; });

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
                if (is_fresh_var(j)) out << "~";
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


        /*
          An annotated state is a triple ⟨E′, λ, σ⟩, where E′ is a set of pairs ⟨e, ℓ⟩ in which
          e is an equation and ℓ is a linear combination of variables from L
        */
       //
        enum class entry_status {
            F,
            S,
            NO_S_NO_F
        };
        struct eprime_entry {
            unsigned m_row_index; // the index of the row in the constraint matrix that m_e corresponds to
            // originally m_l is the column defining the term  m_e was constructed from
            lar_term m_l;
            mpq m_c; // the constant of the term
            entry_status m_entry_status;
        };
        std_vector<eprime_entry> m_eprime;    
    // the terms are stored in m_A and m_c
        static_matrix<mpq, mpq> m_e_matrix;  // the rows of the matrix are the terms, without the constant part
        int_solver& lia;
        lar_solver& lra;
        explanation m_infeas_explanation;
        indexed_vector<mpq> m_indexed_work_vector;
        // the set of equations that are in S        
        bool m_report_branch = false;

        // set F
        std::list<unsigned> m_f;  // F = {λ(t):t in m_f}
        // set S
        std::list<unsigned> m_s;     // S = {λ(t): t in m_s}
        mpq m_c; // the constant of the equation
        lar_term m_tmp_l;; // the dependency of the equation
        // map to open the term e.m_l
        // suppose e.m_l = sum {coeff*k}, then subst(e.m_e) = fix_var(sum {coeff*lar.get_term(k)})
        
        std_vector<unsigned> m_k2s;
        
        unsigned            m_conflict_index = -1;  // m_eprime[m_conflict_index] gives the conflict
        public:
        imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {}
        term_o get_term_from_e_matrix(unsigned i) const {
            term_o t;
            for (const auto & p: m_e_matrix.m_rows[i]) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_eprime[i].m_c;
            return t;
        }
        // the term has form sum(a_i*x_i) - t.j() = 0,
        // i is the index of the term in the lra.m_terms
        void fill_eprime_entry(const lar_term& t) {
            TRACE("dioph_eq", print_lar_term_L(t, tout) << std::endl;);
            unsigned  i = static_cast<unsigned>(m_eprime.size());
            eprime_entry te = {i, lar_term(t.j()), mpq(0), entry_status::NO_S_NO_F};
            m_f.push_back(te.m_row_index);            
            m_eprime.push_back(te);
            eprime_entry& e = m_eprime.back();
            m_e_matrix.add_row();
            SASSERT(m_e_matrix.row_count() == m_eprime.size()); // this invariant is going to be broken

            for (const auto & p: t) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.var())) 
                    e.m_c += p.coeff()*lia.lower_bound(p.var()).x;
                else {
                    while (p.var() >= m_e_matrix.column_count())
                        m_e_matrix.add_column();
                    m_e_matrix.add_new_element(e.m_row_index, p.var(), p.coeff());
                }                
            }
            unsigned j = t.j();
            if (is_fixed(j))
                e.m_c -= lia.lower_bound(j).x;            
            else {
                while (j >= m_e_matrix.column_count())
                    m_e_matrix.add_column();
                m_e_matrix.add_new_element(e.m_row_index, j, - mpq(1));
            }                
            e.m_entry_status = entry_status::F;                        
            TRACE("dioph_eq", print_eprime_entry(e, tout););
            SASSERT(entry_invariant(e));
        }

        bool all_vars_are_int_and_small(const lar_term& term) const {
            for (const auto& p : term) {
                if (!lia.column_is_int(p.var())) 
                    return false;
                if (p.coeff().is_big())
                    return false;
            }            
            return true;
        }


        void init() {
            m_e_matrix = static_matrix<mpq, mpq>();
            m_report_branch = false;
            m_k2s.clear();
            m_conflict_index = -1;
            m_infeas_explanation.clear();
            lia.get_term().clear();
            m_eprime.clear();
            for (unsigned j = 0; j < lra.column_count(); j++) {
                if (!lra.column_is_int(j)|| !lra.column_has_term(j)) continue;
                const lar_term& t = lra.get_term(j);
                if (!all_vars_are_int_and_small(t)) {
                    TRACE("dioph_eq", tout << "not all vars are int and small\n";);
                    continue;
                }
                fill_eprime_entry(t);
            }

        }

        // look only at the fixed columns
        u_dependency * get_dep_from_row(const row_strip<mpq>& row) {
            u_dependency* dep = nullptr;
            for (const auto & p: row) {
                if (!is_fixed(p.var())) continue;
                u_dependency * bound_dep = lra.get_bound_constraint_witnesses_for_column(p.var());
                dep = lra.mk_join(dep, bound_dep);
            }
            return dep;
        }

        template <typename K> mpq gcd_of_coeffs(const K & k) {
            mpq g(0);
            for (const auto & p : k) {
                if (g.is_zero())
                    g = abs(p.coeff());
                else
                    g = gcd(g, p.coeff());
                if (g.is_one()) break;
            }
            return g;
        }

        std::ostream & print_dep(std::ostream& out, u_dependency* dep) {
            explanation ex(lra.flatten(dep));
            return lra.print_expl(out, ex);
        }

        std::string var_str(unsigned j) {
            return std::string(is_fresh_var(j)? "~":"") + std::to_string(j);
        }

        bool has_fresh_var(unsigned row_index) const {
            for (const auto & p: m_e_matrix.m_rows[row_index]) {
                if (is_fresh_var(p.var()))
                    return true;
            }
            return false;
        }

        void prepare_lia_branch_report(const eprime_entry & e, const mpq& g, const mpq new_c) {
            /* We have ep.m_e/g = 0, or sum((coff_i/g)*x_i) + new_c = 0,
               or sum((coeff_i/g)*x_i) = -new_c, where new_c is not an integer
               Then sum((coeff_i/g)*x_i) <= floor(-new_c) or sum((coeff_i/g)*x_i) >= ceil(-new_c)
            */
            lar_term& t = lia.get_term();
            for (const auto& p: m_e_matrix.m_rows[e.m_row_index]) {
                t.add_monomial(p.coeff()/g, p.var());
            }
            lia.offset() = floor(-new_c);
            lia.is_upper() = true;
            m_report_branch = true;
            TRACE("dioph_eq", tout << "prepare branch:"; print_lar_term_L(t, tout) << " <= " << lia.offset() << std::endl;);
        }
        
        // returns true if no conflict is found and false otherwise
        // this function devides all cooficients, and the free constant, of the ep.m_e by the gcd of all coefficients,  
        // it is needed by the next steps
        // the conflict can be used to report "cuts from proofs"
        bool normalize_e_by_gcd(unsigned row_index) {
            eprime_entry& e = m_eprime[row_index];
            TRACE("dioph_eq", print_eprime_entry(e, tout) << std::endl;);
            mpq g = gcd_of_coeffs(m_e_matrix.m_rows[row_index]);
            if (g.is_zero() || g.is_one()) {
                SASSERT(g.is_one() || e.m_c.is_zero());
                return true;
            }
            TRACE("dioph_eq", tout << "g:" << g << std::endl;);
            mpq c_g = e.m_c / g;
            if (c_g.is_int()) {
                for (auto& p: m_e_matrix.m_rows[row_index]) {
                    p.coeff() /= g;
                }
                m_eprime[row_index].m_c = c_g;
                e.m_l *= (1/g);
                TRACE("dioph_eq",  tout << "ep_m_e:"; print_eprime_entry(e, tout) << std::endl;);
                SASSERT(entry_invariant(e));
                return true;
            }
            // c_g is not integral
            if (lra.settings().stats().m_dio_conflicts % lra.settings().dio_cut_from_proof_period() == 0 &&
                !has_fresh_var(e.m_row_index))
                prepare_lia_branch_report(e, g, c_g);
            return false;
        }

        // returns true if no conflict is found and false otherwise
        bool normalize_by_gcd() {
            for (unsigned l: m_f) {
                if (!normalize_e_by_gcd(l)) {
                    SASSERT(entry_invariant(m_eprime[l]));
                    m_conflict_index = l;
                    return false;
                }
                SASSERT(entry_invariant(m_eprime[l]));                    
            }
            return true;
        }

        void init_term_from_constraint(term_o& t, const lar_base_constraint& c) {
            for (const auto& p: c.coeffs()) {
                t.add_monomial(p.first, p.second);
            }
            t.c() = - c.rhs();
        }

        // We look at term e.m_e: it is in form (+-)x_k + sum {a_i*x_i} + c = 0.
        // We substitute x_k in t by (+-)coeff*(sum {a_i*x_i} + c), where coeff is the coefficient of x_k in t.

        void subs_front_in_indexed_vector(std::queue<unsigned> & q) {
            unsigned k = pop_front(q);
            const eprime_entry& e = entry_for_subs(k);
            TRACE("dioph_eq", tout << "k:" << k << ", in ";  print_term_o(create_term_from_ind_c(), tout) << std::endl;
            tout << "subs with e:"; print_eprime_entry(e, tout) << std::endl;);
            mpq coeff = m_indexed_work_vector[k]; // need to copy since it will be zeroed 
            m_indexed_work_vector.erase(k);         // m_indexed_work_vector[k] = 0;   
            
            const auto& e_row = m_e_matrix.m_rows[e.m_row_index];
            auto it = std::find_if(e_row.begin(), e_row.end(), [k](const auto & c){ return c.var() == k;});
            const mpq& k_coeff_in_e = it->coeff();
            bool is_one = k_coeff_in_e.is_one();
            SASSERT(is_one || k_coeff_in_e.is_minus_one());
            if (is_one) coeff = -coeff;
            
            for (const auto& p: e_row) {
                unsigned j = p.var();
                if (j == k) continue;
                m_indexed_work_vector.add_value_at_index(j, p.coeff()*coeff); 
                // do we need to add j to the queue?
                if (!is_fresh_var(j) && !m_indexed_work_vector[j].is_zero() && can_substitute(j))
                    q.push(j);               
            }
            m_c += coeff * e.m_c;
            m_tmp_l += coeff * e.m_l;
            TRACE("dioph_eq", tout << "after subs k:"<< k<< "\n"; print_term_o(create_term_from_ind_c(), tout) << std::endl;
                    tout << "m_tmp_l:{"; print_lar_term_L(m_tmp_l, tout); tout << "}, opened:"; print_ml(m_tmp_l, tout) << std::endl;);
        }

        term_o create_term_from_l(const lar_term& l) {
            term_o ret;
            for (const auto& p: l) {
                const auto & t = lra.get_term(p.j());
                ret.add_monomial(-mpq(1), p.j());
                for (const auto& q: t) {
                    ret.add_monomial(p.coeff()*q.coeff(), q.j());
                }
            }
            return ret;
        }

        bool is_fixed(unsigned j) const {
            return (!is_fresh_var(j)) && lra.column_is_fixed(j);
        }

        template <typename T> term_o fix_vars(const T& t) const {
            term_o ret;
            for (auto& p: t) {
                if (is_fixed(p.var())) {
                    ret.c() += p.coeff() * this->lra.get_lower_bound(p.var()).x;
                } else {
                    ret.add_monomial(p.coeff(), p.var());
                }
            }
            return ret;
        }
        const eprime_entry& entry_for_subs(unsigned k) const {
            return m_eprime[m_k2s[k]];
        }

        const unsigned sub_index(unsigned k) const {
            return m_k2s[k];
        }
    
        template <typename T>  T pop_front(std::queue<T>& q) const {
           T value = q.front();
           q.pop();
           return value;
         }
    
        void subs_indexed_vector_with_S(std::queue<unsigned> &q) {
            while (!q.empty())
                subs_front_in_indexed_vector(q);            
        }

        void debug_remove_fresh_vars(term_o& t) {
            std::queue<unsigned> q;
            for (const auto& p: t) {
                if (is_fresh_var(p.j())) {
                    q.push(p.j());
                }
            }
            while (!q.empty()) {
                unsigned j = pop_front(q);
                    
            }
            
        }

        lia_move tighten_with_S() {
            int change = 0;
            for (unsigned j = 0; j < lra.column_count(); j++) {
                if (!lra.column_has_term(j) || lra.column_is_free(j) ||
                    lra.column_is_fixed(j) || !lia.column_is_int(j)) continue;
                if (tighten_bounds_for_term_column(j)) {
                    change++;
                }
                if (!m_infeas_explanation.empty()) {
                    return lia_move::conflict;
                }   
            }
            TRACE("dioph_eq", tout << "change:" << change << "\n";);
            if (!change)
                return lia_move::undef;
            
            auto st = lra.find_feasible_solution();
            if (st != lp::lp_status::FEASIBLE && st != lp::lp_status::OPTIMAL && st != lp::lp_status::CANCELLED) {
                lra.get_infeasibility_explanation(m_infeas_explanation);
                return lia_move::conflict;
            }
            return lia_move::undef;
        }

        std::ostream& print_queue(std::queue<unsigned> q, std::ostream& out) {
            out << "qu: ";
            while (!q.empty()) {
                out << q.front() << " ";
                q.pop();
            }   
            out<< std::endl;
            return out;
        }   

        term_o create_term_from_ind_c() {
            term_o t;
            for (const auto& p: m_indexed_work_vector) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_c;
            return t;
        }

        void fill_indexed_work_vector_from_term(const lar_term& lar_t) {
            m_indexed_work_vector.resize(m_e_matrix.column_count());
            m_c = 0;
            m_tmp_l = lar_term();
            for (const auto& p: lar_t) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.j())) 
                    m_c += p.coeff()*lia.lower_bound(p.j()).x;
                else
                    m_indexed_work_vector.set_value(p.coeff(), p.j());
            }
            
        }
        // j is the index of the column representing a term
        // return true if a new tighter bound was set on j
        bool tighten_bounds_for_term_column(unsigned j) {
            term_o term_to_tighten = lra.get_term(j); // copy the term aside
            std::queue<unsigned> q;
            for (const auto& p: term_to_tighten) {
                if (can_substitute(p.j())) 
                    q.push(p.j());
            }
            if (q.empty()) {
                return false;
            }
            TRACE("dioph_eq", tout << "j:"<< j<< ", t: "; print_lar_term_L(term_to_tighten, tout) << std::endl;);
            fill_indexed_work_vector_from_term(term_to_tighten);
            TRACE("dioph_eq", tout << "t orig:"; print_lar_term_L(term_to_tighten, tout) << std::endl; tout << "from ind:";
                  print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "m_tmp_l:"; print_lar_term_L(m_tmp_l, tout) << std::endl;
                );
            subs_indexed_vector_with_S(q);

            TRACE("dioph_eq", tout << "after subs\n"; print_term_o(create_term_from_ind_c(), tout) << std::endl;
                tout << "term_to_tighten:"; print_lar_term_L(term_to_tighten, tout) << std::endl;
                tout << "m_tmp_l:"; print_lar_term_L(m_tmp_l, tout) << std::endl;
                tout << "open_ml:"; print_term_o( open_ml(m_tmp_l), tout) << std::endl;
                tout << "term_to_tighten + open_ml:"; print_term_o(term_to_tighten + open_ml(m_tmp_l), tout) << std::endl;
                print_lar_term_L(remove_fresh_vars(term_to_tighten + open_ml(m_tmp_l)), tout) << std::endl;
                );
            SASSERT(fix_vars(remove_fresh_vars(term_to_tighten + open_ml(m_tmp_l) - create_term_from_ind_c())).is_empty());
            mpq g = gcd_of_coeffs(m_indexed_work_vector);
            TRACE("dioph_eq", tout << "after process_q_with_S\nt:"; print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "g:" << g << std::endl; /*tout << "dep:"; print_dep(tout, m_tmp_l) << std::endl;*/);
            
            if (g.is_one()) {
                TRACE("dioph_eq", tout << "g is one" << std::endl;);
                return false;
            } else if (g.is_zero()) {
                handle_constant_term(j);
                if (!m_infeas_explanation.empty())
                     return true;
                return false;
            } 
            // g is not trivial, trying to tighten the bounds
            return tighten_bounds_for_term(g, j);            
        }

        void get_expl_from_lar_term(const lar_term & l, explanation& ex) {
            for (const auto& p: l) {
                if (lra.column_is_fixed(p.j())) {
                    u_dependency* u = lra.get_bound_constraint_witnesses_for_column(p.j());
                    for (const auto& ci: lra.flatten(u)) {
                        ex.push_back(ci);
                    }
                }
            }
        }
        
        void handle_constant_term(unsigned j) {
            if (m_c.is_zero()) {
                return;
            }
            mpq rs;
            bool is_strict;
            u_dependency *b_dep = nullptr;
            if (lra.has_upper_bound(j, b_dep, rs, is_strict)) {
                if (m_c > rs || (is_strict && m_c == rs)) {
                    get_expl_from_lar_term(m_tmp_l, m_infeas_explanation);
                    return;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                if (m_c < rs || (is_strict && m_c == rs)) {
                    get_expl_from_lar_term(m_tmp_l, m_infeas_explanation);
                }
            }
        }

        // returns true if there is a change in the bounds
        // m_indexed_work_vector contains the coefficients of the term
        // m_c contains the constant term
        // m_tmp_l is the linear combination of the equations that removs the substituted variablse
        bool tighten_bounds_for_term(const mpq& g, unsigned j) {
            mpq rs;
            bool is_strict;
            bool change = false;
            u_dependency *b_dep = nullptr;
            SASSERT(!g.is_zero());

            if (lra.has_upper_bound(j, b_dep, rs, is_strict)) {
                TRACE("dioph_eq", tout << "current upper bound for x:" << j << ":" << rs << std::endl;);
                rs = (rs - m_c) / g;
                TRACE("dioph_eq", tout << "(rs - m_c) / g:" << rs << std::endl;);
                if (!rs.is_int()) {
                    tighten_bound_for_term_for_bound_kind(g, j, rs, true);
                    change = true;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                TRACE("dioph_eq", tout << "current lower bound for x" << j << ":" << rs << std::endl;);
                rs = (rs - m_c) / g;
                TRACE("dioph_eq", tout << "(rs - m_c) / g:" << rs << std::endl;);
                if (!rs.is_int()) {
                    tighten_bound_for_term_for_bound_kind(g, j, rs, false);
                    change = true;
                }
            }
            return change;
            
        }

        void tighten_bound_for_term_for_bound_kind( const mpq& g, unsigned j, const mpq & ub, bool upper) {
            // ub = (upper_bound(j) - m_c)/g.
            // we have x[j] = t = g*t_+ m_c <= upper_bound(j), then
            // t_ <= floor((upper_bound(j) - m_c)/g) = floor(ub)
            //
            // so xj = g*t_+m_c <= g*floor(ub) + m_c is new upper bound
            // <= can be replaced with >= for lower bounds, with ceil instead of floor
            mpq bound = g * (upper? floor(ub) : ceil(ub)) + m_c;
            TRACE("dioph_eq", tout << "is upper:" << upper << std::endl;
                  tout << "new " << (upper? "upper":"lower" ) <<  " bound:" << bound << std::endl;
                );
            
            SASSERT(upper && bound < lra.get_upper_bound(j).x || !upper && bound > lra.get_lower_bound(j).x);
            lconstraint_kind kind = upper? lconstraint_kind::LE: lconstraint_kind::GE;
            u_dependency* dep = collect_explanation_from_indexed_vector(upper);
            dep = lra.mk_join(dep, explain_fixed(m_tmp_l));
            u_dependency* j_bound_dep = upper? lra.get_column_upper_bound_witness(j): lra.get_column_lower_bound_witness(j);
            dep = lra.mk_join(dep, j_bound_dep);
            TRACE("dioph_eq", tout << "jterm:"; print_lar_term_L(lra.get_term(j), tout) << "\ndep:"; print_dep(tout, dep) << std::endl;);            
            lra.update_column_type_and_bound(j, kind, bound, dep);            
        }

        u_dependency* explain_fixed(const lar_term& t) {
            u_dependency* dep = nullptr;
            for (const auto& p: t) {
                if (is_fixed(p.j())) {
                    u_dependency* bound_dep = lra.get_bound_constraint_witnesses_for_column(p.j());
                    dep = lra.mk_join(dep, bound_dep);
                }
            }
            return dep;
        }

        u_dependency* collect_explanation_from_indexed_vector(bool upper) {
            TRACE("dioph_eq",
                tout << (upper?"upper":"lower")  << std::endl;
                tout << "indexed_vec:"; print_term_o(create_term_from_ind_c(), tout);
            );

            term_o t = remove_fresh_vars(create_term_from_ind_c());    

            u_dependency* dep = nullptr;
            int bound_sign = upper? 1: -1;
            for (const auto& p: t) {
                int var_bound_sign = p.coeff().is_pos()? bound_sign: -bound_sign;
                u_dependency* bound_dep = (var_bound_sign == 1? lra.get_column_upper_bound_witness(p.var()): lra.get_column_lower_bound_witness(p.var()));
                dep = lra.mk_join(dep, bound_dep);
            }
            return dep;
        }
public:
        lia_move check() {
            init();
            while (m_f.size()) {
                if (!normalize_by_gcd()) {
                    lra.settings().stats().m_dio_conflicts++;
                    if (m_report_branch) {
                        m_report_branch = false;
                        return lia_move::branch;
                    }
                    return lia_move::conflict;
                }
                rewrite_eqs();
                if (m_conflict_index != UINT_MAX) {
                    lra.settings().stats().m_dio_conflicts++;
                    return lia_move::conflict;
                }
            }
            TRACE("dioph_eq", print_S(tout););
            lia_move ret = tighten_with_S();
            if (ret == lia_move::conflict) {
                lra.settings().stats().m_dio_conflicts++;
                enable_trace("arith");
                enable_trace("dioph_eq");
                return lia_move::conflict;
             }
            return lia_move::undef;
        }
       private: 
        std::list<unsigned>::iterator pick_eh() {
            return m_f.begin(); // TODO: make a smarter joice
        }

        void add_operator(lar_term& t, const mpq& k, const lar_term& l) {
            for (const auto& p: l) {
                t.add_monomial(k*p.coeff(), p.j());
            }
        }

        std::tuple<mpq, unsigned, int> find_minimal_abs_coeff(unsigned row_index) const {
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
            mpq t;
            for (const auto& p : m_e_matrix.m_rows[row_index]) {
                t = abs(p.coeff());
                if (first || t < ahk || (t == ahk && p.var() < k)) { // tre last condition is for debug
                    ahk = t;
                    k_sign = p.coeff().is_pos() ? 1 : -1;
                    k = p.var();
                    first = false;
//                if (ahk.is_one()) // uncomment later
                //                  break;                    
                }
            }
            
            return std::make_tuple(ahk, k, k_sign);
        }

        term_o get_term_to_subst(const term_o& eh, unsigned k, int k_sign) {
            term_o t;
            for (const auto & p: eh) {
                if (p.j() == k) continue;
                t.add_monomial(-k_sign*p.coeff(), p.j());
            }
            t.c() = -k_sign*eh.c();
            TRACE("dioph_eq", tout << "subst_term:"; print_term_o(t, tout) << std::endl;);
            return t;
        }

        std::ostream& print_e_row(unsigned i, std::ostream& out) {
            return print_term_o(get_term_from_e_matrix(i), out);
        }
        // j is the variable to eliminate, it appears in row e.m_e_matrix with 
        // a coefficient equal to +-1
        void eliminate_var_in_f(eprime_entry& e, unsigned j, int j_sign) {
            TRACE("dioph_eq", tout << "eliminate var:" << j << " by using:"; print_eprime_entry(e.m_row_index, tout) << std::endl;);
            SASSERT(entry_invariant(e));
            unsigned piv_row_index = e.m_row_index;
            auto &column = m_e_matrix.m_columns[j];
            int pivot_col_cell_index = -1;
            for (unsigned k = 0; k < column.size(); k++) {
                if (column[k].var() == piv_row_index) {
                    pivot_col_cell_index = k;
                    break;
                }
            }
            SASSERT(pivot_col_cell_index != -1);                
            if (pivot_col_cell_index != 0) {
                // swap the pivot column cell with the head cell
                auto c = column[0];
                column[0]  = column[pivot_col_cell_index];
                column[pivot_col_cell_index] = c;

                m_e_matrix.m_rows[piv_row_index][column[0].offset()].offset() = 0;
                m_e_matrix.m_rows[c.var()][c.offset()].offset() = pivot_col_cell_index;
            }

            unsigned cell_to_process = column.size() - 1;
            while (cell_to_process > 0) {
                auto & c = column[cell_to_process];
                if (m_eprime[c.var()].m_entry_status != entry_status::F) {
                    cell_to_process--;
                    continue;
                }
                
                SASSERT(c.var() != piv_row_index && entry_invariant(m_eprime[c.var()]));
                mpq coeff = m_e_matrix.get_val(c);
                unsigned i = c.var();
                TRACE("dioph_eq", tout << "before pivot entry :"; print_eprime_entry(i, tout) << std::endl;);
                m_eprime[i].m_c -=  j_sign * coeff*e.m_c;
                m_e_matrix.pivot_row_to_row_given_cell_with_sign(piv_row_index, c, j, j_sign);
                m_eprime[i].m_l -=  j_sign * coeff * e.m_l;
                TRACE("dioph_eq", tout << "after pivoting c_row:"; print_eprime_entry(i, tout););
                CTRACE("dioph_eq", !entry_invariant(m_eprime[i]), 
                tout << "invariant delta:"; 
                {   
                    const auto& e = m_eprime[i];                    
                    print_term_o(get_term_from_e_matrix(e.m_row_index) - fix_vars(open_ml(e.m_l)), tout) << std::endl;
                }
                );
                SASSERT(entry_invariant(m_eprime[i]));
                cell_to_process--;
            }
        }

        bool entry_invariant(const eprime_entry& e) const {
            return remove_fresh_vars(get_term_from_e_matrix(e.m_row_index)) == fix_vars(open_ml(e.m_l));
        }

        term_o remove_fresh_vars(const term_o& tt) const{
            term_o t = tt;
            std::queue<unsigned> q;
            for (const auto& p: t) {
                if (is_fresh_var(p.j())) {
                    q.push(p.j());
                }
            }
            while (!q.empty()) {
                unsigned xt = pop_front(q);
                const auto & xt_row = m_e_matrix.m_rows[m_k2s[xt]];
                term_o xt_term;
                for (const auto & p: xt_row) {
                    if (p.var() == xt) continue;
                    xt_term.add_monomial(p.coeff(), p.var());
                }
                mpq xt_coeff = t.get_coeff(xt);
                t.erase_var(xt);
                t += xt_coeff * xt_term;
                for (const auto & p: t) {
                    if (is_fresh_var(p.j())) {
                        q.push(p.j());
                    }
                }
            }
            return t;
        }

        std::ostream& print_ml(const lar_term & ml, std::ostream & out) {
            term_o opened_ml = open_ml(ml);
            return print_term_o(opened_ml, out);
        }

        term_o open_ml(const lar_term & ml) const {
            term_o r;
            for (const auto& p : ml) {
                r += p.coeff()*(lra.get_term(p.var()) - lar_term(p.var()));                
            }
            return r;
        }
       // it clears the row, and puts the term in the work vector
        void move_row_to_work_vector(unsigned e_index) {
            unsigned h = m_eprime[e_index].m_row_index; 
            // backup the term at h
            m_indexed_work_vector.resize(m_e_matrix.column_count());
            auto &hrow = m_e_matrix.m_rows[h];
            for (const auto& cell : hrow)
                m_indexed_work_vector.set_value(cell.coeff(), cell.var());
            while (hrow.size() > 0) {
                auto & c = hrow.back();
                m_e_matrix.remove_element(hrow, c);
            }
        }
       
        // k is the variable to substitute
        void fresh_var_step(unsigned h, unsigned k, const mpq& ahk) {
            move_row_to_work_vector(h); // it clears the row, and puts the term in the work vector
            // step 7 from the paper
            // xt is the fresh variable
            unsigned xt = std::max(m_e_matrix.column_count(), lra.column_count()); // use var_register later
            unsigned fresh_row = m_e_matrix.row_count();
            m_e_matrix.add_row(); // for the fresh variable definition
            while (xt >= m_e_matrix.column_count())
                 m_e_matrix.add_column(); 
            // Add a new row for the fresh variable definition
            /* Let eh = sum(ai*xi) + c. For each i != k, let ai = qi*ahk + ri, and let c = c_q * ahk + c_r.
               eh = ahk*(x_k + sum{qi*xi|i != k} + c_q) + sum {ri*xi|i!= k} + c_r.
               Then -xt + x_k + sum {qi*x_i)| i != k} + c_q will be the fresh row
               eh = ahk*xt +  sum {ri*x_i | i != k} + c_r  is the row m_e_matrix[e.m_row_index]
            */  
            auto & e = m_eprime[h];
            mpq q, r;
            q = machine_div_rem(e.m_c, ahk, r);
            e.m_c = r;
            m_e_matrix.add_new_element(h, xt, ahk);
            
            m_eprime.push_back({fresh_row, lar_term(), mpq(0), entry_status::NO_S_NO_F});
            m_e_matrix.add_new_element(fresh_row, xt, -mpq(1));
            m_e_matrix.add_new_element(fresh_row, k, mpq(1));
            for (unsigned i: m_indexed_work_vector.m_index) {
                mpq ai = m_indexed_work_vector[i];
                if (i == k) continue;
                q = machine_div_rem(ai, ahk, r);
                if (!r.is_zero()) 
                    m_e_matrix.add_new_element(h, i, r);
                if (!q.is_zero())
                    m_e_matrix.add_new_element(fresh_row, i, q);
            }
    
            m_k2s.resize(std::max(k + 1, xt + 1), -1);  
            m_k2s[k] = m_k2s[xt] = fresh_row;
            TRACE("dioph_eq", tout << "changed entry:"; print_eprime_entry(h, tout)<< std::endl;      
                  tout <<  "added entry for fresh var:\n"; print_eprime_entry(fresh_row, tout) << std::endl;);
            SASSERT(entry_invariant(m_eprime[h]));      
            SASSERT(entry_invariant(m_eprime[fresh_row]));
            eliminate_var_in_f(m_eprime.back(), k, 1);
        }

        std::ostream& print_eprime_entry(unsigned i, std::ostream& out, bool print_dep = true) {
            out << "m_eprime[" << i << "]:";
            return print_eprime_entry(m_eprime[i], out, print_dep);
        }

        std::ostream& print_eprime_entry(const eprime_entry& e, std::ostream& out, bool print_dep = true) {
            out << "{\n";
            print_term_o(get_term_from_e_matrix(e.m_row_index), out << "\tm_e:") << ",\n";
            //out << "\tstatus:" << (int)e.m_entry_status;
            if (print_dep) {
                out << "\tm_l:{"; print_lar_term_L(e.m_l, out) << "}, ";
                print_ml(e.m_l, out<< " \topened m_l:") << "\n";   
            }
            out << "}\n";
            return out;
        }      
        
        // k is the index of the variable that is being substituted
        void move_entry_from_f_to_s(unsigned k, unsigned h) {
            SASSERT(m_eprime[h].m_entry_status == entry_status::F);
            m_eprime[h].m_entry_status = entry_status::S;
            if (k >= m_k2s.size()) { // k is a fresh variable
                m_k2s.resize(k+1, -1 );
            }
            m_s.push_back(h);
            TRACE("dioph_eq", tout << "removed " << h << "th entry from F" << std::endl;);
            m_k2s[k] = h;
            m_f.remove(h);
         }

        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            unsigned h = -1;
            auto it = m_f.begin(); 
            while (it != m_f.end()) {
                SASSERT(*it ==m_eprime[*it].m_row_index);
                if (m_e_matrix.m_rows[*it].size() == 0) {
                    if (m_eprime[*it].m_c.is_zero()) {
                        it = m_f.erase(it);
                        continue;
                    } else {
                        m_conflict_index = *it;
                        return;
                    }
                }
                h = *it;
                break;
            }
            if (h == UINT_MAX) return; 
            auto& eprime_entry = m_eprime[h];
            TRACE("dioph_eq", print_eprime_entry(h, tout););
            auto [ahk, k, k_sign] = find_minimal_abs_coeff(eprime_entry.m_row_index);
            TRACE("dioph_eq", tout << "ahk:" << ahk << ", k:" << k << ", k_sign:" << k_sign << std::endl;);
            if (ahk.is_one()) {
                TRACE("dioph_eq", tout << "push to S:\n"; print_eprime_entry(h, tout););
                move_entry_from_f_to_s(k, h);
                eliminate_var_in_f(eprime_entry, k , k_sign);
            } else {
                fresh_var_step(h, k, ahk*mpq(k_sign));
            }
        }
public:
        void explain(explanation& ex) {
            if (m_conflict_index == UINT_MAX) {
                SASSERT(!(lra.get_status() == lp_status::FEASIBLE || lra.get_status() == lp_status::OPTIMAL));
                for (auto ci: m_infeas_explanation) {
                    ex.push_back(ci.ci());
                }
                TRACE("dioph_eq", lra.print_expl(tout, ex););
                return;
            }
            SASSERT(ex.empty());
            TRACE("dioph_eq", tout << "conflict:"; print_eprime_entry(m_conflict_index, tout, true) << std::endl;);
            auto & ep = m_eprime[m_conflict_index];
            /*
              for (const auto & pl : ep.m_l) {
              unsigned row_index = pl.j();
              for (const auto & p : lra.get_row(row_index))
              if (lra.column_is_fixed(p.var()))
              lra.explain_fixed_column(p.var(), ex);
              }
            */
            for (auto ci: lra.flatten(eq_deps(ep.m_l))) {
                ex.push_back(ci);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }

        bool is_fresh_var(unsigned j) const {
            return j >= lra.column_count();
        }
        bool can_substitute(unsigned k) {
            return k < m_k2s.size() && m_k2s[k] != -1;
        }
        u_dependency * eq_deps(const lar_term& t) {
            NOT_IMPLEMENTED_YET();
            return nullptr;
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

}
