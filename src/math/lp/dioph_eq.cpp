#include "math/lp/dioph_eq.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include <list>
#include <queue>
/*
    Following paper: "A Practical Approach to Satisfiability  Modulo Linear Integer Arithmetic"
    by Alberto Griggio(griggio@fbk.eu)
    Data structures are:
    -- term_o: inherits lar_term and differs from it by having a constant, while lar_term is just
    a sum of monomials
    -- entry : has a dependency lar_term, keeping the history of the entry updates, the rational constant
    of the corresponding term_o, and the entry status that is in {F,S, NO_S_NO_F}. The entry status is used for efficiency
    reasons. It allows quickly check if an entry belongs to F, S, or neither. 
    dioph_eq::imp main fields are
    -- lra: pointer to lar_solver.
    -- lia: point to int_solver.
    -- m_entries: it keeps all "entry" objects.
    -- m_e_matrix: i-th row of this matrix keeps the term corresponding to m_entries[i].
    The actual term is the sum of the matrix row and the constant m_c of the entry.
    The column j of the matrix corresponds to j column of lar_solver if j < lra.column_count().
    Otherwise, j is a fresh column. It has to change in the interactive version.
    Implementation remarks:
    -- get_term_from_entry(unsigned i) return a term corresponding i-th entry. If t = get_term_from_entry(i)
    then we have equality t = 0. Initially get_term_from_entry(i) is set to initt(j) = lra.get_term(j) - j,
    for some column j,where all fixed variables are replaced by their values.
    To track the explanations of equality t = 0 we initially set m_entries[i].m_l = lar_term(j), and update m_l
    accordingly with the pivot operations. The explanation is obtained by replacing term m_l = sum(aj*j) by the linear
    combination sum (aj*initt(j)) and joining the explanations of all fixed variables in the latter sum.
    entry_invariant(i) guarantees the validity of the i-th entry.
 */
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
                print_entry(i, out);
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
        struct entry {
            lar_term m_l;
            mpq m_c; // the constant of the term, the term is taken from the row of m_e_matrix with the same index as the entry
            entry_status m_entry_status;
        };
        var_register m_var_register;
        std_vector<entry> m_entries;    
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
        std_vector<unsigned> m_fresh_definitions; // seems only needed in the debug version in remove_fresh_vars
        unsigned            m_conflict_index = -1;  // m_entries[m_conflict_index] gives the conflict
        public:
        imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {}
        term_o get_term_from_entry(unsigned i) const {
            term_o t;
            for (const auto & p: m_e_matrix.m_rows[i]) {
                t.add_monomial(p.coeff(), p.var());
            }
            t.c() = m_entries[i].m_c;
            return t;
        }

        // adds variable j of lar_solver to the local diophantine handler
        unsigned add_var(unsigned j) {
            return this->m_var_register.add_var(j, true);
        }
        
        unsigned local_to_lar_solver(unsigned j) const {
            return m_var_register.local_to_external(j);
        }
        
        // the term has form sum(a_i*x_i) - t.j() = 0,
        // i is the index of the term in the lra.m_terms
        void fill_entry(const lar_term& t) {
            TRACE("dioph_eq", print_lar_term_L(t, tout) << std::endl;);
            entry te = {lar_term(t.j()), mpq(0), entry_status::F};
            unsigned entry_index = m_entries.size();
            m_f.push_back(entry_index);            
            m_entries.push_back(te);
            entry& e = m_entries.back();
            m_e_matrix.add_row();
            SASSERT(m_e_matrix.row_count() == m_entries.size());

            for (const auto & p: t) {
                SASSERT(p.coeff().is_int());
                if (is_fixed(p.var())) 
                    e.m_c += p.coeff()*lia.lower_bound(p.var()).x;
                else {
                    unsigned lj = add_var(p.var());
                    while (lj >= m_e_matrix.column_count())
                        m_e_matrix.add_column();
                    m_e_matrix.add_new_element(entry_index, lj, p.coeff());
                }                
            }
            if (is_fixed(t.j()))
                e.m_c -= lia.lower_bound(t.j()).x;            
            else {
                unsigned lj = add_var(t.j());
                while (lj >= m_e_matrix.column_count())
                    m_e_matrix.add_column();
                m_e_matrix.add_new_element(entry_index, lj, - mpq(1));
            }                
            TRACE("dioph_eq", print_entry(entry_index, tout););
            SASSERT(entry_invariant(entry_index));
        }

        bool all_vars_are_int(const lar_term& term) const {
            for (const auto& p : term) {
                if (!lia.column_is_int(p.var())) 
                    return false;
            }            
            return true;
        }

        void init() {
            m_e_matrix = static_matrix<mpq, mpq>();
            m_report_branch = false;
            m_k2s.clear();
            m_fresh_definitions.clear();
            m_conflict_index = -1;
            m_infeas_explanation.clear();
            lia.get_term().clear();
            m_entries.clear();
            m_var_register.clear();

            for (unsigned j = 0; j < lra.column_count(); j++) {
                if (!lra.column_is_int(j)|| !lra.column_has_term(j)) continue;
                const lar_term& t = lra.get_term(j);
                if (!all_vars_are_int(t)) {
                    TRACE("dioph_eq", tout << "not all vars are integrall\n";);
                    continue;
                }
                fill_entry(t);
            }
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

        void prepare_lia_branch_report(unsigned ei, const entry & e, const mpq& g, const mpq new_c) {
            /* We have ep.m_e/g = 0, or sum((coff_i/g)*x_i) + new_c = 0,
               or sum((coeff_i/g)*x_i) = -new_c, where new_c is not an integer
               Then sum((coeff_i/g)*x_i) <= floor(-new_c) or sum((coeff_i/g)*x_i) >= ceil(-new_c)
            */
            lar_term& t = lia.get_term();
            for (const auto& p: m_e_matrix.m_rows[ei]) {
                t.add_monomial(p.coeff()/g, local_to_lar_solver(p.var()));
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
        bool normalize_e_by_gcd(unsigned ei) {
            entry& e = m_entries[ei];
            TRACE("dioph_eq", print_entry(ei, tout) << std::endl;);
            mpq g = gcd_of_coeffs(m_e_matrix.m_rows[ei]);
            if (g.is_zero() || g.is_one()) {
                SASSERT(g.is_one() || e.m_c.is_zero());
                return true;
            }
            TRACE("dioph_eq", tout << "g:" << g << std::endl;);
            mpq c_g = e.m_c / g;
            if (c_g.is_int()) {
                for (auto& p: m_e_matrix.m_rows[ei]) {
                    p.coeff() /= g;
                }
                m_entries[ei].m_c = c_g;
                e.m_l *= (1/g);
                TRACE("dioph_eq",  tout << "ep_m_e:"; print_entry(ei, tout) << std::endl;);
                SASSERT(entry_invariant(ei));
                return true;
            }
            // c_g is not integral
            if (lra.settings().stats().m_dio_conflicts % lra.settings().dio_cut_from_proof_period() == 0 && !has_fresh_var(ei))
                prepare_lia_branch_report(ei, e, g, c_g);
            return false;
        }

        // returns true if no conflict is found and false otherwise
        bool normalize_by_gcd() {
            for (unsigned l: m_f) {
                if (!normalize_e_by_gcd(l)) {
                    SASSERT(entry_invariant(l));
                    m_conflict_index = l;
                    return false;
                }
                SASSERT(entry_invariant(l));                    
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
            if (m_indexed_work_vector[k].is_zero()) return;
            const entry& e = entry_for_subs(k);
            TRACE("dioph_eq", tout << "k:" << k << ", in ";  print_term_o(create_term_from_ind_c(), tout) << std::endl;
            tout << "subs with e:"; print_entry(m_k2s[k], tout) << std::endl;);
            mpq coeff = m_indexed_work_vector[k]; // need to copy since it will be zeroed 
            m_indexed_work_vector.erase(k);         // m_indexed_work_vector[k] = 0;   
            
            const auto& e_row = m_e_matrix.m_rows[m_k2s[k]];
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
                const auto & t = lra.get_term(local_to_lar_solver(p.j()));
                ret.add_monomial(-mpq(1), p.j());
                for (const auto& q: t) {
                    ret.add_monomial(p.coeff()*q.coeff(), q.j());
                }
            }
            return ret;
        }

        bool is_fixed(unsigned j) const {
            return lra.column_is_fixed(j);
        }

        template <typename T> term_o fix_vars(const T& t) const {
            term_o ret;
            for (const auto& p: t) {
                if (is_fixed(p.var())) {
                    ret.c() += p.coeff() * this->lra.get_lower_bound(p.var()).x;
                } else {
                    ret.add_monomial(p.coeff(), p.var());
                }
            }
            return ret;
        }
        const entry& entry_for_subs(unsigned k) const {
            return m_entries[m_k2s[k]];
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

        lia_move tighten_with_S() {
            for (unsigned j = 0; j < lra.column_count(); j++) {               
                if (!lra.column_has_term(j) || lra.column_is_free(j) ||
                    is_fixed(j) || !lia.column_is_int(j)) continue;
                
                if (tighten_bounds_for_term_column(j))
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
                    m_indexed_work_vector.set_value(p.coeff(), lar_solver_to_local(p.j()));
            }
            
        }
        unsigned lar_solver_to_local(unsigned j) const {
            return m_var_register.external_to_local(j);
        }
        // j is the index of the column representing a term
        // return true if a conflict was found
        bool tighten_bounds_for_term_column(unsigned j) {
            term_o term_to_tighten = lra.get_term(j); // copy the term aside
            if (!all_vars_are_int(term_to_tighten)) return false;
            std::queue<unsigned> q;
            for (const auto& p: term_to_tighten) {
                if (!lra.column_is_fixed(p.j()) && can_substitute(lar_solver_to_local(p.j()))) 
                    q.push(lar_solver_to_local(p.j()));
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
            SASSERT(
            fix_vars(term_to_tighten + open_ml(m_tmp_l)) ==  
             term_to_lar_solver(remove_fresh_vars(create_term_from_ind_c())));
            mpq g = gcd_of_coeffs(m_indexed_work_vector);
            TRACE("dioph_eq", tout << "after process_q_with_S\nt:"; print_term_o(create_term_from_ind_c(), tout) << std::endl;
                  tout << "g:" << g << std::endl; /*tout << "dep:"; print_dep(tout, m_tmp_l) << std::endl;*/);
            
            if (g.is_one()) return false;
            if (g.is_zero()) {
                handle_constant_term(j);
                return !m_infeas_explanation.empty();
            } 
            // g is not trivial, trying to tighten the bounds
            return tighten_bounds_for_non_trivial_gcd(g, j, true) 
                   || 
                   tighten_bounds_for_non_trivial_gcd(g, j, false);
        }

        void get_expl_from_meta_term(const lar_term& t, explanation& ex) {
            u_dependency *dep = explain_fixed_in_meta_term(t);
            for (constraint_index ci : lra.flatten(dep))
                ex.push_back(ci);
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
                    u_dependency* dep = lra.mk_join(explain_fixed(lra.get_term(j)), explain_fixed_in_meta_term(m_tmp_l));
                    dep = lra.mk_join(dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                    return;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                if (m_c < rs || (is_strict && m_c == rs)) {
                    u_dependency* dep = lra.mk_join(explain_fixed(lra.get_term(j)), explain_fixed_in_meta_term(m_tmp_l));
                    dep = lra.mk_join(dep, lra.get_bound_constraint_witnesses_for_column(j));
                    for (constraint_index ci : lra.flatten(dep)) {
                        m_infeas_explanation.push_back(ci);
                    }
                }
            }
        }

        // returns true if there is a change in the bounds
        // m_indexed_work_vector contains the coefficients of the term
        // m_c contains the constant term
        // m_tmp_l is the linear combination of the equations that removs the substituted variablse
        // returns true iff the conflict is found
        bool tighten_bounds_for_non_trivial_gcd(const mpq& g, unsigned j, bool is_upper) {
            mpq rs;
            bool is_strict;
            u_dependency *b_dep = nullptr;
            SASSERT(!g.is_zero());

            if (lra.has_bound_of_type(j, b_dep, rs, is_strict, is_upper)) {
                TRACE("dioph_eq", tout << "current upper bound for x:" << j << ":" << rs << std::endl;);
                rs = (rs - m_c) / g;
                TRACE("dioph_eq", tout << "(rs - m_c) / g:" << rs << std::endl;);
                if (!rs.is_int()) {
                    if (tighten_bound_kind(g, j, rs, is_upper, b_dep))
                        return true;    
                }
            }
            return false;
        }

        bool tighten_bound_kind( const mpq& g, unsigned j, const mpq & ub, bool upper, u_dependency* prev_dep) {
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
            
            SASSERT((upper && bound < lra.get_upper_bound(j).x) || (!upper && bound > lra.get_lower_bound(j).x));
            lconstraint_kind kind = upper? lconstraint_kind::LE: lconstraint_kind::GE;
            u_dependency* dep = prev_dep;
            dep = lra.mk_join(dep, explain_fixed_in_meta_term(m_tmp_l));
            u_dependency* j_bound_dep = upper? lra.get_column_upper_bound_witness(j): lra.get_column_lower_bound_witness(j);
            dep = lra.mk_join(dep, j_bound_dep);
            dep = lra.mk_join(dep, explain_fixed(lra.get_term(j)));
            dep = lra.mk_join(dep, lra.get_bound_constraint_witnesses_for_column(j));
            TRACE("dioph_eq", tout << "jterm:"; print_lar_term_L(lra.get_term(j), tout) << "\ndep:"; print_dep(tout, dep) << std::endl;
            );            
            lra.update_column_type_and_bound(j, kind, bound, dep);            
            auto st = lra.find_feasible_solution();
            if (st != lp::lp_status::FEASIBLE && st != lp::lp_status::OPTIMAL && st != lp::lp_status::CANCELLED) {
                lra.get_infeasibility_explanation(m_infeas_explanation);
                return true;
            }
            return false;
        }

        u_dependency* explain_fixed_in_meta_term(const lar_term& t) {
            u_dependency* dep = nullptr;

            for (const auto& p: open_ml(t)) {
                if (is_fixed(p.j()))
                    dep = lra.mk_join(dep, lra.get_bound_constraint_witnesses_for_column(p.j()));                
            }
            return dep;
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

        std::tuple<mpq, unsigned, int> find_minimal_abs_coeff(unsigned ei) const {
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
            mpq t;
            for (const auto& p : m_e_matrix.m_rows[ei]) {
                t = abs(p.coeff());
                if (first || t < ahk || (t == ahk && p.var() < k)) { // the last condition is for debug
                    ahk = t;
                    k_sign = p.coeff().is_pos() ? 1 : -1;
                    k = p.var();
                    first = false;
                    if (ahk.is_one())
                        break;                    
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
            return print_term_o(get_term_from_entry(i), out);
        }
        // j is the variable to eliminate, it appears in row e.m_e_matrix with 
        // a coefficient equal to +-1
        void eliminate_var_in_f(unsigned ei, unsigned j, int j_sign) {
            entry& e = m_entries[ei];
            TRACE("dioph_eq", tout << "eliminate var:" << j << " by using:"; print_entry(ei, tout) << std::endl;);
            auto &column = m_e_matrix.m_columns[j];
            auto it = std::find_if(column.begin(), column.end(), [ei](const auto &cell) {return cell.var() == ei;});
            unsigned pivot_col_cell_index = std::distance(column.begin(), it);
            if (pivot_col_cell_index != 0) {
                // swap the pivot column cell with the head cell
                auto c = column[0];
                column[0]  = column[pivot_col_cell_index];
                column[pivot_col_cell_index] = c;

                m_e_matrix.m_rows[ei][column[0].offset()].offset() = 0;
                m_e_matrix.m_rows[c.var()][c.offset()].offset() = pivot_col_cell_index;
            }

            unsigned cell_to_process = column.size() - 1;
            while (cell_to_process > 0) {
                auto & c = column[cell_to_process];
                if (m_entries[c.var()].m_entry_status != entry_status::F) {
                    cell_to_process--;
                    continue;
                }
                
                SASSERT(c.var() != ei && entry_invariant(c.var()));
                mpq coeff = m_e_matrix.get_val(c);
                unsigned i = c.var();
                TRACE("dioph_eq", tout << "before pivot entry :"; print_entry(i, tout) << std::endl;);
                m_entries[i].m_c -=  j_sign * coeff*e.m_c;
                m_e_matrix.pivot_row_to_row_given_cell_with_sign(ei, c, j, j_sign);
                m_entries[i].m_l -=  j_sign * coeff * e.m_l;
                TRACE("dioph_eq", tout << "after pivoting c_row:"; print_entry(i, tout););
                CTRACE("dioph_eq", !entry_invariant(i), 
                tout << "invariant delta:"; 
                {   
                    const auto& e = m_entries[i];                    
                    print_term_o(get_term_from_entry(ei) - fix_vars(open_ml(e.m_l)), tout) << std::endl;
                }
                );
                SASSERT(entry_invariant(i));
                cell_to_process--;
            }
        }

        term_o term_to_lar_solver(const term_o& eterm) const {
            term_o ret;
            for (const auto& p : eterm) {
                ret.add_monomial(p.coeff(), local_to_lar_solver(p.var()));
            }
            ret.c() = eterm.c();
            return ret;
        }

        bool entry_invariant(unsigned ei) const {
            const auto &e = m_entries[ei];
            bool ret =  term_to_lar_solver(remove_fresh_vars(get_term_from_entry(ei))) == fix_vars(open_ml(e.m_l));
            if (ret) return true;
            TRACE("dioph_eq", 
                  tout << "get_term_from_entry("<< ei <<"):";
                  print_term_o(get_term_from_entry(ei), tout) <<std::endl;
                  tout << "remove_fresh_vars:"; print_term_o(remove_fresh_vars(get_term_from_entry(ei)), tout) << std::endl;
                  tout << "e.m_l:"; print_lar_term_L(e.m_l, tout) << std::endl;                  
                  tout << "open_ml(e.m_l):"; print_term_o(open_ml(e.m_l), tout) << std::endl;
                  tout << "fix_vars(open_ml(e.m_l)):"; print_term_o(fix_vars(open_ml(e.m_l)), tout) << std::endl;
                );
            return false;
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
                term_o fresh_t = get_term_from_entry(m_fresh_definitions[xt]);
                if (fresh_t.get_coeff(xt).is_minus_one() == false)
                    std::cout << "coeff:" << fresh_t.get_coeff(xt) << std::endl;
                SASSERT(fresh_t.get_coeff(xt).is_minus_one());
                fresh_t.erase_var(xt);
                if (!t.contains(xt)) continue;
                mpq xt_coeff = t.get_coeff(xt);
                t.erase_var(xt);
                t += xt_coeff * fresh_t;
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
        void move_row_to_work_vector(unsigned ei) {
            m_indexed_work_vector.resize(m_e_matrix.column_count());
            auto &row = m_e_matrix.m_rows[ei];
            for (const auto& cell : row)
                m_indexed_work_vector.set_value(cell.coeff(), cell.var());
            while (row.size() > 0) {
                auto & c = row.back();
                m_e_matrix.remove_element(row, c);
            }
        }
       
        // k is the variable to substitute
        void fresh_var_step(unsigned h, unsigned k, const mpq& ahk) {
            move_row_to_work_vector(h); // it clears the row, and puts the term in the work vector
            // step 7 from the paper
            // xt is the fresh variable
            unsigned xt = add_var(UINT_MAX);
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
            auto & e = m_entries[h];
            mpq q, r;
            q = machine_div_rem(e.m_c, ahk, r);
            e.m_c = r;
            m_e_matrix.add_new_element(h, xt, ahk);
            
            m_entries.push_back({lar_term(), q, entry_status::NO_S_NO_F});
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
            m_k2s[k] = fresh_row;
            m_fresh_definitions.resize(xt + 1, -1);
            m_fresh_definitions[xt] = fresh_row;
            TRACE("dioph_eq", tout << "changed entry:"; print_entry(h, tout)<< std::endl;      
                  tout <<  "added entry for fresh var:\n"; print_entry(fresh_row, tout) << std::endl;);
            SASSERT(entry_invariant(h));      
            SASSERT(entry_invariant(fresh_row));
            eliminate_var_in_f(fresh_row, k, 1);
        }

        std::ostream& print_entry(unsigned i, std::ostream& out, bool print_dep = true) {
            out << "m_entries[" << i << "]:";
            return print_entry(i, m_entries[i], out, print_dep);
        }

        std::ostream& print_entry(unsigned ei, const entry& e, std::ostream& out, bool need_print_dep = true) {
            out << "{\n";
            print_term_o(get_term_from_entry(ei), out << "\tm_e:") << ",\n";
            //out << "\tstatus:" << (int)e.m_entry_status;
            if (need_print_dep) {
                out << "\tm_l:{"; print_lar_term_L(e.m_l, out) << "}, ";
                print_ml(e.m_l, out<< " \tfixed expl of m_l:") << "\n";   
                print_dep(out, explain_fixed_in_meta_term(e.m_l)) << ",";
            }
            switch (e.m_entry_status)
            {
            case entry_status::F:
                out << "in F\n";
                break;
            case entry_status::S:
                out << "in S\n";
                break;
                default:
                out << "NOSF\n";
            } 
            out << "}\n";
            return out;
        }      
        
        // k is the index of the variable that is being substituted
        void move_entry_from_f_to_s(unsigned k, unsigned h) {
            SASSERT(m_entries[h].m_entry_status == entry_status::F);
            m_entries[h].m_entry_status = entry_status::S;
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
                if (m_e_matrix.m_rows[*it].size() == 0) {
                    if (m_entries[*it].m_c.is_zero()) {
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
            auto [ahk, k, k_sign] = find_minimal_abs_coeff(h);
            TRACE("dioph_eq",
                  tout << "eh:"; print_entry(h, tout);
                  tout << "ahk:" << ahk << ", k:" << k << ", k_sign:" << k_sign << std::endl;);
            
            if (ahk.is_one()) {
                TRACE("dioph_eq", tout << "push to S:\n"; print_entry(h, tout););
                move_entry_from_f_to_s(k, h);
                eliminate_var_in_f(h, k , k_sign);
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
            TRACE("dioph_eq", tout << "conflict:"; print_entry(m_conflict_index, tout, true) << std::endl;);
            auto & ep = m_entries[m_conflict_index];
            for (auto ci: lra.flatten(explain_fixed_in_meta_term(ep.m_l))) {
                ex.push_back(ci);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }

        bool is_fresh_var(unsigned j) const {
            return m_var_register.local_to_external(j) == UINT_MAX;
        }
        bool can_substitute(unsigned k) {
            return k < m_k2s.size() && m_k2s[k] != UINT_MAX;
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
