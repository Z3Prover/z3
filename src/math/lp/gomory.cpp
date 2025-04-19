/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#include "math/lp/gomory.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"

namespace lp {
    
enum class row_polarity { UNDEF, MIN, MAX, MIXED};
struct create_cut {
    lar_term   &          m_t; // the term to return in the cut
    mpq        &          m_k; // the right side of the cut
    explanation*          m_ex; // the conflict explanation
    unsigned              m_inf_col; // a basis column which has to be an integer but has a non integral value
    const row_strip<mpq>& m_row;
    int_solver&           lia;
    mpq                   m_f;
    mpq                   m_one_minus_f;
    mpq                   m_fj;
    mpq                   m_one_minus_fj;
    mpq                   m_abs_max, m_big_number;
    row_polarity          m_polarity;
    bool                  m_found_big;
    u_dependency*         m_dep;

    const impq & get_value(unsigned j) const { return lia.get_value(j); }
    bool is_int(unsigned j) const { return lia.column_is_int(j) || (lia.is_fixed(j) &&
                                                             lia.lra.column_lower_bound(j).is_int()); }
    bool is_real(unsigned j) const { return !is_int(j); }
    bool at_lower(unsigned j) const { return lia.at_lower(j); }
    bool at_upper(unsigned j) const { return lia.at_upper(j); }
    const impq & lower_bound(unsigned j) const { return lia.lower_bound(j); }
    const impq & upper_bound(unsigned j) const  { return lia.upper_bound(j); }
    u_dependency* column_lower_bound_constraint(unsigned j) const { return lia.column_lower_bound_constraint(j); }
    u_dependency* column_upper_bound_constraint(unsigned j) const { return lia.column_upper_bound_constraint(j); }
    bool column_is_fixed(unsigned j) const { return lia.lra.column_is_fixed(j); }
    void push_explanation(u_dependency* d) {
        for (auto ci : lia.lra.flatten(d))
            m_ex->push_back(ci);
    }

    void int_case_in_gomory_cut(unsigned j) {
        SASSERT(is_int(j) && m_fj.is_pos());
        TRACE("gomory_cut_detail", 
              tout << " k = " << m_k;
              tout << ", fj: " << m_fj << ", ";
              tout << (at_lower(j)?"at_lower":"at_upper")<< std::endl;
              );
        mpq new_a;
        if (at_lower(j)) {
            // here we have the product of new_a*(xj - lb(j)), so new_a*lb(j) is added to m_k
            new_a = m_fj <= m_one_minus_f ? m_fj / m_one_minus_f : ((1 - m_fj) / m_f);
            SASSERT(new_a.is_pos());
            m_k.addmul(new_a, lower_bound(j).x);   
            push_explanation(column_lower_bound_constraint(j));         
        }
        else {
            SASSERT(at_upper(j));
            // here we have the expression  new_a*(xj - ub), so new_a*ub(j) is added to m_k
            new_a = - (m_fj <= m_f ? m_fj / m_f  : ((1 - m_fj) / m_one_minus_f));
            SASSERT(new_a.is_neg());
            m_k.addmul(new_a, upper_bound(j).x);
            push_explanation(column_upper_bound_constraint(j));
        }        
        m_t.add_monomial(new_a, j);
        TRACE("gomory_cut_detail", tout << "new_a = " << new_a << ", k = " << m_k << "\n";);
        if (numerator(new_a) > m_big_number)
            m_found_big = true;
    }

    void set_polarity(row_polarity p) {
        if (m_polarity == row_polarity::MIXED) return;
        if (m_polarity == row_polarity::UNDEF) m_polarity = p;
        else if (m_polarity != p) m_polarity = row_polarity::MIXED;
    }

    void real_case_in_gomory_cut(const mpq & a, unsigned j) {
        TRACE("gomory_cut_detail_real", tout << "j = " << j << ", a = " << a << ", m_k = " << m_k << "\n";);
        mpq new_a;
        if (at_lower(j)) {
            if (a.is_pos()) { 
                // the delta is a (x - f) is positive it has to grow and fight m_one_minus_f
                new_a = a / m_one_minus_f;
                set_polarity(row_polarity::MIN); // reverse the polarity since a = -p.coeff()
            }
            else {
                // the delta is negative and it works again m_f
                new_a = - a / m_f;
                set_polarity(row_polarity::MAX);
            }
            m_k.addmul(new_a, lower_bound(j).x); // is it a faster operation than
            // k += lower_bound(j).x * new_a;
            push_explanation(column_lower_bound_constraint(j));
        }
        else {
            SASSERT(at_upper(j));
            if (a.is_pos()) {
                // the delta is works again m_f
                new_a =  - a / m_f;
                set_polarity(row_polarity::MAX);
            }
            else {
                // the delta is positive works again m_one_minus_f
                new_a =   a / m_one_minus_f;
                set_polarity(row_polarity::MIN);
            }
            m_k.addmul(new_a, upper_bound(j).x); //  k += upper_bound(j).x * new_a;
            push_explanation(column_upper_bound_constraint(j));
        }
        m_t.add_monomial(new_a, j);
        TRACE("gomory_cut_detail_real", tout << "add " << new_a << "*v" << j << ", k: " << m_k << "\n";
              tout << "m_t =  "; lia.lra.print_term(m_t, tout) << "\nk: " << m_k << "\n";);
        
        if (numerator(new_a) > m_big_number)
            m_found_big = true;
    }

    lia_move report_conflict_from_gomory_cut() {
        SASSERT(m_k.is_pos());
        // conflict 0 >= k where k is positive
        return lia_move::conflict;
    }
    

    std::string var_name(unsigned j) const {
        return std::string("x") + std::to_string(j);
    }

    std::ostream& dump_coeff_val(std::ostream & out, const mpq & a) const {
        if (a.is_int()) 
            out << a;
        else if (a >= zero_of_type<mpq>())
            out << "(/ " << numerator(a) << " " << denominator(a) << ")";
        else 
            out << "(- (/ " <<   numerator(-a) << " " << denominator(-a) << "))";
        return out;
    }
    
    template <typename T>
    void dump_coeff(std::ostream & out, const T& c) const {
        dump_coeff_val(out << "(* ", c.coeff()) << " " << var_name(c.j()) << ")";
    }
    
    std::ostream& dump_row_coefficients(std::ostream & out) const {
        mpq lc(1);
        for (const auto& p : m_row) 
            lc = lcm(lc, denominator(p.coeff())); 
        for (const auto& p : m_row) 
            dump_coeff_val(out << " (* ", p.coeff()*lc) << " " << var_name(p.var()) << ")";
        return out;
    }
    
    void dump_the_row(std::ostream& out) const {
        out << "; the row, excluding fixed vars\n";
        out << "(assert (= (+";
        dump_row_coefficients(out) << ") 0))\n";
    }

    void dump_declaration(std::ostream& out, unsigned v) const {
        out << "(declare-const " << var_name(v) << (is_int(v) ? " Int" : " Real") << ")\n";
    }
    
    void dump_declarations(std::ostream& out) const {
        // for a column j the var name is vj
        for (const auto & p : m_row) 
            dump_declaration(out, p.var());
        for (lar_term::ival p : m_t) {
            if (lia.lra.column_has_term(p.j()))
                dump_declaration(out, p.j());            
        }
    }

    void dump_lower_bound_expl(std::ostream & out, unsigned j) const {
        out << "(assert (>= " << var_name(j) << " " << lower_bound(j).x << "))\n";
    }

    void dump_upper_bound_expl(std::ostream & out, unsigned j) const {
        out << "(assert (<= " << var_name(j) << " " << upper_bound(j).x << "))\n";
    }
    
    void dump_explanations(std::ostream& out) const {
        for (const auto & p : m_row) {            
            unsigned j = p.var();
            if (j == m_inf_col || (!is_real(j) && p.coeff().is_int())) 
                continue;
            else if (at_lower(j)) 
                dump_lower_bound_expl(out, j);
            else {
                SASSERT(at_upper(j));
                dump_upper_bound_expl(out, j);
            }
        }
    }

    std::ostream& dump_term_coefficients(std::ostream & out) const {
        for (lar_term::ival p : m_t) 
            dump_coeff(out, p);
        return out;
    }
    
    std::ostream& dump_term_sum(std::ostream & out) const {
        return dump_term_coefficients(out << "(+ ") << ")";
    }
    
    std::ostream& dump_term_ge_k(std::ostream & out) const {
        return dump_term_sum(out << "(>= ") << " " << m_k << ")";
    }

    void dump_the_cut_assert(std::ostream & out) const {
        dump_term_ge_k(out << "(assert (not ") << "))\n";
    }

    void dump_cut_and_constraints_as_smt_lemma(std::ostream& out) const {
        dump_declarations(out);
        dump_the_row(out);
        dump_explanations(out);
        dump_the_cut_assert(out);
        out << "(check-sat)\n";
    }

public:
    void dump(std::ostream& out) {
        out << "applying cut at:\n"; print_linear_combination_indices_only<row_strip<mpq>, mpq>(m_row, out); out << std::endl;
        for (auto & p : m_row) 
            lia.lra.print_column_info(p.var(), out);
        out << "inf_col = " << m_inf_col << std::endl;
    }

    lia_move cut() {
        TRACE("gomory_cut", dump(tout););
        // If m_polarity is MAX, then
        // the row constraints the base variable to be at the maximum,
        // MIN - at the minimum,
        // MIXED : the row does not constraint the base variable to be at an extremum
        // UNDEF is the initial state
        m_polarity = row_polarity::UNDEF; 
        // gomory cut will be  m_t >= m_k and the current solution has a property m_t < m_k
        m_k = 1;
        m_t.clear();
        m_ex->clear();
        m_found_big = false;
        TRACE("gomory_cut_detail", tout << "m_f: " << m_f << ", ";
              tout << "1 - m_f: " << 1 - m_f << ", get_value(m_inf_col).x - m_f = " << get_value(m_inf_col).x - m_f << "\n";);
        SASSERT(m_f.is_pos() && (get_value(m_inf_col).x - m_f).is_int());  
        auto set_polarity_for_int = [&](const mpq & a, lpvar j) {
            if (a.is_pos()) {
                if (at_lower(j))
                    set_polarity(row_polarity::MAX);
                else if (at_upper(j))
                    set_polarity(row_polarity::MIN);
                else 
                    set_polarity(row_polarity::MIXED);
            }
            else {
                if (at_lower(j))
                    set_polarity(row_polarity::MIN);
                else if (at_upper(j))
                    set_polarity(row_polarity::MAX);
                else 
                    set_polarity(row_polarity::MIXED);
            }
        };
          
        
        m_abs_max = 0;
        for (const auto & p : m_row) {
            mpq t = abs(ceil(p.coeff()));
            if (t > m_abs_max)
                m_abs_max = t;
        }
        m_big_number = m_abs_max.expt(2);

        for (const auto & p : m_row) {
            unsigned j = p.var();
            if (j == m_inf_col) continue;
             // use -p.coeff() to make the format compatible with the format used in: Integrating Simplex with DPLL(T)

            if (lia.is_fixed(j)) {
                push_explanation(column_lower_bound_constraint(j));
                push_explanation(column_upper_bound_constraint(j));
                continue;
            }
            if (is_real(j))
                real_case_in_gomory_cut(- p.coeff(), j);
            else {
                if (!p.coeff().is_int()) {
                    m_fj = fractional_part(-p.coeff());
                    m_one_minus_fj = 1 - m_fj;
                    int_case_in_gomory_cut(j);
                }
                if (m_polarity != row_polarity::MIXED) 
                    set_polarity_for_int(p.coeff(), j);
                
            }

            if (m_found_big) {
                return lia_move::undef;
            }
        }

        if (m_t.is_empty()) {
            return report_conflict_from_gomory_cut();
        }
        TRACE("gomory_cut", print_linear_combination_of_column_indices_only(m_t.coeffs_as_vector(), tout << "gomory cut: "); tout << " >= " << m_k << std::endl;);
        
        m_dep = nullptr;
        for (auto c : *m_ex) 
         	m_dep = lia.lra.join_deps(lia.lra.dep_manager().mk_leaf(c.ci()), m_dep);

        TRACE("gomory_cut_detail", dump_cut_and_constraints_as_smt_lemma(tout);
              lia.lra.display(tout));
        SASSERT(lia.current_solution_is_inf_on_cut());
              
        lia.settings().stats().m_gomory_cuts++;
        return lia_move::cut;
    }

    create_cut(lar_term & t, mpq & k, explanation* ex, unsigned basic_inf_int_j, const row_strip<mpq>& row, int_solver& lia) :
        m_t(t),
        m_k(k),
        m_ex(ex),
        m_inf_col(basic_inf_int_j),
        m_row(row),
        lia(lia),
        m_f(fractional_part(get_value(basic_inf_int_j).x)),
        m_one_minus_f(1 - m_f) {}
    
    };

    bool gomory::is_gomory_cut_target(lpvar k) {
        SASSERT(lia.is_base(k));
        const row_strip<mpq>& row = lra.get_row(lia.row_of_basic_column(k));
        // Consider monomial c*x from the row, where x is non-basic.
        // Then, for each such monomial, one of following conditions 
		// has to hold for the row to be eligible for Gomory cut:
        // 1) c is integral and x integral varible with an integral value
        // 2) the value of x is at a bound and has no infinitesimals.

        
        unsigned j;
        for (const auto & p : row) {
            j = p.var();
            if (k == j) continue;
            
            if (p.coeff().is_int() && lia.column_is_int(j) && lia.get_value(j).is_int()) continue;
            
            if ( !lia.at_bound(j) || lia.get_value(j).y != 0) {
                TRACE("gomory_cut", tout << "row is not gomory cut target:\n";
                      lia.display_column(tout, j);
                      tout << "infinitesimal: " << !(lia.get_value(j).y ==0) << "\n";);
                return false;
            }
        }
        return true;

        // Condition 1) above can be relaxed even more, allowing any value for x, but it will change the calculation for m_f.
    }

 // return the minimal distance from the variable value to an integer
    mpq get_gomory_score(const int_solver& lia, lpvar j) {
        const mpq& val = lia.get_value(j).x;
        auto l = val - floor(val);
        if (l <= mpq(1, 2))
            return l;
        return mpq(1) - l;
    }

    unsigned_vector gomory::gomory_select_int_infeasible_vars(unsigned num_cuts) {
        std::list<lpvar> sorted_vars;
        std::unordered_map<lpvar, mpq> score;
        for (lpvar j : lra.r_basis()) {
            if (!lia.column_is_int_inf(j) || !is_gomory_cut_target(j))
                continue;
            SASSERT(!lia.is_fixed(j));            
            sorted_vars.push_back(j);
            score[j] = get_gomory_score(lia, j);
        }
        // prefer the variables with the values close to integers
        sorted_vars.sort([&](lpvar j, lpvar k) {
            auto diff = score[j] - score[k];
            if (diff.is_neg())
                return true;
            if (diff.is_pos())
                return false;
            return lra.usage_in_terms(j) > lra.usage_in_terms(k);
        });
        unsigned_vector ret;
        unsigned n = static_cast<unsigned>(sorted_vars.size());

        while (num_cuts-- && n > 0) {
            unsigned k = lia.settings().random_next() % n;
           
            double k_ratio = k / (double) n;
            k_ratio *= k_ratio*k_ratio;  // square k_ratio to make it smaller
            k = static_cast<unsigned>(std::floor(k_ratio * n));
            // these operations move k to the beginning of the indices range
            SASSERT(0 <= k && k < n);
            auto it = sorted_vars.begin();
            while(k--) it++;

            ret.push_back(*it);
            sorted_vars.erase(it);
            n--;            
        }
        return ret;
    }
    
    row_polarity test_row_polarity(const int_solver& lia, const row_strip<mpq>& row, lpvar basic_j) {
        row_polarity ret = row_polarity::UNDEF;
        for (const auto& p : row) {
            lpvar j = p.var();
            if (j == basic_j)
                continue;
            if (lia.is_fixed(j))
                continue;

            row_polarity rp;
            if (p.coeff().is_pos()) {
                if (lia.at_lower(j))
                    rp = row_polarity::MAX;
                else if (lia.at_upper(j))
                    rp = row_polarity::MIN;
                else 
				    rp = row_polarity::MIXED;
            }
            else {
                if (lia.at_lower(j))
                    rp = row_polarity::MIN;
                else if (lia.at_upper(j))
                    rp = row_polarity::MAX;
                else
                    rp = row_polarity::MIXED;
                    
            }
            if (ret == row_polarity::UNDEF)
                ret = rp;
            if (ret != rp)
                return row_polarity::MIXED;
        }
        return ret;
    }

    u_dependency* gomory::add_deps(u_dependency* dep,  const row_strip<mpq>& row, lpvar basic_var) {
        u_dependency* ret = dep;
        for (const auto& p : row) {
            lpvar j = p.var();
            if (j == basic_var)
                continue;
            if (lia.is_fixed(j))
                continue; 
            if (lia.is_real(j)) continue;
            if (!p.coeff().is_int()) continue;
            // the explanation for all above have been already added
            if (lia.at_lower(j))
                ret = lia.lra.join_deps(lia.column_lower_bound_constraint(j), ret);
            else {
                SASSERT(lia.at_upper(j));
                ret = lia.lra.join_deps(lia.column_upper_bound_constraint(j), ret);
            }
        }
        return ret;
    }

    lia_move gomory::get_gomory_cuts(unsigned num_cuts) {
        struct cut_result {lar_term t; mpq k; u_dependency *dep;};
        vector<cut_result> big_cuts;
        unsigned_vector columns_for_cuts = gomory_select_int_infeasible_vars(num_cuts);
        bool has_small_cut = false;

        // define inline helper functions
        auto is_small_cut = [&](lar_term const& t) {
            return all_of(t, [&](auto ci) { return ci.coeff().is_small(); });
        };
        auto add_cut = [&](const lar_term& t, const mpq& k, u_dependency * dep) {
            lp::lpvar j = lra.add_term(t.coeffs_as_vector(), UINT_MAX);
            lra.update_column_type_and_bound(j, lp::lconstraint_kind::GE,  k, dep); 
        };
        auto _check_feasible = [&](void) {
            lra.find_feasible_solution();
            if (!lra.is_feasible() && !lia.settings().get_cancel_flag()) {
                lra.get_infeasibility_explanation(*(lia.expl()));
                return false;
            }
            return true;
        };

// start creating cuts        
        for (unsigned j : columns_for_cuts) {
            SASSERT(is_gomory_cut_target(j));
            unsigned row_index = lia.row_of_basic_column(j);
            const row_strip<mpq>& row = lra.get_row(row_index);
            create_cut cc(lia.get_term(), lia.offset(), lia.expl(), j, row, lia);
            auto r = cc.cut();
            if (r != lia_move::cut) {
                if (r == lia_move::conflict)
                    return lia_move::conflict;
                continue;
            }
            SASSERT(test_row_polarity(lia, row, j) == cc.m_polarity);
            if (cc.m_polarity == row_polarity::MAX) 
                lra.update_column_type_and_bound(j, lp::lconstraint_kind::LE, floor(lra.get_column_value(j).x), add_deps(cc.m_dep, row, j));
            else if (cc.m_polarity == row_polarity::MIN)
                lra.update_column_type_and_bound(j, lp::lconstraint_kind::GE, ceil(lra.get_column_value(j).x), add_deps(cc.m_dep, row, j));
            
            if (!is_small_cut(lia.get_term())) {
                big_cuts.push_back({cc.m_t, cc.m_k, cc.m_dep});
                continue;
            }
            has_small_cut = true;
            add_cut(cc.m_t, cc.m_k, cc.m_dep);
            if (lia.settings().get_cancel_flag())
                return lia_move::cancelled;
        }

        if (big_cuts.size()) {
            lra.push();        
            for (auto const& cut : big_cuts) 
                add_cut(cut.t, cut.k, cut.dep);
            bool feas = _check_feasible();
            lra.pop(1);

            if (!feas)       
                for (auto const& cut : big_cuts) 
                    add_cut(cut.t, cut.k, cut.dep);
        }
        
        if (!_check_feasible())
            return lia_move::conflict;

        if (lra.get_status() == lp_status::CANCELLED)
            return lia_move::cancelled;        
        
        if (!lra.has_inf_int())
            return lia_move::sat;

        if (has_small_cut || big_cuts.size())
            return lia_move::continue_with_check;
        
        lra.move_non_basic_columns_to_bounds();
        return lia_move::undef;
    }
    
    
    gomory::gomory(int_solver& lia): lia(lia), lra(lia.lra) { }
}
