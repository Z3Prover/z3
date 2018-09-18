namespace lp {
#include "util/lp/lp_utils.h"
struct gomory_test {
    gomory_test(
        std::function<std::string (unsigned)> name_function_p,
        std::function<mpq (unsigned)> get_value_p,
        std::function<bool (unsigned)> at_low_p,
        std::function<bool (unsigned)> at_upper_p,
        std::function<impq (unsigned) > lower_bound_p,
        std::function<impq (unsigned) > upper_bound_p,
        std::function<unsigned (unsigned) > column_lower_bound_constraint_p,
        std::function<unsigned (unsigned) > column_upper_bound_constraint_p
                ) :
        m_name_function(name_function_p),
        get_value(get_value_p),
        at_low(at_low_p),
        at_upper(at_upper_p),
        lower_bound(lower_bound_p),
        upper_bound(upper_bound_p),
        column_lower_bound_constraint(column_lower_bound_constraint_p),
        column_upper_bound_constraint(column_upper_bound_constraint_p)
    {}

    std::function<std::string (unsigned)> m_name_function;
    std::function<mpq (unsigned)> get_value;
    std::function<bool (unsigned)> at_low;
    std::function<bool (unsigned)> at_upper;
    std::function<impq (unsigned) > lower_bound;
    std::function<impq (unsigned) > upper_bound;
    std::function<unsigned (unsigned) > column_lower_bound_constraint;
    std::function<unsigned (unsigned) > column_upper_bound_constraint;
    
    bool is_real(unsigned) { return false; } // todo: test real case
    void print_row(std::ostream& out, vector<std::pair<mpq, unsigned>> & row ) {
        bool first = true;
        for (const auto & it : row) {
            auto val = it.first;
            if (first) {
                first = false;
            } else {
                if (numeric_traits<mpq>::is_pos(val)) {
                    out << " + ";
                } else {
                    out << " - ";
                    val = -val;
                }
            }
            if (val == -numeric_traits<mpq>::one())
                out << " - ";
            else if (val != numeric_traits<mpq>::one())
                out << T_to_string(val);
        
            out << m_name_function(it.second);
        }
    }

    void real_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term& pol, explanation & expl, const mpq& f_0, const mpq& one_minus_f_0) {
        TRACE("gomory_cut_detail_real", tout << "real\n";);
        mpq new_a;
        if (at_low(x_j)) {
            if (a.is_pos()) {
                new_a  =  a / (1 - f_0);
            }
            else {
                new_a  =  a / f_0;
                new_a.neg();
            }
            k.addmul(new_a, lower_bound(x_j).x); // is it a faster operation than
            // k += lower_bound(x_j).x * new_a;  
            expl.push_justification(column_lower_bound_constraint(x_j), new_a);
        }
        else {
            lp_assert(at_upper(x_j));
            if (a.is_pos()) {
                new_a =   a / f_0; 
                new_a.neg(); // the upper terms are inverted.
            }
            else {
                new_a =   a / (mpq(1) - f_0); 
            }
            k.addmul(new_a, upper_bound(x_j).x); //  k += upper_bound(x_j).x * new_a; 
            expl.push_justification(column_upper_bound_constraint(x_j), new_a);
        }
        TRACE("gomory_cut_detail_real", tout << a << "*v" << x_j << " k: " << k << "\n";);
        pol.add_monomial(new_a, x_j);
    }
    
    void int_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term & t, explanation& expl, mpq & lcm_den, const mpq& f_0, const mpq& one_minus_f_0) {
        lp_assert(is_int(x_j));
        lp_assert(!a.is_int());
             lp_assert(f_0 > zero_of_type<mpq>() && f_0 < one_of_type<mpq>());
        mpq f_j =  fractional_part(a);
        TRACE("gomory_cut_detail", 
              tout << a << " x_j = " << x_j << ", k = " << k << "\n";
              tout << "f_j: " << f_j << "\n";
              tout << "f_0: " << f_0 << "\n";
              tout << "1 - f_0: " << one_minus_f_0 << "\n";
              tout << "at_low(" << x_j << ") = " << at_low(x_j) << std::endl;
              );
        lp_assert (!f_j.is_zero());
        mpq new_a;
        if (at_low(x_j)) {
            if (f_j <= one_minus_f_0) {
                new_a = f_j / one_minus_f_0;
            }
            else {
                new_a = (1 - f_j) / f_0;
            }
            k.addmul(new_a, lower_bound(x_j).x);
            expl.push_justification(column_lower_bound_constraint(x_j), new_a);
        }
        else {
            lp_assert(at_upper(x_j));
            if (f_j <= f_0) {
                new_a = f_j / f_0;
            }
            else {
                new_a = (mpq(1) - f_j) / (one_minus_f_0);
            }
            new_a.neg(); // the upper terms are inverted
            k.addmul(new_a, upper_bound(x_j).x);
            expl.push_justification(column_upper_bound_constraint(x_j), new_a);
        }
        TRACE("gomory_cut_detail", tout << "new_a: " << new_a << " k: " << k << "\n";);
        t.add_monomial(new_a, x_j);
        lcm_den = lcm(lcm_den, denominator(new_a));
    }


    void report_conflict_from_gomory_cut(mpq &k) {
        lp_assert(false);
    }

    void adjust_term_and_k_for_some_ints_case_gomory(lar_term& t, mpq& k, mpq &lcm_den) {
        lp_assert(!t.is_empty());
        auto pol = t.coeffs_as_vector();
        t.clear();
        if (pol.size() == 1) {
            TRACE("gomory_cut_detail", tout << "pol.size() is 1" << std::endl;);
            unsigned v = pol[0].second;
            lp_assert(is_int(v));
            const mpq& a = pol[0].first;
            k /= a;
            if (a.is_pos()) { // we have av >= k
                if (!k.is_int())
                    k = ceil(k);
                // switch size
                t.add_monomial(- mpq(1), v);
                k.neg();
            } else {
                if (!k.is_int())
                    k = floor(k);
                t.add_monomial(mpq(1), v);
            }
        } else {
            TRACE("gomory_cut_detail", tout << "pol.size() > 1" << std::endl;);
            lcm_den = lcm(lcm_den, denominator(k));
            TRACE("gomory_cut_detail", tout << "k: " << k << " lcm_den: " << lcm_den << "\n";
                  for (unsigned i = 0; i < pol.size(); i++) {
                      tout << pol[i].first << " " << pol[i].second << "\n";
                  }
                  tout << "k: " << k << "\n";);
            lp_assert(lcm_den.is_pos());
            if (!lcm_den.is_one()) {
                // normalize coefficients of integer parameters to be integers.
                for (auto & pi: pol) {
                    pi.first *= lcm_den;
                    SASSERT(!is_int(pi.second) || pi.first.is_int());
                }
                k *= lcm_den;
            }
            TRACE("gomory_cut_detail", tout << "after *lcm\n";
                  for (unsigned i = 0; i < pol.size(); i++) {
                      tout << pol[i].first << " * v" << pol[i].second << "\n";
                  }
                  tout << "k: " << k << "\n";);
            
            // negate everything to return -pol <= -k
            for (const auto & pi: pol)
                t.add_monomial(-pi.first, pi.second);
            k.neg();
        }
        TRACE("gomory_cut_detail", tout << "k = " << k << std::endl;);
        lp_assert(k.is_int());
    }

    void print_term(lar_term & t, std::ostream & out) {
        lp_assert(is_zero(t.m_v));
        vector<std::pair<mpq, unsigned>>  row;
        for (auto p : t.m_coeffs)
            row.push_back(std::make_pair(p.second, p.first));
        print_row(out, row);
    }
    
    void mk_gomory_cut(lar_term& t, mpq& k, explanation & expl, unsigned inf_col, vector<std::pair<mpq, unsigned>> & row) {
        enable_trace("gomory_cut");
        enable_trace("gomory_cut_detail");

        TRACE("gomory_cut",
              tout << "applying cut at:\n"; print_row(tout, row); 
              tout << std::endl << "inf_col = " << inf_col << std::endl;
              );
        
        // gomory will be   t >= k
        k = 1;
        mpq lcm_den(1);
        unsigned x_j;
        mpq a;
        bool some_int_columns = false;
        mpq f_0  = fractional_part(get_value(inf_col));
        mpq one_min_f_0 = 1 - f_0;
        for ( auto pp : row) {
            a = pp.first;
            x_j = pp.second;
            if (x_j == inf_col)
                continue;
            // make the format compatible with the format used in: Integrating Simplex with DPLL(T)
            a.neg();  
            if (is_real(x_j)) 
                real_case_in_gomory_cut(a, x_j, k, t, expl, f_0, one_min_f_0);
            else {
                if (a.is_int()) continue; // f_j will be zero and no monomial will be added
                some_int_columns = true;
                int_case_in_gomory_cut(a, x_j, k, t, expl, lcm_den, f_0, one_min_f_0);
            }
        }

        if (t.is_empty())
            return report_conflict_from_gomory_cut(k);
        if (some_int_columns)
            adjust_term_and_k_for_some_ints_case_gomory(t, k, lcm_den);

        TRACE("gomory_cut", tout<<"new cut :"; print_term(t, tout); tout << " >= " << k << std::endl;);

    }
};
}
