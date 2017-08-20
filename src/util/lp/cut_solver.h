/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#pragma once
#include "util/vector.h"
#include "util/trace.h"
#include "util/lp/lp_settings.h"
#include "util/lp/column_namer.h"
#include "util/lp/integer_domain.h"
#include <functional>
namespace lp {
template <typename T>
class cut_solver : public column_namer {
public: // for debugging
    struct polynomial {
        // the polynom evaluates to m_term + m_a
        vector<std::pair<T, var_index>> m_term;
        mpq m_a; // the free coefficient
        polynomial(vector<std::pair<T, var_index>>& p, const mpq & a) : m_term(p), m_a(a) {
        }
        polynomial(vector<std::pair<T, var_index>>& p) : polynomial(p, 0) {
        }
        
    };
    
    struct ineq { // we only have less or equal, which is enough for integral variables
        polynomial m_poly;
        ineq(vector<std::pair<T, var_index>>& term, const mpq& a): m_poly(term, a) {
        }
    };

    vector<ineq> m_ineqs;

    enum class lbool {
        l_false, // false
        l_true, // true
        l_undef  // undef
    };
    
    enum class literal_type {
        BOOL,
        INEQ,
        BOUND
    };

    struct literal {
        literal_type m_tag;
        bool m_sign; // true means the pointed inequality is negated, or bound is negated, or boolean value is negated
        bool m_is_lower;
        unsigned m_id;
        unsigned m_index_of_ineq; // index into m_ineqs
        bool m_bool_val; // used if m_tag is equal to BOOL
        mpq m_bound; // used if m_tag is BOUND
        literal(bool sign, bool val):  m_tag(literal_type::BOOL),
            m_bool_val(val){
        } 
        literal(bool sign, unsigned index_of_ineq) : m_tag(literal_type::INEQ), m_index_of_ineq(index_of_ineq) {}
    };    

    struct var_info {
        unsigned m_user_var_index;
        var_info(unsigned user_var_index) : m_user_var_index(user_var_index) {}
        vector<unsigned> m_literals; // point to m_trail
        integer_domain<T> m_domain;
    };

    vector<var_info> m_var_infos;
    
    bool lhs_is_int(const vector<std::pair<T, var_index>> & lhs) const {
        for (auto & p : lhs) {
            if (numeric_traits<T>::is_int(p.first) == false) return false;
        }
        return true;
    }
    
    public:
    std::string get_column_name(unsigned j) const {
        return m_var_name_function(m_var_infos[j].m_user_var_index);
    }

    unsigned add_ineq(vector<std::pair<T, var_index>> & lhs, const mpq& free_coeff) {
        lp_assert(lhs_is_int(lhs));
        lp_assert(free_coeff.is_int());
        vector<std::pair<T, var_index>>  local_lhs;
        for (auto & p : lhs)
            local_lhs.push_back(std::make_pair(p.first, add_var(p.second)));
        m_ineqs.push_back(ineq(local_lhs, free_coeff));
        return m_ineqs.size() - 1;
    }
        
    std::function<std::string (unsigned)> m_var_name_function;
    bool m_inconsistent;   // tracks if state is consistent
    unsigned m_scope_lvl;  // tracks the number of case splits

    svector<literal>          m_trail;
    // backtracking state from the SAT solver:
    struct scope {
        unsigned m_trail_lim;               // pointer into assignment stack
        unsigned m_clauses_to_reinit_lim;   // ignore for now
        bool     m_inconsistent;            // really needed?
    };

    svector<scope>          m_scopes;
    std::unordered_map<unsigned, unsigned> m_user_vars_to_cut_solver_vars;
    unsigned add_var(unsigned user_var_index) {
        unsigned ret;
        if (try_get_value(m_user_vars_to_cut_solver_vars, user_var_index, ret))
            return ret;
        unsigned j = m_var_infos.size();
        m_var_infos.push_back(var_info(user_var_index));
        return m_user_vars_to_cut_solver_vars[user_var_index] = j;      
    }


    bool is_lower_bound(literal & l) const {
        if (l.m_tag != literal_type::BOUND || l.m_is_lower)
            return false;
        l = l.m_bound;
        return true;
    }
    
    bool lower_for_var(unsigned j, T & lower) const {
        bool ret = false;
        for (unsigned i : m_var_infos[j].m_literals)
            if (is_lower_bound(m_trail[i])) {
                if (ret == false) {
                    ret = true;
                    lower = get_bound(m_trail[i]);
                } else {
                    lower = std::max(lower, get_bound(m_trail[i]));
                }
            }
        return ret;
    }

    bool is_upper_bound(literal & l) const {
        if (l.m_tag != literal_type::BOUND || l.m_is_upper)
            return false;
        l = l.m_bound;
        return true;
    }
    
    bool upper_for_var(unsigned j, T & upper) const {
        bool ret = false;
        for (unsigned i : m_var_infos[j].m_literals)
            if (is_upper_bound(m_trail[i])) {
                if (ret == false) {
                    ret = true;
                    upper = get_bound(m_trail[i]);
                } else {
                    upper = std::min(upper, get_bound(m_trail[i]));
                }
            }
        return ret;
    }

    // used for testing only
    void add_lower_bound_for_user_var(unsigned user_var_index, const T& bound) {
        unsigned j = m_user_vars_to_cut_solver_vars[user_var_index];
        auto & vi = m_var_infos[j];
        vi.m_domain.intersect_with_lower_bound(bound);
    }

    // used for testing only
    void add_upper_bound_for_user_var(unsigned user_var_index, const T& bound) {
        unsigned j = m_user_vars_to_cut_solver_vars[user_var_index];
        auto & vi = m_var_infos[j];
        vi.m_domain.intersect_with_upper_bound(bound);
    }

    
    bool  at_base_lvl() const { return m_scope_lvl == 0; }

    lbool check() {
        init_search();
        propagate();
        while (true) {
            lbool r = bounded_search();
            if (r != lbool::l_undef)
                return r;

            restart();
            simplify_problem();
            if (check_inconsistent()) return lbool::l_false;
            gc();
        }
    }

    cut_solver(std::function<std::string (unsigned)> var_name_function) : m_var_name_function(var_name_function) {
    }
    
    void init_search() {
        // TBD
        // initialize data-structures
    }

    void simplify_problem() {
        // no-op
    }

    void gc() {
        // no-op
    }

    void restart() {
        // no-op for now
    }

    bool check_inconsistent() {
        // TBD
        return false;
    }

    lbool bounded_search() {
        while (true) {
            checkpoint();
            bool done = false;
            while (!done) {
                lbool is_sat = propagate_and_backjump_step(done);
                if (is_sat != lbool::l_true) return is_sat;
            }

            gc();

            if (!decide()) {
                lbool is_sat = final_check();
                if (is_sat != lbool::l_undef) {
                    return is_sat;
                }
            }
        }
    }

    void checkpoint() {
        // check for cancelation
    }

    void cleanup() {
    }

    lbool propagate_and_backjump_step(bool& done) {
        done = true;
        propagate();
        if (!inconsistent())
            return lbool::l_true;
        if (!resolve_conflict())
            return lbool::l_false;
        if (at_base_lvl()) {
            cleanup(); // cleaner may propagate frozen clauses
            if (inconsistent()) {
                TRACE("sat", tout << "conflict at level 0\n";);
                return lbool::l_false;
            }
            gc();
        }
        done = false;
        return lbool::l_true;
    }

    lbool final_check() {
        // there are no more case splits, and all clauses are satisfied.
        // prepare the model for external consumption.
        return lbool::l_true;
    }
    

    bool resolve_conflict() {
        while (true) {
            bool r = resolve_conflict_core();
            // after pop, clauses are reinitialized, 
            // this may trigger another conflict.
            if (!r)
                return false;
            if (!inconsistent())
                return true;
        }
    }

    bool resolve_conflict_core() {
        // this is where the main action is.
        return true;
    }

    void propagate() {
        // this is where the main action is.
    }

    bool decide() {
        // this is where the main action is.
        // pick the next variable and bound or value on the variable.
        // return false if all variables have been assigned.
        return false;
    }

    bool inconsistent() const { return m_inconsistent; }

    bool get_var_low_bound(var_index i, T & bound) const {
        const var_info & v = m_var_infos[i];
        return v.m_domain.get_lower_bound(bound);
    }

    bool get_var_upper_bound(var_index i, T & bound) const {
        const var_info & v = m_var_infos[i];
        return v.m_domain.get_upper_bound(bound);
    }

    
    // finds the lower bound of the monomial,
    // otherwise returns false
    bool lower_monomial(const std::pair<T, var_index> & p, mpq & lb) const {
        lp_assert(p.first != 0);
        T var_bound;
        if (p.first > 0) {
            if (!get_var_low_bound(p.second, var_bound))
                return false;
            lb = p.first * var_bound;
        }
        else {
            if (!get_var_upper_bound(p.second, var_bound))
                return false;
            lb = p.first * var_bound;
        }
        return true;
    }
    
    // returns false if not limited from below
    // otherwise the answer is put into lp
    bool lower(const polynomial & f, mpq & lb) const {
        lb = 0;
        mpq lm;
        for (const auto & p : f.m_term) {
            if (lower_monomial(p, lm)) {
                lb += lm;
            } else {
                return false;
            }
        }
        lb += f.m_a;
        return true;
    }

    void print_ineq(unsigned i, std::ostream & out) {
        print_polynomial(m_ineqs[i].m_poly, out);
        out << " <= 0" << std::endl;
    }

    void print_polynomial(const polynomial & p, std::ostream & out) {
        this->print_linear_combination_of_column_indices(p.m_term, out);
        if (!is_zero(p.m_a)) {
            if (p.m_a < 0) {
                out << " - " << -p.m_a;
            } else {
                out << " + " << p.m_a;
            }
        }
    }
};
}
