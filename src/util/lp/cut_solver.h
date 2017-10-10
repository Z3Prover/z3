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
#include "util/lp/lp_utils.h"
#include <functional>
namespace lp {
template <typename T>
class cut_solver : public column_namer {
public: // for debugging

    struct tight_ineq {
        var_index m_j;
        bool m_le; // less or equal
        T m_b; // the right size
        tight_ineq(var_index j, bool le, const T & b) : m_j(j), m_le(le), m_b(b) {}
        T coeff() const {
            return m_le? one_of_type<T>() : - one_of_type<T>();
        }

    };
    
    struct polynomial {
        // the polynomial evaluates to m_coeffs + m_a
        std::vector<std::pair<T, var_index>> m_coeffs;
        T m_a; // the free coefficient
        polynomial(std::vector<std::pair<T, var_index>>& p, const T & a) : m_coeffs(p), m_a(a) {}
        polynomial(std::vector<std::pair<T, var_index>>& p) : polynomial(p, 0) {}
        polynomial(): m_a(zero_of_type<T>()) {}
        const T & coeff(var_index j) const {
            for (const auto & t : m_coeffs) {
                if (j == t.second) {
                    return t.first;
                }
            }
            return cut_solver::m_local_zero;
        }
        std::vector<std::pair<T, var_index>> copy_coeff_but_one(var_index j) const {
            std::vector<std::pair<T, var_index>> ret;
            for (const auto & t : m_coeffs)
                if (t.second != j)
                    ret.push_back(std::make_pair(t.first, t.second));

            return ret;
        }

        void clear() {
            m_coeffs.clear();
            m_a = zero_of_type<T>();
        }
        
        bool is_zero() const { return m_coeffs.size() == 0 && numeric_traits<T>::is_zero(m_a); }
    };
    
    struct ineq { // we only have less or equal, which is enough for integral variables
        polynomial m_poly;
        ineq(std::vector<std::pair<T, var_index>>& term, const T& a): m_poly(term, a) {
        }
        ineq() {}
        bool contains(var_index j) const {
            return m_poly.contains(j);
        }
        const T & coeff(var_index j) const {
            return m_poly.coeff(j);
        }
        void clear() { m_poly.clear(); }
    };

    std::vector<ineq> m_ineqs;

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

    enum class bound_type {
        LOWER, UPPER, UNDEF
    };
    struct literal {
        literal_type m_tag;
        bool m_sign; // true means the pointed inequality is negated, or bound is negated, or boolean value is negated
        bool m_is_lower;
        unsigned m_id;
        unsigned m_index_of_ineq; // index into m_ineqs
        bool m_bool_val; // used if m_tag is equal to BOOL
        T m_bound; // used if m_tag is BOUND
        literal(bool sign, bool val):  m_tag(literal_type::BOOL),
            m_bool_val(val){
        } 
        literal(bool sign, unsigned index_of_ineq) : m_tag(literal_type::INEQ), m_index_of_ineq(index_of_ineq) {}
    };    

    
    struct bound_result {
        T m_bound;
        bound_type m_type;
        
        bound_result() {}
        bound_result(const T & b, bound_type bt): m_bound(b), m_type(bt) {}
        bound_result(bound_type bt) : m_type(bt) {}
        void print( std::ostream & out) const {
            if (m_type == bound_type::LOWER) {
                out << "lower bound = ";
            }
            else if (m_type == bound_type::UPPER) {
                out << "upper bound = ";
            }
            else {
                out << "undef";
                return;
            }
            out << m_bound;
        }
    };
    
    struct var_info {
        unsigned m_user_var_index;
        var_info(unsigned user_var_index) : m_user_var_index(user_var_index) {}
        std::vector<unsigned> m_literals; // point to m_trail
        integer_domain<T> m_domain;
    };

    std::vector<var_info> m_var_infos;
    
    bool lhs_is_int(const std::vector<std::pair<T, var_index>> & lhs) const {
        for (auto & p : lhs) {
            if (numeric_traits<T>::is_int(p.first) == false) return false;
        }
        return true;
    }
    
    public:
    std::string get_column_name(unsigned j) const {
        return m_var_name_function(m_var_infos[j].m_user_var_index);
    }

    unsigned add_ineq(std::vector<std::pair<T, var_index>> & lhs, const T& free_coeff) {
        lp_assert(lhs_is_int(lhs));
        lp_assert(is_int(free_coeff));
        std::vector<std::pair<T, var_index>>  local_lhs;
        for (auto & p : lhs)
            local_lhs.push_back(std::make_pair(p.first, add_var(p.second)));
        m_ineqs.push_back(ineq(local_lhs, free_coeff));
        return m_ineqs.size() - 1;
    }

    ineq & get_ineq(unsigned i) {
        return m_ineqs[i];
    }
    
    const ineq & get_ineq(unsigned i) const {
        return m_ineqs[i];
    }
    
    std::function<std::string (unsigned)> m_var_name_function;
    bool m_inconsistent;   // tracks if state is consistent
    unsigned m_scope_lvl;  // tracks the number of case splits

    std::vector<literal>          m_trail;
    // backtracking state from the SAT solver:
    struct scope {
        unsigned m_trail_lim;               // pointer into assignment stack
        unsigned m_clauses_to_reinit_lim;   // ignore for now
        bool     m_inconsistent;            // really needed?
    };

    std::vector<scope>          m_scopes;
    std::unordered_map<unsigned, unsigned> m_user_vars_to_cut_solver_vars;
    static T m_local_zero;
    
    unsigned add_var(unsigned user_var_index) {
        unsigned ret;
        if (try_get_value(m_user_vars_to_cut_solver_vars, user_var_index, ret))
            return ret;
        unsigned j = m_var_infos.size();
        m_var_infos.push_back(var_info(user_var_index));
        return m_user_vars_to_cut_solver_vars[user_var_index] = j;      
    }


    bool is_lower_bound(literal & l) const {
        if (l.m_tag != literal_type::BOUND || !l.m_is_lower)
            return false;
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
        if (l.m_tag != literal_type::BOUND || !l.m_is_upper)
            return false;
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

    bool var_lower_bound_exists(var_info i) const {
        const var_info & v = m_var_infos[i];
        return v.m_domain.lower_bound_exists();
    }
    
    bool get_var_lower_bound(var_index i, T & bound) const {
        const var_info & v = m_var_infos[i];
        return v.m_domain.get_lower_bound(bound);
    }

    bool get_var_upper_bound(var_index i, T & bound) const {
        const var_info & v = m_var_infos[i];
        return v.m_domain.get_upper_bound(bound);
    }

    bool lower_monomial_exists(const std::pair<T, var_index> & p) const {
        lp_assert(p.first != 0);

        if (p.first > 0) {
            if (!m_var_infos[p.second].m_domain.lower_bound_exists())
                return false;
        }
        else {
            if (!m_var_infos[p.second].m_domain.upper_bound_exists())
                return false;
        }
        return true;
    }

    bool upper_monomial_exists(const std::pair<T, var_index> & p) const {
        lp_assert(p.first != 0);
        if (p.first > 0) {
            if (!m_var_infos[p.second].m_domain.upper_bound_exists())
                return false;
        }
        else {
            if (!m_var_infos[p.second].m_domain.lower_bound_exists())
                return false;
        }
        return true;
    }

    
    // finds the lower bound of the monomial,
    // otherwise returns false
    bool lower_monomial(const std::pair<T, var_index> & p, T & lb) const {
        lp_assert(p.first != 0);
        T var_bound;
        if (p.first > 0) {
            if (!get_var_lower_bound(p.second, var_bound))
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

    bool upper_monomial(const std::pair<T, var_index> & p, T & lb) const {
        lp_assert(p.first != 0);
        T var_bound;
        if (p.first > 0) {
            if (!get_var_upper_bound(p.second, var_bound))
                return false;
        }
        else {
            if (!get_var_lower_bound(p.second, var_bound))
                return false;
        }
        lb = p.first * var_bound;
        return true;
    }

    
    
    // returns false if not limited from below
    // otherwise the answer is put into lp
    bool lower(const polynomial & f, T & lb) const {
        lb = f.m_a;
        T lm;
        for (const auto & p : f.m_coeffs) {
            if (lower_monomial(p, lm)) {
                lb += lm;
            } else {
                return false;
            }
        }
        return true;
    }


 
    bound_result lower_without(const polynomial & p, var_index j) const {
        bound_result r;
        for (const auto & t:  p.m_coeffs) {
            if (t.second == j)
                continue;
            if (!lower_monomial_exists(t)) {
                r.m_type = bound_type::UNDEF;
                return r;
            }
        }
        // if we are here then there is a lower bound for p
        r.m_bound = p.m_a;
        for (const auto & t:  p.m_coeffs) {
            if (t.second == j)
                continue;

            T l;
            lower_monomial(t, l);
            r.m_bound += l;
        }
        r.m_type = bound_type::LOWER;
        return r;
    }

    bound_result upper_without(const polynomial & p, var_index j) const {
        bound_result r;
        for (const auto & t:  p.m_coeffs) {
            if (t.second == j)
                continue;
            if (!upper_monomial_exists(t)) {
                r.m_type = bound_type::UNDEF;
                return r;
            }
        }
        // if we are here then there is an upper bound for p
        r.m_bound = p.m_a;
        for (const auto & t:  p.m_coeffs) {
            if (t.second == j)
                continue;
            T b;
            upper_monomial(t, b);
            r.m_bound += b;
        }
        r.m_type = bound_type::UPPER;
        return r;
    }

    
    // a is the coefficient before j
    bound_result bound_on_polynomial(const polynomial & p, const T& a, var_index j) const {
        lp_assert(!is_zero(a));
        if (numeric_traits<T>::is_pos(a)) {
            bound_result r = upper_without(p, j);
            if (r.m_type == bound_type::UNDEF)
                return r;
            lp_assert(is_int(r.m_bound));
            r.m_bound = - ceil_ratio(r.m_bound , a);
            r.m_type = bound_type::UPPER;
            return r;
        }
        else {
            bound_result r = lower_without(p, j);
            if (r.m_type == bound_type::UNDEF)
                return r;
            r.m_bound = -floor_ratio(r.m_bound, a);
            r.m_type = bound_type::LOWER;
            return r;
        }
    }
    

    
    bound_result bound(const ineq & q, var_index j) const {
        const T& a = q.m_poly.coeff(j);
        return bound_on_polynomial(q.m_poly, a, j);
    }

    bound_result bound(unsigned ineq_index, var_index j) const {
        return bound(m_ineqs[ineq_index], j);
    }

    
    
    void print_ineq(unsigned i, std::ostream & out) {
        print_ineq(m_ineqs[i], out);
    }

    void print_ineq(const ineq & i, std::ostream & out) {
        print_polynomial(i.m_poly, out);
        out << " <= 0";
    }


    void print_tight_ineq(std::ostream & o, const tight_ineq & t) const {
        o << get_column_name(t.m_j) << " ";
        if (t.m_le)
            o << "<= ";
        else
            o << "=> ";
        o << t.m_b;
    }
    

    
    void print_polynomial(const polynomial & p, std::ostream & out) {
        this->print_linear_combination_of_column_indices_std(p.m_coeffs, out);
        if (!is_zero(p.m_a)) {
            if (p.m_a < 0) {
                out << " - " << -p.m_a;
            } else {
                out << " + " << p.m_a;
            }
        }
    }

    
    //te is an inequality we resove by eliminating varible t.m_j from t
    bool resolve(const tight_ineq & t, const ineq & ie, ineq & result) const {
        lp_assert(result.m_poly.is_zero());
        const T & a = ie.coeff(t.m_j);
        if (t.m_le) {
            if (is_pos(a))
                return false;
        } else { // t.m_le == false
            if (is_neg(a)) 
                return false;
        }
        result.m_poly.m_coeffs = ie.m_poly.copy_coeff_but_one(t.m_j);
        result.m_poly.m_a = a * t.m_b + ie.m_poly.m_a;
        return true;
    }

    // returns true iff p imposes a better bound on j
    bool improves(var_index j, const ineq & p) const {
        auto a = p.coeff(j);
        if (is_zero(a))
            return false;
        const auto& dom = m_var_infos[j].m_domain;
        if (dom.is_empty())
            return false;
        if (is_pos(a)) {
            bound_result new_upper = bound(p, j);
            if (new_upper.m_type == bound_type::UNDEF)
                return false;
            T b;
            bool upper_bound_exists = get_var_upper_bound(j, b);
            return (!upper_bound_exists || new_upper.m_bound < b) &&
                dom.intersection_with_upper_bound_is_empty(new_upper.m_bound);
        }

        lp_assert(is_neg(a));
        bound_result new_lower = bound(p, j);
        if (new_lower.m_type == bound_type::UNDEF)
            return false;
        T b;
        bool lower_bound_exists = get_var_lower_bound(j, b);
        return (!lower_bound_exists || new_lower.m_bound > b) &&
            dom.intersection_with_lower_bound_is_empty(new_lower.m_bound);
        
    }
    
};
}
