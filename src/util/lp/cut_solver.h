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
#include "util/lp/int_set.h"
#include "util/lp/linear_combination_iterator_on_std_vector.h"
#include "util/lp/bound_propagator_int.h"
#include "util/lp/bound_analyzer_on_int_ineq.h"
#include "util/lp/stacked_vector.h"

namespace lp {
enum
class lbool { l_false, l_true, l_undef };
template <typename T>
class cut_solver : public column_namer {
public: // for debugging
    struct polynomial {
        // the polynomial evaluates to m_coeffs + m_a
        std::vector<std::pair<T, var_index>> m_coeffs;
        T m_a; // the free coefficient
        polynomial(std::vector<std::pair<T, var_index>>& p, const T & a) : m_coeffs(p), m_a(a) {}
        polynomial(std::vector<std::pair<T, var_index>>& p) : polynomial(p, 0) {}
        polynomial(): m_a(zero_of_type<T>()) {}
        polynomial(const polynomial & p) : m_coeffs(p.m_coeffs), m_a(p.m_a) {} 
            
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

        void add_polynomial(const polynomial & p) {
            m_a += p.m_a;
            for (const auto & t: p.m_coeffs)
                add_monomial(t.first, t.second);
        }

        void clear() {
            m_coeffs.clear();
            m_a = zero_of_type<T>();
        }
        
        bool is_zero() const { return m_coeffs.size() == 0 && numeric_traits<T>::is_zero(m_a); }

        void add_monomial(const T & t, var_index j) {
            for (unsigned k = 0; k < m_coeffs.size(); k++) {
                auto & l = m_coeffs[k];
                if (j == l.second) {
                    l.first += t;
                    if (l.first == 0)
                        m_coeffs.erase(m_coeffs.begin() + k);
                    return;
                }
            }
            m_coeffs.push_back(std::make_pair(t, j));
            lp_assert(is_correct());
        }

        bool is_correct() const {
            std::unordered_set<var_index> s;
            for (auto & l : m_coeffs) {
                if (l.first == 0)
                    return false;
                s.insert(l.second);
            }
            return m_coeffs.size() == s.size();
        }

        linear_combination_iterator_on_std_vector_with_additional_element<T> get_iterator() {
            return linear_combination_iterator_on_std_vector_with_additional_element<T>(m_coeffs);
        }
        
    };
    
    struct ineq { // we only have less or equal, which is enough for integral variables
        polynomial m_poly;
        vector<constraint_index> m_explanation; 
        ineq(std::vector<std::pair<T, var_index>>& term,
             const T& a,
             vector<constraint_index> explanation):
            m_poly(term, a), m_explanation(explanation) {
        }
        ineq() {}
        bool contains(var_index j) const {
            return m_poly.contains(j);
        }
        const T & coeff(var_index j) const {
            return m_poly.coeff(j);
        }
        
        void clear() { m_poly.clear(); }

        bool is_simple() const {
            return m_poly.m_coeffs.size() == 1 &&
                (m_poly.m_coeffs[0].first == one_of_type<T>()
                 || m_poly.m_coeffs[0].first == -one_of_type<T>());
        }

        bool is_tight(unsigned j) const {
            const T & a = m_poly.coeff(j);
            return a == 1 || a == -1;
        }
        void add_monomial(const T & t, var_index j) {
            m_poly.add_monomial(t, j);
        }
    };

    struct div_constraint {
        // m_d divides m_poly
        polynomial m_poly;
        T m_d; 
        div_constraint(const polynomial & p, const T& d): m_poly(p), m_d(d) {
        }
    };
    
    std::vector<ineq> m_ineqs;
    std::vector<div_constraint> m_div_constraints;
    
    enum class literal_type {
        BOOL,INEQ, BOUND, DIV            
    };

    struct literal {
        literal_type m_tag;
        bool m_sign; // true means the pointed inequality is negated, or bound is negated, or boolean value is negated
// these fields are used is m_tag is BOUND        
        unsigned m_var_index;
        bool m_is_lower;
        T m_bound;
        int m_tight_explanation_ineq_index; // points to m_ineqs
//=================
        unsigned m_id;
        int m_ineq_index; // index into m_ineqs, if m_index_of_ineq < 0 then the literal is decided
        bool m_bool_val; // used if m_tag is equal to BOOL
        unsigned m_index_of_div_constraint;
        literal(unsigned var_index, bool is_lower, const T & bound, int ineq_index):
            m_tag(literal_type::BOUND),
            m_var_index(var_index),
            m_is_lower(is_lower),
            m_bound(bound),
            m_tight_explanation_ineq_index(-1),
            m_ineq_index(ineq_index)
        {
        }
        
        literal(unsigned var_id, bool is_lower, const T & bound):
            literal(var_id, is_lower, bound, -1) {
        }
        literal(literal_type tag) : m_tag(tag) {}
        literal(bool sign, bool val):  m_tag(literal_type::BOOL),
            m_bool_val(val){
        } 
        literal(bool sign, unsigned ineq_index) : m_tag(literal_type::INEQ), m_ineq_index(ineq_index) {}
        bool decided() const {
            return m_ineq_index < 0;
        }

    };    

    enum class bound_type {
        LOWER, UPPER, UNDEF
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
        bool is_fixed() const { return m_domain.is_fixed();}
        std::unordered_set<int> m_dependent_ineqs; // the set of inequalities involving the var
        void add_dependent_ineq(unsigned i) {
            m_dependent_ineqs.insert(i);
        }
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

    unsigned add_ineq(std::vector<std::pair<T, var_index>> & lhs,
                      const T& free_coeff,
                      vector<constraint_index> explanation) {
        lp_assert(lhs_is_int(lhs));
        lp_assert(is_int(free_coeff));
        std::vector<std::pair<T, var_index>>  local_lhs;
        unsigned ineq_index = m_ineqs.size();
        for (auto & p : lhs)
            local_lhs.push_back(std::make_pair(p.first, add_var(p.second)));
        
        m_ineqs.push_back(ineq(local_lhs, free_coeff, explanation));

        for (auto & p : local_lhs)
            m_var_infos[p.second].add_dependent_ineq(ineq_index);
        
        return ineq_index;
    }

    ineq & get_ineq(unsigned i) {
        return m_ineqs[i];
    }
    
    const ineq & get_ineq(unsigned i) const {
        return m_ineqs[i];
    }

    std::vector<T> m_v; // the values of the variables
    std::function<std::string (unsigned)> m_var_name_function;
    unsigned m_scope_lvl;  // tracks the number of case splits
    int_set m_changed_vars;
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
    vector<constraint_index> m_explanation; // if this vector has some elements we have a conflict 
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
        if (consistent())
            return lbool::l_true;
        init_search();
        propagate();
        while (true) {
            lbool r = bounded_search();
            if (r != lbool::l_undef)
                return r;
            return r; // temporary fix for debugging
            restart();
            simplify_problem();
            if (check_inconsistent()) return lbool::l_false;
            gc();
        }
    }

    cut_solver(std::function<std::string (unsigned)> var_name_function) : m_var_name_function(var_name_function) {
    }
    
    void init_search() {
        // initialize data-structures
        m_changed_vars.resize(m_v.size());
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
                if (is_sat == lbool::l_undef) // temporary fix for debugging
                    return lbool::l_undef;
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
        return lbool::l_undef; // temporary fix for debugging
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

    void restrict_var_domain_with_bound_result(var_index j, const bound_result & br) {
        if (br.m_type == bound_type::UPPER) {
            m_var_infos[j].m_domain.intersect_with_upper_bound(br.m_bound);
        } else {
            m_var_infos[j].m_domain.intersect_with_lower_bound(br.m_bound);
        }
    }

    bool propagate_simple_ineq(unsigned ineq_index) {
        const ineq & t = m_ineqs[ineq_index];
        TRACE("cut_solver_state",   print_ineq(tout, t); tout << std::endl;);
        var_index j = t.m_poly.m_coeffs[0].second;
        
        bound_result br = bound(t, j);
        TRACE("cut_solver_state", tout << "bound result = {"; br.print(tout); tout << "}\n";
              tout << "domain of " << get_column_name(j) << " = "; m_var_infos[j].m_domain.print(tout);
              tout << "\n";
              );
        
        if (improves(j, br)) {
            literal l(j, br.m_type == bound_type::LOWER, br.m_bound, ineq_index);
            l.m_tight_explanation_ineq_index = ineq_index;
            
            m_trail.push_back(l);
            restrict_var_domain_with_bound_result(j, br);
            TRACE("cut_solver_state", tout <<"improved domain = ";
                  m_var_infos[j].m_domain.print(tout);
                  tout<<"\n";
                  tout << "literal = "; print_literal(tout, l);
                  tout <<"\n";
                  );
            m_changed_vars.insert(j);
            return true;
        }
        
        TRACE("cut_solver_state", tout <<"no improvement\n";);
        return false;
    }
    
        
    bool propagate_simple_ineqs() {
        bool ret = false;
        for (unsigned i = 0; i < m_ineqs.size(); i++) {
            if (m_ineqs[i].is_simple() && propagate_simple_ineq(i)){
               ret = true;
            }
        }
        return ret;
    }

    unsigned find_large_enough_j(unsigned i) {
        unsigned r = 0;
        for (const auto & p : m_ineqs[i].m_poly.m_coeffs) {
            r = std::max(r, p.second + 1);
        }
        return r;
    }
    
    void propagate_inequality(unsigned i) {
        ineq& ie = m_ineqs[i];
        unsigned slack_var_for_ineq = find_large_enough_j(i);
        bound_propagator_int<T> bp(*this, slack_var_for_ineq);
        
        linear_combination_iterator_on_std_vector_with_additional_element<T> it(ie.m_poly.m_coeffs, slack_var_for_ineq);
        
        bound_analyzer_on_int_ineq<T>::analyze(
            it,
            -ie.m_poly.m_a,
            i,
            bp);
    }
    
    void propagate_on_ineqs_of_var(var_index j) {
        for (unsigned i : m_var_infos[j].m_dependent_ineqs)
            propagate_inequality(i); 
    }
    
    void propagate_ineqs_for_changed_var() {
        TRACE("cut_solver_state", tout << "changed vars size = " << m_changed_vars.size() << "\n";);
        while (!m_changed_vars.is_empty()) {
            unsigned j = m_changed_vars.m_index.back();
            propagate_on_ineqs_of_var(j);
            m_changed_vars.erase(j);
        }
    }
    
    void propagate() {
        propagate_simple_ineqs();
        propagate_ineqs_for_changed_var();
    }

    bool decide() {
        // this is where the main action is.
        // pick the next variable and bound or value on the variable.
        // return false if all variables have been assigned.
        return false;
    }

    bool inconsistent() const {
        return !consistent();
    }

    bool consistent() const {
        for (const auto & i : m_ineqs) {
            if (!consistent(i))
                return false;
        }

        return true;
    }
    
    bool consistent(const ineq & i) const {
        bool ret = value(i.m_poly) <= zero_of_type<T>();
        if (!ret) {
            TRACE("cut_solver_state", 
                  tout << "inconsistent ineq "; print_ineq(tout,i); tout <<"\n";
                  tout << "value = " << value(i.m_poly) << '\n';
                  );
        }
        return ret;
    }
    
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
    // otherwise the answer is put into lb
    bool lower(unsigned ineq_index, T & lb) const {
        return lower(m_ineqs[ineq_index].m_poly, lb);
    }

        
    // returns false if not limited from below
    // otherwise the answer is put into lb
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

    bool upper(const polynomial & p, T b) const {
        for (const auto & t:  p.m_coeffs) {
            if (!upper_monomial_exists(t)) {
                return false;
            }
        }
        // if we are here then there is an upper bound for p
        b = p.m_a;
        T bb;
        for (const auto & t:  p.m_coeffs) {
            upper_monomial(t, bb);
            b += bb;
        }
        return true;
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


    void print_state(std::ostream & out) const {
        out << "ineqs:\n";
        for (const auto & i: m_ineqs) {
            print_ineq(out, i);
            out << "\n";
        }
        out << "end of ineqs\n";
        out << "var values\n";
        for (unsigned j = 0; j < m_v.size(); j++) {
            out << get_column_name(j) << " = " << m_v[j] << "\n";
        }
        out << "end of var values\n";
        out << "trail\n";
        for (const auto & l : m_trail) {
            print_literal(out, l);
            out << "\n";
        }
        out << "end of trail\n";
        out << "end of state dump" << std::endl;
    }
    
    void print_ineq(std::ostream & out, unsigned i)  const {
        print_ineq(out, m_ineqs[i]);
    }

    void print_ineq(std::ostream & out, const ineq & i ) const {
        print_polynomial(out, i.m_poly);
        out << " <= 0";
    }

    void print_literal_bound(std::ostream & o, const literal & t) const {
        o << "BOUND: ";
        o << get_column_name(t.m_var_index) << " ";
        if (t.m_is_lower)
            o << ">= ";
        else
            o << "<= ";
        o << t.m_bound;
        if (t.m_tight_explanation_ineq_index >= 0) {
            o << "  tight ineq ";
            print_ineq(o, t.m_tight_explanation_ineq_index);
        }
        if (t.m_ineq_index >= 0) {
            o << "  ineq ";
            print_ineq(o, t.m_ineq_index);
        }
    }

    void print_literal(std::ostream & o, const literal & t) const {
        if (t.m_tag == literal_type::BOUND)
            print_literal_bound(o, t);
        else {
            lp_assert(false);
        }
    }
    

    
    void print_polynomial(std::ostream & out, const polynomial & p) const {
        this->print_linear_combination_of_column_indices_std(p.m_coeffs, out);
        if (!is_zero(p.m_a)) {
            if (p.m_a < 0) {
                out << " - " << -p.m_a;
            } else {
                out << " + " << p.m_a;
            }
        }
    }

    // trying to improve inequality ie by using literal t, and eliminate the literal variable.
    // the literal has to be a BOUND and has to point out to a tight inequality for the bounded variable
    bool resolve(const literal & t, const ineq & ie, ineq & result) const {
        lp_assert(literal_is_correct(t));
        lp_assert(t.m_tag == literal_type::BOUND);
        lp_assert(t.m_ineq_index >= 0); // ! t.decided()
        var_index j = t.m_var_index;
        const ineq & tight_i = m_ineqs[t.m_ineq_index];
        lp_assert(tight_i.is_tight(j));
        result.clear();
        auto coeffs = ie.m_poly.m_coeffs;
        int k = -1; // the position of t.m_var_index in coeffs
        T a;
        for (unsigned i = 0; i < coeffs.size(); i++) {
            if (coeffs[i].second == j) {
                k = i;
                a = coeffs[i].first;
            } else {
                result.m_poly.m_coeffs.push_back(coeffs[i]);
            }
        }
        
        if (k == -1)
            return false;

        a = coeffs[k].first;
        if (t.m_is_lower) {
            if (is_neg(a))
                return false;
        } else { // t.m_lower == false
            if (is_pos(a)) 
                return false;
        }

        for (auto & c : tight_i.m_poly.m_coeffs) {
            if (c.second != j)
                result.add_monomial( a * c.first, c.second);
        }
        result.m_poly.m_a = ie.m_poly.m_a + a * tight_i.m_poly.m_a;
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


       // returns true iff br imposes a better bound on j
    bool improves(var_index j, const bound_result & br) const {
        if (br.m_type == bound_type::UNDEF)
            return false;
        const auto& dom = m_var_infos[j].m_domain;
        if (dom.is_empty())
            return false;
        if (br.m_type == bound_type::UPPER) {
            T b;
            bool j_has_upper_bound = get_var_upper_bound(j, b);
            return (!j_has_upper_bound || br.m_bound < b) &&
               !dom.intersection_with_upper_bound_is_empty(br.m_bound);
        }

        if (br.m_type == bound_type::UNDEF)
            return false;
        T b;
        bool lower_bound_exists = get_var_lower_bound(j, b);
        return (!lower_bound_exists || br.m_bound > b) &&
            !dom.intersection_with_lower_bound_is_empty(br.m_bound);
    }


    void add_bound(T v, unsigned j, bool is_lower, unsigned ineq_index) {
        literal l(j, is_lower, v);
        if (m_ineqs[ineq_index].is_tight(j))
            l.m_tight_explanation_ineq_index = ineq_index;
        else
            l.m_ineq_index = ineq_index;
        m_trail.push_back(l);
    }
    
    bool literal_is_correct(const literal &t ) const {
        if (t.m_tag == literal_type::BOUND) {
            if (t.decided())
                return true;
            auto & i = m_ineqs[t.m_ineq_index];
            int sign_should_be = t.m_is_lower? -1: 1;
            const T &a = i.coeff(t.m_var_index);
            int sign = a > 0? 1: -1;
            return sign == sign_should_be;
        }
        return true;
    }

    T value(const polynomial & p) const {
        T ret= p.m_a;
        for (const auto & t:p.m_coeffs)
            ret += t.first * m_v[t.second];
        return ret;
    }
};
}
