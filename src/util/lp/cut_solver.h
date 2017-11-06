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
#include "util/lp/stacked_vector.h"
#include "util/lp/linear_combination_iterator_on_std_vector.h"
namespace lp {
enum
class lbool { l_false, l_true, l_undef };
template <typename T>
class cut_solver : public column_namer {
public: // for debugging
    class monomial {
        T m_coeff; // the coefficient of the monomial
        var_index m_var; // the variable index
    public:
        monomial(const T& coeff, var_index var) : m_coeff(coeff), m_var(var) {}
        // copy constructor
        monomial(const monomial& m) : monomial(m.coeff(), m.var()) {}
        const T & coeff() const { return m_coeff; }
        T & coeff() { return m_coeff; }
        var_index var() const { return m_var; }
        std::pair<T, var_index> to_pair() const { return std::make_pair(coeff(), var());}
    };

    std::vector<std::pair<T, var_index>> to_pairs(const std::vector<monomial>& ms) const {
        std::vector<std::pair<T, var_index>> ret;
        for (const auto p : ms)
            ret.push_back(p.to_pair());
        return ret;
    }
    
    struct polynomial {
        // the polynomial evaluates to m_coeffs + m_a
        std::vector<monomial> m_coeffs;
        T m_a; // the free coefficient
        polynomial(std::vector<monomial>& p, const T & a) : m_coeffs(p), m_a(a) {}
        polynomial(std::vector<monomial>& p) : polynomial(p, 0) {}
        polynomial(): m_a(zero_of_type<T>()) {}
        polynomial(const polynomial & p) : m_coeffs(p.m_coeffs), m_a(p.m_a) {} 
            
        const T & coeff(var_index j) const {
            for (const auto & t : m_coeffs) {
                if (j == t.var()) {
                    return t.coeff();
                }
            }
            return cut_solver::m_local_zero;
        }

        std::vector<monomial> copy_coeff_but_one(var_index j) const {
            std::vector<monomial> ret;
            for (const auto & t : m_coeffs)
                if (t.var() != j)
                    ret.push_back(std::make_pair(t.coeff(), t.var()));

            return ret;
        }

        polynomial &  operator+=(const polynomial & p) {
            m_a += p.m_a;
            for (const auto & t: p.m_coeffs)
                add_monomial(t.first, t.second);
	    return *this;
	}

        void clear() {
            m_coeffs.clear();
            m_a = zero_of_type<T>();
        }
        
        bool is_zero() const { return m_coeffs.size() == 0 && numeric_traits<T>::is_zero(m_a); }

        polynomial & operator+=(const monomial &m ){
            for (unsigned k = 0; k < m_coeffs.size(); k++) {
                auto & l = m_coeffs[k];
                if (m.var() == l.var()) {
                    l.coeff() += m.coeff();
                    if (l.coeff() == 0)
                        m_coeffs.erase(m_coeffs.begin() + k);
                    return *this;
                }
            }
            m_coeffs.push_back(m);
            lp_assert(is_correct());
            return *this;
        }

        bool is_correct() const {
            std::unordered_set<var_index> s;
            for (auto & l : m_coeffs) {
                if (l.coeff() == 0)
                    return false;
                s.insert(l.var());
            }
            return m_coeffs.size() == s.size();
        }
    };
    
    struct ineq { // we only have less or equal, which is enough for integral variables
        polynomial m_poly;
        vector<constraint_index> m_explanation; 
        ineq(std::vector<monomial>& term,
             const T& a,
             const vector<constraint_index> &explanation):
            m_poly(term, a),
            m_explanation(explanation) {
        }
        ineq() {}
        bool contains(var_index j) const {
            return m_poly.contains(j);
        }
        const T & coeff(var_index j) const {
            return m_poly.coeff(j);
        }

        const std::vector<monomial>& coeffs() const { return m_poly.m_coeffs;}
        
        void clear() { m_poly.clear(); }

        bool is_simple() const {
            return m_poly.m_coeffs.size() == 1 &&
                (m_poly.m_coeffs[0].coeff() == one_of_type<T>()
                 || m_poly.m_coeffs[0].coeff() == -one_of_type<T>());
        }

        bool is_tight(unsigned j) const {
            const T & a = m_poly.coeff(j);
            return a == 1 || a == -1;
        }
        void add_monomial(const T & t, var_index j) {
            m_poly += monomial(t, j);
        }
    };

    // copy constructor
    struct div_constraint {
        // m_d divides m_poly
        polynomial m_poly;
        T m_d; 
        vector<unsigned> m_explanation;
        div_constraint(const polynomial & p, const T& d): m_poly(p), m_d(d) {}
        div_constraint() {}
        div_constraint(const div_constraint& d):
            m_poly(d.m_poly),
            m_d(d.m_d),
            m_explanation(d.m_explanation){}
    };
    
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
        // copy constructor
        literal(unsigned var_index, bool is_lower, const T & bound, int ineq_index):
            m_tag(literal_type::BOUND),
            m_sign(true),
            m_var_index(var_index),
            m_is_lower(is_lower),
            m_bound(bound),
            m_tight_explanation_ineq_index(-1),
            m_ineq_index(ineq_index) {
        }
        literal(unsigned var_id, bool is_lower, const T & bound):
            literal(var_id, is_lower, bound, -1) {
        }
        literal() {
            lp_assert(false); // required by std::vector::resize() but should not be called
        }

        literal(const literal & l) :
            m_tag(l.m_tag),
            m_sign(l.m_sign),
            m_var_index(l.m_var_index),
            m_is_lower(l.m_is_lower),
            m_bound(l.m_bound),
            m_tight_explanation_ineq_index(l.m_tight_explanation_ineq_index),
            m_id(l.m_id),
            m_ineq_index(l.m_ineq_index),
            m_bool_val(l.m_bool_val),
            m_index_of_div_constraint(l.m_index_of_div_constraint) { }
        
        bool decided() const { return m_ineq_index < 0; }
    };    

    enum class bound_type {
        LOWER, UPPER, UNDEF
    };
    struct bound_result {
        T m_bound;
        bound_type m_type;
        
        bound_result(const T & b, bound_type bt): m_bound(b), m_type(bt) {}
        bound_result() : m_type(bound_type::UNDEF) {
        }
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
    
    bool lhs_is_int(const std::vector<monomial> & lhs) const {
        for (auto & p : lhs) {
            if (numeric_traits<T>::is_int(p.coeff()) == false) return false;
        }
        return true;
    }
    
    public:
    std::string get_column_name(unsigned j) const {
        return m_var_name_function(m_var_infos[j].m_user_var_index);
    }

    unsigned add_ineq(std::vector<monomial> & lhs,
                      const T& free_coeff,
                      vector<constraint_index> explanation) {
        lp_assert(lhs_is_int(lhs));
        lp_assert(is_int(free_coeff));
        std::vector<monomial>  local_lhs;
        unsigned ineq_index = m_ineqs.size();
        for (auto & p : lhs)
            local_lhs.push_back(monomial(p.coeff(), add_var(p.var())));
        
        m_ineqs.push_back(ineq(local_lhs, free_coeff, explanation));
        TRACE("ba_int",
              tout << "explanation :";
              for (auto i: explanation) {
                  m_print_constraint_function(i, tout);
                  tout << "\n";
              });

        for (auto & p : local_lhs)
            m_var_infos[p.var()].add_dependent_ineq(ineq_index);
        
        return ineq_index;
    }

    ineq & get_ineq(unsigned i) {
        return m_ineqs[i];
    }
    
    const ineq & get_ineq(unsigned i) const {
        return m_ineqs[i];
    }

    std::vector<ineq> m_ineqs;
    std::vector<div_constraint> m_div_constraints;
    
    std::vector<T> m_v; // the values of the variables
    std::function<std::string (unsigned)> m_var_name_function;
    std::function<void (unsigned, std::ostream &)> m_print_constraint_function;
    unsigned m_scope_lvl;  // tracks the number of case splits
    int_set m_changed_vars;
    std::vector<literal>          m_trail;

    struct scope {
        unsigned m_trail_size;
        unsigned m_ineqs_size;
        unsigned m_div_constraints_size;
        scope() {}
        scope(unsigned trail_size,
              unsigned ineqs_size,
              unsigned div_constraints_size) : m_trail_size(trail_size),
                                               m_ineqs_size(ineqs_size),
                                               m_div_constraints_size(div_constraints_size) {}
    };

    stacked_value<scope>          m_scope;
    std::unordered_map<unsigned, unsigned> m_user_vars_to_cut_solver_vars;
    static T m_local_zero;
    std::unordered_set<constraint_index> m_explanation; // if this collection is not empty we have a conflict 

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
        if (conflict())
            return lbool::l_false;
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

    cut_solver(std::function<std::string (unsigned)> var_name_function,
               std::function<void (unsigned, std::ostream &)> print_constraint_function
               ) : m_var_name_function(var_name_function), m_print_constraint_function(print_constraint_function) {
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

    void push_literal_to_trail(const literal & l) {
        unsigned literal_index = m_trail.size();
        m_trail.push_back(l);
        TRACE("ba_int", print_literal(tout, l););
        if (l.m_tag == literal_type::BOUND) {
            m_var_infos[l.m_var_index].m_literals.push_back(literal_index);
        } else {
            lp_assert(false); // not implemented
        }
    }
    
    bool propagate_simple_ineq(unsigned ineq_index) {
        const ineq & t = m_ineqs[ineq_index];
        TRACE("cut_solver_state",   print_ineq(tout, t); tout << std::endl;);
        var_index j = t.m_poly.m_coeffs[0].var();
        
        bound_result br = bound(t, j);
        TRACE("cut_solver_state", tout << "bound result = {"; br.print(tout); tout << "}\n";
              tout << "domain of " << get_column_name(j) << " = "; m_var_infos[j].m_domain.print(tout);
              tout << "\n";
              );
        
        if (improves(j, br)) {
            literal l(j, br.m_type == bound_type::LOWER, br.m_bound, ineq_index);
            l.m_tight_explanation_ineq_index = ineq_index;
            push_literal_to_trail(l);
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
            r = std::max(r, p.var() + 1);
        }
        return r;
    }

    std::string var_name(unsigned j) const {
        return get_column_name(j);
    }

    void trace_print_domain_change(unsigned j, const T& v, const monomial & p, unsigned ineq_index) const {
        tout << "change in domain of " << var_name(j) << ", v = " << v << ", domain becomes ";
        print_var_domain(tout, j);
        T lb;
        bool r = lower(ineq_index, lb);
        if (r)
            tout << "lower_of_ineq = " << lb << "\n";
        else
            tout << "no lower bound for ineq\n";
    }
    
    void propagate_monomial_on_lower(const monomial & p, const T& lower_val, unsigned ineq_index) {
        unsigned j = p.var();
        if (is_pos(p.coeff())) {
            T m;
            get_var_lower_bound(p.var(), m);
            T v = floor(- lower_val / p.coeff()) + m;
            bool change = m_var_infos[j].m_domain.intersect_with_upper_bound(v);
            if (change) {
                TRACE("ba_int", trace_print_domain_change(j, v, p, ineq_index););
                add_bound(v, j, false, ineq_index);
            }
        } else {
            T m;
            get_var_upper_bound(p.var(), m);
            T v = ceil( - lower_val / p.coeff()) + m;
            bool change = m_var_infos[j].m_domain.intersect_with_lower_bound(v);
            if (change) {
                TRACE("ba_int", trace_print_domain_change(j, v, p, ineq_index););
                add_bound(v, j, true , ineq_index);
            }
        }
    }

    void propagate_monomial_on_right_side(const monomial & p, const T& rs, unsigned ineq_index) {
        unsigned j = p.var();
        if (is_pos(p.coeff())) {
            T m;
            T v = floor(rs / p.coeff());
            bool change = m_var_infos[j].m_domain.intersect_with_upper_bound(v);
            if (change) {
                TRACE("ba_int", trace_print_domain_change(j, v, p, ineq_index););
                add_bound(v, j, false, ineq_index);
            }
        } else {
            T v = ceil(rs / p.coeff());
            bool change = m_var_infos[j].m_domain.intersect_with_lower_bound(v);
            if (change) {
                TRACE("ba_int", trace_print_domain_change(j, v, p, ineq_index););
                add_bound(v, j, true , ineq_index);
            }
        }
    }

    
    void print_var_domain(std::ostream & out, unsigned j) const {
        m_var_infos[j].m_domain.print(out);
    }
    
    // b is the value of lower
    void propagate_inequality_on_lower(unsigned i, const T & b) {
        for (const auto & p: m_ineqs[i].coeffs()) {
            propagate_monomial_on_lower(p, b, i);
        }
    }

    unsigned find_lower_bound_literal(bool is_lower, unsigned j, unsigned & upper_end_of_trail) const {
        TRACE("ba_int", tout << get_column_name(j) << "\n"; tout << "literal's size = " << m_var_infos[j].m_literals.size() << "\n";);
        for (unsigned k = m_var_infos[j].m_literals.size(); k--;) {
            unsigned literal_index = m_var_infos[j].m_literals[k];
            if (literal_index >= upper_end_of_trail)
                continue;
            const literal& l = m_trail[literal_index];
            if (l.m_tag == literal_type::BOUND && l.m_var_index == j && l.m_is_lower == is_lower) {
                TRACE("ba_int",
                      tout << "found lower bound expl\n";
                      print_literal(tout, l); tout << "\n";);
                return literal_index;
            }
        }
        lp_assert(false); // unreachable
        return 0;// to avoid the warning
    }

    void add_inequality_explanations(unsigned ineq_index)  {
        for (constraint_index ci : m_ineqs[ineq_index].m_explanation) 
            m_explanation.insert(ci);
    }
    
    void fill_conflict_explanation(unsigned ineq_index, unsigned upper_end_of_trail) {
        // it is a depth search in the DAG of inequalities: the chidlren of an inequalitiy are those inequalities the provide its lower bound
        add_inequality_explanations(ineq_index);
        const ineq& in = m_ineqs[ineq_index];
        TRACE("ba_int", print_ineq(tout, in););
        for (const auto & p: in.coeffs()){
            unsigned literal_index = find_lower_bound_literal(is_pos(p.coeff()), p.var(), upper_end_of_trail);
            unsigned l_ineq_index = m_trail[literal_index].m_ineq_index;
            if (!m_ineqs[l_ineq_index].is_simple()) 
                fill_conflict_explanation(l_ineq_index, literal_index);
        }
    }

    void trace_print_ineq(std::ostream& out, unsigned i) {
        print_ineq(out, i); tout << "\n";
        unsigned j;
        auto pairs = to_pairs(m_ineqs[i].m_poly.m_coeffs);
        auto it = linear_combination_iterator_on_std_vector<T>(pairs);
        while (it.next(j)) {
            out << "domain of " << var_name(j) << " = ";
            print_var_domain(out, j);
        }
    }

   
    void propagate_inequality_only_one_unlim(unsigned ineq_index, unsigned the_only_unlim) {
        const ineq& i = m_ineqs[ineq_index];
        T rs = - i.m_poly.m_a;
        for (unsigned j = 0; j < i.m_poly.m_coeffs.size(); j++) {
            if (j == the_only_unlim) continue;
            T m;
            lower_monomial(i.m_poly.m_coeffs[j], m);
            rs -= m;
        }

        // we cannot get a conflict here because the monomial i.m_poly.m_coeffs[the_only_unlim]
        // is unlimited from below and we are adding an upper bound for it
        propagate_monomial_on_right_side(i.m_poly.m_coeffs[the_only_unlim], rs, ineq_index);
    }
    
    void propagate_inequality(unsigned i) {
        TRACE("ba_int", trace_print_ineq(tout, i););
        const ineq & in = m_ineqs[i];
        if (in.is_simple())
            return;
        // consider a special case for inequalities with just two variables
        unsigned the_only_unlim;
        int r = lower_analize(in, the_only_unlim);
        if (r == 0) {
            T b;
            lower(in.m_poly, b);
            if (is_pos(b)) {
                lp_assert(m_explanation.size() == 0);
                std::unordered_set<unsigned> expl;
                fill_conflict_explanation(i, m_trail.size());
                TRACE("ba_int", tout << "conflict explanation\n";
                      for (auto p : m_explanation) {
                          m_print_constraint_function(p, tout);
                      }
                      );
            } else {
                propagate_inequality_on_lower(i, b);
            }
        } else if (r == 1) {
            propagate_inequality_only_one_unlim(i, the_only_unlim);
        }
    }

    bool conflict() const { return m_explanation.size() > 0; }
    
    void propagate_on_ineqs_of_var(var_index j) {
        for (unsigned i : m_var_infos[j].m_dependent_ineqs) {
            propagate_inequality(i);
            if (conflict())
                return;
        }
    }
    
    void propagate_ineqs_for_changed_vars() {
        TRACE("cut_solver_state", tout << "changed vars size = " << m_changed_vars.size() << "\n";);
        while (!m_changed_vars.is_empty()) {
            unsigned j = m_changed_vars.m_index.back();
            propagate_on_ineqs_of_var(j);
            if (conflict())
                return;
            m_changed_vars.erase(j);
        }
    }
    
    void propagate() {
        propagate_simple_ineqs();
        propagate_ineqs_for_changed_vars();
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

    bool lower_monomial_exists(const monomial & p) const {
        lp_assert(p.coeff() != 0);

        if (p.coeff() > 0) {
            if (!m_var_infos[p.var()].m_domain.lower_bound_exists())
                return false;
        }
        else {
            if (!m_var_infos[p.var()].m_domain.upper_bound_exists())
                return false;
        }
        return true;
    }

    bool upper_monomial_exists(const monomial & p) const {
        lp_assert(p.coeff() != 0);
        if (p.coeff() > 0) {
            if (!m_var_infos[p.var()].m_domain.upper_bound_exists())
                return false;
        }
        else {
            if (!m_var_infos[p.var()].m_domain.lower_bound_exists())
                return false;
        }
        return true;
    }

    
    // finds the lower bound of the monomial,
    // otherwise returns false
    bool lower_monomial(const monomial & p, T & lb) const {
        lp_assert(p.coeff() != 0);
        T var_bound;
        if (p.coeff() > 0) {
            if (!get_var_lower_bound(p.var(), var_bound))
                return false;
            lb = p.coeff() * var_bound;
        }
        else {
            if (!get_var_upper_bound(p.var(), var_bound))
                return false;
            lb = p.coeff() * var_bound;
        }
        return true;
    }

    bool upper_monomial(const monomial & p, T & lb) const {
        lp_assert(p.coeff() != 0);
        T var_bound;
        if (p.coeff() > 0) {
            if (!get_var_upper_bound(p.var(), var_bound))
                return false;
        }
        else {
            if (!get_var_lower_bound(p.var(), var_bound))
                return false;
        }
        lb = p.coeff() * var_bound;
        return true;
    }

    
    
    // returns false if not limited from below
    // otherwise the answer is put into lb
    bool lower(unsigned ineq_index, T & lb) const {
        return lower(m_ineqs[ineq_index].m_poly, lb);
    }

                      // returns false if not limited from below
    // otherwise the answer is put into lb
    T lower_val(unsigned ineq_index) const {
        return lower_val(m_ineqs[ineq_index]);
    }
    
    T lower_val(const ineq & i) const {
        T lb;
#if Z3DEBUG
        bool r =
#endif
        lower(i.m_poly, lb);
        lp_assert(r);
        return lb;
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


     // returns the number of lower unlimited monomials - 0, 1, >=2
    // if there is only one lower unlimited then the index is put into the_only_unlimited
    int lower_analize(const ineq & f, unsigned & the_only_unlimited) const {
        int ret = 0;
        for (unsigned j = 0; j < f.m_poly.m_coeffs.size(); j++) {
            if (!lower_monomial_exists(f.m_poly.m_coeffs[j])) {
                if (ret == 1)
                    return 2;
                ret ++;
                the_only_unlimited = j;
            }
        }
        return ret;
    }


 
    bound_result lower_without(const polynomial & p, var_index j) const {
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;
            if (!lower_monomial_exists(t)) {
                return bound_result();
            }
        }
        // if we are here then there is a lower bound for p
        T bound = p.m_a;
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;

            T l;
            lower_monomial(t, l);
            bound += l;
        }
        return bound_result(bound,bound_type::LOWER);
    }

    bound_result upper_without(const polynomial & p, var_index j) const {
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;
            if (!upper_monomial_exists(t)) {
                return bound_result();
            }
        }
        // if we are here then there is an upper bound for p
        T bound = p.m_a;
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;
            T b;
            upper_monomial(t, b);
            bound += b;
        }
        return bound_result(bound, bound_type::UPPER);
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
        out << " <= 0, explanations = \n";
        for (unsigned j : i.m_explanation) {
            out << "constraint_index = " << j << ":";
            m_print_constraint_function(j, out);
        }
        out << "\n";
       
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
        std::vector<std::pair<T, unsigned>> pairs = to_pairs(p.m_coeffs);
        this->print_linear_combination_of_column_indices_std(pairs, out);
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
        const ineq & tight_i = m_ineqs[t.m_tight_explanation_ineq_index];
        lp_assert(tight_i.is_tight(j));
        result.clear();
        const auto &coeffs = ie.m_poly.m_coeffs;
        // start here !!!!!!!!!!!!!!!!!!!!1
        bool found = false;
        T a;
        for (const auto & c : coeffs) {
            if (c.var() == j) {
                a = c.coeff();
                found = true;
            }
            else {
                result.m_poly.m_coeffs.push_back(c);
            }
        }
        
        if ( !found || (t.m_is_lower == is_neg(a)))
            return false;

        for (auto & c : tight_i.m_poly.m_coeffs) {
            if (c.var() != j)
                result.m_poly += monomial(a * c.coeff(), c.var());
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
        l.m_ineq_index = ineq_index;
        if (m_ineqs[ineq_index].is_tight(j))
            l.m_tight_explanation_ineq_index = ineq_index; // otherwise it remains -1
        
        push_literal_to_trail(l);
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
            ret += t.coeff() * m_v[t.var()];
        return ret;
    }

    void pop(unsigned k) {
        m_scope.pop(k);
        m_trail.resize(m_scope().m_trail_size);
        m_ineqs.resize(m_scope().m_ineqs_size);
        m_div_constraints.resize(m_scope().m_div_constraints_size);
    }

    void push() {
        m_scope = scope(m_trail.size(), m_ineqs.size(), m_div_constraints.size());
        m_scope.push();
    }
};
}
