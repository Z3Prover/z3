/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#include "util/lp/cut_solver.h"
namespace lp {

template <typename T>
lbool cut_solver<T>::check() {
    init_search();
    while (true) {
        TRACE("cs_ch", tout << "inside loop\n";);
        lbool r = bounded_search();
        if (r != lbool::l_undef)
            return r;
        restart();
        simplify_problem();
        if (check_inconsistent()) return lbool::l_false;
        gc();
    }
}

template <typename T>
void cut_solver<T>::init_search() {
    m_changed_vars.resize(m_v.size());
    m_explanation.clear();
}


template <typename T>
void cut_solver<T>::propagate_inequality(unsigned i) {
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
            if (at_base_lvl())
                fill_conflict_explanation(i, m_trail.size());
            TRACE("trace_conflict_int", tout << "conflict explanation\n";
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

template <typename T>
void cut_solver<T>::print_state(std::ostream & out) const {
    out << "ineqs:\n";
    for (const auto & i: m_ineqs) {
        print_ineq(out, i);
    }
    out << "end of ineqs\n";
    out << "trail\n";
    for (const auto & l : m_trail) {
        print_literal(out, l);
        out << "\n";
    }
    out << "end of trail\n";
    out << "var_infos\n";
    for (const auto & v: m_var_infos) {
        print_var_info(out, v);
    }
    out << "end of var_infos\n";
    out << "end of state dump" << std::endl;
}
template <typename T>
lbool cut_solver<T>::bounded_search() {
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

template <typename T>
lbool cut_solver<T>::propagate_and_backjump_step(bool& done) {
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


template <typename T>
void cut_solver<T>::pop(unsigned k) {
    TRACE("trace_push_pop_in_cut_solver", tout << "before pop\n";print_state(tout););
    m_scope.pop(k);
    m_trail.resize(m_scope().m_trail_size);
    pop_ineqs();
    pop_div_constraints();
    pop_var_domains(k);
    m_decision_has_been_made.pop(k);
    TRACE("trace_push_pop_in_cut_solver", tout << "after pop\n";print_state(tout););
}

template <typename T>
void cut_solver<T>::push() {
    TRACE("trace_push_pop_in_cut_solver", print_state(tout););
    m_scope = scope(m_trail.size(), m_ineqs.size(), m_div_constraints.size());
    m_scope.push();
    push_var_domains();
    m_decision_has_been_made.push();
}

template <typename T>
void cut_solver<T>::checkpoint() {
    push();
    // check for cancelation
}

template <typename T>
cut_solver<T>::cut_solver(std::function<std::string (unsigned)> var_name_function,
                          std::function<void (unsigned, std::ostream &)> print_constraint_function
                          ) : m_var_name_function(var_name_function),
                              m_print_constraint_function(print_constraint_function),
                              m_decision_has_been_made(false) {}

template <typename T>
void cut_solver<T>::propagate() {
    propagate_simple_ineqs();
    propagate_ineqs_for_changed_vars();
}

template <typename T>
bool cut_solver<T>::propagate_simple_ineq(unsigned ineq_index) {
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
        if (j >= m_changed_vars.size())
            m_changed_vars.resize(j + 1);
        m_changed_vars.insert(j);
        return true;
    }
        
    TRACE("cut_solver_state", tout <<"no improvement\n";);
    return false;
}
    

template <typename T>
bool cut_solver<T>::propagate_simple_ineqs() {
    bool ret = false;
    for (unsigned i = 0; i < m_ineqs.size(); i++) {
        if (m_ineqs[i].is_simple() && propagate_simple_ineq(i)){
            ret = true;
        }
    }
    return ret;
}

template <typename T>
bool cut_solver<T>::consistent(const ineq & i) const {
    if (find_non_fixed_var() != -1)
        return false; // ignore the variables values and only return true if every variable is fixed
    bool ret = value(i.m_poly) <= zero_of_type<T>();
    if (!ret) {
        TRACE("cut_solver_state_inconsistent", 
              tout << "inconsistent ineq "; print_ineq(tout,i); tout <<"\n";
              tout << "value = " << value(i.m_poly) << '\n';
              );
        }
    return ret;
}

template <typename T>
int cut_solver<T>::find_non_fixed_var() const {
    // it is a very non efficient implementation for now.
    // the current limitation is that we only deal with bounded vars.
    // the search should be randomized.
    for (unsigned j = 0; j < m_var_infos.size(); j++) {
        const auto & d = m_var_infos[j].m_domain;
        lp_assert(d.lower_bound_exists() && d.upper_bound_exists());
        if (!d.is_fixed())
            return j;
    }
    return -1;
}

}
