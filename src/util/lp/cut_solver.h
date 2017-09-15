/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#pragma once
#include "util/vector.h"
#include "util/trace.h"
#include "util/lp/lp_settings.h"
namespace lp {
template <typename T>
class cut_solver {

    struct ineq { // we only have less or equal, which is enough for integral variables
        mpq m_bound;
        vector<std::pair<T, var_index>> m_term;
        ineq(vector<std::pair<T, var_index>>& term, mpq bound):m_bound(bound),m_term(term) {
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

        unsigned m_id;
        unsigned m_index_of_ineq; // index into m_ineqs
        bool m_bool_val; // used if m_tag is equal to BOOL
        mpq m_bound; // used if m_tag is BOUND
        literal(bool sign, bool val):  m_tag(literal_type::BOOL),
            m_bool_val(val){
        } 
        literal(bool sign, unsigned index_of_ineq) : m_tag(literal_type::INEQ), m_index_of_ineq(index_of_ineq) {}
    };

    bool lhs_is_int(const vector<std::pair<mpq, var_index>> & lhs) const {
        for (auto & p : lhs)
            if (p.first.is_int() == false) return false;
        return true;
    }
    
    public:
    void add_ineq(vector<std::pair<mpq, var_index>> & lhs, mpq rhs) {
        lp_assert(lhs_is_int(lhs));
        lp_assert(rhs.is_int());
        m_ineqs.push_back(ineq(lhs, rhs));
    }
        
        
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

    cut_solver() {
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
    
};
}
