/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bound_propagator.h

Abstract:

    Bound propagators for arithmetic.
    Support class for implementing strategies and search procedures

Author:

    Leonardo de Moura (leonardo) 2011-06-18.

Revision History:

--*/
#ifndef _BOUND_PROPAGATOR_H_
#define _BOUND_PROPAGATOR_H_

#include"mpq.h"
#include"vector.h"
#include"params.h"
#include"statistics.h"
#include"numeral_buffer.h"
#include"linear_equation.h"

class bound_propagator {
public:
    typedef unsigned var;
    typedef unsigned assumption;
    typedef unsynch_mpq_manager numeral_manager;
    typedef unsigned_vector assumption_vector;
    typedef unsigned constraint_id;
    typedef numeral_buffer<mpz, numeral_manager> mpz_buffer;
    typedef svector<double> double_vector;
    static const assumption null_assumption = UINT_MAX;
    static const var null_var = UINT_MAX;
    static const unsigned null_constraint_idx = UINT_MAX;
    class trail_info {
        unsigned m_x_lower;
    public:
        trail_info(var x, bool is_lower):m_x_lower((x << 1) + static_cast<unsigned>(is_lower)) {}
        trail_info():m_x_lower(UINT_MAX) {}
        var x() const { return m_x_lower >> 1; }
        bool is_lower() const { return (m_x_lower & 1) != 0; }
    };

protected:

    enum ckind { LINEAR  // only linear equalities so far.
    };

    /**
       \brief Constraints don't need justification.
    */
    class constraint {
        friend class bound_propagator;
        unsigned     m_kind:2;
        unsigned     m_dead:1;
        unsigned     m_timestamp; // Constraint tried to propagate new bounds using bounds with timestamp < m_timestamp.
        unsigned     m_act;       // activity
        unsigned     m_counter;   // number of times the constraint propagated
        union {
            linear_equation * m_eq;
        };
    };

    enum bkind { AXIOM,      // doesn't need justification
                 ASSUMPTION, // aka external case-split, it is used to connect with external search engine.
                 DERIVED,    // implied
                 DECISION    // internal case-split
    };
                
    struct bound {
        mpq        m_k;
        double     m_approx_k;
        unsigned   m_lower:1;
        unsigned   m_strict:1;
        unsigned   m_mark:1;
        unsigned   m_kind:2;
        unsigned   m_level:27;
        unsigned   m_timestamp;
        union {
            assumption   m_assumption;
            unsigned     m_constraint_idx;
        };
        bound *      m_prev;
        bound(numeral_manager & m, mpq const & k, double approx_k, bool lower, bool strict, unsigned lvl, unsigned ts, bkind bk, 
              unsigned c_idx, assumption a, bound * prev);
        
        bound * at(unsigned timestamp);
        bkind kind() const { return static_cast<bkind>(m_kind); }
        bool is_lower() const { return m_lower != 0; }
    };

    typedef ptr_vector<bound>       var2bound;
    typedef svector<var>            var_vector;
    typedef svector<constraint>     constraint_vector;
    typedef unsigned_vector         c_idx_vector;
    typedef c_idx_vector            wlist;
    typedef small_object_allocator  allocator;
    typedef linear_equation_manager lin_eq_manager;

    numeral_manager &   m;
    allocator &         m_allocator;
    lin_eq_manager      m_eq_manager;
    constraint_vector   m_constraints;
    char_vector         m_is_int;
    char_vector         m_dead;
    var2bound           m_lowers;
    var2bound           m_uppers;
    vector<wlist>       m_watches;
    svector<trail_info> m_trail;
    unsigned            m_qhead;
    c_idx_vector        m_reinit_stack;
    unsigned_vector     m_lower_refinements;  // number of times a lower bound was propagated for each variable (loop prevention)
    unsigned_vector     m_upper_refinements;  // number of times a upper bound was propagated for each variable (loop prevention)
    unsigned            m_timestamp;
    var                 m_conflict;
    mpq                 m_tmp;
    
    struct scope {
        unsigned       m_trail_limit;
        unsigned       m_qhead_old;
        unsigned       m_reinit_stack_limit;
        unsigned       m_timestamp_old:31;
        unsigned       m_in_conflict:1;
    };

    svector<scope>     m_scopes;

    unsigned_vector    m_to_reset_ts; // temp field: ids of the constraints we must reset the field m_timestamp

    // config
    unsigned           m_max_refinements; // maximum number of refinements per round
    double             m_small_interval;
    double             m_threshold; // improvement threshold
    double             m_strict2double;

    // statistics
    unsigned           m_conflicts;
    unsigned           m_propagations;
    unsigned           m_false_alarms;

    void del_constraint(constraint & cnstr);
    void del_constraints_core();

    template<bool LOWER>
    bool relevant_bound(var x, double approx_k) const;
    bool relevant_lower(var x, double approx_k) const;
    bool relevant_upper(var x, double approx_k) const;
    bool get_interval_size(var x, double & r) const;
    void check_feasibility(var x);

    bool assert_lower_core(var x, mpq & k, bool strict, bkind bk, unsigned c_idx, assumption a);
    bool assert_upper_core(var x, mpq & k, bool strict, bkind bk, unsigned c_idx, assumption a);

    bool propagate(unsigned c_idx);
    bool propagate_eq(unsigned c_idx);
    bool propagate_lower(unsigned c_idx, unsigned i);
    bool propagate_upper(unsigned c_idx, unsigned i);
    void undo_trail(unsigned old_sz);

    typedef std::pair<var, bound *> var_bound;
    svector<var_bound> m_todo;
    void explain(var x, bound * b, unsigned ts, assumption_vector & ex) const;
    bool is_a_i_pos(linear_equation const & eq, var x) const;

    template<bool LOWER, typename Numeral>
    bool get_bound(unsigned sz, Numeral const * as, var const * xs, mpq & r, bool & st) const;

    void init_eq(linear_equation * eq);

public:
    bound_propagator(numeral_manager & m, allocator & a, params_ref const & p);
    ~bound_propagator();
    
    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void collect_statistics(statistics & st) const;
    void reset_statistics();

    double strict2double() const { return m_strict2double; }
    
    bool is_int(var x) const { return m_is_int[x] != 0; }

    unsigned scope_lvl() const { return m_scopes.size(); }
    void mk_var(var x, bool is_int);
    void del_var(var x);
    bool is_dead(var x) const { return m_dead[x] != 0; }
    void mk_eq(unsigned sz, mpq * as, var * xs);
    void mk_eq(unsigned sz, mpz * as, var * xs);
    void del_constraints();
    void assert_lower(var x, mpq const & k, bool strict, assumption a = null_assumption) {
        m.set(m_tmp, k);
        assert_lower_core(x, m_tmp, strict, a == null_assumption ? AXIOM : ASSUMPTION, 0, a);
    }
    void assert_upper(var x, mpq const & k, bool strict, assumption a = null_assumption) {
        m.set(m_tmp, k);
        assert_upper_core(x, m_tmp, strict, a == null_assumption ? AXIOM : ASSUMPTION, 0, a);
    }
    void assert_decided_lower(var x, mpq const & k) {
        m.set(m_tmp, k);
        assert_lower_core(x, m_tmp, false, DECISION, 0, null_assumption);
    }
    void assert_decided_upper(var x, mpq const & k) {
        m.set(m_tmp, k);
        assert_upper_core(x, m_tmp, false, DECISION, 0, null_assumption);
    }
    void propagate();
    void push();
    void pop(unsigned num_scopes);
    void reset();
    bool has_lower(var x) const { return m_lowers[x] != 0; }
    bool has_upper(var x) const { return m_uppers[x] != 0; }
    bool lower(var x, mpq & k, bool & strict, unsigned & ts) const;
    bool upper(var x, mpq & k, bool & strict, unsigned & ts) const;
    bool is_fixed(var x) const { return has_lower(x) && has_upper(x) && m.eq(m_lowers[x]->m_k, m_uppers[x]->m_k) && !inconsistent(); }
    mpq const & lower(var x, bool & strict) const { SASSERT(has_lower(x)); bound * b = m_lowers[x]; strict = b->m_strict; return b->m_k; }
    mpq const & upper(var x, bool & strict) const { SASSERT(has_upper(x)); bound * b = m_uppers[x]; strict = b->m_strict; return b->m_k; }
    mpq const & lower(var x) const { SASSERT(has_lower(x)); return m_lowers[x]->m_k; }
    mpq const & upper(var x) const { SASSERT(has_upper(x)); return m_uppers[x]->m_k; }
    double approx_lower(var x) const { 
        SASSERT(has_lower(x)); 
        return m_lowers[x]->m_strict ? m_lowers[x]->m_approx_k + m_strict2double : m_lowers[x]->m_approx_k;
    }
    double approx_upper(var x) const { 
        SASSERT(has_upper(x)); 
        return m_uppers[x]->m_strict ? m_uppers[x]->m_approx_k - m_strict2double : m_uppers[x]->m_approx_k; 
    }
    bool is_zero(var x) const { return has_lower(x) && has_upper(x) && m.is_zero(lower(x)) && m.is_zero(upper(x)); }
    void explain_lower(var x, unsigned ts, assumption_vector & ex) const { explain(x, m_lowers[x], ts, ex); }
    void explain_upper(var x, unsigned ts, assumption_vector & ex) const { explain(x, m_uppers[x], ts, ex); }
    void explain_lower(var x, assumption_vector & ex) const { explain_lower(x, m_timestamp, ex); }
    void explain_upper(var x, assumption_vector & ex) const { explain_upper(x, m_timestamp, ex); }
    var  conflict_var() const { return m_conflict; }
    bool inconsistent() const { return m_conflict != null_var; }
    
    unsigned trail_size() const { return m_trail.size(); }
    unsigned qhead() const { return m_qhead; }

    typedef svector<trail_info>::const_iterator trail_iterator;

    trail_iterator begin_trail() const { return m_trail.begin(); }
    trail_iterator end_trail() const { return m_trail.end(); }

    bool lower(unsigned sz, mpq const * as, var const * xs, mpq & r, bool & st) const;
    bool upper(unsigned sz, mpq const * as, var const * xs, mpq & r, bool & st) const;
    void display(std::ostream & out) const;
    void display_var_bounds(std::ostream & out, var x, bool approx = true, bool precise = true) const;
    void display_bounds(std::ostream & out, bool approx = true, bool precise = true) const;
    void display_precise_bounds(std::ostream & out) const { display_bounds(out, false, true); }
    void display_approx_bounds(std::ostream & out) const { display_bounds(out, true, false); }
    void display_constraints(std::ostream & out) const;
    void display_bounds_of(std::ostream & out, linear_equation const & eq) const;

    unsigned get_num_false_alarms() const { return m_false_alarms; }
    unsigned get_num_propagations() const { return m_propagations; }
};

#endif
