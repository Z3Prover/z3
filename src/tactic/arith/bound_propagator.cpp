/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bound_propagator.cpp

Abstract:

    Bound propagators for arithmetic.
    Support class for implementing strategies and search procedures

Author:

    Leonardo de Moura (leonardo) 2011-06-18.

Revision History:

--*/
#include "tactic/arith/bound_propagator.h"
#include<cmath>

// -------------------------------
// Bound Relaxation configuration
//
// The idea is to minimize errors in floating point computations
//
// If RELAX_BOUNDS is undefined, then bound relaxation is disabled.
// Otherwise, lower bounds l are relaxed using the formula
//    PRECISION * floor(l * INV_PRECISION + TOLERANCE)
// and upper bounds u as:
//    PRECISION * ceil(u * INV_PRECISION - TOLERANCE)
// In the LP literature, the suggested values are
//  l :=  10^-5 * floor(l*10^5 + 10^-6)
//  u :=  10^-5 * ceil(u*10^5 - 10^-6)
// I'm using the following values because of strict bounds
//  l :=  10^-6 * floor(l*10^6 + 10^-7)
//  u :=  10^-6 * ceil(u*10^6 - 10^-7)
#define RELAX_BOUNDS
#define TOLERANCE 0.0000001
#define PRECISION 0.000001
#define INV_PRECISION 1000000.0
// -------------------------------

bound_propagator::bound::bound(numeral_manager & m,
                               mpq const & k, 
                               double approx_k,
                               bool lower, 
                               bool strict, 
                               unsigned lvl, 
                               unsigned ts, 
                               bkind bk, 
                               unsigned c_idx,
                               assumption a, 
                               bound * prev):
    m_approx_k(approx_k),
    m_lower(lower),
    m_strict(strict),
    m_kind(bk),
    m_level(lvl),
    m_timestamp(ts),
    m_prev(prev) {
    m.set(m_k, k);
    if (bk == DERIVED)
        m_constraint_idx = c_idx;
    else
        m_assumption = a;
}

bound_propagator::bound_propagator(numeral_manager & _m, allocator & a, params_ref const & p):
    m(_m),
    m_allocator(a), 
    m_eq_manager(m, a) {
    m_timestamp = 0;
    m_qhead     = 0;
    m_conflict  = null_var;
    updt_params(p);
    reset_statistics();
}

bound_propagator::~bound_propagator() {
    m.del(m_tmp);
    reset();
}

void bound_propagator::del_constraints_core() {
    for (auto & c : m_constraints) {
        del_constraint(c);
    }
    m_constraints.reset();
}

void bound_propagator::del_constraints() {
    SASSERT(scope_lvl() == 0);
    if (m_constraints.empty())
        return;
    del_constraints_core();
    m_constraints.finalize();
    for (auto& wl : m_watches) {
        wl.finalize();
    }
}

void bound_propagator::del_constraint(constraint & c) {
    switch (c.m_kind) {
    case LINEAR:
        m_eq_manager.del(c.m_eq);
        break;
    default:
        UNREACHABLE();
        break;
    }
}
    
void bound_propagator::updt_params(params_ref const & p) {
    m_max_refinements = p.get_uint("bound_max_refinements", 16);
    m_threshold       = p.get_double("bound_threshold", 0.05);
    m_small_interval  = p.get_double("bound_small_interval", 128);
    m_strict2double   = p.get_double("strict2double", 0.00001);
}

void bound_propagator::get_param_descrs(param_descrs & r) {
    r.insert("bound_max_refinements", CPK_UINT, "(default: 16) maximum number of bound refinements (per round) for unbounded variables.");
    r.insert("bound_threshold", CPK_DOUBLE, "(default: 0.05) bound propagation improvement threshold ratio.");
}

void bound_propagator::collect_statistics(statistics & st) const {
    st.update("bound conflicts", m_conflicts);
    st.update("bound propagations", m_propagations);
    st.update("bound false alarms", m_false_alarms);
}

void bound_propagator::reset_statistics() {
    m_conflicts = 0;
    m_propagations = 0;
    m_false_alarms = 0;
}

void bound_propagator::mk_var(var x, bool is_int) {
    m_is_int.reserve(x+1, false);
    m_dead.reserve(x+1, true);
    m_lowers.reserve(x+1, 0);
    m_uppers.reserve(x+1, 0);
    m_lower_refinements.reserve(x+1, 0);
    m_upper_refinements.reserve(x+1, 0);
    m_watches.reserve(x+1);

    SASSERT(m_dead[x]);

    m_is_int[x] = is_int;
    m_dead[x]   = false;
    m_lowers[x] = 0;
    m_uppers[x] = 0;
    m_lower_refinements[x] = 0;
    m_upper_refinements[x] = 0;
    m_watches[x].reset();
}

void bound_propagator::del_var(var x) {
    SASSERT(!m_dead[x]);
    m_dead[x] = true;
    // mark constraints containing x as dead.
    wlist & wl = m_watches[x];
    for (auto c : wl) {
        m_constraints[c].m_dead = true;
    }
}

void bound_propagator::mk_eq(unsigned sz, mpq * as, var * xs) {
    linear_equation * eq = m_eq_manager.mk(sz, as, xs);
    init_eq(eq);
}

void bound_propagator::mk_eq(unsigned sz, mpz * as, var * xs) {
    linear_equation * eq = m_eq_manager.mk(sz, as, xs);
    init_eq(eq);
}

void bound_propagator::init_eq(linear_equation * eq) {
    if (eq == nullptr)
        return;
    unsigned c_idx = m_constraints.size();
    m_constraints.push_back(constraint());
    constraint & new_c  = m_constraints.back();
    new_c.m_kind        = LINEAR;
    new_c.m_dead        = false;
    new_c.m_timestamp   = 0;
    new_c.m_act         = 0;
    new_c.m_counter     = 0;
    new_c.m_eq          = eq;
    unsigned sz = eq->size();
    for (unsigned i = 0; i < sz; i++) {
        m_watches[eq->x(i)].push_back(c_idx);
    }
    if (propagate(c_idx) && scope_lvl() > 0)
        m_reinit_stack.push_back(c_idx);
}

void bound_propagator::push() {
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_trail_limit        = m_trail.size();
    s.m_qhead_old          = m_qhead;
    s.m_reinit_stack_limit = m_reinit_stack.size();
    s.m_timestamp_old      = m_timestamp;
    s.m_in_conflict        = inconsistent();
}

void bound_propagator::undo_trail(unsigned old_sz) {
    SASSERT(old_sz <= m_trail.size());
    unsigned i = m_trail.size();
    while (i > old_sz) {
        --i;
        trail_info & info = m_trail.back();
        var x         = info.x();
        bool is_lower = info.is_lower();
        m_trail.pop_back();
        bound * b;
        if (is_lower) {
            b = m_lowers[x];
            m_lowers[x] = b->m_prev;
        }
        else {
            b = m_uppers[x];
            m_uppers[x] = b->m_prev;
        }
        m.del(b->m_k);
        b->~bound();
        m_allocator.deallocate(sizeof(bound), b);
    }
    SASSERT(m_trail.size() == old_sz);
}

void bound_propagator::pop(unsigned num_scopes) {
    unsigned lvl     = scope_lvl();
    SASSERT(num_scopes <= lvl);
    unsigned new_lvl = lvl - num_scopes;
    scope & s        = m_scopes[new_lvl];
    undo_trail(s.m_trail_limit);
    m_timestamp = s.m_timestamp_old;
    m_qhead     = s.m_qhead_old;
    if (!s.m_in_conflict)
        m_conflict = null_var;
    unsigned reinit_stack_sz = s.m_reinit_stack_limit;
    m_scopes.shrink(new_lvl);

    // reinitialize
    unsigned i  = reinit_stack_sz;
    unsigned j  = reinit_stack_sz;
    unsigned sz = m_reinit_stack.size();
    for (; i < sz; i++) {
        unsigned c_idx = m_reinit_stack[i];
        bool p = propagate(c_idx);
        if (new_lvl > 0 && p) {
            m_reinit_stack[j] = c_idx;
            j++;
        }
    }
    m_reinit_stack.shrink(j);
}

bool bound_propagator::assert_lower_core(var x, mpq & k, bool strict, bkind bk, unsigned c_idx, assumption a) {
    if (is_int(x)) {
        if (m.is_int(k)) {
            if (strict)
                m.inc(k);
        }
        else {
            m.ceil(k, k);
        }
        SASSERT(m.is_int(k));
        strict = false;
    }
    TRACE("bound_propagator_detail", tout << "new lower x" << x << " " << m.to_string(k) << " strict: " << strict << "\n";);

    bound * old_lower = m_lowers[x];
    if (old_lower) {
        bool improves = m.gt(k, old_lower->m_k) || (!old_lower->m_strict && strict && m.eq(k, old_lower->m_k));
        if (!improves) {
            if (bk == DERIVED) {
                TRACE("bound_propagator_detail", tout << "false alarm\n";);
                m_false_alarms++;
            }
            return false;
        }
    }
    
    if (bk == DERIVED) {
        TRACE("bound_propagator_derived", tout << "new lower x" << x << " " << m.to_string(k) << " strict: " << strict << "\n";);
        m_propagations++;
    }

    if (scope_lvl() == 0 && bk == DERIVED)
        bk = AXIOM; // don't need justification at level 0

    double approx_k = m.get_double(k);
    TRACE("new_bound", tout << "x" << x << " lower: " << m.to_string(k) << " approx: " << approx_k << "\n";);
#ifdef RELAX_BOUNDS
    approx_k = PRECISION*floor(approx_k*INV_PRECISION + TOLERANCE);
    TRACE("new_bound", tout << "x" << x << " lower: " << m.to_string(k) << " relaxed approx: " << approx_k << "\n";);
#endif
    void  * mem = m_allocator.allocate(sizeof(bound));
    bound * new_lower = new (mem) bound(m, k, approx_k, true, strict, scope_lvl(), m_timestamp, bk, c_idx, a, old_lower);
    m_timestamp++;
    m_lowers[x] = new_lower;
    m_trail.push_back(trail_info(x, true));
    m_lower_refinements[x]++;
    check_feasibility(x);

    return true;
}

bool bound_propagator::assert_upper_core(var x, mpq & k, bool strict, bkind bk, unsigned c_idx, assumption a) {
    if (is_int(x)) {
        if (m.is_int(k)) {
            if (strict)
                m.dec(k);
        }
        else {
            m.floor(k, k);
        }
        SASSERT(m.is_int(k));
        strict = false;
    }

    TRACE("bound_propagator_detail", tout << "new upper x" << x << " " << m.to_string(k) << " strict: " << strict << "\n";);

    bound * old_upper = m_uppers[x];
    if (old_upper) {
        bool improves = m.lt(k, old_upper->m_k) || (!old_upper->m_strict && strict && m.eq(k, old_upper->m_k));
        if (!improves) {
            if (bk == DERIVED) {
                TRACE("bound_propagator_detail", tout << "false alarm\n";);
                m_false_alarms++;
            }
            return false;
        }
    }

    if (bk == DERIVED) {
        m_propagations++;
        TRACE("bound_propagator_derived", tout << "new upper x" << x << " " << m.to_string(k) << " strict: " << strict << "\n";);
    }

    if (scope_lvl() == 0 && bk == DERIVED)
        bk = AXIOM; // don't need justification at level 0

    double approx_k = m.get_double(k);
    TRACE("new_bound", tout << "x" << x << " upper: " << m.to_string(k) << " approx: " << approx_k << "\n";);
#ifdef RELAX_BOUNDS
    approx_k = PRECISION*ceil(approx_k*INV_PRECISION - TOLERANCE);
    TRACE("new_bound", tout << "x" << x << " upper: " << m.to_string(k) << " relaxed approx: " << approx_k << "\n";);
#endif
    
    void  * mem = m_allocator.allocate(sizeof(bound));
    bound * new_upper = new (mem) bound(m, k, approx_k, false, strict, scope_lvl(), m_timestamp, bk, c_idx, a, m_uppers[x]);
    m_timestamp++;
    m_uppers[x] = new_upper;
    m_trail.push_back(trail_info(x, false));
    m_upper_refinements[x]++;
    check_feasibility(x);
    return true;
}

bool bound_propagator::get_interval_size(var x, double & r) const {
    bound * l = m_lowers[x];
    bound * u = m_uppers[x];
    if (l && u) {
        r = u->m_approx_k - l->m_approx_k;
        return true;
    }
    return false;
}

template<bool LOWER>
bool bound_propagator::relevant_bound(var x, double new_k) const {
    TRACE("bound_propagator_detail", tout << "relevant_bound x" << x << " " << new_k << " LOWER: " << LOWER << "\n";
          if (LOWER && has_lower(x)) tout << "old: " << m.to_string(m_lowers[x]->m_k) << " | " << m_lowers[x]->m_approx_k << "\n";
          if (!LOWER && has_upper(x)) tout << "old: " << m.to_string(m_uppers[x]->m_k) << " | " << m_uppers[x]->m_approx_k << "\n";);
    bound * b = LOWER ? m_lowers[x] : m_uppers[x];
    if (b == nullptr)
        return true; // variable did not have a bound
    
    double interval_size;
    bool bounded = get_interval_size(x, interval_size);

    if (!is_int(x)) {
        // check if the improvement is significant
        double improvement;
        double abs_k = b->m_approx_k;
        if (abs_k < 0.0) 
            abs_k -= abs_k;
        if (bounded)
            improvement = m_threshold * std::max(std::min(interval_size, abs_k), 1.0);
        else
            improvement = m_threshold * std::max(abs_k, 1.0);
        
        if (LOWER) {
            if (new_k <= b->m_approx_k + improvement) {
                TRACE("bound_propagator", tout << "LOWER new: " << new_k << " old: " << b->m_approx_k << " improvement is too small\n";);
                return false; // improvement is too small
            }
        }
        else {
            if (new_k >= b->m_approx_k - improvement) {
                TRACE("bound_propagator", tout << "UPPER new: " << new_k << " old: " << b->m_approx_k << " improvement is too small\n";);
                return false; // improvement is too small
            }
        }
    }
    else {
        if (LOWER) {
            if (new_k < b->m_approx_k + 1.0)
                return false; // no improvement
        }
        else {
            if (new_k > b->m_approx_k - 1.0)
                return false; // no improvement
        }
    }
    
    if (bounded && interval_size <= m_small_interval)
        return true;
    
    if (LOWER)
        return m_lower_refinements[x] < m_max_refinements;
    else
        return m_upper_refinements[x] < m_max_refinements;
}

bool bound_propagator::relevant_lower(var x, double approx_k) const {
    return relevant_bound<true>(x, approx_k);
}

bool bound_propagator::relevant_upper(var x, double approx_k) const {
    return relevant_bound<false>(x, approx_k);
}

void bound_propagator::check_feasibility(var x) {
    if (inconsistent())
        return;
    bound * l = m_lowers[x];
    bound * u = m_uppers[x];
    if (l && u) {
        if (m.lt(l->m_k, u->m_k))
            return;
        if (!l->m_strict && !u->m_strict && m.eq(l->m_k, u->m_k))
            return;
        m_conflict = x;
        m_conflicts++;
        SASSERT(inconsistent());
        TRACE("bound_propagator", tout << "inconsistency detected: x" << x << "\n"; display(tout););
    }
}

void bound_propagator::propagate() {
    m_to_reset_ts.reset();

    while (m_qhead < m_trail.size()) {
        if (inconsistent())
            break;
        trail_info & info = m_trail[m_qhead];
        var x = info.x();
        bool is_lower = info.is_lower();
        bound * b   = is_lower ? m_lowers[x] : m_uppers[x];
        SASSERT(b);
        unsigned ts = b->m_timestamp; 
        TRACE("bound_propagator_detail", tout << "propagating x" << x << "\n";);
        m_qhead++;
        wlist const & wl = m_watches[x];
        for (unsigned c_idx : wl) {
            constraint & c = m_constraints[c_idx];
            // We don't need to visit c if it was already propagated using b.
            // Whenever we visit c we store in c.m_timestamp the current timestamp
            // So, we know that c was already propagated any bound using bounds with timestamp lower than c.m_timestamp.
            if (ts >= c.m_timestamp) {
                if (c.m_timestamp == 0)
                    m_to_reset_ts.push_back(c_idx);
                c.m_timestamp = m_timestamp; 
                propagate(c_idx);
            }
        }
    }

    for (unsigned c : m_to_reset_ts) 
        m_constraints[c].m_timestamp = 0;
}

bool bound_propagator::propagate(unsigned c_idx) {
    constraint const & c = m_constraints[c_idx];
    if (c.m_dead)
        return false;
    if (c.m_kind == LINEAR)
        return propagate_eq(c_idx);
    return false;
}

bool bound_propagator::propagate_eq(unsigned c_idx) {
    constraint const & c = m_constraints[c_idx];
    linear_equation * eq = c.m_eq;

#if 0
    {
        static unsigned counter = 0;
        static unsigned visited = 0;
        counter++;
        visited += eq->size();
        if (counter % 1000 == 0)
            verbose_stream() << "[bound-propagator] :propagate-eq " << counter << " :visited-vars " << visited << std::endl;
    }
#endif

    TRACE("bound_propagator_detail", tout << "propagating using eq: "; m_eq_manager.display(tout, *eq); tout << "\n";);
    // ll = (Sum_{a_i < 0} -a_i*lower(x_i)) + (Sum_{a_i > 0} -a_i * upper(x_i)) 
    // uu = (Sum_{a_i > 0} -a_i*lower(x_i)) + (Sum_{a_i < 0} -a_i * upper(x_i)) 
    unsigned ll_i = UINT_MAX; // position of the variable that couldn't contribute to ll
    unsigned uu_i = UINT_MAX; // position of the variable that coundn't contribute to uu
    bool ll_failed = false;
    bool uu_failed = false;
    double ll = 0.0;
    double uu = 0.0;
    unsigned sz = eq->size();
    for (unsigned i = 0; i < sz; i++) {
        var x_i     = eq->x(i);
        double a_i  = eq->approx_a(i);
        bound * l_i = m_lowers[x_i];
        bound * u_i = m_uppers[x_i];
        if (a_i < 0.0) {
            if (!ll_failed) {
                if (l_i == nullptr) {
                    if (ll_i == UINT_MAX)
                        ll_i = i;
                    else
                        ll_failed = true;
                }
                else {
                    ll -= a_i * l_i->m_approx_k;
                }
            }
            
            if (!uu_failed) {
                if (u_i == nullptr) {
                    if (uu_i == UINT_MAX)
                        uu_i = i;
                    else
                        uu_failed = true;
                }
                else {
                    uu -= a_i * u_i->m_approx_k;
                }
            }
        }
        else {
            if (!ll_failed) {
                if (u_i == nullptr) {
                    if (ll_i == UINT_MAX)
                        ll_i = i;
                    else
                        ll_failed = true;
                }
                else {
                    ll -= a_i * u_i->m_approx_k;
                }
            }

            if (!uu_failed) {
                if (l_i == nullptr) {
                    if (uu_i == UINT_MAX)
                        uu_i = i;
                    else
                        uu_failed = true;
                }
                else {
                    uu -= a_i * l_i->m_approx_k;
                }
            }
        }
        if (ll_failed && uu_failed)
            return false; // nothing to propagate
    }

    bool propagated = false;

    SASSERT(!ll_failed || !uu_failed);
    if (ll_i == UINT_MAX || uu_i == UINT_MAX) {
        for (unsigned i = 0; i < sz; i++) {
            var x_i     = eq->x(i);
            double a_i  = eq->approx_a(i);
            bound * l_i = m_lowers[x_i];
            bound * u_i = m_uppers[x_i];
            // ll = (Sum_{a_i < 0} -a_i*lower(x_i)) + (Sum_{a_i > 0} -a_i * upper(x_i)) 
            // uu = (Sum_{a_i > 0} -a_i*lower(x_i)) + (Sum_{a_i < 0} -a_i * upper(x_i)) 
            if (ll_i == UINT_MAX) {
                // can propagate a lower bound for a_i*x_i
                if (a_i > 0.0) {
                    // can propagate a lower bound for x_i
                    double new_k = (ll + a_i * u_i->m_approx_k)/a_i;
                    if (relevant_lower(x_i, new_k) && propagate_lower(c_idx, i))
                        propagated = true;
                }
                else {
                    // a_i < 0.0
                    // can propagate a upper bound for x_i
                    double new_k = (ll + a_i * l_i->m_approx_k)/a_i;
                    if (relevant_upper(x_i, new_k) && propagate_upper(c_idx, i))
                        propagated = true;
                }
            }
            if (uu_i == UINT_MAX) {
                // can propagate an upper bound for a_i*x_i
                if (a_i > 0.0) {
                    // can propagate a upper bound for x_i
                    double new_k = (uu + a_i * l_i->m_approx_k)/a_i;
                    if (relevant_upper(x_i, new_k) && propagate_upper(c_idx, i))
                        propagated = true;
                }
                else {
                    // a_i < 0.0
                    // can propagate a lower bound for x_i
                    double new_k = (uu + a_i * u_i->m_approx_k)/a_i;
                    if (relevant_lower(x_i, new_k) && propagate_lower(c_idx, i))
                        propagated = true;
                }
            }
        }
    }

    if (!ll_failed && ll_i != UINT_MAX) {
        // can propagate a lower bound for the monomial at position ll_i
        var x_i      = eq->x(ll_i);
        double a_i   = eq->approx_a(ll_i);
        double new_k = ll/a_i;
        if (a_i > 0.0) {
            if (relevant_lower(x_i, new_k) && propagate_lower(c_idx, ll_i))
                propagated = true;
        }
        else {
            if (relevant_upper(x_i, new_k) && propagate_upper(c_idx, ll_i))
                propagated = true;
        }
    }

    if (!uu_failed && uu_i != UINT_MAX) {
        // can propagate a upper bound for the monomial at position uu_i
        var x_i      = eq->x(uu_i);
        double a_i   = eq->approx_a(uu_i);
        double new_k = uu/a_i;
        if (a_i > 0.0) {
            if (relevant_upper(x_i, new_k) && propagate_upper(c_idx, uu_i))
                propagated = true;
        }
        else {
            if (relevant_lower(x_i, new_k) && propagate_lower(c_idx, uu_i))
                propagated = true;
        }
    }
    
    return propagated;
}

/**
   \brief Try to propagate a lower bound for the variable stored at position i, using mpq's (rationals).
   When this method is invoked, we know that all other variables have the "right" bounds, and
   using doubles we improve the current known bound.
*/
bool bound_propagator::propagate_lower(unsigned c_idx, unsigned i) {
    constraint const & c = m_constraints[c_idx];
    linear_equation * eq = c.m_eq;
    var x_i = eq->x(i);
    mpz const & a_i = eq->a(i);
    unsigned sz = eq->size();
    mpq k;
    bool strict = false;
    bool neg_a_i = m.is_neg(a_i);
    for (unsigned j = 0; j < sz; j++) {
        if (i == j)
            continue;
        var x_j = eq->x(j);
        mpz const & a_j = eq->a(j);
        bound * b_j = (m.is_neg(a_j) == neg_a_i) ? m_uppers[x_j] : m_lowers[x_j];
        TRACE("bound_propagator_step_detail", tout << "k: " << m.to_string(k) << " b_j->m_k: " << m.to_string(b_j->m_k) << 
              " a_j: " << m.to_string(a_j) << "\n";);
        SASSERT(b_j);
        if (b_j->m_strict)
            strict = true;
        m.addmul(k, a_j, b_j->m_k, k);
    }
    TRACE("bound_propagator_step_detail", tout << "k: " << m.to_string(k) << "\n";);
    m.neg(k);
    m.div(k, a_i, k);
    TRACE("bound_propagator_step", tout << "propagating lower x" << x_i << " " << m.to_string(k) << " strict: " << strict << " using\n";
          m_eq_manager.display(tout, *eq); tout << "\n"; display_bounds_of(tout, *eq););
    bool r = assert_lower_core(x_i, k, strict, DERIVED, c_idx, null_assumption);
    m.del(k);
    return r;
}

/**
   \brief Try to propagate a upper bound for the variable stored at position i, using mpq's (rationals).
   When this method is invoked, we know that all other variables have the "right" bounds, and
   using doubles we improve the current known bound.
*/
bool bound_propagator::propagate_upper(unsigned c_idx, unsigned i) {
    constraint const & c = m_constraints[c_idx];
    linear_equation * eq = c.m_eq;
    var x_i = eq->x(i);
    mpz const & a_i = eq->a(i);
    unsigned sz = eq->size();
    mpq k;
    bool strict = false;
    bool neg_a_i = m.is_neg(a_i);
    for (unsigned j = 0; j < sz; j++) {
        if (i == j)
            continue;
        var x_j = eq->x(j);
        mpz const & a_j = eq->a(j);
        bound * b_j = (m.is_neg(a_j) == neg_a_i) ? m_lowers[x_j] : m_uppers[x_j];
        SASSERT(b_j);
        if (b_j->m_strict)
            strict = true;
        m.addmul(k, a_j, b_j->m_k, k);
    }
    m.neg(k);
    m.div(k, a_i, k);
    TRACE("bound_propagator_step", tout << "propagating upper x" << x_i << " " << m.to_string(k) << " strict: " << strict << " using\n";
          m_eq_manager.display(tout, *eq); tout << "\n"; display_bounds_of(tout, *eq););
    bool r = assert_upper_core(x_i, k, strict, DERIVED, c_idx, null_assumption);
    m.del(k);
    return r;
}

void bound_propagator::reset() {
    undo_trail(0);
    del_constraints_core();
    m_constraints.finalize();
    m_is_int.finalize();
    m_dead.finalize();
    m_lowers.finalize();
    m_uppers.finalize();
    m_watches.finalize();
    m_trail.finalize();
    m_qhead = 0;
    m_reinit_stack.finalize();
    m_lower_refinements.finalize();
    m_upper_refinements.finalize();
    m_timestamp = 0;
    m_conflict = null_var;
    m_scopes.finalize();
}

bool bound_propagator::lower(var x, mpq & k, bool & strict, unsigned & ts) const {
    bound * b = m_lowers[x];
    if (!b)
        return false;
    m.set(k, b->m_k);
    strict = b->m_strict;
    ts = b->m_timestamp;
    return true;
}

bool bound_propagator::upper(var x, mpq & k, bool & strict, unsigned & ts) const {
    bound * b = m_uppers[x];
    if (!b)
        return false;
    m.set(k, b->m_k);
    strict = b->m_strict;
    ts = b->m_timestamp;
    return true;
}

bound_propagator::bound * bound_propagator::bound::at(unsigned timestamp) {
    bound * r = this;
    while (r != nullptr && r->m_timestamp >= timestamp)
        r = r->m_prev;
    return r;
}

/**
   \brief Return true if the coefficient of x in eq is positive
*/
bool bound_propagator::is_a_i_pos(linear_equation const & eq, var x) const {
    unsigned i = eq.pos(x);
    if (i == UINT_MAX)
        return false;
    return m.is_pos(eq.a(i));
}

void bound_propagator::explain(var x, bound * b, unsigned ts, assumption_vector & ex) const {
    if (!b)
        return;
    b = b->at(ts);
    if (!b)
        return;
    if (b->m_kind == AXIOM || b->m_kind == DECISION)
        return;
    if (b->m_kind == ASSUMPTION) {
        ex.push_back(b->m_assumption);
        return;
    }
    svector<var_bound> & todo = const_cast<bound_propagator*>(this)->m_todo;
    todo.reset();
    unsigned qhead = 0;
    todo.push_back(var_bound(x, b));
    b->m_mark = true;
    while (qhead < todo.size()) {
        var_bound & vb = todo[qhead];
        qhead ++;
        var x     = vb.first;
        bound * b = vb.second;
        SASSERT(b->kind() == ASSUMPTION || b->kind() == DERIVED);
        if (b->kind() == ASSUMPTION) {
            ex.push_back(b->m_assumption);
            continue;
        }
        SASSERT(b->kind() == DERIVED);
        constraint const & c = m_constraints[b->m_constraint_idx];
        switch (c.m_kind) {
        case LINEAR: {
            linear_equation * eq = c.m_eq;
            bool is_lower  = b->is_lower();
            if (!is_a_i_pos(*eq, x))
                is_lower = !is_lower;
            unsigned sz = eq->size();
            for (unsigned i = 0; i < sz; i++) {
                var x_i = eq->x(i);
                if (x_i == x)
                    continue;
                bound * b = (m.is_neg(eq->a(i)) == is_lower) ? m_lowers[x_i] : m_uppers[x_i];
                SASSERT(b);
                if (b->kind() == DERIVED || b->kind() == ASSUMPTION) {
                    if (!b->m_mark) {
                        b->m_mark = true;
                        todo.push_back(var_bound(x_i, b));
                    }
                }
            }
            break;
        }
        default:
            break;
        }
    }
    unsigned sz = todo.size();
    for (unsigned i = 0; i < sz; i++)
        todo[i].second->m_mark = false;
    todo.reset();
}

/**
   \brief Compute lower (upper) bound for the linear polynomial as[0]*xs[0] + ... + as[sz-1]*xs[sz-1]
   
   Return false if the lower (upper) bound is -oo (oo)
*/
template<bool LOWER, typename Numeral>
bool bound_propagator::get_bound(unsigned sz, Numeral const * as, var const * xs, mpq & r, bool & st) const {
    st = false;
    m.reset(r);
    for (unsigned i = 0; i < sz; i++) {
        var x_i = xs[i];
        Numeral const & a_i = as[i];
        if (m.is_zero(a_i))
            continue;
        bound * b = (m.is_neg(a_i) == LOWER) ? m_uppers[x_i] : m_lowers[x_i];
        if (!b) {
            m.reset(r);
            return false;
        }
        if (b->m_strict)
            st = true;
        m.addmul(r, a_i, b->m_k, r); 
    }
    return true;
}

bool bound_propagator::lower(unsigned sz, mpq const * as, var const * xs, mpq & r, bool & st) const {
    return get_bound<true, mpq>(sz, as, xs, r, st);
}

bool bound_propagator::upper(unsigned sz, mpq const * as, var const * xs, mpq & r, bool & st) const {
    return get_bound<false, mpq>(sz, as, xs, r, st);
}

void bound_propagator::display_bounds_of(std::ostream & out, linear_equation const & eq) const {
    for (unsigned i = 0; i < eq.size(); i++) {
        display_var_bounds(out, eq.x(i));
        out << "\n";
    }
}

void bound_propagator::display_var_bounds(std::ostream & out, var x, bool approx, bool precise) const {
    if (m_lowers[x]) {
        if (precise)
            out << m.to_string(m_lowers[x]->m_k);
        if (precise && approx)
            out << " | ";
        if (approx)
            out << m_lowers[x]->m_approx_k;
        out << " " << (m_lowers[x]->m_strict ? "<" : "<=");
    }
    else {
        out << "-oo <";
    }
    out << " x" << x << " ";
    if (m_uppers[x]) {
        out << (m_uppers[x]->m_strict ? "<" : "<=") << " ";
        if (precise)
            out << m.to_string(m_uppers[x]->m_k);
        if (precise && approx)
            out << " | ";
        if (approx)
            out << m_uppers[x]->m_approx_k;
    }
    else {
        out << "< oo";
    }
}

void bound_propagator::display_bounds(std::ostream & out, bool approx, bool precise) const {
    unsigned num_vars = m_dead.size();
    for (unsigned x = 0; x < num_vars; x++) {
        if (!is_dead(x)) {
            display_var_bounds(out, x, approx, precise);
            out << "\n";
        }
    }
}

void bound_propagator::display_constraints(std::ostream & out) const {
    for (constraint const& c : m_constraints) {
        if (c.m_kind == LINEAR) {
            m_eq_manager.display(out, *(c.m_eq));
            out << "\n";
        }
    }
}

void bound_propagator::display(std::ostream & out) const {
    display_bounds(out);
    display_constraints(out);
}



