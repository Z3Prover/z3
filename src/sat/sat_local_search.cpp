/*++
  Copyright (c) 2017 Microsoft Corporation

Module Name:

  sat_local_search.cpp

Abstract:
   
  Local search module for cardinality clauses.

Author:

  Sixue Liu 2017-2-21

Notes:

--*/

#include "sat/sat_local_search.h"
#include "sat/sat_solver.h"
#include "sat/ba_solver.h"
#include "sat/sat_params.hpp"
#include "util/timer.h"

namespace sat {

    void local_search::init() {
        flet<bool> _init(m_initializing, true);
        m_unsat_stack.reset();
        for (unsigned i = 0; i < m_assumptions.size(); ++i) {
            add_clause(1, m_assumptions.c_ptr() + i);
        }

        // add sentinel variable.
        m_vars.push_back(var_info());

        if (m_config.phase_sticky()) {
            for (var_info& vi : m_vars)
                if (!vi.m_unit) 
                    vi.m_value = vi.m_bias > 50;
        }
        else {
            for (var_info& vi : m_vars) 
                if (!vi.m_unit)
                    vi.m_value = (0 == (m_rand() % 2));
        }

        m_index_in_unsat_stack.resize(num_constraints(), 0);
        set_parameters();
    }

    void local_search::init_cur_solution() {
        for (var_info& vi : m_vars) {
            if (!vi.m_unit) {
                if (m_config.phase_sticky()) {
                    vi.m_value = ((unsigned)(m_rand() % 100) < vi.m_bias);
                }
                else {
                    vi.m_value = (m_rand() % 2) == 0;
                }
            }
        }
    }

    // figure out slack, and init unsat stack
    void local_search::init_slack() {
        for (unsigned v = 0; v < num_vars(); ++v) {
            bool is_true = cur_solution(v);
            coeff_vector& truep = m_vars[v].m_watch[is_true];
            for (auto const& coeff : truep) {
                unsigned c = coeff.m_constraint_id;
                constraint& cn = m_constraints[c];
                cn.m_slack -= coeff.m_coeff;
            }            
        }
        for (unsigned c = 0; c < num_constraints(); ++c) {
            // violate the at-most-k constraint
            if (m_constraints[c].m_slack < 0)
                unsat(c);
        }
    }

    // figure out variables scores and slack_scores
    void local_search::init_scores() {
        for (unsigned v = 0; v < num_vars(); ++v) {
            bool is_true = cur_solution(v);
            coeff_vector& truep = m_vars[v].m_watch[is_true];
            coeff_vector& falsep = m_vars[v].m_watch[!is_true];
            for (auto const& coeff : falsep) {
                constraint& c = m_constraints[coeff.m_constraint_id];
                // will --slack
                if (c.m_slack <= 0) {
                    dec_slack_score(v);
                    if (c.m_slack == 0)
                        dec_score(v);
                }
            }
            for (auto const& coeff : truep) {
                constraint& c = m_constraints[coeff.m_constraint_id];
                // will --true_terms_count[c]
                // will ++slack
                if (c.m_slack <= -1) {
                    inc_slack_score(v);
                    if (c.m_slack == -1)
                        inc_score(v);
                }
            }
        }
    }

    // init goodvars 
    void local_search::init_goodvars() {
        m_goodvar_stack.reset();
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (score(v) > 0) { // && conf_change[v] == true
                m_vars[v].m_in_goodvar_stack = true;
                m_goodvar_stack.push_back(v);
            }
        }
    }

    void local_search::reinit() {

        //
        // the following methods does NOT converge for pseudo-boolean
        // can try other way to define "worse" and "better"
        // the current best noise is below 1000
        //
        if (m_best_unsat_rate > m_last_best_unsat_rate) {
            // worse
            m_noise -= m_noise * 2 * m_noise_delta;
            m_best_unsat_rate *= 1000.0;
        }
        else {
            // better
            m_noise += (10000 - m_noise) * m_noise_delta;
        }

        for (constraint & c : m_constraints) {
            c.m_slack = c.m_k;
        }
        
        // init unsat stack
        m_is_unsat = false;
        m_unsat_stack.reset();
        
        // init solution using the bias
        init_cur_solution();
        
        // init variable information
        // the last variable is the virtual variable

        m_vars.back().m_score = INT_MIN;
        m_vars.back().m_conf_change = false;       
        m_vars.back().m_slack_score = INT_MIN;
        m_vars.back().m_time_stamp = m_max_steps + 1;
        for (unsigned i = 0; i < num_vars(); ++i) {
            m_vars[i].m_time_stamp = 0;
            m_vars[i].m_conf_change = true;
            m_vars[i].m_in_goodvar_stack = false;
            m_vars[i].m_score = 0;
            m_vars[i].m_slack_score = 0;
        }         
        init_slack();
        init_scores();
        init_goodvars();
        set_best_unsat();

        for (bool_var v : m_units) {
            propagate(literal(v, !cur_solution(v)));
            if (m_is_unsat) break;
        }
        if (m_is_unsat) {
            IF_VERBOSE(0, verbose_stream() << "unsat during reinit\n");
        }
        DEBUG_CODE(verify_slack(););
    }

    bool local_search::propagate(literal lit) {
        bool unit = is_unit(lit);
        VERIFY(is_true(lit));
        m_prop_queue.reset();
        add_propagation(lit);
        for (unsigned i = 0; i < m_prop_queue.size() && i < m_vars.size(); ++i) {
            literal lit2 = m_prop_queue[i];
            if (!is_true(lit2)) {
                if (is_unit(lit2)) {
                    return false;
                }
                flip_walksat(lit2.var());
                add_propagation(lit2);
            }
        }
        if (m_prop_queue.size() >= m_vars.size()) {
            IF_VERBOSE(0, verbose_stream() << "propagation loop\n");
            return false;
        }
        if (unit) {
            for (literal lit2 : m_prop_queue) {
                VERIFY(is_true(lit2));
                add_unit(lit2, lit);
            }
        }
        return true;
    }

    void local_search::add_propagation(literal l) {
        VERIFY(is_true(l));
        for (literal lit : m_vars[l.var()].m_bin[l.sign()]) {
            if (!is_true(lit)) {
                m_prop_queue.push_back(lit);
            }
        }
    }

    void local_search::set_best_unsat() {
        m_best_unsat = m_unsat_stack.size();
        m_best_phase.reserve(m_vars.size());
        for (unsigned i = m_vars.size(); i-- > 0; ) {
            m_best_phase[i] = m_vars[i].m_value;
        }        
    }    
    
    void local_search::verify_solution() const {
        IF_VERBOSE(0, verbose_stream() << "verifying solution\n");
        for (constraint const& c : m_constraints) 
            verify_constraint(c);
    }

    void local_search::verify_unsat_stack() const {        
        for (unsigned i : m_unsat_stack) {
            constraint const& c = m_constraints[i];
            if (c.m_k >= constraint_value(c)) {
                IF_VERBOSE(0, display(verbose_stream() << i << " ", c) << "\n");
                IF_VERBOSE(0, verbose_stream() << "units " << m_units << "\n");
            }
            VERIFY(c.m_k < constraint_value(c));
        }
    }

    bool local_search::verify_goodvar() const {
        unsigned g = 0;
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (conf_change(v) && score(v) > 0) {
                ++g;
            }
        }
        return g == m_goodvar_stack.size();
    }

    unsigned local_search::constraint_coeff(constraint const& c, literal l) const {
        for (auto const& pb : m_vars[l.var()].m_watch[is_pos(l)]) {
            if (pb.m_constraint_id == c.m_id) return pb.m_coeff;
        }
        UNREACHABLE();
        return 0;
    }

    void local_search::verify_constraint(constraint const& c) const {
        unsigned value = constraint_value(c);
        IF_VERBOSE(11, display(verbose_stream() << "verify ", c););
        TRACE("sat", display(verbose_stream() << "verify ", c););
        if (c.m_k < value) {
            IF_VERBOSE(0, display(verbose_stream() << "violated constraint: ", c) << "value: " << value << "\n";);
        }
    }

    void local_search::verify_slack(constraint const& c) const {
        VERIFY(constraint_value(c) + c.m_slack == c.m_k);
    }

    void local_search::verify_slack() const {
        for (constraint const& c : m_constraints) {
            verify_slack(c);
        }
    }

    unsigned local_search::constraint_value(constraint const& c) const {
        unsigned value = 0;
        for (literal t : c) {
            if (is_true(t)) {
                value += constraint_coeff(c, t);
            }
        }
        return value;
    }
    
    void local_search::add_clause(unsigned sz, literal const* c) {
        add_cardinality(sz, c, sz - 1);
    }

    // ~c <= k
    void local_search::add_cardinality(unsigned sz, literal const* c, unsigned k) {
        if (sz == 1 && k == 0) {
            add_unit(c[0], null_literal);
            return;
        }
        if (k == 1 && sz == 2) {
            // IF_VERBOSE(0, verbose_stream() << "bin: " << ~c[0] << " + " << ~c[1] << " <= 1\n");
            for (unsigned i = 0; i < 2; ++i) {
                literal t(c[i]), s(c[1-i]);
                m_vars.reserve(t.var() + 1);
                m_vars[t.var()].m_bin[is_pos(t)].push_back(s);
            }
        }
        unsigned id = m_constraints.size();
        m_constraints.push_back(constraint(k, id));
        for (unsigned i = 0; i < sz; ++i) {
            m_vars.reserve(c[i].var() + 1);
            literal t(~c[i]);            
            m_vars[t.var()].m_watch[is_pos(t)].push_back(pbcoeff(id, 1));
            m_constraints.back().push(t);
        }
        
    }

    // c * coeffs <= k
    void local_search::add_pb(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k) {
        if (sz == 1 && k == 0) {     
            add_unit(~c[0], null_literal);
            return;
        }
        unsigned id = m_constraints.size();
        m_constraints.push_back(constraint(k, id));
        for (unsigned i = 0; i < sz; ++i) {
            m_vars.reserve(c[i].var() + 1);            
            literal t(c[i]);            
            m_vars[t.var()].m_watch[is_pos(t)].push_back(pbcoeff(id, coeffs[i]));
            m_constraints.back().push(t);
        }
    }

    void local_search::add_unit(literal lit, literal exp) {
        bool_var v = lit.var();
        if (is_unit(lit)) return;
        SASSERT(!m_units.contains(v));
        if (m_vars[v].m_value == lit.sign() && !m_initializing) {
            flip_walksat(v);
        }
        m_vars[v].m_value = !lit.sign();
        m_vars[v].m_bias  = lit.sign() ? 0 : 100;
        m_vars[v].m_unit  = true;
        m_vars[v].m_explain = exp;
        m_units.push_back(v);
        DEBUG_CODE(verify_unsat_stack(););
    }

    local_search::local_search() :         
        m_is_unsat(false),
        m_par(nullptr) {
    }

    void local_search::reinit(solver& s) {
        import(s, true); 
        if (s.m_best_phase_size > 0) {
            for (unsigned i = num_vars(); i-- > 0; ) {
                set_phase(i, s.m_best_phase[i]);
            }
        }
    }

    void local_search::import(solver const& s, bool _init) {        
        flet<bool> linit(m_initializing, true);
        m_is_pb = false;
        m_vars.reset();
        m_constraints.reset();
        m_units.reset();
        m_unsat_stack.reset();
        m_vars.reserve(s.num_vars());
        m_config.set_config(s.get_config());

        if (m_config.phase_sticky()) {
            unsigned v = 0;
            for (var_info& vi : m_vars) {
                vi.m_bias = s.m_phase[v++] ? 98 : 2;
            }
        }

        // copy units
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            add_clause(1, s.m_trail.c_ptr() + i);
        }

        // copy binary clauses
        {
            unsigned sz = s.m_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l1 = ~to_literal(l_idx);
                watch_list const & wlist = s.m_watches[l_idx];
                for (watched const& w : wlist) {
                    if (!w.is_binary_non_learned_clause())
                        continue;
                    literal l2 = w.get_literal();
                    if (l1.index() > l2.index()) 
                        continue;
                    literal ls[2] = { l1, l2 };
                    add_clause(2, ls);
                }
            }
        }

        // copy clauses
        for (clause* c : s.m_clauses) {
            add_clause(c->size(), c->begin());
        }
        m_num_non_binary_clauses = s.m_clauses.size();

        // copy cardinality clauses
        ba_solver* ext = dynamic_cast<ba_solver*>(s.get_extension());
        if (ext) {
            unsigned_vector coeffs;
            literal_vector lits;
            for (ba_solver::constraint* cp : ext->m_constraints) {
                switch (cp->tag()) {
                case ba_solver::card_t: {
                    ba_solver::card const& c = cp->to_card();
                    unsigned n = c.size();
                    unsigned k = c.k();
                    
                    if (c.lit() == null_literal) {
                        //    c.lits() >= k 
                        // <=> 
                        //    ~c.lits() <= n - k
                        lits.reset();
                        for (unsigned j = 0; j < n; ++j) lits.push_back(c[j]);
                        add_cardinality(lits.size(), lits.c_ptr(), n - k);
                    }
                    else {
                        //
                        // c.lit() <=> c.lits() >= k
                        // 
                        //    (c.lits() < k) or c.lit()
                        // =  (c.lits() + (n - k + 1)*~c.lit()) <= n    
                        //
                        //    ~c.lit() or (c.lits() >= k)
                        // =  ~c.lit() or (~c.lits() <= n - k)
                        // =  k*c.lit() + ~c.lits() <= n 
                        // 
                        m_is_pb = true;
                        lits.reset();
                        coeffs.reset();
                        for (literal l : c) lits.push_back(l), coeffs.push_back(1);
                        lits.push_back(~c.lit()); coeffs.push_back(n - k + 1);
                        add_pb(lits.size(), lits.c_ptr(), coeffs.c_ptr(), n);
                        
                        lits.reset();
                        coeffs.reset();
                        for (literal l : c) lits.push_back(~l), coeffs.push_back(1);
                        lits.push_back(c.lit()); coeffs.push_back(k);
                        add_pb(lits.size(), lits.c_ptr(), coeffs.c_ptr(), n);
                    }
                    break;
                }
                case ba_solver::pb_t: {
                    ba_solver::pb const& p = cp->to_pb();
                    lits.reset();
                    coeffs.reset();
                    m_is_pb = true;
                    unsigned sum = 0;
                    for (ba_solver::wliteral wl : p) sum += wl.first;

                    if (p.lit() == null_literal) {
                        //   w1 + .. + w_n >= k
                        // <=> 
                        //  ~wl + ... + ~w_n <= sum_of_weights - k
                        for (ba_solver::wliteral wl : p) lits.push_back(~(wl.second)), coeffs.push_back(wl.first);
                        add_pb(lits.size(), lits.c_ptr(), coeffs.c_ptr(), sum - p.k());
                    }
                    else {
                        //    lit <=> w1 + .. + w_n >= k
                        // <=>
                        //     lit or w1 + .. + w_n <= k - 1
                        //    ~lit or w1 + .. + w_n >= k
                        // <=> 
                        //     (sum - k + 1)*~lit + w1 + .. + w_n <= sum
                        //     k*lit + ~wl + ... + ~w_n <= sum
                        lits.push_back(p.lit()), coeffs.push_back(p.k());
                        for (ba_solver::wliteral wl : p) lits.push_back(~(wl.second)), coeffs.push_back(wl.first);
                        add_pb(lits.size(), lits.c_ptr(), coeffs.c_ptr(), sum);

                        lits.reset();
                        coeffs.reset();
                        lits.push_back(~p.lit()), coeffs.push_back(sum + 1 - p.k());
                        for (ba_solver::wliteral wl : p) lits.push_back(wl.second), coeffs.push_back(wl.first);
                        add_pb(lits.size(), lits.c_ptr(), coeffs.c_ptr(), sum);
                    }
                    break;
                }
                case ba_solver::xr_t:
                    NOT_IMPLEMENTED_YET();
                    break;
                }
            }
        }
        if (_init) {
            init();
        }
    }
    
    local_search::~local_search() {
    }
    

    lbool local_search::check() {
        return check(0, nullptr, nullptr);
    }

#define PROGRESS(tries, flips)                                          \
    if (tries % 10 == 0 || m_unsat_stack.empty()) {                     \
        IF_VERBOSE(1, verbose_stream() << "(sat.local-search"           \
                   << " :flips " << flips                               \
                   << " :noise " << m_noise                             \
                   << " :unsat " << /*m_unsat_stack.size()*/ m_best_unsat               \
                   << " :constraints " << m_constraints.size()          \
                   << " :time " << (timer.get_seconds() < 0.001 ? 0.0 : timer.get_seconds()) << ")\n";); \
    }

    void local_search::walksat() {
        m_best_unsat_rate = 1;
        m_last_best_unsat_rate = 1;

        reinit();
        DEBUG_CODE(verify_slack(););
        timer timer;
        unsigned step = 0, total_flips = 0, tries = 0;
        
        for (tries = 1; !m_unsat_stack.empty() && m_limit.inc(); ++tries) {
            ++m_stats.m_num_restarts;
            for (step = 0; step < m_max_steps && !m_unsat_stack.empty(); ++step) {
                pick_flip_walksat();
                if (m_unsat_stack.size() < m_best_unsat) {
                    set_best_unsat();
                    m_last_best_unsat_rate = m_best_unsat_rate;
                    m_best_unsat_rate = (double)m_unsat_stack.size() / num_constraints();                                        
                }
                if (m_is_unsat) return;                    
            }
            total_flips += step;
            PROGRESS(tries, total_flips);
            if (m_par) {
                double max_avg = 0;
                for (unsigned v = 0; v < num_vars(); ++v) {
                    max_avg = std::max(max_avg, (double)m_vars[v].m_slow_break);
                }
                double sum = 0;
                for (unsigned v = 0; v < num_vars(); ++v) {
                    sum += exp(m_config.itau() * (m_vars[v].m_slow_break - max_avg));
                }
                if (sum == 0) {
                    sum = 0.01;
                }
                for (unsigned v = 0; v < num_vars(); ++v) {
                    m_vars[v].m_break_prob = exp(m_config.itau() * (m_vars[v].m_slow_break - max_avg)) / sum;
                }
                
                m_par->to_solver(*this);
            }
            if (m_par && m_par->from_solver(*this)) {
                reinit();
            }
            if (tries % 10 == 0 && !m_unsat_stack.empty()) {
                reinit();
            }            
        }
        PROGRESS(0, total_flips);
    }
    
    lbool local_search::check(unsigned sz, literal const* assumptions, parallel* p) {
        flet<parallel*> _p(m_par, p);
        m_model.reset();
        m_assumptions.reset();
        m_assumptions.append(sz, assumptions);
        unsigned num_units = m_units.size();
        init();
        walksat();
        
        // remove unit clauses
        for (unsigned i = m_units.size(); i-- > num_units; ) {
            m_vars[m_units[i]].m_unit = false;
        }
        m_units.shrink(num_units); 

        TRACE("sat", display(tout););

        lbool result;
        if (m_is_unsat) {
            result = l_false;
        }
        else if (m_unsat_stack.empty()) {
            verify_solution();
            extract_model();
            result = l_true;
        }
        else {
            result = l_undef;
        }
        m_vars.pop_back();  // remove sentinel variable
        IF_VERBOSE(1, verbose_stream() << "(sat.local-search " << result << ")\n";);
        IF_VERBOSE(20, display(verbose_stream()););
        return result;
    }


    void local_search::sat(unsigned c) {
        unsigned last_unsat_constraint = m_unsat_stack.back();
        int index = m_index_in_unsat_stack[c];
        m_unsat_stack[index] = last_unsat_constraint;
        m_index_in_unsat_stack[last_unsat_constraint] = index;
        m_unsat_stack.pop_back();
    }

    // swap the deleted one with the last one and pop
    void local_search::unsat(unsigned c) {
        m_index_in_unsat_stack[c] = m_unsat_stack.size();
        m_unsat_stack.push_back(c);
    }

    void local_search::pick_flip_lookahead() {
        unsigned num_unsat = m_unsat_stack.size();
        constraint const& c = m_constraints[m_unsat_stack[m_rand() % num_unsat]];
        literal best = null_literal;
        unsigned best_make = UINT_MAX;
        for (literal lit : c.m_literals) {
            if (!is_unit(lit) && is_true(lit)) {
                flip_walksat(lit.var());
                if (propagate(~lit) && best_make > m_unsat_stack.size()) {
                    best = lit;
                    best_make = m_unsat_stack.size();
                }
                flip_walksat(lit.var());
                propagate(lit);
            }
        }
        if (best != null_literal) {
            flip_walksat(best.var());
            propagate(~best);
        }        
        else {
            IF_VERBOSE(1, verbose_stream() << "(sat.local-search no best)\n");
        }
    }

    void local_search::pick_flip_walksat() {
    reflip:
        bool_var best_var = null_bool_var;
        unsigned n = 1;
        bool_var v = null_bool_var;
        unsigned num_unsat = m_unsat_stack.size();
        constraint const& c = m_constraints[m_unsat_stack[m_rand() % num_unsat]];
        unsigned reflipped = 0;
        bool is_core = m_unsat_stack.size() <= 10;
        if (m_rand() % 10000 <= m_noise) {
            // take this branch with 98% probability.
            // find the first one, to fast break the rest    
            unsigned best_bsb = 0;
            literal_vector::const_iterator cit = c.m_literals.begin(), cend = c.m_literals.end();
            literal l;
            for (; (cit != cend) && (!is_true(*cit) || is_unit(*cit)); ++cit) { }
            if (cit == cend) {
                if (c.m_k < constraint_value(c)) {
                    IF_VERBOSE(0, display(verbose_stream() << "unsat clause\n", c)); 
                    m_is_unsat = true;
                    return;
                }
                goto reflip;
            }
            l = *cit;
            best_var = v = l.var();
            bool tt = cur_solution(v);
            coeff_vector const& falsep = m_vars[v].m_watch[!tt];
            for (pbcoeff const& pbc : falsep) {
                int slack = constraint_slack(pbc.m_constraint_id);
                if (slack < 0)
                    ++best_bsb;
                else if (slack < static_cast<int>(pbc.m_coeff))
                    best_bsb += num_unsat;
            }
            ++cit;
            for (; cit != cend; ++cit) {
                l = *cit;
                if (is_true(l) && !is_unit(l)) {
                    v = l.var();                    
                    unsigned bsb = 0;
                    coeff_vector const& falsep = m_vars[v].m_watch[!cur_solution(v)];
                    auto it = falsep.begin(), end = falsep.end();
                    for (; it != end; ++it) {
                        int slack = constraint_slack(it->m_constraint_id);
                        if (slack < 0) {
                            if (bsb == best_bsb) {
                                break;
                            }
                            else {
                                ++bsb;
                            }
                        }
                        else if (slack < static_cast<int>(it->m_coeff)) {
                            bsb += num_unsat;
                            if (bsb > best_bsb) {
                                break;
                            }
                        }
                    }
                    if (it == end) {
                        if (bsb < best_bsb) {
                            best_bsb = bsb;
                            best_var = v;
                            n = 1;
                        }
                        else {// if (bsb == best_bb)
                            ++n;
                            if (m_rand() % n == 0) {
                                best_var = v;
                            }
                        }
                    }
                }
            }
        }
        else {
            for (literal l : c) {
                if (is_true(l) && !is_unit(l)) {
                    if (m_rand() % n == 0) {
                        best_var = l.var();
                    }
                    ++n;
                }
            }
        }
        if (best_var == null_bool_var) {
            IF_VERBOSE(1, verbose_stream() << "(sat.local_search :unsat)\n");
            return;
        }
        if (is_unit(best_var)) {
            goto reflip;
        }
        flip_walksat(best_var);
        literal lit(best_var, !cur_solution(best_var));
        if (!propagate(lit)) {
            if (is_true(lit)) { 
                flip_walksat(best_var);
            }
            add_unit(~lit, null_literal);
            if (!propagate(~lit)) {
                IF_VERBOSE(0, verbose_stream() << "unsat\n");
                m_is_unsat = true;
                return;
            }
            goto reflip;
        }

        if (false && is_core && c.m_k < constraint_value(c)) {
            ++reflipped;
            goto reflip;
        }
    }

    void local_search::flip_walksat(bool_var flipvar) {

        ++m_stats.m_num_flips;
        VERIFY(!is_unit(flipvar));
        m_vars[flipvar].m_value = !cur_solution(flipvar);
        m_vars[flipvar].m_flips++;
        m_vars[flipvar].m_slow_break.update(abs(m_vars[flipvar].m_slack_score));

        bool flip_is_true = cur_solution(flipvar);
        coeff_vector const& truep = m_vars[flipvar].m_watch[flip_is_true];
        coeff_vector const& falsep = m_vars[flipvar].m_watch[!flip_is_true];

        for (auto const& pbc : truep) {
            unsigned ci = pbc.m_constraint_id;
            constraint& c = m_constraints[ci];
            int old_slack = c.m_slack;
            c.m_slack -= pbc.m_coeff;
            DEBUG_CODE(verify_slack(c););
            if (c.m_slack < 0 && old_slack >= 0) { // from non-negative to negative: sat -> unsat
                unsat(ci);
            }
        }
        for (auto const& pbc : falsep) {
            unsigned ci = pbc.m_constraint_id;
            constraint& c = m_constraints[ci];
            int old_slack = c.m_slack;
            c.m_slack += pbc.m_coeff;
            DEBUG_CODE(verify_slack(c););
            if (c.m_slack >= 0 && old_slack < 0) { // from negative to non-negative: unsat -> sat
                sat(ci);
            }
        }
        
        DEBUG_CODE(verify_unsat_stack(););
    }

    void local_search::set_parameters()  {
        m_rand.set_seed(m_config.random_seed());
        m_best_known_value = m_config.best_known_value();

        m_max_steps = std::min(static_cast<unsigned>(20 * num_vars()), static_cast<unsigned>(1 << 17)); // cut steps off at 100K
        
        TRACE("sat", 
              tout << "seed:\t" << m_config.random_seed() << '\n';
              tout << "best_known_value:\t" << m_config.best_known_value() << '\n';
              tout << "max_steps:\t" << m_max_steps << '\n';
              );
    }

    void local_search::print_info(std::ostream& out) {
        for (unsigned v = 0; v < num_vars(); ++v) {
            out << "v" << v << "\t" 
                << m_vars[v].m_neighbors.size() << '\t' 
                << cur_solution(v) << '\t' 
                << conf_change(v)  << '\t' 
                << score(v)        << '\t' 
                << slack_score(v)  << '\n';
        }
    }

    void local_search::extract_model() {
        m_model.reset();
        for (unsigned v = 0; v < num_vars(); ++v) {
            m_model.push_back(cur_solution(v) ? l_true : l_false);
        }
    }

    std::ostream& local_search::display(std::ostream& out) const {
        for (constraint const& c : m_constraints) {
            display(out, c);
        }        
        for (bool_var v = 0; v < num_vars(); ++v) {
            display(out, v, m_vars[v]);
        }
        return out;
    }
    
    std::ostream& local_search::display(std::ostream& out, constraint const& c) const {
        for (literal l : c) {
            unsigned coeff = constraint_coeff(c, l);
            if (coeff > 1) out << coeff << " * ";
            out << l << " ";
        }
        return out << " <= " << c.m_k << " lhs value: " << constraint_value(c) << "\n";
    }
    
    std::ostream& local_search::display(std::ostream& out, unsigned v, var_info const& vi) const {
        out << "v" << v << " := " << (vi.m_value?"true":"false") << " bias: " << vi.m_bias;
        if (vi.m_unit) out << " u " << vi.m_explain;
        return out << "\n";
    }

    void local_search::collect_statistics(statistics& st) const {
        if (m_config.dbg_flips()) {
            unsigned i = 0;
            for (var_info const& vi : m_vars) {
                IF_VERBOSE(0, verbose_stream() << "flips: " << i << " " << vi.m_flips << " " << vi.m_slow_break  << "\n");               
                ++i;
            }
        }
        st.update("local-search-flips", m_stats.m_num_flips);
        st.update("local-search-restarts", m_stats.m_num_restarts);
    }


    void local_search::set_phase(bool_var v, bool f) {
        unsigned& bias = m_vars[v].m_bias;
        if (f  && bias < 100) bias++;
        if (!f && bias > 0) bias--;
    }

    void local_search::set_bias(bool_var v, lbool f) {
        switch (f) {
        case l_true: m_vars[v].m_bias = 99; break;
        case l_false: m_vars[v].m_bias = 1; break;
        default: break;
        }

    }

}
