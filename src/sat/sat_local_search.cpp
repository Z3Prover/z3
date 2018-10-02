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

        for (unsigned i = 0; i < m_assumptions.size(); ++i) {
            add_clause(1, m_assumptions.c_ptr() + i);
        }

        // add sentinel variable.
        m_vars.push_back(var_info());

        if (m_config.phase_sticky()) {
            for (var_info& vi : m_vars)
                if (!vi.m_unit) 
                    vi.m_value = vi.m_bias < 100;
        }
        else {
            for (var_info& vi : m_vars) 
                if (!vi.m_unit)
                    vi.m_value = (0 == (m_rand() % 2));
        }

        m_best_solution.resize(num_vars() + 1, false);
        m_index_in_unsat_stack.resize(num_constraints(), 0);
        coefficient_in_ob_constraint.resize(num_vars() + 1, 0);

        if (m_config.mode() == local_search_mode::gsat) {
            uint_set is_neighbor;
            for (bool_var v = 0; v < num_vars(); ++v) {
                is_neighbor.reset();
                bool pol = true;
                var_info& vi = m_vars[v];
                for (unsigned k = 0; k < 2; pol = !pol, k++) { 
                    for (auto const& wi : m_vars[v].m_watch[pol]) {
                        constraint const& c = m_constraints[wi.m_constraint_id];
                        for (literal lit : c) {
                            bool_var w = lit.var(); 
                            if (w == v || is_neighbor.contains(w)) continue;
                            is_neighbor.insert(w);
                            vi.m_neighbors.push_back(w);
                        }
                    }
                }
            }
        }

        for (auto const& c : ob_constraint) {
            coefficient_in_ob_constraint[c.var_id] = c.coefficient;
        }

        set_parameters();
    }

    void local_search::init_cur_solution() {
        for (var_info& vi : m_vars) {
            // use bias with a small probability
            if (!vi.m_unit) {
                if (m_rand() % 10 < 5 || m_config.phase_sticky()) {
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
                //SASSERT(falsep[i].m_coeff == 1);
                // will --slack
                if (c.m_slack <= 0) {
                    dec_slack_score(v);
                    if (c.m_slack == 0)
                        dec_score(v);
                }
            }
            for (auto const& coeff : truep) {
                //SASSERT(coeff.m_coeff == 1);
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

        IF_VERBOSE(1, verbose_stream() << "(sat-local-search reinit)\n";);
        if (true || !m_is_pb) {
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
        m_vars.back().m_cscc = 0;
        m_vars.back().m_time_stamp = m_max_steps + 1;
        for (unsigned i = 0; i < num_vars(); ++i) {
            m_vars[i].m_time_stamp = 0;
            m_vars[i].m_cscc = 1;
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
            for (literal lit : m_prop_queue) {
                VERIFY(is_true(lit));
                add_unit(lit);
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
        if (m_best_unsat == 1) {
            constraint const& c = m_constraints[m_unsat_stack[0]];
            IF_VERBOSE(2, display(verbose_stream() << "single unsat:", c));
        }
    }
    
    void local_search::calculate_and_update_ob() {
        unsigned i, v;
        int objective_value = 0;
        for (i = 0; i < ob_constraint.size(); ++i) {
            v = ob_constraint[i].var_id;
            if (cur_solution(v))
                objective_value += ob_constraint[i].coefficient;
        }
        if (objective_value > m_best_objective_value) {
            m_best_solution.reset();
            for (unsigned v = 0; v < num_vars(); ++v) {
                m_best_solution.push_back(cur_solution(v));
            }
            m_best_objective_value = objective_value;
        }
    }

    bool local_search::all_objectives_are_met() const {
        for (unsigned i = 0; i < ob_constraint.size(); ++i) {
            bool_var v = ob_constraint[i].var_id;            
            if (!cur_solution(v)) return false;
        }
        return true;
    }
    
    void local_search::verify_solution() const {
        IF_VERBOSE(0, verbose_stream() << "verifying solution\n");
        for (constraint const& c : m_constraints) 
            verify_constraint(c);
    }

    void local_search::verify_unsat_stack() const {        
        for (unsigned i : m_unsat_stack) {
            constraint const& c = m_constraints[i];
            VERIFY(c.m_k < constraint_value(c));
        }
    }

    unsigned local_search::constraint_coeff(constraint const& c, literal l) const {
        for (auto const& pb : m_vars[l.var()].m_watch[is_pos(l)]) {
            if (pb.m_constraint_id == c.m_id) return pb.m_coeff;
        }
        UNREACHABLE();
        return 0;
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

    void local_search::verify_constraint(constraint const& c) const {
        unsigned value = constraint_value(c);
        IF_VERBOSE(11, display(verbose_stream() << "verify ", c););
        TRACE("sat", display(verbose_stream() << "verify ", c););
        if (c.m_k < value) {
            IF_VERBOSE(0, display(verbose_stream() << "violated constraint: ", c) << "value: " << value << "\n";);
        }
    }
    
    void local_search::add_clause(unsigned sz, literal const* c) {
        add_cardinality(sz, c, sz - 1);
    }

    // ~c <= k
    void local_search::add_cardinality(unsigned sz, literal const* c, unsigned k) {
        if (sz == 1 && k == 0) {
            add_unit(c[0]);
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
            add_unit(~c[0]);
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

    void local_search::add_unit(literal lit) {
        bool_var v = lit.var();
        if (is_unit(lit)) return;
        VERIFY(!m_units.contains(v));
        m_vars[v].m_bias  = lit.sign() ? 0 : 100;
        m_vars[v].m_value = !lit.sign();
        m_vars[v].m_unit  = true;
        m_units.push_back(v);
        verify_unsat_stack();
    }

    local_search::local_search() :         
        m_is_unsat(false),
        m_par(nullptr) {
    }

    void local_search::import(solver& s, bool _init) {        
        m_is_pb = false;
        m_vars.reset();
        m_constraints.reset();
        m_units.reset();
        m_unsat_stack.reset();

        m_vars.reserve(s.num_vars());
        if (m_config.phase_sticky()) {
            unsigned v = 0;
            for (var_info& vi : m_vars) {
                if (!vi.m_unit) 
                    vi.m_bias = s.m_phase[v] == POS_PHASE ? 100 : 0;
                ++v;
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
    
    void local_search::add_soft(bool_var v, int weight) {
        ob_constraint.push_back(ob_term(v, weight));
    }

    lbool local_search::check() {
        return check(0, nullptr);
    }

#define PROGRESS(tries, flips)                                          \
    if (tries % 10 == 0 || m_unsat_stack.empty()) {                     \
        IF_VERBOSE(1, verbose_stream() << "(sat-local-search"           \
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
        timer timer;
        timer.start();
        unsigned step = 0, total_flips = 0, tries = 0;
        PROGRESS(tries, total_flips);
        
        for (tries = 1; !m_unsat_stack.empty() && m_limit.inc(); ++tries) {
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
            if (m_par && m_par->get_phase(*this)) {
                reinit();
            }
            if (tries % 10 == 0 && !m_unsat_stack.empty()) {
                reinit();
            }            
        }
    }

    void local_search::gsat() {
        reinit();
        bool_var flipvar;
        timer timer;
        timer.start();
        unsigned tries, step = 0, total_flips = 0;
        for (tries = 1; m_limit.inc() && !m_unsat_stack.empty(); ++tries) {
            reinit();
            for (step = 1; step <= m_max_steps; ) {
                // feasible
                if (m_unsat_stack.empty()) {
                    calculate_and_update_ob();
                    if (m_best_objective_value >= m_best_known_value) {
                        break;
                    }
                }          
                if (m_unsat_stack.size() < m_best_unsat) {
                    set_best_unsat();
                }
                flipvar = pick_var_gsat();
                flip_gsat(flipvar);
                m_vars[flipvar].m_time_stamp = step++;
            }
            total_flips += step;
            PROGRESS(tries, total_flips);

            // tell the SAT solvers about the phase of variables.
            if (m_par && tries % 10 == 0) {
                m_par->get_phase(*this);
            }
        }
    }
    
    lbool local_search::check(unsigned sz, literal const* assumptions, parallel* p) {
        flet<parallel*> _p(m_par, p);
        m_model.reset();
        m_assumptions.reset();
        m_assumptions.append(sz, assumptions);
        init();

        switch (m_config.mode()) {
        case local_search_mode::gsat:
            gsat();
            break;
        case local_search_mode::wsat:
            walksat();
            break;
        }


        // remove unit clauses from assumptions.
        m_constraints.shrink(num_constraints() - sz);

        TRACE("sat", display(tout););

        lbool result;
        if (m_is_unsat) {
            // result = l_false;
            result = l_undef;
        }
        else if (m_unsat_stack.empty() && all_objectives_are_met()) {
            verify_solution();
            extract_model();
            result = l_true;
        }
        else {
            result = l_undef;
        }
        IF_VERBOSE(1, verbose_stream() << "(sat-local-search " << result << ")\n";);
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

    void local_search::pick_flip_walksat() {
    reflip:
        bool_var best_var = null_bool_var;
        unsigned n = 1;
        bool_var v = null_bool_var;
        unsigned num_unsat = m_unsat_stack.size();
        constraint const& c = m_constraints[m_unsat_stack[m_rand() % m_unsat_stack.size()]];
        // VERIFY(c.m_k < constraint_value(c));
        unsigned reflipped = 0;
        bool is_core = m_unsat_stack.size() <= 10;
        // TBD: dynamic noise strategy 
        //if (m_rand() % 100 < 98) {
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
            add_unit(~lit);
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
        VERIFY(!is_unit(flipvar));
        m_vars[flipvar].m_value = !cur_solution(flipvar);

        bool flip_is_true = cur_solution(flipvar);
        coeff_vector const& truep = m_vars[flipvar].m_watch[flip_is_true];
        coeff_vector const& falsep = m_vars[flipvar].m_watch[!flip_is_true];

        for (auto const& pbc : truep) {
            unsigned ci = pbc.m_constraint_id;
            constraint& c = m_constraints[ci];
            int old_slack = c.m_slack;
            c.m_slack -= pbc.m_coeff;
            if (c.m_slack < 0 && old_slack >= 0) { // from non-negative to negative: sat -> unsat
                unsat(ci);
            }
        }
        for (auto const& pbc : falsep) {
            unsigned ci = pbc.m_constraint_id;
            constraint& c = m_constraints[ci];
            int old_slack = c.m_slack;
            c.m_slack += pbc.m_coeff;
            if (c.m_slack >= 0 && old_slack < 0) { // from negative to non-negative: unsat -> sat
                sat(ci);
            }
        }
        
        // verify_unsat_stack();
    }

    void local_search::flip_gsat(bool_var flipvar) {
        // already changed truth value!!!!
        m_vars[flipvar].m_value = !cur_solution(flipvar);

        unsigned v;
        int org_flipvar_score = score(flipvar);
        int org_flipvar_slack_score = slack_score(flipvar);

        bool flip_is_true = cur_solution(flipvar);
        coeff_vector& truep = m_vars[flipvar].m_watch[flip_is_true];
        coeff_vector& falsep = m_vars[flipvar].m_watch[!flip_is_true];

        // update related clauses and neighbor vars
        for (unsigned i = 0; i < truep.size(); ++i) {
            constraint & c = m_constraints[truep[i].m_constraint_id];
            //++true_terms_count[c];
            --c.m_slack;
            switch (c.m_slack) {
            case -2:  // from -1 to -2
                for (literal l : c) {
                    v = l.var();
                    // flipping the slack increasing var will no longer satisfy this constraint
                    if (is_true(l)) {
                        //score[v] -= constraint_weight[c];
                        dec_score(v);
                    }
                }
                break;
            case -1: // from 0 to -1: sat -> unsat
                for (literal l : c) {
                    v = l.var();
                    inc_cscc(v);
                    //score[v] += constraint_weight[c];
                    inc_score(v);
                    // slack increasing var
                    if (is_true(l))
                        inc_slack_score(v);
                }
                unsat(truep[i].m_constraint_id);
                break;
            case 0: // from 1 to 0
                for (literal l : c) {
                    v = l.var();
                    // flip the slack decreasing var will falsify this constraint
                    if (is_false(l)) {
                        // score[v] -= constraint_weight[c];
                        dec_score(v);
                        dec_slack_score(v);
                    }
                }
                break;
            default:
                break;
            }
        }
        for (pbcoeff const& f : falsep) {
            constraint& c = m_constraints[f.m_constraint_id];
            //--true_terms_count[c];
            ++c.m_slack;
            switch (c.m_slack) {
            case 1: // from 0 to 1
                for (literal l : c) {
                    v = l.var();
                    // flip the slack decreasing var will no long falsify this constraint
                    if (is_false(l)) {
                        //score[v] += constraint_weight[c];
                        inc_score(v);
                        inc_slack_score(v);
                    }
                }
                break;
            case 0: // from -1 to 0: unsat -> sat
                for (literal l : c) {
                    v = l.var();
                    inc_cscc(v);
                    //score[v] -= constraint_weight[c];
                    dec_score(v);
                    // slack increasing var no longer sat this var
                    if (is_true(l))
                        dec_slack_score(v);
                }
                sat(f.m_constraint_id);
                break;
            case -1: // from -2 to -1
                for (literal l : c) {
                    v = l.var();
                    // flip the slack increasing var will satisfy this constraint
                    if (is_true(l)) {
                        //score[v] += constraint_weight[c];
                        inc_score(v);
                    }
                }
                break;
            default:
                break;
            }
        }
        m_vars[flipvar].m_score = -org_flipvar_score;
        m_vars[flipvar].m_slack_score = -org_flipvar_slack_score;
        m_vars[flipvar].m_conf_change = false;
        m_vars[flipvar].m_cscc = 0;

        /* update CCD */
        // remove the vars no longer goodvar in goodvar stack
        for (unsigned i = m_goodvar_stack.size(); i > 0;) {
            --i;
            v = m_goodvar_stack[i];
            if (score(v) <= 0) {
                m_goodvar_stack[i] = m_goodvar_stack.back();
                m_goodvar_stack.pop_back();
                m_vars[v].m_in_goodvar_stack = false;
            }
        }
        // update all flipvar's neighbor's conf_change to true, add goodvar/okvar

        var_info& vi = m_vars[flipvar];
        for (auto v : vi.m_neighbors) {
            m_vars[v].m_conf_change = true;
            if (score(v) > 0 && !already_in_goodvar_stack(v)) {
                m_goodvar_stack.push_back(v);
                m_vars[v].m_in_goodvar_stack = true;
            }
        }
    }

    bool local_search::tie_breaker_sat(bool_var v, bool_var best_var)  {
        // most improvement on objective value
        int v_imp = cur_solution(v) ? -coefficient_in_ob_constraint.get(v, 0) : coefficient_in_ob_constraint.get(v, 0);
        int b_imp = cur_solution(best_var) ? -coefficient_in_ob_constraint.get(best_var, 0) : coefficient_in_ob_constraint.get(best_var, 0);
        // std::cout << v_imp << "\n";
        // break tie 1: max imp
        // break tie 2: conf_change
        // break tie 3: time_stamp
        
        return 
            (v_imp > b_imp) ||
            ((v_imp == b_imp) && 
             ((conf_change(v) && !conf_change(best_var)) ||
              ((conf_change(v) == conf_change(best_var)) && 
               (time_stamp(v) < time_stamp(best_var)))));
    }

    bool local_search::tie_breaker_ccd(bool_var v, bool_var best_var)  {
        // break tie 1: max score
        // break tie 2: max slack_score
        // break tie 3: cscc
        // break tie 4: oldest one
        return 
            ((score(v) > score(best_var)) ||
             ((score(v) == score(best_var)) &&
              ((slack_score(v) > slack_score(best_var)) ||
               ((slack_score(v) == slack_score(best_var)) &&
                ((cscc(v) > cscc(best_var)) ||
                 ((cscc(v) == cscc(best_var)) && 
                  (time_stamp(v) < time_stamp(best_var))))))));
    }

    bool_var local_search::pick_var_gsat() {
        bool_var best_var = m_vars.size()-1;  // sentinel variable
        // SAT Mode
        if (m_unsat_stack.empty()) {
            //std::cout << "as\t";
            for (auto const& c : ob_constraint) {
                bool_var v = c.var_id;
                if (tie_breaker_sat(v, best_var))
                    best_var = v;
            }
            return best_var;
        }

        // Unsat Mode: CCD > RD
        // CCD mode
        if (!m_goodvar_stack.empty()) {
            //++ccd;
            best_var = m_goodvar_stack[0];
            for (bool_var v : m_goodvar_stack) {
                if (tie_breaker_ccd(v, best_var))
                    best_var = v;
            }
            return best_var;
        }

        // Diversification Mode
        constraint const& c = m_constraints[m_unsat_stack[m_rand() % m_unsat_stack.size()]]; // a random unsat constraint
        // Within c, from all slack increasing var, choose the oldest one
        for (literal l : c) {
            bool_var v = l.var();
            if (is_true(l) && time_stamp(v) < time_stamp(best_var))
                best_var = v;
        }
        return best_var;
    }

    void local_search::set_parameters()  {
        m_rand.set_seed(m_config.random_seed());
        m_best_known_value = m_config.best_known_value();

        switch (m_config.mode()) {
        case local_search_mode::gsat:
            m_max_steps = 2 * num_vars();
            break;
        case local_search_mode::wsat:
            m_max_steps = std::min(static_cast<unsigned>(20 * num_vars()), static_cast<unsigned>(1 << 17)); // cut steps off at 100K
            break;
        }

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
        return out << "v" << v << " := " << (vi.m_value?"true":"false") << " bias: " << vi.m_bias << "\n";
    }

    bool local_search::check_goodvar() {
        unsigned g = 0;
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (conf_change(v) && score(v) > 0) {
                ++g;
                if (!already_in_goodvar_stack(v))
                    std::cout << "3\n";
            }
        }
        if (g == m_goodvar_stack.size())
            return true;
        else {
            if (g < m_goodvar_stack.size())
                std::cout << "1\n";
            else
                std::cout << "2\n"; // delete too many
            return false;
        }
    }

    void local_search::set_phase(bool_var v, lbool f) {
        unsigned& bias = m_vars[v].m_bias;
        if (f == l_true && bias < 100) bias++;
        if (f == l_false && bias > 0) bias--;
        // f == l_undef ?
    }

}
