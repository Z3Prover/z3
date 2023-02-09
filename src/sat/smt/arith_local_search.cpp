/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_local_search.cpp

Abstract:

    Local search dispatch for SMT

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

--*/
#include "sat/sat_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {
    

    ///
    /// need access to clauses
    /// need access to m_unsat
    /// need update of phase
    /// need to initialize ineqs (arithmetical atoms)
    /// 
    
    solver::sls::sls(solver& s): 
        s(s), m(s.m) {}

    void solver::sls::operator()(bool_vector& phase) {
        
        // need to init variables/atoms/ineqs

        m.limit().push(m_max_arith_steps);
        m_best_min_unsat = unsat().size();
        unsigned num_steps = 0;
        while (m.inc() && m_best_min_unsat > 0 && num_steps < m_max_arith_steps) {
            if (!flip())
                return;
            ++m_stats.m_num_flips;
            ++num_steps;
            unsigned num_unsat = unsat().size();
            if (num_unsat < m_best_min_unsat) {
                m_best_min_unsat = num_unsat;
                num_steps = 0;
                save_best_values();
            }
        }
    }

    void solver::sls::set_bounds_begin() {
        m_max_arith_steps = 0;
    }

    void solver::sls::set_bounds_end(unsigned num_literals) {
        // m_max_arith_steps = s.ctx.m_sl_config.L *
    }

    void solver::sls::set_bounds(enode* n) {
        ++m_max_arith_steps;
    }

    bool solver::sls::flip() {
        log();
        if (flip_unsat())
            return true;
        if (flip_clauses())
            return true;
        if (flip_dscore())
            return true;
        return false;
    }

    // distance to true
    rational solver::sls::dtt(rational const& args, ineq const& ineq) const {
        switch (ineq.m_op) {
        case ineq_kind::LE:
            if (args <= ineq.m_bound)
                return rational::zero();
            return args - ineq.m_bound;
        case ineq_kind::EQ:
            if (args == ineq.m_bound)
                return rational::zero();
            return rational::one();
        case ineq_kind::NE:
            if (args == ineq.m_bound)
                return rational::one();
            return rational::zero();
        case ineq_kind::LT:
        default:
            if (args < ineq.m_bound)
                return rational::zero();
            return args - ineq.m_bound + 1;
        }
    }

    rational solver::sls::dtt(ineq const& ineq, var_t v, rational const& new_value) const {
        auto new_args_value = ineq.m_args_value;
        for (auto const& [coeff, w] : ineq.m_args) {
            if (w == v) {
                new_args_value += coeff * (new_value - m_vars[w].m_value);
                break;
            }
        }
        return dtt(new_args_value, ineq);
    }

    // critical move
    bool solver::sls::cm(ineq const& ineq, var_t v, rational& new_value) {
        SASSERT(!ineq.is_true());
        auto delta = ineq.m_args_value - ineq.m_bound;
        for (auto const& [coeff, w] : ineq.m_args) {
            if (w == v) {
                if (coeff > 0)
                    new_value = value(v) - abs(ceil(delta / coeff));
                else
                    new_value = value(v) + abs(floor(delta / coeff));
                switch (ineq.m_op) {
                case ineq_kind::LE:
                    SASSERT(delta + coeff * (new_value - value(v)) <= 0);
                    return true;
                case ineq_kind::EQ:
                    return delta + coeff * (new_value - value(v)) == 0;
                case ineq_kind::NE:
                    return delta + coeff * (new_value - value(v)) != 0;
                case ineq_kind::LT:
                    return delta + coeff * (new_value - value(v)) < 0;
                default:
                    UNREACHABLE(); break;
                }
            }
        }
        return false;
    }

    bool solver::sls::flip_unsat() {
        unsigned start = s.random();
        unsigned sz = unsat().size();
        for (unsigned i = sz; i-- > 0; ) {
            unsigned cl = unsat().elem_at((i + start) % sz);
            if (flip(cl))
                return true;
        }
        return false;
    }


    bool solver::sls::flip(unsigned cl) {
        auto const& clause = get_clause(cl);
        rational new_value;
        for (literal lit : clause) {
            auto const* ai = atom(lit);
            if (!ai)
                continue;
            ineq const& ineq = ai->m_ineq;
            for (auto const& [coeff, v] : ineq.m_args) {
                if (!ineq.is_true() && cm(ineq, v, new_value)) {
                    int score = cm_score(v, new_value);
                    if (score <= 0)
                        continue;
                    unsigned num_unsat = unsat().size();
                    update(v, new_value);
                    IF_VERBOSE(0,
                        verbose_stream() << "score " << v << " " << score << "\n"
                                         << num_unsat << " -> " << unsat().size() << "\n");
                    return true;
                }
            }
        }
        return false;
    }

    bool solver::sls::flip_clauses() {
        unsigned start = s.random();
        for (unsigned i = num_clauses(); i-- > 0; )
            if (flip((i + start) % num_clauses()))
                return true;
        return false;
    }

    bool solver::sls::flip_dscore() {
        paws();
        unsigned start = s.random();
        for (unsigned i = unsat().size(); i-- > 0; ) {
            unsigned cl = unsat().elem_at((i + start) % unsat().size());
            if (flip_dscore(cl))
                return true;
        }
        IF_VERBOSE(2, verbose_stream() << "(sls " << m_stats.m_num_flips << " " << unsat().size() << ")\n");
        return false;
    }

    bool solver::sls::flip_dscore(unsigned cl) {
        auto const& clause = get_clause(cl);
        rational new_value, min_value, min_score(-1);
        var_t min_var = UINT_MAX;
        for (auto lit : clause) {
            auto const* ai = atom(lit);
            if (!ai)
                continue;
            ineq const& ineq = ai->m_ineq;
            for (auto const& [coeff, v] : ineq.m_args) {
                if (!ineq.is_true() && cm(ineq, v, new_value)) {
                    rational score = dscore(v, new_value);
                    if (UINT_MAX == min_var || score < min_score) {
                        min_var = v;
                        min_value = new_value;
                        min_score = score;
                    }
                }
            }
        }
        if (min_var != UINT_MAX) {
            update(min_var, min_value);
            return true;
        }
        return false;
    }

    void solver::sls::paws() {
        for (unsigned cl = num_clauses(); cl-- > 0; ) {
            auto& clause = get_clause_info(cl);
            bool above = 10000 * m_config.sp <= (s.random() % 10000);
            if (!above && clause.is_true() && clause.m_weight > 1)
                clause.m_weight -= 1;
            if (above && !clause.is_true())
                clause.m_weight += 1;
        }
    }

    //
    // dscore(op) = sum_c (dts(c,alpha) - dts(c,alpha_after)) * weight(c)
    // 
    rational solver::sls::dscore(var_t v, rational const& new_value) const {
        auto const& vi = m_vars[v];
        rational score(0);
        for (auto const& [coeff, atm] : vi.m_atoms) {
            auto const& ai = *m_atoms[atm];
            auto const& cl = get_clause_info(ai.m_clause_idx);
            // score += (dts(cl) - dts(cl, v, new_value)) * rational(cl.m_weight);
        }
        return score;
    }

    int solver::sls::cm_score(var_t v, rational const& new_value) {
        int score = 0;
        auto& vi = m_vars[v];
        for (auto const& [coeff, atm] : vi.m_atoms) {
            auto const& ai = *m_atoms[atm];
            auto const& clause = get_clause_info(ai.m_clause_idx);
            rational dtt_old = dtt(ai.m_ineq);
            rational dtt_new = dtt(ai.m_ineq, v, new_value);
            if (!clause.is_true()) {
                if (dtt_new == 0)
                    ++score;
            }
            else if (dtt_new == 0 || dtt_old > 0 || clause.m_num_trues > 0)
                continue;
            else {
                bool has_true = false;
                for (auto lit : *clause.m_clause) {
                    if (!atom(lit))
                        continue;
                    auto const& ai = *atom(lit);
                    rational d = dtt(ai.m_ineq, v, new_value);
                    has_true |= (d == 0);
                }
                if (!has_true)
                    --score;
            }
        }
        return score;
    }

    rational solver::sls::dts(unsigned cl) const {
        rational d(1), d2;
        bool first = true;
        for (auto a : get_clause(cl)) {
            auto const* ai = atom(a);
            if (!ai)
                continue;
            d2 = dtt(ai->m_ineq);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    rational solver::sls::dts(unsigned cl, var_t v, rational const& new_value) const {
        rational d(1), d2;
        bool first = true;
        for (auto lit : get_clause(cl)) {
            auto const* ai = atom(lit);
            if (!ai)
                continue;
            d2 = dtt(ai->m_ineq, v, new_value);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    void solver::sls::update(var_t v, rational const& new_value) {
        auto& vi = m_vars[v];
        auto const& old_value = vi.m_value;
        for (auto const& [coeff, atm] : vi.m_atoms) {
            auto& ai = *m_atoms[atm];
            SASSERT(!ai.m_is_bool);
            auto& clause = get_clause_info(ai.m_clause_idx);
            rational dtt_old = dtt(ai.m_ineq);
            ai.m_ineq.m_args_value += coeff * (new_value - old_value);
            rational dtt_new = dtt(ai.m_ineq);
            bool was_true = clause.is_true();
            auto& dts_value = dts(ai.m_clause_idx);
            if (dtt_new < dts_value) {
                if (was_true && dts_value > 0 && dtt_new == 0 && 1 == clause.m_num_trues) {
                    for (auto lit : *clause.m_clause) {
#if false
                        TODO
                        if (is_true(lit)) {
                            dec_break(lit);
                            break;
                        }
#endif
                    }
                }
                dts_value = dtt_new;
                if (!was_true && clause.is_true())
                    unsat().remove(ai.m_clause_idx);
            }
            else if (dts_value == dtt_old && dtt_old < dtt_new) {
                dts_value = dts(ai.m_clause_idx);
                if (was_true && !clause.is_true())
                    unsat().insert(ai.m_clause_idx);
                if (was_true && clause.is_true() && dts_value > 0 && dtt_old == 0 && 1 == clause.m_num_trues) {
                    for (auto lit : *clause.m_clause) {
#if false
                        TODO
                        if (is_true(lit)) {
                            inc_break(lit);
                            break;
                        }
#endif
                    }
                }
            }
            SASSERT(dts_value >= 0);
        }
        vi.m_value = new_value;
    }

#if 0






    void solver::sls::add_clause(sat::clause* cl) {
        unsigned clause_idx = m_clauses.size();
        m_clauses.push_back({ cl, 1, rational::zero() });
        clause& cls = m_clauses.back();
        cls.m_dts = dts(cls);
        for (sat::literal lit : *cl) {
            if (is_true(lit))
                cls.add(lit);
        }

        for (auto a : arith)
            m_atoms[a].m_clause_idx = clause_idx;

        if (!cl.is_true()) {
            m_best_min_unsat++;
            m_unsat.insert(clause_idx);
        }
        else if (cl.m_dts > 0 && cl.m_num_trues == 1)
            inc_break(sat::to_literal(cl.m_trues));

    }


#endif
}

