/*++
Copyright (c) 2023 Microsoft Corporation

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
    
    sls::sls(solver& s): 
        s(s), m(s.m) {}

    void sls::reset() {
        m_literals.reset();
        m_vars.reset();
        m_terms.reset();
    }

    void sls::log() {
        IF_VERBOSE(2, verbose_stream() << "(sls :flips " << m_stats.m_num_flips << " :unsat " << unsat().size() << ")\n");
    }

    void sls::save_best_values() {
        for (unsigned v = 0; v < s.get_num_vars(); ++v)
            m_vars[v].m_best_value = m_vars[v].m_value;
    }

    void sls::store_best_values() {
        // first compute assignment to terms
        // then update non-basic variables in tableau.
        for (auto const& [t, v] : m_terms) {
            int64_t val = 0;
            lp::lar_term const& term = s.lp().get_term(t);
            for (lp::lar_term::ival arg : term) {
                auto t2 = s.lp().column2tv(arg.column());
                auto w = s.lp().local_to_external(t2.id());
                val += to_numeral(arg.coeff()) * value(w);
            }
            update(v, val);
        }

        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            if (s.is_bool(v))
                continue;
            if (!s.lp().external_is_used(v))
                continue;
            int64_t old_value = 0;
            if (s.is_registered_var(v))
                old_value = to_numeral(s.get_ivalue(v).x);
            int64_t new_value = m_vars[v].m_best_value;
            if (old_value == new_value)
                continue;
            s.ensure_column(v);
            lp::column_index vj = s.lp().to_column_index(v);
            SASSERT(!vj.is_null());
            if (!s.lp().is_base(vj.index())) {
                rational new_value_(new_value, rational::i64());
                lp::impq val(new_value_, rational::zero());
                s.lp().set_value_for_nbasic_column(vj.index(), val);
                // TODO - figure out why this leads to unsound (unsat).
            }
        }
    }

    void sls::set(sat::ddfw* d) { 
        m_bool_search = d; 
        reset();
        m_literals.reserve(s.s().num_vars() * 2);
        add_vars();
        for (unsigned i = 0; i < d->num_clauses(); ++i)
            for (sat::literal lit : *d->get_clause_info(i).m_clause)
                init_literal(lit);
        for (unsigned v = 0; v < s.s().num_vars(); ++v)
            init_bool_var_assignment(v);
        m_best_min_unsat = std::numeric_limits<unsigned>::max();

        d->set(this);
    }


    // distance to true
    int64_t sls::dtt(int64_t args, ineq const& ineq) const {
        switch (ineq.m_op) {
        case ineq_kind::LE:
            if (args <= ineq.m_bound)
                return 0;
            return args - ineq.m_bound;
        case ineq_kind::EQ:
            if (args == ineq.m_bound)
                return 0;
            return 1;
        case ineq_kind::NE:
            if (args == ineq.m_bound)
                return 1;
            return 0;
        case ineq_kind::LT:
            if (args < ineq.m_bound)
                return 0;
            return args - ineq.m_bound + 1;
        default:
            UNREACHABLE();
            return 0;
        }
    }

    //
    // dtt is high overhead. It walks ineq.m_args
    // m_vars[w].m_value can be computed outside and shared among calls
    // different data-structures for storing coefficients
    // 
    int64_t sls::dtt(ineq const& ineq, var_t v, int64_t new_value) const {
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
    bool sls::cm(ineq const& ineq, var_t v, int64_t& new_value) {
        SASSERT(!ineq.is_true());
        int64_t delta = ineq.m_args_value - ineq.m_bound;
        if (ineq.m_op == ineq_kind::NE || ineq.m_op == ineq_kind::LT)
            delta--;
        for (auto const& [coeff, w] : ineq.m_args) {
            if (w == v) {

                if (coeff > 0)
                    new_value = value(v) - abs((delta + coeff - 1)/ coeff);
                else
                    new_value = value(v) + abs(delta) / -coeff;

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
                    UNREACHABLE(); 
                    break;
                }
            }
        }
        return false;
    }

    // flip on the first positive score
    // it could be changed to flip on maximal positive score
    // or flip on maximal non-negative score
    // or flip on first non-negative score
    bool sls::flip(ineq const& ineq) {
        int64_t new_value;
        for (auto const& [coeff, v] : ineq.m_args) {
            if (!cm(ineq, v, new_value))
                continue;
            int score = cm_score(v, new_value);
            if (score <= 0)
                continue;
            unsigned num_unsat = unsat().size();
            update(v, new_value);
            IF_VERBOSE(2,
                verbose_stream() << "v" << v << " score " << score << " "
                << num_unsat << " -> " << unsat().size() << "\n");
            SASSERT(num_unsat > unsat().size());
            return true;
        }
        return false;
    }

    //
    // dscore(op) = sum_c (dts(c,alpha) - dts(c,alpha_after)) * weight(c)
    // TODO - use cached dts instead of computed dts
    // cached dts has to be updated when the score of literals are updated.
    // 
    double sls::dscore(var_t v, int64_t new_value) const {
        auto const& vi = m_vars[v];
        double score = 0;
        for (auto const& [coeff, lit] : vi.m_literals) 
            for (auto cl : m_bool_search->get_use_list(lit))              
                score += (compute_dts(cl) - dts(cl, v, new_value)) * m_bool_search->get_weight(cl);        
        return score;
    }

    //
    // cm_score is costly. It involves several cache misses.
    // Note that
    // - m_bool_search->get_use_list(lit).size() is "often" 1 or 2
    // - dtt_old can be saved
    //
    int sls::cm_score(var_t v, int64_t new_value) {
        int score = 0;
        auto& vi = m_vars[v];
        int64_t old_value = vi.m_value;
        for (auto const& [coeff, lit] : vi.m_literals) {
            auto const& ineq = *atom(lit);            
            int64_t dtt_old = dtt(ineq);
            int64_t delta = coeff * (new_value - old_value);
            int64_t dtt_new = dtt(ineq.m_args_value + delta, ineq);

            if (dtt_old == dtt_new)
                continue;
            
            for (auto cl : m_bool_search->get_use_list(lit)) {
                auto const& clause = get_clause_info(cl);
                if (!clause.is_true()) {
                    VERIFY(dtt_old != 0);
                    if (dtt_new == 0)
                        ++score;  // false -> true
                }
                else if (dtt_new == 0 || dtt_old > 0 || clause.m_num_trues > 1) // true -> true not really, same variable can be in multiple literals
                    continue;
                else if (all_of(*clause.m_clause, [&](auto lit2) { return !atom(lit2) || dtt(*atom(lit2), v, new_value) > 0; })) // ?? TODO
                    --score;
            }
        }
        return score;
    }

    int64_t sls::compute_dts(unsigned cl) const {
        int64_t d(1), d2;
        bool first = true;
        for (auto a : get_clause(cl)) {
            auto const* ineq = atom(a);
            if (!ineq)
                continue;
            d2 = dtt(*ineq);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    int64_t sls::dts(unsigned cl, var_t v, int64_t new_value) const {
        int64_t d(1), d2;
        bool first = true;
        for (auto lit : get_clause(cl)) {
            auto const* ineq = atom(lit);
            if (!ineq)
                continue;
            d2 = dtt(*ineq, v, new_value);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    void sls::update(var_t v, int64_t new_value) {
        auto& vi = m_vars[v];
        auto const& old_value = vi.m_value;
        for (auto const& [coeff, lit] : vi.m_literals) {
            auto& ineq = *atom(lit);
            ineq.m_args_value += coeff * (new_value - old_value);
            int64_t dtt_new = dtt(ineq);
            if ((dtt_new == 0) != is_true(lit)) 
                m_bool_search->flip(lit.var());
                                                 
            SASSERT((dtt_new == 0) == is_true(lit));
        }
        vi.m_value = new_value;
    }

    void sls::add_vars() {
        SASSERT(m_vars.empty());
        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            int64_t value = s.is_registered_var(v)  ? to_numeral(s.get_ivalue(v).x) : 0;
            auto k = s.is_int(v) ? sls::var_kind::INT : sls::var_kind::REAL;
            m_vars.push_back({ value, value, k, {} });
        }
    }

    sls::ineq& sls::new_ineq(ineq_kind op, int64_t const& bound) {
        auto* i = alloc(ineq);
        i->m_bound = bound;
        i->m_op = op;
        return *i;
    }

    void sls::add_arg(sat::literal lit, ineq& ineq, int64_t const& c, var_t v) {
        ineq.m_args.push_back({ c, v });
        ineq.m_args_value += c * value(v);
        m_vars[v].m_literals.push_back({ c, lit });
    }

    int64_t sls::to_numeral(rational const& r) {
        if (r.is_int64())
            return r.get_int64();
        return 0;
    }


    void sls::add_args(sat::literal lit, ineq& ineq, lp::tv t, theory_var v, int64_t sign) {
        if (t.is_term()) {
            lp::lar_term const& term = s.lp().get_term(t);

            for (lp::lar_term::ival arg : term) {
                auto t2 = s.lp().column2tv(arg.column());
                auto w = s.lp().local_to_external(t2.id());
                add_arg(lit, ineq, sign * to_numeral(arg.coeff()), w);
            }
        }
        else
            add_arg(lit, ineq, sign, s.lp().local_to_external(t.id()));
    }


    void sls::init_literal(sat::literal lit) {
        if (m_literals.get(lit.index(), nullptr))
            return;
        api_bound* b = nullptr;
        s.m_bool_var2bound.find(lit.var(), b);
        if (b) {
            auto t = b->tv();
            rational bound = b->get_value();
            bool should_minus = false;
            sls::ineq_kind op;
            if (!lit.sign()) {
                should_minus = b->get_bound_kind() == lp_api::bound_kind::upper_t;
                op = sls::ineq_kind::LE;
            }
            else {
                should_minus = b->get_bound_kind() == lp_api::bound_kind::lower_t;
                if (s.is_int(b->get_var())) {
                    bound -= 1;
                    op = sls::ineq_kind::LE;
                }
                else
                    op = sls::ineq_kind::LT;

            }
            if (should_minus)
                bound.neg();
            auto& ineq = new_ineq(op, to_numeral(bound));

            add_args(lit, ineq, t, b->get_var(), should_minus ? -1 : 1);
            m_literals.set(lit.index(), &ineq);
            return;
        }

        expr* e = s.bool_var2expr(lit.var());
        expr* l = nullptr, * r = nullptr;
        if (e && m.is_eq(e, l, r) && s.a.is_int_real(l)) {
            theory_var u = s.get_th_var(l);
            theory_var v = s.get_th_var(r);
            lp::tv tu = s.get_tv(u);
            lp::tv tv = s.get_tv(v);
            auto& ineq = new_ineq(lit.sign() ? sls::ineq_kind::NE : sls::ineq_kind::EQ, 0);            
            add_args(lit, ineq, tu, u, 1);
            add_args(lit, ineq, tv, v, -1);
            m_literals.set(lit.index(), &ineq);
            return;
        }
    }

    void sls::init_bool_var_assignment(sat::bool_var v) {
        init_literal_assignment(literal(v, false));
        init_literal_assignment(literal(v, true));      
    }

    void sls::init_literal_assignment(sat::literal lit) {
        auto* ineq = m_literals.get(lit.index(), nullptr);
        if (ineq && is_true(lit) != (dtt(*ineq) == 0)) 
            m_bool_search->flip(lit.var());        
    }

    void sls::init_search()  {
        on_restart();
    }

    void sls::finish_search()  {
        store_best_values();
    }

    void sls::flip(sat::bool_var v)  {
        sat::literal lit(v, m_bool_search->get_value(v));
        SASSERT(!is_true(lit));
        auto const* ineq = atom(lit);
        if (!ineq) 
            IF_VERBOSE(0, verbose_stream() << "no inequality for variable " << v << "\n");
        if (!ineq)
            return;
        IF_VERBOSE(1, verbose_stream() << "flip " << lit << "\n");
        SASSERT(!ineq->is_true());
        flip(*ineq);
    }

    double sls::reward(sat::bool_var v) {
        if (m_dscore_mode)
            return dscore_reward(v);
        else 
            return dtt_reward(v);
    }

    double sls::dtt_reward(sat::bool_var v) {
        sat::literal litv(v, m_bool_search->get_value(v));
        auto const* ineq = atom(litv);
        if (!ineq)
            return 0;
        int64_t new_value;
        double result = 0;
        for (auto const & [coeff, x] : ineq->m_args) {
            if (!cm(*ineq, x, new_value))
                continue;
            for (auto const [coeff, lit] : m_vars[x].m_literals) {
                auto dtt_old = dtt(*atom(lit));
                auto dtt_new = dtt(*atom(lit), x, new_value);
                if ((dtt_new == 0) != (dtt_old == 0))
                    result += m_bool_search->reward(lit.var());
            }
        }
        return result; 
    }

    double sls::dscore_reward(sat::bool_var x) {
        m_dscore_mode = false;
        sat::literal litv(x, m_bool_search->get_value(x));
        auto const* ineq = atom(litv);
        if (!ineq)
            return 0;
        SASSERT(!ineq->is_true());
        int64_t new_value;
        double result = 0;
        for (auto const& [coeff, v] : ineq->m_args) 
            if (cm(*ineq, v, new_value)) 
                result += dscore(v, new_value);        
        return result;
    }

    // switch to dscore mode
    void sls::on_rescale()  {
        m_dscore_mode = true;
    }

    void sls::on_save_model() {
        save_best_values();
    }

    void sls::on_restart()  {
        for (unsigned v = 0; v < s.s().num_vars(); ++v)
            init_bool_var_assignment(v);
    }
}
