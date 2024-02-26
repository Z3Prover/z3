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
        m_bool_vars.reset();
        m_vars.reset();
        m_terms.reset();
    }

    void sls::save_best_values() {
        for (unsigned v = 0; v < s.get_num_vars(); ++v)
            m_vars[v].m_best_value = m_vars[v].m_value;
        check_ineqs();   
        if (unsat().size() == 1) {
            auto idx = *unsat().begin();
            verbose_stream() << idx << "\n";
            auto const& c = *m_bool_search->m_clauses[idx].m_clause;
            verbose_stream() << c << "\n";
            for (auto lit : c) {
                bool_var bv = lit.var();
                ineq* i = atom(bv);
                if (i)
                    verbose_stream() << lit << ": " << *i << "\n";
            }
            verbose_stream() << "\n";
        }
    }

    void sls::store_best_values() {
        // first compute assignment to terms
        // then update non-basic variables in tableau.

        if (!unsat().empty())
            return;
        
        for (auto const& [t,v] : m_terms) {
            int64_t val = 0;
            lp::lar_term const& term = s.lp().get_term(t);
            for (lp::lar_term::ival const& arg : term) {
                auto t2 = arg.j();
                auto w = s.lp().local_to_external(t2);
                val += to_numeral(arg.coeff()) * m_vars[w].m_best_value;
            }
            m_vars[v].m_best_value = val;
        }

        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            if (s.is_bool(v))
                continue;
            if (!s.lp().external_is_used(v)) 
                continue;            
            int64_t new_value = m_vars[v].m_best_value;
            s.ensure_column(v);
            lp::lpvar vj = s.lp().external_to_local(v);
            SASSERT(vj  != lp::null_lpvar);
            if (!s.lp().is_base(vj)) {
                rational new_value_(new_value, rational::i64());
                lp::impq val(new_value_, rational::zero());
                s.lp().set_value_for_nbasic_column(vj, val);
            }
        }

        lbool r = s.make_feasible();
        VERIFY (!unsat().empty() || r == l_true);    
#if 0
        if (unsat().empty()) 
            s.m_num_conflicts = s.get_config().m_arith_propagation_threshold;
#endif   

        auto check_bool_var = [&](sat::bool_var bv) {
            auto* ineq = m_bool_vars.get(bv, nullptr);
            if (!ineq)
                return;
            api_bound* b = nullptr;
            s.m_bool_var2bound.find(bv, b);
            if (!b)
                return;
            auto bound = b->get_value();
            theory_var v = b->get_var();
            if (s.get_phase(bv) == m_bool_search->get_model()[bv])
                return;
            switch (b->get_bound_kind()) {
            case lp_api::lower_t:
                verbose_stream() << "v" << v << " " << bound << " <= " << s.get_value(v) << " " << m_vars[v].m_best_value << "\n";
                break;
            case lp_api::upper_t:
                verbose_stream() << "v" << v << " " << bound << " >= " << s.get_value(v) << " " << m_vars[v].m_best_value << "\n";
                break;
            }
            int64_t value = 0;
            for (auto const& [coeff, v] : ineq->m_args) {
                value += coeff * m_vars[v].m_best_value;
            }
            ineq->m_args_value = value;
            verbose_stream() << *ineq << " dtt " << dtt(false, *ineq) << " phase " << s.get_phase(bv) << " model " << m_bool_search->get_model()[bv] << "\n";
            for (auto const& [coeff, v] : ineq->m_args) 
                verbose_stream() << "v" << v << " := " << m_vars[v].m_best_value << "\n";
            s.display(verbose_stream());
            display(verbose_stream());
            UNREACHABLE();
            exit(0);
        };

        if (unsat().empty()) {
            for (bool_var v = 0; v < s.s().num_vars(); ++v) 
                check_bool_var(v);            
        }
    }

    void sls::set(sat::ddfw* d) { 
        m_bool_search = d; 
        reset();
        m_bool_vars.reserve(s.s().num_vars());
        add_vars();
        for (unsigned i = 0; i < d->num_clauses(); ++i)
            for (sat::literal lit : *d->get_clause_info(i).m_clause)
                init_bool_var(lit.var());
        for (unsigned v = 0; v < s.s().num_vars(); ++v)
            init_bool_var_assignment(v);

        d->set(this);
    }

    // distance to true
    int64_t sls::dtt(bool sign, int64_t args, ineq const& ineq) const {
        switch (ineq.m_op) {
        case ineq_kind::LE:
            if (sign) {
                if (args <= ineq.m_bound)
                    return ineq.m_bound - args + 1;
                return 0;
            }
            if (args <= ineq.m_bound)
                return 0;
            return args - ineq.m_bound;
        case ineq_kind::EQ:
            if (sign) {
                if (args == ineq.m_bound)
                    return 1;
                return 0;
            }
            if (args == ineq.m_bound)
                return 0;
            return 1;
        case ineq_kind::NE:
            if (sign) {
                if (args == ineq.m_bound)
                    return 0;
                return 1;
            }
            if (args == ineq.m_bound)
                return 1;
            return 0;
        case ineq_kind::LT:
            if (sign) {
                if (args < ineq.m_bound)
                    return ineq.m_bound - args;
                return 0;
            }
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
    int64_t sls::dtt(bool sign, ineq const& ineq, var_t v, int64_t new_value) const {
        for (auto const& [coeff, w] : ineq.m_args) 
            if (w == v)
                return dtt(sign, ineq.m_args_value + coeff * (new_value - m_vars[v].m_value), ineq);
        return 1;
    }

    int64_t sls::dtt(bool sign, ineq const& ineq, int64_t coeff, int64_t old_value, int64_t new_value) const {
        return dtt(sign, ineq.m_args_value + coeff * (new_value - old_value), ineq);
    }

    bool sls::cm(bool old_sign, ineq const& ineq, var_t v, int64_t& new_value) {
        for (auto const& [coeff, w] : ineq.m_args) 
            if (w == v)
                return cm(old_sign, ineq, v, coeff, new_value);        
        return false;
    }

    bool sls::cm(bool old_sign, ineq const& ineq, var_t v, int64_t coeff, int64_t& new_value) {
        SASSERT(ineq.is_true() != old_sign);
        VERIFY(ineq.is_true() != old_sign);
        auto bound = ineq.m_bound;
        auto argsv = ineq.m_args_value;
        bool solved = false;
        int64_t delta = argsv - bound;
        auto make_eq = [&]() {
            SASSERT(delta != 0);
            if (delta < 0)
                new_value = value(v) + (abs(delta) + abs(coeff) - 1) / coeff;
            else
                new_value = value(v) - (delta + abs(coeff) - 1) / coeff;
            solved = argsv + coeff * (new_value - value(v)) == bound;
            if (!solved && abs(coeff) == 1) {
                verbose_stream() << "did not solve equality " << ineq << " for " << v << "\n";
                verbose_stream() << new_value << " " << value(v) << " delta " << delta << " lhs " << (argsv + coeff * (new_value - value(v))) << " bound " << bound << "\n";
                UNREACHABLE();
            }
            return solved;
        };

        auto make_diseq = [&]() {
            if (delta >= 0)
                delta++;
            else
                delta--;
            new_value = value(v) + (abs(delta) + abs(coeff) - 1) / coeff;
            VERIFY(argsv + coeff * (new_value - value(v)) != bound);
            return true;
        };

        if (!old_sign) {
            switch (ineq.m_op) {                
            case ineq_kind::LE:
                // args <= bound -> args > bound
                SASSERT(argsv <= bound);
                SASSERT(delta <= 0);
                --delta;
                new_value = value(v) + (abs(delta) + abs(coeff) - 1) / coeff;
                VERIFY(argsv + coeff * (new_value - value(v)) > bound);
                return true;
            case ineq_kind::LT:
                // args < bound -> args >= bound
                SASSERT(argsv <= ineq.m_bound);
                SASSERT(delta <= 0);
                new_value = value(v) + (abs(delta) + abs(coeff) - 1) / coeff;
                VERIFY(argsv + coeff * (new_value - value(v)) >= bound);
                return true;
            case ineq_kind::EQ:
                return make_diseq();
            case ineq_kind::NE:
                return make_eq();
            default:
                UNREACHABLE();
                break;
            }
        }
        else {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                SASSERT(argsv > ineq.m_bound);
                SASSERT(delta > 0);
                new_value = value(v) - (delta + abs(coeff) - 1) / coeff;
                VERIFY(argsv + coeff * (new_value - value(v)) <= bound);
                return true;
            case ineq_kind::LT:
                SASSERT(argsv >= ineq.m_bound);
                SASSERT(delta >= 0);
                ++delta;
                new_value = value(v) - (abs(delta) + abs(coeff) - 1) / coeff;
                VERIFY(argsv + coeff * (new_value - value(v)) < bound);
                return true;
            case ineq_kind::NE:
                return make_diseq();
            case ineq_kind::EQ:
                return make_eq();
            default:
                UNREACHABLE();
                break;
            }
        }
        return false;
    }

    // flip on the first positive score
    // it could be changed to flip on maximal positive score
    // or flip on maximal non-negative score
    // or flip on first non-negative score
    bool sls::flip(bool sign, ineq const& ineq) {
        int64_t new_value;
        auto v = ineq.m_var_to_flip;
        if (v == UINT_MAX) {
            IF_VERBOSE(1, verbose_stream() << "no var to flip\n");
            return false;
        }
        if (!cm(sign, ineq, v, new_value)) {
            verbose_stream() << "no critical move for " << v << "\n";
            return false;
        }
        update(v, new_value);
        return true;
    }

    //
    // dscore(op) = sum_c (dts(c,alpha) - dts(c,alpha_after)) * weight(c)
    // TODO - use cached dts instead of computed dts
    // cached dts has to be updated when the score of literals are updated.
    // 
    double sls::dscore(var_t v, int64_t new_value) const {        
        double score = 0;
        auto const& vi = m_vars[v];
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            sat::literal lit(bv, false);
            for (auto cl : m_bool_search->get_use_list(lit))
                score += (compute_dts(cl) - dts(cl, v, new_value)) * m_bool_search->get_weight(cl);
            for (auto cl : m_bool_search->get_use_list(~lit))
                score += (compute_dts(cl) - dts(cl, v, new_value)) * m_bool_search->get_weight(cl);
        }
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
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            auto const& ineq = *atom(bv);            
            bool old_sign = sign(bv);
            int64_t dtt_old = dtt(old_sign, ineq);
            int64_t dtt_new = dtt(old_sign, ineq, coeff, old_value, new_value);
            if ((dtt_old == 0) == (dtt_new == 0))
                continue;
            sat::literal lit(bv, old_sign);
            if (dtt_old == 0) 
                // flip from true to false
                lit.neg();
                  
            // lit flips form false to true:            
            for (auto cl : m_bool_search->get_use_list(lit)) {
                auto const& clause = get_clause_info(cl);
                if (!clause.is_true())
                    ++score;
            }
            // ignore the situation where clause contains multiple literals using v
            for (auto cl : m_bool_search->get_use_list(~lit)) {
                auto const& clause = get_clause_info(cl);
                if (clause.m_num_trues == 1)
                    --score;
            }
        }
        return score;
    }

    int64_t sls::compute_dts(unsigned cl) const {
        int64_t d(1), d2;
        bool first = true;
        for (auto a : get_clause(cl)) {
            auto const* ineq = atom(a.var());
            if (!ineq)
                continue;
            d2 = dtt(a.sign(), *ineq);
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
            auto const* ineq = atom(lit.var());
            if (!ineq)
                continue;
            d2 = dtt(lit.sign(), *ineq, v, new_value);
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
        auto old_value = vi.m_value;
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            auto& ineq = *atom(bv);
            bool old_sign = sign(bv);
            sat::literal lit(bv, old_sign);
            SASSERT(is_true(lit));            
            ineq.m_args_value += coeff * (new_value - old_value);
            int64_t dtt_new = dtt(old_sign, ineq);
            if (dtt_new != 0)
                m_bool_search->flip(bv);                                                 
            SASSERT(dtt(sign(bv), ineq) == 0);
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

    void sls::add_arg(sat::bool_var bv, ineq& ineq, int64_t const& c, var_t v) {
        ineq.m_args.push_back({ c, v });
        ineq.m_args_value += c * value(v);
        m_vars[v].m_bool_vars.push_back({ c, bv});
    }

    int64_t sls::to_numeral(rational const& r) {
        if (r.is_int64())
            return r.get_int64();
        return 0;
    }

    void sls::add_args(sat::bool_var bv, ineq& ineq, lp::lpvar t, theory_var v, int64_t sign) {
        if (s.lp().column_has_term(t)) {
            lp::lar_term const& term = s.lp().get_term(t);
            m_terms.push_back({t,v});
            for (lp::lar_term::ival arg : term) {
                auto t2 = arg.j();
                auto w = s.lp().local_to_external(t2);
                add_arg(bv, ineq, sign * to_numeral(arg.coeff()), w);
            }
        }
        else
            add_arg(bv, ineq, sign, s.lp().local_to_external(t));
    }

    void sls::init_bool_var(sat::bool_var bv) {
        if (m_bool_vars.get(bv, nullptr))
            return;
        api_bound* b = nullptr;
        s.m_bool_var2bound.find(bv, b);
        if (b) {
            auto t = b->column_index();
            rational bound = b->get_value();
            bool should_minus = false;
            sls::ineq_kind op;
            should_minus = b->get_bound_kind() == lp_api::bound_kind::lower_t;
            op = sls::ineq_kind::LE;
            if (should_minus)
                bound.neg();

            auto& ineq = new_ineq(op, to_numeral(bound));


            add_args(bv, ineq, t, b->get_var(), should_minus ? -1 : 1);
            m_bool_vars.set(bv, &ineq);
            m_bool_search->set_external(bv);
            return;
        }

        expr* e = s.bool_var2expr(bv);
        expr* l = nullptr, * r = nullptr;
        if (e && m.is_eq(e, l, r) && s.a.is_int_real(l)) {
            theory_var u = s.get_th_var(l);
            theory_var v = s.get_th_var(r);
            lp::lpvar tu = s.get_column(u);
            lp::lpvar tv = s.get_column(v);
            auto& ineq = new_ineq(sls::ineq_kind::EQ, 0);            
            add_args(bv, ineq, tu, u, 1);
            add_args(bv, ineq, tv, v, -1);
            m_bool_vars.set(bv, &ineq);
            m_bool_search->set_external(bv);
            return;
        }
    }

    void sls::init_bool_var_assignment(sat::bool_var v) {
        auto* ineq = m_bool_vars.get(v, nullptr);
        if (ineq && is_true(sat::literal(v, false)) != (dtt(false, *ineq) == 0))
            m_bool_search->flip(v);
    }

    void sls::init_search()  {
        on_restart();
    }

    void sls::finish_search()  {
        store_best_values();
    }

    void sls::flip(sat::bool_var v)  {
        sat::literal lit(v, !sign(v));
        SASSERT(!is_true(lit));
        auto const* ineq = atom(v);
        if (!ineq) 
            IF_VERBOSE(0, verbose_stream() << "no inequality for variable " << v << "\n");
        if (!ineq)
            return;
        SASSERT(ineq->is_true() == lit.sign());
        flip(sign(v), *ineq);
    }

    double sls::reward(sat::bool_var v) {
        if (m_dscore_mode)
            return dscore_reward(v);
        else 
            return dtt_reward(v);
    }

    double sls::dtt_reward(sat::bool_var bv0) {
        bool sign0 = sign(bv0);
        auto* ineq = atom(bv0);
        if (!ineq)
            return -1;
        int64_t new_value;      
        double max_result = -1;
        for (auto const & [coeff, x] : ineq->m_args) {
            if (!cm(sign0, *ineq, x, coeff, new_value))
                continue;
            double result = 0;
            auto old_value = m_vars[x].m_value;
            for (auto const& [coeff, bv] : m_vars[x].m_bool_vars) {
                result += m_bool_search->reward(bv);
                continue;
                bool old_sign = sign(bv);
                auto dtt_old = dtt(old_sign, *atom(bv));
                auto dtt_new = dtt(old_sign, *atom(bv), coeff, old_value, new_value);
                if ((dtt_new == 0) != (dtt_old == 0))
                    result += m_bool_search->reward(bv);
            }
            if (result > max_result) {
                max_result = result;
                ineq->m_var_to_flip = x;
            }
        }
        return max_result; 
    }

    double sls::dscore_reward(sat::bool_var bv) {
        m_dscore_mode = false;
        bool old_sign = sign(bv);
        sat::literal litv(bv, old_sign);
        auto* ineq = atom(bv);
        if (!ineq)
            return 0;
        SASSERT(ineq->is_true() != old_sign);
        int64_t new_value;

        for (auto const& [coeff, v] : ineq->m_args) {
            double result = 0;
            if (cm(old_sign, *ineq, v, coeff, new_value))
                result = dscore(v, new_value);
            // just pick first positive, or pick a max?
            if (result > 0) {
                ineq->m_var_to_flip = v;
                return result;
            }
        }
        return 0;
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

        check_ineqs();
    }

    void sls::check_ineqs() {

        auto check_bool_var = [&](sat::bool_var bv) {
            auto const* ineq = atom(bv);
            if (!ineq)
                return;
            int64_t d = dtt(sign(bv), *ineq);
            sat::literal lit(bv, sign(bv));
            if (is_true(lit) != (d == 0)) {
                verbose_stream() << "invalid assignment " << bv << " " << *ineq << "\n";
            }
            VERIFY(is_true(lit) == (d == 0));
        };
        for (unsigned v = 0; v < s.get_num_vars(); ++v)
            check_bool_var(v);
    }

    std::ostream& sls::display(std::ostream& out) const {
        for (bool_var bv = 0; bv < s.s().num_vars(); ++bv) {
            auto const* ineq = atom(bv);            
            if (!ineq)
                continue;
            out << bv << " " << *ineq << "\n";            
        }
        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            if (s.is_bool(v))
                continue;
            out << "v" << v << " := " << m_vars[v].m_value << " " << m_vars[v].m_best_value << "\n";
        }
        return out;
    }

}
