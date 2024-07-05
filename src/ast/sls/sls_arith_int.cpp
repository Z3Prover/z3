/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    arith_sls_int.cpp

Abstract:

    Local search dispatch for NIA

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

--*/

#include "ast/sls/sls_arith_int.h"
#include "ast/ast_ll_pp.h"

namespace sls {

    template<typename int_t>
    arith_plugin<int_t>::arith_plugin(context& ctx) :
        plugin(ctx),
        a(m) {
        m_fid = a.get_family_id();
    }

    template<typename int_t>
    void arith_plugin<int_t>::reset() {
        m_bool_vars.reset();
        m_vars.reset();
        m_expr2var.reset();
    }

    template<typename int_t>
    void arith_plugin<int_t>::save_best_values() {
        for (auto& v : m_vars)
            v.m_best_value = v.m_value;
        check_ineqs();
    }

    template<typename int_t>
    void arith_plugin<int_t>::store_best_values() {
    }

    // distance to true
    template<typename int_t>
    int_t arith_plugin<int_t>::dtt(bool sign, int_t const& args, ineq const& ineq) const {
        int_t zero{ 0 };
        switch (ineq.m_op) {
        case ineq_kind::LE:
            if (sign) {
                if (args + ineq.m_coeff <= 0)
                    return -ineq.m_coeff - args + 1;
                return zero;
            }
            if (args + ineq.m_coeff <= 0)
                return zero;
            return args + ineq.m_coeff;
        case ineq_kind::EQ:
            if (sign) {
                if (args + ineq.m_coeff == 0)
                    return int_t(1);
                return zero;
            }
            if (args + ineq.m_coeff == 0)
                return zero;
            return int_t(1);
        case ineq_kind::LT:
            if (sign) {
                if (args + ineq.m_coeff < 0)
                    return -ineq.m_coeff - args;
                return zero;
            }
            if (args + ineq.m_coeff < 0)
                return zero;
            return args + ineq.m_coeff + 1;
        default:
            UNREACHABLE();
            return zero;
        }
    }

    //
    // dtt is high overhead. It walks ineq.m_args
    // m_vars[w].m_value can be computed outside and shared among calls
    // different data-structures for storing coefficients
    // 
    template<typename int_t>
    int_t arith_plugin<int_t>::dtt(bool sign, ineq const& ineq, var_t v, int_t const& new_value) const {
        for (auto const& [coeff, w] : ineq.m_args)
            if (w == v)
                return dtt(sign, ineq.m_args_value + coeff * (new_value - m_vars[v].m_value), ineq);
        return int_t(1);
    }

    template<typename int_t>
    int_t arith_plugin<int_t>::dtt(bool sign, ineq const& ineq, int_t const& coeff, int_t const& old_value, int_t const& new_value) const {
        return dtt(sign, ineq.m_args_value + coeff * (new_value - old_value), ineq);
    }

    template<typename int_t>
    bool arith_plugin<int_t>::cm(ineq const& ineq, var_t v, int_t& new_value) {
        for (auto const& [coeff, w] : ineq.m_args)
            if (w == v)
                return cm(ineq, v, coeff, new_value);
        return false;
    }

    template<typename int_t>
    bool arith_plugin<int_t>::cm(ineq const& ineq, var_t v, int_t const& coeff, int_t& new_value) {
        auto bound = -ineq.m_coeff;
        auto argsv = ineq.m_args_value;
        bool solved = false;
        int_t delta = argsv - bound;

        if (ineq.is_true()) {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                // args <= bound -> args > bound
                SASSERT(argsv <= bound);
                SASSERT(delta <= 0);
                delta -= 1 + (ctx.rand() % 10);
                new_value = value(v) + div(abs(delta) + abs(coeff) - 1, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) > bound);
                return true;
            case ineq_kind::LT:
                // args < bound -> args >= bound
                SASSERT(argsv <= bound);
                SASSERT(delta <= 0);
                delta = abs(delta) + ctx.rand() % 10;
                new_value = value(v) + div(delta + abs(coeff) - 1, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) >= bound);
                return true;
            case ineq_kind::EQ: {
                delta = abs(delta) + 1 + ctx.rand() % 10;
                int sign = ctx.rand() % 2 == 0 ? 1 : -1;
                new_value = value(v) + sign * div(abs(delta) + abs(coeff) - 1, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) != bound);
                return true;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
        else {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                SASSERT(argsv > bound);
                SASSERT(delta > 0);
                delta += rand() % 10;
                new_value = value(v) - div(delta + abs(coeff) - 1, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) <= bound);
                return true;
            case ineq_kind::LT:
                SASSERT(argsv >= bound);
                SASSERT(delta >= 0);
                delta += 1 + rand() % 10;
                new_value = value(v) - div(delta + abs(coeff) - 1, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) < bound);
                return true;
            case ineq_kind::EQ:
                SASSERT(delta != 0);
                if (delta < 0)
                    new_value = value(v) + div(abs(delta) + abs(coeff) - 1, coeff);
                else
                    new_value = value(v) - div(delta + abs(coeff) - 1, coeff);
                solved = argsv + coeff * (new_value - value(v)) == bound;
                if (!solved && abs(coeff) == 1) {
                    verbose_stream() << "did not solve equality " << ineq << " for " << v << "\n";
                    verbose_stream() << new_value << " " << value(v) << " delta " << delta << " lhs " << (argsv + coeff * (new_value - value(v))) << " bound " << bound << "\n";
                    UNREACHABLE();
                }
                return solved;
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
    template<typename int_t>
    void arith_plugin<int_t>::repair(sat::literal lit, ineq const& ineq) {
        int_t new_value;
        if (UINT_MAX == ineq.m_var_to_flip)
            dtt_reward(lit);
        auto v = ineq.m_var_to_flip;
        if (v == UINT_MAX) {
            IF_VERBOSE(1, verbose_stream() << "no var to flip\n");
            return;
        }
        // verbose_stream() << "var to flip " << v << "\n";
        if (!cm(ineq, v, new_value)) {
            IF_VERBOSE(1, verbose_stream() << "no critical move for " << v << "\n");
            return;
        }
        update(v, new_value);
    }

    //
    // dscore(op) = sum_c (dts(c,alpha) - dts(c,alpha_after)) * weight(c)
    // TODO - use cached dts instead of computed dts
    // cached dts has to be updated when the score of literals are updated.
    // 
    template<typename int_t>
    double arith_plugin<int_t>::dscore(var_t v, int_t const& new_value) const {
        double score = 0;
        auto const& vi = m_vars[v];
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            sat::literal lit(bv, false);
            for (auto cl : ctx.get_use_list(lit))
                score += (compute_dts(cl) - dts(cl, v, new_value)).get_int64() * ctx.get_weight(cl);
            for (auto cl : ctx.get_use_list(~lit))
                score += (compute_dts(cl) - dts(cl, v, new_value)).get_int64() * ctx.get_weight(cl);
        }
        return score;
    }

    //
    // cm_score is costly. It involves several cache misses.
    // Note that
    // - get_use_list(lit).size() is "often" 1 or 2
    // - dtt_old can be saved
    //
    template<typename int_t>
    int arith_plugin<int_t>::cm_score(var_t v, int_t const& new_value) {
        int score = 0;
        auto& vi = m_vars[v];
        int_t old_value = vi.m_value;
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            auto const& ineq = *atom(bv);
            bool old_sign = sign(bv);
            int_t dtt_old = dtt(old_sign, ineq);
            int_t dtt_new = dtt(old_sign, ineq, coeff, old_value, new_value);
            if ((dtt_old == 0) == (dtt_new == 0))
                continue;
            sat::literal lit(bv, old_sign);
            if (dtt_old == 0)
                // flip from true to false
                lit.neg();

            // lit flips form false to true:           

            for (auto cl : ctx.get_use_list(lit)) {
                auto const& clause = ctx.get_clause(cl);
                if (!clause.is_true())
                    ++score;
            }

            // ignore the situation where clause contains multiple literals using v
            for (auto cl : ctx.get_use_list(~lit)) {
                auto const& clause = ctx.get_clause(cl);
                if (clause.m_num_trues == 1)
                    --score;
            }
        }
        return score;
    }

    template<typename int_t>
    int_t arith_plugin<int_t>::compute_dts(unsigned cl) const {
        int_t d(1), d2;
        bool first = true;
        for (auto a : ctx.get_clause(cl)) {
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

    template<typename int_t>
    int_t arith_plugin<int_t>::dts(unsigned cl, var_t v, int_t const& new_value) const {
        int_t d(1), d2;
        bool first = true;
        for (auto lit : ctx.get_clause(cl)) {
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

    template<typename int_t>
    void arith_plugin<int_t>::update(var_t v, int_t const& new_value) {
        auto& vi = m_vars[v];
        auto old_value = vi.m_value;
        if (old_value == new_value)
            return;
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            auto& ineq = *atom(bv);
            bool old_sign = sign(bv);
            sat::literal lit(bv, old_sign);
            SASSERT(ctx.is_true(lit));
            ineq.m_args_value += coeff * (new_value - old_value);
            int_t dtt_new = dtt(old_sign, ineq);
            if (dtt_new != 0)
                ctx.flip(bv);
            SASSERT(dtt(sign(bv), ineq) == 0);
        }
        vi.m_value = new_value;
        for (auto idx : vi.m_muls) {
            auto const& [v, monomial] = m_muls[idx];

            int_t prod(1);
            for (auto w : monomial)
                prod *= value(w);
            if (value(v) != prod)
                m_vars_to_update.push_back({ v, prod });
        }
        for (auto const& idx : vi.m_adds) {
            auto const& ad = m_adds[idx];
            auto const& args = ad.m_args;
            auto v = ad.m_var;
            int_t sum(ad.m_coeff);
            for (auto [c, w] : args)
                sum += c * value(w);
            if (value(v) != sum)
                m_vars_to_update.push_back({ v, sum });
        }
        if (vi.m_add_idx != UINT_MAX || vi.m_mul_idx != UINT_MAX)
            // add repair actions for additions.
            m_defs_to_update.push_back(v);
    }

    template<typename int_t>
    typename arith_plugin<int_t>::ineq& arith_plugin<int_t>::new_ineq(ineq_kind op, int_t const& coeff) {
        auto* i = alloc(ineq);
        i->m_coeff = coeff;
        i->m_op = op;
        return *i;
    }

    template<typename int_t>
    void arith_plugin<int_t>::add_arg(linear_term& ineq, int_t const& c, var_t v) {
        ineq.m_args.push_back({ c, v });
    }

    template<typename int_t>
    bool arith_plugin<int_t>::is_int64(expr* e, int_t& i) {
        rational r;
        if (a.is_numeral(e, r) && r.is_int64()) {
            i = int_t(r.get_int64());
            return true;
        }
        return false;
    }

    bool arith_plugin<checked_int64<true>>::is_int(expr* e, checked_int64<true>& i) {
        return is_int64(e, i);
    }

    bool arith_plugin<rational>::is_int(expr* e, rational& i) {
        return a.is_numeral(e, i) && i.is_int();
    }

    template<typename int_t>
    bool arith_plugin<int_t>::is_int(expr* e, int_t& i) {
        return false;
    }

    template<typename int_t>
    void arith_plugin<int_t>::add_args(linear_term& term, expr* e, int_t const& coeff) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v != UINT_MAX) {
            add_arg(term, coeff, v);
            return;
        }
        expr* x, * y;
        int_t i;
        if (is_int(e, i)) {
            term.m_coeff += coeff * i;
            return;
        }
        if (a.is_add(e)) {
            for (expr* arg : *to_app(e))
                add_args(term, arg, coeff);
            return;
        }
        if (a.is_sub(e, x, y)) {
            add_args(term, x, coeff);
            add_args(term, y, -coeff);
            return;
        }

        if (a.is_mul(e)) {
            unsigned_vector m;
            int_t c = coeff;
            for (expr* arg : *to_app(e))
                if (is_int(x, i))
                    c *= i;
                else
                    m.push_back(mk_term(arg));
            switch (m.size()) {
            case 0:
                term.m_coeff += c;
                break;
            case 1:
                add_arg(term, c, m[0]);
                break;
            default: {
                auto v = mk_var(e);
                unsigned idx = m_muls.size();
                m_muls.push_back({ v, m });
                int_t prod(1);
                for (auto w : m)
                    m_vars[w].m_muls.push_back(idx), prod *= value(w);
                m_vars[v].m_mul_idx = idx;
                m_vars[v].m_value = prod;
                add_arg(term, c, v);
                break;
            }
            }
            return;
        }
        if (a.is_uminus(e, x)) {
            add_args(term, x, -coeff);
            return;
        }

        if (is_uninterp(e)) {
            auto v = mk_var(e);
            add_arg(term, coeff, v);
            return;
        }

        UNREACHABLE();
    }

    template<typename int_t>
    typename arith_plugin<int_t>::var_t arith_plugin<int_t>::mk_term(expr* e) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v != UINT_MAX)
            return v;
        linear_term t = linear_term({ {}, 0 });
        add_args(t, e, int_t(1));
        if (t.m_coeff == 1 && t.m_args.size() == 1 && t.m_args[0].first == 1)
            return t.m_args[0].second;
        v = mk_var(e);
        auto idx = m_adds.size();
        int_t sum(t.m_coeff);
        m_adds.push_back({ t.m_args, t.m_coeff, v });
        for (auto const& [c, w] : t.m_args)
            m_vars[w].m_adds.push_back(idx), sum += c * value(w);
        m_vars[v].m_add_idx = idx;
        m_vars[v].m_value = sum;
        return v;
    }

    template<typename int_t>
    unsigned arith_plugin<int_t>::mk_var(expr* e) {
        unsigned v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX) {
            v = m_vars.size();
            m_expr2var.setx(e->get_id(), v, UINT_MAX);
            m_vars.push_back(var_info(e, var_kind::INT));
        }
        return v;
    }

    template<typename int_t>
    void arith_plugin<int_t>::init_bool_var(sat::bool_var bv) {
        if (m_bool_vars.get(bv, nullptr))
            return;
        expr* e = ctx.atom(bv);
        // verbose_stream() << "bool var " << bv << " " << mk_bounded_pp(e, m) << "\n";
        if (!e)
            return;
        expr* x, * y;
        m_bool_vars.reserve(bv + 1);
        if (a.is_le(e, x, y) || a.is_ge(e, y, x)) {
            auto& ineq = new_ineq(ineq_kind::LE, int_t(0));
            add_args(ineq, x, int_t(1));
            add_args(ineq, y, int_t(-1));
            init_ineq(bv, ineq);
        }
        else if ((a.is_lt(e, x, y) || a.is_gt(e, y, x)) && a.is_int(x)) {
            auto& ineq = new_ineq(ineq_kind::LE, int_t(1));
            add_args(ineq, x, int_t(1));
            add_args(ineq, y, int_t(-1));
            init_ineq(bv, ineq);
        }
        else if (m.is_eq(e, x, y) && a.is_int_real(x)) {
            auto& ineq = new_ineq(ineq_kind::EQ, int_t(0));
            add_args(ineq, x, int_t(1));
            add_args(ineq, y, int_t(-1));
            init_ineq(bv, ineq);
        }
        else {
            SASSERT(!a.is_arith_expr(e));
        }
    }

    template<typename int_t>
    void arith_plugin<int_t>::init_ineq(sat::bool_var bv, ineq& i) {
        i.m_args_value = 0;
        for (auto const& [coeff, v] : i.m_args) {
            m_vars[v].m_bool_vars.push_back({ coeff, bv });
            i.m_args_value += coeff * value(v);
        }
        m_bool_vars.set(bv, &i);
    }

    template<typename int_t>
    void arith_plugin<int_t>::init_bool_var_assignment(sat::bool_var v) {
        auto* ineq = m_bool_vars.get(v, nullptr);
        if (ineq && ctx.is_true(sat::literal(v, false)) != (dtt(false, *ineq) == 0))
            ctx.flip(v);
    }

    template<typename int_t>
    void arith_plugin<int_t>::repair(sat::literal lit) {
        if (!ctx.is_true(lit))
            return;
        auto const* ineq = atom(lit.var());
        if (!ineq)
            return;
        if (ineq->is_true() != lit.sign())
            return;
        TRACE("sls", tout << "repair " << lit << "\n");
        repair(lit, *ineq);
    }

    template<typename int_t>
    void arith_plugin<int_t>::propagate_updates() {
        while (!m_defs_to_update.empty() || !m_vars_to_update.empty()) {
            while (!m_vars_to_update.empty()) {
                auto [w, new_value1] = m_vars_to_update.back();
                m_vars_to_update.pop_back();
                update(w, new_value1);
            }
            repair_defs();
        }
    }

    template<typename int_t>
    void arith_plugin<int_t>::repair_defs() {
        while (!m_defs_to_update.empty()) {
            auto v = m_defs_to_update.back();
            m_defs_to_update.pop_back();
            auto const& vi = m_vars[v];
            if (vi.m_mul_idx != UINT_MAX)
                repair_mul(m_muls[vi.m_mul_idx]);
            if (vi.m_add_idx != UINT_MAX)
                repair_add(m_adds[vi.m_add_idx]);
        }
    }

    template<typename int_t>
    void arith_plugin<int_t>::repair_add(add_def const& ad) {
        auto v = ad.m_var;
        auto const& coeffs = ad.m_args;
        int_t sum(ad.m_coeff);
        int_t val = value(v);
        for (auto const& [c, w] : coeffs)
            sum += c * value(w);
        if (val == sum)
            return;
        if (rand() % 20 == 0)
            update(v, sum);
        else {
            auto const& [c, w] = coeffs[rand() % coeffs.size()];
            int_t delta = sum - val;
            int_t new_value = value(w) + div(delta, c);
            update(w, new_value);
        }
    }

    template<typename int_t>
    void arith_plugin<int_t>::repair_mul(mul_def const& md) {
        int_t product(1);
        int_t val = value(md.m_var);
        for (auto v : md.m_monomial)
            product *= value(v);
        if (product == val)
            return;
        if (rand() % 20 == 0) {
            update(md.m_var, product);
        }
        else if (val == 0) {
            auto v = md.m_monomial[rand() % md.m_monomial.size()];
            int_t zero(0);
            update(v, zero);
        }
        else if (val == 1 || val == -1) {
            product = 1;
            for (auto v : md.m_monomial) {
                int_t new_value(1);
                if (rand() % 2 == 0)
                    new_value = -1;
                product *= new_value;
                update(v, new_value);
            }
            if (product != val) {
                auto last = md.m_monomial.back();
                update(last, -value(last));
            }
        }
        else {
            product = 1;
            for (auto v : md.m_monomial) {
                int_t new_value{ 1 };
                if (rand() % 2 == 0)
                    new_value = -1;
                product *= new_value;
                update(v, new_value);
            }
            auto v = md.m_monomial[rand() % md.m_monomial.size()];
            if ((product < 0 && 0 < val) || (val < 0 && 0 < product))
                update(v, -val * value(v));
            else
                update(v, val * value(v));
        }
    }

    template<typename int_t>
    double arith_plugin<int_t>::reward(sat::literal lit) {
        if (m_dscore_mode)
            return dscore_reward(lit.var());
        else
            return dtt_reward(lit);
    }

    template<typename int_t>
    double arith_plugin<int_t>::dtt_reward(sat::literal lit) {
        auto* ineq = atom(lit.var());
        if (!ineq)
            return -1;
        int_t new_value;
        double max_result = -1;
        unsigned n = 0;
        for (auto const& [coeff, x] : ineq->m_args) {
            if (!cm(*ineq, x, coeff, new_value))
                continue;
            double result = 0;
            auto old_value = m_vars[x].m_value;
            for (auto const& [coeff, bv] : m_vars[x].m_bool_vars) {
                result += ctx.reward(bv);
#if 0
                bool old_sign = sign(bv);
                auto dtt_old = dtt(old_sign, *atom(bv));
                auto dtt_new = dtt(old_sign, *atom(bv), coeff, old_value, new_value);
                if ((dtt_new == 0) != (dtt_old == 0))
                    result += ctx.reward(bv);
#endif
            }
            if (result > max_result || max_result == -1 || (result == max_result && (rand() % ++n == 0))) {
                max_result = result;
                ineq->m_var_to_flip = x;
            }
        }
        return max_result;
    }

    template<typename int_t>
    double arith_plugin<int_t>::dscore_reward(sat::bool_var bv) {
        m_dscore_mode = false;
        bool old_sign = sign(bv);
        sat::literal litv(bv, old_sign);
        auto* ineq = atom(bv);
        if (!ineq)
            return 0;
        SASSERT(ineq->is_true() != old_sign);
        int_t new_value;

        for (auto const& [coeff, v] : ineq->m_args) {
            double result = 0;
            if (cm(*ineq, v, coeff, new_value))
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
    template<typename int_t>
    void arith_plugin<int_t>::on_rescale() {
        m_dscore_mode = true;
    }

    template<typename int_t>
    void arith_plugin<int_t>::on_restart() {
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v)
            init_bool_var_assignment(v);
        check_ineqs();
    }

    template<typename int_t>
    void arith_plugin<int_t>::check_ineqs() {
        auto check_bool_var = [&](sat::bool_var bv) {
            auto const* ineq = atom(bv);
            if (!ineq)
                return;
            int_t d = dtt(sign(bv), *ineq);
            sat::literal lit(bv, sign(bv));
            if (ctx.is_true(lit) != (d == 0)) {
                verbose_stream() << "invalid assignment " << bv << " " << *ineq << "\n";
            }
            VERIFY(ctx.is_true(lit) == (d == 0));
            };
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v)
            check_bool_var(v);
    }

    template<typename int_t>
    void arith_plugin<int_t>::register_term(expr* e) {
    }

    template<typename int_t>
    expr_ref arith_plugin<int_t>::get_value(expr* e) {
        auto v = mk_var(e);
        return expr_ref(a.mk_numeral(rational(m_vars[v].m_value.get_int64(), rational::i64()), a.is_int(e)), m);
    }

    template<typename int_t>
    lbool arith_plugin<int_t>::check() {
        // repair each root literal
        for (sat::literal lit : ctx.root_literals())
            repair(lit);

        propagate_updates();

        // update literal assignment based on current model
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v)
            init_bool_var_assignment(v);

        return ctx.unsat().empty() ? l_true : l_undef;
    }

    template<typename int_t>
    bool arith_plugin<int_t>::is_sat() {
        for (auto const& clause : ctx.clauses()) {
            bool sat = false;
            for (auto lit : clause.m_clause) {
                if (!ctx.is_true(lit))
                    continue;
                auto ineq = atom(lit.var());
                if (!ineq) {
                    sat = true;
                    break;
                }
                if (ineq->is_true() != lit.sign()) {
                    sat = true;
                    break;
                }
            }
            if (!sat)
                return false;
        }
        return true;
    }

    template<typename int_t>
    std::ostream& arith_plugin<int_t>::display(std::ostream& out) const {
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v) {
            auto ineq = atom(v);
            if (ineq)
                out << v << ": " << *ineq << "\n";
        }
        for (unsigned v = 0; v < m_vars.size(); ++v) {
            auto const& vi = m_vars[v];
            out << "v" << v << " := " << vi.m_value << " " << vi.m_best_value << " ";
            out << mk_bounded_pp(vi.m_expr, m) << " - ";
            for (auto [c, bv] : vi.m_bool_vars)
                out << c << "@" << bv << " ";
            out << "\n";
        }
        return out;
    }

    template<typename int_t>
    void arith_plugin<int_t>::mk_model(model& mdl) {
        for (auto const& v : m_vars) {
            expr* e = v.m_expr;
            if (is_uninterp_const(e))
                mdl.register_decl(to_app(e)->get_decl(), get_value(e));
        }
    }
}

template class sls::arith_plugin<checked_int64<true>>;
template class sls::arith_plugin<rational>;