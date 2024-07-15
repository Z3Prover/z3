/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    sls_arith_base.cpp

Abstract:

    Local search dispatch for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

--*/

#include "ast/sls/sls_arith_base.h"
#include "ast/ast_ll_pp.h"

namespace sls {

    template<typename num_t>
    arith_base<num_t>::arith_base(context& ctx) :
        plugin(ctx),
        a(m) {
        m_fid = a.get_family_id();
    }

    template<typename num_t>
    void arith_base<num_t>::save_best_values() {
        for (auto& v : m_vars)
            v.m_best_value = v.m_value;
        check_ineqs();
    }

    // distance to true
    template<typename num_t>
    num_t arith_base<num_t>::dtt(bool sign, num_t const& args, ineq const& ineq) const {
        num_t zero{ 0 };
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
                    return num_t(1);
                return zero;
            }
            if (args + ineq.m_coeff == 0)
                return zero;
            return num_t(1);
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
    template<typename num_t>
    num_t arith_base<num_t>::dtt(bool sign, ineq const& ineq, var_t v, num_t const& new_value) const {
        for (auto const& [coeff, w] : ineq.m_args)
            if (w == v)
                return dtt(sign, ineq.m_args_value + coeff * (new_value - m_vars[v].m_value), ineq);
        return num_t(1);
    }

    template<typename num_t>
    num_t arith_base<num_t>::dtt(bool sign, ineq const& ineq, num_t const& coeff, num_t const& old_value, num_t const& new_value) const {
        return dtt(sign, ineq.m_args_value + coeff * (new_value - old_value), ineq);
    }

    template<typename num_t>
    bool arith_base<num_t>::cm(ineq const& ineq, var_t v, num_t& new_value) {
        for (auto const& [coeff, w] : ineq.m_args)
            if (w == v)
                return cm(ineq, v, coeff, new_value);
        return false;
    }

    template<typename num_t>
    num_t arith_base<num_t>::divide(var_t v, num_t const& delta, num_t const& coeff) {
        if (m_vars[v].m_sort == var_sort::REAL)
            return delta / coeff;
        return div(delta + abs(coeff) - 1, coeff);
    }

    template<typename num_t>
    bool arith_base<num_t>::cm(ineq const& ineq, var_t v, num_t const& coeff, num_t& new_value) {
        auto bound = -ineq.m_coeff;
        auto argsv = ineq.m_args_value;
        bool solved = false;
        num_t delta = argsv - bound;

        if (ineq.is_true()) {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                // args <= bound -> args > bound
                SASSERT(argsv <= bound);
                SASSERT(delta <= 0);
                delta -= 1 + (ctx.rand() % 10);
                new_value = value(v) + divide(v, abs(delta), coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) > bound);
                return true;
            case ineq_kind::LT:
                // args < bound -> args >= bound
                SASSERT(argsv <= bound);
                SASSERT(delta <= 0);
                delta = abs(delta) + ctx.rand() % 10;
                new_value = value(v) + divide(v, delta, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) >= bound);
                return true;
            case ineq_kind::EQ: {
                delta = abs(delta) + 1 + ctx.rand() % 10;
                int sign = ctx.rand() % 2 == 0 ? 1 : -1;
                new_value = value(v) + sign * divide(v, abs(delta), coeff);
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
                new_value = value(v) - divide(v, delta, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) <= bound);
                return true;
            case ineq_kind::LT:
                SASSERT(argsv >= bound);
                SASSERT(delta >= 0);
                delta += 1 + rand() % 10;
                new_value = value(v) - divide(v, delta, coeff);
                VERIFY(argsv + coeff * (new_value - value(v)) < bound);
                return true;
            case ineq_kind::EQ:
                SASSERT(delta != 0);
                if (delta < 0)
                    new_value = value(v) + divide(v, abs(delta), coeff);
                else
                    new_value = value(v) - divide(v, delta, coeff);
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
    template<typename num_t>
    void arith_base<num_t>::repair(sat::literal lit, ineq const& ineq) {
        num_t new_value;
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
    template<typename num_t>
    double arith_base<num_t>::dscore(var_t v, num_t const& new_value) const {
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
    template<typename num_t>
    int arith_base<num_t>::cm_score(var_t v, num_t const& new_value) {
        int score = 0;
        auto& vi = m_vars[v];
        num_t old_value = vi.m_value;
        for (auto const& [coeff, bv] : vi.m_bool_vars) {
            auto const& ineq = *atom(bv);
            bool old_sign = sign(bv);
            num_t dtt_old = dtt(old_sign, ineq);
            num_t dtt_new = dtt(old_sign, ineq, coeff, old_value, new_value);
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

    template<typename num_t>
    num_t arith_base<num_t>::compute_dts(unsigned cl) const {
        num_t d(1), d2;
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

    template<typename num_t>
    num_t arith_base<num_t>::dts(unsigned cl, var_t v, num_t const& new_value) const {
        num_t d(1), d2;
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

    template<typename num_t>
    void arith_base<num_t>::update(var_t v, num_t const& new_value) {
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
            num_t dtt_new = dtt(old_sign, ineq);
            if (dtt_new != 0)
                ctx.flip(bv);
            SASSERT(dtt(sign(bv), ineq) == 0);
        }
        vi.m_value = new_value;
        for (auto idx : vi.m_muls) {
            auto const& [w, coeff, monomial] = m_muls[idx];
            ctx.new_value_eh(m_vars[w].m_expr);
        }
        for (auto idx : vi.m_adds) {
            auto const& ad = m_adds[idx];
            ctx.new_value_eh(m_vars[ad.m_var].m_expr);
        }
        expr* e = vi.m_expr;
        ctx.new_value_eh(e);
    }

    template<typename num_t>
    typename arith_base<num_t>::ineq& arith_base<num_t>::new_ineq(ineq_kind op, num_t const& coeff) {
        auto* i = alloc(ineq);
        i->m_coeff = coeff;
        i->m_op = op;
        return *i;
    }

    template<typename num_t>
    void arith_base<num_t>::add_arg(linear_term& ineq, num_t const& c, var_t v) {
        ineq.m_args.push_back({ c, v });
    }

    bool arith_base<checked_int64<true>>::is_num(expr* e, checked_int64<true>& i) {
        rational r;
        if (a.is_numeral(e, r)) {            
            if (!r.is_int64())
                throw overflow_exception();
            i = r.get_int64();
            return true;
        }
        return false;
    }

    bool arith_base<rational>::is_num(expr* e, rational& i) {
        return a.is_numeral(e, i);
    }

    template<typename num_t>
    bool arith_base<num_t>::is_num(expr* e, num_t& i) {
        UNREACHABLE();
        return false;
    }

    expr_ref arith_base<rational>::from_num(sort* s, rational const& n) {
        return expr_ref(a.mk_numeral(n, s), m);
    }

    expr_ref arith_base<checked_int64<true>>::from_num(sort* s, checked_int64<true> const& n) {
        return expr_ref(a.mk_numeral(rational(n.get_int64(), rational::i64()), s), m);
    }

    template<typename num_t>
    expr_ref arith_base<num_t>::from_num(sort* s, num_t const& n) {
        UNREACHABLE();
        return expr_ref(m);
    }

    template<typename num_t>
    void arith_base<num_t>::add_args(linear_term& term, expr* e, num_t const& coeff) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        expr* x, * y;
        num_t i;
        if (v != UINT_MAX)
            add_arg(term, coeff, v);
        else if (is_num(e, i))
            term.m_coeff += coeff * i;
        else if (a.is_add(e)) {
            for (expr* arg : *to_app(e))
                add_args(term, arg, coeff);
        }
        else if (a.is_sub(e, x, y)) {
            add_args(term, x, coeff);
            add_args(term, y, -coeff);
        }
        else if (a.is_mul(e)) {
            unsigned_vector m;
            num_t c = coeff;
            for (expr* arg : *to_app(e))
                if (is_num(x, i))
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
                v = mk_var(e);
                unsigned idx = m_muls.size();
                m_muls.push_back({ v, c, m });
                num_t prod(c);
                for (auto w : m)
                    m_vars[w].m_muls.push_back(idx), prod *= value(w);
                m_vars[v].m_def_idx = idx;
                m_vars[v].m_op = arith_op_kind::OP_MUL;
                m_vars[v].m_value = prod;
                add_arg(term, num_t(1), v);
                break;
            }
            }
        }
        else if (a.is_uminus(e, x))
            add_args(term, x, -coeff);
        else if (a.is_mod(e, x, y) || a.is_mod0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_MOD, e, x, y));
        else if (a.is_idiv(e, x, y) || a.is_idiv0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_IDIV, e, x, y));
        else if (a.is_div(e, x, y) || a.is_div0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_DIV, e, x, y));
        else if (a.is_rem(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_REM, e, x, y));
        else if (a.is_power(e, x, y) || a.is_power0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_POWER, e, x, y));
        else if (a.is_abs(e, x))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_ABS, e, x, x));
        else if (a.is_to_int(e, x))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_TO_INT, e, x, x));
        else if (a.is_to_real(e, x))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_TO_REAL, e, x, x));       
        else if (a.is_arith_expr(e)) {
            NOT_IMPLEMENTED_YET();
        }
        else 
            add_arg(term, coeff, mk_var(e));
    }

    template<typename num_t>
    typename arith_base<num_t>::var_t arith_base<num_t>::mk_op(arith_op_kind k, expr* e, expr* x, expr* y) {
        auto v = mk_var(e);
        auto w = mk_term(x);
        auto u = mk_term(y);
        unsigned idx = m_ops.size();
        num_t val;
        switch (k) {
        case arith_op_kind::OP_MOD:
            val = value(v) == 0 ? num_t(0) : mod(value(w), value(v));
            break;
        case arith_op_kind::OP_REM:
            if (value(v) == 0)
                val = 0;
            else {
                val = value(w);
                val %= value(v);
            }
            break;
        case arith_op_kind::OP_IDIV:
            val = value(v) == 0 ? num_t(0): div(value(w), value(v));
            break;
        case arith_op_kind::OP_DIV:
            val = value(v) == 0? num_t(0) : value(w) / value(v);
            break;
        case arith_op_kind::OP_ABS:
            val = abs(value(w));
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
        m_ops.push_back({v, k, v, w});
        m_vars[v].m_def_idx = idx;
        m_vars[v].m_op = k;
        m_vars[v].m_value = val;
        return v;
    }

    template<typename num_t>
    typename arith_base<num_t>::var_t arith_base<num_t>::mk_term(expr* e) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v != UINT_MAX)
            return v;
        linear_term t;
        add_args(t, e, num_t(1));
        if (t.m_coeff == 0 && t.m_args.size() == 1 && t.m_args[0].first == 1)
            return t.m_args[0].second;
        v = mk_var(e);
        auto idx = m_adds.size();
        num_t sum(t.m_coeff);
        m_adds.push_back({ t.m_args, t.m_coeff, v });
        for (auto const& [c, w] : t.m_args)
            m_vars[w].m_adds.push_back(idx), sum += c * value(w);
        m_vars[v].m_def_idx = idx;
        m_vars[v].m_op = arith_op_kind::OP_ADD;
        m_vars[v].m_value = sum;
        return v;
    }

    template<typename num_t>
    typename arith_base<num_t>::var_t arith_base<num_t>::mk_var(expr* e) {
        var_t v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX) {
            v = m_vars.size();
            m_expr2var.setx(e->get_id(), v, UINT_MAX);
            m_vars.push_back(var_info(e, a.is_int(e) ? var_sort::INT : var_sort::REAL));            
        }
        return v;
    }

    template<typename num_t>
    void arith_base<num_t>::init_bool_var(sat::bool_var bv) {
        if (m_bool_vars.get(bv, nullptr))
            return;
        expr* e = ctx.atom(bv);
        verbose_stream() << "bool var " << bv << " " << mk_bounded_pp(e, m) << "\n";
        if (!e)
            return;
        expr* x, * y;
        m_bool_vars.reserve(bv + 1);
        if (a.is_le(e, x, y) || a.is_ge(e, y, x)) {
            auto& ineq = new_ineq(ineq_kind::LE, num_t(0));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if ((a.is_lt(e, x, y) || a.is_gt(e, y, x)) && a.is_int(x)) {
            auto& ineq = new_ineq(ineq_kind::LE, num_t(1));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if ((a.is_lt(e, x, y) || a.is_gt(e, y, x)) && a.is_real(x)) {
            auto& ineq = new_ineq(ineq_kind::LT, num_t(0));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if (m.is_eq(e, x, y) && a.is_int_real(x)) {
            auto& ineq = new_ineq(ineq_kind::EQ, num_t(0));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if (m.is_distinct(e) && a.is_int_real(to_app(e)->get_arg(0))) {
            NOT_IMPLEMENTED_YET();
        }
        else if (a.is_is_int(e, x))
        {
            NOT_IMPLEMENTED_YET();
        }
#if 0
        else if (a.is_idivides(e, x, y))
            NOT_IMPLEMENTED_YET();
#endif
        else {
            SASSERT(!a.is_arith_expr(e));
        }
    }

    template<typename num_t>
    void arith_base<num_t>::init_ineq(sat::bool_var bv, ineq& i) {
        i.m_args_value = 0;
        for (auto const& [coeff, v] : i.m_args) {
            m_vars[v].m_bool_vars.push_back({ coeff, bv });
            i.m_args_value += coeff * value(v);
        }
        m_bool_vars.set(bv, &i);
    }

    template<typename num_t>
    void arith_base<num_t>::init_bool_var_assignment(sat::bool_var v) {
        auto* ineq = m_bool_vars.get(v, nullptr);
        if (ineq && ctx.is_true(sat::literal(v, false)) != (dtt(false, *ineq) == 0))
            ctx.flip(v);
    }

    template<typename num_t>
    void arith_base<num_t>::propagate_literal(sat::literal lit) {
        TRACE("sls", tout << "repair is-true: " << ctx.is_true(lit) << " lit: " << lit << "\n");
        if (!ctx.is_true(lit))
            return;
        auto const* ineq = atom(lit.var());
        if (!ineq)
            return;
        TRACE("sls", tout << "repair lit: " << lit << " ineq-is-true: " << ineq->is_true() << "\n");
        if (ineq->is_true() != lit.sign())
            return;        
        repair(lit, *ineq);
    }

    template<typename num_t>
    bool arith_base<num_t>::propagate() {
        return false;
    }

    template<typename num_t>
    void arith_base<num_t>::repair_up(app* e) {        
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX)
            return;
        auto const& vi = m_vars[v];
        if (vi.m_def_idx == UINT_MAX)
            return;
        m_ops.reserve(vi.m_def_idx + 1);
        auto const& od = m_ops[vi.m_def_idx];
        num_t v1, v2;
        switch (vi.m_op) {
        case LAST_ARITH_OP:
            break;
        case OP_ADD: {
            auto const& ad = m_adds[vi.m_def_idx];
            auto const& args = ad.m_args;
            num_t sum(ad.m_coeff);
            for (auto [c, w] : args)
                sum += c * value(w);
            update(v, sum);
            break;
        }
        case OP_MUL: {
            auto const& [w, coeff, monomial] = m_muls[vi.m_def_idx];
            num_t prod(coeff);
            for (auto w : monomial)
                prod *= value(w);
            update(v, prod);
            break;
        }
        case OP_MOD:
            v1 = value(od.m_arg1);
            v2 = value(od.m_arg2);
            update(v, v2 == 0 ? num_t(0) : mod(v1, v2));
            break;
        case OP_DIV:
            v1 = value(od.m_arg1);
            v2 = value(od.m_arg2);
            update(v, v2 == 0 ? num_t(0) : v1 / v2);
            break;
        case OP_IDIV:
            v1 = value(od.m_arg1);
            v2 = value(od.m_arg2);
            update(v, v2 == 0 ? num_t(0) : div(v1, v2));
            break;
        case OP_REM:
            v1 = value(od.m_arg1);
            v2 = value(od.m_arg2);
            update(v, v2 == 0 ? num_t(0) : v1 %= v2);
            break;
        case OP_ABS:
            update(v, abs(value(od.m_arg1)));
            break;
        default:
            NOT_IMPLEMENTED_YET();
        }
    }

    template<typename num_t>
    void arith_base<num_t>::repair_down(app* e) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX)
            return;
        auto const& vi = m_vars[v];
        if (vi.m_def_idx == UINT_MAX)
            return;
        TRACE("sls", tout << "repair def " << mk_bounded_pp(vi.m_expr, m) << "\n");
        switch (vi.m_op) {
        case arith_op_kind::LAST_ARITH_OP:
            break;
        case arith_op_kind::OP_ADD:
            repair_add(m_adds[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_MUL:
            repair_mul(m_muls[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_MOD:
            repair_mod(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_REM:
            repair_rem(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_POWER:
            repair_power(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_IDIV:
            repair_idiv(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_DIV:
            repair_div(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_ABS:
            repair_abs(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_TO_INT:
            repair_to_int(m_ops[vi.m_def_idx]);
            break;
        case arith_op_kind::OP_TO_REAL:
            repair_to_real(m_ops[vi.m_def_idx]);
            break;
        default:
            NOT_IMPLEMENTED_YET();
        }
    }

    template<typename num_t>
    void arith_base<num_t>::repair_add(add_def const& ad) {
        auto v = ad.m_var;
        auto const& coeffs = ad.m_args;
        num_t sum(ad.m_coeff);
        num_t val = value(v);
        for (auto const& [c, w] : coeffs)
            sum += c * value(w);
        if (val == sum)
            return;
        if (rand() % 20 == 0)
            update(v, sum);
        else {
            auto const& [c, w] = coeffs[rand() % coeffs.size()];
            num_t delta = sum - val;
            bool is_real = m_vars[w].m_sort == var_sort::REAL;
            bool round_down = rand() % 2 == 0;
            num_t new_value = value(w) + (is_real ? delta / c : round_down ? div(delta, c) : div(delta + c - 1, c));
            update(w, new_value);
        }
    }

    template<typename num_t>
    void arith_base<num_t>::repair_mul(mul_def const& md) {
        auto const& [v, coeff, monomial] = md;
        num_t product(coeff);
        num_t val = value(v);
        for (auto v : monomial)
            product *= value(v);
        if (product == val)
            return;
        if (rand() % 20 == 0) {
            update(v, product);
        }
        else if (val == 0) {
            auto v = monomial[ctx.rand(monomial.size())];
            num_t zero(0);
            update(v, zero);
        }
        else if (val == 1 || val == -1) {
            product = coeff;
            for (auto v : monomial) {
                num_t new_value(1);
                if (rand() % 2 == 0)
                    new_value = -1;
                product *= new_value;
                update(v, new_value);
            }
            if (product != val) {
                auto last = monomial.back();
                update(last, -value(last));
            }
        }
        else if (rand() % 2 == 0 && product != 0) {
            // value1(v) * product / value(v) = val
            // value1(v) = value(v) * val / product
            auto w = monomial[ctx.rand(monomial.size())];
            auto old_value = value(w);
            num_t new_value;
            if (m_vars[w].m_sort == var_sort::REAL) 
                new_value = old_value * val / product;
            else
                new_value = divide(w, old_value * val, product);
            update(w, new_value);
        }
        else {
            product = coeff;
            for (auto v : monomial) {
                num_t new_value{ 1 };
                if (rand() % 2 == 0)
                    new_value = -1;
                product *= new_value;
                update(v, new_value);
            }
            auto v = monomial[ctx.rand(monomial.size())];
            if ((product < 0 && 0 < val) || (val < 0 && 0 < product))
                update(v, -val * value(v));
            else
                update(v, val * value(v));
        }
    }

    template<typename num_t>
    void arith_base<num_t>::repair_rem(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        if (v2 == 0) {
            update(od.m_var, num_t(0));
            return;
        }         

        IF_VERBOSE(0, verbose_stream() << "todo repair rem");
        // bail
        v1 %= v2;
        update(od.m_var, v1);
    }

    template<typename num_t>
    void arith_base<num_t>::repair_abs(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        if (val < 0)
            update(od.m_var, abs(v1));
        else if (rand() % 2 == 0)
            update(od.m_arg1, val);
        else
            update(od.m_arg1, -val);        
    }

    template<typename num_t>
    void arith_base<num_t>::repair_to_int(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        if (val - 1 < v1 && v1 <= val)
            return;
        update(od.m_arg1, val);        
    }

    template<typename num_t>
    void arith_base<num_t>::repair_to_real(op_def const& od) {
        if (rand() % 20 == 0)
            update(od.m_var, value(od.m_arg1));
        else 
            update(od.m_arg1, value(od.m_arg1));
    }

    template<typename num_t>
    void arith_base<num_t>::repair_power(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        if (v1 == 0 && v2 == 0) {
            update(od.m_var, num_t(0));
            return;
        }
        IF_VERBOSE(0, verbose_stream() << "todo repair ^");
        NOT_IMPLEMENTED_YET();
    }

    template<typename num_t>
    void arith_base<num_t>::repair_mod(op_def const& od) {        
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        // repair first argument
        if (val >= 0 && val < v2) {
            auto v3 = mod(v1, v2);
            if (v3 == val)
                return;
            // find r, such that mod(v1 + r, v2) = val
            // v1 := v1 + val - v3 (+/- v2)
            v1 += val - v3;
            switch (rand() % 6) {
            case 0:
                v1 += v2;
                break;
            case 1:
                v1 -= v2;
                break;
            default:
                break;
            }
            update(od.m_arg1, v1);
            return;
        }
        update(od.m_var, v2 == 0 ? num_t(0) : mod(v1, v2));
    }

    template<typename num_t>
    void arith_base<num_t>::repair_idiv(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        IF_VERBOSE(0, verbose_stream() << "todo repair div");
        // bail
        update(od.m_var, v2 == 0 ? num_t(0) : div(v1, v2));
    }
    
    template<typename num_t>
    void arith_base<num_t>::repair_div(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        IF_VERBOSE(0, verbose_stream() << "todo repair /");
        // bail
        update(od.m_var, v2 == 0 ? num_t(0) : v1 / v2);
    }

    template<typename num_t>
    double arith_base<num_t>::reward(sat::literal lit) {
        if (m_dscore_mode)
            return dscore_reward(lit.var());
        else
            return dtt_reward(lit);
    }

    template<typename num_t>
    double arith_base<num_t>::dtt_reward(sat::literal lit) {
        auto* ineq = atom(lit.var());
        if (!ineq)
            return -1;
        num_t new_value;
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

    template<typename num_t>
    double arith_base<num_t>::dscore_reward(sat::bool_var bv) {
        m_dscore_mode = false;
        bool old_sign = sign(bv);
        sat::literal litv(bv, old_sign);
        auto* ineq = atom(bv);
        if (!ineq)
            return 0;
        SASSERT(ineq->is_true() != old_sign);
        num_t new_value;

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
    template<typename num_t>
    void arith_base<num_t>::on_rescale() {
        m_dscore_mode = true;
    }

    template<typename num_t>
    void arith_base<num_t>::on_restart() {
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v)
            init_bool_var_assignment(v);
        check_ineqs();
    }

    template<typename num_t>
    void arith_base<num_t>::check_ineqs() {
        auto check_bool_var = [&](sat::bool_var bv) {
            auto const* ineq = atom(bv);
            if (!ineq)
                return;
            num_t d = dtt(sign(bv), *ineq);
            sat::literal lit(bv, sign(bv));
            if (ctx.is_true(lit) != (d == 0)) {
                verbose_stream() << "invalid assignment " << bv << " " << *ineq << "\n";
            }
            VERIFY(ctx.is_true(lit) == (d == 0));
            };
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v)
            check_bool_var(v);
    }

    template<typename num_t>
    void arith_base<num_t>::register_term(expr* _e) {
        if (!is_app(_e))
            return;
        app* e = to_app(_e);
        auto v = ctx.atom2bool_var(e);
        if (v != sat::null_bool_var)
            init_bool_var(v);
        if (!a.is_arith_expr(e) && !m.is_eq(e) && !m.is_distinct(e))
            for (auto arg : *e)
                if (a.is_int_real(arg))
                    mk_term(arg);
    }

    template<typename num_t>
    void arith_base<num_t>::set_value(expr* e, expr* v) {
        if (!a.is_int_real(e))
            return;
        var_t w = m_expr2var.get(e->get_id(), UINT_MAX);
        if (w == UINT_MAX)
            w = mk_term(e);

        num_t n;
        if (!is_num(v, n))
            return;
        verbose_stream() << "set value " << w << " " << mk_bounded_pp(e, m) << " " << n << " " << value(w) << "\n";
        if (n == value(w))
            return;
        update(w, n);        
    }

    template<typename num_t>
    expr_ref arith_base<num_t>::get_value(expr* e) {
        auto v = mk_var(e);
        return expr_ref(a.mk_numeral(rational(m_vars[v].m_value.get_int64(), rational::i64()), a.is_int(e)), m);
    }

    template<typename num_t>
    bool arith_base<num_t>::is_sat() {
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

    template<typename num_t>
    std::ostream& arith_base<num_t>::display(std::ostream& out) const {
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v) {
            auto ineq = atom(v);
            if (ineq)
                out << v << ": " << *ineq << "\n";
        }
        for (unsigned v = 0; v < m_vars.size(); ++v) {
            auto const& vi = m_vars[v];
            out << "v" << v << " := " << vi.m_value << " (best " << vi.m_best_value << ") ";
            out << mk_bounded_pp(vi.m_expr, m) << " : ";
            for (auto [c, bv] : vi.m_bool_vars)
                out << c << "@" << bv << " ";
            out << "\n";
        }
        for (auto md : m_muls) {
            out << "v" << md.m_var << " := ";
            for (auto w : md.m_monomial)
                out << "v" << w << " ";
            out << "\n";
        }
        for (auto ad : m_adds) {
            out << "v" << ad.m_var << " := ";
            bool first = true;
            for (auto [c, w] : ad.m_args)
                out << (first?"":" + ") << c << "* v" << w;
            if (ad.m_coeff != 0)
                out << " + " << ad.m_coeff;
            out << "\n";
        }
        for (auto od : m_ops) {
            out << "v" << od.m_var << " := ";
            out << "v" << od.m_arg1 << " op-" << od.m_op << " v" << od.m_arg2 << "\n";
        }
        return out;
    }

    template<typename num_t>
    void arith_base<num_t>::mk_model(model& mdl) {
    }
}

template class sls::arith_base<checked_int64<true>>;
template class sls::arith_base<rational>;
