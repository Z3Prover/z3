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
    /// need to initialize ineqs (arithmetical atoms)
    /// 
    

    sls::sls(solver& s): 
        s(s), m(s.m) {}

    void sls::operator()(bool_vector& phase) {
        
        unsigned num_steps = 0;
        for (unsigned v = 0; v < s.s().num_vars(); ++v)
            init_bool_var_assignment(v);
        m_best_min_unsat = unsat().size();
        while (m.inc() && m_best_min_unsat > 0 && num_steps < m_max_arith_steps) {
            if (!flip())
                break;
            ++m_stats.m_num_flips;
            ++num_steps;
            unsigned num_unsat = unsat().size();
            if (num_unsat < m_best_min_unsat) {
                m_best_min_unsat = num_unsat;
                num_steps = 0;
                save_best_values();
            }
        }
        IF_VERBOSE(2, verbose_stream() << "(sls " << m_stats.m_num_flips << " " << unsat().size() << ")\n");
    }

    void sls::save_best_values() {
        // first compute assignment to terms
        // then update non-basic variables in tableau, assuming a sat solution was found.
#if false
        for (auto const& [t, v] : terms) {
            rational val;
            lp::lar_term const& term = lp().get_term(t);
            for (lp::lar_term::ival arg : term) {
                auto t2 = lp().column2tv(arg.column());
                auto w = lp().local_to_external(t2.id());
                val += arg.coeff() * local_search.value(w);
            }
            update(v, val);
        }
#endif

        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            if (s.is_bool(v))
                continue;
            if (!s.lp().external_is_used(v))
                continue;
            rational old_value = s.is_registered_var(v) ? s.get_ivalue(v).x : rational::zero();
            rational new_value = value(v);
            if (old_value == new_value)
                continue;
            s.ensure_column(v);
            lp::column_index vj = s.lp().to_column_index(v);
            SASSERT(!vj.is_null());
            if (!s.lp().is_base(vj.index())) {
                lp::impq val(new_value);
                s.lp().set_value_for_nbasic_column(vj.index(), val);
            }
        }
    }

    void sls::set(sat::ddfw* d) { 
        m_bool_search = d; 
        add_vars();
        m_clauses.resize(d->num_clauses());
        for (unsigned i = 0; i < d->num_clauses(); ++i)
            for (sat::literal lit : *d->get_clause_info(i).m_clause)
                init_literal(lit);
    }

    void sls::set_bounds_begin() {        
        m_max_arith_steps = 0;
    }

    void sls::set_bounds(enode* n) {
        ++m_max_arith_steps;
    }

    void sls::set_bounds_end(unsigned num_literals) {
        m_max_arith_steps = (m_config.L * m_max_arith_steps) / num_literals;
    }

    bool sls::flip() {
        log();
        return flip_unsat() || flip_clauses() || flip_dscore();
    }

    // distance to true
    rational sls::dtt(rational const& args, ineq const& ineq) const {
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
            if (args < ineq.m_bound)
                return rational::zero();
            return args - ineq.m_bound + 1;
        default:
            UNREACHABLE();
            return rational::zero();
        }
    }

    rational sls::dtt(ineq const& ineq, var_t v, rational const& new_value) const {
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
    bool sls::cm(ineq const& ineq, var_t v, rational& new_value) {
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
                    UNREACHABLE(); 
                    break;
                }
            }
        }
        return false;
    }

    bool sls::flip_unsat() {
        unsigned start = s.random();
        unsigned sz = unsat().size();
        for (unsigned i = sz; i-- > 0; ) 
            if (flip(unsat().elem_at((i + start) % sz)))
                return true;        
        return false;
    }

    bool sls::flip(unsigned cl) {
        auto const& clause = get_clause(cl);
        rational new_value;
        for (literal lit : clause) {
            auto const* ineq = atom(lit);
            if (!ineq || ineq->is_true())
                continue;
            for (auto const& [coeff, v] : ineq->m_args) {
                if (!cm(*ineq, v, new_value))
                    continue;
                int score = cm_score(v, new_value);
                if (score <= 0)
                    continue;
                unsigned num_unsat = unsat().size();
                update(v, new_value);
                IF_VERBOSE(2,
                    verbose_stream() << "score " << v << " " << score << "\n"
                    << num_unsat << " -> " << unsat().size() << "\n");
                return true;
            }
        }
        return false;
    }

    bool sls::flip_clauses() {
        unsigned start = s.random();
        unsigned sz = m_bool_search->num_clauses();
        for (unsigned i = sz; i-- > 0; )
            if (flip((i + start) % sz))
                return true;
        return false;
    }

    bool sls::flip_dscore() {
        paws();
        unsigned start = s.random();
        unsigned sz = unsat().size();
        for (unsigned i = sz; i-- > 0; ) 
            if (flip_dscore(unsat().elem_at((i + start) % sz)))
                return true;        
        return false;
    }

    bool sls::flip_dscore(unsigned cl) {
        auto const& clause = get_clause(cl);
        rational new_value, min_value, min_score(-1);
        var_t min_var = UINT_MAX;
        for (auto lit : clause) {
            auto const* ineq = atom(lit);
            if (!ineq || ineq->is_true())
                continue;
            for (auto const& [coeff, v] : ineq->m_args) {
                if (cm(*ineq, v, new_value)) {
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

    /**
    * redistribute weights of clauses. TODO - re-use ddfw weights instead.
    */
    void sls::paws() {
        for (unsigned cl = num_clauses(); cl-- > 0; ) {
            auto& clause = get_clause_info(cl);
            bool above = 10000 * m_config.sp <= (s.random() % 10000);
            if (!above && clause.is_true() && get_weight(cl) > 1)
                get_weight(cl) -= 1;
            if (above && !clause.is_true())
                get_weight(cl) += 1;
        }
    }

    //
    // dscore(op) = sum_c (dts(c,alpha) - dts(c,alpha_after)) * weight(c)
    // 
    rational sls::dscore(var_t v, rational const& new_value) const {
        auto const& vi = m_vars[v];
        rational score(0);
        for (auto const& [coeff, lit] : vi.m_literals) 
            for (auto cl : m_bool_search->get_use_list(lit))              
                score += (dts(cl) - dts(cl, v, new_value)) * rational(get_weight(cl));        
        return score;
    }

    int sls::cm_score(var_t v, rational const& new_value) {
        int score = 0;
        auto& vi = m_vars[v];
        for (auto const& [coeff, lit] : vi.m_literals) {
            auto const& ineq = *atom(lit);            
            rational dtt_old = dtt(ineq);
            rational dtt_new = dtt(ineq, v, new_value);
            for (auto cl : m_bool_search->get_use_list(lit)) {
                auto const& clause = get_clause_info(cl);
                if (!clause.is_true()) {
                    if (dtt_new == 0)
                        ++score;  // false -> true
                }
                else if (dtt_new == 0 || dtt_old > 0 || clause.m_num_trues > 0) // true -> true ?? TODO
                    continue;
                else if (all_of(*clause.m_clause, [&](auto lit) { return !atom(lit) || dtt(*atom(lit), v, new_value) > 0; })) // ?? TODO
                    --score;
            }
        }
        return score;
    }

    rational sls::dts(unsigned cl) const {
        rational d(1), d2;
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

    rational sls::dts(unsigned cl, var_t v, rational const& new_value) const {
        rational d(1), d2;
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

    void sls::update(var_t v, rational const& new_value) {
        auto& vi = m_vars[v];
        auto const& old_value = vi.m_value;
        for (auto const& [coeff, lit] : vi.m_literals) {
            auto& ineq = *atom(lit);
            rational dtt_old = dtt(ineq);
            ineq.m_args_value += coeff * (new_value - old_value);
            rational dtt_new = dtt(ineq);
            SASSERT(!(dtt_new == 0 && dtt_new < dtt_old) || m_bool_search->get_value(lit.var()) == lit.sign());
            SASSERT(!(dtt_old == 0 && dtt_new > dtt_old) || m_bool_search->get_value(lit.var()) != lit.sign());
            if (dtt_new == 0 && dtt_new < dtt_old)        // flip from false to true
                m_bool_search->flip(lit.var());                                                  
            else if (dtt_old == 0 && dtt_old < dtt_new)   // flip from true to false
                m_bool_search->flip(lit.var());  
            dtt(ineq) = dtt_new;
            SASSERT((dtt_new == 0) == (m_bool_search->get_value(lit.var()) != lit.sign()));
        }
        vi.m_value = new_value;
    }

    void sls::add_vars() {
        SASSERT(m_vars.empty());
        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            rational value = s.is_registered_var(v) ? s.get_ivalue(v).x : rational::zero();
            value = s.is_int(v) ? ceil(value) : value;
            auto k = s.is_int(v) ? sls::var_kind::INT : sls::var_kind::REAL;
            m_vars.push_back({ value, value, k, {} });
        }
    }

    sls::ineq& sls::new_ineq(ineq_kind op, rational const& bound) {
        auto* i = alloc(ineq);
        i->m_bound = bound;
        i->m_op = op;
        return *i;
    }

    void sls::add_arg(sat::literal lit, ineq& ineq, rational const& c, var_t v) {
        ineq.m_args.push_back({ c, v });
        ineq.m_args_value += c * value(v);
        m_vars[v].m_literals.push_back({ c, lit });
    }

    void sls::add_bounds(sat::literal_vector& bounds) {
        unsigned bvars = s.s().num_vars();
        auto add_ineq = [&](sat::literal lit, ineq& i) {
            m_literals.set(lit.index(), &i);
            bounds.push_back(lit);
        };
        for (unsigned v = 0; v < s.get_num_vars(); ++v) {
            rational lo, hi;
            bool is_strict_lo = false, is_strict_hi = false;
            lp::constraint_index ci;
            if (!s.is_registered_var(v))
                continue;
            lp::column_index vi = s.lp().to_column_index(v);
            if (vi.is_null())
                continue;
            bool has_lo = s.lp().has_lower_bound(vi.index(), ci, lo, is_strict_lo);
            bool has_hi = s.lp().has_upper_bound(vi.index(), ci, hi, is_strict_hi);

            if (has_lo && has_hi && lo == hi) {
                auto& ineq = new_ineq(sls::ineq_kind::EQ, lo);
                sat::literal lit(bvars++);
                add_arg(lit, ineq, rational::one(), v);
                add_ineq(lit, ineq);
                continue;
            }
            if (has_lo) {
                auto& ineq = new_ineq(is_strict_lo ? sls::ineq_kind::LT : sls::ineq_kind::LE, -lo);
                sat::literal lit(bvars++);
                add_arg(lit, ineq, -rational::one(), v);
                add_ineq(lit, ineq);
            }
            if (has_hi) {
                auto& ineq = new_ineq(is_strict_hi ? sls::ineq_kind::LT : sls::ineq_kind::LE, hi);
                sat::literal lit(bvars++);
                add_arg(lit, ineq, rational::one(), v);
                add_ineq(lit, ineq);
            }
        }
    }


    void sls::add_args(ineq& ineq, lp::tv t, theory_var v, rational sign) {
        if (t.is_term()) {
            lp::lar_term const& term = s.lp().get_term(t);

            for (lp::lar_term::ival arg : term) {
                auto t2 = s.lp().column2tv(arg.column());
                auto w = s.lp().local_to_external(t2.id());
                ineq.m_args.push_back({ sign * arg.coeff(), w });
            }
        }
        else
            ineq.m_args.push_back({ sign, s.lp().local_to_external(t.id()) });
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
            auto& ineq = new_ineq(op, bound);

            add_args(ineq, t, b->get_var(), should_minus ? rational::minus_one() :rational::one());
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
            auto& ineq = new_ineq(lit.sign() ? sls::ineq_kind::NE : sls::ineq_kind::EQ, rational::zero());            
            add_args(ineq, tu, u, rational::one());
            add_args(ineq, tv, v, -rational::one());
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
        if (ineq && m_bool_search->get_value(lit.var()) != (dtt(*ineq) == 0))
            m_bool_search->flip(lit.var());
    }
}

