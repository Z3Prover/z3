/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sls_fpa_plugin.cpp

Abstract:

    Theory plugin for floating-point local search

Author:

    Atomic

--*/
#include "ast/sls/sls_fpa_plugin.h"
#include "ast/ast_pp.h"

namespace sls {

    fpa_plugin::fpa_plugin(context& ctx):
        plugin(ctx),
        m_fpa(m),
        m_rw(m),
        m_terms(m),
        m_values(m),
        m_gpu(ctx) {
        m_fid = m_fpa.get_family_id();
    }

    void fpa_plugin::not_supported() const {
        throw default_exception("floating-point local search plugin not implemented yet for this term");
    }

    expr* fpa_plugin::value(expr* e) const {
        return m_values.get(e->get_id(), nullptr);
    }

    void fpa_plugin::cache_value(expr* e, expr* v) {
        m_values.setx(e->get_id(), v);
    }

    bool fpa_plugin::contains_fp_term(expr* e) const {
        if (!e)
            return false;
        if (m_fpa.is_float(e) || m_fpa.is_rm(e))
            return true;
        if (!is_app(e))
            return false;
        for (expr* arg : *to_app(e)) {
            if (contains_fp_term(arg))
                return true;
        }
        return false;
    }

    bool fpa_plugin::is_fp_atomic_predicate(expr* e) const {
        if (!is_app(e) || !m.is_bool(e))
            return false;
        auto* a = to_app(e);
        if (a->get_decl()->get_family_id() == m_fid)
            return true;
        if (m.is_eq(e))
            return m_fpa.is_float(a->get_arg(0)) && m_fpa.is_float(a->get_arg(1));
        if (m.is_distinct(e) && a->get_num_args() == 2)
            return m_fpa.is_float(a->get_arg(0)) && m_fpa.is_float(a->get_arg(1));
        return false;
    }

    bool fpa_plugin::is_fp_predicate(expr* e) const {
        return m.is_bool(e) && contains_fp_term(e);
    }

    expr* fpa_plugin::mk_int_value(sort* s, int value) {
        scoped_mpf v(m_fpa.fm());
        m_fpa.fm().set(v, m_fpa.get_ebits(s), m_fpa.get_sbits(s), value);
        return m_fpa.mk_value(v);
    }

    bool fpa_plugin::assign_var(expr* e, expr* v) {
        if (!is_uninterp_const(e) || !m_fpa.is_float(e) || e->get_sort() != v->get_sort())
            return false;
        cache_value(e, v);
        ctx.new_value_eh(e);
        return true;
    }

    expr_ref fpa_plugin::eval_bool(app* a) {
        expr* e = a;
        expr_ref result(m);
        if (m.is_not(e)) {
            result = m.mk_not(eval(a->get_arg(0)));
            return result;
        }
        if (m.is_and(e)) {
            for (expr* arg : *a) {
                if (m.is_false(eval(arg))) {
                    result = m.mk_false();
                    return result;
                }
            }
            result = m.mk_true();
            return result;
        }
        if (m.is_or(e)) {
            for (expr* arg : *a) {
                if (m.is_true(eval(arg))) {
                    result = m.mk_true();
                    return result;
                }
            }
            result = m.mk_false();
            return result;
        }
        if (m.is_implies(e)) {
            result = m.mk_bool_val(!m.is_true(eval(a->get_arg(0))) || m.is_true(eval(a->get_arg(1))));
            return result;
        }
        if (m.is_iff(e)) {
            result = m.mk_bool_val(m.is_true(eval(a->get_arg(0))) == m.is_true(eval(a->get_arg(1))));
            return result;
        }
        if (m.is_ite(e)) {
            result = m.is_true(eval(a->get_arg(0))) ? eval(a->get_arg(1)) : eval(a->get_arg(2));
            return result;
        }
        if (m.is_xor(e)) {
            bool b = false;
            for (expr* arg : *a)
                b ^= m.is_true(eval(arg));
            result = m.mk_bool_val(b);
            return result;
        }
        if (m.is_eq(e) && m.is_bool(a->get_arg(0))) {
            result = m.mk_bool_val(m.is_true(eval(a->get_arg(0))) == m.is_true(eval(a->get_arg(1))));
            return result;
        }
        if (m.is_distinct(e) && a->get_num_args() == 2 && m.is_bool(a->get_arg(0))) {
            result = m.mk_bool_val(m.is_true(eval(a->get_arg(0))) != m.is_true(eval(a->get_arg(1))));
            return result;
        }
        not_supported();
        return expr_ref(m);
    }

    expr_ref fpa_plugin::eval(expr* e) {
        if (m_fpa.is_numeral(e) || m_fpa.is_rm_numeral(e)) {
            cache_value(e, e);
            return expr_ref(e, m);
        }
        if (!is_app(e))
            not_supported();

        auto* a = to_app(e);
        if (is_uninterp_const(e)) {
            if (auto* v = value(e))
                return expr_ref(v, m);
            if (m_fpa.is_float(e)) {
                expr* v = m_fpa.mk_pzero(e->get_sort());
                cache_value(e, v);
                return expr_ref(v, m);
            }
            if (m_fpa.is_rm(e)) {
                expr* v = m_fpa.mk_round_nearest_ties_to_even();
                cache_value(e, v);
                return expr_ref(v, m);
            }
        }

        if (m.is_bool(e) && a->get_decl()->get_family_id() != m_fid && !m.is_eq(e) && !m.is_distinct(e))
            return eval_bool(a);

        expr_ref_vector args(m);
        for (expr* arg : *a)
            args.push_back(eval(arg));

        expr_ref r(m);
        if (m.is_eq(e) && m_fpa.is_float(a->get_arg(0))) {
            auto st = m_rw.mk_float_eq(args.get(0), args.get(1), r);
            if (st == BR_FAILED)
                not_supported();
            return r;
        }
        if (m.is_distinct(e) && a->get_num_args() == 2 && m_fpa.is_float(a->get_arg(0))) {
            auto st = m_rw.mk_float_eq(args.get(0), args.get(1), r);
            if (st == BR_FAILED)
                not_supported();
            return expr_ref(m.mk_not(r), m);
        }
        if (a->get_decl()->get_family_id() != m_fid)
            not_supported();

        auto st = m_rw.mk_app_core(a->get_decl(), a->get_num_args(), args.data(), r);
        if (st == BR_FAILED)
            not_supported();
        return r;
    }

    bool fpa_plugin::try_candidate(expr* var, expr* candidate, expr* goal, bool desired) {
        expr_ref old(eval(var), m);
        cache_value(var, candidate);
        expr_ref v = eval(goal);
        bool ok = (m.is_true(v) && desired) || (m.is_false(v) && !desired);
        if (ok) {
            ctx.new_value_eh(var);
            return true;
        }
        cache_value(var, old);
        return false;
    }

    void fpa_plugin::collect_seed_atoms(expr* e, bool desired, ptr_vector<app>& seeds) {
        if (!is_app(e))
            return;
        auto* a = to_app(e);
        if (is_fp_atomic_predicate(e)) {
            seeds.push_back(a);
            return;
        }
        if (m.is_not(e)) {
            collect_seed_atoms(a->get_arg(0), !desired, seeds);
            return;
        }
        if (m.is_and(e) || m.is_or(e)) {
            for (expr* arg : *a) {
                bool child_true = m.is_true(eval(arg));
                if ((desired && !child_true) || (!desired && child_true))
                    collect_seed_atoms(arg, desired, seeds);
            }
            return;
        }
        if (m.is_implies(e)) {
            if (desired) {
                if (m.is_true(eval(a->get_arg(0))) && !m.is_true(eval(a->get_arg(1)))) {
                    collect_seed_atoms(a->get_arg(0), false, seeds);
                    collect_seed_atoms(a->get_arg(1), true, seeds);
                }
            }
            else {
                collect_seed_atoms(a->get_arg(0), true, seeds);
                collect_seed_atoms(a->get_arg(1), false, seeds);
            }
            return;
        }
        if (m.is_iff(e)) {
            collect_seed_atoms(a->get_arg(0), true, seeds);
            collect_seed_atoms(a->get_arg(1), true, seeds);
            return;
        }
        if (m.is_ite(e)) {
            if (m.is_true(eval(a->get_arg(0))))
                collect_seed_atoms(a->get_arg(1), desired, seeds);
            else
                collect_seed_atoms(a->get_arg(2), desired, seeds);
            return;
        }
    }

    bool fpa_plugin::add_candidates_from_atom(app* atom, vector<fpa_lookahead_candidate>& candidates) {
        auto kind = static_cast<fpa_op_kind>(atom->get_decl()->get_decl_kind());
        expr* target = nullptr;
        expr_ref fixed(m);

        auto add_candidate = [&](expr* val) {
            fpa_lookahead_candidate c;
            c.vars.push_back(target);
            c.values.push_back(val);
            candidates.push_back(c);
        };

        switch (kind) {
        case OP_FPA_EQ:
        case OP_FPA_LT:
        case OP_FPA_LE:
        case OP_FPA_GT:
        case OP_FPA_GE:
            if (ctx.is_fixed(atom->get_arg(1), fixed) && is_uninterp_const(atom->get_arg(0)))
                target = atom->get_arg(0);
            else if (ctx.is_fixed(atom->get_arg(0), fixed) && is_uninterp_const(atom->get_arg(1)))
                target = atom->get_arg(1);
            else
                return false;
            add_candidate(fixed.get());
            add_candidate(m_fpa.mk_ninf(target->get_sort()));
            add_candidate(m_fpa.mk_pinf(target->get_sort()));
            break;
        case OP_FPA_IS_NAN:
        case OP_FPA_IS_INF:
        case OP_FPA_IS_ZERO:
        case OP_FPA_IS_POSITIVE:
        case OP_FPA_IS_NEGATIVE:
        case OP_FPA_IS_NORMAL:
            target = atom->get_arg(0);
            if (!is_uninterp_const(target))
                return false;
            add_candidate(m_fpa.mk_pzero(target->get_sort()));
            add_candidate(m_fpa.mk_nzero(target->get_sort()));
            add_candidate(m_fpa.mk_nan(target->get_sort()));
            add_candidate(m_fpa.mk_pinf(target->get_sort()));
            add_candidate(m_fpa.mk_ninf(target->get_sort()));
            add_candidate(mk_int_value(target->get_sort(), 1));
            break;
        default:
            return false;
        }
        return true;
    }

    bool fpa_plugin::repair_predicate_lookahead(app* e, bool desired) {
        ptr_vector<app> seeds;
        vector<fpa_lookahead_candidate> candidates;
        ptr_vector<expr> dag;

        collect_seed_atoms(e, desired, seeds);
        for (app* atom : seeds)
            add_candidates_from_atom(atom, candidates);
        if (candidates.empty())
            return false;

        m_gpu.serialize_dag(e, dag);
        int idx = m_gpu.choose_candidate(e, desired, dag, candidates,
            [&](fpa_lookahead_candidate const& c) {
                SASSERT(c.vars.size() == 1 && c.values.size() == 1);
                return try_candidate(c.vars[0], c.values[0], e, desired);
            });
        return idx >= 0;
    }

    void fpa_plugin::register_term(expr* e) {
        if (is_fp_predicate(e) || m_fpa.is_float(e) || m_fpa.is_rm(e))
            m_terms.push_back(e);
    }

    expr_ref fpa_plugin::get_value(expr* e) {
        if (is_fp_predicate(e) || m_fpa.is_float(e) || m_fpa.is_rm(e))
            return eval(e);
        return expr_ref(m);
    }

    void fpa_plugin::initialize() {
        for (expr* e : m_terms)
            if (m_fpa.is_float(e) || m_fpa.is_rm(e))
                (void)eval(e);
    }

    void fpa_plugin::propagate_literal(sat::literal) {
    }

    bool fpa_plugin::propagate() {
        return false;
    }

    bool fpa_plugin::repair_down(app*) {
        return false;
    }

    void fpa_plugin::repair_up(app*) {
    }

    void fpa_plugin::repair_literal(sat::literal lit) {
        if (!ctx.is_true(lit))
            return;
        auto e = ctx.atom(lit.var());
        if (!is_fp_predicate(e))
            return;
        bool desired = !lit.sign();
        expr_ref v = eval(e);
        if ((m.is_true(v) && desired) || (m.is_false(v) && !desired))
            return;
        if (!repair_predicate_lookahead(to_app(e), desired))
            ctx.flip(lit.var());
    }

    bool fpa_plugin::is_sat() {
        for (expr* e : m_terms) {
            if (!is_fp_predicate(e))
                continue;
            expr_ref v = eval(e);
            if (!m.is_true(v) && !m.is_false(v))
                not_supported();
            if (m.is_true(v) != ctx.is_true(e))
                return false;
        }
        return true;
    }

    std::ostream& fpa_plugin::display(std::ostream& out) const {
        out << "floating-point local search plugin: " << m_terms.size() << " terms\n";
        return out;
    }

    bool fpa_plugin::set_value(expr* e, expr* v) {
        if (!m_fpa.is_float(e) && !m_fpa.is_rm(e))
            return false;
        if (e->get_sort() != v->get_sort())
            return false;
        cache_value(e, v);
        return true;
    }

    void fpa_plugin::collect_statistics(statistics& st) const {
        st.copy(m_stats);
        st.update("sls-fpa-terms", m_terms.size());
    }

    void fpa_plugin::reset_statistics() {
        m_stats.reset();
    }

}
