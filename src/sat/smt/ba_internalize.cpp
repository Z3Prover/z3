/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    ba_internalize.h

Abstract:

    Internalize methods for Boolean algebra operators.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/


#include "sat/smt/ba_internalize.h"

namespace sat {

    literal ba_internalize::internalize(expr* e, bool sign, bool root) {
        if (pb.is_pb(e)) 
            return internalize_pb(e, sign, root);
        if (m.is_xor(e))
            return internalize_xor(e, sign, root);
        UNREACHABLE();
        return null_literal;
    }

    literal ba_internalize::internalize_xor(expr* e, bool sign, bool root) {
        sat::literal_vector lits;
        sat::bool_var v = m_solver.add_var(true);
        lits.push_back(literal(v, true));
        auto add_expr = [&](expr* a) {
            literal lit = si.internalize(a);
            m_solver.set_external(lit.var());
            lits.push_back(lit);
        };
        expr* e1 = nullptr;
        while (m.is_iff(e, e1, e))
            add_expr(e1);
        add_expr(e);
        // ensure that = is converted to xor
        for (unsigned i = 1; i + 1 < lits.size(); ++i) {
            lits[i].neg();
        }
        ba.add_xr(lits);
        auto* aig = m_solver.get_cut_simplifier();
        if (aig) aig->add_xor(~lits.back(), lits.size() - 1, lits.c_ptr() + 1);
        sat::literal lit(v, sign);
        return literal(v, sign);
    }

    literal ba_internalize::internalize_pb(expr* e, bool sign, bool root) {
        SASSERT(pb.is_pb(e));
        app* t = to_app(e);
        rational k = pb.get_k(t);
        switch (t->get_decl_kind()) {
        case OP_AT_MOST_K:
            return convert_at_most_k(t, k, root, sign);
        case OP_AT_LEAST_K:
            return convert_at_least_k(t, k, root, sign);
        case OP_PB_LE:
            if (pb.has_unit_coefficients(t))
                return convert_at_most_k(t, k, root, sign);
            else
                return convert_pb_le(t, root, sign);
        case OP_PB_GE:
            if (pb.has_unit_coefficients(t))
                return convert_at_least_k(t, k, root, sign);
            else
                return convert_pb_ge(t, root, sign);
        case OP_PB_EQ:
            if (pb.has_unit_coefficients(t))
                return convert_eq_k(t, k, root, sign);
            else
                return convert_pb_eq(t, root, sign);
        default:
            UNREACHABLE();
        }
        return null_literal;
    }

    void ba_internalize::check_unsigned(rational const& c) {
        if (!c.is_unsigned()) {
            throw default_exception("unsigned coefficient expected");
        }
    }

    void ba_internalize::convert_to_wlits(app* t, sat::literal_vector const& lits, svector<wliteral>& wlits) {
        for (unsigned i = 0; i < lits.size(); ++i) {
            rational c = pb.get_coeff(t, i);
            check_unsigned(c);
            wlits.push_back(std::make_pair(c.get_unsigned(), lits[i]));
        }
    }

    void ba_internalize::convert_pb_args(app* t, literal_vector& lits) {
        for (expr* arg : *t) {
            lits.push_back(si.internalize(arg));
            m_solver.set_external(lits.back().var());
        }
    }

    void ba_internalize::convert_pb_args(app* t, svector<wliteral>& wlits) {
        sat::literal_vector lits;
        convert_pb_args(t, lits);    
        convert_to_wlits(t, lits, wlits);
    }

    literal ba_internalize::convert_pb_le(app* t, bool root, bool sign) {
        rational k = pb.get_k(t);
        k.neg();
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        for (wliteral& wl : wlits) {
            wl.second.neg();
            k += rational(wl.first);
        }
        check_unsigned(k);
        if (root && m_solver.num_user_scopes() == 0) {
            unsigned k1 = k.get_unsigned();
            if (sign) {
                k1 = 1 - k1;
                for (wliteral& wl : wlits) {
                    wl.second.neg();
                    k1 += wl.first;
                }
            }
            ba.add_pb_ge(null_bool_var, wlits, k1);
            return null_literal;
        }
        else {
            bool_var v = m_solver.add_var(true);
            literal lit(v, sign);
            ba.add_pb_ge(v, wlits, k.get_unsigned());
            TRACE("ba", tout << "root: " << root << " lit: " << lit << "\n";);
            return lit;
        }
    }


    literal ba_internalize::convert_pb_ge(app* t, bool root, bool sign) {
        rational k = pb.get_k(t);
        check_unsigned(k);
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        if (root && m_solver.num_user_scopes() == 0) {
            unsigned k1 = k.get_unsigned();
            if (sign) {
                k1 = 1 - k1;
                for (wliteral& wl : wlits) {
                    wl.second.neg();
                    k1 += wl.first;
                }
            }
            ba.add_pb_ge(sat::null_bool_var, wlits, k1);
            return null_literal;
        }
        else {
            sat::bool_var v = m_solver.add_var(true);
            sat::literal lit(v, sign);
            ba.add_pb_ge(v, wlits, k.get_unsigned());
            TRACE("goal2sat", tout << "root: " << root << " lit: " << lit << "\n";);
            return lit;
        }
    }

    literal ba_internalize::convert_pb_eq(app* t, bool root, bool sign) {
        rational k = pb.get_k(t);
        SASSERT(k.is_unsigned());
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        bool base_assert = (root && !sign && m_solver.num_user_scopes() == 0);
        bool_var v1 = base_assert ? null_bool_var : m_solver.add_var(true);
        bool_var v2 = base_assert ? null_bool_var : m_solver.add_var(true);
        ba.add_pb_ge(v1, wlits, k.get_unsigned());
        k.neg();
        for (wliteral& wl : wlits) {
            wl.second.neg();
            k += rational(wl.first);
        }
        check_unsigned(k);
        ba.add_pb_ge(v2, wlits, k.get_unsigned());
        if (base_assert) {
            return null_literal;
        }
        else {
            literal l1(v1, false), l2(v2, false);
            bool_var v = m_solver.add_var(false);
            literal l(v, false);
            si.mk_clause(~l, l1);
            si.mk_clause(~l, l2);
            si.mk_clause(~l1, ~l2, l);
            si.cache(t, l);
            if (sign) l.neg();
            return l;
        }
    }

    literal ba_internalize::convert_at_least_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        literal_vector lits;
        convert_pb_args(t, lits);
        unsigned k2 = k.get_unsigned();
        if (root && m_solver.num_user_scopes() == 0) {
            if (sign) {
                for (literal& l : lits) l.neg();
                k2 = lits.size() + 1 - k2;
            }
            ba.add_at_least(null_bool_var, lits, k2);
            return null_literal;
        }
        else {
            bool_var v = m_solver.add_var(true);
            literal lit(v, false);
            ba.add_at_least(v, lits, k.get_unsigned());
            si.cache(t, lit);
            if (sign) lit.neg();
            TRACE("ba", tout << "root: " << root << " lit: " << lit << "\n";);
            return lit;
        }
    }

    literal ba_internalize::convert_at_most_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        literal_vector lits;
        convert_pb_args(t, lits);
        for (literal& l : lits) {
            l.neg();
        }
        unsigned k2 = lits.size() - k.get_unsigned();
        if (root && m_solver.num_user_scopes() == 0) {
            if (sign) {
                for (literal& l : lits) l.neg();
                k2 = lits.size() + 1 - k2;
            }
            ba.add_at_least(null_bool_var, lits, k2);
            return null_literal;
        }
        else {
            bool_var v = m_solver.add_var(true);
            literal lit(v, false);
            ba.add_at_least(v, lits, k2);
            si.cache(t, lit);
            if (sign) lit.neg();
            return lit;
        }
    }

    literal ba_internalize::convert_eq_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        literal_vector lits;
        convert_pb_args(t, lits);
        bool_var v1 = (root && !sign) ? null_bool_var : m_solver.add_var(true);
        bool_var v2 = (root && !sign) ? null_bool_var : m_solver.add_var(true);
        ba.add_at_least(v1, lits, k.get_unsigned());
        for (literal& l : lits) {
            l.neg();
        }
        ba.add_at_least(v2, lits, lits.size() - k.get_unsigned());

        if (!root || sign) {        
            literal l1(v1, false), l2(v2, false);
            bool_var v = m_solver.add_var(false);
            literal l(v, false);
            si.mk_clause(~l, l1);
            si.mk_clause(~l, l2);
            si.mk_clause(~l1, ~l2, l);
            si.cache(t, l);
            if (sign) l.neg();
            return l;
        }
        else {
            return null_literal;
        }
    }

    expr_ref ba_decompile::get_card(std::function<expr_ref(sat::literal)>& lit2expr, ba_solver::card const& c) {
        ptr_buffer<expr> lits;
        for (sat::literal l : c) {
            lits.push_back(lit2expr(l));
        }
        expr_ref fml(pb.mk_at_least_k(c.size(), lits.c_ptr(), c.k()), m);

        if (c.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(c.lit()), fml);
        }
        return fml;
    }

    expr_ref ba_decompile::get_pb(std::function<expr_ref(sat::literal)>& lit2expr, ba_solver::pb const& p)  {
        ptr_buffer<expr> lits;
        vector<rational> coeffs;
        for (auto const& wl : p) {
            lits.push_back(lit2expr(wl.second));
            coeffs.push_back(rational(wl.first));
        }
        rational k(p.k());
        expr_ref fml(pb.mk_ge(p.size(), coeffs.c_ptr(), lits.c_ptr(), k), m);

        if (p.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(p.lit()), fml);
        }
        return fml;
    }

    expr_ref ba_decompile::get_xor(std::function<expr_ref(sat::literal)>& lit2expr, ba_solver::xr const& x) {
        ptr_buffer<expr> lits;
        for (sat::literal l : x) {
            lits.push_back(lit2expr(l));
        }
        expr_ref fml(m.mk_xor(x.size(), lits.c_ptr()), m);

        if (x.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(x.lit()), fml);
        }
        return fml;
    }

    bool ba_decompile::to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) {
        for (auto* c : ba.constraints()) {
            switch (c->tag()) {
            case ba_solver::card_t:
                fmls.push_back(get_card(l2e, c->to_card()));
                break;
            case sat::ba_solver::pb_t:
                fmls.push_back(get_pb(l2e, c->to_pb()));
                break;
            case sat::ba_solver::xr_t:
                fmls.push_back(get_xor(l2e, c->to_xr()));
                break;
            }
        }
        return true;
    }
}
