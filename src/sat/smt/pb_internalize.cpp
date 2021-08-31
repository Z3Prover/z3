/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    ba_internalize.cpp

Abstract:

    Internalize methods for Boolean algebra operators.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/


#include "sat/smt/pb_solver.h"
#include "ast/pb_decl_plugin.h"

namespace pb {

    void solver::internalize(expr* e, bool redundant) {
        internalize(e, false, false, redundant);
    }

    literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        flet<bool> _redundant(m_is_redundant, redundant);
        if (m_pb.is_pb(e)) 
            return internalize_pb(e, sign, root);
        UNREACHABLE();
        return sat::null_literal;
    }

    literal solver::internalize_pb(expr* e, bool sign, bool root) {
        SASSERT(m_pb.is_pb(e));
        app* t = to_app(e);
        rational k = m_pb.get_k(t);
        switch (t->get_decl_kind()) {
        case OP_AT_MOST_K:
            return convert_at_most_k(t, k, root, sign);
        case OP_AT_LEAST_K:
            return convert_at_least_k(t, k, root, sign);
        case OP_PB_LE:
            if (m_pb.has_unit_coefficients(t))
                return convert_at_most_k(t, k, root, sign);
            else
                return convert_pb_le(t, root, sign);
        case OP_PB_GE:
            if (m_pb.has_unit_coefficients(t))
                return convert_at_least_k(t, k, root, sign);
            else
                return convert_pb_ge(t, root, sign);
        case OP_PB_EQ:
            if (m_pb.has_unit_coefficients(t))
                return convert_eq_k(t, k, root, sign);
            else
                return convert_pb_eq(t, root, sign);
        default:
            UNREACHABLE();
        }
        return sat::null_literal;
    }

    void solver::check_unsigned(rational const& c) {
        if (!c.is_unsigned()) {
            throw default_exception("unsigned coefficient expected");
        }
    }

    void solver::convert_to_wlits(app* t, sat::literal_vector const& lits, svector<wliteral>& wlits) {
        for (unsigned i = 0; i < lits.size(); ++i) {
            rational c = m_pb.get_coeff(t, i);
            check_unsigned(c);
            wlits.push_back(std::make_pair(c.get_unsigned(), lits[i]));
        }
    }

    void solver::convert_pb_args(app* t, literal_vector& lits) {
        for (expr* arg : *t) {
            lits.push_back(si.internalize(arg, m_is_redundant));
            s().set_external(lits.back().var());
        }
    }

    void solver::convert_pb_args(app* t, svector<wliteral>& wlits) {
        sat::literal_vector lits;
        convert_pb_args(t, lits);    
        convert_to_wlits(t, lits, wlits);
    }

    literal solver::convert_pb_le(app* t, bool root, bool sign) {
        rational k = m_pb.get_k(t);
        k.neg();
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        for (wliteral& wl : wlits) {
            wl.second.neg();
            k += rational(wl.first);
        }
        check_unsigned(k);
        if (root && s().num_user_scopes() == 0) {
            unsigned k1 = k.get_unsigned();
            if (sign) {
                k1 = 1 - k1;
                for (wliteral& wl : wlits) {
                    wl.second.neg();
                    k1 += wl.first;
                }
            }
            add_pb_ge(sat::null_bool_var, wlits, k1);
            return sat::null_literal;
        }
        else {
            bool_var v = s().add_var(true);
            literal lit(v, sign);
            add_pb_ge(v, wlits, k.get_unsigned());
            TRACE("ba", tout << "root: " << root << " lit: " << lit << "\n";);
            return lit;
        }
    }


    literal solver::convert_pb_ge(app* t, bool root, bool sign) {
        rational k = m_pb.get_k(t);
        check_unsigned(k);
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        if (root && s().num_user_scopes() == 0) {
            unsigned k1 = k.get_unsigned();
            if (sign) {
                k1 = 1 - k1;
                for (wliteral& wl : wlits) {
                    wl.second.neg();
                    k1 += wl.first;
                }
            }
            add_pb_ge(sat::null_bool_var, wlits, k1);
            return sat::null_literal;
        }
        else {
            sat::bool_var v = s().add_var(true);
            sat::literal lit(v, sign);
            add_pb_ge(v, wlits, k.get_unsigned());
            TRACE("goal2sat", tout << "root: " << root << " lit: " << lit << "\n";);
            return lit;
        }
    }

    literal solver::convert_pb_eq(app* t, bool root, bool sign) {
        rational k = m_pb.get_k(t);
        SASSERT(k.is_unsigned());
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        bool base_assert = (root && !sign && s().num_user_scopes() == 0);
        bool_var v1 = base_assert ? sat::null_bool_var : s().add_var(true);
        bool_var v2 = base_assert ? sat::null_bool_var : s().add_var(true);
        add_pb_ge(v1, wlits, k.get_unsigned());
        k.neg();
        for (wliteral& wl : wlits) {
            wl.second.neg();
            k += rational(wl.first);
        }
        check_unsigned(k);
        add_pb_ge(v2, wlits, k.get_unsigned());
        if (base_assert) {
            return sat::null_literal;
        }
        else {
            literal l1(v1, false), l2(v2, false);
            bool_var v = s().add_var(false);
            literal l(v, false);
            s().mk_clause(~l, l1);
            s().mk_clause(~l, l2);
            s().mk_clause(~l1, ~l2, l);
            si.cache(t, l);
            if (sign) l.neg();
            return l;
        }
    }

    literal solver::convert_at_least_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        literal_vector lits;
        convert_pb_args(t, lits);
        unsigned k2 = k.get_unsigned();
        if (root && s().num_user_scopes() == 0) {
            if (sign) {
                for (literal& l : lits) l.neg();
                k2 = lits.size() + 1 - k2;
            }
            add_at_least(sat::null_bool_var, lits, k2);
            return sat::null_literal;
        }
        else {
            bool_var v = s().add_var(true);
            literal lit(v, false);
            add_at_least(v, lits, k.get_unsigned());
            si.cache(t, lit);
            if (sign) lit.neg();
            TRACE("ba", tout << "root: " << root << " lit: " << lit << "\n";);
            return lit;
        }
    }

    literal solver::convert_at_most_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        literal_vector lits;
        convert_pb_args(t, lits);
        for (literal& l : lits) {
            l.neg();
        }
        unsigned k2 = lits.size() - k.get_unsigned();
        if (root && s().num_user_scopes() == 0) {
            if (sign) {
                for (literal& l : lits) l.neg();
                k2 = lits.size() + 1 - k2;
            }
            add_at_least(sat::null_bool_var, lits, k2);
            return sat::null_literal;
        }
        else {
            bool_var v = s().add_var(true);
            literal lit(v, false);
            add_at_least(v, lits, k2);
            si.cache(t, lit);
            if (sign) lit.neg();
            return lit;
        }
    }

    literal solver::convert_eq_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        literal_vector lits;
        convert_pb_args(t, lits);
        bool_var v1 = (root && !sign) ? sat::null_bool_var : s().add_var(true);
        bool_var v2 = (root && !sign) ? sat::null_bool_var : s().add_var(true);
        add_at_least(v1, lits, k.get_unsigned());
        for (literal& l : lits) {
            l.neg();
        }
        add_at_least(v2, lits, lits.size() - k.get_unsigned());

        if (!root || sign) {        
            literal l1(v1, false), l2(v2, false);
            bool_var v = s().add_var(false);
            literal l(v, false);
            s().mk_clause(~l, l1);
            s().mk_clause(~l, l2);
            s().mk_clause(~l1, ~l2, l);
            si.cache(t, l);
            if (sign) l.neg();
            return l;
        }
        else {
            return sat::null_literal;
        }
    }

    expr_ref solver::get_card(std::function<expr_ref(sat::literal)>& lit2expr, card const& c) {
        ptr_buffer<expr> lits;
        for (sat::literal l : c) {
            lits.push_back(lit2expr(l));
        }
        expr_ref fml(m_pb.mk_at_least_k(c.size(), lits.data(), c.k()), m);

        if (c.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(c.lit()), fml);
        }
        return fml;
    }

    expr_ref solver::get_pb(std::function<expr_ref(sat::literal)>& lit2expr, pbc const& p)  {
        ptr_buffer<expr> lits;
        vector<rational> coeffs;
        for (auto const& wl : p) {
            lits.push_back(lit2expr(wl.second));
            coeffs.push_back(rational(wl.first));
        }
        rational k(p.k());
        expr_ref fml(m_pb.mk_ge(p.size(), coeffs.data(), lits.data(), k), m);

        if (p.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(p.lit()), fml);
        }
        return fml;
    }

    bool solver::to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) {
        for (auto* c : constraints()) {
            switch (c->tag()) {
            case pb::tag_t::card_t:
                fmls.push_back(get_card(l2e, c->to_card()));
                break;
            case pb::tag_t::pb_t:
                fmls.push_back(get_pb(l2e, c->to_pb()));
                break;
            }
        }
        return true;
    }
}
