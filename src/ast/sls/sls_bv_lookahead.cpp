/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_lookahead.h

Abstract:

    Lookahead solver for BV, modeled after sls_engine/sls_tracker/sls_evaluator.

Author:

    Nikolaj Bjorner (nbjorner) 2024-12-26

--*/

#include "ast/sls/sls_bv_lookahead.h"
#include "ast/sls/sls_bv_eval.h"
#include "ast/sls/sls_bv_terms.h"

namespace sls {

    bv_lookahead::bv_lookahead(bv_eval& ev) : 
        bv(ev.bv), 
        m_ev(ev), 
        ctx(ev.ctx), 
        m(ev.m) {}

    bool bv_lookahead::try_repair_down(expr* e) {
        return false;
        auto is_true = m_ev.bval0(e);
        if (!is_true)
            return false;
        auto const& uninterp = m_ev.terms.uninterp_occurs(e);
        if (uninterp.empty())
            return false;
        //        for (auto e : uninterp)
        //            verbose_stream() << mk_bounded_pp(e, m) << " ";
        //        verbose_stream() << "\n";

        expr* t = uninterp[m_ev.m_rand() % uninterp.size()];

        auto& v = wval(t);
        if (v.set_random(m_ev.m_rand)) {
            //verbose_stream() << "set random " << mk_bounded_pp(t, m) << "\n";
            ctx.new_value_eh(t);
            return true;
        }
        return false;


        for (auto e : uninterp) {
            auto& v = wval(e);
            v.get_variant(m_ev.m_tmp, m_ev.m_rand);
            auto d = lookahead(e, m_ev.m_tmp);
            //verbose_stream() << mk_bounded_pp(e, m) << " " << d << "\n";
        }
        return false;
    }

    double bv_lookahead::lookahead(expr* e, bvect const& new_value) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());

        bool has_tabu = false;
        double break_count = 0, make_count = 0;

        wval(e).eval = new_value;
        if (!insert_update(e)) {
            restore_lookahead();
            return -1000000;
        }
        insert_update_stack(e);
        unsigned max_depth = get_depth(e);
        for (unsigned depth = max_depth; depth <= max_depth; ++depth) {
            for (unsigned i = 0; !has_tabu && i < m_update_stack[depth].size(); ++i) {
                e = m_update_stack[depth][i];
                if (bv.is_bv(e)) {
                    auto& v = m_ev.eval(to_app(e));
                    if (insert_update(e)) {
                        for (auto p : ctx.parents(e)) {
                            insert_update_stack(p);
                            max_depth = std::max(max_depth, get_depth(p));
                        }
                    }
                    else
                        has_tabu = true;
                }
                else if (m.is_bool(e) && m_ev.can_eval1(to_app(e))) {
                    bool is_true = ctx.is_true(e);
                    bool is_true_new = m_ev.bval1(to_app(e));
                    bool is_true_old = m_ev.bval1_tmp(to_app(e));
                    // verbose_stream() << "parent " << mk_bounded_pp(e, m) << " " << is_true << " " << is_true_new << " " << is_true_old << "\n";
                    if (is_true == is_true_new && is_true_new != is_true_old)
                        ++make_count;
                    if (is_true == is_true_old && is_true_new != is_true_old)
                        ++break_count;
                }
            }
            m_update_stack[depth].reset();
        }
        restore_lookahead();
        if (has_tabu)
            return -10000;
        return make_count - break_count;
    }

    bool bv_lookahead::insert_update(expr* e) {
        m_restore.push_back(e);
        m_on_restore.mark(e);
        auto& v = wval(e);
        v.save_value();
        return v.commit_eval();
    }

    void bv_lookahead::insert_update_stack(expr* e) {
        unsigned depth = get_depth(e);
        m_update_stack.reserve(depth + 1);
        if (!m_update_stack[depth].contains(e))
            m_update_stack[depth].push_back(e);
    }

    void bv_lookahead::restore_lookahead() {
        for (auto e : m_restore)
            wval(e).restore_value();
        m_restore.reset();
        m_on_restore.reset();
    }

    sls::bv_valuation& bv_lookahead::wval(expr* e) const {
        return m_ev.wval(e);
    }

    bool bv_lookahead::on_restore(expr* e) const {
        return m_on_restore.is_marked(e);
    }
}