/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    theory_intblast
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-27

--*/

#include "smt/smt_context.h"
#include "smt/theory_intblast.h"

namespace smt {

    void theory_intblast::translator_trail::push(push_back_vector<expr_ref_vector> const& c) {
        ctx.push_trail(c);
    }
    void theory_intblast::translator_trail::push(push_back_vector<ptr_vector<app>> const& c) {
        ctx.push_trail(c);
    }
    
    void theory_intblast::translator_trail::push_idx(set_vector_idx_trail<expr_ref_vector> const& c) {
        ctx.push_trail(c);
    }

    theory_intblast::theory_intblast(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("bv")),
        m_trail(ctx),
        m_translator(m, m_trail),
        bv(m),
        a(m)
    {}
    
    theory_intblast::~theory_intblast() {}
    
    void theory_intblast::init() {
        
    }    
    
    final_check_status theory_intblast::final_check_eh() {
        for (auto e : m_translator.bv2int()) {
            auto* n = ctx.get_enode(e);
            auto* r1 = n->get_arg(0)->get_root();
            for (auto sib : *n) {
                if (sib == n)
                    continue;
                if (!bv.is_bv2int(sib->get_expr()))
                    continue;
                if (sib->get_arg(0)->get_root() == r1)
                    continue;
                if (bv.get_bv_size(r1->get_expr()) != bv.get_bv_size(sib->get_arg(0)->get_expr()))
                    continue;
                auto a = mk_eq(n->get_expr(), sib->get_expr(), false);
                auto b = mk_eq(sib->get_arg(0)->get_expr(), n->get_arg(0)->get_expr(), false);
                ctx.mark_as_relevant(a);
                ctx.mark_as_relevant(b);
                ctx.mk_clause(~a, b, nullptr);
                return final_check_status::FC_CONTINUE;
            }
        }
        // ensure that int2bv respects values
        // bv2int(int2bv(x)) = x mod N
        for (auto e : m_translator.int2bv()) {
            auto n = ctx.get_enode(e);
            auto x = n->get_arg(0)->get_expr();
            auto bv2int = bv.mk_bv2int(e);
            ctx.internalize(bv2int, false);
            auto N = rational::power_of_two(bv.get_bv_size(e));
            auto xModN = a.mk_mod(x, a.mk_int(N));
            ctx.internalize(xModN, false);
            auto nBv2int = ctx.get_enode(bv2int);
            auto nxModN = ctx.get_enode(xModN);
            if (nBv2int->get_root() != nxModN->get_root()) {
                auto a = mk_eq(nBv2int->get_expr(), nxModN->get_expr(), false);
                ctx.mark_as_relevant(a);
                ctx.mk_clause(1, &a, nullptr);
                return final_check_status::FC_CONTINUE;
            }
        }
        return final_check_status::FC_DONE;
    }

    bool theory_intblast::add_bound_axioms() {
        auto const& vars = m_translator.vars();
        if (m_vars_qhead == vars.size())
            return false;
        ctx.push_trail(value_trail(m_vars_qhead));
        for (; m_vars_qhead < vars.size(); ++m_vars_qhead) {
            auto v = vars[m_vars_qhead];
            auto w = m_translator.translated(v);
            auto sz = rational::power_of_two(bv.get_bv_size(v->get_sort()));
            auto lo = mk_literal(a.mk_ge(w, a.mk_int(0)));
            auto hi = mk_literal(a.mk_le(w, a.mk_int(sz - 1)));
            ctx.mark_as_relevant(lo);
            ctx.mark_as_relevant(hi);
            ctx.mk_clause(1, &lo, nullptr);
            ctx.mk_clause(1, &hi, nullptr);
        }
        return true;
    }

    bool theory_intblast::add_predicate_axioms() {
        auto const& preds = m_translator.preds();
        if (m_preds_qhead == preds.size())
            return false;
        ctx.push_trail(value_trail(m_preds_qhead));
        for (; m_preds_qhead < preds.size(); ++m_preds_qhead) {
            expr* e = preds[m_preds_qhead];
            expr_ref r(m_translator.translated(e), m);
            ctx.get_rewriter()(r);
            auto a = mk_literal(e);
            auto b = mk_literal(r);
            ctx.mark_as_relevant(b);
//            verbose_stream() << "add-predicate-axiom: " << mk_pp(e, m) << " == " << r << "\n";
            ctx.mk_clause(~a, b, nullptr);
            ctx.mk_clause(a, ~b, nullptr);
        }
        return true;
    }

    bool theory_intblast::can_propagate() {
        return m_preds_qhead < m_translator.preds().size() || m_vars_qhead < m_translator.vars().size();
    }

    void theory_intblast::propagate() {
        add_bound_axioms();
        add_predicate_axioms();
    }
    
    bool theory_intblast::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }
    
    bool theory_intblast::internalize_term(app* term) {
        m_translator.internalize_bv(term);
        return true;
    }
    
    void theory_intblast::internalize_eq_eh(app * atom, bool_var v) {
        m_translator.translate_eq(atom);
    }


}
