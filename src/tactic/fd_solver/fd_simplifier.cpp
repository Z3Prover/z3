/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    fd_simplifier.cpp

Abstract:

    Finite-domain preprocessing simplifier.

--*/

#include "tactic/fd_solver/fd_simplifier.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/enum2bv_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/simplifiers/bound_manager.h"
#include "ast/simplifiers/card2bv.h"
#include "ast/simplifiers/then_simplifier.h"
#include "tactic/arith/bv2int_rewriter.h"

namespace {

class enum2bv_simplifier : public dependent_expr_simplifier {
    enum2bv_rewriter        m_rewriter;
    obj_hashtable<func_decl> m_hidden;
    obj_hashtable<func_decl> m_defined;
    func_decl_ref_vector     m_hidden_trail;
    func_decl_ref_vector     m_defined_trail;
    unsigned_vector          m_hidden_limits;
    unsigned_vector          m_defined_limits;
    unsigned                 m_num_rewrites = 0;

    void update_model_trail() {
        for (auto const& kv : m_rewriter.enum2bv()) {
            func_decl* f = kv.m_value;
            if (!m_hidden.contains(f)) {
                m_hidden.insert(f);
                m_hidden_trail.push_back(f);
                m_fmls.model_trail().hide(f);
            }
        }
        for (auto const& kv : m_rewriter.enum2def()) {
            func_decl* f = kv.m_key;
            if (!m_defined.contains(f)) {
                m_defined.insert(f);
                m_defined_trail.push_back(f);
                m_fmls.model_trail().push(f, kv.m_value, nullptr, {});
            }
        }
    }

public:
    enum2bv_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s) :
        dependent_expr_simplifier(m, s),
        m_rewriter(m, p),
        m_hidden_trail(m),
        m_defined_trail(m) {}

    char const* name() const override { return "enum2bv"; }

    void reduce() override {
        expr_ref result(m);
        proof_ref proof(m);
        for (unsigned idx : indices()) {
            auto [f, p, d] = m_fmls[idx]();
            m_rewriter(f, result, proof);
            if (result != f) {
                m_fmls.update(idx, dependent_expr(m, result, mp(p, proof), d));
                ++m_num_rewrites;
            }
        }

        expr_ref_vector bounds(m);
        m_rewriter.flush_side_constraints(bounds);
        for (expr* bound : bounds)
            m_fmls.add(dependent_expr(m, bound, nullptr, nullptr));
        update_model_trail();
    }

    void push() override {
        m_rewriter.push();
        m_hidden_limits.push_back(m_hidden_trail.size());
        m_defined_limits.push_back(m_defined_trail.size());
    }

    void pop(unsigned n) override {
        unsigned hidden_limit = m_hidden_limits[m_hidden_limits.size() - n];
        unsigned defined_limit = m_defined_limits[m_defined_limits.size() - n];
        for (unsigned i = m_hidden_trail.size(); i-- > hidden_limit;)
            m_hidden.remove(m_hidden_trail.get(i));
        for (unsigned i = m_defined_trail.size(); i-- > defined_limit;)
            m_defined.remove(m_defined_trail.get(i));
        m_hidden_trail.shrink(hidden_limit);
        m_defined_trail.shrink(defined_limit);
        m_hidden_limits.shrink(m_hidden_limits.size() - n);
        m_defined_limits.shrink(m_defined_limits.size() - n);
        m_rewriter.pop(n);
    }

    void translate(dependent_expr_simplifier const& src, ast_translation& tr) override {
        auto const& source = dynamic_cast<enum2bv_simplifier const&>(src);
        SASSERT(source.m_hidden_limits.empty());
        SASSERT(source.m_defined_limits.empty());
        SASSERT(m_hidden_trail.empty());
        SASSERT(m_defined_trail.empty());
        m_rewriter.translate(source.m_rewriter, tr);
        for (func_decl* f : source.m_hidden_trail) {
            func_decl* translated = tr(f);
            m_hidden.insert(translated);
            m_hidden_trail.push_back(translated);
        }
        for (func_decl* f : source.m_defined_trail) {
            func_decl* translated = tr(f);
            m_defined.insert(translated);
            m_defined_trail.push_back(translated);
        }
    }

    void updt_params(params_ref const& p) override { m_rewriter.updt_params(p); }
    void collect_statistics(statistics& st) const override {
        st.update("enum2bv-rewrites", m_num_rewrites);
    }
    void reset_statistics() override { m_num_rewrites = 0; }
};

class bounded_int2bv_simplifier : public dependent_expr_simplifier {
    bv_util                         m_bv;
    arith_util                      m_arith;
    ptr_vector<bound_manager>       m_bounds;
    func_decl_ref_vector            m_bv_fns;
    func_decl_ref_vector            m_int_fns;
    unsigned_vector                 m_fn_limits;
    obj_map<func_decl, func_decl*>  m_int2bv;
    obj_map<func_decl, func_decl*>  m_bv2int;
    obj_map<func_decl, rational>    m_bv2offset;
    bv2int_rewriter_ctx             m_rewriter_ctx;
    bv2int_rewriter_star            m_rewriter;
    expr_ref_vector                 m_side_conditions;
    unsigned                        m_num_rewrites = 0;

    unsigned get_num_bits(rational const& k) const {
        SASSERT(!k.is_neg());
        SASSERT(k.is_int());
        rational bound(1);
        unsigned num_bits = 1;
        while (bound <= k) {
            ++num_bits;
            bound *= rational(2);
        }
        return num_bits;
    }

    void collect_bounds(bound_manager& bounds, expr* f, expr_dependency* d, proof* p) {
        if (m.is_and(f)) {
            for (expr* arg : *to_app(f))
                collect_bounds(bounds, arg, d, p);
        }
        else {
            bounds(f, d, p);
        }
    }

    void add_model_definition(func_decl* f, func_decl* fbv, rational const& offset) {
        m_fmls.model_trail().hide(fbv);
        expr_ref value(m_bv.mk_ubv2int(m.mk_const(fbv)), m);
        if (!offset.is_zero())
            value = m_arith.mk_add(value, m_arith.mk_numeral(offset, true));
        m_fmls.model_trail().push(f, value, nullptr, {});
    }

    void accumulate_sub(expr_safe_replace& sub, bound_manager& bounds) {
        for (expr* e : bounds) {
            rational lo, hi;
            bool strict_lo = false, strict_hi = false;
            SASSERT(is_uninterp_const(e));
            func_decl* f = to_app(e)->get_decl();
            if (!bounds.has_lower(e, lo, strict_lo) ||
                !bounds.has_upper(e, hi, strict_hi) ||
                lo > hi || strict_lo || strict_hi || !m_arith.is_int(e))
                continue;

            func_decl* fbv = nullptr;
            rational offset;
            if (!m_int2bv.find(f, fbv)) {
                rational domain_size = hi - lo + rational::one();
                unsigned num_bits = get_num_bits(domain_size);
                expr_ref b(m.mk_fresh_const("b", m_bv.mk_sort(num_bits)), m);
                fbv = to_app(b)->get_decl();
                offset = lo;
                m_int2bv.insert(f, fbv);
                m_bv2int.insert(fbv, f);
                m_bv2offset.insert(fbv, offset);
                m_bv_fns.push_back(fbv);
                m_int_fns.push_back(f);
                add_model_definition(f, fbv, offset);
                unsigned shift = 0;
                if (!offset.is_zero() && !domain_size.is_power_of_two(shift)) {
                    m_side_conditions.push_back(
                        m_bv.mk_ule(b, m_bv.mk_numeral(domain_size - rational::one(), num_bits)));
                }
            }
            else {
                VERIFY(m_bv2offset.find(fbv, offset));
            }

            expr_ref replacement(m_bv.mk_ubv2int(m.mk_const(fbv)), m);
            if (!offset.is_zero())
                replacement = m_arith.mk_add(replacement, m_arith.mk_numeral(offset, true));
            sub.insert(e, replacement);
        }
    }

    void accumulate_sub(expr_safe_replace& sub) {
        for (bound_manager* bounds : m_bounds)
            accumulate_sub(sub, *bounds);
    }

public:
    bounded_int2bv_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s) :
        dependent_expr_simplifier(m, s),
        m_bv(m),
        m_arith(m),
        m_bv_fns(m),
        m_int_fns(m),
        m_rewriter_ctx(m, p, p.get_uint("max_bv_size", UINT_MAX)),
        m_rewriter(m, m_rewriter_ctx),
        m_side_conditions(m) {
        m_bounds.push_back(alloc(bound_manager, m));
    }

    ~bounded_int2bv_simplifier() override {
        for (bound_manager* bounds : m_bounds)
            dealloc(bounds);
    }

    char const* name() const override { return "bounded-int2bv"; }

    void reduce() override {
        bound_manager& bounds = *m_bounds.back();
        for (unsigned idx : indices()) {
            auto [f, p, d] = m_fmls[idx]();
            collect_bounds(bounds, f, d, p);
        }

        expr_safe_replace sub(m);
        accumulate_sub(sub);
        if (!sub.empty()) {
            expr_ref replaced(m), result(m);
            proof_ref proof(m);
            for (unsigned idx : indices()) {
                auto [f, p, d] = m_fmls[idx]();
                sub(f, replaced);
                m_rewriter(replaced, result, proof);
                if (result != f) {
                    m_fmls.update(idx, dependent_expr(m, result, nullptr, d));
                    ++m_num_rewrites;
                }
            }
        }

        for (expr* bound : m_side_conditions)
            m_fmls.add(dependent_expr(m, bound, nullptr, nullptr));
        m_side_conditions.reset();
        m_rewriter.reset();
    }

    void push() override {
        m_fn_limits.push_back(m_bv_fns.size());
        m_bounds.push_back(alloc(bound_manager, m));
    }

    void pop(unsigned n) override {
        unsigned limit = m_fn_limits[m_fn_limits.size() - n];
        for (unsigned i = m_int_fns.size(); i-- > limit;) {
            m_int2bv.erase(m_int_fns.get(i));
            m_bv2int.erase(m_bv_fns.get(i));
            m_bv2offset.erase(m_bv_fns.get(i));
        }
        m_bv_fns.shrink(limit);
        m_int_fns.shrink(limit);
        m_fn_limits.shrink(m_fn_limits.size() - n);
        while (n-- > 0) {
            dealloc(m_bounds.back());
            m_bounds.pop_back();
        }
    }

    void translate(dependent_expr_simplifier const& src, ast_translation& tr) override {
        auto const& source = dynamic_cast<bounded_int2bv_simplifier const&>(src);
        SASSERT(source.m_bounds.size() == 1);
        SASSERT(source.m_fn_limits.empty());
        SASSERT(m_bounds.size() == 1);
        SASSERT(m_int_fns.empty());
        m_bounds.back()->translate(*source.m_bounds.back(), tr);
        for (unsigned i = 0; i < source.m_int_fns.size(); ++i) {
            func_decl* f = tr(source.m_int_fns.get(i));
            func_decl* fbv = tr(source.m_bv_fns.get(i));
            rational offset;
            VERIFY(source.m_bv2offset.find(source.m_bv_fns.get(i), offset));
            m_int2bv.insert(f, fbv);
            m_bv2int.insert(fbv, f);
            m_bv2offset.insert(fbv, offset);
            m_int_fns.push_back(f);
            m_bv_fns.push_back(fbv);
        }
        for (expr* condition : source.m_side_conditions)
            m_side_conditions.push_back(tr(condition));
    }

    void collect_statistics(statistics& st) const override {
        st.update("bounded-int2bv-rewrites", m_num_rewrites);
    }
    void reset_statistics() override { m_num_rewrites = 0; }
};

}

dependent_expr_simplifier* mk_fd_simplifier(
    ast_manager& m,
    params_ref const& p,
    dependent_expr_state& s) {
    auto* result = alloc(then_simplifier, m, p, s);
    result->add_simplifier(alloc(bounded_int2bv_simplifier, m, p, s));
    result->add_simplifier(alloc(card2bv, m, p, s));
    result->add_simplifier(alloc(enum2bv_simplifier, m, p, s));
    return result;
}
