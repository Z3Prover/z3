/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bounded_int2bv_solver.cpp

Abstract:

    This solver identifies bounded integers and rewrites them to bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:

--*/
#include "tactic/fd_solver/bounded_int2bv_solver.h"
#include "solver/solver_na2as.h"
#include "tactic/tactic.h"
#include "ast/rewriter/pb2bv_rewriter.h"
#include "tactic/generic_model_converter.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"
#include "tactic/arith/bound_manager.h"
#include "tactic/arith/bv2int_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

class bounded_int2bv_solver : public solver_na2as {
    ast_manager&     m;
    mutable bv_util          m_bv;
    mutable arith_util       m_arith;
    mutable expr_ref_vector  m_assertions;
    ref<solver>      m_solver;
    mutable ptr_vector<bound_manager> m_bounds;
    mutable func_decl_ref_vector  m_bv_fns;
    mutable func_decl_ref_vector  m_int_fns;
    unsigned_vector       m_bv_fns_lim;
    mutable obj_map<func_decl, func_decl*> m_int2bv;
    mutable obj_map<func_decl, func_decl*> m_bv2int;
    mutable obj_map<func_decl, rational>   m_bv2offset;
    mutable bv2int_rewriter_ctx   m_rewriter_ctx;
    mutable bv2int_rewriter_star  m_rewriter;

public:

    bounded_int2bv_solver(ast_manager& m, params_ref const& p, solver* s):
        solver_na2as(m),
        m(m),
        m_bv(m),
        m_arith(m),
        m_assertions(m),
        m_solver(s),
        m_bv_fns(m),
        m_int_fns(m),
        m_rewriter_ctx(m, p, p.get_uint("max_bv_size", UINT_MAX)),
        m_rewriter(m, m_rewriter_ctx)
    {
        solver::updt_params(p);
        m_bounds.push_back(alloc(bound_manager, m));
    }

    ~bounded_int2bv_solver() override {
        while (!m_bounds.empty()) {
            dealloc(m_bounds.back());
            m_bounds.pop_back();
        }
    }

    solver* translate(ast_manager& dst_m, params_ref const& p) override {
        flush_assertions();
        bounded_int2bv_solver* result = alloc(bounded_int2bv_solver, dst_m, p, m_solver->translate(dst_m, p));
        ast_translation tr(m, dst_m);
        for (auto& kv : m_int2bv) result->m_int2bv.insert(tr(kv.m_key), tr(kv.m_value));        
        for (auto& kv : m_bv2int) result->m_bv2int.insert(tr(kv.m_key), tr(kv.m_value));
        for (auto& kv : m_bv2offset) result->m_bv2offset.insert(tr(kv.m_key), kv.m_value);
        for (func_decl* f : m_bv_fns) result->m_bv_fns.push_back(tr(f));
        for (func_decl* f : m_int_fns) result->m_int_fns.push_back(tr(f));
        for (bound_manager* b : m_bounds) result->m_bounds.push_back(b->translate(dst_m));
        model_converter_ref mc = external_model_converter();
        if (mc) {
            ast_translation tr(m, dst_m);
            result->set_model_converter(mc->translate(tr));
        }
        return result;
    }

    void assert_expr_core(expr * t) override {
        unsigned i = m_assertions.size();
        m_assertions.push_back(t);
        while (i < m_assertions.size()) {
            t = m_assertions[i].get();
            if (m.is_and(t)) {
                m_assertions.append(to_app(t)->get_num_args(), to_app(t)->get_args());
                m_assertions[i] = m_assertions.back();
                m_assertions.pop_back();
            }
            else {
                ++i;
            }
        }
    }

    void push_core() override {
        flush_assertions();
        m_solver->push();
        m_bv_fns_lim.push_back(m_bv_fns.size());
        m_bounds.push_back(alloc(bound_manager, m));
    }

    void pop_core(unsigned n) override {
        m_assertions.reset();
        m_solver->pop(n);

        if (n > 0) {
            SASSERT(n <= m_bv_fns_lim.size());
            unsigned new_sz = m_bv_fns_lim.size() - n;
            unsigned lim = m_bv_fns_lim[new_sz];
            for (unsigned i = m_int_fns.size(); i > lim; ) {
                --i;
                m_int2bv.erase(m_int_fns[i].get());
                m_bv2int.erase(m_bv_fns[i].get());
                m_bv2offset.erase(m_bv_fns[i].get());
            }
            m_bv_fns_lim.resize(new_sz);
            m_bv_fns.resize(lim);
            m_int_fns.resize(lim);
        }

        while (n > 0) {
            dealloc(m_bounds.back());
            m_bounds.pop_back();
            --n;
        }
    }

    lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override {
        flush_assertions();
        return m_solver->check_sat_core(num_assumptions, assumptions);
    }

    void updt_params(params_ref const & p) override { solver::updt_params(p); m_solver->updt_params(p);  }
    void collect_param_descrs(param_descrs & r) override { m_solver->collect_param_descrs(r); }
    void set_produce_models(bool f) override { m_solver->set_produce_models(f); }
    void set_progress_callback(progress_callback * callback) override { m_solver->set_progress_callback(callback);  }
    void collect_statistics(statistics & st) const override { m_solver->collect_statistics(st); }
    void get_unsat_core(expr_ref_vector & r) override { m_solver->get_unsat_core(r); }
    void get_model_core(model_ref & mdl) override {
        m_solver->get_model(mdl);
        if (mdl) {
            model_converter_ref mc = local_model_converter();
            if (mc) (*mc)(mdl);
        }
    }
    void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
        m_solver->get_levels(vars, depth);
    }
    expr_ref_vector get_trail() override {
        return m_solver->get_trail();
    }

    model_converter* external_model_converter() const {
        return concat(mc0(), local_model_converter());
    }
    model_converter* local_model_converter() const {
        if (m_int2bv.empty() && m_bv_fns.empty()) return nullptr;
        generic_model_converter* mc = alloc(generic_model_converter, m, "bounded_int2bv");
        for (func_decl* f : m_bv_fns) 
            mc->hide(f);
        for (auto const& kv : m_int2bv) {
            rational offset;
            VERIFY (m_bv2offset.find(kv.m_value, offset));
            expr_ref value(m_bv.mk_bv2int(m.mk_const(kv.m_value)), m);
            if (!offset.is_zero()) {
                value = m_arith.mk_add(value, m_arith.mk_numeral(offset, true));
            }
            TRACE("int2bv", tout << mk_pp(kv.m_key, m) << " " << value << "\n";);
            mc->add(kv.m_key, value);
        }
        return mc;
    }

    model_converter_ref get_model_converter() const override { 
        model_converter_ref mc = external_model_converter();
        mc = concat(mc.get(), m_solver->get_model_converter().get());
        return mc;
    }
    proof * get_proof() override { return m_solver->get_proof(); }
    std::string reason_unknown() const override { return m_solver->reason_unknown(); }
    void set_reason_unknown(char const* msg) override { m_solver->set_reason_unknown(msg); }
    void get_labels(svector<symbol> & r) override { m_solver->get_labels(r); }
    ast_manager& get_manager() const override { return m;  }
    expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) override { flush_assertions(); return m_solver->cube(vars, backtrack_level); }
    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override { return m_solver->find_mutexes(vars, mutexes); }
    lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override {
        flush_assertions();
        expr_ref_vector bvars(m);
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr* v = vars[i];
            func_decl* f;
            rational offset;
            if (is_app(v) && is_uninterp_const(v) && m_int2bv.find(to_app(v)->get_decl(), f)) {
                bvars.push_back(m.mk_const(f));
            }
            else {
                bvars.push_back(v);
            }
        }
        lbool r = m_solver->get_consequences(asms, bvars, consequences);

        // translate bit-vector consequences back to integer values
        for (unsigned i = 0; i < consequences.size(); ++i) {
            expr* a = nullptr, *b = nullptr, *u = nullptr, *v = nullptr;
            func_decl* f;
            rational num;
            unsigned bvsize;
            rational offset;
            VERIFY(m.is_implies(consequences[i].get(), a, b));
            if (m.is_eq(b, u, v) && is_uninterp_const(u) && m_bv2int.find(to_app(u)->get_decl(), f) && m_bv.is_numeral(v, num, bvsize)) {
                SASSERT(num.is_unsigned());
                expr_ref head(m);
                VERIFY (m_bv2offset.find(to_app(u)->get_decl(), offset));
                // f + offset == num
                // f == num - offset
                head = m.mk_eq(m.mk_const(f), m_arith.mk_numeral(num + offset, true));
                consequences[i] = m.mk_implies(a, head);
            }
        }
        return r;
    }

private:

    void accumulate_sub(expr_safe_replace& sub) const {
        for (unsigned i = 0; i < m_bounds.size(); ++i) {
            accumulate_sub(sub, *m_bounds[i]);
        }
    }

    void accumulate_sub(expr_safe_replace& sub, bound_manager& bm) const {
        bound_manager::iterator it = bm.begin(), end = bm.end();
        for (; it != end; ++it) {
            expr* e = *it;
            rational lo, hi;
            bool s1 = false, s2 = false;
            SASSERT(is_uninterp_const(e));
            func_decl* f = to_app(e)->get_decl();

            if (bm.has_lower(e, lo, s1) && bm.has_upper(e, hi, s2) && lo <= hi && !s1 && !s2) {
                func_decl* fbv;
                rational offset;
                if (!m_int2bv.find(f, fbv)) {
                    rational n = hi - lo + rational::one();
                    unsigned num_bits = get_num_bits(n);
                    expr_ref b(m);
                    b = m.mk_fresh_const("b", m_bv.mk_sort(num_bits));
                    fbv = to_app(b)->get_decl();
                    offset = lo;
                    m_int2bv.insert(f, fbv);
                    m_bv2int.insert(fbv, f);
                    m_bv2offset.insert(fbv, offset);
                    m_bv_fns.push_back(fbv);
                    m_int_fns.push_back(f);
                    unsigned shift;
                    if (!offset.is_zero() && !n.is_power_of_two(shift)) {
                        m_assertions.push_back(m_bv.mk_ule(b, m_bv.mk_numeral(n-rational::one(), num_bits)));
                    }
                }
                else {
                    VERIFY(m_bv2offset.find(fbv, offset));
                }
                expr_ref t(m.mk_const(fbv), m);
                t = m_bv.mk_bv2int(t);
                if (!offset.is_zero()) {
                    t = m_arith.mk_add(t, m_arith.mk_numeral(offset, true));
                }
                TRACE("pb", tout << lo << " <= " << hi << " offset: " << offset << "\n"; tout << mk_pp(e, m) << " |-> " << t << "\n";);
                sub.insert(e, t);
            }
            else {
                TRACE("pb", 
                      tout << "unprocessed entry: " << mk_pp(e, m) << "\n";
                      if (bm.has_lower(e, lo, s1)) {
                          tout << "lower: " << lo << " " << s1 << "\n";
                      }
                      if (bm.has_upper(e, hi, s2)) {
                          tout << "upper: " << hi << " " << s2 << "\n";
                      });
            }
        }
    }


    unsigned get_num_bits(rational const& k) const {
        SASSERT(!k.is_neg());
        SASSERT(k.is_int());
        rational two(2);
        rational bound(1);
        unsigned num_bits = 1;
        while (bound <= k) {
            ++num_bits;
            bound *= two;
        }
        return num_bits;
    }

    void flush_assertions() const {
        if (m_assertions.empty()) return;
        bound_manager& bm = *m_bounds.back();
        for (expr* a : m_assertions) {
            bm(a);
        }
        TRACE("int2bv", bm.display(tout););
        expr_safe_replace sub(m);
        accumulate_sub(sub);
        proof_ref proof(m);
        expr_ref fml1(m), fml2(m);
        if (sub.empty()) {
            m_solver->assert_expr(m_assertions);
        }
        else {
            for (expr* a : m_assertions) {
                sub(a, fml1);
                m_rewriter(fml1, fml2, proof);
                if (m.canceled()) {
                    m_rewriter.reset();
                    return;
                }
                m_solver->assert_expr(fml2);
                TRACE("int2bv", tout << fml2 << "\n";);
            }
        }
        m_assertions.reset();
        m_rewriter.reset();
    }

    unsigned get_num_assertions() const override {
        flush_assertions();
        return m_solver->get_num_assertions();
    }

    expr * get_assertion(unsigned idx) const override {
        flush_assertions();
        return m_solver->get_assertion(idx);
    }

};

solver * mk_bounded_int2bv_solver(ast_manager & m, params_ref const & p, solver* s) {
    return alloc(bounded_int2bv_solver, m, p, s);
}
