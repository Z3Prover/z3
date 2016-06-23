/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_util.cpp

Abstract:

    Utility functions for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:


Notes: 
    

--*/

#include <sstream>
#include "arith_simplifier_plugin.h"
#include "array_decl_plugin.h"
#include "ast_pp.h"
#include "basic_simplifier_plugin.h"
#include "bv_simplifier_plugin.h"
#include "bool_rewriter.h"
#include "dl_util.h"
#include "for_each_expr.h"
#include "smt_params.h"
#include "model.h"
#include "ref_vector.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "util.h"
#include "pdr_manager.h"
#include "pdr_util.h"
#include "arith_decl_plugin.h"
#include "expr_replacer.h"
#include "model_smt2_pp.h"
#include "poly_rewriter.h"
#include "poly_rewriter_def.h"
#include "arith_rewriter.h"
#include "scoped_proof.h"



namespace pdr {

    unsigned ceil_log2(unsigned u) {
        if (u == 0) { return 0; }
        unsigned pow2 = next_power_of_two(u);
        return get_num_1bits(pow2-1);
    }

    std::string pp_cube(const ptr_vector<expr>& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(const expr_ref_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(const app_ref_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }
    
    std::string pp_cube(const app_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(unsigned sz, app * const * lits, ast_manager& m) {
        return pp_cube(sz, (expr * const *)(lits), m);
    }

    std::string pp_cube(unsigned sz, expr * const * lits, ast_manager& m) {
        std::stringstream res;
        res << "(";
        expr * const * end = lits+sz;
        for (expr * const * it = lits; it!=end; it++) {
            res << mk_pp(*it, m);
            if (it+1!=end) {
                res << ", ";
            }
        }
        res << ")";
        return res.str();
    }

    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        expr_ref_vector conjs(m);
        flatten_and(fml, conjs);
        obj_map<expr, unsigned> diseqs;
        expr* n, *lhs, *rhs;
        for (unsigned i = 0; i < conjs.size(); ++i) {
            if (m.is_not(conjs[i].get(), n) &&
                m.is_eq(n, lhs, rhs)) {
                if (!m.is_value(rhs)) {
                    std::swap(lhs, rhs);
                }
                if (!m.is_value(rhs)) {
                    continue;
                }
                diseqs.insert_if_not_there2(lhs, 0)->get_data().m_value++;
            }
        }
        expr_substitution sub(m);

        unsigned orig_size = conjs.size();
        unsigned num_deleted = 0;
        expr_ref val(m), tmp(m);
        proof_ref pr(m);
        pr = m.mk_asserted(m.mk_true());
        obj_map<expr, unsigned>::iterator it  = diseqs.begin();
        obj_map<expr, unsigned>::iterator end = diseqs.end();
        for (; it != end; ++it) {
            if (it->m_value >= threshold) {
                model.eval(it->m_key, val);
                sub.insert(it->m_key, val, pr);
                conjs.push_back(m.mk_eq(it->m_key, val));
                num_deleted += it->m_value;
            }
        }
        if (orig_size < conjs.size()) {
            scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
            rep->set_substitution(&sub);
            for (unsigned i = 0; i < orig_size; ++i) {
                tmp = conjs[i].get();
                (*rep)(tmp);
                if (m.is_true(tmp)) {
                    conjs[i] = conjs.back();
                    SASSERT(orig_size <= conjs.size());
                    conjs.pop_back();
                    SASSERT(orig_size <= 1 + conjs.size());
                    if (i + 1 == orig_size) {
                        // no-op.
                    }
                    else if (orig_size <= conjs.size()) {
                        // no-op
                    }
                    else {
                        SASSERT(orig_size == 1 + conjs.size());
                        --orig_size;
                        --i;
                    }
                }
                else {
                    conjs[i] = tmp;
                }
            }            
            IF_VERBOSE(2, verbose_stream() << "Deleted " << num_deleted << " disequalities " << conjs.size() << " conjuncts\n";);
        }
        fml = m.mk_and(conjs.size(), conjs.c_ptr());        
    }

    class test_diff_logic {
        ast_manager& m;
        arith_util a;
        bv_util    bv;
        bool m_is_dl;
        bool m_test_for_utvpi;

        bool is_numeric(expr* e) const {
            if (a.is_numeral(e)) {
                return true;
            }
            expr* cond, *th, *el;
            if (m.is_ite(e, cond, th, el)) {
                return is_numeric(th) && is_numeric(el);
            }
            return false;
        }
        
        bool is_arith_expr(expr *e) const {
            return is_app(e) && a.get_family_id() == to_app(e)->get_family_id();
        }

        bool is_offset(expr* e) const {
            if (a.is_numeral(e)) {
                return true;
            }
            expr* cond, *th, *el, *e1, *e2;
            if (m.is_ite(e, cond, th, el)) {
                return is_offset(th) && is_offset(el);
            }
            // recognize offsets.
            if (a.is_add(e, e1, e2)) {
                if (is_numeric(e1)) {
                    return is_offset(e2);
                }
                if (is_numeric(e2)) {
                    return is_offset(e1);
                }
                return false;
            }
            if (m_test_for_utvpi) {
                if (a.is_mul(e, e1, e2)) {
                    if (is_minus_one(e1)) {
                        return is_offset(e2);
                    }
                    if (is_minus_one(e2)) {
                        return is_offset(e1);
                    }
                }
            }
            return !is_arith_expr(e);
        }

        bool is_minus_one(expr const * e) const { 
            rational r; return a.is_numeral(e, r) && r.is_minus_one(); 
        }

        bool test_ineq(expr* e) const {
            SASSERT(a.is_le(e) || a.is_ge(e) || m.is_eq(e));
            SASSERT(to_app(e)->get_num_args() == 2);
            expr * lhs = to_app(e)->get_arg(0);
            expr * rhs = to_app(e)->get_arg(1);
            if (is_offset(lhs) && is_offset(rhs)) 
                return true;    
            if (!is_numeric(rhs)) 
                std::swap(lhs, rhs);
            if (!is_numeric(rhs)) 
                return false;    
            // lhs can be 'x' or '(+ x (* -1 y))'
            if (is_offset(lhs))
                return true;
            expr* arg1, *arg2;
            if (!a.is_add(lhs, arg1, arg2)) 
                return false;    
            // x
            if (m_test_for_utvpi) {
                return is_offset(arg1) && is_offset(arg2);
            }
            if (is_arith_expr(arg1)) 
                std::swap(arg1, arg2);
            if (is_arith_expr(arg1))
                return false;
            // arg2: (* -1 y)
            expr* m1, *m2;
            if (!a.is_mul(arg2, m1, m2))
                return false;
            return is_minus_one(m1) && is_offset(m2);
        }

        bool test_eq(expr* e) const {
            expr* lhs = 0, *rhs = 0;
            VERIFY(m.is_eq(e, lhs, rhs));
            if (!a.is_int_real(lhs)) {
                return true;
            }
            if (a.is_numeral(lhs) || a.is_numeral(rhs)) {
                return test_ineq(e);
            }
            return 
                test_term(lhs) && 
                test_term(rhs) &&
                !a.is_mul(lhs) &&
                !a.is_mul(rhs);
        }

        bool test_term(expr* e) const {
            if (m.is_bool(e)) {
                return true;
            }
            if (a.is_numeral(e)) {
                return true;
            }
            if (is_offset(e)) {
                return true;
            }
            expr* lhs, *rhs;
            if (a.is_add(e, lhs, rhs)) {
                if (!a.is_numeral(lhs)) {
                    std::swap(lhs, rhs);
                }
                return a.is_numeral(lhs) && is_offset(rhs);
            }
            if (a.is_mul(e, lhs, rhs)) {
                return is_minus_one(lhs) || is_minus_one(rhs);
            }
            return false;
        }

        bool is_non_arith_or_basic(expr* e) {
            if (!is_app(e)) {
                return false;
            }
            family_id fid = to_app(e)->get_family_id();

            if (fid == null_family_id && 
                !m.is_bool(e) && 
                to_app(e)->get_num_args() > 0) {
                return true;
            }
            return 
                fid != m.get_basic_family_id() &&
                fid != null_family_id &&
                fid != a.get_family_id() &&
                fid != bv.get_family_id();
        }

    public:
        test_diff_logic(ast_manager& m): m(m), a(m), bv(m), m_is_dl(true), m_test_for_utvpi(false) {}
       
        void test_for_utvpi() { m_test_for_utvpi = true; }

        void operator()(expr* e) {
            if (!m_is_dl) {
                return;
            }
            if (a.is_le(e) || a.is_ge(e)) {
                m_is_dl = test_ineq(e);
            }
            else if (m.is_eq(e)) {
                m_is_dl = test_eq(e);
            }
            else if (is_non_arith_or_basic(e)) {
                m_is_dl = false;
            }
            else if (is_app(e)) {
                app* a = to_app(e);                
                for (unsigned i = 0; m_is_dl && i < a->get_num_args(); ++i) {
                    m_is_dl = test_term(a->get_arg(i));
                }
            }

            if (!m_is_dl) {
                char const* msg = "non-diff: ";
                if (m_test_for_utvpi) {
                    msg = "non-utvpi: ";
                }
                IF_VERBOSE(1, verbose_stream() << msg << mk_pp(e, m) << "\n";);
            }
        }

        bool is_dl() const { return m_is_dl; }
    };

    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        test_diff_logic test(m);
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

    bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        test_diff_logic test(m);
        test.test_for_utvpi();
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

    class arith_normalizer : public poly_rewriter<arith_rewriter_core> {
        ast_manager& m;
        arith_util   m_util;
        enum op_kind { LE, GE, EQ };
    public:
        arith_normalizer(ast_manager& m, params_ref const& p = params_ref()): poly_rewriter<arith_rewriter_core>(m, p), m(m), m_util(m) {}
        
        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            br_status st = BR_FAILED;
            if (m.is_eq(f)) {
                SASSERT(num_args == 2); return mk_eq_core(args[0], args[1], result);
            }

            if (f->get_family_id() != get_fid()) {
                return st;
            }
            switch (f->get_decl_kind()) {
            case OP_NUM: st = BR_FAILED; break;
            case OP_IRRATIONAL_ALGEBRAIC_NUM: st = BR_FAILED; break;
            case OP_LE:  SASSERT(num_args == 2); st = mk_le_core(args[0], args[1], result); break;
            case OP_GE:  SASSERT(num_args == 2); st = mk_ge_core(args[0], args[1], result); break;
            case OP_LT:  SASSERT(num_args == 2); st = mk_lt_core(args[0], args[1], result); break;
            case OP_GT:  SASSERT(num_args == 2); st = mk_gt_core(args[0], args[1], result); break;
            default: st = BR_FAILED; break;
            }
            return st;
        }      

    private:
        
        br_status mk_eq_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, EQ, result);
        }
        br_status mk_le_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, LE, result);
        }
        br_status mk_ge_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, GE, result);
        }
        br_status mk_lt_core(expr* arg1, expr* arg2, expr_ref& result) {
            result = m.mk_not(m_util.mk_ge(arg1, arg2));
            return BR_REWRITE2;
        }
        br_status mk_gt_core(expr* arg1, expr* arg2, expr_ref& result) {
            result = m.mk_not(m_util.mk_le(arg1, arg2));
            return BR_REWRITE2;
        }

        br_status mk_le_ge_eq_core(expr* arg1, expr* arg2, op_kind kind, expr_ref& result) {
            if (m_util.is_real(arg1)) {
                numeral g(0);
                get_coeffs(arg1, g);
                get_coeffs(arg2, g);
                if (!g.is_one() && !g.is_zero()) {
                    SASSERT(g.is_pos());
                    expr_ref new_arg1 = rdiv_polynomial(arg1, g);
                    expr_ref new_arg2 = rdiv_polynomial(arg2, g);
                    switch(kind) {
                    case LE: result = m_util.mk_le(new_arg1, new_arg2); return BR_DONE;
                    case GE: result = m_util.mk_ge(new_arg1, new_arg2); return BR_DONE;
                    case EQ: result = m_util.mk_eq(new_arg1, new_arg2); return BR_DONE;
                    }
                }
            }
            return BR_FAILED;
        }

        void update_coeff(numeral const& r, numeral& g) {
            if (g.is_zero() || abs(r) < g) {
                g = abs(r);
            }
        }        

        void get_coeffs(expr* e, numeral& g) {
            rational r;
            unsigned sz;
            expr* const* args = get_monomials(e, sz);
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = args[i];
                if (!m_util.is_numeral(arg, r)) {
                    get_power_product(arg, r);
                }
                update_coeff(r, g);
            }
        }

        expr_ref rdiv_polynomial(expr* e, numeral const& g) {
            rational r;
            SASSERT(g.is_pos());
            SASSERT(!g.is_one());
            expr_ref_vector monomes(m);
            unsigned sz;           
            expr* const* args = get_monomials(e, sz);
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = args[i];
                if (m_util.is_numeral(arg, r)) {
                    monomes.push_back(m_util.mk_numeral(r/g, false));
                }
                else {
                    expr* p = get_power_product(arg, r);
                    r /= g;
                    if (r.is_one()) {
                        monomes.push_back(p);
                    }
                    else {
                        monomes.push_back(m_util.mk_mul(m_util.mk_numeral(r, false), p));
                    }
                }
            }
            expr_ref result(m);
            mk_add(monomes.size(), monomes.c_ptr(), result);
            return result;
        }
                
    };
    

    struct arith_normalizer_cfg: public default_rewriter_cfg {
        arith_normalizer m_r;
        bool rewrite_patterns() const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            return m_r.mk_app_core(f, num, args, result);
        }
        arith_normalizer_cfg(ast_manager & m, params_ref const & p):m_r(m,p) {}        
    };

    class arith_normalizer_star : public rewriter_tpl<arith_normalizer_cfg> {
        arith_normalizer_cfg m_cfg;
    public:
        arith_normalizer_star(ast_manager & m, params_ref const & p):
            rewriter_tpl<arith_normalizer_cfg>(m, false, m_cfg),
            m_cfg(m, p) {}
    };


    void normalize_arithmetic(expr_ref& t) {
        ast_manager& m = t.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        arith_normalizer_star rw(m, p);
        expr_ref tmp(m);
        rw(t, tmp);
        t = tmp;                
    }

}

template class rewriter_tpl<pdr::arith_normalizer_cfg>;


