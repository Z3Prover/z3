/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    bv_bounds_simplifier.h

Abstract:

    Context dependent simplification for bit-vectors

Author:

    Nikolaj and Nuno 

--*/

#pragma once

#include "math/interval/mod_interval.h"

namespace bv {


    struct undo_bound {
        expr* e = nullptr;
        interval b;
        bool fresh = false;
        undo_bound(expr* e, const interval& b, bool fresh) : e(e), b(b), fresh(fresh) {}
    };

    struct bv_bounds_base {
        typedef obj_map<expr, interval> map;
        typedef obj_map<expr, bool> expr_set;
        typedef obj_map<expr, unsigned> expr_cnt;

        ast_manager&       m;
        bv_util            m_bv;
        vector<undo_bound> m_scopes;
        svector<expr_set*> m_expr_vars;
        svector<expr_cnt*> m_bound_exprs;
        map                m_bound;
        bool               m_propagate_eq = false;
        ptr_vector<expr>   m_args;

        bv_bounds_base(ast_manager& m):m(m), m_bv(m) {}

        virtual ~bv_bounds_base() {
            for (auto* e : m_expr_vars)
                dealloc(e);
            for (auto* b : m_bound_exprs)
                dealloc(b);
        }

        bool is_bound(expr *e, expr*& v, interval& b) const {
            rational r;
            expr *lhs = nullptr, *rhs = nullptr;
            unsigned sz;

            if (m_bv.is_bv_ule(e, lhs, rhs)) {
                if (m_bv.is_numeral(lhs, r, sz)) { // C ule x <=> x uge C
                    if (m_bv.is_numeral(rhs))
                        return false;
                    b = interval(r, rational::power_of_two(sz) - 1, sz, true);
                    v = rhs;
                    return true;                    
                }
                if (m_bv.is_numeral(rhs, r, sz)) { // x ule C
                    b = interval(rational::zero(), r, sz, true);
                    v = lhs;
                    return true;
                }
                // TBD: x + s <= x + q
                //      x + s <= x
                //      x <= x + q
            } 
            else if (m_bv.is_bv_sle(e, lhs, rhs)) {
                if (m_bv.is_numeral(lhs, r, sz)) { // C sle x <=> x sge C
                    if (m_bv.is_numeral(rhs))
                        return false;
                    b = interval(r, rational::power_of_two(sz-1) - 1, sz, true);
                    v = rhs;
                    return true;
                }
                if (m_bv.is_numeral(rhs, r, sz)) { // x sle C
                    b = interval(rational::power_of_two(sz-1), r, sz, true);
                    v = lhs;
                    return true;
                }
                // TBD: other cases for forbidden intervals
            } 
            else if (m.is_eq(e, lhs, rhs)) {
                if (m_bv.is_numeral(rhs))
                    std::swap(lhs, rhs);
                if (m_bv.is_numeral(rhs))
                    return false;
                if (m_bv.is_numeral(lhs, r, sz)) {
                    unsigned lo, hi;
                    expr* rhs2;
                    if (m_bv.is_extract(rhs, lo, hi, rhs2) && r == 0) {
                        unsigned sz2 = m_bv.get_bv_size(rhs2);
                        if (sz2 - 1 == hi) {
                            b = interval(rational::zero(), rational::power_of_two(lo) - 1, sz2, false);
                            v = rhs2;
                            return true;
                        }
                    }
                    b = interval(r, r, sz, true);
                    v = rhs;
                    return true;
                }
            }
            return false;
        }

        bool assert_expr_core(expr * t, bool sign) {
            while (m.is_not(t, t)) 
                sign = !sign;            

            interval b;
            expr* t1;
            if (is_bound(t, t1, b)) {
                SASSERT(m_bv.get_bv_size(t1) == b.size());
                SASSERT(!m_bv.is_numeral(t1));
                if (sign && !b.negate(b))
                    return false;

                TRACE("bv", tout << (sign?"(not ":"") << mk_pp(t, m) << (sign ? ")" : "") << ": " << mk_pp(t1, m) << " in " << b << "\n";);
                map::obj_map_entry* e = m_bound.find_core(t1);
                if (e) {
                    interval& old = e->get_data().m_value;
                    interval intr;
                    if (!old.intersect(b, intr))
                        return false;
                    if (old == intr)
                        return true;
                    m_scopes.push_back(undo_bound(t1, old, false));
                    old = intr;
                    SASSERT(old.size() == m_bv.get_bv_size(t1));
                } 
                else {
                    SASSERT(b.size() == m_bv.get_bv_size(t1));
                    m_bound.insert(t1, b);
                    m_scopes.push_back(undo_bound(t1, interval(), true));
                }
            }
            return true;
        }

        //
        // x + q <= s <=> x not in [s - q + 1, -q[
        //            <=> x in [-q, s - q], s != -1
        //
        // x in [lo, hi]
        // q = -lo
        // hi = s + lo => s = hi - lo
        // hi - lo != -1
        // 

        expr_ref mk_bound(expr* t, rational const& lo, rational const& hi) {
            sort* s = t->get_sort();

            if (lo == hi + 1)
                return expr_ref(m.mk_true(), m);
            else 
                return expr_ref(m_bv.mk_ule(m_bv.mk_bv_add(t, m_bv.mk_numeral(-lo, s)), m_bv.mk_numeral(hi - lo, s)), m);
        }

        // 
        // use interval information to rewrite sub-terms x to (0 ++ x[hi:0])
        // in other words, identify leading 0s.
        // 
        bool zero_patch(expr* t, expr_ref& result) {
            if (!is_app(t))
                return false;

            if (m_bv.is_extract(t))
                return false;

            m_args.reset();
            bool simplified = false;
            interval b;
            for (expr* arg : *to_app(t)) {
                if (!m_bv.is_bv(arg)) {
                    m_args.push_back(arg);
                    continue;
                }
                if (!m_bv.is_extract(arg) && m_bound.find(arg, b) && b.lo() <= b.hi()) {
                    unsigned num_bits = b.hi().get_num_bits();
                    unsigned bv_size = m_bv.get_bv_size(arg);
                    if (0 < num_bits && num_bits < bv_size) {
                        m_args.push_back(m_bv.mk_concat(m_bv.mk_zero(bv_size - num_bits), 
                                                        m_bv.mk_extract(num_bits - 1, 0, arg)));                        
                        simplified = true;
                    }
                    else 
                        m_args.push_back(arg);
                }
                else
                    m_args.push_back(arg);
            }

            if (simplified) {
                result = m.mk_app(to_app(t)->get_decl(), m_args);
                TRACE("bv", tout << mk_pp(t, m) << " -> " << result << "\n");
                return true;
            }

            return false;
        }

        bool simplify_core(expr* t, expr_ref& result) {
            expr* t1;
            interval b;

            if (m_bound.find(t, b) && b.is_singleton()) {
                result = m_bv.mk_numeral(b.lo(), m_bv.get_bv_size(t));
                return true;
            }

            if (zero_patch(t, result))
                return result;
            
            if (!m.is_bool(t))
                return false;

            bool sign = false;
            while (m.is_not(t, t)) 
                sign = !sign;

            if (!is_bound(t, t1, b))
                return false;

            if (sign && b.tight()) {
                sign = false;
                if (!b.negate(b)) {
                    result = m.mk_false();
                    return true;
                }
            }

            interval ctx, intr;
            result = nullptr;

            if (b.is_full() && b.tight()) 
                result = m.mk_true();
            else if (!m_bound.find(t1, ctx)) {
            }
            else if (ctx.implies(b)) 
                result = m.mk_true();
            else if (!b.intersect(ctx, intr)) 
                result = m.mk_false();
            else if (m_propagate_eq && intr.is_singleton()) 
                result = m.mk_eq(t1, m_bv.mk_numeral(intr.lo(), t1->get_sort()));
            else if (false && intr != b) 
                result = mk_bound(t1, intr.lo(), intr.hi());
            else {
                TRACE("bv", tout << mk_pp(t, m) << " b: " << b << " ctx: " << ctx << " intr " << intr << "\n");
            }

            CTRACE("bv", result, tout << mk_pp(t, m) << " " << b << " (ctx: " << ctx << ") (intr: " << intr << "): " << result << "\n";);
            if (sign && result)
                result = m.mk_not(result);
            return result != nullptr;
        }

        // check if t contains v
        ptr_vector<expr> todo;
        bool contains(expr* t, expr* v) {
            ast_fast_mark1 mark;
            todo.push_back(t);
            while (!todo.empty()) {
                t = todo.back();
                todo.pop_back();
                if (mark.is_marked(t))
                    continue;                
                if (t == v) {
                    todo.reset();
                    return true;
                }
                mark.mark(t);
            
                if (!is_app(t)) 
                    continue;                
                app* a = to_app(t);
                todo.append(a->get_num_args(), a->get_args());
            }
            return false;
        }

        bool contains_bound(expr* t) {
            ast_fast_mark1 mark1;
            ast_fast_mark2 mark2;

            todo.push_back(t);
            while (!todo.empty()) {
                t = todo.back();
                todo.pop_back();
                if (mark1.is_marked(t)) {
                    continue;
                }
                mark1.mark(t);
            
                if (!is_app(t)) {
                    continue;
                }
                interval b;
                expr* e;
                if (is_bound(t, e, b)) {
                    if (mark2.is_marked(e)) {
                        todo.reset();
                        return true;
                    }
                    mark2.mark(e);
                    if (m_bound.contains(e)) {
                        todo.reset();
                        return true;
                    }
                }

                app* a = to_app(t);
                todo.append(a->get_num_args(), a->get_args());
            }
            return false;
        }

        void pop_core(unsigned num_scopes) {
            TRACE("bv", tout << "pop: " << num_scopes << "\n";);
            if (m_scopes.empty())
                return;
            unsigned target = m_scopes.size() - num_scopes;
            if (target == 0) {
                m_bound.reset();
                m_scopes.reset();
                return;
            }
            for (unsigned i = m_scopes.size(); i-- > target; ) {
                undo_bound& undo = m_scopes[i];
                SASSERT(m_bound.contains(undo.e));
                if (undo.fresh) 
                    m_bound.erase(undo.e);
                else 
                    m_bound.insert(undo.e, undo.b);                
            }
            m_scopes.shrink(target);
        }

    };

}
