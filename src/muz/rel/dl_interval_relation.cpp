/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_interval_relation.cpp

Abstract:

    Basic interval reatlion.

Author:

    Nikolaj Bjorner (nbjorner) 2010-2-11

Revision History:

--*/

#include "util/debug.h"
#include "ast/ast_pp.h"
#include "muz/rel/dl_interval_relation.h"
#include "muz/rel/dl_relation_manager.h"
#include "ast/rewriter/bool_rewriter.h"


namespace datalog {
    // -------------------------
    // interval_relation_plugin

    interval_relation_plugin::interval_relation_plugin(relation_manager& m):
        relation_plugin(interval_relation_plugin::get_name(), m), 
        m_empty(m_dep),
        m_arith(get_ast_manager()) {
    }

    bool interval_relation_plugin::can_handle_signature(const relation_signature & sig) {
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (!m_arith.is_int(sig[i]) && !m_arith.is_real(sig[i])) {
                return false;
            }
        }
        return true;
    }


    relation_base * interval_relation_plugin::mk_empty(const relation_signature & s) {
        return alloc(interval_relation, *this, s, true);
    }

    relation_base * interval_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {        
        return alloc(interval_relation, *this, s, false);
    }

    class interval_relation_plugin::join_fn : public convenient_relation_join_fn {
    public:
        join_fn(const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2){
        }

        relation_base * operator()(const relation_base & _r1, const relation_base & _r2) override {
            interval_relation const& r1 = get(_r1);
            interval_relation const& r2 = get(_r2);
            interval_relation_plugin& p = r1.get_plugin();
            interval_relation* result = dynamic_cast<interval_relation*>(p.mk_full(nullptr, get_result_signature()));
            result->mk_join(r1, r2, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
            return result;
        }
    };

    relation_join_fn * interval_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(r1) || !check_kind(r2)) {
            return nullptr;
        }
        return alloc(join_fn, r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2);
    }


    class interval_relation_plugin::project_fn : public convenient_relation_project_fn {
    public:
        project_fn(const relation_signature & orig_sig, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(orig_sig, removed_col_cnt, removed_cols) {
        }

        relation_base * operator()(const relation_base & _r) override {
            interval_relation const& r = get(_r);
            interval_relation_plugin& p = r.get_plugin();
            interval_relation* result = dynamic_cast<interval_relation*>(p.mk_full(nullptr, get_result_signature()));
            result->mk_project(r, m_removed_cols.size(), m_removed_cols.c_ptr());
            return result;
        }
    };

    relation_transformer_fn * interval_relation_plugin::mk_project_fn(const relation_base & r, 
            unsigned col_cnt, const unsigned * removed_cols) {
        return alloc(project_fn, r.get_signature(), col_cnt, removed_cols);
    }
   
    class interval_relation_plugin::rename_fn : public convenient_relation_rename_fn {
    public:
        rename_fn(const relation_signature & orig_sig, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(orig_sig, cycle_len, cycle) {
        }

        relation_base * operator()(const relation_base & _r) override {
            interval_relation const& r = get(_r);
            interval_relation_plugin& p = r.get_plugin();
            interval_relation* result = dynamic_cast<interval_relation*>(p.mk_full(nullptr, get_result_signature()));
            result->mk_rename(r, m_cycle.size(), m_cycle.c_ptr());
            return result;
        }
    };

    relation_transformer_fn * interval_relation_plugin::mk_rename_fn(const relation_base & r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if(!check_kind(r)) {
            return nullptr;
        }
        return alloc(rename_fn, r.get_signature(), cycle_len, permutation_cycle);
    }
     
    interval interval_relation_plugin::unite(interval const& src1, interval const& src2) {
        bool l_open = src1.is_lower_open();
        bool r_open = src1.is_upper_open();
        ext_numeral low = src1.inf();
        ext_numeral high = src1.sup();
        if (src2.inf() < low || (src2.inf() == low && l_open)) {
            low = src2.inf();
            l_open = src2.is_lower_open();
        }
        if (src2.sup() > high || (src2.sup() == high && r_open)) {
            high = src2.sup();
            r_open = src2.is_upper_open();
        }
        return interval(dep(), low, l_open, nullptr, high, r_open, nullptr);
    }

    interval interval_relation_plugin::widen(interval const& src1, interval const& src2) {
        bool l_open = src1.is_lower_open();
        bool r_open = src1.is_upper_open();
        ext_numeral low = src1.inf();
        ext_numeral high = src1.sup();
        
        if (src2.inf() < low || (low == src2.inf() && l_open && !src2.is_lower_open())) {
            low = ext_numeral(false);
            l_open = true;
        }
        if (high < src2.sup() || (src2.sup() == high && !r_open && src2.is_upper_open())) {
            high = ext_numeral(true);
            r_open = true;
        }
        return interval(dep(), low, l_open, nullptr, high, r_open, nullptr);
    }

    interval interval_relation_plugin::meet(interval const& src1, interval const& src2, bool& isempty) {
        isempty = false;
        if (is_empty(0, src1) || is_infinite(src2)) {
            return src1;
        }
        if (is_empty(0, src2) || is_infinite(src1)) {
            return src2;
        }
        bool l_open = src1.is_lower_open();
        bool r_open = src1.is_upper_open();
        ext_numeral low = src1.inf();
        ext_numeral high = src1.sup();
        if (src2.inf() > low || (src2.inf() == low && !l_open)) {
            low = src2.inf();
            l_open = src2.is_lower_open();
        }
        if (src2.sup() < high || (src2.sup() == high && !r_open)) {
            high = src2.sup();
            r_open = src2.is_upper_open();
        }
        if (low > high || (low == high && (l_open || r_open))) {
            isempty = true;
            return interval(dep());
        }
        else {
            return interval(dep(), low, l_open, nullptr, high, r_open, nullptr);
        }
    }
    
    bool interval_relation_plugin::is_infinite(interval const& i) {
        return i.plus_infinity() && i.minus_infinity();
    }

    bool interval_relation_plugin::is_empty(unsigned, interval const& i) {
        return i.sup() < i.inf();
    }

    class interval_relation_plugin::union_fn : public relation_union_fn {
        bool                      m_is_widen;
    public:
        union_fn(bool is_widen) :
            m_is_widen(is_widen) {            
        }

        void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) override {

            TRACE("interval_relation", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););

            interval_relation& r = get(_r);
            interval_relation const& src = get(_src);
            if (_delta) {
                interval_relation& d = get(*_delta);
                r.mk_union(src, &d, m_is_widen);
            }
            else {
                r.mk_union(src, nullptr, m_is_widen);
            }            
        }
    };

    relation_union_fn * interval_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return nullptr;
        }
        return alloc(union_fn, false);
    }

    relation_union_fn * interval_relation_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return nullptr;
        }
        return alloc(union_fn, true);
    }

    class interval_relation_plugin::filter_identical_fn : public relation_mutator_fn {
        unsigned_vector m_identical_cols;
    public:
        filter_identical_fn(unsigned col_cnt, const unsigned * identical_cols) 
            : m_identical_cols(col_cnt, identical_cols) {}

        void operator()(relation_base & r) override {
            interval_relation & pr = get(r);
            for (unsigned i = 1; i < m_identical_cols.size(); ++i) {
                unsigned c1 = m_identical_cols[0];
                unsigned c2 = m_identical_cols[i];
                pr.equate(c1, c2);
            }
        }
    };

    relation_mutator_fn * interval_relation_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        if(!check_kind(t)) {
            return nullptr;
        }
        return alloc(filter_identical_fn, col_cnt, identical_cols);
    }


    class interval_relation_plugin::filter_equal_fn : public relation_mutator_fn {
        unsigned m_col;
        rational m_value;
    public:
        filter_equal_fn(relation_manager & m, const relation_element & value, unsigned col) 
            : m_col(col) {
            arith_util arith(m.get_context().get_manager());
            VERIFY(arith.is_numeral(value, m_value));            
        }

        void operator()(relation_base & _r) override {
            interval_relation & r = get(_r);
            interval_relation_plugin & p = r.get_plugin();
            r.mk_intersect(m_col, interval(p.dep(), m_value));
            TRACE("interval_relation", tout << m_value << "\n"; r.display(tout););            
        }
    };

    relation_mutator_fn * interval_relation_plugin::mk_filter_equal_fn(const relation_base & r, 
        const relation_element & value, unsigned col) {
        if(check_kind(r)) {
            return alloc(filter_equal_fn, get_manager(), value, col);
        }
        return nullptr;
    }


    class interval_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        app_ref m_cond;
    public:
        filter_interpreted_fn(interval_relation const& t, app* cond):
            m_cond(cond, t.get_plugin().get_ast_manager()) {
        }

        void operator()(relation_base& t) override {
            get(t).filter_interpreted(m_cond);
            TRACE("interval_relation", tout << mk_pp(m_cond, m_cond.get_manager()) << "\n"; t.display(tout););
        }
    };

    relation_mutator_fn * interval_relation_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        if (check_kind(t)) {
            return alloc(filter_interpreted_fn, get(t), condition);
        }
        return nullptr;
    }

    interval_relation& interval_relation_plugin::get(relation_base& r) {
        return dynamic_cast<interval_relation&>(r);
    }

    interval_relation const & interval_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<interval_relation const&>(r);
    }

    // -----------------------
    // interval_relation

    interval_relation::interval_relation(interval_relation_plugin& p, relation_signature const& s, bool is_empty):
        vector_relation<interval>(p, s, is_empty, interval(p.dep())) 
    {
        TRACE("interval_relation", tout << s.size() << "\n";);
    }    

    void interval_relation::add_fact(const relation_fact & f) {
        interval_relation r(get_plugin(), get_signature(), false);
        ast_manager& m = get_plugin().get_ast_manager();        
        for (unsigned i = 0; i < f.size(); ++i) {
            app_ref eq(m);
            expr* e = f[i];
            eq = m.mk_eq(m.mk_var(i, m.get_sort(e)), e);
            r.filter_interpreted(eq.get());
        }            
        mk_union(r, nullptr, false);
    }

    bool interval_relation::contains_fact(const relation_fact & f) const {
        SASSERT(f.size() == get_signature().size());
        interval_relation_plugin& p = get_plugin();

        for (unsigned i = 0; i < f.size(); ++i) {
            if (f[i] != f[find(i)]) {
                return false;
            }
            interval const& iv = (*this)[i];
            if (p.is_infinite(iv)) {
                continue;
            }
            rational v;
            if (p.m_arith.is_numeral(f[i], v)) {
                if (!iv.contains(v)) {
                    return false;
                }
            }
            else {
                // TBD: may or must?
            }
        }
        return true;
    }

    interval_relation * interval_relation::clone() const {
        interval_relation* result = alloc(interval_relation, get_plugin(), get_signature(), empty());
        result->copy(*this);
        return result;
    }

    interval_relation * interval_relation::complement(func_decl*) const {
        UNREACHABLE();
        return nullptr;
    }

    void interval_relation::to_formula(expr_ref& fml) const {
        ast_manager& m = get_plugin().get_ast_manager();
        arith_util& arith = get_plugin().m_arith;
        expr_ref_vector conjs(m);
        relation_signature const& sig = get_signature();
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (i != find(i)) {
                conjs.push_back(m.mk_eq(m.mk_var(i, sig[i]), 
                                        m.mk_var(find(i), sig[find(i)])));
                continue;
            }            
            interval const& iv = (*this)[i];
            sort* ty = sig[i];
            expr_ref var(m.mk_var(i, ty), m);
            if (!iv.minus_infinity()) {
                expr* lo = arith.mk_numeral(iv.get_lower_value(), ty);
                if (iv.is_lower_open()) {
                    conjs.push_back(arith.mk_lt(lo, var));
                }
                else {
                    conjs.push_back(arith.mk_le(lo, var));
                }
            }
            if (!iv.plus_infinity()) {
                expr* hi = arith.mk_numeral(iv.get_upper_value(), ty);
                if (iv.is_upper_open()) {
                    conjs.push_back(arith.mk_lt(var, hi));
                }
                else {
                    conjs.push_back(arith.mk_le(var, hi));
                }
            }
        }
        bool_rewriter br(m);
        br.mk_and(conjs.size(), conjs.c_ptr(), fml);
    }


    void interval_relation::display_index(unsigned i, interval const& j, std::ostream & out) const {
        out << i << " in " << j << "\n";                
    }

    interval_relation_plugin& interval_relation::get_plugin() const {
        return static_cast<interval_relation_plugin &>(relation_base::get_plugin());        
    }

    void interval_relation::mk_intersect(unsigned idx, interval const& i) {
        bool isempty;
        (*this)[idx] = mk_intersect((*this)[idx], i, isempty);
        if (isempty || is_empty(idx, (*this)[idx])) {
            set_empty();
        }
    }

    void interval_relation::mk_rename_elem(interval& i, unsigned, unsigned const* ) {

    }

    void interval_relation::filter_interpreted(app* cond) {
        interval_relation_plugin& p = get_plugin();
        rational k;
        unsigned x, y;
        if (p.is_lt(cond, x, k, y)) {
            // 0 < x - y + k
            if (x == UINT_MAX) {
                // y < k
                mk_intersect(y, interval(p.dep(), k, true, false, nullptr));
                return;
            }
            if (y == UINT_MAX) {
                // -k < x
                mk_intersect(x, interval(p.dep(), -k, true, true, nullptr));
                return;
            }
            // y < x + k
            ext_numeral x_hi = (*this)[x].sup();
            ext_numeral y_lo = (*this)[y].inf();
            if (!x_hi.is_infinite()) {
                mk_intersect(y, interval(p.dep(), k + x_hi.to_rational(), true, false, nullptr));
            }
            if (!y_lo.is_infinite()) {
                mk_intersect(x, interval(p.dep(), y_lo.to_rational() - k, true, true, nullptr));
            }
            return;
        }
        bool is_int = false;
        if (p.is_le(cond, x, k, y, is_int)) {
            // 0 <= x - y + k
            if (x == UINT_MAX) {
                // y <= k
                mk_intersect(y, interval(p.dep(), k, false, false, nullptr));
                return;
            }
            if (y == UINT_MAX) {
                // -k <= x
                mk_intersect(x, interval(p.dep(), -k, false, true, nullptr));
                return;
            }
            ext_numeral x_hi = (*this)[x].sup();
            ext_numeral y_lo = (*this)[y].inf();
            if (!x_hi.is_infinite()) {
                mk_intersect(y, interval(p.dep(), k + x_hi.to_rational(), false, false, nullptr));
            }
            if (!y_lo.is_infinite()) {
                mk_intersect(x, interval(p.dep(), y_lo.to_rational() - k, false, true, nullptr));
            }
            return;
        }
        if (p.is_eq(cond, x, k, y)) {
            // y = x + k
            if (x == UINT_MAX) {
                SASSERT(y != UINT_MAX);
                mk_intersect(y, interval(p.dep(), k));
                return;
            }
            if (y == UINT_MAX) {
                // x = - k
                SASSERT(x != UINT_MAX);
                mk_intersect(x, interval(p.dep(), -k));
                return;
            }
            interval x_i = (*this)[x];
            interval y_i = (*this)[y];
            x_i += interval(p.dep(), k);
            y_i -= interval(p.dep(), k);
            mk_intersect(x, y_i);
            mk_intersect(y, x_i);
        }
        if (get_plugin().get_ast_manager().is_false(cond)) {
            set_empty();
        }
    }

    bool interval_relation_plugin::is_linear(expr* e, unsigned& neg, unsigned& pos, rational& k, bool is_pos) const {
#define SET_VAR(_idx_)                              \
            if (is_pos &&pos == UINT_MAX) {         \
                pos = _idx_;                        \
                return true;                        \
            }                                       \
            if (!is_pos && neg == UINT_MAX) {       \
                neg = _idx_;                        \
                return true;                        \
            }                                       \
            else {                                  \
                return false;                       \
            }                   

        if (is_var(e)) {
            SET_VAR(to_var(e)->get_idx());
        }
        if (!is_app(e)) {
            return false;
        }
        app* a = to_app(e);
 
        if (m_arith.is_add(e)) {
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                if (!is_linear(a->get_arg(i), neg, pos, k, is_pos)) return false;
            }
            return true;
        }
        if (m_arith.is_sub(e)) {
            SASSERT(a->get_num_args() == 2);
            return 
                is_linear(a->get_arg(0), neg, pos, k, is_pos) &&
                is_linear(a->get_arg(1), neg, pos, k, !is_pos);
        }
        rational k1;
        SASSERT(!m_arith.is_mul(e) || a->get_num_args() == 2);
        if (m_arith.is_mul(e) &&
            m_arith.is_numeral(a->get_arg(0), k1) && 
            k1.is_minus_one() &&
            is_var(a->get_arg(1))) {
            SET_VAR(to_var(a->get_arg(1))->get_idx());                
        }
        
        if (m_arith.is_numeral(e, k1)) {
            if (is_pos) {
                k += k1;
            }
            else {
                k -= k1;
            }
            return true;
        }
        return false;
    }

    // 0 <= x - y + k
    bool interval_relation_plugin::is_le(app* cond, unsigned& x, rational& k, unsigned& y, bool& is_int) const {
        ast_manager& m = get_ast_manager();
        k.reset();
        x = UINT_MAX;
        y = UINT_MAX;

        if (m_arith.is_le(cond)) {
            is_int = m_arith.is_int(cond->get_arg(0));
            if (!is_linear(cond->get_arg(0), y, x, k, false)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, true)) return false;
            return (x != UINT_MAX || y != UINT_MAX);
        }
        if (m_arith.is_ge(cond)) {
            is_int = m_arith.is_int(cond->get_arg(0));
            if (!is_linear(cond->get_arg(0), y, x, k, true)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, false)) return false;
            return (x != UINT_MAX || y != UINT_MAX);
        }
        if (m_arith.is_lt(cond) && m_arith.is_int(cond->get_arg(0))) {
            is_int = true;
            if (!is_linear(cond->get_arg(0), y, x, k, false)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, true)) return false;
            k -= rational::one();
            return (x != UINT_MAX || y != UINT_MAX);
        }
        if (m_arith.is_gt(cond) && m_arith.is_int(cond->get_arg(0))) {
            is_int = true;
            if (!is_linear(cond->get_arg(0), y, x, k, true)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, false)) return false;
            k += rational::one();
            return (x != UINT_MAX || y != UINT_MAX);
        }
        if (m.is_not(cond) && is_app(cond->get_arg(0))) {
            //     not (0 <= x - y + k) 
            // <=>
            //     0 > x - y + k
            // <=>
            //     0 <= y - x - k - 1
            if (is_le(to_app(cond->get_arg(0)), x, k, y, is_int) && is_int) {
                k.neg();
                k -= rational::one();                
                std::swap(x, y);
                return true;
            }
            //     not (0 < x - y + k) 
            // <=>
            //     0 >= x - y + k
            // <=>
            //     0 <= y - x - k 
            if (is_lt(to_app(cond->get_arg(0)), x, k, y)) {
                is_int = false;
                k.neg();
                std::swap(x, y);
                return true;
            }
        }
        return false;
    }

    // 0 < x - y + k
    bool interval_relation_plugin::is_lt(app* cond, unsigned& x, rational& k, unsigned& y) const {
        k.reset();
        x = UINT_MAX;
        y = UINT_MAX;
        if (m_arith.is_lt(cond) && m_arith.is_real(cond->get_arg(0))) {
            if (!is_linear(cond->get_arg(0), y, x, k, false)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, true)) return false;
            return (x != UINT_MAX || y != UINT_MAX);
        }
        if (m_arith.is_gt(cond) && m_arith.is_real(cond->get_arg(0))) {
            if (!is_linear(cond->get_arg(0), y, x, k, true)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, false)) return false;
            return (x != UINT_MAX || y != UINT_MAX);
        }
        return false;
    }

    // 0 = x - y + k 
    bool interval_relation_plugin::is_eq(app* cond, unsigned& x, rational& k, unsigned& y) const {
        ast_manager& m = get_ast_manager();
        k.reset();
        x = UINT_MAX;
        y = UINT_MAX;
        if (m.is_eq(cond)) {
            if (!is_linear(cond->get_arg(0), y, x, k, false)) return false;
            if (!is_linear(cond->get_arg(1), y, x, k, true)) return false;
            return (x != UINT_MAX || y != UINT_MAX);
        }
        return false;
    }

};

