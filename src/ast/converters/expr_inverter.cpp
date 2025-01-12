/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    expr_inverter.cpp

Abstract:

    inverter interface and instance

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-11

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/converters/expr_inverter.h"

class basic_expr_inverter : public iexpr_inverter {
    iexpr_inverter& inv;

    bool process_eq(func_decl* f, expr* arg1, expr* arg2, expr_ref& r) {
        expr* v;
        expr* t;
        if (uncnstr(arg1)) 
            v = arg1, t = arg2;        
        else if (uncnstr(arg2)) 
            v = arg2, t = arg1;        
        else
            return false;

        expr_ref d(m);
        if (!inv.mk_diff(t, d))
            return false;

        mk_fresh_uncnstr_var_for(f, r);
        if (m_mc)
            add_def(v, m.mk_ite(r, t, d));

        return true;
    }

public:

    basic_expr_inverter(ast_manager& m, iexpr_inverter& inv) : iexpr_inverter(m), inv(inv) {}

    family_id get_fid() const override { return m.get_basic_family_id(); }

    /**
     * if (c, x, x') -> fresh
     * x := fresh
     * x' := fresh
     * 
     * if (x, x', e) -> fresh
     * x := true
     * x' := fresh
     * 
     * if (x, t, x') -> fresh
     * x := false
     * x' := fresh
     * 
     * not x -> fresh
     * x := not fresh
     * 
     * x & x' -> fresh
     * x := fresh
     * x' := true
     * 
     * x or x' -> fresh
     * x := fresh
     * x' := false
     *
     * x = t -> fresh
     * x := if(fresh, t, diff(t))
     * where diff is a diagonalization function available in domains of size > 1.
     *
     */

    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        SASSERT(f->get_family_id() == m.get_basic_family_id());
        switch (f->get_decl_kind()) {
        case OP_ITE:
            SASSERT(num == 3);
            if (uncnstr(args[1]) && uncnstr(args[2])) {
                mk_fresh_uncnstr_var_for(f, r);
                add_def(args[1], r);
                add_def(args[2], r);
                return true;
            }
            if (uncnstr(args[0]) && uncnstr(args[1])) {
                mk_fresh_uncnstr_var_for(f, r);
                add_def(args[0], m.mk_true());
                add_def(args[1], r);
                return true;
            }
            if (uncnstr(args[0]) && uncnstr(args[2])) {
                mk_fresh_uncnstr_var_for(f, r);
                add_def(args[0], m.mk_false());
                add_def(args[2], r);
                return true;
            }
            return false;
        case OP_NOT:
            SASSERT(num == 1);
            if (uncnstr(args[0])) {
                mk_fresh_uncnstr_var_for(f, r);
                add_def(args[0], m.mk_not(r));
                return true;
            }
            return false;
        case OP_AND:
            if (num > 0 && uncnstr(num, args)) {
                mk_fresh_uncnstr_var_for(f, r);
                add_defs(num, args, r, m.mk_true());
                return true;
            }
            return false;
        case OP_OR:
            if (num > 0 && uncnstr(num, args)) {
                mk_fresh_uncnstr_var_for(f, r);
                add_defs(num, args, r, m.mk_false());
                return true;
            }
            return false;
        case OP_EQ:
            SASSERT(num == 2);
            return process_eq(f, args[0], args[1], r);
        default:
            return false;
        }        
        return false;
    }
    
    bool mk_diff(expr* t, expr_ref& r) override {
        SASSERT(m.is_bool(t));
        r = mk_not(m, t);
        return true;
    }
};

class arith_expr_inverter : public iexpr_inverter {
    arith_util a;
public:

    arith_expr_inverter(ast_manager& m) : iexpr_inverter(m), a(m) {}

    family_id get_fid() const override { return a.get_family_id(); }

    bool process_le_ge(func_decl* f, expr* arg1, expr* arg2, bool le, expr_ref& r) {
        expr* v;
        expr* t;
        if (uncnstr(arg1)) {
            v = arg1;
            t = arg2;
        }
        else if (uncnstr(arg2)) {
            v = arg2;
            t = arg1;
            le = !le;
        }
        else 
            return false;
        
        mk_fresh_uncnstr_var_for(f, r);
        if (m_mc) {
            // v = ite(u, t, t + 1) if le
            // v = ite(u, t, t - 1) if !le
            add_def(v, m.mk_ite(r, t, a.mk_add(t, a.mk_numeral(rational(le ? 1 : -1), arg1->get_sort()))));
        }
        return true;
    }

    bool process_add(unsigned num, expr* const* args, expr_ref& u) {
        if (num == 0)
            return false;
        unsigned i;
        expr* v = nullptr;
        for (i = 0; i < num; i++) {
            expr* arg = args[i];
            if (uncnstr(arg)) {
                v = arg;
                break;
            }
        }
        if (v == nullptr)
            return false;
        mk_fresh_uncnstr_var_for(v->get_sort(), u);
        if (!m_mc)
            return true;
        ptr_buffer<expr> new_args;
        for (unsigned j = 0; j < num; j++) 
            if (j != i)
                new_args.push_back(args[j]);
        
        if (new_args.empty()) 
            add_def(v, u);
        else {
            expr* rest = a.mk_add(new_args); 
            add_def(v, a.mk_sub(u, rest));
        }
        return true;
    }

    bool process_arith_mul(unsigned num, expr* const* args, expr_ref & u) {
        if (num == 0)
            return false;
        sort* s = args[0]->get_sort();
        if (uncnstr(num, args)) {
            mk_fresh_uncnstr_var_for(s, u);
            if (m_mc)
                add_defs(num, args, u, a.mk_numeral(rational(1), s));
            return true;
        }
        // c * v case for reals
        bool is_int;
        rational val;
        if (num == 2 && uncnstr(args[1]) && a.is_numeral(args[0], val, is_int) && !is_int) {
            if (val.is_zero())
                return false;
            mk_fresh_uncnstr_var_for(s, u);
            if (m_mc) {
                val = rational(1) / val;
                add_def(args[1], a.mk_mul(a.mk_numeral(val, false), u));
            }
            return true;
        }
        return false;
    }


    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        SASSERT(f->get_family_id() == a.get_family_id());
        switch (f->get_decl_kind()) {
        case OP_ADD:
            return process_add(num, args, r);
        case OP_MUL:
            return process_arith_mul(num, args, r);
        case OP_LE:
            SASSERT(num == 2);
            return process_le_ge(f, args[0], args[1], true, r);
        case OP_GE:
            SASSERT(num == 2);
            return process_le_ge(f, args[0], args[1], false, r);
        default:
            return false;
        }
    }


    bool mk_diff(expr* t, expr_ref& r) override {
        SASSERT(a.is_int_real(t));
        r = a.mk_add(t, a.mk_numeral(rational(1), a.is_int(t)));
        return true;
    }
};

class bv_expr_inverter : public iexpr_inverter {
    bv_util bv;

    bool process_add(unsigned num, expr* const* args, expr_ref& u) {
        if (num == 0)
            return false;
        unsigned i;
        expr* v = nullptr;
        for (i = 0; i < num; i++) {
            expr* arg = args[i];
            if (uncnstr(arg)) {
                v = arg;
                break;
            }
        }
        if (!v)
            return false;
        mk_fresh_uncnstr_var_for(v->get_sort(), u);
        if (!m_mc)
            return true;
        ptr_buffer<expr> new_args;
        for (unsigned j = 0; j < num; j++)
            if (j != i)
                new_args.push_back(args[j]);

        if (new_args.empty())
            add_def(v, u);
        else {
            expr* rest = bv.mk_bv_add(new_args);
            add_def(v, bv.mk_bv_sub(u, rest));
        }
        return true;
    }

    bool process_bv_mul(func_decl* f, unsigned num, expr* const* args, expr_ref& r) {
        if (num == 0)
            return false;
        if (uncnstr(num, args)) {
            sort* s = args[0]->get_sort();
            mk_fresh_uncnstr_var_for(f, r);
            if (m_mc)
                add_defs(num, args, r, bv.mk_one(s));
            return true;
        }
        // c * v (c is odd) case
        unsigned sz;
        rational val;
        rational inv;
        if (num == 2 &&
            uncnstr(args[1]) &&
            bv.is_numeral(args[0], val, sz) &&
            val.mult_inverse(sz, inv)) {
            mk_fresh_uncnstr_var_for(f, r);
            if (m_mc)
                add_def(args[1], bv.mk_bv_mul(bv.mk_numeral(inv, sz), r));
            return true;
        }

        //
        // x * K -> fresh[hi-sh-1:0] ++ 0...0
        // where sh = parity of K
        // then x -> J^-1*fresh 
        // where J = K >> sh
        // Because x * K = fresh * K * J^-1 = fresh * 2^sh = fresh[hi-sh-1:0] ++ 0...0
        //
        if (num == 2 &&
            uncnstr(args[1]) &&
            bv.is_numeral(args[0], val, sz) &&
            val.is_pos()) {
            unsigned sh = 0;
            while (val.is_even()) {
                val /= rational(2);
                ++sh;
            }
            mk_fresh_uncnstr_var_for(f, r);
            if (sh > 0)
                r = bv.mk_concat(bv.mk_extract(sz - sh - 1, 0, r), bv.mk_zero(sh));

            if (m_mc) {
                rational inv_r;
                VERIFY(val.mult_inverse(sz, inv_r));
                add_def(args[1], bv.mk_bv_mul(bv.mk_numeral(inv_r, sz), r)); 
            }
            return true;
        }

        //
        // assume x is unconstrained, we can handle general multiplication as follows: 
        // x * y -> if y = 0 then y else fresh << parity(y)
        // and x -> if y = 0 then y else (y >> parity(y))^-1
        // parity can be defined using a "giant" ite expression.
        //

#if 0
        for (unsigned i = 0; i < num; ++i)
            if (uncnstr(args[i]))
                IF_VERBOSE(11, verbose_stream() << "MISSED mult-unconstrained " << mk_bounded_pp(args[i], m) << "\n");
#endif

        return false;
    }


    bool process_extract(func_decl* f, expr* arg, expr_ref& r) {
        if (!uncnstr(arg))
            return false;
        mk_fresh_uncnstr_var_for(f, r);
        if (!m_mc)
            return true;
        unsigned high = bv.get_extract_high(f);
        unsigned low = bv.get_extract_low(f);
        unsigned bv_size = bv.get_bv_size(arg->get_sort());
        if (bv_size == high - low + 1) 
            add_def(arg, r);        
        else {
            ptr_buffer<expr> args;
            if (high < bv_size - 1)
                args.push_back(bv.mk_zero(bv_size - high - 1));
            args.push_back(r);
            if (low > 0)
                args.push_back(bv.mk_zero(low));
            add_def(arg, bv.mk_concat(args.size(), args.data()));
        }
        return true;
    }

    bool process_bv_div(func_decl* f, expr* arg1, expr* arg2, expr_ref& r) {
        if (uncnstr(arg1) && uncnstr(arg2)) {
            sort* s = arg1->get_sort();
            mk_fresh_uncnstr_var_for(f, r);
            if (m_mc) {
                add_def(arg1, r);
                add_def(arg2, bv.mk_one(s));
            }
            return true;
        }
        return false;
    }

    bool process_concat(func_decl* f, unsigned num, expr* const* args, expr_ref& r) {
//        return false;
        if (num == 0)
            return false;
        if (!uncnstr(num, args))
            return false;
        mk_fresh_uncnstr_var_for(f, r);
        if (m_mc) {
            unsigned i = num;
            unsigned low = 0;
            while (i > 0) {
                --i;
                expr* arg = args[i];
                unsigned sz = bv.get_bv_size(arg);
                add_def(arg, bv.mk_extract(low + sz - 1, low, r));
                low += sz;
            }
        }
        return true;
    }

    bool process_bv_le(func_decl* f, expr* arg1, expr* arg2, bool is_signed, expr_ref& r) {
        unsigned bv_sz = bv.get_bv_size(arg1);
        if (uncnstr(arg1) && uncnstr(arg2)) {
            mk_fresh_uncnstr_var_for(f, r);
            if (m_mc) {
                add_def(arg1, m.mk_ite(r, bv.mk_zero(bv_sz), bv.mk_one(bv_sz)));
                add_def(arg2, bv.mk_zero(bv_sz));
            }
            return true;
        }
        if (uncnstr(arg1)) {
            // v <= t
            expr* v = arg1;
            expr* t = arg2;
            // v <= t --->  (u or t == MAX)   u is fresh
            //     add definition v = ite(u or t == MAX, t, t+1)
            
            rational MAX;
            if (is_signed)
                MAX = rational::power_of_two(bv_sz - 1) - rational(1);
            else
                MAX = rational::power_of_two(bv_sz) - rational(1);
            mk_fresh_uncnstr_var_for(f, r);
            r = m.mk_or(r, m.mk_eq(t, bv.mk_numeral(MAX, bv_sz)));
            if (m_mc)
                add_def(v, m.mk_ite(r, t, bv.mk_bv_add(t, bv.mk_one(bv_sz))));
            return true;
        }
        if (uncnstr(arg2)) {
            // v >= t
            expr* v = arg2;
            expr* t = arg1;
            // v >= t --->  (u ot t == MIN)  u is fresh
            //    add definition v = ite(u or t == MIN, t, t-1)
            rational MIN;
            if (is_signed)
                MIN = -rational::power_of_two(bv_sz - 1);
            else
                MIN = rational(0);
            mk_fresh_uncnstr_var_for(f, r);
            r = m.mk_or(r, m.mk_eq(t, bv.mk_numeral(MIN, bv_sz)));
            if (m_mc)
                add_def(v, m.mk_ite(r, t, bv.mk_bv_sub(t, bv.mk_one(bv_sz))));
            return true;
        }
        return false;
    }

    bool process_bvnot(expr* e, expr_ref& r) {
        if (!uncnstr(e))
            return false;
        mk_fresh_uncnstr_var_for(e->get_sort(), r);
        if (m_mc)
            add_def(e, bv.mk_bv_not(r));
        return true;
    }

    bool process_shift(func_decl* f, expr* arg1, expr* arg2, expr_ref& r) {
        if (uncnstr(arg1) && uncnstr(arg2)) {
            mk_fresh_uncnstr_var_for(f, r);
            if (m_mc) {
                add_def(arg1, r);
                add_def(arg2, bv.mk_zero(arg2->get_sort()));
            }
            return true;
        }
        return false;
    }

    public:
        bv_expr_inverter(ast_manager& m) : iexpr_inverter(m), bv(m) {}

        family_id get_fid() const override { return bv.get_family_id(); }

    /**
     * x + t -> fresh
     * x := fresh - t
     *
     * x * x' * x'' -> fresh
     * x := fresh
     * x', x'' := 1
     *
     * c * x -> fresh, c is odd
     * x := fresh*c^-1
     *
     * x[sz-1:0] -> fresh
     * x := fresh
     *
     * x[hi:lo] -> fresh
     * x := fresh1 ++ fresh ++ fresh2
     *
     * x udiv x', x sdiv x' -> fresh
     * x' := 1
     * x := fresh
     *
     * x ++ x' ++ x'' -> fresh
     * x   := fresh[hi1:lo1]
     * x'  := fresh[hi2:lo2]
     * x'' := fresh[hi3:lo3]
     *
     * x <= t -> fresh or t == MAX
     * x := if(fresh, t, t + 1)
     * t <= x -> fresh or t == MIN
     * x := if(fresh, t, t - 1)
     *
     * ~x -> fresh
     * x := ~fresh
     *
     * x | y -> fresh
     * x := fresh
     * y := 0
     *
     */
    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        SASSERT(f->get_family_id() == bv.get_family_id());
        switch (f->get_decl_kind()) {
        case OP_BADD:
            return process_add(num, args, r);
        case OP_BMUL:
            return process_bv_mul(f, num, args, r);
        case OP_BSDIV:
        case OP_BUDIV:
        case OP_BSDIV_I:
        case OP_BUDIV_I:
            SASSERT(num == 2);
            return process_bv_div(f, args[0], args[1], r);
        case OP_SLEQ:
            SASSERT(num == 2);
            return process_bv_le(f, args[0], args[1], true, r);
        case OP_ULEQ:
            SASSERT(num == 2);
            return process_bv_le(f, args[0], args[1], false, r);
        case OP_CONCAT:
            return process_concat(f, num, args, r);
        case OP_EXTRACT:
            SASSERT(num == 1);
            return process_extract(f, args[0], r);
        case OP_BNOT:
            SASSERT(num == 1);
            return process_bvnot(args[0], r);
        case OP_BOR:
            if (num > 0 && uncnstr(num, args)) {
                sort* s = args[0]->get_sort();
                mk_fresh_uncnstr_var_for(f, r);
                if (m_mc)
                    add_defs(num, args, r, bv.mk_zero(s));
                return true;
            }
            return false;
        case OP_BAND:
            if (num > 0 && uncnstr(num, args)) {
                sort* s = args[0]->get_sort();
                mk_fresh_uncnstr_var_for(f, r);
                if (m_mc)
                    add_defs(num, args, r, bv.mk_numeral(rational::power_of_two(bv.get_bv_size(s)) - 1, s));
                return true;
            }
            return false;
        case OP_BSHL:
        case OP_BASHR:
        case OP_BLSHR:
            return process_shift(f, args[0], args[1], r);
        default:
            return false;
        }
    }

    bool mk_diff(expr* t, expr_ref& r) override {
        SASSERT(bv.is_bv(t));
        r = bv.mk_bv_not(t);
        return true;
    }
};



/**
 * F[select(x, i)] -> F[fresh]
 * x := const(fresh)

 * F[store(x, ..., x')] -> F[fresh]
 * x' := select(x, ...)
 * x := fresh
 */

class array_expr_inverter : public iexpr_inverter {
    array_util a;
    iexpr_inverter& inv;
public:
    array_expr_inverter(ast_manager& m, iexpr_inverter& s) : iexpr_inverter(m), a(m), inv(s) {}

    family_id get_fid() const override { return a.get_family_id(); }

    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        SASSERT(f->get_family_id() == a.get_family_id());
        switch (f->get_decl_kind()) {
        case OP_SELECT:
            if (uncnstr(args[0])) {
                mk_fresh_uncnstr_var_for(f, r);
                sort* s = args[0]->get_sort();
                if (m_mc)
                    add_def(args[0], a.mk_const_array(s, r));
                return true;
            }
            return false;
        case OP_STORE:
            if (uncnstr(args[0]) && uncnstr(args[num - 1])) {
                mk_fresh_uncnstr_var_for(f, r);
                if (m_mc) {
                    add_def(args[num - 1], m.mk_app(a.get_family_id(), OP_SELECT, num - 1, args));
                    add_def(args[0], r);
                }
                return true;
            }
            return false;
        default:
            return false;
        }
    }

    bool mk_diff(expr* t, expr_ref& r) override {
        sort* s = t->get_sort();
        SASSERT(a.is_array(s));
        if (m.is_uninterp(get_array_range(s)))
            return false;
        unsigned arity = get_array_arity(s);
        for (unsigned i = 0; i < arity; i++)
            if (m.is_uninterp(get_array_domain(s, i)))
                return false;
        // building 
        // r = (store t i1 ... in d)
        // where i1 ... in are arbitrary values
        // and d is a term different from (select t i1 ... in)
        expr_ref_vector new_args(m);
        new_args.push_back(t);
        for (unsigned i = 0; i < arity; i++)
            new_args.push_back(m.get_some_value(get_array_domain(s, i)));
        expr_ref sel(m);
        sel = a.mk_select(new_args);
        expr_ref diff_sel(m);
        if (!inv.mk_diff(sel, diff_sel))
            return false;
        new_args.push_back(diff_sel);
        r = a.mk_store(new_args);
        return true;
    }
};



class dt_expr_inverter : public iexpr_inverter {
    datatype_util dt;
public:

    dt_expr_inverter(ast_manager& m) : iexpr_inverter(m), dt(m) {}

    family_id get_fid() const override { return dt.get_family_id(); }
    /**
     *   head(x) -> fresh
     *   x := cons(fresh, arb)
     */
    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        if (dt.is_accessor(f)) {
            SASSERT(num == 1);
            if (uncnstr(args[0])) {
                if (!m_mc) {
                    mk_fresh_uncnstr_var_for(f, r);
                    return true;
                }
                func_decl* c = dt.get_accessor_constructor(f);
                for (unsigned i = 0; i < c->get_arity(); i++)
                    if (!m.is_fully_interp(c->get_domain(i)))
                        return false;
                mk_fresh_uncnstr_var_for(f, r);
                ptr_vector<func_decl> const& accs = *dt.get_constructor_accessors(c);
                ptr_buffer<expr> new_args;
                for (unsigned i = 0; i < accs.size(); i++) {
                    if (accs[i] == f)
                        new_args.push_back(r);
                    else
                        new_args.push_back(m.get_some_value(c->get_domain(i)));
                }
                add_def(args[0], m.mk_app(c, new_args));
                return true;
            }
        }
        return false;
    }

    bool mk_diff(expr* t, expr_ref& r) override {
        // In the current implementation, I only handle the case where
        // the datatype has a recursive constructor.
        sort* s = t->get_sort();
        ptr_vector<func_decl> const& constructors = *dt.get_datatype_constructors(s);
        for (func_decl* constructor : constructors) {
            unsigned num = constructor->get_arity();
            unsigned target = UINT_MAX;
            for (unsigned i = 0; i < num; i++) {
                sort* s_arg = constructor->get_domain(i);
                if (s == s_arg) {
                    target = i;
                    continue;
                }
                if (m.is_uninterp(s_arg))
                    break;
            }
            if (target == UINT_MAX)
                continue;
            // use the constructor the distinct term constructor(...,t,...)
            ptr_buffer<expr> new_args;
            for (unsigned i = 0; i < num; i++) {
                if (i == target) 
                    new_args.push_back(t);
                else 
                    new_args.push_back(m.get_some_value(constructor->get_domain(i)));
            }
            r = m.mk_app(constructor, new_args);
            return true;
        }
        return false;
    }
};

#if 0
class pb_expr_inverter : public iexpr_inverter {
    pb_util pb;
public:
    pb_expr_inverter(ast_manager& m) : iexpr_inverter(m), pb(m) {}

    family_id get_fid() const override { return pb.get_family_id(); }

    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        rational k, c;
        unsigned new_k = 0;
        expr_ref_vector new_args(m), uncnstr_args(m);
        vector<rational> coeffs;
        switch (f->get_decl_kind()) {
        case OP_AT_MOST_K:
            // a' + b' + c  + d <= 3 -> r := c + d <= 1
            // a' + b' + c  + d <= 1 -> r := c + d <= 1
            // a' + b' + c' + d <= 2 -> r := fresh        
            // a', b', c' := ~r
            k = pb.get_k(f);
            if (!k.is_unsigned())
                return false;
            for (unsigned i = 0; i < num; ++i)
                if (uncnstr(args[i]))
                    uncnstr_args.push_back(args[i]);
                else
                    new_args.push_back(args[i]);
            if (uncnstr_args.empty())
                return false;
            if (new_args.size() <= k && uncnstr_args.size() > k) 
                mk_fresh_uncnstr_var_for(f, r);         
            else if (new_args.size() <= k) // k >= uncnstr_args.size()
                r = pb.mk_at_most_k(new_args, k.get_unsigned() - uncnstr_args.size());            
            else // |new_args| > k
                r = pb.mk_at_most_k(new_args, k.get_unsigned());
            if (m_mc) {
                for (unsigned i = 0; i < uncnstr_args.size(); ++i)
                    add_def(uncnstr_args.get(i), m.mk_not(r));
            }
            return true;
        case OP_AT_LEAST_K:
            k = pb.get_k(f);
            if (!k.is_unsigned())
                return false;
            for (unsigned i = 0; i < num; ++i)
                if (uncnstr(args[i]))
                    uncnstr_args.push_back(args[i]);
                else
                    new_args.push_back(args[i]);
            if (uncnstr_args.empty())
                return false;
            // cases k <= uncstr_args.size()
            // k > uncstr_args.size()
            return false;
        case OP_PB_LE:
            // 2*x + 3*y + z + 2*u <= k -> r
            // r := z + 2u <= 
            // 
            k = pb.get_k(f);
            for (unsigned i = 0; i < num; ++i)
                if (uncnstr(args[i]))
                    uncnstr_args.push_back(args[i]), c += pb.get_coeff(f, i);
                else
                    new_args.push_back(args[i]), coeffs.push_back(pb.get_coeff(f, i));
            if (uncnstr_args.empty())
                return false;
            return false;
        default:
            return false;
        }
    }

    bool mk_diff(expr* t, expr_ref& r) override {
         return false;
    }
};
#endif


class seq_expr_inverter : public iexpr_inverter {
    seq_util seq;
    seq_rewriter rw;
public:
    seq_expr_inverter(ast_manager& m) : iexpr_inverter(m), seq(m), rw(m) {}
    
    family_id get_fid() const override { return seq.get_family_id(); }

    bool operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& r) override {
        switch (f->get_decl_kind()) {
        case _OP_STRING_CONCAT:
        case OP_SEQ_CONCAT: {
            expr* x, *y;
            
            if (uncnstr(args[0]) && num == 2 &&
                args[1]->get_ref_count() == 1 && 
                seq.str.is_concat(args[1], x, y) &&
                uncnstr(x)) {
                mk_fresh_uncnstr_var_for(f, r);
                if (m_mc) {
                    add_def(args[0], seq.str.mk_empty(args[0]->get_sort()));
                    add_def(x, r);
                }
                r = seq.str.mk_concat(r, y);
                return true;                
            }
                
            if (!uncnstr(num, args)) 
                return false;
            mk_fresh_uncnstr_var_for(f, r);
            if (m_mc) {
                add_def(args[0], r);
                for (unsigned i = 1; i < num; ++i)
                    add_def(args[i], seq.str.mk_empty(args[0]->get_sort()));
            }            
            return true;
        }
        case OP_SEQ_CONTAINS:
            if (uncnstr(args[0])) {
                // x contains y -> r or y is empty
                mk_fresh_uncnstr_var_for(f, r);
                expr_ref emp(seq.str.mk_is_empty(args[0]), m);
                if (m_mc)
                    add_def(args[0], m.mk_ite(r, args[1], seq.str.mk_empty(args[0]->get_sort())));
                r = m.mk_or(r, emp);
                return true;
            }
            if (uncnstr(args[1]) && seq.is_string(args[0]->get_sort())) {
                // x contains y -> r
                // y -> if r then x else x + x + a
                mk_fresh_uncnstr_var_for(f, r);
                if (m_mc)
                    add_def(args[1], m.mk_ite(r, args[0], seq.str.mk_concat(args[0], args[0], seq.str.mk_string(zstring("a")))));
                return true;
            }
            return false;
        case OP_SEQ_IN_RE:
            if (uncnstr(args[0]) && seq.re.is_ground(args[1]) && seq.is_string(args[0]->get_sort())) {
                zstring s1;
                expr* re = args[1];
                if (l_true != rw.some_string_in_re(re, s1))
                    return false;
                zstring s2;
                expr_ref not_re(seq.re.mk_complement(re), m);
                if (l_true != rw.some_string_in_re(not_re, s2))
                    return false;

                mk_fresh_uncnstr_var_for(f, r);
                expr_ref witness1 = expr_ref(seq.str.mk_string(s1), m);
                expr_ref witness2 = expr_ref(seq.str.mk_string(s2), m);
                if (m_mc)
                    add_def(args[0], m.mk_ite(r, witness1, witness2));
                return true;
            }
            return false;
        default:
            verbose_stream() << mk_pp(f, m) << "\n";
            return false;                
            
        }
    }
    
    bool mk_diff(expr* t, expr_ref& r) override {
        if (seq.is_string(t->get_sort())) {
            r = seq.str.mk_concat(t, seq.str.mk_string(zstring("a")));
            return true;
        }
        return false;
    }
    
};


expr_inverter::~expr_inverter() {
    for (auto* v : m_inverters)
        dealloc(v);
}


bool iexpr_inverter::uncnstr(unsigned num, expr * const * args) const {
    for (unsigned i = 0; i < num; i++)
        if (!m_is_var(args[i]))
            return false;
    return true;
}

/**
   \brief Create a fresh variable for abstracting (f args[0] ... args[num-1])
   Return true if a new variable was created, and false if the variable already existed for this
   application. Store the variable in v
*/
void iexpr_inverter::mk_fresh_uncnstr_var_for(sort * s, expr_ref & v) {
    v = m.mk_fresh_const(nullptr, s);
    if (m_mc) 
        m_mc->hide(v);
}

void iexpr_inverter::add_def(expr * v, expr * def) {
    expr_ref _v(v, m);
    expr_ref _d(def, m);
    if (!m_mc)
        return;
    SASSERT(uncnstr(v));
    SASSERT(to_app(v)->get_num_args() == 0);
    m_mc->add(v, def);
}

void iexpr_inverter::add_defs(unsigned num, expr* const* args, expr* u, expr* identity) {
    expr_ref _id(identity, m);    
    if (!m_mc)
        return;
    add_def(args[0], u);
    for (unsigned i = 1; i < num; i++)
        add_def(args[i], identity);
}


expr_inverter::expr_inverter(ast_manager& m): iexpr_inverter(m) {
    auto add = [&](iexpr_inverter* i) {
        m_inverters.setx(i->get_fid(), i, nullptr);
    };
    add(alloc(arith_expr_inverter, m));
    add(alloc(bv_expr_inverter, m));
    add(alloc(array_expr_inverter, m, *this));
    add(alloc(dt_expr_inverter, m));
    add(alloc(basic_expr_inverter, m, *this));
    add(alloc(seq_expr_inverter, m));
    //add(alloc(pb_expr_inverter, m));
}


bool expr_inverter::operator()(func_decl* f, unsigned num, expr* const* args, expr_ref& new_expr) {
    if (num == 0)
        return false;
            
    for (unsigned i = 0; i < num; i++) 
        if (!is_ground(args[i]))
            return false;

    family_id fid = f->get_family_id();
    if (fid == null_family_id)
        return false;

    auto* p = m_inverters.get(fid, nullptr);
    return p && (*p)(f, num, args, new_expr);       
}

bool expr_inverter::mk_diff(expr* t, expr_ref& r) {
    sort * s = t->get_sort();
    if (!m.is_fully_interp(s))
        return false;

    // If the interpreted sort has only one element,
    // then it is unsound to eliminate the unconstrained variable in the equality
    sort_size sz = s->get_num_elements();
    if (sz.is_finite() && sz.size() <= 1)
        return false;

    if (!m_mc) {
        // easy case, model generation is disabled.
        mk_fresh_uncnstr_var_for(s, r);
        return true;
    }

    family_id fid = s->get_family_id();
    auto* p = m_inverters.get(fid, nullptr);
    return p && p->mk_diff(t, r);
}

void expr_inverter::set_is_var(std::function<bool(expr*)>& is_var) {
    for (auto* p : m_inverters)
        if (p)
            p->set_is_var(is_var);
}

void expr_inverter::set_model_converter(generic_model_converter* mc) {
    m_mc = mc;
    for (auto* p : m_inverters)
        if (p)
            p->set_model_converter(mc);
}

void expr_inverter::set_produce_proofs(bool pr) {
    m_produce_proofs = pr;
    for (auto* p : m_inverters)
        if (p)
            p->set_produce_proofs(pr);
}
