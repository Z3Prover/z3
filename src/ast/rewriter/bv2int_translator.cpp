/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv2int_translator
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-27

--*/

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/bv2int_translator.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"

bv2int_translator::bv2int_translator(ast_manager& m, bv2int_translator_trail& ctx) :
    m(m),
    ctx(ctx),
    bv(m),
    a(m),
    m_translate(m),
    m_args(m),
    m_pinned(m),
    m_vars(m),
    m_preds(m)
{}

void bv2int_translator::reset(bool is_plugin) {
    m_vars.reset();
    m_preds.reset();
    for (unsigned i = m_translate.size(); i-- > 0; )
        m_translate[i] = nullptr;
    m_is_plugin = is_plugin;
}


void bv2int_translator::set_translated(expr* e, expr* r) {
    SASSERT(r);
    SASSERT(!is_translated(e));
    m_translate.setx(e->get_id(), r);
    ctx.push_idx(set_vector_idx_trail(m_translate, e->get_id()));
}

void bv2int_translator::internalize_bv(app* e) {
    ensure_translated(e);
    if (m.is_bool(e)) {
        m_preds.push_back(e);
        ctx.push(push_back_vector(m_preds));
    }
}

void bv2int_translator::ensure_translated(expr* e) {
    if (m_translate.get(e->get_id(), nullptr))
        return;
    ptr_vector<expr> todo;
    ast_fast_mark1 visited;
    todo.push_back(e);
    visited.mark(e);
    for (unsigned i = 0; i < todo.size(); ++i) {
        expr* e = todo[i];
        if (!is_app(e))
            continue;
        app* a = to_app(e);
        if (m.is_bool(e) && a->get_family_id() != bv.get_family_id())
            continue;
        for (auto arg : *a)
            if (!visited.is_marked(arg) && !m_translate.get(arg->get_id(), nullptr)) {
                visited.mark(arg);
                todo.push_back(arg);
            }
    }
    std::stable_sort(todo.begin(), todo.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
    for (expr* e : todo)
        translate_expr(e);
}

rational bv2int_translator::bv_size(expr* bv_expr) {
    return rational::power_of_two(bv.get_bv_size(bv_expr->get_sort()));
}

void bv2int_translator::translate_expr(expr* e) {
    if (is_quantifier(e))
        translate_quantifier(to_quantifier(e));
    else if (is_var(e))
        translate_var(to_var(e));
    else {
        app* ap = to_app(e);
        if (m_is_plugin && ap->get_family_id() == basic_family_id && m.is_bool(ap)) {
            set_translated(e, e);
            return;
        }
        m_args.reset();
        for (auto arg : *ap)
            m_args.push_back(translated(arg));

        if (ap->get_family_id() == basic_family_id)
            translate_basic(ap);
        else if (ap->get_family_id() == bv.get_family_id())
            translate_bv(ap);
        else
            translate_app(ap);
    }
}

void bv2int_translator::translate_quantifier(quantifier* q) {
    if (m_is_plugin) {
        set_translated(q, q);
        return;
    }
    if (is_lambda(q))
        throw default_exception("lambdas are not supported in intblaster");
    expr* b = q->get_expr();
    unsigned nd = q->get_num_decls();
    ptr_vector<sort> sorts;
    for (unsigned i = 0; i < nd; ++i) {
        auto s = q->get_decl_sort(i);
        if (bv.is_bv_sort(s)) {
            NOT_IMPLEMENTED_YET();
            sorts.push_back(a.mk_int());
        }
        else
            sorts.push_back(s);
    }
    b = translated(b);
    // TODO if sorts contain integer, then created bounds variables.       
    set_translated(q, m.update_quantifier(q, b));
}

void bv2int_translator::translate_var(var* v) {
    if (bv.is_bv_sort(v->get_sort()))
        set_translated(v, m.mk_var(v->get_idx(), a.mk_int()));
    else
        set_translated(v, v);
}

// Translate functions that are not built-in or bit-vectors.
// Base method uses fresh functions.
// Other method could use bv2int, int2bv axioms and coercions.
// f(args) = bv2int(f(int2bv(args'))
//

void bv2int_translator::translate_app(app* e) {

    if (m_is_plugin && m.is_bool(e)) {
        set_translated(e, e);
        return;
    }

    bool has_bv_sort = bv.is_bv(e);
    func_decl* f = e->get_decl();

    for (unsigned i = 0; i < m_args.size(); ++i)
        if (bv.is_bv(e->get_arg(i)))
            m_args[i] = bv.mk_int2bv(bv.get_bv_size(e->get_arg(i)), m_args.get(i));

    if (has_bv_sort)
        m_vars.push_back(e);
    if (m_is_plugin) {
        expr* r = m.mk_app(f, m_args);
        if (has_bv_sort) {
            ctx.push(push_back_vector(m_vars));
            r = bv.mk_ubv2int(r);
        }
        set_translated(e, r);
        return;
    }
    else if (has_bv_sort) {
        if (f->get_family_id() != null_family_id)
            throw default_exception("conversion for interpreted functions is not supported by intblast solver");
        func_decl* g = nullptr;
        if (!m_new_funs.find(f, g)) {
            g = m.mk_fresh_func_decl(e->get_decl()->get_name(), symbol("bv"), f->get_arity(), f->get_domain(), a.mk_int());
            m_new_funs.insert(f, g);
        }
        f = g;
        m_pinned.push_back(f);
    }
    set_translated(e, m.mk_app(f, m_args));
}

expr_ref bv2int_translator::mk_le(expr* x, expr* y) {
    if (a.is_numeral(y))
        return expr_ref(a.mk_le(x, y), m);
    if (a.is_numeral(x))
        return expr_ref(a.mk_ge(y, x), m);
    return expr_ref(a.mk_le(a.mk_sub(x, y), a.mk_numeral(rational(0), x->get_sort())), m);
}

expr_ref bv2int_translator::mk_lt(expr* x, expr* y) {
    return expr_ref(m.mk_not(mk_le(y, x)), m);
}



void bv2int_translator::translate_bv(app* e) {

    auto bnot = [&](expr* e) {
        return a.mk_sub(a.mk_int(-1), e);
        };

    auto band = [&](expr_ref_vector const& args) {
        expr* r = arg(0);
        for (unsigned i = 1; i < args.size(); ++i)
            r = a.mk_band(bv.get_bv_size(e), r, arg(i));
        return r;
        };

    auto rotate_left = [&](unsigned n) {
        auto sz = bv.get_bv_size(e);
        n = n % sz;
        expr* r = arg(0);
        if (n != 0 && sz != 1) {
            // r[sz - n - 1 : 0] ++ r[sz - 1 : sz - n]
            // r * 2^(sz - n) + (r div 2^n) mod 2^(sz - n)???
            // r * A + (r div B) mod A
            auto N = bv_size(e);
            auto A = rational::power_of_two(sz - n);
            auto B = rational::power_of_two(n);
            auto hi = mul(r, a.mk_int(A));
            auto lo = amod(e, a.mk_idiv(umod(e, 0), a.mk_int(B)), A);
            r = add(hi, lo);
        }
        return r;
        };

    expr* bv_expr = e;
    expr_ref r(m);
    auto const& args = m_args;
    switch (e->get_decl_kind()) {
    case OP_BADD:
        r = a.mk_add(args);
        break;
    case OP_BSUB:
        r = a.mk_sub(args.size(), args.data());
        break;
    case OP_BMUL:
        r = a.mk_mul(args);
        break;
    case OP_ULEQ:
        bv_expr = e->get_arg(0);
        r = mk_le(umod(bv_expr, 0), umod(bv_expr, 1));
        break;
    case OP_UGEQ:
        bv_expr = e->get_arg(0);
        r = mk_ge(umod(bv_expr, 0), umod(bv_expr, 1));
        break;
    case OP_ULT:
        bv_expr = e->get_arg(0);
        r = mk_lt(umod(bv_expr, 0), umod(bv_expr, 1));
        break;
    case OP_UGT:
        bv_expr = e->get_arg(0);
        r = mk_gt(umod(bv_expr, 0), umod(bv_expr, 1));
        break;
    case OP_SLEQ:
        bv_expr = e->get_arg(0);
        r = mk_le(smod(bv_expr, 0), smod(bv_expr, 1));
        break;
    case OP_SGEQ:
        bv_expr = e->get_arg(0);
        r = mk_ge(smod(bv_expr, 0), smod(bv_expr, 1));
        break;
    case OP_SLT:
        bv_expr = e->get_arg(0);
        r = mk_lt(smod(bv_expr, 0), smod(bv_expr, 1));
        break;
    case OP_SGT:
        bv_expr = e->get_arg(0);
        r = mk_gt(smod(bv_expr, 0), smod(bv_expr, 1));
        break;
    case OP_BNEG:
        r = a.mk_uminus(arg(0));
        break;
    case OP_CONCAT: {
        unsigned sz = 0;
        expr_ref new_arg(m);
        for (unsigned i = args.size(); i-- > 0;) {
            expr* old_arg = e->get_arg(i);
            new_arg = umod(old_arg, i);
            if (sz > 0) {
                new_arg = mul(new_arg, a.mk_int(rational::power_of_two(sz)));
                r = add(r, new_arg);
            }
            else
                r = new_arg;
            sz += bv.get_bv_size(old_arg->get_sort());
        }
        break;
    }
    case OP_EXTRACT: {
        unsigned lo, hi;
        expr* old_arg;
        VERIFY(bv.is_extract(e, lo, hi, old_arg));
        r = arg(0);
        if (lo > 0)
            r = a.mk_idiv(r, a.mk_int(rational::power_of_two(lo)));
        break;
    }
    case OP_BV_NUM: {
        rational val;
        unsigned sz;
        VERIFY(bv.is_numeral(e, val, sz));
        r = a.mk_int(val);
        break;
    }
    case OP_BUREM:
    case OP_BUREM_I: {
        expr* x = umod(e, 0), * y = umod(e, 1);
        r = if_eq(y, 0, x, a.mk_mod(x, y));
        break;
    }
    case OP_BUDIV:
    case OP_BUDIV_I: {
        expr* x = umod(e, 0), * y = umod(e, 1);
        r = if_eq(y, 0, a.mk_int(-1), a.mk_idiv(x, y));
        break;
    }
    case OP_BUMUL_NO_OVFL: {
        bv_expr = e->get_arg(0);
        r = mk_lt(mul(umod(bv_expr, 0), umod(bv_expr, 1)), a.mk_int(bv_size(bv_expr)));
        break;
    }
    case OP_BSHL: {
        if (!a.is_numeral(arg(0)) && !a.is_numeral(arg(1)))
            r = a.mk_shl(bv.get_bv_size(e), arg(0), arg(1));
        else {
            expr* x = arg(0), * y = umod(e, 1);
            r = a.mk_int(0);
            for (unsigned i = 0; i < bv.get_bv_size(e); ++i)
                r = if_eq(y, i, mul(x, a.mk_int(rational::power_of_two(i))), r);
        }
        break;
    }
    case OP_BNOT:
        r = bnot(arg(0));
        break;
    case OP_BLSHR:
        if (!a.is_numeral(arg(0)) && !a.is_numeral(arg(1)))
            r = a.mk_lshr(bv.get_bv_size(e), arg(0), arg(1));
        else {
            expr* x = arg(0), * y = umod(e, 1);
            r = a.mk_int(0);
            IF_VERBOSE(4, verbose_stream() << "lshr " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
            for (unsigned i = 0; i < bv.get_bv_size(e); ++i)
                r = if_eq(y, i, a.mk_idiv(x, a.mk_int(rational::power_of_two(i))), r);
        }
        break;
    case OP_BASHR:
        if (!a.is_numeral(arg(1)))
            r = a.mk_ashr(bv.get_bv_size(e), arg(0), arg(1));
        else {

            //
            // ashr(x, y)
            // if y = k & x >= 0 -> x / 2^k   
            // if y = k & x < 0  -> (x / 2^k) - 2^{N-k}
            //
            unsigned sz = bv.get_bv_size(e);
            rational N = bv_size(e);
            expr* x = umod(e, 0), * y = umod(e, 1);
            expr* signx = a.mk_ge(x, a.mk_int(N / 2));
            r = m.mk_ite(signx, a.mk_int(-1), a.mk_int(0));
            IF_VERBOSE(4, verbose_stream() << "ashr " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
            for (unsigned i = 0; i < sz; ++i) {
                expr* d = a.mk_idiv(x, a.mk_int(rational::power_of_two(i)));
                r = if_eq(y, i,
                    m.mk_ite(signx, add(d, a.mk_int(-rational::power_of_two(sz - i))), d),
                    r);
            }
        }
        break;
    case OP_BOR:
        // p | q := (p + q) - band(p, q)
        IF_VERBOSE(4, verbose_stream() << "bor " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
        r = arg(0);
        for (unsigned i = 1; i < args.size(); ++i)
            r = a.mk_sub(add(r, arg(i)), a.mk_band(bv.get_bv_size(e), r, arg(i)));
        break;
    case OP_BNAND:
        r = bnot(band(args));
        break;
    case OP_BAND:
        IF_VERBOSE(4, verbose_stream() << "band " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
        r = band(args);
        break;
    case OP_BXNOR:
    case OP_BXOR: {
        // p ^ q := (p + q) - 2*band(p, q);
        unsigned sz = bv.get_bv_size(e);
        IF_VERBOSE(4, verbose_stream() << "bxor " << bv.get_bv_size(e) << "\n");
        r = arg(0);
        for (unsigned i = 1; i < args.size(); ++i) {
            expr* q = arg(i);
            r = a.mk_sub(add(r, q), mul(a.mk_int(2), a.mk_band(sz, r, q)));
        }
        if (e->get_decl_kind() == OP_BXNOR)
            r = bnot(r);
        break;
    }
    case OP_ZERO_EXT:
        bv_expr = e->get_arg(0);
        r = umod(bv_expr, 0);
        SASSERT(bv.get_bv_size(e) >= bv.get_bv_size(bv_expr));
        break;
    case OP_SIGN_EXT: {
        bv_expr = e->get_arg(0);
        r = umod(bv_expr, 0);
        SASSERT(bv.get_bv_size(e) >= bv.get_bv_size(bv_expr));
        unsigned arg_sz = bv.get_bv_size(bv_expr);
        //unsigned sz = bv.get_bv_size(e);
        // rational N = rational::power_of_two(sz);
        rational M = rational::power_of_two(arg_sz);
        expr* signbit = a.mk_ge(r, a.mk_int(M / 2));
        r = m.mk_ite(signbit, a.mk_sub(r, a.mk_int(M)), r);
        break;
    }
    case OP_INT2BV:
        m_int2bv.push_back(e);
        ctx.push(push_back_vector(m_int2bv));
        r = arg(0);
        break;
    case OP_UBV2INT:
        m_bv2int.push_back(e);
        ctx.push(push_back_vector(m_bv2int));
        r = umod(e->get_arg(0), 0);
        break;
    case OP_BCOMP:
        bv_expr = e->get_arg(0);
        r = m.mk_ite(m.mk_eq(umod(bv_expr, 0), umod(bv_expr, 1)), a.mk_int(1), a.mk_int(0));
        break;
    case OP_BSMOD_I:
    case OP_BSMOD: {
        expr* x = umod(e, 0), * y = umod(e, 1);
        rational N = bv_size(e);
        expr* signx = a.mk_ge(x, a.mk_int(N / 2));
        expr* signy = a.mk_ge(y, a.mk_int(N / 2));
        expr* u = a.mk_mod(x, y);
        // u = 0 ->  0
        // y = 0 ->  x
        // x < 0, y < 0 ->  -u
        // x < 0, y >= 0 ->  y - u
        // x >= 0, y < 0 ->  y + u
        // x >= 0, y >= 0 ->  u
        r = a.mk_uminus(u);
        r = m.mk_ite(m.mk_and(m.mk_not(signx), signy), add(u, y), r);
        r = m.mk_ite(m.mk_and(signx, m.mk_not(signy)), a.mk_sub(y, u), r);
        r = m.mk_ite(m.mk_and(m.mk_not(signx), m.mk_not(signy)), u, r);
        r = if_eq(u, 0, a.mk_int(0), r);
        r = if_eq(y, 0, x, r);
        break;
    }
    case OP_BSDIV_I:
    case OP_BSDIV: {
        // d = udiv(abs(x), abs(y))
        // y = 0, x > 0 -> 1
        // y = 0, x <= 0 -> -1
        // x = 0, y != 0 -> 0
        // x > 0, y < 0 -> -d
        // x < 0, y > 0 -> -d
        // x > 0, y > 0 -> d
        // x < 0, y < 0 -> d
        expr* x = umod(e, 0), * y = umod(e, 1);
        rational N = bv_size(e);
        expr* signx = a.mk_ge(x, a.mk_int(N / 2));
        expr* signy = a.mk_ge(y, a.mk_int(N / 2));
        x = m.mk_ite(signx, a.mk_sub(a.mk_int(N), x), x);
        y = m.mk_ite(signy, a.mk_sub(a.mk_int(N), y), y);
        expr* d = a.mk_idiv(x, y);
        r = m.mk_ite(m.mk_iff(signx, signy), d, a.mk_uminus(d));
        r = if_eq(y, 0, m.mk_ite(signx, a.mk_int(1), a.mk_int(-1)), r);
        break;
    }
    case OP_BSREM_I:
    case OP_BSREM: {
        // y = 0 -> x
        // else x - sdiv(x, y) * y
        expr* x = umod(e, 0), * y = umod(e, 1);
        rational N = bv_size(e);
        expr* signx = a.mk_ge(x, a.mk_int(N / 2));
        expr* signy = a.mk_ge(y, a.mk_int(N / 2));
        expr* absx = m.mk_ite(signx, a.mk_sub(a.mk_int(N), x), x);
        expr* absy = m.mk_ite(signy, a.mk_sub(a.mk_int(N), y), y);
        expr* d = a.mk_idiv(absx, absy);
        d = m.mk_ite(m.mk_iff(signx, signy), d, a.mk_uminus(d));
        r = a.mk_sub(x, mul(d, y));
        r = if_eq(y, 0, x, r);
        break;
    }
    case OP_ROTATE_LEFT: {
        auto n = e->get_parameter(0).get_int();
        r = rotate_left(n);
        break;
    }
    case OP_ROTATE_RIGHT: {
        unsigned sz = bv.get_bv_size(e);
        auto n = e->get_parameter(0).get_int();
        r = rotate_left(sz - n);
        break;
    }
    case OP_EXT_ROTATE_LEFT: {
        unsigned sz = bv.get_bv_size(e);
        expr* y = umod(e, 1);
        r = a.mk_int(0);
        for (unsigned i = 0; i < sz; ++i)
            r = if_eq(y, i, rotate_left(i), r);
        break;
    }
    case OP_EXT_ROTATE_RIGHT: {
        unsigned sz = bv.get_bv_size(e);
        expr* y = umod(e, 1);
        r = a.mk_int(0);
        for (unsigned i = 0; i < sz; ++i)
            r = if_eq(y, i, rotate_left(sz - i), r);
        break;
    }
    case OP_REPEAT: {
        unsigned n = e->get_parameter(0).get_int();
        expr* x = umod(e->get_arg(0), 0);
        r = x;
        rational N = bv_size(e->get_arg(0));
        rational N0 = N;
        for (unsigned i = 1; i < n; ++i)
            r = add(mul(a.mk_int(N), x), r), N *= N0;
        break;
    }
    case OP_BREDOR: {
        r = umod(e->get_arg(0), 0);
        r = m.mk_not(m.mk_eq(r, a.mk_int(0)));
        break;
    }
    case OP_BREDAND: {
        rational N = bv_size(e->get_arg(0));
        r = umod(e->get_arg(0), 0);
        r = m.mk_not(m.mk_eq(r, a.mk_int(N - 1)));
        break;
    }
    default:
        verbose_stream() << mk_pp(e, m) << "\n";
        NOT_IMPLEMENTED_YET();
    }
    set_translated(e, r);
}

expr_ref bv2int_translator::if_eq(expr* n, unsigned k, expr* th, expr* el) {
    rational r;
    expr_ref _th(th, m), _el(el, m);
    if (bv.is_numeral(n, r)) {
        if (r == k)
            return expr_ref(th, m);
        else
            return expr_ref(el, m);
    }
    return expr_ref(m.mk_ite(m.mk_eq(n, a.mk_int(k)), th, el), m);
}

void bv2int_translator::translate_basic(app* e) {
    if (m.is_eq(e)) {
        bool has_bv_arg = any_of(*e, [&](expr* arg) { return bv.is_bv(arg); });
        if (has_bv_arg) {
            expr* bv_expr = e->get_arg(0);
            rational N = rational::power_of_two(bv.get_bv_size(bv_expr));
            if (a.is_numeral(arg(0)) || a.is_numeral(arg(1)) ||
                is_bounded(arg(0), N) || is_bounded(arg(1), N)) {
                set_translated(e, m.mk_eq(umod(bv_expr, 0), umod(bv_expr, 1)));
            }
            else {
                m_args[0] = a.mk_sub(arg(0), arg(1));
                set_translated(e, m.mk_eq(umod(bv_expr, 0), a.mk_int(0)));
            }
        }
        else
            set_translated(e, m.mk_eq(arg(0), arg(1)));
    }
    else if (m.is_ite(e))
        set_translated(e, m.mk_ite(arg(0), arg(1), arg(2)));
    else if (m_is_plugin)
        set_translated(e, e);
    else
        set_translated(e, m.mk_app(e->get_decl(), m_args));
}

bool bv2int_translator::is_bounded(expr* x, rational const& N) {
    return any_of(m_vars, [&](expr* v) {
        return is_translated(v) && translated(v) == x && bv_size(v) <= N;
        });
}

bool bv2int_translator::is_non_negative(expr* bv_expr, expr* e) {
    auto N = rational::power_of_two(bv.get_bv_size(bv_expr));
    rational r;
    if (a.is_numeral(e, r))
        return r >= 0;
    if (is_bounded(e, N))
        return true;
    expr* x = nullptr, * y = nullptr;
    if (a.is_mul(e, x, y))
        return is_non_negative(bv_expr, x) && is_non_negative(bv_expr, y);
    if (a.is_add(e, x, y))
        return is_non_negative(bv_expr, x) && is_non_negative(bv_expr, y);
    return false;
}

expr* bv2int_translator::umod(expr* bv_expr, unsigned i) {
    expr* x = arg(i);
    rational N = bv_size(bv_expr);
    return amod(bv_expr, x, N);
}

expr* bv2int_translator::smod(expr* bv_expr, unsigned i) {
    expr* x = arg(i);
    auto N = bv_size(bv_expr);
    auto shift = N / 2;
    rational r;
    if (a.is_numeral(x, r))
        return a.mk_int(mod(r + shift, N));
    return amod(bv_expr, add(x, a.mk_int(shift)), N);
}

expr_ref bv2int_translator::mul(expr* x, expr* y) {
    expr_ref _x(x, m), _y(y, m);
    if (a.is_zero(x))
        return _x;
    if (a.is_zero(y))
        return _y;
    if (a.is_one(x))
        return _y;
    if (a.is_one(y))
        return _x;
    rational v1, v2;
    if (a.is_numeral(x, v1) && a.is_numeral(y, v2))
        return expr_ref(a.mk_int(v1 * v2), m);
    _x = a.mk_mul(x, y);
    return _x;
}

expr_ref bv2int_translator::add(expr* x, expr* y) {
    expr_ref _x(x, m), _y(y, m);
    if (a.is_zero(x))
        return _y;
    if (a.is_zero(y))
        return _x;
    rational v1, v2;
    if (a.is_numeral(x, v1) && a.is_numeral(y, v2))
        return expr_ref(a.mk_int(v1 + v2), m);
    _x = a.mk_add(x, y);
    return _x;
}

/*
* Perform simplifications that are claimed sound when the bit-vector interpretations of
* mod/div always guard the mod and dividend to be non-zero.
* Potentially shady area is for arithmetic expressions created by int2bv.
* They will be guarded by a modulus which does not disappear.
*/
expr* bv2int_translator::amod(expr* bv_expr, expr* x, rational const& N) {
    rational v;
    expr* r = nullptr, * c = nullptr, * t = nullptr, * e = nullptr;
    if (m.is_ite(x, c, t, e))
        r = m.mk_ite(c, amod(bv_expr, t, N), amod(bv_expr, e, N));
    else if (a.is_idiv(x, t, e) && a.is_numeral(t, v) && 0 <= v && v < N && is_non_negative(bv_expr, e))
        r = x;
    else if (a.is_mod(x, t, e) && a.is_numeral(t, v) && 0 <= v && v < N)
        r = x;
    else if (a.is_numeral(x, v))
        r = a.mk_int(mod(v, N));
    else if (is_bounded(x, N))
        r = x;
    else
        r = a.mk_mod(x, a.mk_int(N));
    return r;
}

void bv2int_translator::translate_eq(expr* e) {
    expr* x = nullptr, * y = nullptr;
    VERIFY(m.is_eq(e, x, y));
    SASSERT(bv.is_bv(x));
    if (!is_translated(e)) {
        ensure_translated(x);
        ensure_translated(y);
        m_args.reset();
        m_args.push_back(a.mk_sub(translated(x), translated(y)));
        set_translated(e, m.mk_eq(umod(x, 0), a.mk_int(0)));
    }
    m_preds.push_back(e);
    TRACE("bv", tout << mk_pp(e, m) << " " << mk_pp(translated(e), m) << "\n");
    ctx.push(push_back_vector(m_preds));

}
