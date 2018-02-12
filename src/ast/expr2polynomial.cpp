/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr2polynomial.cpp

Abstract:

    Translator from Z3 expressions into multivariate polynomials (and back).


Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#include "ast/expr2polynomial.h"
#include "ast/expr2var.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "util/z3_exception.h"
#include "util/cooperate.h"
#include "util/common_msgs.h"

struct expr2polynomial::imp {
    struct frame {
        app *     m_curr;
        unsigned  m_idx;
        frame():m_curr(nullptr), m_idx(0) {}
        frame(app * t):m_curr(t), m_idx(0) {}
    };

    expr2polynomial &                  m_wrapper;
    ast_manager &                      m_am;
    arith_util                         m_autil;
    polynomial::manager &              m_pm;
    expr2var *                         m_expr2var;
    bool                               m_expr2var_owner;
    expr_ref_vector                    m_var2expr;

    obj_map<expr, unsigned>            m_cache;
    expr_ref_vector                    m_cached_domain;
    polynomial::polynomial_ref_vector  m_cached_polynomials;
    polynomial::scoped_numeral_vector  m_cached_denominators;

    svector<frame>                     m_frame_stack;
    polynomial::polynomial_ref_vector  m_presult_stack;
    polynomial::scoped_numeral_vector  m_dresult_stack;

    bool                               m_use_var_idxs;

    volatile bool                      m_cancel;

    imp(expr2polynomial & w, ast_manager & am, polynomial::manager & pm, expr2var * e2v, bool use_var_idxs):
        m_wrapper(w),
        m_am(am),
        m_autil(am),
        m_pm(pm),
        m_expr2var(e2v == nullptr && !use_var_idxs ? alloc(expr2var, am) : e2v),
        m_expr2var_owner(e2v == nullptr && !use_var_idxs),
        m_var2expr(am),
        m_cached_domain(am),
        m_cached_polynomials(pm),
        m_cached_denominators(pm.m()),
        m_presult_stack(pm),
        m_dresult_stack(pm.m()),
        m_use_var_idxs(use_var_idxs),
        m_cancel(false) {
    }

    ~imp() {
        if (m_expr2var_owner)
            dealloc(m_expr2var);
    }

    ast_manager & m() { return m_am; }
    polynomial::manager & pm() { return m_pm; }
    polynomial::numeral_manager & nm() { return pm().m(); }

    void reset() {
        m_frame_stack.reset();
        m_presult_stack.reset();
        m_dresult_stack.reset();
    }

    void reset_cache() {
        m_cache.reset();
        m_cached_domain.reset();
        m_cached_polynomials.reset();
        m_cached_denominators.reset();
    }

    void checkpoint() {
        if (m_cancel)
            throw default_exception(Z3_CANCELED_MSG);
        cooperate("expr2polynomial");
    }

    void throw_not_polynomial() {
        throw default_exception("the given expression is not a polynomial");
    }

    void throw_no_int_var() {
        throw default_exception("integer variables are not allowed in the given polynomial");
    }

    void push_frame(app * t) {
        m_frame_stack.push_back(frame(t));
    }

    void cache_result(expr * t) {
        SASSERT(!m_cache.contains(t));
        SASSERT(m_cached_denominators.size() == m_cached_polynomials.size());
        SASSERT(m_cached_denominators.size() == m_cached_domain.size());
        if (t->get_ref_count() <= 1)
            return;
        unsigned idx = m_cached_polynomials.size();
        m_cache.insert(t, idx);
        m_cached_domain.push_back(t);
        m_cached_polynomials.push_back(m_presult_stack.back());
        m_cached_denominators.push_back(m_dresult_stack.back());
    }

    bool is_cached(expr * t) {
        return t->get_ref_count() > 1 && m_cache.contains(t);
    }

    bool is_int_real(expr * t) {
        return m_autil.is_int_real(t);
    }

    void store_result(expr * t, polynomial::polynomial * p, polynomial::numeral & d) {
        m_presult_stack.push_back(p);
        m_dresult_stack.push_back(d);
        cache_result(t);
    }

    void store_var_poly(expr * t) {
        polynomial::var x;
        if (m_use_var_idxs) {
            SASSERT(::is_var(t));
            if (m_autil.is_int(t))
                throw_no_int_var();
            unsigned idx = to_var(t)->get_idx();
            while (idx >= m_pm.num_vars())
                m_pm.mk_var();
            x = static_cast<polynomial::var>(idx);
        }
        else {
            x = m_expr2var->to_var(t);
            if (x == UINT_MAX) {
                bool is_int = m_autil.is_int(t);
                x = m_wrapper.mk_var(is_int);
                m_expr2var->insert(t, x);
                if (x >= m_var2expr.size())
                    m_var2expr.resize(x+1, nullptr);
                m_var2expr.set(x, t);
            }
        }
        polynomial::numeral one(1);
        store_result(t, pm().mk_polynomial(x), one);
    }

    void store_const_poly(app * n) {
        rational val;
        VERIFY(m_autil.is_numeral(n, val));
        polynomial::scoped_numeral d(nm());
        d = val.to_mpq().denominator();
        store_result(n, pm().mk_const(numerator(val)), d);
    }

    bool visit_arith_app(app * t) {
        switch (t->get_decl_kind()) {
        case OP_NUM:
            store_const_poly(t);
            return true;
        case OP_ADD: case OP_SUB: case OP_MUL: case OP_UMINUS: case OP_TO_REAL:
            push_frame(t);
            return false;
        case OP_POWER: {
            rational k;
            SASSERT(t->get_num_args() == 2);
            if (!m_autil.is_numeral(t->get_arg(1), k) || !k.is_int() || !k.is_unsigned()) {
                if (m_use_var_idxs)
                    throw_not_polynomial();
                else
                    store_var_poly(t);
                return true;
            }
            push_frame(t);
            return false;
        }
        default:
            // can't handle operator
            if (m_use_var_idxs)
                throw_not_polynomial();
            store_var_poly(t);
            return true;
        }
    }

    bool visit(expr * t) {
        SASSERT(is_int_real(t));
        if (is_cached(t)) {
            unsigned idx = m_cache.find(t);
            m_presult_stack.push_back(m_cached_polynomials.get(idx));
            m_dresult_stack.push_back(m_cached_denominators.get(idx));
            return true;
        }

        SASSERT(!is_quantifier(t));
        if (::is_var(t)) {
            store_var_poly(t);
            return true;
        }

        SASSERT(is_app(t));
        if (!m_autil.is_arith_expr(t)) {
            if (m_use_var_idxs)
                throw_not_polynomial();
            store_var_poly(t);
            return true;
        }

        return visit_arith_app(to_app(t));
    }

    void pop(unsigned num_args) {
        SASSERT(m_presult_stack.size() == m_dresult_stack.size());
        SASSERT(m_presult_stack.size() >= num_args);
        m_presult_stack.shrink(m_presult_stack.size() - num_args);
        m_dresult_stack.shrink(m_dresult_stack.size() - num_args);
    }

    polynomial::polynomial * const * polynomial_args(unsigned num_args) {
        SASSERT(m_presult_stack.size() >= num_args);
        return m_presult_stack.c_ptr() + m_presult_stack.size() - num_args;
    }

    polynomial::numeral const * denominator_args(unsigned num_args) {
        SASSERT(m_dresult_stack.size() >= num_args);
        return m_dresult_stack.c_ptr() + m_dresult_stack.size() - num_args;
    }

    template<bool is_add>
    void process_add_sub(app * t) {
        SASSERT(t->get_num_args() <= m_presult_stack.size());
        unsigned num_args = t->get_num_args();
        polynomial::polynomial * const * p_args = polynomial_args(num_args);
        polynomial::numeral const * d_args = denominator_args(num_args);
        polynomial::polynomial_ref p(pm());
        polynomial::polynomial_ref p_aux(pm());
        polynomial::scoped_numeral d(nm());
        polynomial::scoped_numeral d_aux(nm());
        d = 1;
        for (unsigned i = 0; i < num_args; i++) {
            nm().lcm(d, d_args[i], d);
        }
        p = pm().mk_zero();
        for (unsigned i = 0; i < num_args; i++) {
            checkpoint();
            nm().div(d, d_args[i], d_aux);
            p_aux = pm().mul(d_aux, p_args[i]);
            if (i == 0)
                p = p_aux;
            else if (is_add)
                p = pm().add(p, p_aux);
            else
                p = pm().sub(p, p_aux);
        }
        pop(num_args);
        store_result(t, p.get(), d.get());
    }

    void process_add(app * t) {
        process_add_sub<true>(t);
    }

    void process_sub(app * t) {
        process_add_sub<false>(t);
    }

    void process_mul(app * t) {
        SASSERT(t->get_num_args() <= m_presult_stack.size());
        unsigned num_args = t->get_num_args();
        polynomial::polynomial * const * p_args = polynomial_args(num_args);
        polynomial::numeral const * d_args = denominator_args(num_args);
        polynomial::polynomial_ref p(pm());
        polynomial::scoped_numeral d(nm());
        p = pm().mk_const(rational(1));
        d = 1;
        for (unsigned i = 0; i < num_args; i++) {
            checkpoint();
            p = pm().mul(p, p_args[i]);
            d = d * d_args[i];
        }
        pop(num_args);
        store_result(t, p.get(), d.get());
    }

    void process_uminus(app * t) {
        SASSERT(t->get_num_args() <= m_presult_stack.size());
        polynomial::polynomial_ref neg_p(pm());
        neg_p = pm().neg(m_presult_stack.back());
        m_presult_stack.pop_back();
        m_presult_stack.push_back(neg_p);
        cache_result(t);
    }

    void process_power(app * t) {
        SASSERT(t->get_num_args() <= m_presult_stack.size());
        rational _k;
        VERIFY(m_autil.is_numeral(t->get_arg(1), _k));
        SASSERT(_k.is_int() && _k.is_unsigned());
        unsigned k = _k.get_unsigned();
        polynomial::polynomial_ref p(pm());
        polynomial::scoped_numeral d(nm());
        unsigned num_args = t->get_num_args();
        polynomial::polynomial * const * p_args = polynomial_args(num_args);
        polynomial::numeral const * d_args = denominator_args(num_args);
        pm().pw(p_args[0], k, p);
        nm().power(d_args[0], k, d);
        pop(num_args);
        store_result(t, p.get(), d.get());
    }

    void process_to_real(app * t) {
        // do nothing
        cache_result(t);
    }

    void process_app(app * t) {
        SASSERT(m_presult_stack.size() == m_dresult_stack.size());

        switch (t->get_decl_kind()) {
        case OP_ADD:
            process_add(t);
            return;
        case OP_SUB:
            process_sub(t);
            return;
        case OP_MUL:
            process_mul(t);
            return;
        case OP_POWER:
            process_power(t);
            return;
        case OP_UMINUS:
            process_uminus(t);
            return;
        case OP_TO_REAL:
            process_to_real(t);
            return;
        default:
            UNREACHABLE();
        }
    }

    bool to_polynomial(expr * t, polynomial::polynomial_ref & p, polynomial::scoped_numeral & d) {
        if (!is_int_real(t))
            return false;
        reset();
        if (!visit(t)) {
            while (!m_frame_stack.empty()) {
            begin_loop:
                checkpoint();
                frame & fr = m_frame_stack.back();
                app * a = fr.m_curr;
                TRACE("expr2polynomial", tout << "processing: " << fr.m_idx << "\n" << mk_ismt2_pp(a, m()) << "\n";);
                unsigned num_args = a->get_num_args();
                while (fr.m_idx < num_args) {
                    expr * arg = a->get_arg(fr.m_idx);
                    fr.m_idx++;
                    if (!visit(arg))
                        goto begin_loop;
                }
                process_app(a);
                m_frame_stack.pop_back();
            }
        }
        p = m_presult_stack.back();
        d = m_dresult_stack.back();
        reset();
        return true;
    }

    bool is_int_poly(polynomial::polynomial_ref const & p) {
        unsigned sz = size(p);
        for (unsigned i = 0; i < sz; i++) {
            polynomial::monomial * m = pm().get_monomial(p, i);
            unsigned msz = pm().size(m);
            for (unsigned j = 0; j < msz; j++) {
                polynomial::var x = pm().get_var(m, j);
                if (!m_wrapper.is_int(x))
                    return false;
            }
        }
        return true;
    }

    void to_expr(polynomial::polynomial_ref const & p, bool use_power, expr_ref & r) {
        expr_ref_buffer args(m());
        expr_ref_buffer margs(m());
        unsigned sz = size(p);
        bool is_int = is_int_poly(p);

        for (unsigned i = 0; i < sz; i++) {
            margs.reset();
            polynomial::monomial * _m = pm().get_monomial(p, i);
            polynomial::numeral const & a = pm().coeff(p, i);
            if (!nm().is_one(a)) {
                margs.push_back(m_autil.mk_numeral(rational(a), is_int));
            }
            unsigned msz = pm().size(_m);
            for (unsigned j = 0; j < msz; j++) {
                polynomial::var x = pm().get_var(_m, j);
                expr * t;
                if (m_use_var_idxs) {
                    t = m().mk_var(x, m_autil.mk_real());
                }
                else {
                    t = m_var2expr.get(x);
                    if (m_wrapper.is_int(x) && !is_int) {
                        t = m_autil.mk_to_real(t);
                    }
                }
                unsigned d = pm().degree(_m, j);
                if (use_power && d > 1) {
                    margs.push_back(m_autil.mk_power(t, m_autil.mk_numeral(rational(d), is_int)));
                }
                else {
                    for (unsigned k = 0; k < d; k++)
                        margs.push_back(t);
                }
            }
            if (margs.size() == 0) {
                args.push_back(m_autil.mk_numeral(rational(1), is_int));
            }
            else if (margs.size() == 1) {
                args.push_back(margs[0]);
            }
            else {
                args.push_back(m_autil.mk_mul(margs.size(), margs.c_ptr()));
            }
        }

        if (args.size() == 0) {
            r = m_autil.mk_numeral(rational(0), is_int);
        }
        else if (args.size() == 1) {
            r = args[0];
        }
        else {
            r = m_autil.mk_add(args.size(), args.c_ptr());
        }
    }

    void set_cancel(bool f) {
        m_cancel = f;
    }
};

expr2polynomial::expr2polynomial(ast_manager & am, polynomial::manager & pm, expr2var * e2v, bool use_var_idxs) {
    m_imp = alloc(imp, *this, am, pm, e2v, use_var_idxs);
}

expr2polynomial::~expr2polynomial() {
    dealloc(m_imp);
}

ast_manager & expr2polynomial::m() const {
    return m_imp->m_am;
}

polynomial::manager & expr2polynomial::pm() const {
    return m_imp->m_pm;
}

bool expr2polynomial::to_polynomial(expr * t, polynomial::polynomial_ref & p, polynomial::scoped_numeral & d) {
    return m_imp->to_polynomial(t, p, d);
}

void expr2polynomial::to_expr(polynomial::polynomial_ref const & p, bool use_power, expr_ref & r) {
    m_imp->to_expr(p, use_power, r);
}

bool expr2polynomial::is_var(expr * t) const {
    SASSERT(!m_imp->m_use_var_idxs);
    return m_imp->m_expr2var->is_var(t);
}

expr2var const & expr2polynomial::get_mapping() const {
    SASSERT(!m_imp->m_use_var_idxs);
    return *(m_imp->m_expr2var);
}

void expr2polynomial::set_cancel(bool f) {
    m_imp->set_cancel(f);
}

default_expr2polynomial::default_expr2polynomial(ast_manager & am, polynomial::manager & pm):
    expr2polynomial(am, pm, nullptr) {
}

default_expr2polynomial::~default_expr2polynomial() {
}

bool default_expr2polynomial::is_int(polynomial::var x) const {
    return m_is_int[x];
}

polynomial::var default_expr2polynomial::mk_var(bool is_int) {
    polynomial::var x = pm().mk_var();
    m_is_int.reserve(x+1, false);
    m_is_int[x] = is_int;
    return x;
}
