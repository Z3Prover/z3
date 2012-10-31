/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    expr2subpaving.cpp

Abstract:

    Translator from Z3 expressions into generic subpaving data-structure.
    
    
Author:

    Leonardo (leonardo) 2012-08-08

Notes:

--*/
#include"expr2subpaving.h"
#include"expr2var.h"
#include"ref_util.h"
#include"z3_exception.h"
#include"cooperate.h"
#include"arith_decl_plugin.h"
#include"scoped_numeral_buffer.h"

struct expr2subpaving::imp {
    struct frame {
        app *     m_curr;
        unsigned  m_idx;
        frame():m_curr(0), m_idx(0) {}
        frame(app * t):m_curr(t), m_idx(0) {}
    };

    ast_manager &                      m_manager;
    subpaving::context &               m_subpaving;
    unsynch_mpq_manager &              m_qm;
    arith_util                         m_autil;
    expr2var *                         m_expr2var;
    bool                               m_expr2var_owner;

    expr_ref_vector                    m_var2expr;

    typedef svector<subpaving::var>    var_vector;
    
    obj_map<expr, unsigned>            m_cache;
    var_vector                         m_cached_vars; 
    scoped_mpz_vector                  m_cached_numerators;
    scoped_mpz_vector                  m_cached_denominators;

    obj_map<expr, subpaving::ineq*>    m_lit_cache;

    volatile bool                      m_cancel;

    imp(ast_manager & m, subpaving::context & s, expr2var * e2v):
        m_manager(m),
        m_subpaving(s),
        m_qm(s.qm()),
        m_autil(m),
        m_var2expr(m),
        m_cached_numerators(m_qm),
        m_cached_denominators(m_qm) {

        if (e2v == 0) {
            m_expr2var       = alloc(expr2var, m);
            m_expr2var_owner = true;
        }
        else {
            m_expr2var       = e2v;
            m_expr2var_owner = false;
        }
        
        m_cancel = false;
    }
    
    ~imp() {
        reset_cache();
        if (m_expr2var_owner)
            dealloc(m_expr2var);
    }
    
    ast_manager & m() { return m_manager; }
    
    subpaving::context & s() { return m_subpaving; }

    unsynch_mpq_manager & qm() const { return m_qm; }

    void reset_cache() {
        dec_ref_map_keys(m(), m_cache);
        m_cached_vars.reset();
        m_cached_numerators.reset();
        m_cached_denominators.reset();
        dec_ref_map_key_values(m(), s(), m_lit_cache);
    }

    void checkpoint() {
        if (m_cancel)
            throw default_exception("canceled");
        cooperate("expr2subpaving");
    }

    subpaving::var mk_var_for(expr * t) {
        SASSERT(!m_autil.is_numeral(t));
        subpaving::var x = m_expr2var->to_var(t);
        if (x == subpaving::null_var) {
            bool is_int = m_autil.is_int(t);
            x = s().mk_var(is_int);
            m_expr2var->insert(t, x);
            if (x >= m_var2expr.size())
                m_var2expr.resize(x+1, 0);
            m_var2expr.set(x, t);
        }
        return x;
    }
    
    void found_non_simplified() {
        throw default_exception("you must apply simplifier before internalizing expressions into the subpaving module.");
    }

    bool is_cached(expr * t) {
        return t->get_ref_count() > 1 && m_cache.contains(t);
    }

    bool is_int_real(expr * t) {
        return m_autil.is_int_real(t);
    }

    void cache_result(expr * t, subpaving::var x, mpz const & n, mpz const & d) {
        SASSERT(!m_cache.contains(t));
        SASSERT(m_cached_numerators.size()   == m_cached_vars.size());
        SASSERT(m_cached_denominators.size() == m_cached_vars.size());
        if (t->get_ref_count() <= 1) 
            return;
        unsigned idx = m_cached_vars.size();
        m_cache.insert(t, idx);
        m().inc_ref(t);
        m_cached_vars.push_back(x);
        m_cached_numerators.push_back(n);
        m_cached_denominators.push_back(d);
    }

    subpaving::var process_num(app * t, unsigned depth, mpz & n, mpz & d) {
        rational k;
        VERIFY(m_autil.is_numeral(t, k));
        qm().set(n, k.to_mpq().numerator());
        qm().set(d, k.to_mpq().denominator());
        return subpaving::null_var;
    }

    // Put t as a^k.
    void as_power(expr * t, expr * & a, unsigned & k) {
        if (!m_autil.is_power(t)) {
            a = t;
            k = 1;
            return;
        }
        rational _k;
        if (!m_autil.is_numeral(to_app(t)->get_arg(1), _k) || !_k.is_int() || !_k.is_unsigned()) {
            a = t;
            k = 1;
            return;
        }
        a = to_app(t)->get_arg(0);
        k = _k.get_unsigned();
    }

    subpaving::var process_mul(app * t, unsigned depth, mpz & n, mpz & d) {
        unsigned num_args = t->get_num_args();
        if (num_args <= 1)
            found_non_simplified();
        rational k;
        expr * m;
        if (m_autil.is_numeral(t->get_arg(0), k)) {
            if (num_args != 2)
                found_non_simplified();
            qm().set(n, k.to_mpq().numerator());
            qm().set(d, k.to_mpq().denominator());
            m = t->get_arg(1);
        }
        else {
            qm().set(n, 1);
            qm().set(d, 1);
            m = t;
        }
        expr * const * margs;
        unsigned sz;
        if (m_autil.is_mul(m)) {
            margs = to_app(m)->get_args();
            sz    = to_app(m)->get_num_args();
        }
        else {
            margs = &m;
            sz    = 1;
        }
        scoped_mpz n_arg(qm());
        scoped_mpz d_arg(qm());
        sbuffer<subpaving::power> pws;
        for (unsigned i = 0; i < sz; i++) {
            expr * arg = margs[i];
            unsigned k; 
            as_power(arg, arg, k);
            subpaving::var x_arg = process(arg, depth+1, n_arg, d_arg);
            qm().power(n_arg, k, n_arg);
            qm().power(d_arg, k, d_arg);
            qm().mul(n, n_arg, n);
            qm().mul(d, d_arg, d);
            if (x_arg != subpaving::null_var)
                pws.push_back(subpaving::power(x_arg, k));
        }
        subpaving::var x;
        if (pws.empty())
            x = subpaving::null_var;
        else if (pws.size() == 1 && pws[0].degree() == 1)
            x = pws[0].get_var();
        else
            x = s().mk_monomial(pws.size(), pws.c_ptr());
        cache_result(t, x, n, d);
        return x;
    }
    
    typedef _scoped_numeral_buffer<unsynch_mpz_manager> mpz_buffer;
    typedef sbuffer<subpaving::var> var_buffer;

    subpaving::var process_add(app * t, unsigned depth, mpz & n, mpz & d) {
        unsigned num_args = t->get_num_args();
        mpz_buffer ns(qm()), ds(qm());
        var_buffer xs;
        scoped_mpq c(qm()), c_arg(qm());
        scoped_mpz n_arg(qm()), d_arg(qm());
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg           = t->get_arg(i);
            subpaving::var x_arg = process(arg, depth+1, n_arg, d_arg);
            if (x_arg == subpaving::null_var) {
                qm().set(c_arg, n_arg, d_arg);
                qm().add(c, c_arg, c);
            }
            else {
                xs.push_back(x_arg);
                ns.push_back(n_arg);
                ds.push_back(d_arg);
            }
        }
        qm().set(d,  c.get().denominator());
        unsigned sz = xs.size();
        for (unsigned i = 0; i < sz; i++) {
            qm().lcm(d, ds[i], d);
        }
        scoped_mpz & k = d_arg;
        qm().div(d, c.get().denominator(), k);
        scoped_mpz sum_c(qm());
        qm().mul(c.get().numerator(), k, sum_c);
        for (unsigned i = 0; i < sz; i++) {
            qm().div(d, ds[i], k);
            qm().mul(ns[i], k, ns[i]);
        }
        subpaving::var x;
        if (sz == 0) {
            qm().set(n, sum_c);
            x = subpaving::null_var;
        }
        else {
            x = s().mk_sum(sum_c, sz, ns.c_ptr(), xs.c_ptr());
            qm().set(n, 1);
        }
        cache_result(t, x, n, d);
        return x;
    }

    subpaving::var process_power(app * t, unsigned depth, mpz & n, mpz & d) {
        rational k;
        SASSERT(t->get_num_args() == 2);
        if (!m_autil.is_numeral(t->get_arg(1), k) || !k.is_int() || !k.is_unsigned()) {
            qm().set(n, 1);
            qm().set(d, 1);
            return mk_var_for(t);
        }
        unsigned _k = k.get_unsigned();
        subpaving::var x = process(t->get_arg(0), depth+1, n, d);
        if (x != subpaving::null_var) {
            subpaving::power p(x, _k);
            x = s().mk_monomial(1, &p);
        }
        qm().power(n, _k, n);
        qm().power(d, _k, d);
        cache_result(t, x, n, d);
        return x;
    }

    subpaving::var process_arith_app(app * t, unsigned depth, mpz & n, mpz & d) {
        SASSERT(m_autil.is_arith_expr(t));

        switch (t->get_decl_kind()) {
        case OP_NUM:
            return process_num(t, depth, n, d);
        case OP_ADD: 
            return process_add(t, depth, n, d);
        case OP_MUL: 
            return process_mul(t, depth, n, d);
        case OP_POWER:
            return process_power(t, depth, n, d);
        case OP_TO_REAL: 
            return process(t->get_arg(0), depth+1, n, d);
        case OP_SUB:
        case OP_UMINUS:
            found_non_simplified();
            break;
        case OP_TO_INT:
        case OP_DIV:
        case OP_IDIV:
        case OP_MOD:
        case OP_REM:
        case OP_IRRATIONAL_ALGEBRAIC_NUM:
            throw default_exception("you must apply arithmetic purifier before internalizing expressions into the subpaving module.");
        case OP_SIN: 
        case OP_COS:
        case OP_TAN:
        case OP_ASIN:
        case OP_ACOS:
        case OP_ATAN:
        case OP_SINH:
        case OP_COSH:
        case OP_TANH:
        case OP_ASINH:
        case OP_ACOSH:
        case OP_ATANH:
            // TODO
            throw default_exception("transcendental and hyperbolic functions are not supported yet.");
        default:
            UNREACHABLE();
        }
        return subpaving::null_var;
    }

    subpaving::var process(expr * t, unsigned depth, mpz & n, mpz & d) {
        SASSERT(is_int_real(t));
        checkpoint();

        if (is_cached(t)) {
            unsigned idx = m_cache.find(t);
            qm().set(n, m_cached_numerators[idx]);
            qm().set(d, m_cached_denominators[idx]);
            return m_cached_vars[idx];
        }

        SASSERT(!is_quantifier(t));
        if (::is_var(t) || !m_autil.is_arith_expr(t)) {
            qm().set(n, 1);
            qm().set(d, 1);
            return mk_var_for(t);
        }

        return process_arith_app(to_app(t), depth, n, d);
    }
    
    bool is_var(expr * t) const { 
        return m_expr2var->is_var(t); 
    }

    void set_cancel(bool f) {
        m_cancel = f;
    }
    
    subpaving::var internalize_term(expr * t, mpz & n, mpz & d) {
        return process(t, 0, n, d);
    }
};

expr2subpaving::expr2subpaving(ast_manager & m, subpaving::context & s, expr2var * e2v) {
    m_imp = alloc(imp, m, s, e2v);
}

expr2subpaving::~expr2subpaving() {
    dealloc(m_imp);
}

ast_manager & expr2subpaving::m() const {
    return m_imp->m();
}

subpaving::context & expr2subpaving::s() const {
    return m_imp->s();
}
    
bool expr2subpaving::is_var(expr * t) const {
    return m_imp->is_var(t);
}
    
void expr2subpaving::set_cancel(bool f) {
    m_imp->set_cancel(f);
}

subpaving::var expr2subpaving::internalize_term(expr * t, mpz & n, mpz & d) {
    return m_imp->internalize_term(t, n, d);
}
