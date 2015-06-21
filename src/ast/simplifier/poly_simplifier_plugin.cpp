/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    poly_simplifier_plugin.cpp

Abstract:

    Abstract class for families that have polynomials.

Author:

    Leonardo (leonardo) 2008-01-08
    
--*/
#include"poly_simplifier_plugin.h"
#include"ast_pp.h"
#include"ast_util.h"
#include"ast_smt2_pp.h"
#include"ast_ll_pp.h"

poly_simplifier_plugin::poly_simplifier_plugin(symbol const & fname, ast_manager & m, decl_kind add, decl_kind mul, decl_kind uminus, decl_kind sub,
                                               decl_kind num):
    simplifier_plugin(fname, m), 
    m_ADD(add), 
    m_MUL(mul),
    m_SUB(sub),
    m_UMINUS(uminus),
    m_NUM(num),
    m_curr_sort(0),
    m_curr_sort_zero(0) {
}

expr * poly_simplifier_plugin::mk_add(unsigned num_args, expr * const * args) { 
    SASSERT(num_args > 0);
#ifdef Z3DEBUG
    // check for incorrect use of mk_add
    for (unsigned i = 0; i < num_args; i++) {
        SASSERT(!is_zero(args[i]));
    }
#endif    
    if (num_args == 1)
        return args[0];
    else
        return m_manager.mk_app(m_fid, m_ADD, num_args, args); 
}

expr * poly_simplifier_plugin::mk_mul(unsigned num_args, expr * const * args) { 
    SASSERT(num_args > 0);
#ifdef Z3DEBUG
    // check for incorrect use of mk_mul
    set_curr_sort(args[0]);
    SASSERT(!is_zero(args[0]));
    numeral k;
    for (unsigned i = 0; i < num_args; i++) {
        SASSERT(!is_numeral(args[i], k) || !k.is_one());
        SASSERT(i == 0 || !is_numeral(args[i]));
    }
#endif
    if (num_args == 1) 
        return args[0];
    else if (num_args == 2)
        return m_manager.mk_app(m_fid, m_MUL, args[0], args[1]);
    else if (is_numeral(args[0]))
        return m_manager.mk_app(m_fid, m_MUL, args[0], m_manager.mk_app(m_fid, m_MUL, num_args - 1, args+1));
    else
        return m_manager.mk_app(m_fid, m_MUL, num_args, args); 
}

expr * poly_simplifier_plugin::mk_mul(numeral const & c, expr * body) {
    numeral c_prime, d;
    c_prime = norm(c);
    if (c_prime.is_zero())
        return 0;
    if (body == 0)
        return mk_numeral(c_prime);
    if (c_prime.is_one())
         return body;
    if (is_numeral(body, d)) {
        c_prime = norm(c_prime*d);
        if (c_prime.is_zero())
            return 0;
        return mk_numeral(c_prime);
    }
    set_curr_sort(body);
    expr * args[2] = { mk_numeral(c_prime), body };
    return mk_mul(2, args);
}

/**
   \brief Traverse args, and copy the non-numeral exprs to result, and accumulate the 
   value of the numerals in k.
*/
void poly_simplifier_plugin::process_monomial(unsigned num_args, expr * const * args, numeral & k, ptr_buffer<expr> & result) {
    rational v;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = args[i];
        if (is_numeral(arg, v))
            k *= v;
        else
            result.push_back(arg);
    }
}

#ifdef Z3DEBUG
/**
   \brief Return true if m is a wellformed monomial.
*/
bool poly_simplifier_plugin::wf_monomial(expr * m) const {
    SASSERT(!is_add(m));
    if (is_mul(m)) {
        app * curr = to_app(m);
        expr * pp  = 0;
        if (is_numeral(curr->get_arg(0)))
            pp = curr->get_arg(1);
        else
            pp = curr;
        if (is_mul(pp)) {
            for (unsigned i = 0; i < to_app(pp)->get_num_args(); i++) {
                expr * arg = to_app(pp)->get_arg(i);
                CTRACE("wf_monomial_bug", is_mul(arg), 
                       tout << "m:  "  << mk_ismt2_pp(m, m_manager) << "\n";
                       tout << "pp: "  << mk_ismt2_pp(pp, m_manager) << "\n";
                       tout << "arg: " << mk_ismt2_pp(arg, m_manager) << "\n";
                       tout << "i:  " << i << "\n";
                       );
                SASSERT(!is_mul(arg));
                SASSERT(!is_numeral(arg));
            }
        }
    }
    return true;
}

/**
   \brief Return true if m is a wellformed polynomial.
*/
bool poly_simplifier_plugin::wf_polynomial(expr * m) const {
    if (is_add(m)) {
        for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
            expr * arg = to_app(m)->get_arg(i);
            SASSERT(!is_add(arg));
            SASSERT(wf_monomial(arg));
        }
    }
    else if (is_mul(m)) {
        SASSERT(wf_monomial(m));
    }
    return true;
}
#endif

/**
   \brief Functor used to sort the elements of a monomial.
   Force numeric constants to be in the beginning.
*/
struct monomial_element_lt_proc {
    poly_simplifier_plugin &  m_plugin;
    monomial_element_lt_proc(poly_simplifier_plugin & p):m_plugin(p) {}
    bool operator()(expr * m1, expr * m2) const {
        SASSERT(!m_plugin.is_numeral(m1) || !m_plugin.is_numeral(m2));
        if (m_plugin.is_numeral(m1))
            return true;
        if (m_plugin.is_numeral(m2))
            return false;
        return m1->get_id() < m2->get_id();
    }
};

/**
   \brief Create a monomial (* args). 
*/
void poly_simplifier_plugin::mk_monomial(unsigned num_args, expr * * args, expr_ref & result) {
    switch(num_args) {
    case 0:
        result = mk_one();
        break;
    case 1:
        result = args[0];
        break;
    default:
        std::stable_sort(args, args + num_args, monomial_element_lt_proc(*this));
        result = mk_mul(num_args, args);
        SASSERT(wf_monomial(result));
        break;
    }
}

/**
   \brief Return the body of the monomial. That is, the monomial without a coefficient.
   Examples: (* 2 (* x y)) ==> (* x y)
             (* x x) ==> (* x x)
             x       ==> x
             10      ==> 10
*/
expr * poly_simplifier_plugin::get_monomial_body(expr * m) {
    TRACE("get_monomial_body_bug", tout << mk_pp(m, m_manager) << "\n";);
    SASSERT(wf_monomial(m));
    if (!is_mul(m))
       return m;
    if (is_numeral(to_app(m)->get_arg(0)))
        return to_app(m)->get_arg(1);
    return m;
}

inline bool is_essentially_var(expr * n, family_id fid) {
    SASSERT(is_var(n) || is_app(n));
    return is_var(n) || to_app(n)->get_family_id() != fid;
}

/**
   \brief Hack for ordering monomials.
   We want an order << where
      - (* c1 m1) << (* c2 m2)    when  m1->get_id() < m2->get_id(), and c1 and c2 are numerals.
      - c << m                    when  c is a numeral, and m is not.

   So, this method returns -1 for numerals, and the id of the body of the monomial   
*/
int poly_simplifier_plugin::get_monomial_body_order(expr * m) {
    if (is_essentially_var(m, m_fid)) {
        return m->get_id();
    }
    else if (is_mul(m)) {
        if (is_numeral(to_app(m)->get_arg(0)))
            return to_app(m)->get_arg(1)->get_id();
        else
            return m->get_id();
    }
    else if (is_numeral(m)) {
        return -1;
    }
    else {
        return m->get_id();
    }
}

void poly_simplifier_plugin::get_monomial_coeff(expr * m, numeral & result) {
    SASSERT(!is_numeral(m));
    SASSERT(wf_monomial(m));
    if (!is_mul(m))
        result = numeral::one();
    else if (is_numeral(to_app(m)->get_arg(0), result))
        return;
    else
        result = numeral::one();
}

/**
   \brief Return true if n1 and n2 can be written as k1 * t and k2 * t, where k1 and
   k2 are numerals, or n1 and n2 are both numerals.
*/
bool poly_simplifier_plugin::eq_monomials_modulo_k(expr * n1, expr * n2) {
    bool is_num1 = is_numeral(n1);
    bool is_num2 = is_numeral(n2);
    if (is_num1 != is_num2)
        return false;
    if (is_num1 && is_num2)
        return true;
    return get_monomial_body(n1) == get_monomial_body(n2);
}

/**
   \brief Return (k1 + k2) * t (or (k1 - k2) * t when inv = true), where n1 = k1 * t, and n2 = k2 * t
   Return false if the monomials cancel each other.
*/
bool poly_simplifier_plugin::merge_monomials(bool inv, expr * n1, expr * n2, expr_ref & result) {
    numeral k1;
    numeral k2;
    bool is_num1 = is_numeral(n1, k1);
    bool is_num2 = is_numeral(n2, k2);
    SASSERT(is_num1 == is_num2);
    if (!is_num1 && !is_num2) {
        get_monomial_coeff(n1, k1);
        get_monomial_coeff(n2, k2);        
        SASSERT(eq_monomials_modulo_k(n1, n2));
    }
    if (inv)
        k1 -= k2;
    else 
        k1 += k2;
    if (k1.is_zero())
        return false;
    if (is_num1 && is_num2) {
        result = mk_numeral(k1);
    }
    else {
        expr * b = get_monomial_body(n1);
        if (k1.is_one())
            result = b;
        else
            result = m_manager.mk_app(m_fid, m_MUL, mk_numeral(k1), b);
    }
    TRACE("merge_monomials", tout << mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) << "\n" << mk_pp(result, m_manager) << "\n";);
    return true;
}

/**
   \brief Return a monomial equivalent to -n.
*/
void poly_simplifier_plugin::inv_monomial(expr * n, expr_ref & result) {
    set_curr_sort(n);
    SASSERT(wf_monomial(n));
    rational v;
    SASSERT(n != 0);
    TRACE("inv_monomial_bug", tout << "n:\n" << mk_ismt2_pp(n, m_manager) << "\n";);
    if (is_numeral(n, v)) {
        TRACE("inv_monomial_bug", tout << "is numeral\n";);
        v.neg();
        result = mk_numeral(v);
    }
    else {
        TRACE("inv_monomial_bug", tout << "is not numeral\n";);
        numeral k;
        get_monomial_coeff(n, k);
        expr * b = get_monomial_body(n);
        k.neg();
        if (k.is_one())
            result = b;
        else
            result = m_manager.mk_app(m_fid, m_MUL, mk_numeral(k), b);
    }
}

/** 
    \brief Add a monomial n to result. 
*/
template<bool Inv>
void poly_simplifier_plugin::add_monomial_core(expr * n, expr_ref_vector & result) {
    if (is_zero(n)) 
        return;
    if (Inv) {
        expr_ref n_prime(m_manager);
        inv_monomial(n, n_prime);
        result.push_back(n_prime);
    }
    else { 
        result.push_back(n);
    }
}

void poly_simplifier_plugin::add_monomial(bool inv, expr * n, expr_ref_vector & result) {
    if (inv)
        add_monomial_core<true>(n, result);
    else
        add_monomial_core<false>(n, result);
}

/**
   \brief Copy the monomials in n to result. The monomials are inverted if inv is true.
   Equivalent monomials are merged. 
*/
template<bool Inv>
void poly_simplifier_plugin::process_sum_of_monomials_core(expr * n, expr_ref_vector & result) {
    SASSERT(wf_polynomial(n));
    if (is_add(n)) {
        for (unsigned i = 0; i < to_app(n)->get_num_args(); i++) 
            add_monomial_core<Inv>(to_app(n)->get_arg(i), result);
    }
    else {
        add_monomial_core<Inv>(n, result);
    }
}

void poly_simplifier_plugin::process_sum_of_monomials(bool inv, expr * n, expr_ref_vector & result) {
    if (inv)
        process_sum_of_monomials_core<true>(n, result);
    else
        process_sum_of_monomials_core<false>(n, result);
}

/**
   \brief Copy the (non-numeral) monomials in n to result. The monomials are inverted if inv is true.
   Equivalent monomials are merged. The constant (numeral) monomials are accumulated in k.
*/
void poly_simplifier_plugin::process_sum_of_monomials(bool inv, expr * n, expr_ref_vector & result, numeral & k) {
    SASSERT(wf_polynomial(n));
    numeral val;
    if (is_add(n)) {
        for (unsigned i = 0; i < to_app(n)->get_num_args(); i++) {
            expr * arg = to_app(n)->get_arg(i);
            if (is_numeral(arg, val)) {
                k += inv ? -val : val;
            }
            else {
                add_monomial(inv, arg, result);
            }
        }
    }
    else if (is_numeral(n, val)) {
        k += inv ? -val : val;
    }
    else {
        add_monomial(inv, n, result);
    }
}

/**
   \brief Functor used to sort monomials.
   Force numeric constants to be in the beginning of a polynomial.
*/
struct monomial_lt_proc {
    poly_simplifier_plugin & m_plugin;
    monomial_lt_proc(poly_simplifier_plugin & p):m_plugin(p) {}
    bool operator()(expr * m1, expr * m2) const {
        return m_plugin.get_monomial_body_order(m1) < m_plugin.get_monomial_body_order(m2);
    }
};

void poly_simplifier_plugin::mk_sum_of_monomials_core(unsigned sz, expr ** ms, expr_ref & result) {
    switch (sz) {
    case 0:
        result = mk_zero();
        break;
    case 1:
        result = ms[0];
        break;
    default:
        result = mk_add(sz, ms);
        break;
    }
}

/**
   \brief Return true if m is essentially a variable, or is of the form (* c x),
   where c is a numeral and x is essentially a variable.
   Store the "variable" in x.
*/
bool poly_simplifier_plugin::is_simple_monomial(expr * m, expr * & x) {
    if (is_essentially_var(m, m_fid)) {
        x = m;
        return true;
    }
    if (is_app(m) && to_app(m)->get_num_args() == 2) {
        expr * arg1 = to_app(m)->get_arg(0);
        expr * arg2 = to_app(m)->get_arg(1);
        if (is_numeral(arg1) && is_essentially_var(arg2, m_fid)) {
            x = arg2;
            return true;
        }
    }
    return false;
}

/**
   \brief Return true if all monomials are simple, and each "variable" occurs only once.
   The method assumes the monomials were sorted using monomial_lt_proc.
*/
bool poly_simplifier_plugin::is_simple_sum_of_monomials(expr_ref_vector & monomials) {
    expr * last_var = 0;
    expr * curr_var = 0;
    unsigned size = monomials.size();
    for (unsigned i = 0; i < size; i++) {
        expr * m = monomials.get(i);
        if (!is_simple_monomial(m, curr_var))
            return false;
        if (curr_var == last_var)
            return false;
        last_var = curr_var;
    }
    return true;
}

/**
   \brief Store in result the sum of the given monomials.
*/
void poly_simplifier_plugin::mk_sum_of_monomials(expr_ref_vector & monomials, expr_ref & result) {
    switch (monomials.size()) {
    case 0:
        result = mk_zero();
        break;
    case 1:
        result = monomials.get(0);
        break;
    default: {
        TRACE("mk_sum_sort", tout << "before\n"; for (unsigned i = 0; i < monomials.size(); i++) tout << mk_ll_pp(monomials.get(i), m_manager) << "\n";);
        std::stable_sort(monomials.c_ptr(), monomials.c_ptr() + monomials.size(), monomial_lt_proc(*this));
        TRACE("mk_sum_sort", tout << "after\n";  for (unsigned i = 0; i < monomials.size(); i++) tout << mk_ll_pp(monomials.get(i), m_manager) << "\n";);
        if (is_simple_sum_of_monomials(monomials)) {
            mk_sum_of_monomials_core(monomials.size(), monomials.c_ptr(), result);
            return;
        }
        ptr_buffer<expr> new_monomials;
        expr * last_body = 0;
        numeral last_coeff;
        numeral coeff; 
        unsigned sz = monomials.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * m    = monomials.get(i);
            expr * body = 0;
            if (!is_numeral(m, coeff)) {
                body = get_monomial_body(m);
                get_monomial_coeff(m, coeff);
            }
            if (last_body == body) {
                last_coeff += coeff;
                continue;
            }
            expr * new_m = mk_mul(last_coeff, last_body);
            if (new_m)
                new_monomials.push_back(new_m);
            last_body  = body;
            last_coeff = coeff;
        }
        expr * new_m = mk_mul(last_coeff, last_body);
        if (new_m)
            new_monomials.push_back(new_m);
        TRACE("mk_sum", for (unsigned i = 0; i < monomials.size(); i++) tout << mk_pp(monomials.get(i), m_manager) << "\n";
              tout << "======>\n";
              for (unsigned i = 0; i < new_monomials.size(); i++) tout << mk_pp(new_monomials.get(i), m_manager) << "\n";);
        mk_sum_of_monomials_core(new_monomials.size(), new_monomials.c_ptr(), result);
        break;
    } }
}

/**
   \brief Auxiliary template for mk_add_core
*/
template<bool Inv>
void poly_simplifier_plugin::mk_add_core_core(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args >= 2);
    expr_ref_vector monomials(m_manager);
    process_sum_of_monomials_core<false>(args[0], monomials);
    for (unsigned i = 1; i < num_args; i++) {
        process_sum_of_monomials_core<Inv>(args[i], monomials);
    }
    TRACE("mk_add_core_bug", 
          for (unsigned i = 0; i < monomials.size(); i++) { 
              SASSERT(monomials.get(i) != 0); 
              tout << mk_ismt2_pp(monomials.get(i), m_manager) << "\n"; 
          });
    mk_sum_of_monomials(monomials, result);
}

/**
   \brief Return a sum of monomials. The method assume that each arg in args is a sum of monomials.
   If inv is true, then all but the first argument in args are inverted.
*/
void poly_simplifier_plugin::mk_add_core(bool inv, unsigned num_args, expr * const * args, expr_ref & result) {
    TRACE("mk_add_core_bug", 
          for (unsigned i = 0; i < num_args; i++) { 
              SASSERT(args[i] != 0);
              tout << mk_ismt2_pp(args[i], m_manager) << "\n";
          });
    switch (num_args) {
    case 0:
        result = mk_zero();
        break;
    case 1:
        result = args[0];
        break;
    default:
        if (inv)
            mk_add_core_core<true>(num_args, args, result);
        else
            mk_add_core_core<false>(num_args, args, result);
        break;
    }
}

void poly_simplifier_plugin::mk_add(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args > 0);
    set_curr_sort(args[0]);
    mk_add_core(false, num_args, args, result);
}

void poly_simplifier_plugin::mk_add(expr * arg1, expr * arg2, expr_ref & result) {
    expr * args[2] = { arg1, arg2 };
    mk_add(2, args, result);
}

void poly_simplifier_plugin::mk_sub(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args > 0);
    set_curr_sort(args[0]);
    mk_add_core(true, num_args, args, result);
}

void poly_simplifier_plugin::mk_sub(expr * arg1, expr * arg2, expr_ref & result) {
    expr * args[2] = { arg1, arg2 };
    mk_sub(2, args, result);
}

void poly_simplifier_plugin::mk_uminus(expr * arg, expr_ref & result) {
    set_curr_sort(arg);
    rational v;
    if (is_numeral(arg, v)) {
        v.neg();
        result = mk_numeral(v);
    }
    else {
        expr_ref zero(mk_zero(), m_manager);
        mk_sub(zero.get(), arg, result);
    }
}

/**
   \brief Add monomial n to result, the coeff of n is stored in k.
*/
void poly_simplifier_plugin::append_to_monomial(expr * n, numeral & k, ptr_buffer<expr> & result) {
    SASSERT(wf_monomial(n));
    rational val;
    if (is_numeral(n, val)) {
        k *= val;
        return;
    }
    get_monomial_coeff(n, val);
    k *= val;
    n  = get_monomial_body(n);

    if (is_mul(n)) {
        for (unsigned i = 0; i < to_app(n)->get_num_args(); i++)
            result.push_back(to_app(n)->get_arg(i));
    }
    else {
        result.push_back(n);
    }
}

/**
   \brief Return a sum of monomials that is equivalent to (* args[0] ... args[num_args-1]).
   This method assumes that each arg[i] is a sum of monomials.
*/
void poly_simplifier_plugin::mk_mul(unsigned num_args, expr * const * args, expr_ref & result) {
    if (num_args == 1) {
        result = args[0];
        return;
    }
    rational val;
    if (num_args == 2 && is_numeral(args[0], val) && is_essentially_var(args[1], m_fid)) {
        if (val.is_one())
            result = args[1];
        else if (val.is_zero())
            result = args[0];
        else
            result = mk_mul(num_args, args);
        return;
    }
    if (num_args == 2 && is_essentially_var(args[0], m_fid) && is_numeral(args[1], val)) {
        if (val.is_one())
            result = args[0];
        else if (val.is_zero())
            result = args[1];
        else {
            expr * inv_args[2] = { args[1], args[0] };
            result = mk_mul(2, inv_args);
        }
        return;
    }

    TRACE("mk_mul_bug", 
          for (unsigned i = 0; i < num_args; i++) {
              tout << mk_pp(args[i], m_manager) << "\n";
          });
    set_curr_sort(args[0]);
    buffer<unsigned> szs;
    buffer<unsigned> it;
    vector<ptr_vector<expr> > sums;
    for (unsigned i = 0; i < num_args; i ++) {
        it.push_back(0);
        expr * arg  = args[i];
        SASSERT(wf_polynomial(arg));
        sums.push_back(ptr_vector<expr>());
        ptr_vector<expr> & v = sums.back();
        if (is_add(arg)) {
            v.append(to_app(arg)->get_num_args(), to_app(arg)->get_args());
        }
        else {
            v.push_back(arg);
        }
        szs.push_back(v.size());
    }
    expr_ref_vector monomials(m_manager);
    do {
        rational k(1);
        ptr_buffer<expr> m;
        for (unsigned i = 0; i < num_args; i++) {
            ptr_vector<expr> & v = sums[i];
            expr * arg           = v[it[i]];
            TRACE("mk_mul_bug", tout << "k: " << k << " arg: " << mk_pp(arg, m_manager) << "\n";);
            append_to_monomial(arg, k, m);
            TRACE("mk_mul_bug", tout << "after k: " << k << "\n";);
        }
        expr_ref num(m_manager);
        if (!k.is_zero() && !k.is_one()) {
            num = mk_numeral(k);
            m.push_back(num);
            // bit-vectors can normalize 
            // to 1 during
            // internalization.
            if (is_numeral(num, k) && k.is_one()) {
                m.pop_back();
            }                
        }
        if (!k.is_zero()) {
            expr_ref new_monomial(m_manager);
            TRACE("mk_mul_bug", 
                  for (unsigned i = 0; i < m.size(); i++) {
                      tout << mk_pp(m[i], m_manager) << "\n";
                  });
            mk_monomial(m.size(), m.c_ptr(), new_monomial);
            TRACE("mk_mul_bug", tout << "new_monomial:\n" << mk_pp(new_monomial, m_manager) << "\n";);
            add_monomial_core<false>(new_monomial, monomials);
        }
    }
    while (product_iterator_next(szs.size(), szs.c_ptr(), it.c_ptr()));
    mk_sum_of_monomials(monomials, result);
}

void poly_simplifier_plugin::mk_mul(expr * arg1, expr * arg2, expr_ref & result) {
    expr * args[2] = { arg1, arg2 };
    mk_mul(2, args, result);
}

bool poly_simplifier_plugin::reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    unsigned i = 0;
    for (; i < num_args; i++)
        if (!is_numeral(args[i]))
            break;
    if (i == num_args) {
        // all arguments are numerals
        // check if arguments are different...
        ptr_buffer<expr> buffer;
        buffer.append(num_args, args);
        std::sort(buffer.begin(), buffer.end(), ast_lt_proc());
        for (unsigned i = 0; i < num_args; i++) {
            if (i > 0 && buffer[i] == buffer[i-1]) {
                result = m_manager.mk_false();
                return true;
            }
        }
        result = m_manager.mk_true();
        return true;
    }
    return false;
}

bool poly_simplifier_plugin::reduce(func_decl * f, unsigned num_args, rational const * mults, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    if (is_decl_of(f, m_fid, m_ADD)) {
        SASSERT(num_args > 0);
        set_curr_sort(args[0]);
        expr_ref_buffer args1(m_manager);
        for (unsigned i = 0; i < num_args; ++i) {
            expr * arg = args[i];
            rational m = norm(mults[i]);
            if (m.is_zero()) {
                // skip
            }
            else if (m.is_one()) {
                args1.push_back(arg);
            }
            else {
                expr_ref k(m_manager);
                k = mk_numeral(m);
                expr_ref new_arg(m_manager);
                mk_mul(k, args[i], new_arg);
                args1.push_back(new_arg);
            }
        }
        if (args1.empty()) {
            result = mk_zero();
        }
        else {
            mk_add(args1.size(), args1.c_ptr(), result);
        }
        return true;
    }
    else {
        return simplifier_plugin::reduce(f, num_args, mults, args, result);
    }
}

/**
   \brief Return true if n is can be put into the form (+ v t) or (+ (- v) t)
   \c inv = true will contain true if (- v) is found, and false otherwise.
*/
bool poly_simplifier_plugin::is_var_plus_ground(expr * n, bool & inv, var * & v, expr_ref & t) {
    if (!is_add(n) || is_ground(n))
        return false;
    
    ptr_buffer<expr> args;
    v = 0;
    expr * curr = to_app(n);
    bool stop = false;
    inv = false;
    while (!stop) {
        expr * arg;
        expr * neg_arg;
        if (is_add(curr)) {
            arg  = to_app(curr)->get_arg(0);
            curr = to_app(curr)->get_arg(1);
        }
        else {
            arg  = curr;
            stop = true;
        }
        if (is_ground(arg)) {
            TRACE("model_checker_bug", tout << "pushing:\n" << mk_pp(arg, m_manager) << "\n";);
            args.push_back(arg);
        }
        else if (is_var(arg)) {
            if (v != 0)
                return false; // already found variable
            v = to_var(arg);
        }
        else if (is_times_minus_one(arg, neg_arg) && is_var(neg_arg)) {
            if (v != 0)
                return false; // already found variable
            v = to_var(neg_arg);
            inv = true;
        }
        else {
            return false; // non ground term.
        }
    }
    if (v == 0)
        return false; // did not find variable
    SASSERT(!args.empty());
    mk_add(args.size(), args.c_ptr(), t);
    return true;
}
