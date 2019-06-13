/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    poly_rewriter_def.h

Abstract:

    Basic rewriting rules for Polynomials.

Author:

    Leonardo (leonardo) 2011-04-08

Notes:

--*/
#include "ast/rewriter/poly_rewriter.h"
#include "ast/rewriter/poly_rewriter_params.hpp"
#include "ast/rewriter/arith_rewriter_params.hpp"
#include "ast/ast_lt.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"


template<typename Config>
void poly_rewriter<Config>::updt_params(params_ref const & _p) {
    poly_rewriter_params p(_p);
    m_flat = p.flat();
    m_som  = p.som();
    m_hoist_mul = p.hoist_mul();
    m_hoist_cmul = p.hoist_cmul();
    m_som_blowup = p.som_blowup();
    if (!m_flat) m_som = false;
    if (m_som) m_hoist_mul = false;
    arith_rewriter_params ap(_p);
    m_ast_order  = !ap.arith_ineq_lhs();
}

template<typename Config>
void poly_rewriter<Config>::get_param_descrs(param_descrs & r) {
    poly_rewriter_params::collect_param_descrs(r);
}

template<typename Config>
expr * poly_rewriter<Config>::mk_add_app(unsigned num_args, expr * const * args) { 
    switch (num_args) {
    case 0: return mk_numeral(numeral(0));
    case 1: return args[0];
    default: return m().mk_app(get_fid(), add_decl_kind(), num_args, args);
    }
}

// t = (^ x y)  --> return x, and set k = y  if k is an integer >= 1
// Otherwise return t and set k = 1
template<typename Config>
expr * poly_rewriter<Config>::get_power_body(expr * t, rational & k) {
    if (!is_power(t)) {
        k = rational(1);
        return t;
    }
    if (is_numeral(to_app(t)->get_arg(1), k) && k.is_int() && k > rational(1)) {
        return to_app(t)->get_arg(0);
    }
    k = rational(1);
    return t;
}

template<typename Config>
bool poly_rewriter<Config>::is_zero(expr* e) const {
    rational v;
    return is_numeral(e, v) && v.is_zero();
}


template<typename Config>
expr * poly_rewriter<Config>::mk_mul_app(unsigned num_args, expr * const * args) { 
    switch (num_args) {
    case 0: 
        return mk_numeral(numeral(1));
    case 1: 
        return args[0];
    default: 
        if (use_power()) {
            rational k_prev;
            expr * prev = get_power_body(args[0], k_prev);
            rational k;
            ptr_buffer<expr> new_args;
#define PUSH_POWER() {                                                                          \
                if (k_prev.is_one()) {                                                          \
                    new_args.push_back(prev);                                                   \
                }                                                                               \
                else {                                                                          \
                    expr * pargs[2] = { prev, mk_numeral(k_prev) };                             \
                    new_args.push_back(m().mk_app(get_fid(), power_decl_kind(), 2, pargs));     \
                }                                                                               \
            }
 
            for (unsigned i = 1; i < num_args; i++) {
                expr * arg = get_power_body(args[i], k);
                if (arg == prev) {
                    k_prev += k;
                }
                else {
                    PUSH_POWER();
                    prev   = arg;
                    k_prev = k;
                }
            }
            PUSH_POWER();
            SASSERT(new_args.size() > 0);
            if (new_args.size() == 1) {
                return new_args[0];
            }
            else {
                return m().mk_app(get_fid(), mul_decl_kind(), new_args.size(), new_args.c_ptr());
            }
        }
        else {
            return m().mk_app(get_fid(), mul_decl_kind(), num_args, args);
        }
    }
}

template<typename Config>
expr * poly_rewriter<Config>::mk_mul_app(numeral const & c, expr * arg) {
    if (c.is_one()) {
        return arg;
    }
    else if (is_zero(arg)) {
        return arg;
    }
    else {
        expr * new_args[2] = { mk_numeral(c), arg };
        return mk_mul_app(2, new_args); 
    }
}

template<typename Config>
br_status poly_rewriter<Config>::mk_flat_mul_core(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args >= 2);
    // only try to apply flattening if it is not already in one of the flat monomial forms
    // - (* c x)
    // - (* c (* x_1 ... x_n))
    if (num_args != 2 || !is_numeral(args[0]) || (is_mul(args[1]) && is_numeral(to_app(args[1])->get_arg(0)))) {
        unsigned i;
        for (i = 0; i < num_args; i++) {
            if (is_mul(args[i]))
                break;
        }
        if (i < num_args) {
            // input has nested monomials. 
            ptr_buffer<expr> flat_args;
            // we need the todo buffer to handle: (* (* c (* x_1 ... x_n)) (* d (* y_1 ... y_n)))
            ptr_buffer<expr> todo;
            flat_args.append(i, args);
            for (unsigned j = i; j < num_args; j++) {
                if (is_mul(args[j])) {
                    todo.push_back(args[j]);
                    while (!todo.empty()) {
                        expr * curr = todo.back();
                        todo.pop_back();
                        if (is_mul(curr)) {
                            unsigned k = to_app(curr)->get_num_args();
                            while (k > 0) {
                                --k;
                                todo.push_back(to_app(curr)->get_arg(k));
                            }
                        }
                        else {
                            flat_args.push_back(curr);
                        }
                    }
                }
                else {
                    flat_args.push_back(args[j]);
                }
            }
            TRACE("poly_rewriter",
                  tout << "flat mul:\n";
                  for (unsigned i = 0; i < num_args; i++) tout << mk_bounded_pp(args[i], m()) << "\n";
                  tout << "---->\n";
                  for (unsigned i = 0; i < flat_args.size(); i++) tout << mk_bounded_pp(flat_args[i], m()) << "\n";);
            br_status st = mk_nflat_mul_core(flat_args.size(), flat_args.c_ptr(), result);
            if (st == BR_FAILED) {
                result = mk_mul_app(flat_args.size(), flat_args.c_ptr());
                return BR_DONE;
            }
            return st;
        }
    }
    return mk_nflat_mul_core(num_args, args, result);    
}


template<typename Config>
br_status poly_rewriter<Config>::mk_nflat_mul_core(unsigned num_args, expr * const * args, expr_ref & result) {
    mon_lt lt(*this);
    SASSERT(num_args >= 2);
    // cheap case
    numeral a;
    if (num_args == 2 && is_numeral(args[0], a) && !a.is_one() && !a.is_zero() && 
        (is_var(args[1]) || to_app(args[1])->get_decl()->get_family_id() != get_fid())) 
        return BR_FAILED;
    numeral c(1);
    unsigned num_coeffs = 0;
    unsigned num_add    = 0;
    expr *  var         = nullptr;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = args[i];
        if (is_numeral(arg, a)) {
            num_coeffs++;
            c *= a;
        }
        else {
            var = arg;
            if (is_add(arg))
                num_add++;
        }
    }
    
    normalize(c);
    // (* c_1 ... c_n) --> c_1*...*c_n
    if (num_coeffs == num_args) {
        result = mk_numeral(c);
        return BR_DONE;
    }

    // (* s ... 0 ... r) --> 0
    if (c.is_zero()) {
        result = mk_numeral(c);
        return BR_DONE;
    }

    if (num_coeffs == num_args - 1) {
        SASSERT(var != 0);
        // (* c_1 ... c_n x) --> x  if c_1*...*c_n == 1
        if (c.is_one()) {
            result = var;
            return BR_DONE;
        }

        numeral c_prime;
        if (is_mul(var)) {
            // apply basic simplification even when flattening is not enabled.
            // (* c1 (* c2 x)) --> (* c1*c2 x)
            if (to_app(var)->get_num_args() == 2 && is_numeral(to_app(var)->get_arg(0), c_prime)) {
                c *= c_prime;
                normalize(c);
                result = mk_mul_app(c, to_app(var)->get_arg(1));
                return BR_REWRITE1;
            }
            else {
                // var is a power-product
                return BR_FAILED;
            }
        }
        
        if (num_add == 0 || m_hoist_cmul) {
            SASSERT(!is_add(var) || m_hoist_cmul);
            if (num_args == 2 && args[1] == var) {
                DEBUG_CODE({ 
                    numeral c_prime;
                    SASSERT(is_numeral(args[0], c_prime) && c == c_prime);
                });
                // it is already simplified
                return BR_FAILED;
            }
            
            // (* c_1 ... c_n x) --> (* c_1*...*c_n x)
            result = mk_mul_app(c, var);
            return BR_DONE;
        }
        else {
            SASSERT(is_add(var));
            // (* c_1 ... c_n (+ t_1 ... t_m)) --> (+ (* c_1*...*c_n t_1) ... (* c_1*...*c_n t_m))
            ptr_buffer<expr> new_add_args;
            unsigned num = to_app(var)->get_num_args();
            for (unsigned i = 0; i < num; i++) {
                new_add_args.push_back(mk_mul_app(c, to_app(var)->get_arg(i)));
            }
            result = mk_add_app(new_add_args.size(), new_add_args.c_ptr());
            TRACE("mul_bug", tout << "result: " << mk_bounded_pp(result, m(),5) << "\n";);
            return BR_REWRITE2;
        }
    }

    SASSERT(num_coeffs <= num_args - 2);

    if (!m_som || num_add == 0) {
        ptr_buffer<expr> new_args;
        expr * prev = nullptr;
        bool ordered = true;
        for (unsigned i = 0; i < num_args; i++) {
            expr * curr = args[i];
            if (is_numeral(curr))
                continue;
            if (prev != nullptr && lt(curr, prev))
                ordered = false;
            new_args.push_back(curr);
            prev = curr;
        }
        TRACE("poly_rewriter", 
              for (unsigned i = 0; i < new_args.size(); i++) {
                  if (i > 0)
                      tout << (lt(new_args[i-1], new_args[i]) ? " < " : " !< ");
                  tout << mk_ismt2_pp(new_args[i], m());
              }
              tout << "\nordered: " << ordered << "\n";);
        if (ordered && num_coeffs == 0 && !use_power())
            return BR_FAILED;
        if (!ordered) {
            std::sort(new_args.begin(), new_args.end(), lt);
        TRACE("poly_rewriter",
                  tout << "after sorting:\n";
                  for (unsigned i = 0; i < new_args.size(); i++) {
                      if (i > 0)
                          tout << (lt(new_args[i-1], new_args[i]) ? " < " : " !< ");
                      tout << mk_ismt2_pp(new_args[i], m());
                  }
                  tout << "\n";);
        }
        SASSERT(new_args.size() >= 2);
        result = mk_mul_app(new_args.size(), new_args.c_ptr());
        result = mk_mul_app(c, result);
        TRACE("poly_rewriter", tout << "mk_nflat_mul_core result:\n" << mk_ismt2_pp(result, m()) << "\n";);
        return BR_DONE;
    }

    SASSERT(m_som && num_add > 0);

    sbuffer<unsigned> szs;
    sbuffer<unsigned> it;
    sbuffer<expr **> sums;
    for (unsigned i = 0; i < num_args; i ++) {
        it.push_back(0);
        expr * arg  = args[i];
        if (is_add(arg)) {
            sums.push_back(const_cast<expr**>(to_app(arg)->get_args()));
            szs.push_back(to_app(arg)->get_num_args());
        }
        else {
            sums.push_back(const_cast<expr**>(args + i));
            szs.push_back(1);
            SASSERT(sums.back()[0] == arg);
        }
    }
    unsigned orig_size = sums.size();
    expr_ref_buffer sum(m()); // must be ref_buffer because we may throw an exception
    ptr_buffer<expr> m_args;
    TRACE("som", tout << "starting som...\n";);
    do {
        TRACE("som", for (unsigned i = 0; i < it.size(); i++) tout << it[i] << " ";
              tout << "\n";);
        if (sum.size() > m_som_blowup * orig_size) {
            return BR_FAILED;
        }
        m_args.reset();
        for (unsigned i = 0; i < num_args; i++) {
            expr * const * v = sums[i];
            expr * arg       = v[it[i]];
            m_args.push_back(arg);
        }
        sum.push_back(mk_mul_app(m_args.size(), m_args.c_ptr()));
    }
    while (product_iterator_next(szs.size(), szs.c_ptr(), it.c_ptr()));
    result = mk_add_app(sum.size(), sum.c_ptr());
    return BR_REWRITE2;
}

template<typename Config>
br_status poly_rewriter<Config>::mk_flat_add_core(unsigned num_args, expr * const * args, expr_ref & result) {
    unsigned i;
    for (i = 0; i < num_args; i++) {
        if (is_add(args[i]))
            break;
    }
    if (i < num_args) {
        // has nested ADDs
        ptr_buffer<expr> flat_args;
        flat_args.append(i, args);
        for (; i < num_args; i++) {
            expr * arg = args[i];
            // Remark: all rewrites are depth 1.
            if (is_add(arg)) {
                unsigned num = to_app(arg)->get_num_args();
                for (unsigned j = 0; j < num; j++)
                    flat_args.push_back(to_app(arg)->get_arg(j));
            }
            else {
                flat_args.push_back(arg);
            }
        }
        br_status st = mk_nflat_add_core(flat_args.size(), flat_args.c_ptr(), result);
        if (st == BR_FAILED) {
            result = mk_add_app(flat_args.size(), flat_args.c_ptr());
            return BR_DONE;
        }
        return st;
    }
    return mk_nflat_add_core(num_args, args, result);
}

template<typename Config>
inline expr * poly_rewriter<Config>::get_power_product(expr * t) {
    if (is_mul(t) && to_app(t)->get_num_args() == 2 && is_numeral(to_app(t)->get_arg(0)))
        return to_app(t)->get_arg(1);
    return t;
}

template<typename Config>
inline expr * poly_rewriter<Config>::get_power_product(expr * t, numeral & a) {
    if (is_mul(t) && to_app(t)->get_num_args() == 2 && is_numeral(to_app(t)->get_arg(0), a))
        return to_app(t)->get_arg(1);
    a = numeral(1);
    return t;
}

template<typename Config>
bool poly_rewriter<Config>::is_mul(expr * t, numeral & c, expr * & pp) {
    if (!is_mul(t) || to_app(t)->get_num_args() != 2)
        return false;
    if (!is_numeral(to_app(t)->get_arg(0), c))
        return false;
    pp = to_app(t)->get_arg(1);
    return true;
}

template<typename Config>
struct poly_rewriter<Config>::hoist_cmul_lt {
    poly_rewriter<Config> & m_r;
    hoist_cmul_lt(poly_rewriter<Config> & r):m_r(r) {}

    bool operator()(expr * t1, expr * t2) const {
        expr * pp1 = nullptr;
        expr * pp2 = nullptr;
        numeral c1, c2;
        bool is_mul1 = m_r.is_mul(t1, c1, pp1);
        bool is_mul2 = m_r.is_mul(t2, c2, pp2);
        if (!is_mul1 && is_mul2)
            return true;
        if (is_mul1 && !is_mul2)
            return false;
        if (!is_mul1 && !is_mul2)
            return t1->get_id() < t2->get_id();
        if (c1 < c2)
            return true;
        if (c1 > c2)
            return false;
        return pp1->get_id() < pp2->get_id();
    }
};

template<typename Config>
void poly_rewriter<Config>::hoist_cmul(expr_ref_buffer & args) {
    unsigned sz = args.size();
    std::sort(args.c_ptr(), args.c_ptr() + sz, hoist_cmul_lt(*this));
    numeral c, c_prime;
    ptr_buffer<expr> pps;
    expr * pp, * pp_prime;
    unsigned j = 0;
    unsigned i = 0;
    while (i < sz) {
        expr * mon = args[i];
        if (is_mul(mon, c, pp) && i < sz - 1) {
            expr * mon_prime = args[i+1];
            if (is_mul(mon_prime, c_prime, pp_prime) && c == c_prime) {
                // found target
                pps.reset();
                pps.push_back(pp);
                pps.push_back(pp_prime);
                i += 2;
                while (i < sz && is_mul(args[i], c_prime, pp_prime) && c == c_prime) {
                    pps.push_back(pp_prime);
                    i++;
                }
                SASSERT(is_numeral(to_app(mon)->get_arg(0), c_prime) && c == c_prime);
                expr * mul_args[2] = { to_app(mon)->get_arg(0), mk_add_app(pps.size(), pps.c_ptr()) };
                args.set(j, mk_mul_app(2, mul_args));
                j++;
                continue;
            }
        }
        args.set(j, mon);
        j++;
        i++;
    }
    args.resize(j);
}

template<typename Config>
bool poly_rewriter<Config>::mon_lt::operator()(expr* e1, expr * e2) const {
    if (rw.m_ast_order) 
        return lt(e1,e2);
    return ordinal(e1) < ordinal(e2);
}

inline bool is_essentially_var(expr * n, family_id fid) {
    SASSERT(is_var(n) || is_app(n));
    return is_var(n) || to_app(n)->get_family_id() != fid;
}

template<typename Config>
int poly_rewriter<Config>::mon_lt::ordinal(expr* e) const {
    rational k;
    if (is_essentially_var(e, rw.get_fid())) {
        return e->get_id();
    }
    else if (rw.is_mul(e)) {
        if (rw.is_numeral(to_app(e)->get_arg(0)))
            return to_app(e)->get_arg(1)->get_id();
        else
            return e->get_id();
    }
    else if (rw.is_numeral(e)) {
        return -1;
    }
    else if (rw.use_power() && rw.is_power(e) && rw.is_numeral(to_app(e)->get_arg(1), k) && k > rational(1)) {
        return to_app(e)->get_arg(0)->get_id();
    }
    else {
        return e->get_id();
    }
}


template<typename Config>
br_status poly_rewriter<Config>::mk_nflat_add_core(unsigned num_args, expr * const * args, expr_ref & result) {
    mon_lt lt(*this);
    SASSERT(num_args >= 2);
    numeral c;
    unsigned num_coeffs = 0;
    numeral a;
    expr_fast_mark1 visited;  // visited.is_marked(power_product) if the power_product occurs in args
    expr_fast_mark2 multiple; // multiple.is_marked(power_product) if power_product occurs more than once
    bool     has_multiple = false;
    expr *   prev = nullptr;
    bool     ordered  = true;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = args[i];

        if (is_numeral(arg, a)) {
            num_coeffs++;
            c += a;
            ordered = !m_sort_sums || i == 0;
        }
        else if (m_sort_sums && ordered) {
            if (prev != nullptr && lt(arg, prev))
                ordered = false;
            prev = arg;        
        }


        arg = get_power_product(arg);
        if (visited.is_marked(arg)) {
            multiple.mark(arg);
            has_multiple = true;
        }
        else {
            visited.mark(arg);
        }
    }
    normalize(c);
    SASSERT(m_sort_sums || ordered);
    TRACE("rewriter", 
          tout << "ordered: " << ordered << " sort sums: " << m_sort_sums << "\n";
          for (unsigned i = 0; i < num_args; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";);

    if (has_multiple) {
        // expensive case
        buffer<numeral>  coeffs;
        m_expr2pos.reset();
        // compute the coefficient of power products that occur multiple times.
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = args[i];
            if (is_numeral(arg))
                continue;
            expr * pp = get_power_product(arg, a);
            if (!multiple.is_marked(pp))
                continue;
            unsigned pos;
            if (m_expr2pos.find(pp, pos)) {
                coeffs[pos] += a;
            }
            else {
                m_expr2pos.insert(pp, coeffs.size());
                coeffs.push_back(a);
            }
        }
        expr_ref_buffer new_args(m());
        if (!c.is_zero()) {
            new_args.push_back(mk_numeral(c));
        }
        // copy power products with non zero coefficients to new_args
        visited.reset();
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = args[i];
            if (is_numeral(arg))
                continue;
            expr * pp = get_power_product(arg);
            if (!multiple.is_marked(pp)) {
                new_args.push_back(arg);
            }
            else if (!visited.is_marked(pp)) {
                visited.mark(pp);
                unsigned pos = UINT_MAX;
                m_expr2pos.find(pp, pos);
                SASSERT(pos != UINT_MAX);
                a = coeffs[pos];
                normalize(a);
                if (!a.is_zero()) 
                    new_args.push_back(mk_mul_app(a, pp));
            }
        }
        if (m_hoist_cmul) {
            hoist_cmul(new_args);
        }
        else if (m_sort_sums) {
            TRACE("rewriter_bug", tout << "new_args.size(): " << new_args.size() << "\n";);
            if (c.is_zero())
                std::sort(new_args.c_ptr(), new_args.c_ptr() + new_args.size(), mon_lt(*this));
            else
                std::sort(new_args.c_ptr() + 1, new_args.c_ptr() + new_args.size(), mon_lt(*this));
        }
        result = mk_add_app(new_args.size(), new_args.c_ptr());
        TRACE("rewriter", tout << result << "\n";);
        if (hoist_multiplication(result)) {
            return BR_REWRITE_FULL;
        }
        return BR_DONE;
    }
    else {
        SASSERT(!has_multiple);
        if (ordered && !m_hoist_mul && !m_hoist_cmul) {
            if (num_coeffs == 0)
                return BR_FAILED; 
            if (num_coeffs == 1 && is_numeral(args[0], a) && !a.is_zero())
                return BR_FAILED;
        }
        expr_ref_buffer new_args(m());
        if (!c.is_zero())
            new_args.push_back(mk_numeral(c));
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = args[i];
            if (is_numeral(arg))
                continue;
            new_args.push_back(arg);
        }
        if (m_hoist_cmul) {
            hoist_cmul(new_args);
        }
        else if (!ordered) {
            if (c.is_zero())
                std::sort(new_args.c_ptr(), new_args.c_ptr() + new_args.size(), lt);
            else 
                std::sort(new_args.c_ptr() + 1, new_args.c_ptr() + new_args.size(), lt);
    }
        result = mk_add_app(new_args.size(), new_args.c_ptr());        
        if (hoist_multiplication(result)) {
            return BR_REWRITE_FULL;
        }
        return BR_DONE;
    }
}


template<typename Config>
br_status poly_rewriter<Config>::mk_uminus(expr * arg, expr_ref & result) {
    numeral a;
    set_curr_sort(m().get_sort(arg));
    if (is_numeral(arg, a)) {
        a.neg();
        normalize(a);
        result = mk_numeral(a);
        return BR_DONE;
    }
    else {
        result = mk_mul_app(numeral(-1), arg);
        return BR_REWRITE1;
    }
}

template<typename Config>
br_status poly_rewriter<Config>::mk_sub(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args > 0);
    if (num_args == 1) {
        result = args[0];
        return BR_DONE;
    }
    set_curr_sort(m().get_sort(args[0]));
    expr_ref minus_one(mk_numeral(numeral(-1)), m());
    expr_ref_buffer new_args(m());
    new_args.push_back(args[0]);
    for (unsigned i = 1; i < num_args; i++) {
        if (is_zero(args[i])) continue;
        expr * aux_args[2] = { minus_one, args[i] };
        new_args.push_back(mk_mul_app(2, aux_args));
    }
    result = mk_add_app(new_args.size(), new_args.c_ptr());
    return BR_REWRITE2;
}

/**
   \brief Cancel/Combine monomials that occur is the left and right hand sides.
   
   \remark If move = true, then all non-constant monomials are moved to the left-hand-side.
*/
template<typename Config>
br_status poly_rewriter<Config>::cancel_monomials(expr * lhs, expr * rhs, bool move, expr_ref & lhs_result, expr_ref & rhs_result) {
    set_curr_sort(m().get_sort(lhs));
    mon_lt lt(*this);
    unsigned lhs_sz;
    expr * const * lhs_monomials = get_monomials(lhs, lhs_sz);
    unsigned rhs_sz;
    expr * const * rhs_monomials = get_monomials(rhs, rhs_sz);

    expr_fast_mark1 visited;  // visited.is_marked(power_product) if the power_product occurs in lhs or rhs
    expr_fast_mark2 multiple; // multiple.is_marked(power_product) if power_product occurs more than once
    bool     has_multiple = false;

    numeral c(0);
    numeral a;
    unsigned num_coeffs = 0;

    for (unsigned i = 0; i < lhs_sz; i++) {
        expr * arg = lhs_monomials[i];
        if (is_numeral(arg, a)) {
            c += a;
            num_coeffs++;
        }
        else {
            visited.mark(get_power_product(arg));
        }
    }

    if (move && num_coeffs == 0 && is_numeral(rhs)) {
        TRACE("mk_le_bug", tout << "no coeffs\n";);
        return BR_FAILED;
    }

    for (unsigned i = 0; i < rhs_sz; i++) {
        expr * arg = rhs_monomials[i];
        if (is_numeral(arg, a)) {
            c -= a;
            num_coeffs++;
        }
        else {
            expr * pp = get_power_product(arg);
            if (visited.is_marked(pp)) {
                multiple.mark(pp);
                has_multiple = true;
            }
        }
    }

    normalize(c);

    if (!has_multiple && num_coeffs <= 1) {
        if (move) {
            if (is_numeral(rhs)) {
                return BR_FAILED;
            }
        }
        else {
            if (num_coeffs == 0 || is_numeral(rhs)) {
                return BR_FAILED;
            }
        }
    }
    
    buffer<numeral>  coeffs;
    m_expr2pos.reset();
    for (unsigned i = 0; i < lhs_sz; i++) {
        expr * arg = lhs_monomials[i];
        if (is_numeral(arg))
            continue;
        expr * pp = get_power_product(arg, a);
        if (!multiple.is_marked(pp))
            continue;
        unsigned pos;
        if (m_expr2pos.find(pp, pos)) {
            coeffs[pos] += a;
        }
        else {
            m_expr2pos.insert(pp, coeffs.size());
            coeffs.push_back(a);
        }
    }

    for (unsigned i = 0; i < rhs_sz; i++) {
        expr * arg = rhs_monomials[i];
        if (is_numeral(arg))
            continue;
        expr * pp = get_power_product(arg, a);
        if (!multiple.is_marked(pp))
            continue;
        unsigned pos = UINT_MAX;
        m_expr2pos.find(pp, pos);
        SASSERT(pos != UINT_MAX);
        coeffs[pos] -= a;
    }


    ptr_buffer<expr> new_lhs_monomials;
    new_lhs_monomials.push_back(0); // save space for coefficient if needed
    // copy power products with non zero coefficients to new_lhs_monomials
    visited.reset();
    for (unsigned i = 0; i < lhs_sz; i++) {
        expr * arg = lhs_monomials[i];
        if (is_numeral(arg))
            continue;
        expr * pp = get_power_product(arg);
        if (!multiple.is_marked(pp)) {
            new_lhs_monomials.push_back(arg);
        }
        else if (!visited.is_marked(pp)) {
            visited.mark(pp);
            unsigned pos = UINT_MAX;
            m_expr2pos.find(pp, pos);
            SASSERT(pos != UINT_MAX);
            a = coeffs[pos];
            if (!a.is_zero())
                new_lhs_monomials.push_back(mk_mul_app(a, pp));
        }
    }
    
    ptr_buffer<expr> new_rhs_monomials;
    new_rhs_monomials.push_back(0); // save space for coefficient if needed
    for (unsigned i = 0; i < rhs_sz; i++) {
        expr * arg = rhs_monomials[i];
        if (is_numeral(arg))
            continue;
        expr * pp = get_power_product(arg, a);
        if (!multiple.is_marked(pp)) {
            if (move) {
                if (!a.is_zero()) {
                    if (a.is_minus_one()) {
                        new_lhs_monomials.push_back(pp);
                    }
                    else {
                        a.neg();
                        SASSERT(!a.is_one());
                        expr * args[2] = { mk_numeral(a), pp };
                        new_lhs_monomials.push_back(mk_mul_app(2, args));
                    }
                }
            }
            else {
                new_rhs_monomials.push_back(arg);
            }
        }
    }

    bool c_at_rhs = false;
    if (move) {
        if (m_sort_sums) { 
            // + 1 to skip coefficient
            std::sort(new_lhs_monomials.begin() + 1, new_lhs_monomials.end(), lt);
        }
        c_at_rhs = true;
    }
    else if (new_rhs_monomials.size() == 1) { // rhs is empty
        c_at_rhs = true;
    }
    else if (new_lhs_monomials.size() > 1) {
        c_at_rhs = true;
    }

    if (c_at_rhs) {
        c.neg();
        normalize(c);
    }
    // When recreating the lhs and rhs also insert coefficient on the appropriate side.
    // Ignore coefficient if it's 0 and there are no other summands.
    const bool insert_c_lhs = !c_at_rhs && (new_lhs_monomials.size() == 1 || !c.is_zero());
    const bool insert_c_rhs =  c_at_rhs && (new_rhs_monomials.size() == 1 || !c.is_zero());
    const unsigned lhs_offset = insert_c_lhs ? 0 : 1;
    const unsigned rhs_offset = insert_c_rhs ? 0 : 1;
    new_rhs_monomials[0] = insert_c_rhs ? mk_numeral(c) : nullptr;
    new_lhs_monomials[0] = insert_c_lhs ? mk_numeral(c) : nullptr;
    lhs_result = mk_add_app(new_lhs_monomials.size() - lhs_offset, new_lhs_monomials.c_ptr() + lhs_offset);
    rhs_result = mk_add_app(new_rhs_monomials.size() - rhs_offset, new_rhs_monomials.c_ptr() + rhs_offset);
    TRACE("mk_le_bug", tout << lhs_result << " " << rhs_result << "\n";);
    return BR_DONE;
}

#define TO_BUFFER(_tester_, _buffer_, _e_)                       \
    _buffer_.push_back(_e_);                                     \
    for (unsigned _i = 0; _i < _buffer_.size(); ) {                \
        expr* _e = _buffer_[_i];                                  \
        if (_tester_(_e)) {                                      \
            app* a = to_app(_e);                                 \
            _buffer_[_i] = a->get_arg(0);                        \
            for (unsigned _j = 1; _j < a->get_num_args(); ++_j) {       \
                _buffer_.push_back(a->get_arg(_j));                    \
            }                                                   \
        }                                                       \
        else {                                                  \
            ++_i;                                                \
        }                                                       \
    }                                                           \

template<typename Config>
bool poly_rewriter<Config>::hoist_multiplication(expr_ref& som) {
    if (!m_hoist_mul) {
        return false;
    }
    ptr_buffer<expr> adds, muls;
    TO_BUFFER(is_add, adds, som);
    buffer<bool> valid(adds.size(), true);
    obj_map<expr, unsigned> mul_map;
    unsigned j;
    bool change = false;
    for (unsigned k = 0; k < adds.size(); ++k) {
        expr* e = adds[k];
        muls.reset();
        TO_BUFFER(is_mul, muls, e);
        for (unsigned i = 0; i < muls.size(); ++i) {
            e = muls[i];
            if (is_numeral(e)) {
                continue;
            }
            if (mul_map.find(e, j) && valid[j] && j != k) {
                m_curr_sort = m().get_sort(adds[k]);
                adds[j]  = merge_muls(adds[j], adds[k]);
                adds[k]  = mk_numeral(rational(0)); 
                valid[j] = false;
                valid[k] = false;
                change = true;
                break;
            }
            else {
                mul_map.insert(e, k);
            }
        }
    }
    if (!change) {
        return false;
    }
    
    som = mk_add_app(adds.size(), adds.c_ptr());
    
       
    return true;
}

template<typename Config>
expr* poly_rewriter<Config>::merge_muls(expr* x, expr* y) {
    ptr_buffer<expr> m1, m2;
    TO_BUFFER(is_mul, m1, x);
    TO_BUFFER(is_mul, m2, y);
    unsigned k = 0;
    for (unsigned i = 0; i < m1.size(); ++i) {
        x = m1[i];
        bool found = false;
        unsigned j;
        for (j = k; j < m2.size(); ++j) {
            found = m2[j] == x;
            if (found) break;
        }
        if (found) {
            std::swap(m1[i],m1[k]);
            std::swap(m2[j],m2[k]);
            ++k;
        }
    }
    m_curr_sort = m().get_sort(x);
    SASSERT(k > 0);
    SASSERT(m1.size() >= k); 
    SASSERT(m2.size() >= k);
    expr* args[2] = { mk_mul_app(m1.size()-k, m1.c_ptr()+k), 
                      mk_mul_app(m2.size()-k, m2.c_ptr()+k) };
    if (k == m1.size()) {
        m1.push_back(0);
    }
    m1[k] = mk_add_app(2, args);
    return mk_mul_app(k+1, m1.c_ptr());
}

template<typename Config>
bool poly_rewriter<Config>::is_times_minus_one(expr * n, expr* & r) const {
    if (is_mul(n) && to_app(n)->get_num_args() == 2 && is_minus_one(to_app(n)->get_arg(0))) {
        r = to_app(n)->get_arg(1);
        return true;
    }
    return false;
}

/**
   \brief Return true if n is can be put into the form (+ v t) or (+ (- v) t)
   \c inv = true will contain true if (- v) is found, and false otherwise.
*/
template<typename Config>
bool poly_rewriter<Config>::is_var_plus_ground(expr * n, bool & inv, var * & v, expr_ref & t) {
    if (!is_add(n) || is_ground(n))
        return false;
    
    ptr_buffer<expr> args;
    v = nullptr;
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
            args.push_back(arg);
        }
        else if (is_var(arg)) {
            if (v != nullptr)
                return false; // already found variable
            v = to_var(arg);
        }
        else if (is_times_minus_one(arg, neg_arg) && is_var(neg_arg)) {
            if (v != nullptr)
                return false; // already found variable
            v = to_var(neg_arg);
            inv = true;
        }
        else {
            return false; // non ground term.
        }
    }
    if (v == nullptr)
        return false; // did not find variable
    SASSERT(!args.empty());
    mk_add(args.size(), args.c_ptr(), t);
    return true;
}
