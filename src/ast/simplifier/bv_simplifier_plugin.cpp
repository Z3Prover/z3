/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    bv_simplifier_plugin.cpp

Abstract:

    Simplifier for the bv family.

Author:

    Leonardo (leonardo) 2008-01-08
    Nikolaj Bjorner (nbjorner) 2008-01-05
    
--*/
#include"bv_simplifier_plugin.h"
#include"ast_ll_pp.h"
#include"ast_pp.h"
#include"arith_decl_plugin.h"
#include"obj_hashtable.h"
#include"ast_util.h"

bv_simplifier_plugin::~bv_simplifier_plugin() {
    flush_caches();
}

bv_simplifier_plugin::bv_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b, bv_simplifier_params & p):
    poly_simplifier_plugin(symbol("bv"), m, OP_BADD, OP_BMUL, OP_BNEG, OP_BSUB, OP_BV_NUM),
    m_manager(m),
    m_util(m),
    m_arith(m),
    m_bsimp(b),
    m_params(p),
    m_zeros(m) {
}

rational bv_simplifier_plugin::norm(const numeral & n) {
    unsigned bv_size = get_bv_size(m_curr_sort);
    return norm(n, bv_size, false);
}


bool bv_simplifier_plugin::is_numeral(expr * n, rational & val) const { 
    unsigned bv_size;
    return m_util.is_numeral(n, val, bv_size); 
}

expr * bv_simplifier_plugin::get_zero(sort * s) const {
    bv_simplifier_plugin * _this = const_cast<bv_simplifier_plugin*>(this);
    unsigned bv_size = _this->get_bv_size(s);
    if (bv_size >= m_zeros.size())
        _this->m_zeros.resize(bv_size+1);
    if (m_zeros.get(bv_size) == 0)
        _this->m_zeros.set(bv_size, _this->m_util.mk_numeral(rational(0), s));
    return m_zeros.get(bv_size);
}

bool bv_simplifier_plugin::are_numerals(unsigned num_args, expr * const* args, unsigned& bv_size) {
    numeral r;
    if (num_args == 0) {
        return false;
    }
    for (unsigned i = 0; i < num_args; ++i) {
        if (!m_util.is_numeral(args[i], r, bv_size)) {
            return false;
        }
    }
    return true;
}

app * bv_simplifier_plugin::mk_numeral(numeral const & n) { 
    unsigned bv_size = get_bv_size(m_curr_sort);
    return mk_numeral(n, bv_size); 
}

app * bv_simplifier_plugin::mk_numeral(numeral const& n, unsigned bv_size) {
    numeral r = mod(n, rational::power_of_two(bv_size));
    SASSERT(!r.is_neg());
    SASSERT(r < rational::power_of_two(bv_size));
    return m_util.mk_numeral(r, bv_size);
}

bool bv_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    
    SASSERT(f->get_family_id() == m_fid);
    
    bv_op_kind k = static_cast<bv_op_kind>(f->get_decl_kind());
    switch (k) {
    case OP_BV_NUM:    SASSERT(num_args == 0); result = mk_numeral(f->get_parameter(0).get_rational(), f->get_parameter(1).get_int()); break;
    case OP_BIT0:      SASSERT(num_args == 0); result = mk_numeral(0, 1); break;
    case OP_BIT1:      SASSERT(num_args == 0); result = mk_numeral(1, 1); break;
    case OP_BADD:      SASSERT(num_args > 0); 
        mk_add(num_args, args, result); 
        TRACE("bv_add_bug", 
              for (unsigned i = 0; i < num_args; i++) tout << mk_bounded_pp(args[i], m_manager, 10) << "\n";
              tout << mk_bounded_pp(result, m_manager, 10) << "\n";); 
        mk_add_concat(result);              
        break;
    case OP_BSUB:      SASSERT(num_args > 0); mk_sub(num_args, args, result);  break;
    case OP_BNEG:      SASSERT(num_args == 1); mk_uminus(args[0], result);     break;
    case OP_BMUL:      SASSERT(num_args > 0);  mk_mul(num_args, args, result); break;
    case OP_ULEQ:      if (m_presimp) return false; SASSERT(num_args == 2); mk_ule(args[0], args[1], result); break;
    case OP_UGEQ:      if (m_presimp) return false; SASSERT(num_args == 2); mk_ule(args[1], args[0], result); break;
    case OP_ULT:       if (m_presimp) return false; SASSERT(num_args == 2); mk_ult(args[0], args[1], result); break;
    case OP_UGT:       if (m_presimp) return false; SASSERT(num_args == 2); mk_ult(args[1], args[0], result); break;
    case OP_SLEQ:      if (m_presimp) return false; SASSERT(num_args == 2); mk_sle(args[0], args[1], result); break;
    case OP_SGEQ:      if (m_presimp) return false; SASSERT(num_args == 2); mk_sle(args[1], args[0], result); break;
    case OP_SLT:       if (m_presimp) return false; SASSERT(num_args == 2); mk_slt(args[0], args[1], result); break;
    case OP_SGT:       if (m_presimp) return false; SASSERT(num_args == 2); mk_slt(args[1], args[0], result); break;
    case OP_BAND:      SASSERT(num_args > 0); mk_bv_and(num_args, args, result); break;
    case OP_BOR:       SASSERT(num_args > 0); mk_bv_or(num_args, args, result); break;
    case OP_BNOT:      SASSERT(num_args == 1); mk_bv_not(args[0], result); break;
    case OP_BXOR:      SASSERT(num_args > 0); mk_bv_xor(num_args, args, result); break;
    case OP_CONCAT:    SASSERT(num_args > 0); mk_concat(num_args, args, result); break;
    case OP_ZERO_EXT:  
        SASSERT(num_args == 1); SASSERT(f->get_num_parameters() == 1); 
        mk_zeroext(f->get_parameter(0).get_int(), args[0], result);
        break;
    case OP_EXTRACT:
        SASSERT(num_args == 1); SASSERT(f->get_num_parameters() == 2); 
        mk_extract(f->get_parameter(0).get_int(), f->get_parameter(1).get_int(), args[0], result);
        break;
    case OP_REPEAT:
        SASSERT(num_args == 1); SASSERT(f->get_num_parameters() == 1); 
        mk_repeat(f->get_parameter(0).get_int(), args[0], result);
        break;
    case OP_BUREM:
        SASSERT(num_args == 2);
        mk_bv_urem(args[0], args[1], result);
        break;
    case OP_SIGN_EXT:  
        SASSERT(num_args == 1); SASSERT(f->get_num_parameters() == 1);
        mk_sign_extend(f->get_parameter(0).get_int(), args[0], result);
        break;
    case OP_BSHL:      SASSERT(num_args == 2); mk_bv_shl(args[0], args[1], result); break;
    case OP_BLSHR:     SASSERT(num_args == 2); mk_bv_lshr(args[0], args[1], result); break;
    case OP_INT2BV:    SASSERT(num_args == 1); mk_int2bv(args[0], f->get_range(), result); break;
    case OP_BV2INT:    SASSERT(num_args == 1); mk_bv2int(args[0], f->get_range(), result); break;
    case OP_BSDIV:     SASSERT(num_args == 2); mk_bv_sdiv(args[0], args[1], result);  break;
    case OP_BUDIV:     SASSERT(num_args == 2); mk_bv_udiv(args[0], args[1], result);  break;
    case OP_BSREM:     SASSERT(num_args == 2); mk_bv_srem(args[0], args[1], result);  break;
    case OP_BSMOD:     SASSERT(num_args == 2); mk_bv_smod(args[0], args[1], result);  break;
    case OP_BNAND:     SASSERT(num_args > 0); mk_bv_nand(num_args, args, result);  break;
    case OP_BNOR:      SASSERT(num_args > 0); mk_bv_nor(num_args, args, result);  break;
    case OP_BXNOR:     SASSERT(num_args > 0); mk_bv_xnor(num_args, args, result);  break;
    case OP_ROTATE_LEFT:  SASSERT(num_args == 1); mk_bv_rotate_left(f, args[0], result); break;
    case OP_ROTATE_RIGHT: SASSERT(num_args == 1); mk_bv_rotate_right(f, args[0], result); break;
    case OP_EXT_ROTATE_LEFT: SASSERT(num_args == 2); mk_bv_ext_rotate_left(args[0], args[1], result); break;
    case OP_EXT_ROTATE_RIGHT: SASSERT(num_args == 2); mk_bv_ext_rotate_right(args[0], args[1], result); break;
    case OP_BREDOR:    SASSERT(num_args == 1); mk_bv_redor(args[0], result); break;
    case OP_BREDAND:   SASSERT(num_args == 1); mk_bv_redand(args[0], result); break;
    case OP_BCOMP:     SASSERT(num_args == 2); mk_bv_comp(args[0], args[1], result); break;
    case OP_BASHR:     SASSERT(num_args == 2); mk_bv_ashr(args[0], args[1], result); break;
    case OP_BSDIV_I:   SASSERT(num_args == 2); mk_bv_sdiv_i(args[0], args[1], result);  break;
    case OP_BUDIV_I:   SASSERT(num_args == 2); mk_bv_udiv_i(args[0], args[1], result);  break;
    case OP_BSREM_I:   SASSERT(num_args == 2); mk_bv_srem_i(args[0], args[1], result);  break;
    case OP_BUREM_I:   SASSERT(num_args == 2); mk_bv_urem_i(args[0], args[1], result);  break;
    case OP_BSMOD_I:   SASSERT(num_args == 2); mk_bv_smod_i(args[0], args[1], result);  break;
    case OP_BSDIV0:
    case OP_BUDIV0:
    case OP_BSREM0:
    case OP_BUREM0:
    case OP_BSMOD0:
    case OP_BIT2BOOL:
    case OP_CARRY:
    case OP_XOR3:
    case OP_MKBV:
    case OP_BUMUL_NO_OVFL:
    case OP_BSMUL_NO_OVFL:
    case OP_BSMUL_NO_UDFL:
        result = m_manager.mk_app(f, num_args, args);
        break;        
    default:
        UNREACHABLE();
        break;
    }
    SASSERT(result.get());

    TRACE("bv_simplifier", 
          tout << mk_pp(f, m_manager) << "\n";
          for (unsigned i = 0; i < num_args; ++i) {
              tout << mk_pp(args[i], m_manager) << " ";
          }
          tout << "\n";
          tout << mk_pp(result.get(), m_manager) << "\n";
          );

    return true;
}

bool bv_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {    
    set_reduce_invoked();

    if (m_presimp)
        return false;
    expr_ref tmp(m_manager);
    tmp = m_manager.mk_eq(lhs,rhs);
    mk_bv_eq(lhs, rhs, result);
    return result.get() != tmp.get();
}

bool bv_simplifier_plugin::reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result) { 
    set_reduce_invoked();

    return false;
}

void bv_simplifier_plugin::flush_caches() { 
    TRACE("extract_cache", tout << "flushing extract cache...\n";);
    extract_cache::iterator it  = m_extract_cache.begin();
    extract_cache::iterator end = m_extract_cache.end();
    for (; it != end; ++it) {
        extract_entry & e = (*it).m_key;
        m_manager.dec_ref(e.m_arg);
        m_manager.dec_ref((*it).m_value);
    }
    m_extract_cache.reset();
}


inline uint64 bv_simplifier_plugin::to_uint64(const numeral & n, unsigned bv_size) {
    SASSERT(bv_size <= 64);
    numeral tmp = n;
    if (tmp.is_neg()) {
        tmp = mod(tmp, rational::power_of_two(bv_size));
    }
    SASSERT(tmp.is_nonneg());
    SASSERT(tmp.is_uint64());
    return tmp.get_uint64();
}

#define MK_BV_OP(_oper_,_binop_) \
rational bv_simplifier_plugin::mk_bv_ ## _oper_(numeral const& a0, numeral const& b0, unsigned sz) { \
    rational r(0), a(a0), b(b0); \
    numeral p64 = rational::power_of_two(64); \
    numeral mul(1); \
    while (sz > 0) { \
        numeral a1 = a % p64; \
        numeral b1 = b % p64; \
        uint64 u = a1.get_uint64() _binop_ b1.get_uint64(); \
        if (sz < 64) { \
            uint64 mask = shift_left(1ull,(uint64)sz) - 1ull; \
            u = mask & u; \
        } \
        r += mul*rational(u,rational::ui64()); \
        mul *= p64; \
        a = div(a, p64); \
        b = div(b, p64); \
        sz -= (sz<64)?sz:64; \
    } \
    return r; \
}

MK_BV_OP(and,&)
MK_BV_OP(or,|)
MK_BV_OP(xor,^)

rational bv_simplifier_plugin::mk_bv_not(numeral const& a0, unsigned sz) { 
    rational r(0), a(a0), mul(1);
    numeral p64 = rational::power_of_two(64); 
    while (sz > 0) { 
        numeral a1 = a % p64; 
        uint64 u = ~a1.get_uint64();
        if (sz < 64) { 
            uint64 mask = shift_left(1ull,(uint64)sz) - 1ull; 
            u = mask & u; 
        } 
        r += mul*rational(u,rational::ui64()); 
        mul *= p64; 
        a = div(a, p64); 
        sz -= (64<sz)?64:sz; 
    } 
    return r; 
}


void bv_simplifier_plugin::mk_ule(expr* a, expr* b, expr_ref& result) {
    mk_leq_core(false, a, b, result);
}

void bv_simplifier_plugin::mk_ult(expr* a, expr* b, expr_ref& result) {
    expr_ref tmp(m_manager);
    mk_leq_core(false, b, a, tmp);
    m_bsimp.mk_not(tmp.get(), result);
}

void bv_simplifier_plugin::mk_sle(expr* a, expr* b, expr_ref& result) {
    mk_leq_core(true, a, b, result);
}

void bv_simplifier_plugin::mk_slt(expr* a, expr* b, expr_ref& result) {
    expr_ref tmp(m_manager);
    mk_leq_core(true, b, a, tmp);
    m_bsimp.mk_not(tmp.get(), result);
}

void bv_simplifier_plugin::mk_leq_core(bool is_signed, expr * arg1, expr * arg2, expr_ref & result) {
    numeral r1, r2, r3;
    bool is_num1     = is_numeral(arg1, r1);
    bool is_num2     = is_numeral(arg2, r2);
    decl_kind k      = is_signed ? OP_SLEQ : OP_ULEQ;
    unsigned bv_size = get_bv_size(arg1);

    if (is_num1) {
        r1 = norm(r1, bv_size, is_signed);
    }
    if (is_num2) {
        r2 = norm(r2, bv_size, is_signed);
    }

    if (is_num1 && is_num2) {
        result = r1 <= r2 ? m_manager.mk_true() : m_manager.mk_false();
        return;
    }

    numeral lower, upper;

    if (is_num1 || is_num2) {
        if (is_signed) {
            lower = - rational::power_of_two(bv_size - 1);
            upper =   rational::power_of_two(bv_size - 1) - numeral(1);
        }
        else {
            lower = numeral(0);
            upper = rational::power_of_two(bv_size) - numeral(1);
        }
    }

    if (is_num2) {
        if (r2 == lower) {
            m_bsimp.mk_eq(arg1, arg2, result);
            return;
        }
        if (r2 == upper) {
            result = m_manager.mk_true();
            return;
        }
    }

    if (is_num1) {
        // 0 <= arg2 is true
        if (r1 == lower) {
            result = m_manager.mk_true();
            return;
        }

        // 2^n-1 <= arg2 is arg1 = arg2
        if (r1 == upper) {
            m_bsimp.mk_eq(arg1, arg2, result);
            return;
        }
    }

    //
    // In general, we can use lexicographic extensions of concat.
    // But this does not always turn into savings.
    // Only apply the simplification if arg1 is a numeral.
    // 
    if (is_num1 && !is_signed && m_util.is_concat(arg2) && to_app(arg2)->get_num_args() == 2) {
        // 
        // c <=_u (concat 0 a) <=> c[u:l] = 0 && c[l-1:0] <=_u a
        //
        app* app = to_app(arg2);
        expr * arg2_1 = app->get_arg(0);
        expr * arg2_2 = app->get_arg(1);
        if (m_util.is_zero(arg2_1)) {
            unsigned sz1   = get_bv_size(arg2_1);
            unsigned sz2   = get_bv_size(arg2_2);
            
            expr_ref tmp1(m_manager);
            expr_ref tmp2(m_manager);
            mk_extract(sz2 + sz1 - 1, sz2, arg1, tmp1);
            mk_extract(sz2 - 1, 0, arg1, tmp2);
            
            expr_ref eq(m_manager);
            expr_ref zero(m_manager);
            zero = mk_bv0(sz1);
            mk_bv_eq(tmp1.get(), zero, eq);
            
            expr_ref ineq(m_manager);
            ineq = m_util.mk_ule(tmp2.get(), arg2_2);
            
            m_bsimp.mk_and(eq.get(), ineq.get(), result);
            return;
        }
    }

    //
    // TODO: 
    // Others:
    //
    // k <=_s (concat 0 a) <=> (k[u:l] = 0 && k[l-1:0] <=_u a) || k[u:u] = bv1
    //
    // (concat 0 a) <=_s k <=> k[u:u] = bv0 && (k[u:l] != 0 || a <=_u k[l-1:0])
    //
    // (concat 0 a) <=_u k <=> k[u:l] != 0 || a <=_u k[l-1:0]
    //

    result = m_manager.mk_app(m_fid, k, arg1, arg2);
}

void bv_simplifier_plugin::mk_extract(unsigned high, unsigned low, expr* arg, expr_ref& result) {
    
    unsigned arg_sz = get_bv_size(arg);
    unsigned sz     = high - low + 1;
    TRACE("bv_simplifier_plugin", tout << "mk_extract [" << high << ":" << low << "]\n";
          tout << "arg_sz: " << arg_sz << " sz: " << sz << "\n";
          tout << "arg:\n";
          ast_ll_pp(tout, m_manager, arg););    

    if (arg_sz == sz) {
        result = arg;
    }
    else {
        mk_extract_core(high, low, arg, result);
    }
    if (m_extract_cache.size() > (1 << 12)) {
        m_extract_cache.reset();
    }

    TRACE("bv_simplifier_plugin", tout << "mk_extract [" << high << ":" << low << "]\n";
          tout << "arg_sz: " << arg_sz << " sz: " << sz << "\n";
          tout << "arg:\n";
          ast_ll_pp(tout, m_manager, arg);
          tout << "=====================>\n";
          ast_ll_pp(tout, m_manager, result.get()););
}


void bv_simplifier_plugin::cache_extract(unsigned h, unsigned l, expr * arg, expr * result) {
    m_manager.inc_ref(arg); 
    m_manager.inc_ref(result);
    m_extract_cache.insert(extract_entry(h, l, arg), result);
}

expr* bv_simplifier_plugin::get_cached_extract(unsigned h, unsigned l, expr * arg) {
    expr * result = 0;
    if (m_extract_cache.find(extract_entry(h, l, arg), result)) {
        return result;
    }
    return 0;
}


void bv_simplifier_plugin::mk_extract_core(unsigned high, unsigned low, expr * arg, expr_ref& result) {
    
    if (!lookup_mk_extract(high, low, arg, result)) {
        while (!m_extract_args.empty()) {
            unsigned low2 = m_lows.back();
            unsigned high2 = m_highs.back();
            expr* arg2 = m_extract_args.back();
            if (try_mk_extract(high2, low2, arg2, result)) {
                if (!m_extract_cache.contains(extract_entry(high2, low2, arg2))) {
                    cache_extract(high2, low2, arg2, result.get());
                }
                m_lows.pop_back();
                m_highs.pop_back();
                m_extract_args.pop_back();
            }
        }
        if (!lookup_mk_extract(high, low, arg, result)) {
            UNREACHABLE();
        }
    }
}


bool bv_simplifier_plugin::lookup_mk_extract(unsigned high, unsigned low, expr * arg, expr_ref& result) {
    expr* cached_result = get_cached_extract(high, low, arg);
    if (cached_result) {
        result = cached_result;
        return true;
    }

    m_extract_args.push_back(arg);
    m_lows.push_back(low);
    m_highs.push_back(high);
    return false;
}


bool bv_simplifier_plugin::try_mk_extract(unsigned high, unsigned low, expr * arg, expr_ref& result) {

    SASSERT(low <= high);
    unsigned arg_sz = get_bv_size(arg);
    unsigned sz     = high - low + 1;
    numeral r;
    unsigned num_bits;

    if (arg_sz == sz) {
        result = arg;
        return true;
    }

    expr* cached_result = get_cached_extract(high, low, arg);
    if (cached_result) {
        result = cached_result;
        return true;
    }    

    if (!is_app(arg)) {
        result = m_util.mk_extract(high, low, arg);
        return true;
    }
    app* a = to_app(arg);

    if (m_util.is_numeral(a, r, num_bits)) {
        if (r.is_neg()) {
            r = mod(r, rational::power_of_two(sz));
        }
        SASSERT(r.is_nonneg());
        if (r.is_uint64()) {
            uint64 u     = r.get_uint64();
            uint64 e     = shift_right(u, low) & (shift_left(1ull, sz) - 1ull);
            TRACE("mk_extract_bug", tout << u << "[" << high << ":" << low << "] " << e << " (u >> low): " << shift_right(u, low) << " (1ull << sz): " 
                  << shift_left(1ull, sz) << " ((1ull << sz) - 1ull)" << (shift_left(1ull, sz) - 1ull) << "\n";);
            result = mk_numeral(numeral(e, numeral::ui64()), sz);
            return true;
        }
        result = mk_numeral(div(r, rational::power_of_two(low)), sz);
        return true;
    }
    // (extract[high:low] (extract[high2:low2] x)) == (extract[high+low2 : low+low2] x)
    else if (is_app_of(a, m_fid, OP_EXTRACT)) {
        expr * x = a->get_arg(0);
        unsigned low2 = a->get_decl()->get_parameter(1).get_int();
        return lookup_mk_extract(high + low2, low + low2, x, result);
    }
    //
    // (extract[hi:lo] (bvXshr A c:bv[n])) -> (extract[hi+c:lo+c] A) 
    //   if c < n, c <= lo <= hi < n - c
    //
    else if ((is_app_of(a, m_fid, OP_BASHR) || is_app_of(a, m_fid, OP_BLSHR)) &&
             is_numeral(a->get_arg(1), r) && r.is_unsigned()) {
        unsigned c = r.get_unsigned();
        unsigned bv_size = get_bv_size(a);
        if (c < bv_size && c <= low && high < bv_size - c) {
            return lookup_mk_extract(high+c, low+c, a->get_arg(0), result);
        }
    }
    // (concat a_0 ... a_{n-1})
    // Remark: the least significant bits are stored in a_{n-1}
    else if (is_app_of(a, m_fid, OP_CONCAT)) {
        expr_ref_buffer new_args(m_manager);
        unsigned i = a->get_num_args();
        // look for first argument
        while (i > 0) {
            --i;
            expr * a_i     = a->get_arg(i);
            unsigned a_sz = get_bv_size(a_i);
            TRACE("extract_bug", tout << "FIRST a_sz: " << a_sz << " high: " << high << " low: " << low << "\n" <<
                  mk_pp(a_i, m_manager) << "\n";);
            if (a_sz <= low) {
                low  -= a_sz;
                high -= a_sz;
            }
            else {
                // found first argument
                if (a_sz <= high) {
                    expr_ref new_arg(m_manager);
                    if (!lookup_mk_extract(a_sz - 1, low, a_i, new_arg)) {
                        return false;
                    }
                    new_args.push_back(new_arg.get());
                    unsigned num_consumed_bytes = a_sz - low;
                    // I have to apply extract[sz - num_consumed_bytes - 1, 0] on the rest of concat
                    high = (sz - num_consumed_bytes - 1);
                    break;
                }
                else {
                    return lookup_mk_extract(high, low, a_i, result);
                }
            }
        }
        TRACE("extract_bug", tout << " high: " << high << " low: " << low << "\n";);
        
        // look for remaining arguments
        while (i > 0) {
            --i;
            expr * a_i     = a->get_arg(i);
            unsigned a_sz = get_bv_size(a_i);
            TRACE("extract_bug", tout << "SECOND a_sz: " << a_sz << " high: " << high << " " << 
                  mk_pp( a_i, m_manager) << "\n";);
            if (a_sz <= high) {
                high  -= a_sz;
                new_args.push_back(a_i);
            }
            else {
                // found last argument
                expr_ref new_arg(m_manager);
                if (!lookup_mk_extract(high, 0, a_i, new_arg)) {
                    return false;
                }
                new_args.push_back(new_arg.get());
                // The arguments in new_args are in reverse order.
                ptr_buffer<expr> rev_new_args;
                unsigned i = new_args.size();
                while (i > 0) {
                    --i;
                    rev_new_args.push_back(new_args[i]);
                }
                mk_concat(rev_new_args.size(), rev_new_args.c_ptr(), result);
                return true;
            }
        }
        UNREACHABLE();
    }
    else if (is_app_of(a, m_fid, OP_SIGN_EXT)) {
        SASSERT(a->get_num_args() == 1);
        unsigned bv_size = get_bv_size(a->get_arg(0));
        if (high < bv_size) {
            return lookup_mk_extract(high, low, a->get_arg(0), result);
        }
    }
    else if (is_app_of(a, m_fid, OP_BAND) ||
             is_app_of(a, m_fid, OP_BOR) ||
             is_app_of(a, m_fid, OP_BXOR) ||
             is_app_of(a, m_fid, OP_BNOR) ||
             is_app_of(a, m_fid, OP_BNAND) ||
             is_app_of(a, m_fid, OP_BNOT) ||
             (low == 0 && is_app_of(a, m_fid, OP_BADD)) ||
             (low == 0 && is_app_of(a, m_fid, OP_BMUL)) ||
             (low == 0 && is_app_of(a, m_fid, OP_BSUB))) {
        expr_ref_buffer new_args(m_manager);
        bool all_found = true;
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            expr_ref new_arg(m_manager);
            if (!lookup_mk_extract(high, low, a->get_arg(i), new_arg)) {
                all_found = false;
            }
            new_args.push_back(new_arg.get());
        }
        if (!all_found) {
            return false;
        }
        // We should not use mk_app because it does not guarantee that the result would be in simplified form.
        // result = m_manager.mk_app(m_fid, a->get_decl_kind(), new_args.size(), new_args.c_ptr());
        if (is_app_of(a, m_fid, OP_BAND))
            mk_bv_and(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BOR))
            mk_bv_or(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BXOR))
            mk_bv_xor(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BNOR))
            mk_bv_nor(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BNAND))
            mk_bv_nand(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BNOT)) {
            SASSERT(new_args.size() == 1);
            mk_bv_not(new_args[0], result);
        }
        else if (is_app_of(a, m_fid, OP_BADD))
            mk_add(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BMUL))
            mk_mul(new_args.size(), new_args.c_ptr(), result);
        else if (is_app_of(a, m_fid, OP_BSUB))
            mk_sub(new_args.size(), new_args.c_ptr(), result);
        else {
            UNREACHABLE();
        }
        return true;
    }
    else if (m_manager.is_ite(a)) {
        expr_ref then_b(m_manager), else_b(m_manager);
        bool ok = lookup_mk_extract(high, low, a->get_arg(1), then_b);
        ok = lookup_mk_extract(high, low, a->get_arg(2), else_b) && ok;
        if (ok) {
            m_bsimp.mk_ite(a->get_arg(0), then_b.get(), else_b.get(), result);
        }
        return ok;
    }
    result = m_util.mk_extract(high, low, arg);
    return true;
}

/**
   \brief Let f be the operator fid:k. Then, this function
   store in result the flat args of n. If n is not an f application, then store n in result.

   Example: if n is (f (f a b) (f c (f d e))), then a b c d e are stored in result.
*/
template<typename T>
void get_assoc_args(family_id fid, decl_kind k, expr * n, T & result) {
    ptr_buffer<expr> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        expr * n = todo.back();
        todo.pop_back();
        if (is_app_of(n, fid, k)) {
            app * app = to_app(n);
            unsigned    i   = app->get_num_args();
            while (i > 0) {
                --i;
                todo.push_back(app->get_arg(i));
            }
        }
        else {
            result.push_back(n);
        }
    }
}

/**
   \brief Similar to get_assoc_args, but the arguments are stored in reverse
   other in result.
*/
template<typename T>
void get_inv_assoc_args(family_id fid, decl_kind k, expr * n, T & result) {
    ptr_buffer<expr> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        expr * n = todo.back();
        todo.pop_back();
        if (is_app_of(n, fid, k)) {
            app * app     = to_app(n);
            unsigned  num = app->get_num_args();
            for (unsigned i = 0; i < num; i++) 
                todo.push_back(app->get_arg(i));
        }
        else {
            result.push_back(n);
        }
    }
}

void bv_simplifier_plugin::mk_bv_eq(expr* a1, expr* a2, expr_ref& result) {
    
    rational val1;
    rational val2;
    bool is_num1 = is_numeral(a1, val1);
    bool is_num2 = is_numeral(a2, val2);
    if (is_num1 && is_num2 && val1 != val2) {
        result = m_manager.mk_false();
        return;
    }

    if (!m_util.is_concat(a1) && !is_num1) {
        mk_eq_core(a1, a2, result);
        return;
    }
    if (!m_util.is_concat(a2) && !is_num2) {
        mk_eq_core(a1, a2, result);
        return;
    }
    
    ptr_buffer<expr> args1, args2;
    get_inv_assoc_args(m_fid, OP_CONCAT, a1, args1);
    get_inv_assoc_args(m_fid, OP_CONCAT, a2, args2);
    TRACE("mk_bv_eq_concat", tout << mk_ll_pp(a1, m_manager) << "\n" << mk_ll_pp(a2, m_manager) << "\n";
          tout << "args1:\n";
          for (unsigned i = 0; i < args1.size(); i++) tout << mk_ll_pp(args1[i], m_manager) << "\n";
          tout << "args2:\n";
          for (unsigned i = 0; i < args2.size(); i++) tout << mk_ll_pp(args2[i], m_manager) << "\n";);

          

    expr_ref lhs(m_manager), rhs(m_manager), eq(m_manager);
    expr_ref_buffer eqs(m_manager);
    unsigned low1 = 0, low2 = 0;
    ptr_buffer<expr>::iterator it1  = args1.begin();
    ptr_buffer<expr>::iterator end1 = args1.end();
    ptr_buffer<expr>::iterator it2  = args2.begin();
    ptr_buffer<expr>::iterator end2 = args2.end();

    while (it1 != end1 && it2 != end2) {
        SASSERT(it1 != end1);
        SASSERT(it2 != end2);
        expr * arg1    = *it1;
        expr * arg2    = *it2;
        TRACE("expr_bv_util", tout << "low1: " << low1 << " low2: " << low2 << "\n";
              tout << mk_pp(arg1, m_manager) << "\n";
              tout << mk_pp(arg2, m_manager) << "\n";);
        unsigned sz1  = get_bv_size(arg1);
        unsigned sz2  = get_bv_size(arg2);
        SASSERT(low1 < sz1 && low2 < sz2);
        unsigned rsz1 = sz1 - low1;
        unsigned rsz2 = sz2 - low2;
        TRACE("expr_bv_util", tout << "rsz1: " << rsz1 << " rsz2: " << rsz2 << "\n";
              tout << mk_pp(arg1, m_manager) << "\n";
              tout << mk_pp(arg2, m_manager) << "\n";);

        if (rsz1 == rsz2) {
            mk_extract(sz1 - 1, low1, arg1, lhs);
            mk_extract(sz2 - 1, low2, arg2, rhs);
            low1 = 0;
            low2 = 0;
            ++it1;
            ++it2;
        }
        else if (rsz1 < rsz2) {
            mk_extract(sz1  - 1, low1, arg1, lhs);
            mk_extract(rsz1 + low2 - 1, low2, arg2, rhs);
            low1  = 0;
            low2 += rsz1; 
            ++it1;
        }
        else {
            mk_extract(rsz2 + low1 - 1, low1, arg1, lhs);
            mk_extract(sz2  - 1, low2, arg2, rhs);
            low1 += rsz2;
            low2  = 0;
            ++it2;
        }
        mk_eq_core(lhs.get(), rhs.get(), eq);
        eqs.push_back(eq.get());
    }
    m_bsimp.mk_and(eqs.size(), eqs.c_ptr(), result);
}

void bv_simplifier_plugin::mk_eq_core(expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("mk_eq_core", ast_ll_pp(tout, m_manager, arg1 ); ast_ll_pp(tout, m_manager, arg2););
    if (arg1 == arg2) {
        result = m_manager.mk_true();
        return;
    }
    if ((m_util.is_bv_and(arg1) && m_util.is_allone(arg2)) || (m_util.is_bv_or(arg1) && m_util.is_zero(arg2))) {
        mk_args_eq_numeral(to_app(arg1), arg2, result);
        return;
    }
    if ((m_util.is_bv_and(arg2) && m_util.is_allone(arg1)) || (m_util.is_bv_or(arg2) && m_util.is_zero(arg1))) {
        mk_args_eq_numeral(to_app(arg2), arg1, result);
        return;
    }

#if 1
    rational r;
    unsigned num_bits = 0;
    if (m_util.is_numeral(arg2, r, num_bits)) {
        std::swap(arg1, arg2);
    }
    
    if (m_util.is_numeral(arg1, r, num_bits) &&
        (m_util.is_bv_and(arg2) || m_util.is_bv_or(arg2) || m_util.is_bv_not(arg2))) {
        rational two(2);
        expr_ref tmp(m_manager);
        expr_ref_vector tmps(m_manager);
        for (unsigned i = 0; i < num_bits; ++i) {
            bool is_neg = (r % two).is_zero();
            bit2bool_simplify(i, arg2, tmp);
            if (is_neg) {
                expr_ref tmp2(m_manager);
                m_bsimp.mk_not(tmp, tmp2);
                tmp = tmp2;
            }
            tmps.push_back(tmp);
            r = div(r, two);
        }        
        m_bsimp.mk_and(tmps.size(), tmps.c_ptr(), result);
        TRACE("mk_eq_bb", 
              tout << mk_pp(arg1, m_manager) << "\n";
              tout << mk_pp(arg2, m_manager) << "\n";
              tout << mk_pp(result, m_manager) << "\n";);
        return;
    }
#endif

    if (!m_util.is_bv_add(arg1) && !m_util.is_bv_add(arg2) && 
        !m_util.is_bv_mul(arg1) && !m_util.is_bv_mul(arg2)) {
        m_bsimp.mk_eq(arg1, arg2, result);
        return;
    }
    
    set_curr_sort(arg1);
    expr_ref_vector args1(m_manager);
    expr_ref_vector args2(m_manager);
    get_assoc_args(m_fid, OP_BADD, arg1, args1);
    get_assoc_args(m_fid, OP_BADD, arg2, args2);
    TRACE("mk_eq_core",
          tout << mk_pp(arg1, m_manager) << "\n" << mk_pp(arg2, m_manager) << "\n";
          tout << args1.size() << " " << args2.size() << "\n";);

    unsigned idx2 = 0;
    while (idx2 < args2.size()) {
        expr * m2 = args2.get(idx2);
        unsigned sz1  = args1.size();
        unsigned idx1 = 0;
        for (; idx1 < sz1; ++idx1) {
            expr * m1 = args1.get(idx1);
            if (eq_monomials_modulo_k(m1, m2)) {
                expr_ref tmp(m_manager);
                if (merge_monomials(true, m1, m2, tmp)) {
                    args1.set(idx1, tmp.get());
                }
                else {
                    // the monomial cancelled each other.
                    args1.erase(idx1);
                }
                break;
            }
        }
        if (idx1 == sz1) {
            ++idx2;
        }
        else {
            args2.erase(idx2);
        }
    }

    expr_ref lhs(m_manager);
    expr_ref rhs(m_manager);
    mk_sum_of_monomials(args1, lhs);
    mk_sum_of_monomials(args2, rhs);
    m_bsimp.mk_eq(lhs.get(), rhs.get(), result);
}

void bv_simplifier_plugin::mk_args_eq_numeral(app * app, expr * n, expr_ref & result) {
    expr_ref_buffer eqs(m_manager);
    expr_ref eq(m_manager);
    unsigned num = app->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        mk_bv_eq(app->get_arg(i), n, eq);
        eqs.push_back(eq.get());
    }
    m_bsimp.mk_and(eqs.size(), eqs.c_ptr(), result);
}

void bv_simplifier_plugin::mk_concat(unsigned num_args, expr * const * args, expr_ref & result) {
    TRACE("bv_simplifier_plugin", tout << "mk_concat:\n";
          for (unsigned i = 0; i < num_args; i++) ast_ll_pp(tout, m_manager, args[i]););
    unsigned shift = 0;
    numeral  val(0), arg_val;
    for (unsigned i = num_args; i > 0; ) {
        --i;
        expr * arg   = args[i];
        if (is_numeral(arg, arg_val)) {
            arg_val    *= rational::power_of_two(shift);
            val        += arg_val;
            shift      += get_bv_size(arg);
            TRACE("bv_simplifier_plugin", 
                  tout << "val: " << val << " arg_val: " << arg_val << " shift: " << shift << "\n";);
        }
        else {
            // one of the arguments is not a number 
            result = m_manager.mk_app(m_fid, OP_CONCAT, num_args, args);
            return;
        }
    }
    
    // all arguments are numerals
    result = mk_numeral(val, shift);
}

void bv_simplifier_plugin::mk_bv_and(unsigned num_args, expr * const* args, expr_ref & result) {
    ptr_buffer<expr> flat_args;
    for (unsigned i = 0; i < num_args; ++i) {
        flat_args.push_back(args[i]);
    }
    // expr_lt_proc is a total order on expressions.
    std::sort(flat_args.begin(), flat_args.end(), expr_lt_proc(m_fid, OP_BNOT));
    SASSERT(num_args > 0);

    unsigned bv_size = get_bv_size(args[0]);

    numeral allone = mk_allone(bv_size);
    numeral val;

    uint64 unit = bv_size <= 64 ? to_uint64(numeral(-1), bv_size) : 0;
    numeral n_unit(allone);
 
    expr * prev  = 0;
    ptr_buffer<expr>::iterator it  = flat_args.begin();
    ptr_buffer<expr>::iterator it2 = it;
    ptr_buffer<expr>::iterator end = flat_args.end();
    for (; it != end; ++it) {
        expr* n = *it;
        if (prev && 
            ((is_app_of(n, m_fid, OP_BNOT)    && to_app(n)->get_arg(0) == prev) ||
             (is_app_of(prev, m_fid, OP_BNOT) && to_app(prev)->get_arg(0) == n))) {
            result = mk_bv0(bv_size);
            return;
        }
        else if (bv_size <= 64 && is_numeral(n, val)) {
            unit &= to_uint64(val, bv_size);
            if (unit == 0) {
                result = mk_bv0(bv_size);
                return;
            }
        }
        else if (bv_size > 64 && is_numeral(n, val)) {
            n_unit = mk_bv_and(val, n_unit, bv_size);
            if (n_unit.is_zero()) {
                result = mk_bv0(bv_size);
                return;
            }
        }
        else if (!prev || prev != n) {
            *it2 = n;
            prev = *it2;
            ++it2;
        }
    }

    if (bv_size <= 64) {
        n_unit = numeral(unit, numeral::ui64());
    }

    flat_args.set_end(it2);
    if (n_unit != allone) {
        flat_args.push_back(mk_numeral(n_unit, bv_size));
    }

    unsigned sz = flat_args.size();
    switch(sz) {
    case 0:
        result = mk_numeral(n_unit, bv_size);
        break;
    case 1:
        result = flat_args.back();
        break;
    default:
        result = mk_list_assoc_app(m_manager, m_fid, OP_BAND, sz, flat_args.c_ptr());
        break;
    }
}

void bv_simplifier_plugin::mk_bv_or(unsigned num_args, expr * const* args, expr_ref & result) {
#if 0
    // Transformations for SAGE
    // (bvor (concat 0 x) (concat y 0)) ==> (concat y x)
    // (bvor (concat x 0) (concat 0 y)) ==> (concat x y)
    if (num_args == 2 && 
        m_util.is_concat(args[0]) && 
        m_util.is_concat(args[1]) &&
        to_app(args[0])->get_num_args() == 2 && 
        to_app(args[1])->get_num_args() == 2) {
        expr * x1 = to_app(args[0])->get_arg(0);
        expr * x2 = to_app(args[0])->get_arg(1);
        expr * y1 = to_app(args[1])->get_arg(0);
        expr * y2 = to_app(args[1])->get_arg(1);
        if (get_bv_size(x1) == get_bv_size(y1) && 
            get_bv_size(x2) == get_bv_size(y2)) {
            if (m_util.is_zero(x1) && m_util.is_zero(y2)) {
                // (bvor (concat 0 x) (concat y 0)) ==> (concat y x)
                mk_concat(y1, x2, result);
                return;
            }
            if (m_util.is_zero(x2) && m_util.is_zero(y1)) {
                // (bvor (concat x 0) (concat 0 y)) ==> (concat x y)
                mk_concat(x1, y2, result);
                return;
            }
        }
    }
    // Investigate why it did not work.
#endif        

    ptr_buffer<expr> flat_args;
    for (unsigned i = 0; i < num_args; ++i) {
        flat_args.push_back(args[i]);
    }
    std::sort(flat_args.begin(), flat_args.end(), expr_lt_proc(m_fid, OP_BNOT));
    SASSERT(num_args > 0);

    unsigned bv_size = get_bv_size(args[0]), sz;
    numeral allone = mk_allone(bv_size);
    numeral val;

    uint64 unit = 0;
    numeral n_unit(0);

    expr * prev  = 0;
    ptr_buffer<expr>::iterator it  = flat_args.begin();
    ptr_buffer<expr>::iterator it2 = it;
    ptr_buffer<expr>::iterator end = flat_args.end();
    for (; it != end; ++it) {
        expr* n = *it;
        if (prev && 
            ((is_app_of(n, m_fid, OP_BNOT)  && to_app(n)->get_arg(0) == prev) ||
             (is_app_of(prev, m_fid, OP_BNOT) && to_app(prev)->get_arg(0) == n))) {
            result = mk_numeral(allone, bv_size);
            return;
        }
        else if (bv_size <= 64 && is_numeral(n, val)) {
            unit |= to_uint64(val, bv_size);
        }
        else if (bv_size > 64 && is_numeral(n, val)) {
            n_unit = mk_bv_or(val, n_unit, bv_size);
        }
        else if (!prev || prev != n) {
            *it2 = n;
            prev = *it2;
            ++it2;
        }
    }

    if (bv_size <= 64) {
        n_unit = numeral(unit, numeral::ui64());
    }

    if (allone == n_unit) {
        result = mk_numeral(allone, bv_size);
        return;
    }

    flat_args.set_end(it2);
    if (!n_unit.is_zero()) {
        flat_args.push_back(mk_numeral(n_unit, bv_size));
    }

    sz = flat_args.size();
    switch(sz) {
    case 0:
        result = mk_numeral(n_unit, bv_size);
        break;
    case 1:
        result = flat_args.back();
        break;
    default:
        result = mk_list_assoc_app(m_manager, m_fid, OP_BOR, sz, flat_args.c_ptr());
        break;
    }
}

void bv_simplifier_plugin::mk_bv_xor(unsigned num_args, expr * const * args, expr_ref & result) {
    ptr_buffer<expr> flat_args;
    for (unsigned i = 0; i < num_args; ++i) {
        flat_args.push_back(args[i]);
    }
    std::sort(flat_args.begin(), flat_args.end(), expr_lt_proc());
    SASSERT(num_args > 0);

    unsigned bv_size = get_bv_size(args[0]);
    numeral val;
    
    uint64 unit = 0;
    numeral n_unit(0);

    expr * prev = 0;
    ptr_buffer<expr>::iterator it  = flat_args.begin();
    ptr_buffer<expr>::iterator it2 = it;
    ptr_buffer<expr>::iterator end = flat_args.end();
    for (; it != end; ++it) {
        if (bv_size <= 64 && is_numeral(*it, val)) {
            uint64 u = to_uint64(val, bv_size);
            unit = u ^ unit;
        }
        else if (bv_size > 64 && is_numeral(*it, val)) {
            n_unit = mk_bv_xor(n_unit, val, bv_size);
        }
        else if (prev != 0 && prev == *it) {
            --it2; // remove prev
            prev = 0;
        }
        else {
            *it2 = *it;
            prev = *it2;
            ++it2;
        }
    }
    flat_args.set_end(it2);

    if (bv_size <= 64) {
        n_unit = numeral(numeral(unit,numeral::ui64()));
    }

    if (!n_unit.is_zero()) {
        flat_args.push_back(mk_numeral(n_unit, bv_size));
    }

    unsigned sz = flat_args.size();
    switch(sz) {
    case 0:
        result = mk_numeral(n_unit, bv_size);
        break;
    case 1:
        result = flat_args.back();
        break;
    default:
        result = mk_list_assoc_app(m_manager, m_fid, OP_BXOR, flat_args.size(), flat_args.c_ptr());
        break;
    }
}

void bv_simplifier_plugin::mk_bv_not(expr * arg, expr_ref & result) {
    numeral val;
    unsigned bv_size;
    if (m_util.is_numeral(arg, val, bv_size)) {
        if (bv_size <= 64) {
            uint64 l    = bv_size;
            uint64 mask = shift_left(1ull,l) - 1ull;
            uint64 u    = val.get_uint64();
            u           = mask & (~u);
            result = mk_numeral(numeral(u, numeral::ui64()), bv_size);
            TRACE("bv_not_bug", 
                  tout << l << " " << mask << " " << u << "\n";
                  tout << mk_pp(arg, m_manager) << "\n" << mk_pp(result, m_manager) << "\n";);
        }
        else {
            numeral r = mk_bv_not(val, bv_size);
            result = mk_numeral(r, bv_size);
            TRACE("bv_not_bug", 
                  tout << mk_pp(arg, m_manager) << "\n" << mk_pp(result, m_manager) << "\n";);   
        }
    }
    else if (is_app_of(arg, m_fid, OP_BNOT)) {
        result = to_app(arg)->get_arg(0);
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BNOT, arg);
    }
}

void bv_simplifier_plugin::mk_zeroext(unsigned n, expr * arg, expr_ref & result) {
    if (n == 0) {
        result = arg;
    }
    else {
        expr_ref zero(m_manager);
        zero = mk_bv0(n);
        mk_concat(zero.get(), arg, result);
    }
}

void bv_simplifier_plugin::mk_repeat(unsigned n, expr * arg, expr_ref & result) {
    ptr_buffer<expr> args;
    for (unsigned i = 0; i < n; i++) {
        args.push_back(arg);
    }
    mk_concat(args.size(), args.c_ptr(), result);
}

bool bv_simplifier_plugin::is_minus_one_core(expr * arg) const {
    numeral r;
    unsigned bv_size;
    if (m_util.is_numeral(arg, r, bv_size)) {
        numeral minus_one(-1);
        minus_one = mod(minus_one, rational::power_of_two(bv_size));
        return r == minus_one;
    }
    return false;
}

bool bv_simplifier_plugin::is_x_minus_one(expr * arg, expr * & x) {
    if (is_add(arg) && to_app(arg)->get_num_args() == 2) {
        if (is_minus_one_core(to_app(arg)->get_arg(0))) {
            x = to_app(arg)->get_arg(1);
            return true;
        }
        if (is_minus_one_core(to_app(arg)->get_arg(1))) {
            x = to_app(arg)->get_arg(0);
            return true;
        }
    }
    return false;
}

void bv_simplifier_plugin::mk_bv_urem(expr * arg1, expr * arg2, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size;
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);
    bv_size = get_bv_size(arg1);

    if (is_num2 && r2.is_zero() && !m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BUREM0, arg1);
        return;
    }

    if (is_num1 && is_num2 && !r2.is_zero()) {
        SASSERT(r1.is_nonneg() && r2.is_pos());
        r1 %= r2;
        result = mk_numeral(r1, bv_size);
        return;
    }

    if (!m_params.m_hi_div0) {
        // TODO: implement the optimization in this branch for the case the hardware interpretation is used for (x urem 0)
        // urem(0, x) ==> ite(x = 0, urem0(x), 0)
        if (is_num1 && r1.is_zero()) {
            expr * zero        = arg1;
            expr_ref urem0(m_manager), eq0(m_manager);
            urem0 = m_manager.mk_app(m_fid, OP_BUREM0, 1, &zero);
            m_bsimp.mk_eq(arg2, zero, eq0);
            m_bsimp.mk_ite(eq0.get(), urem0.get(), zero, result);
            TRACE("urem", 
                  tout << "urem:\n";
                  ast_ll_pp(tout, m_manager, arg1); ast_ll_pp(tout, m_manager, arg2);
                  tout << "result:\n"; ast_ll_pp(tout, m_manager, result.get()););
            return;
        }
        
        // urem(x - 1, x) ==> ite(x = 0, urem0(x-1), x - 1) ==> ite(x = 0, urem0(-1), x - 1)
        expr * x;
        if (is_x_minus_one(arg1, x) && x == arg2) {
            expr * x_minus_1 = arg1;
            expr_ref zero(m_manager);
            zero = mk_bv0(bv_size);
            expr_ref minus_one(m_manager), urem0(m_manager), eq0(m_manager);
            minus_one = mk_numeral(numeral::minus_one(), bv_size);
            expr * minus_1 = minus_one.get();
            urem0 = m_manager.mk_app(m_fid, OP_BUREM0, 1, &minus_1);
            m_bsimp.mk_eq(arg2, zero.get(), eq0);
            m_bsimp.mk_ite(eq0.get(), urem0.get(), x_minus_1, result);
            TRACE("urem", 
                  tout << "urem:\n";
                  ast_ll_pp(tout, m_manager, arg1); ast_ll_pp(tout, m_manager, arg2);
                  tout << "result:\n"; ast_ll_pp(tout, m_manager, result.get()););
            return;
        }
    }

    if (is_num2 || m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BUREM_I, arg1, arg2);
    }
    else {
        bv_size = get_bv_size(arg2);
        result = m_manager.mk_ite(m_manager.mk_eq(arg2, mk_numeral(0, bv_size)),
                                  m_manager.mk_app(m_fid, OP_BUREM0, arg1),
                                  m_manager.mk_app(m_fid, OP_BUREM_I, arg1, arg2));
    }
}

void bv_simplifier_plugin::mk_sign_extend(unsigned n, expr * arg, expr_ref & result) {
    numeral r;
    unsigned bv_size;
    if (m_util.is_numeral(arg, r, bv_size)) {
        unsigned result_bv_size = bv_size + n;
        r = norm(r, bv_size, true);
        r = mod(r, rational::power_of_two(result_bv_size));
        result = mk_numeral(r, result_bv_size);
        TRACE("mk_sign_extend", tout << "n: " << n << "\n"; 
              ast_ll_pp(tout, m_manager, arg); tout << "====>\n"; 
              ast_ll_pp(tout, m_manager, result.get()););
        return;
    }
    parameter param(n);
    result = m_manager.mk_app(m_fid, OP_SIGN_EXT, 1, &param, 1, &arg);
}

/**
   Implement the following reductions
   
   (bvashr (bvashr a n1) n2) ==> (bvashr a (+ n1 n2))
   (bvlshr (bvlshr a n1) n2) ==> (bvlshr a (+ n1 n2))
   (bvshl (bvshl a n1) n2)   ==> (bvshl a (+ n1 n2))
   when n1 and n2 are numerals.
   Remark if (+ n1 n2) is greater than bv_size, we set (+ n1 n2) to bv_size 
   
   Return true if the transformation was applied and the result stored in 'result'.
   Return false otherwise.
*/
bool bv_simplifier_plugin::shift_shift(bv_op_kind k, expr* arg1, expr* arg2, expr_ref& result) {
    SASSERT(k == OP_BASHR || k == OP_BSHL || k == OP_BLSHR);
    if (!is_app_of(arg1, m_fid, k))
        return false;
    expr * a  = to_app(arg1)->get_arg(0);
    expr * n1 = to_app(arg1)->get_arg(1);
    expr * n2 = arg2;
    numeral r1, r2;
    unsigned bv_size = UINT_MAX;
    bool is_num1 = m_util.is_numeral(n1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(n2, r2, bv_size);
    if (!is_num1 || !is_num2)
        return false;
    SASSERT(bv_size != UINT_MAX);
    numeral r = r1 + r2;
    if (r > numeral(bv_size))
        r = numeral(bv_size);
    switch (k) {
    case OP_BASHR:
        mk_bv_ashr(a, m_util.mk_numeral(r, bv_size), result);
        break;
    case OP_BLSHR:
        mk_bv_lshr(a, m_util.mk_numeral(r, bv_size), result);
        break;
    default:
        SASSERT(k == OP_BSHL);
        mk_bv_shl(a, m_util.mk_numeral(r, bv_size), result);
        break;
    }
    return true;
}

void bv_simplifier_plugin::mk_bv_shl(expr * arg1, expr * arg2, expr_ref & result) {
    // x << 0  ==  x
    numeral r1, r2;
    unsigned bv_size = get_bv_size(arg1);        
    bool is_num1 = is_numeral(arg1, r1);
    bool is_num2 = is_numeral(arg2, r2);

    if (is_num2 && r2.is_zero()) {
        result = arg1;
    }
    else if (is_num2 && r2 >= rational(bv_size)) {
        result = mk_numeral(0, bv_size);        
    }
    else if (is_num2 && is_num1 && bv_size <= 64) {
        SASSERT(r1.is_uint64() && r2.is_uint64());
        SASSERT(r2.get_uint64() < bv_size);

        uint64 r = shift_left(r1.get_uint64(), r2.get_uint64());
        result   = mk_numeral(r, bv_size);
    }
    else if (is_num1 && is_num2) {
        SASSERT(r2 < rational(bv_size));
        SASSERT(r2.is_unsigned());
        result = mk_numeral(r1 * rational::power_of_two(r2.get_unsigned()), bv_size);
    }

    //
    // (bvshl x k) -> (concat (extract [n-1-k:0] x) bv0:k)
    //
    else if (is_num2 && r2.is_pos() && r2 < numeral(bv_size)) {
        SASSERT(r2.is_unsigned());
        unsigned r = r2.get_unsigned();
        expr_ref tmp1(m_manager);
        mk_extract(bv_size - r - 1, 0, arg1, tmp1);
        expr_ref zero(m_manager);
        zero = mk_bv0(r);
        expr* args[2] = { tmp1.get(), zero.get() };
        mk_concat(2, args, result);
    }
    else if (shift_shift(OP_BSHL, arg1, arg2, result)) {
        // done
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BSHL, arg1, arg2);
    }
    TRACE("mk_bv_shl", 
          tout << mk_pp(arg1, m_manager) << " << " 
          << mk_pp(arg2, m_manager) << " = " 
          << mk_pp(result.get(), m_manager) << "\n";);
}
 
void bv_simplifier_plugin::mk_bv_lshr(expr * arg1, expr * arg2, expr_ref & result) {
    // x >> 0 == x
    numeral r1, r2;
    unsigned bv_size = get_bv_size(arg1);        
    bool is_num1 = is_numeral(arg1, r1);
    bool is_num2 = is_numeral(arg2, r2);

    if (is_num2 && r2.is_zero()) {
        result = arg1;
    }
    else if (is_num2 && r2 >= rational(bv_size)) {
        result = mk_numeral(rational(0), bv_size);
    }
    else if (is_num1 && is_num2 && bv_size <= 64) {        
        SASSERT(r1.is_uint64()); 
        SASSERT(r2.is_uint64());
        uint64 r = shift_right(r1.get_uint64(), r2.get_uint64());
        result   = mk_numeral(r, bv_size);
    }
    else if (is_num1 && is_num2) {
        SASSERT(r2.is_unsigned());
        unsigned sh = r2.get_unsigned();
        r1 = div(r1, rational::power_of_two(sh));
        result = mk_numeral(r1, bv_size);
    }
    //
    // (bvlshr x k) -> (concat bv0:k (extract [n-1:k] x))
    //
    else if (is_num2 && r2.is_pos() && r2 < numeral(bv_size)) {
        SASSERT(r2.is_unsigned());
        unsigned r = r2.get_unsigned();
        expr_ref tmp1(m_manager);
        mk_extract(bv_size - 1, r, arg1, tmp1);
        expr_ref zero(m_manager);
        zero = mk_bv0(r);
        expr* args[2] = {  zero.get(), tmp1.get() };
        mk_concat(2, args, result);
    }
    else if (shift_shift(OP_BLSHR, arg1, arg2, result)) {
        // done
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BLSHR, arg1, arg2);
    }
    TRACE("mk_bv_lshr", tout << mk_pp(arg1, m_manager) << " >> " << 
          mk_pp(arg2, m_manager) << " = " << mk_pp(result.get(), m_manager) << "\n";);

}


void bv_simplifier_plugin::mk_int2bv(expr * arg, sort* range, expr_ref & result) {
    numeral val;
    bool is_int;
    unsigned bv_size = get_bv_size(range);
    
    if (m_arith.is_numeral(arg, val, is_int)) {
        result = mk_numeral(val, bv_size);
    }
    // (int2bv (bv2int x)) == x
    else if (is_app_of(arg, m_fid, OP_BV2INT) && bv_size == get_bv_size(to_app(arg)->get_arg(0))) {
        result = to_app(arg)->get_arg(0);
    }
    else {
        parameter parameter(bv_size);
        result = m_manager.mk_app(m_fid, OP_INT2BV, 1, &parameter, 1, &arg);
        SASSERT(result.get());
    }
}

void bv_simplifier_plugin::mk_bv2int(expr * arg, sort* range, expr_ref & result) {
    if (!m_params.m_bv2int_distribute) {
        parameter parameter(range);
        result = m_manager.mk_app(m_fid, OP_BV2INT, 1, &parameter, 1, &arg);
        return;
    }
    numeral v;
    if (is_numeral(arg, v)) {
        result = m_arith.mk_numeral(v, true);
    }
    else if (is_mul_no_overflow(arg)) {
        expr_ref tmp1(m_manager), tmp2(m_manager);
        mk_bv2int(to_app(arg)->get_arg(0), range, tmp1);
        mk_bv2int(to_app(arg)->get_arg(1), range, tmp2);
        result = m_arith.mk_mul(tmp1, tmp2);        
    }
    else if (is_add_no_overflow(arg)) {
        expr_ref tmp1(m_manager), tmp2(m_manager);
        mk_bv2int(to_app(arg)->get_arg(0), range, tmp1);
        mk_bv2int(to_app(arg)->get_arg(1), range, tmp2);
        result = m_arith.mk_add(tmp1, tmp2);        
    }
    // commented out to reproduce bug in reduction of int2bv/bv2int
    else if (m_util.is_concat(arg)) {
        expr_ref tmp1(m_manager), tmp2(m_manager);
        unsigned sz2 = get_bv_size(to_app(arg)->get_arg(1));
        mk_bv2int(to_app(arg)->get_arg(0), range, tmp1);
        mk_bv2int(to_app(arg)->get_arg(1), range, tmp2);
        tmp1 = m_arith.mk_mul(m_arith.mk_numeral(power(numeral(2), sz2), true), tmp1);
        result = m_arith.mk_add(tmp1, tmp2);
    }
    else {
        parameter parameter(range);
        result = m_manager.mk_app(m_fid, OP_BV2INT, 1, &parameter, 1, &arg);
    }
    SASSERT(m_arith.is_int(m_manager.get_sort(result.get())));
}

unsigned bv_simplifier_plugin::num_leading_zero_bits(expr* e) {
    numeral v;
    unsigned sz = get_bv_size(e);
    if (is_numeral(e, v)) {
        while (v.is_pos()) {
            SASSERT(sz > 0);
            --sz;
            v = div(v, numeral(2));
        }
        return sz;
    }
    else if (m_util.is_concat(e)) {
        app* a = to_app(e);
        unsigned sz1 = get_bv_size(a->get_arg(0));
        unsigned nb1 = num_leading_zero_bits(a->get_arg(0));
        if (sz1 == nb1) {
            nb1 += num_leading_zero_bits(a->get_arg(1));
        }
        return nb1;
    }
    return 0;
}

bool bv_simplifier_plugin::is_mul_no_overflow(expr* e) {
    if (!is_mul(e)) {
        return false;
    }
    expr* e1 = to_app(e)->get_arg(0);
    expr* e2 = to_app(e)->get_arg(1);
    unsigned sz = get_bv_size(e1);
    unsigned nb1 = num_leading_zero_bits(e1);
    unsigned nb2 = num_leading_zero_bits(e2);
    return nb1 + nb2 >= sz;
}

bool bv_simplifier_plugin::is_add_no_overflow(expr* e) {
    if (!is_add(e)) {
        return false;
    }
    expr* e1 = to_app(e)->get_arg(0);
    expr* e2 = to_app(e)->get_arg(1);
    unsigned nb1 = num_leading_zero_bits(e1);
    unsigned nb2 = num_leading_zero_bits(e2);
    return nb1 > 0 && nb2 > 0;
}



// Macro for generating mk_bv_sdiv_i, mk_bv_udiv_i, mk_bv_srem_i, mk_bv_urem_i and mk_bv_smod_i.
// These are essentially evaluators for the arg1 and arg2 are numerals.
// Q: Why do we need them?
// A: A constant may be eliminated using substitution. Its value is computed using the evaluator.
//    Example: Suppose we have the top-level atom (= x (bvsrem_i a b)), and x is eliminated.
#define MK_FIXED_DIV_I(NAME, OP)                                                                \
void bv_simplifier_plugin::NAME##_i(expr * arg1, expr * arg2, expr_ref & result) {              \
    numeral r1, r2;                                                                             \
    unsigned bv_size;                                                                           \
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);                                        \
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);                                        \
    if (is_num1 && is_num2 && !r2.is_zero()) {                                                  \
        NAME(arg1, arg2, result);                                                               \
    }                                                                                           \
    else  {                                                                                     \
        result = m_manager.mk_app(m_fid, OP, arg1, arg2);                                       \
    }                                                                                           \
}

MK_FIXED_DIV_I(mk_bv_sdiv, OP_BSDIV_I)
MK_FIXED_DIV_I(mk_bv_udiv, OP_BUDIV_I)
MK_FIXED_DIV_I(mk_bv_srem, OP_BSREM_I)
MK_FIXED_DIV_I(mk_bv_urem, OP_BUREM_I)
MK_FIXED_DIV_I(mk_bv_smod, OP_BSMOD_I)

void bv_simplifier_plugin::mk_bv_sdiv(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r1, r2;
    unsigned bv_size;
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);

    if (is_num2 && r2.is_zero() && !m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BSDIV0, arg1);
    }
    else if (is_num1 && is_num2 && !r2.is_zero()) {
        r1 = norm(r1, bv_size, true);
        r2 = norm(r2, bv_size, true);
        result = mk_numeral(machine_div(r1, r2), bv_size);
    }
    else if (is_num2 || m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BSDIV_I, arg1, arg2);
    }
    else {
        bv_size = get_bv_size(arg2);
        result = m_manager.mk_ite(m_manager.mk_eq(arg2, mk_numeral(0, bv_size)),
                                  m_manager.mk_app(m_fid, OP_BSDIV0, arg1),
                                  m_manager.mk_app(m_fid, OP_BSDIV_I, arg1, arg2));
    }
}

void bv_simplifier_plugin::mk_bv_udiv(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r1, r2;
    unsigned bv_size;
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);

    if (is_num2 && r2.is_zero() && !m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BUDIV0, arg1);
    }
    else if (is_num1 && is_num2 && !r2.is_zero()) {
        SASSERT(r1.is_nonneg());
        SASSERT(r2.is_nonneg());
        result = mk_numeral(machine_div(r1, r2), bv_size);
    }
    else if (is_num2 || m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BUDIV_I, arg1, arg2);
    }
    else {
        bv_size = get_bv_size(arg2);
        result = m_manager.mk_ite(m_manager.mk_eq(arg2, mk_numeral(0, bv_size)),
                                  m_manager.mk_app(m_fid, OP_BUDIV0, arg1),
                                  m_manager.mk_app(m_fid, OP_BUDIV_I, arg1, arg2));
    }
}

void bv_simplifier_plugin::mk_bv_srem(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r1, r2;
    unsigned bv_size;
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);

    if (is_num2 && r2.is_zero() && !m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BSREM0, arg1);
    }
    else if (is_num1 && is_num2 && !r2.is_zero()) {
        r1 = norm(r1, bv_size, true);
        r2 = norm(r2, bv_size, true);
        result = mk_numeral(r1 % r2, bv_size);
    }
    else if (is_num2 || m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BSREM_I, arg1, arg2);
    }
    else {
        bv_size = get_bv_size(arg2);
        result = m_manager.mk_ite(m_manager.mk_eq(arg2, mk_numeral(0, bv_size)),
                                  m_manager.mk_app(m_fid, OP_BSREM0, arg1),
                                  m_manager.mk_app(m_fid, OP_BSREM_I, arg1, arg2));
    }
}

void bv_simplifier_plugin::mk_bv_smod(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r1, r2;
    unsigned bv_size;
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);

    if (is_num1)
        r1 = m_util.norm(r1, bv_size, true);
    if (is_num2)
        r2 = m_util.norm(r2, bv_size, true);
    
    TRACE("bv_simplifier", 
          tout << mk_pp(arg1, m_manager) << " smod " << mk_pp(arg2, m_manager) << "\n";
          );


    if (is_num2 && r2.is_zero()) {
        if (!m_params.m_hi_div0)
            result = m_manager.mk_app(m_fid, OP_BSMOD0, arg1);
        else
            result = arg1;
    }
    else if (is_num1 && is_num2) {
        SASSERT(!r2.is_zero());
        numeral abs_r1 = m_util.norm(abs(r1), bv_size);
        numeral abs_r2 = m_util.norm(abs(r2), bv_size);
        numeral u      = m_util.norm(abs_r1 % abs_r2, bv_size);
        numeral r;
        if (u.is_zero())
            r = u;
        else if (r1.is_pos() && r2.is_pos())
            r = u;
        else if (r1.is_neg() && r2.is_pos())
            r = m_util.norm(-u + r2, bv_size);
        else if (r1.is_pos() && r2.is_neg())
            r = m_util.norm(u + r2, bv_size);
        else
            r = m_util.norm(-u, bv_size);
        result = mk_numeral(r, bv_size);
    }
    else if (is_num2 || m_params.m_hi_div0) {
        result = m_manager.mk_app(m_fid, OP_BSMOD_I, arg1, arg2);
    }
    else {
        bv_size = get_bv_size(arg2);
        result = m_manager.mk_ite(m_manager.mk_eq(arg2, mk_numeral(0, bv_size)),
                                  m_manager.mk_app(m_fid, OP_BSMOD0, arg1),
                                  m_manager.mk_app(m_fid, OP_BSMOD_I, arg1, arg2));
    }
}

uint64 bv_simplifier_plugin::n64(expr* e) {
    numeral r;
    unsigned bv_size;
    if (m_util.is_numeral(e, r, bv_size) && bv_size <= 64) {
        return r.get_uint64();
    }
    UNREACHABLE();
    return 0;
}

rational bv_simplifier_plugin::num(expr* e) {
    numeral r;
    unsigned bv_size;
    if (!m_util.is_numeral(e, r, bv_size)) {
        UNREACHABLE();
    }
    return r;

}

void bv_simplifier_plugin::mk_bv_nand(unsigned num_args, expr* const* args, expr_ref& result) {
    unsigned bv_size;
    if (are_numerals(num_args, args, bv_size)) {
        if (bv_size <= 64) {
            uint64 r = n64(args[0]);
            for (unsigned i = 1; i < num_args; i++) {
                r &= n64(args[i]);
            }
            result = mk_numeral(~r, bv_size);
        }
        else {
            numeral r = num(args[0]);
            for (unsigned i = 1; i < num_args; i++) {
                r = mk_bv_and(r, num(args[i]), bv_size);
            }
            result = mk_numeral(mk_bv_not(r, bv_size), bv_size);
        }
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BNAND, num_args, args);
    }
}

void bv_simplifier_plugin::mk_bv_nor(unsigned num_args, expr* const* args, expr_ref& result) {
    unsigned bv_size;
    if (are_numerals(num_args, args, bv_size)) {
        if (bv_size <= 64) {
            uint64 r = n64(args[0]);
            for (unsigned i = 1; i < num_args; i++) {
                r |= n64(args[i]);
            }
            result = mk_numeral(~r, bv_size);
        }
        else {
            numeral r = num(args[0]);
            for (unsigned i = 1; i < num_args; i++) {
                r = mk_bv_or(r, num(args[i]), bv_size);
            }
            result = mk_numeral(mk_bv_not(r, bv_size), bv_size);
        }
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BNOR, num_args, args);
    }
}

void bv_simplifier_plugin::mk_bv_xnor(unsigned num_args, expr* const* args, expr_ref& result) {
    unsigned bv_size;
    if (are_numerals(num_args, args, bv_size)) {
        if (bv_size <= 64) {
            uint64 r = n64(args[0]);
            for (unsigned i = 1; i < num_args; i++) {
                r ^= n64(args[i]);
            }
            result = mk_numeral(~r, bv_size);
        }
        else {
            numeral r = num(args[0]);
            for (unsigned i = 1; i < num_args; i++) {
                r = mk_bv_xor(r, num(args[i]), bv_size);
            }
            result = mk_numeral(mk_bv_not(r, bv_size), bv_size);
        }
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BXNOR, num_args, args);
    }
}

void bv_simplifier_plugin::mk_bv_rotate_left_core(unsigned shift, numeral r, unsigned bv_size, expr_ref& result) {
    SASSERT(shift < bv_size);
    if (bv_size <= 64) {
        uint64 a       = r.get_uint64();
        uint64 r       = shift_left(a, shift) | shift_right(a, bv_size - shift);
        result = mk_numeral(r, bv_size);        
    }
    else {
        rational r1 = div(r, rational::power_of_two(bv_size - shift)); // shift right
        rational r2 = (r * rational::power_of_two(shift)) % rational::power_of_two(bv_size); // shift left
        result = mk_numeral(r1 + r2, bv_size);
    }
}

void bv_simplifier_plugin::mk_bv_rotate_left(func_decl* f, expr* arg, expr_ref& result) {
    numeral r;
    unsigned bv_size;
    SASSERT(f->get_decl_kind() == OP_ROTATE_LEFT);
    if (m_util.is_numeral(arg, r, bv_size)) {
        unsigned shift   = f->get_parameter(0).get_int() % bv_size;
        mk_bv_rotate_left_core(shift, r, bv_size, result);
    }
    else {
        result = m_manager.mk_app(f, arg);
    }
}

void bv_simplifier_plugin::mk_bv_rotate_right_core(unsigned shift, numeral r, unsigned bv_size, expr_ref& result) {
    SASSERT(shift < bv_size);
    if (bv_size <= 64) {
        uint64 a       = r.get_uint64();
        uint64 r       = shift_right(a, shift) | shift_left(a, bv_size - shift);
        result = mk_numeral(r, bv_size);
    }
    else {
        rational r1 = div(r, rational::power_of_two(shift)); // shift right
        rational r2 = (r * rational::power_of_two(bv_size - shift)) % rational::power_of_two(bv_size); // shift left
        result = mk_numeral(r1 + r2, bv_size);            
    }
}

void bv_simplifier_plugin::mk_bv_rotate_right(func_decl* f, expr* arg, expr_ref& result) {
    numeral r;
    unsigned bv_size;
    SASSERT(f->get_decl_kind() == OP_ROTATE_RIGHT);
    if (m_util.is_numeral(arg, r, bv_size)) {
        unsigned shift   = f->get_parameter(0).get_int() % bv_size;
        mk_bv_rotate_right_core(shift, r, bv_size, result);
    }
    else {
        result = m_manager.mk_app(f, arg);
    }
}

void bv_simplifier_plugin::mk_bv_redor(expr* arg, expr_ref& result) {
    if (is_numeral(arg)) {
        result = m_util.is_zero(arg)?mk_numeral(0, 1):mk_numeral(1,1);
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BREDOR, arg);
    }
}

void bv_simplifier_plugin::mk_bv_redand(expr* arg, expr_ref& result) {
    numeral r;
    unsigned bv_size;
    if (m_util.is_numeral(arg, r, bv_size)) {
        numeral allone = mk_allone(bv_size);
        result = mk_numeral((r == allone)?1:0, 1);
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BREDAND, arg);
    }
}

void bv_simplifier_plugin::mk_bv_comp(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r1, r2;
    if (arg1 == arg2) {
        result = mk_numeral(1,1);
    }
    else if (is_numeral(arg1, r1) && is_numeral(arg2, r2)) {
        result = mk_numeral((r1 == r2)?1:0, 1);
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BCOMP, arg1, arg2);
    }
}

void bv_simplifier_plugin::mk_bv_ashr(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r1, r2;
    unsigned bv_size = get_bv_size(arg1);
    bool is_num1 = m_util.is_numeral(arg1, r1, bv_size);
    bool is_num2 = m_util.is_numeral(arg2, r2, bv_size);

    if (bv_size == 0) {
        result = mk_numeral(rational(0), bv_size);
    }
    else if (is_num2 && r2.is_zero()) {
        result = arg1;
    }
    else if (bv_size <= 64 && is_num1 && is_num2) {
        uint64 n1      = n64(arg1);
        uint64 n2_orig = n64(arg2);
        uint64 n2             = n2_orig % bv_size;
        SASSERT(n2 < bv_size);
        uint64 r       = shift_right(n1, n2);
        bool   sign    = (n1 & shift_left(1ull, bv_size - 1ull)) != 0;
        if (n2_orig > n2) {
            if (sign) {
                r = shift_left(1ull, bv_size) - 1ull;
            }
            else {
                r = 0;
            }
        }
        else if (sign) {
            uint64 allone  = shift_left(1ull, bv_size) - 1ull;
            uint64 mask    = ~(shift_left(1ull, bv_size - n2) - 1ull);
            mask          &= allone;
            r |= mask;
        }
        result = mk_numeral(r, bv_size);
        TRACE("bv", tout << mk_pp(arg1, m_manager) << " >> " 
              << mk_pp(arg2, m_manager) << " = " 
              << mk_pp(result.get(), m_manager) << "\n";
              tout << n1 << " >> " << n2 << " = " << r << "\n";
              );
    }
    else if (is_num1 && is_num2 && rational(bv_size) <= r2) {
        if (has_sign_bit(r1, bv_size)) {
            result = mk_numeral(mk_allone(bv_size), bv_size);
        }
        else {
            result = mk_bv0(bv_size);
        }
    }
    else if (is_num1 && is_num2) {
        SASSERT(r2 < rational(bv_size));
        bool   sign = has_sign_bit(r1, bv_size);
        r1 = div(r1, rational::power_of_two(r2.get_unsigned()));
        if (sign) {
            // pad ones.
            rational p(1);
            for (unsigned i = 0; i < bv_size; ++i) {
                if (r1 < p) {
                    r1 += p;
                }
                p *= rational(2);
            }
        }
        result = mk_numeral(r1, bv_size);
        
    }
    else if (shift_shift(OP_BASHR, arg1, arg2, result)) {
        // done
    }
    else {
        result = m_manager.mk_app(m_fid, OP_BASHR, arg1, arg2);
    }
}

void bv_simplifier_plugin::mk_bv_ext_rotate_right(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r2;
    unsigned bv_size;
    if (m_util.is_numeral(arg2, r2, bv_size)) {
        unsigned shift = static_cast<unsigned>((r2 % numeral(bv_size)).get_uint64() % static_cast<uint64>(bv_size));
        numeral r1;
        if (is_numeral(arg1, r1)) {
            mk_bv_rotate_right_core(shift, r1, bv_size, result);
        }
        else {
            parameter p(shift);
            result = m_manager.mk_app(m_fid, OP_ROTATE_RIGHT, 1, &p, 1, &arg1);
        }
    }
    else {
        result = m_manager.mk_app(m_fid, OP_EXT_ROTATE_RIGHT, arg1, arg2);
    }
}


void bv_simplifier_plugin::mk_bv_ext_rotate_left(expr* arg1, expr* arg2, expr_ref& result) {
    numeral r2;
    unsigned bv_size;
    if (m_util.is_numeral(arg2, r2, bv_size)) {
        unsigned shift = static_cast<unsigned>((r2 % numeral(bv_size)).get_uint64() % static_cast<uint64>(bv_size));
        numeral r1;
        if (is_numeral(arg1, r1)) {
            mk_bv_rotate_left_core(shift, r1, bv_size, result);
        }
        else {
            parameter p(shift);
            result = m_manager.mk_app(m_fid, OP_ROTATE_LEFT, 1, &p, 1, &arg1);
        }
    }
    else {
        result = m_manager.mk_app(m_fid, OP_EXT_ROTATE_LEFT, arg1, arg2);
    }
}

void bv_simplifier_plugin::bit2bool_simplify(unsigned idx, expr* e, expr_ref& result) {

    parameter p(idx);

    ptr_vector<expr> todo;
    expr_ref_vector pinned(m_manager);
    ptr_vector<app> cache;
    todo.push_back(e);
    expr* e0 = e;
    ptr_vector<expr> argv;
    expr_ref tmp(m_manager);
    while (!todo.empty()) {
        e = todo.back();
        unsigned e_id = e->get_id();
        if (e_id >= cache.size()) {
            cache.resize(e_id+1,0);
        }
        if (cache[e_id]) {
            todo.pop_back();
            continue;
        }
        if (!m_util.is_numeral(e) &&
            !m_util.is_bv_and(e) &&
            !m_util.is_bv_or(e) &&
            !(is_app_of(e, m_fid, OP_BXOR) && to_app(e)->get_num_args() == 2) &&
            !m_manager.is_ite(e) &&
            !m_util.is_concat(e) &&
            !m_util.is_bv_not(e)) {
            expr_ref extr(m_manager);
            extr = m_util.mk_extract(idx, idx, e);
            cache[e_id] = m_manager.mk_eq(m_util.mk_numeral(1, 1), extr);
            pinned.push_back(cache[e_id]);
            todo.pop_back();
            continue;
        }
        app* a = to_app(e);
        unsigned sz = a->get_num_args();
        if (m_util.is_concat(e)) {
            // look for first argument
            unsigned idx1 = idx;
            while (sz > 0) {
                --sz;
                expr * a_i     = a->get_arg(sz);
                unsigned a_sz = get_bv_size(a_i);
                if (a_sz <= idx1) {
                    idx1 -= a_sz;
                }
                else {
                    // idx < a_sz;
                    bit2bool_simplify(idx1, a_i, tmp);
                    pinned.push_back(tmp);
                    cache[e_id] = to_app(tmp);
                    break;
                }
            }
            todo.pop_back();
            continue;
        }
        argv.reset();
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg_i = a->get_arg(i);
            if (i == 0 && m_manager.is_ite(e)) {
                argv.push_back(arg_i);
            }
            else if (cache.size() > arg_i->get_id() && cache[arg_i->get_id()]) {
                argv.push_back(cache[arg_i->get_id()]);
            }
            else {
                todo.push_back(arg_i);
            }
        }
        if (sz != argv.size()) {
            continue;
        }
        todo.pop_back();
        rational val;
        unsigned num_bits;
        if (m_util.is_numeral(e, val, num_bits)) {
            rational two(2);
            for (unsigned i = 0; i < idx; ++i) {
                val = div(val, two);
            }  
            bool is_pos = !(val % two).is_zero();
            tmp = is_pos?m_manager.mk_true():m_manager.mk_false();
        }
        else if (m_util.is_bv_and(e)) {
            //tmp = m_manager.mk_and(sz, argv.c_ptr());
            m_bsimp.mk_and(sz, argv.c_ptr(), tmp);
            pinned.push_back(tmp);
        }
        else if (m_util.is_bv_or(e)) {
            //tmp = m_manager.mk_or(sz, argv.c_ptr());
            m_bsimp.mk_or(sz, argv.c_ptr(), tmp);
            pinned.push_back(tmp);
        }
        else if (m_util.is_bv_not(e)) {
            //tmp = m_manager.mk_not(argv[0]);
            m_bsimp.mk_not(argv[0], tmp);
            pinned.push_back(tmp);
        }
        else if (is_app_of(e, m_fid, OP_BXOR)) {
            SASSERT(argv.size() == 2);
            m_bsimp.mk_xor(argv[0], argv[1], tmp);
            pinned.push_back(tmp);
        }
        else if (m_manager.is_ite(e)) {
            //tmp = m_manager.mk_ite(argv[0], argv[1], argv[2]);
            m_bsimp.mk_ite(argv[0], argv[1], argv[2], tmp);
            pinned.push_back(tmp);
        }
        else {
            UNREACHABLE();
        }
        cache[e_id] = to_app(tmp);
    }
    result = cache[e0->get_id()]; 
}


// replace addition by concatenation.
void bv_simplifier_plugin::mk_add_concat(expr_ref& result) {
    if (!m_util.is_bv_add(result)) {
        return;
    }
    app* a = to_app(result);
    if (a->get_num_args() != 2) {
        return;
    }
    expr* x = a->get_arg(0);
    expr* y = a->get_arg(1);
    if (!m_util.is_concat(x)) {
        std::swap(x, y);
    }
    if (!m_util.is_concat(x)) {
        return;
    }
    unsigned sz = m_util.get_bv_size(x);

#if 0
    // optimzied version. Seems not worth it..
#define UPDATE_CURR(_curr1, _idx1,_x,_is_num, _i)                       \
    if (_idx1 >= m_util.get_bv_size(_curr1)) {                          \
        _curr1 = _x;                                                    \
        _idx1 = _i;                                                     \
        _is_num = false;                                                \
    }                                                                   \
    while (m_util.is_concat(_curr1)) {                                  \
        _is_num = false;                                                \
        unsigned num_args = to_app(_curr1)->get_num_args();             \
        while (true) {                                                  \
            --num_args;                                                 \
            expr* c1 = to_app(_curr1)->get_arg(num_args);               \
            unsigned sz1 = m_util.get_bv_size(c1);                      \
            if (sz1 < _idx1) {                                          \
                _idx1 -= sz1;                                           \
            }                                                           \
            else {                                                      \
                _curr1 = c1;                                            \
                break;                                                  \
            }                                                           \
        }                                                               \
    }
    
    unsigned idx1 = 0, idx2 = 0;
    expr* curr1 = x, *curr2 = y;
    bool is_num1 = false, is_num2 = false;
    rational val1, val2;
    rational two(2);
    for (unsigned i = 0; i < sz; ++i, ++idx1, ++idx2) {
        UPDATE_CURR(curr1, idx1, x, is_num1, i);
        UPDATE_CURR(curr2, idx2, y, is_num2, i);
        if (idx1 == 0 && m_util.is_numeral(curr1, val1, bv_size)) {
            is_num1 = true;
        }
        if (idx2 == 0 && m_util.is_numeral(curr2, val2, bv_size)) {
            is_num2 = true;
        }
        if ((is_num1 && (val1 % two).is_zero()) ||
            (is_num2 && (val2 % two).is_zero())) {
            val1 = div(val1, two);
            val2 = div(val2, two);
                continue;
        }
        return;
    }
    mk_bv_or(2, a->get_args(), result);
#endif
    
    for (unsigned i = 0; i < sz; ++i) {
        if (!is_zero_bit(x,i) && !is_zero_bit(y,i)) {
            return;
        }
    }
    mk_bv_or(2, a->get_args(), result);
}

bool bv_simplifier_plugin::is_zero_bit(expr* x, unsigned idx) {
    rational val;
    unsigned bv_size;
    if (m_util.is_numeral(x, val, bv_size)) {
        if (val.is_zero()) {
            return true;
        }
        rational two(2);
        while (idx > 0) {
            val = div(val, two);
            idx--;
        }
        return (val % two).is_zero();
    }
    if (m_util.is_concat(x)) {
        unsigned num_args = to_app(x)->get_num_args();
        while (num_args > 0) {
            --num_args;
            expr* y = to_app(x)->get_arg(num_args);
            bv_size = m_util.get_bv_size(y);
            if (bv_size <= idx) {
                idx -= bv_size;
            }
            else {
                return is_zero_bit(y, idx);
            }
        }
        UNREACHABLE();
    }
    
    return false;
}
