/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa_decl_plugin.cpp

Abstract:

    Floating point decl plugin

Author:

    Leonardo de Moura (leonardo) 2012-01-15.

Revision History:

--*/
#include"fpa_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"

fpa_decl_plugin::fpa_decl_plugin():
    m_values(m_fm),
    m_value_table(mpf_hash_proc(m_values), mpf_eq_proc(m_values)) {
    m_real_sort = 0;
    m_int_sort  = 0;
    m_bv_plugin = 0;
}

void fpa_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    m_arith_fid = m_manager->mk_family_id("arith");
    m_real_sort = m_manager->mk_sort(m_arith_fid, REAL_SORT);
    SASSERT(m_real_sort != 0); // arith_decl_plugin must be installed before fpa_decl_plugin.
    m_manager->inc_ref(m_real_sort);

    m_int_sort = m_manager->mk_sort(m_arith_fid, INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before fpa_decl_plugin.
    m_manager->inc_ref(m_int_sort);
    
    // BV is not optional anymore.
    SASSERT(m_manager->has_plugin(symbol("bv")));
    m_bv_fid = m_manager->mk_family_id("bv");
    m_bv_plugin = static_cast<bv_decl_plugin*>(m_manager->get_plugin(m_bv_fid));
}

fpa_decl_plugin::~fpa_decl_plugin() {
}

unsigned fpa_decl_plugin::mk_id(mpf const & v) {
    unsigned new_id = m_id_gen.mk();
    m_values.reserve(new_id+1);
    m_fm.set(m_values[new_id], v);
    unsigned old_id = m_value_table.insert_if_not_there(new_id);
    if (old_id != new_id) {
        m_id_gen.recycle(new_id);
        m_fm.del(m_values[new_id]);
    }
    return old_id;
}

void fpa_decl_plugin::recycled_id(unsigned id) {
    SASSERT(m_value_table.contains(id));
    m_value_table.erase(id);
    m_id_gen.recycle(id);
    m_fm.del(m_values[id]);
}

func_decl * fpa_decl_plugin::mk_numeral_decl(mpf const & v) {
    parameter p(mk_id(v), true);
    SASSERT(p.is_external());
    sort * s = mk_float_sort(v.get_ebits(), v.get_sbits());
    return m_manager->mk_const_decl(symbol("fp.numeral"),  s, func_decl_info(m_family_id, OP_FPA_NUM, 1, &p));
}

app * fpa_decl_plugin::mk_numeral(mpf const & v) {
    sort * s = mk_float_sort(v.get_ebits(), v.get_sbits());
    func_decl * d;
    if (m_fm.is_nan(v))
        d = m_manager->mk_const_decl(symbol("NaN"), s, func_decl_info(m_family_id, OP_FPA_NAN));
    else if (m_fm.is_pinf(v))
        d = m_manager->mk_const_decl(symbol("+oo"), s, func_decl_info(m_family_id, OP_FPA_PLUS_INF));
    else if (m_fm.is_ninf(v))
        d = m_manager->mk_const_decl(symbol("-oo"), s, func_decl_info(m_family_id, OP_FPA_MINUS_INF));
    else if (m_fm.is_pzero(v))
        d = m_manager->mk_const_decl(symbol("+zero"), s, func_decl_info(m_family_id, OP_FPA_PLUS_ZERO));
    else if (m_fm.is_nzero(v))
        d = m_manager->mk_const_decl(symbol("-zero"), s, func_decl_info(m_family_id, OP_FPA_MINUS_ZERO));
    else
        d = mk_numeral_decl(v);
    return m_manager->mk_const(d);
}

bool fpa_decl_plugin::is_numeral(expr * n, mpf & val) {
    if (is_app_of(n, m_family_id, OP_FPA_NUM)) {
        m_fm.set(val, m_values[to_app(n)->get_decl()->get_parameter(0).get_ext_id()]);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_MINUS_INF)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_ninf(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_PLUS_INF)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_pinf(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_NAN)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_nan(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_PLUS_ZERO)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_pzero(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_MINUS_ZERO)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_nzero(ebits, sbits, val);
        return true;
    }
    return false;
}

bool fpa_decl_plugin::is_numeral(expr * n) {
    scoped_mpf v(m_fm);
    return is_numeral(n, v);
}

bool fpa_decl_plugin::is_rm_numeral(expr * n, mpf_rounding_mode & val) {
    if (is_app_of(n, m_family_id, OP_FPA_RM_NEAREST_TIES_TO_AWAY)) {
        val = MPF_ROUND_NEAREST_TAWAY;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_RM_NEAREST_TIES_TO_EVEN)) {
        val = MPF_ROUND_NEAREST_TEVEN;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_RM_TOWARD_NEGATIVE)) {
        val = MPF_ROUND_TOWARD_NEGATIVE;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_RM_TOWARD_POSITIVE)) {
        val = MPF_ROUND_TOWARD_POSITIVE;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FPA_RM_TOWARD_ZERO)) {
        val = MPF_ROUND_TOWARD_ZERO;
        return true;
    }

    return 0;
}

bool fpa_decl_plugin::is_rm_numeral(expr * n) { 
    mpf_rounding_mode t; 
    return is_rm_numeral(n, t); 
}

void fpa_decl_plugin::del(parameter const & p) {
    SASSERT(p.is_external());
    recycled_id(p.get_ext_id());
}

parameter fpa_decl_plugin::translate(parameter const & p, decl_plugin & target) {
    SASSERT(p.is_external());
    fpa_decl_plugin & _target = static_cast<fpa_decl_plugin&>(target);
    return parameter(_target.mk_id(m_values[p.get_ext_id()]), true);
}

void fpa_decl_plugin::finalize() {
    if (m_real_sort) { m_manager->dec_ref(m_real_sort); }
    if (m_int_sort)  { m_manager->dec_ref(m_int_sort); }
}

decl_plugin * fpa_decl_plugin::mk_fresh() { 
    return alloc(fpa_decl_plugin); 
}

sort * fpa_decl_plugin::mk_float_sort(unsigned ebits, unsigned sbits) {
    if (sbits < 2)
        m_manager->raise_exception("minimum number of significand bits is 1");
    if (ebits < 2)
        m_manager->raise_exception("minimum number of exponent bits is 2");

    parameter p1(ebits), p2(sbits);
    parameter ps[2] = { p1, p2 };
    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("FloatingPoint"), sort_info(m_family_id, FLOATING_POINT_SORT, sz, 2, ps));
}

sort * fpa_decl_plugin::mk_rm_sort() {
    return m_manager->mk_sort(symbol("RoundingMode"), sort_info(m_family_id, ROUNDING_MODE_SORT));
}

sort * fpa_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case FLOATING_POINT_SORT:
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int()))
            m_manager->raise_exception("expecting two integer parameters to floating point sort (ebits, sbits)");
        return mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
    case ROUNDING_MODE_SORT:
        return mk_rm_sort();
    case FLOAT16_SORT:
        return mk_float_sort(5, 11);
    case FLOAT32_SORT:
        return mk_float_sort(8, 24);
    case FLOAT64_SORT:
        return mk_float_sort(11, 53);
    case FLOAT128_SORT:
        return mk_float_sort(15, 113);
    default:
        m_manager->raise_exception("unknown floating point theory sort");
        return 0;
    }
}

func_decl * fpa_decl_plugin::mk_rm_const_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                unsigned arity, sort * const * domain, sort * range) {
    if (num_parameters != 0)
        m_manager->raise_exception("rounding mode constant does not have parameters");
    if (arity != 0)
        m_manager->raise_exception("rounding mode is a constant");
    sort * s = mk_rm_sort();
    func_decl_info finfo(m_family_id, k);
    switch (k) {
    case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
        return m_manager->mk_const_decl(symbol("roundNearestTiesToEven"), s, finfo);
    case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
        return m_manager->mk_const_decl(symbol("roundNearestTiesToAway"), s, finfo);
    case OP_FPA_RM_TOWARD_POSITIVE:
        return m_manager->mk_const_decl(symbol("roundTowardPositive"), s, finfo);
    case OP_FPA_RM_TOWARD_NEGATIVE:
        return m_manager->mk_const_decl(symbol("roundTowardNegative"), s, finfo);
    case OP_FPA_RM_TOWARD_ZERO:
        return m_manager->mk_const_decl(symbol("roundTowardZero"), s, finfo);
    default:
        UNREACHABLE();
        return 0;
    }
}

func_decl * fpa_decl_plugin::mk_float_const_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                   unsigned arity, sort * const * domain, sort * range) {
    sort * s = 0;
    if (num_parameters == 1 && parameters[0].is_ast() && is_sort(parameters[0].get_ast()) && is_float_sort(to_sort(parameters[0].get_ast()))) {
        s = to_sort(parameters[0].get_ast());
    }
    else if (num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int()) {
        s = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
    }
    else if (range != 0 && is_float_sort(range)) {
        s = range;
    }
    else {
        m_manager->raise_exception("sort of floating point constant was not specified");
        UNREACHABLE();
    }

    SASSERT(is_sort_of(s, m_family_id, FLOATING_POINT_SORT));
    
    unsigned ebits = s->get_parameter(0).get_int();
    unsigned sbits = s->get_parameter(1).get_int();
    scoped_mpf val(m_fm);

    switch (k)
    {
    case OP_FPA_NAN: m_fm.mk_nan(ebits, sbits, val);
        SASSERT(m_fm.is_nan(val));
        break;
    case OP_FPA_MINUS_INF: m_fm.mk_ninf(ebits, sbits, val); break;
    case OP_FPA_PLUS_INF: m_fm.mk_pinf(ebits, sbits, val); break;
    case OP_FPA_MINUS_ZERO: m_fm.mk_nzero(ebits, sbits, val); break;
    case OP_FPA_PLUS_ZERO: m_fm.mk_pzero(ebits, sbits, val); break;
    }

    return mk_numeral_decl(val);
}

func_decl * fpa_decl_plugin::mk_bin_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                               unsigned arity, sort * const * domain, sort * range) {
    if (arity < 2)
        m_manager->raise_exception("invalid number of arguments to floating point relation");
    if (domain[0] != domain[1] || !is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected equal FloatingPoint sorts as arguments");
    symbol name;
    switch (k) {
    case OP_FPA_EQ: name = "fp.eq";  break;
    case OP_FPA_LT: name = "fp.lt";   break;
    case OP_FPA_GT: name = "fp.gt";   break;        
    case OP_FPA_LE: name = "fp.leq";  break;        
    case OP_FPA_GE: name = "fp.geq";  break;        
    default:
        UNREACHABLE();
        break;
    }
    func_decl_info finfo(m_family_id, k);
    finfo.set_chainable(true);
    return m_manager->mk_func_decl(name, domain[0], domain[1], m_manager->mk_bool_sort(), finfo);
}

func_decl * fpa_decl_plugin::mk_unary_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                 unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to floating point relation");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort");
    symbol name;
    switch (k) {
    case OP_FPA_IS_ZERO: name = "fp.isZero";  break;
    case OP_FPA_IS_NEGATIVE: name = "fp.isNegative";  break;
    case OP_FPA_IS_POSITIVE: name = "fp.isPositive";  break;
    case OP_FPA_IS_NAN: name = "fp.isNaN";  break;
    case OP_FPA_IS_INF: name = "fp.isInfinite";  break;
    case OP_FPA_IS_NORMAL: name = "fp.isNormal";  break;
    case OP_FPA_IS_SUBNORMAL: name = "fp.isSubnormal";  break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_unary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                             unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort"); 
    symbol name;
    switch (k) {
    case OP_FPA_ABS: name = "fp.abs"; break;
    case OP_FPA_NEG: name = "fp.neg"; break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[0], func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_binary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                              unsigned arity, sort * const * domain, sort * range) {
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (domain[0] != domain[1] || !is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected arguments of equal FloatingPoint sorts"); 
    symbol name;
    switch (k) {
    case OP_FPA_REM: name = "fp.rem"; break;
    case OP_FPA_MIN: name = "fp.min"; break;
    case OP_FPA_MAX: name = "fp.max"; break;
    case OP_FPA_INTERNAL_MIN_I: name = "fp.min_i"; break;
    case OP_FPA_INTERNAL_MAX_I: name = "fp.max_i"; break;
    case OP_FPA_INTERNAL_MIN_UNSPECIFIED: name = "fp.min_unspecified"; break;
    case OP_FPA_INTERNAL_MAX_UNSPECIFIED: name = "fp.max_unspecified"; break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[0], func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_rm_binary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                 unsigned arity, sort * const * domain, sort * range) {
    if (arity != 3)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
    if (domain[1] != domain[2] || !is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch, expected arguments 1 and 2 of equal FloatingPoint sorts"); 
    symbol name;
    switch (k) {
    case OP_FPA_ADD: name = "fp.add";   break;
    case OP_FPA_SUB: name = "fp.sub";   break;
    case OP_FPA_MUL: name = "fp.mul";   break;
    case OP_FPA_DIV: name = "fp.div";   break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_rm_unary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                unsigned arity, sort * const * domain, sort * range) {
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected RoundingMode as first argument");
    if (!is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch, expected FloatingPoint as second argument"); 
    symbol name;
    switch (k) {
    case OP_FPA_SQRT: name = "fp.sqrt";   break;
    case OP_FPA_ROUND_TO_INTEGRAL: name = "fp.roundToIntegral";   break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_fma(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {
    if (arity != 4)
        m_manager->raise_exception("invalid number of arguments to fused_ma operator");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected RoundingMode as first argument");
    if (domain[1] != domain[2] || domain[1] != domain[3] || !is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch, expected arguments 1,2,3 of equal FloatingPoint sort");
    symbol name("fp.fma");
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_to_fp(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                        unsigned arity, sort * const * domain, sort * range) {    
    if (m_bv_plugin && arity == 3 && 
        is_sort_of(domain[0], m_bv_fid, BV_SORT) &&
        is_sort_of(domain[1], m_bv_fid, BV_SORT) &&
        is_sort_of(domain[2], m_bv_fid, BV_SORT)) {
        // 3 BVs -> 1 FP
        unsigned ebits = domain[1]->get_parameter(0).get_int();
        unsigned sbits = domain[2]->get_parameter(0).get_int() + 1;
        parameter ps[] = { parameter(ebits), parameter(sbits) };
        sort * fp = mk_float_sort(ebits, sbits);
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, 2, ps));
    }
    else if (m_bv_plugin && arity == 1 && is_sort_of(domain[0], m_bv_fid, BV_SORT)) {
        // 1 BV -> 1 FP
        if (num_parameters != 2)
            m_manager->raise_exception("invalid number of parameters to to_fp");
        if (!parameters[0].is_int() || !parameters[1].is_int())
            m_manager->raise_exception("invalid parameter type to to_fp");

        int ebits = parameters[0].get_int();
        int sbits = parameters[1].get_int();
        
        if (domain[0]->get_parameter(0).get_int() != (ebits + sbits))
            m_manager->raise_exception("sort mismatch; invalid bit-vector size, expected bitvector of size (ebits+sbits)");

        sort * fp = mk_float_sort(ebits, sbits);
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else if (m_bv_plugin && arity == 2 && 
             is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT) &&
             is_sort_of(domain[1], m_bv_fid, BV_SORT)) {
        // RoundingMode + 1 BV -> 1 FP
        if (num_parameters != 2)
            m_manager->raise_exception("invalid number of parameters to to_fp");
        if (!parameters[0].is_int() || !parameters[1].is_int())
            m_manager->raise_exception("invalid parameter type to to_fp");
        int ebits = parameters[0].get_int();
        int sbits = parameters[1].get_int();

        sort * fp = mk_float_sort(ebits, sbits);
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else if (arity == 2 &&
             is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT) &&
             is_sort_of(domain[1], m_family_id, FLOATING_POINT_SORT)) {
        // Rounding + 1 FP -> 1 FP
        if (num_parameters != 2)
            m_manager->raise_exception("invalid number of parameters to to_fp");
        if (!parameters[0].is_int() || !parameters[1].is_int())
            m_manager->raise_exception("invalid parameter type to to_fp");
        int ebits = parameters[0].get_int();
        int sbits = parameters[1].get_int();        
        if (!is_rm_sort(domain[0]))
            m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
        if (!is_sort_of(domain[1], m_family_id, FLOATING_POINT_SORT))
            m_manager->raise_exception("sort mismatch, expected second argument of FloatingPoint sort");
        
        sort * fp = mk_float_sort(ebits, sbits);
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }    
    else if (arity == 3 &&
             is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT) &&
             is_sort_of(domain[1], m_arith_fid, REAL_SORT) &&
             is_sort_of(domain[2], m_arith_fid, INT_SORT))
    {
        // Rounding + 1 Real + 1 Int -> 1 FP
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int()))
            m_manager->raise_exception("expecting two integer parameters to to_fp");                

        sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else if (arity == 1 &&
             is_sort_of(domain[0], m_arith_fid, REAL_SORT))
    {
        // 1 Real -> 1 FP
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int()))
            m_manager->raise_exception("expecting two integer parameters to to_fp");
        if (domain[1] != m_real_sort)
            m_manager->raise_exception("sort mismatch, expected one argument of Real sort");

        sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else if (arity == 2 &&
             is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT) &&
             is_sort_of(domain[1], m_arith_fid, REAL_SORT))
    {
        // Rounding + 1 Real -> 1 FP
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int()))
            m_manager->raise_exception("expecting two integer parameters to to_fp");

        sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else if (arity == 2 &&
             is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT) &&
             is_sort_of(domain[1], m_arith_fid, INT_SORT)) {
        // Rounding + 1 Int -> 1 FP
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int()))
            m_manager->raise_exception("expecting two integer parameters to to_fp");

        sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else {
        m_manager->raise_exception("Unexpected argument combination for (_ to_fp eb sb). Supported argument combinations are: "
                                   "((_ BitVec 1) (_ BitVec eb) (_ BitVec sb-1)), "
                                   "(_ BitVec (eb+sb)), "
                                   "(Real), "
                                   "(RoundingMode (_ BitVec (eb+sb))), "
                                   "(RoundingMode (_ FloatingPoint eb' sb')), "
                                   "(RoundingMode Real Int), "
                                   "(RoundingMode Int), and "
                                   "(RoundingMode Real)."
                                   );
    }

    return 0;
}

func_decl * fpa_decl_plugin::mk_to_fp_unsigned(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                 unsigned arity, sort * const * domain, sort * range) {
    SASSERT(m_bv_plugin);
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to to_fp_unsigned");
    if (!is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT))
        m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
    if (!is_sort_of(domain[1], m_bv_fid, BV_SORT))
        m_manager->raise_exception("sort mismatch, expected second argument of bit-vector sort");
    
    // RoundingMode + 1 BV -> 1 FP
    if (num_parameters != 2)
        m_manager->raise_exception("invalid number of parameters to to_fp_unsigned");
    if (!parameters[0].is_int() || !parameters[1].is_int())
        m_manager->raise_exception("invalid parameter type to to_fp_unsigned");
    
    int ebits = parameters[0].get_int();
    int sbits = parameters[1].get_int();

    sort * fp = mk_float_sort(ebits, sbits);
    symbol name("to_fp_unsigned");
    return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_fp(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    if (arity != 3)
        m_manager->raise_exception("invalid number of arguments to fp");    
    if (!is_sort_of(domain[0], m_bv_fid, BV_SORT) || 
        (domain[0]->get_parameter(0).get_int() != 1) ||
        !is_sort_of(domain[1], m_bv_fid, BV_SORT) ||
        !is_sort_of(domain[2], m_bv_fid, BV_SORT))
        m_manager->raise_exception("sort mismatch, expected three bit-vectors, the first one of size 1.");
    
    int eb = (domain[1])->get_parameter(0).get_int();
    int sb = (domain[2])->get_parameter(0).get_int() + 1;
    symbol name("fp");    
    sort * fp = mk_float_sort(eb, sb);
    return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_to_ubv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range) {
    SASSERT(m_bv_plugin);
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to fp.to_ubv");
    if (num_parameters != 1)
        m_manager->raise_exception("invalid number of parameters to fp.to_ubv");
    if (!parameters[0].is_int())
        m_manager->raise_exception("invalid parameter type; fp.to_ubv expects an int parameter");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
    if (!is_sort_of(domain[1], m_family_id, FLOATING_POINT_SORT))
        m_manager->raise_exception("sort mismatch, expected second argument of FloatingPoint sort");
    if (parameters[0].get_int() <= 0)
        m_manager->raise_exception("invalid parameter value; fp.to_ubv expects a parameter larger than 0");

    symbol name("fp.to_ubv");
    sort * bvs = m_bv_plugin->mk_sort(BV_SORT, 1, parameters);
    return m_manager->mk_func_decl(name, arity, domain, bvs, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_to_sbv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range) {
    SASSERT(m_bv_plugin);
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to fp.to_sbv");
    if (num_parameters != 1)
        m_manager->raise_exception("invalid number of parameters to fp.to_sbv");
    if (!parameters[0].is_int())
        m_manager->raise_exception("invalid parameter type; fp.to_sbv expects an int parameter");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
    if (!is_sort_of(domain[1], m_family_id, FLOATING_POINT_SORT))
        m_manager->raise_exception("sort mismatch, expected second argument of FloatingPoint sort");
    if (parameters[0].get_int() <= 0)
        m_manager->raise_exception("invalid parameter value; fp.to_sbv expects a parameter larger than 0");

    symbol name("fp.to_sbv");
    sort * bvs = m_bv_plugin->mk_sort(BV_SORT, 1, parameters);
    return m_manager->mk_func_decl(name, arity, domain, bvs, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_to_real(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {    
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to fp.to_real");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort");
    
    symbol name("fp.to_real");
    return m_manager->mk_func_decl(name, 1, domain, m_real_sort, func_decl_info(m_family_id, k));
}

func_decl * fpa_decl_plugin::mk_to_ieee_bv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to to_ieee_bv");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort");

    unsigned float_sz = domain[0]->get_parameter(0).get_int() + domain[0]->get_parameter(1).get_int();
    parameter ps[] = { parameter(float_sz) };
    sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, ps);
    symbol name("to_ieee_bv");
    return m_manager->mk_func_decl(name, 1, domain, bv_srt, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_internal_rm(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                            unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to internal_rm");
    if (!is_sort_of(domain[0], m_bv_fid, BV_SORT) || domain[0]->get_parameter(0).get_int() != 3)
        m_manager->raise_exception("sort mismatch, expected argument of sort bitvector, size 3");
    if (!is_rm_sort(range))
        m_manager->raise_exception("sort mismatch, expected range of RoundingMode sort");
    
    parameter ps[] = { parameter(3) };
    sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, ps);
    return m_manager->mk_func_decl(symbol("rm"), 1, &bv_srt, range, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_internal_bv_wrap(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                   unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to internal_bv_wrap");
    if (!is_float_sort(domain[0]) && !is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint or RoundingMode sort");

    if (is_float_sort(domain[0]))
    {
        unsigned float_sz = domain[0]->get_parameter(0).get_int() + domain[0]->get_parameter(1).get_int();
        parameter ps[] = { parameter(float_sz) };
        sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, ps);
        return m_manager->mk_func_decl(symbol("bv_wrap"), 1, domain, bv_srt, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else {        
        parameter ps[] = { parameter(3) };
        sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, ps);
        return m_manager->mk_func_decl(symbol("bv_wrap"), 1, domain, bv_srt, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
}

func_decl * fpa_decl_plugin::mk_internal_bv_unwrap(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                     unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to internal_bv_unwrap");    
    if (!is_sort_of(domain[0], m_bv_fid, BV_SORT))
        m_manager->raise_exception("sort mismatch, expected argument of bitvector sort");
    if (!is_float_sort(range) && !is_rm_sort(range))
        m_manager->raise_exception("sort mismatch, expected range of FloatingPoint or RoundingMode sort");
    
    return m_manager->mk_func_decl(symbol("bv_unwrap"), 1, domain, range, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_internal_to_ubv_unspecified(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range) {
    if (arity != 0)
        m_manager->raise_exception("invalid number of arguments to fp.to_ubv_unspecified");
    if (num_parameters != 1)
        m_manager->raise_exception("invalid number of parameters to fp.to_ubv_unspecified; expecting 1");
    if (!parameters[0].is_int())
        m_manager->raise_exception("invalid parameters type provided to fp.to_ubv_unspecified; expecting an integer");
        
    sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, parameters);
    return m_manager->mk_func_decl(symbol("fp.to_ubv_unspecified"), 0, domain, bv_srt, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_internal_to_sbv_unspecified(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range) {
    if (arity != 0)
        m_manager->raise_exception("invalid number of arguments to internal_to_sbv_unspecified");
    if (num_parameters != 1)
        m_manager->raise_exception("invalid number of parameters to fp.to_sbv_unspecified; expecting 1");
    if (!parameters[0].is_int())
        m_manager->raise_exception("invalid parameters type provided to fp.to_sbv_unspecified; expecting an integer");
    sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, parameters);
    return m_manager->mk_func_decl(symbol("fp.to_sbv_unspecified"), 0, domain, bv_srt, func_decl_info(m_family_id, k, num_parameters, parameters));
}

func_decl * fpa_decl_plugin::mk_internal_to_real_unspecified(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range) {
    if (arity != 0)
        m_manager->raise_exception("invalid number of arguments to internal_to_real_unspecified");
    if (!is_sort_of(range, m_arith_fid, REAL_SORT))
        m_manager->raise_exception("sort mismatch, expected range of FloatingPoint sort");

    return m_manager->mk_func_decl(symbol("fp.to_real_unspecified"), 0, domain, m_real_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
}


func_decl * fpa_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                            unsigned arity, sort * const * domain, sort * range) {
    switch (k) {    
    case OP_FPA_MINUS_INF:
    case OP_FPA_PLUS_INF:
    case OP_FPA_NAN:
    case OP_FPA_MINUS_ZERO:
    case OP_FPA_PLUS_ZERO:
        return mk_float_const_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
    case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
    case OP_FPA_RM_TOWARD_POSITIVE:
    case OP_FPA_RM_TOWARD_NEGATIVE:
    case OP_FPA_RM_TOWARD_ZERO:
        return mk_rm_const_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_EQ:
    case OP_FPA_LT:
    case OP_FPA_GT:
    case OP_FPA_LE:
    case OP_FPA_GE:
        return mk_bin_rel_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_IS_ZERO:
    case OP_FPA_IS_NEGATIVE: 
    case OP_FPA_IS_POSITIVE:
    case OP_FPA_IS_NAN:
    case OP_FPA_IS_INF:
    case OP_FPA_IS_NORMAL:
    case OP_FPA_IS_SUBNORMAL:
        return mk_unary_rel_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_ABS: 
    case OP_FPA_NEG:
        return mk_unary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_REM:
    case OP_FPA_MIN:
    case OP_FPA_MAX:
        return mk_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_ADD:
    case OP_FPA_MUL:
    case OP_FPA_DIV:
        return mk_rm_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_SUB:
        if (arity == 1) 
            return mk_unary_decl(OP_FPA_NEG, num_parameters, parameters, arity, domain, range);
        else
            return mk_rm_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_SQRT:
    case OP_FPA_ROUND_TO_INTEGRAL:
        return mk_rm_unary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_FMA:
        return mk_fma(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_FP:
        return mk_fp(k, num_parameters, parameters, arity, domain, range);    
    case OP_FPA_TO_UBV:
        return mk_to_ubv(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_TO_SBV:
        return mk_to_sbv(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_TO_REAL:
        return mk_to_real(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_TO_FP:
        return mk_to_fp(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_TO_FP_UNSIGNED:
        return mk_to_fp_unsigned(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_TO_IEEE_BV:
        return mk_to_ieee_bv(k, num_parameters, parameters, arity, domain, range);

    case OP_FPA_INTERNAL_RM:
        return mk_internal_rm(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_INTERNAL_BVWRAP:
        return mk_internal_bv_wrap(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_INTERNAL_BVUNWRAP:
        return mk_internal_bv_unwrap(k, num_parameters, parameters, arity, domain, range);
    
    case OP_FPA_INTERNAL_MIN_I:
    case OP_FPA_INTERNAL_MAX_I:
    case OP_FPA_INTERNAL_MIN_UNSPECIFIED:
    case OP_FPA_INTERNAL_MAX_UNSPECIFIED:
        return mk_binary_decl(k, num_parameters, parameters, arity, domain, range);
    
    case OP_FPA_INTERNAL_TO_UBV_UNSPECIFIED:
        return mk_internal_to_ubv_unspecified(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_INTERNAL_TO_SBV_UNSPECIFIED:
        return mk_internal_to_sbv_unspecified(k, num_parameters, parameters, arity, domain, range);
    case OP_FPA_INTERNAL_TO_REAL_UNSPECIFIED:
        return mk_internal_to_real_unspecified(k, num_parameters, parameters, arity, domain, range);
    default:
        m_manager->raise_exception("unsupported floating point operator");
        return 0;
    }
}

void fpa_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    // These are the operators from the final draft of the SMT FloatingPoint standard
    op_names.push_back(builtin_name("+oo", OP_FPA_PLUS_INF));
    op_names.push_back(builtin_name("-oo", OP_FPA_MINUS_INF));
    op_names.push_back(builtin_name("+zero", OP_FPA_PLUS_ZERO));
    op_names.push_back(builtin_name("-zero", OP_FPA_MINUS_ZERO));
    op_names.push_back(builtin_name("NaN", OP_FPA_NAN));

    op_names.push_back(builtin_name("roundNearestTiesToEven", OP_FPA_RM_NEAREST_TIES_TO_EVEN));
    op_names.push_back(builtin_name("roundNearestTiesToAway", OP_FPA_RM_NEAREST_TIES_TO_AWAY));
    op_names.push_back(builtin_name("roundTowardPositive", OP_FPA_RM_TOWARD_POSITIVE));
    op_names.push_back(builtin_name("roundTowardNegative", OP_FPA_RM_TOWARD_NEGATIVE));
    op_names.push_back(builtin_name("roundTowardZero", OP_FPA_RM_TOWARD_ZERO));

    op_names.push_back(builtin_name("RNE", OP_FPA_RM_NEAREST_TIES_TO_EVEN));
    op_names.push_back(builtin_name("RNA", OP_FPA_RM_NEAREST_TIES_TO_AWAY));
    op_names.push_back(builtin_name("RTP", OP_FPA_RM_TOWARD_POSITIVE));
    op_names.push_back(builtin_name("RTN", OP_FPA_RM_TOWARD_NEGATIVE));
    op_names.push_back(builtin_name("RTZ", OP_FPA_RM_TOWARD_ZERO));

    op_names.push_back(builtin_name("fp.abs", OP_FPA_ABS));
    op_names.push_back(builtin_name("fp.neg", OP_FPA_NEG)); 
    op_names.push_back(builtin_name("fp.add", OP_FPA_ADD)); 
    op_names.push_back(builtin_name("fp.sub", OP_FPA_SUB));     
    op_names.push_back(builtin_name("fp.mul", OP_FPA_MUL)); 
    op_names.push_back(builtin_name("fp.div", OP_FPA_DIV));
    op_names.push_back(builtin_name("fp.fma", OP_FPA_FMA)); 
    op_names.push_back(builtin_name("fp.sqrt", OP_FPA_SQRT)); 
    op_names.push_back(builtin_name("fp.rem", OP_FPA_REM));
    op_names.push_back(builtin_name("fp.roundToIntegral", OP_FPA_ROUND_TO_INTEGRAL));
    op_names.push_back(builtin_name("fp.min", OP_FPA_MIN));
    op_names.push_back(builtin_name("fp.max", OP_FPA_MAX));      
    op_names.push_back(builtin_name("fp.leq", OP_FPA_LE));
    op_names.push_back(builtin_name("fp.lt",  OP_FPA_LT));    
    op_names.push_back(builtin_name("fp.geq", OP_FPA_GE));
    op_names.push_back(builtin_name("fp.gt",  OP_FPA_GT));
    op_names.push_back(builtin_name("fp.eq", OP_FPA_EQ));

    op_names.push_back(builtin_name("fp.isNormal", OP_FPA_IS_NORMAL));
    op_names.push_back(builtin_name("fp.isSubnormal", OP_FPA_IS_SUBNORMAL));
    op_names.push_back(builtin_name("fp.isZero", OP_FPA_IS_ZERO));
    op_names.push_back(builtin_name("fp.isInfinite", OP_FPA_IS_INF));
    op_names.push_back(builtin_name("fp.isNaN", OP_FPA_IS_NAN));
    op_names.push_back(builtin_name("fp.isNegative", OP_FPA_IS_NEGATIVE));
    op_names.push_back(builtin_name("fp.isPositive", OP_FPA_IS_POSITIVE));    

    op_names.push_back(builtin_name("fp", OP_FPA_FP));
    op_names.push_back(builtin_name("fp.to_ubv", OP_FPA_TO_UBV));
    op_names.push_back(builtin_name("fp.to_sbv", OP_FPA_TO_SBV));
    op_names.push_back(builtin_name("fp.to_real", OP_FPA_TO_REAL));
   
    op_names.push_back(builtin_name("to_fp", OP_FPA_TO_FP));
    op_names.push_back(builtin_name("to_fp_unsigned", OP_FPA_TO_FP_UNSIGNED));

    /* Extensions */
    op_names.push_back(builtin_name("to_ieee_bv", OP_FPA_TO_IEEE_BV));
}

void fpa_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("FloatingPoint", FLOATING_POINT_SORT));
    sort_names.push_back(builtin_name("RoundingMode", ROUNDING_MODE_SORT));

    // The final theory supports three common FloatingPoint sorts
    sort_names.push_back(builtin_name("Float16", FLOAT16_SORT));
    sort_names.push_back(builtin_name("Float32", FLOAT32_SORT));
    sort_names.push_back(builtin_name("Float64", FLOAT64_SORT));
    sort_names.push_back(builtin_name("Float128", FLOAT128_SORT));
}

expr * fpa_decl_plugin::get_some_value(sort * s) {
    if (s->is_sort_of(m_family_id, FLOATING_POINT_SORT)) {
        mpf tmp;
        m_fm.mk_nan(s->get_parameter(0).get_int(), s->get_parameter(1).get_int(), tmp);
        expr * res = mk_numeral(tmp);
        m_fm.del(tmp);
        return res;
    }
    else if (s->is_sort_of(m_family_id, ROUNDING_MODE_SORT)) {
        func_decl * f = mk_rm_const_decl(OP_FPA_RM_TOWARD_ZERO, 0, 0, 0, 0, s);
        return m_manager->mk_const(f);
    }
    
    UNREACHABLE();
    return 0;
}

bool fpa_decl_plugin::is_value(app * e) const {
    if (e->get_family_id() != m_family_id) 
        return false;
    switch (e->get_decl_kind()) {
    case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
    case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
    case OP_FPA_RM_TOWARD_POSITIVE:
    case OP_FPA_RM_TOWARD_NEGATIVE:
    case OP_FPA_RM_TOWARD_ZERO:
    case OP_FPA_NUM:
    case OP_FPA_PLUS_INF:
    case OP_FPA_MINUS_INF:
    case OP_FPA_PLUS_ZERO:
    case OP_FPA_MINUS_ZERO:
    case OP_FPA_NAN:
        return true;
    case OP_FPA_FP:
        return m_manager->is_value(e->get_arg(0)) &&
               m_manager->is_value(e->get_arg(1)) &&
               m_manager->is_value(e->get_arg(2));
    default:
        return false;
    }
}

bool fpa_decl_plugin::is_unique_value(app* e) const {
    if (e->get_family_id() != m_family_id)
        return false;
    switch (e->get_decl_kind()) {
    case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
    case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
    case OP_FPA_RM_TOWARD_POSITIVE:
    case OP_FPA_RM_TOWARD_NEGATIVE:
    case OP_FPA_RM_TOWARD_ZERO:
        return true;    
    case OP_FPA_PLUS_INF:  /* No; +oo == fp(#b0 #b11 #b00) */
    case OP_FPA_MINUS_INF: /* No; -oo == fp #b1 #b11 #b00) */
    case OP_FPA_PLUS_ZERO: /* No; +zero == fp #b0 #b00 #b000) */
    case OP_FPA_MINUS_ZERO: /* No; -zero == fp #b1 #b00 #b000) */
    case OP_FPA_NAN: /* No; NaN == (fp #b0 #b111111 #b0000001) */
    case OP_FPA_NUM: /* see NaN */
        return false;
    case OP_FPA_FP:
        return m_manager->is_unique_value(e->get_arg(0)) &&
            m_manager->is_unique_value(e->get_arg(1)) &&
            m_manager->is_unique_value(e->get_arg(2));
    default:
        return false;
    }
}

fpa_util::fpa_util(ast_manager & m):
    m_manager(m),
    m_fid(m.mk_family_id("fpa")),
    m_a_util(m),
    m_bv_util(m) {
    m_plugin = static_cast<fpa_decl_plugin*>(m.get_plugin(m_fid));
}

fpa_util::~fpa_util() {
}

sort * fpa_util::mk_float_sort(unsigned ebits, unsigned sbits) {
    parameter ps[2] = { parameter(ebits), parameter(sbits) };
    return m().mk_sort(m_fid, FLOATING_POINT_SORT, 2, ps);
}

unsigned fpa_util::get_ebits(sort * s) {
    SASSERT(is_float(s));
    return static_cast<unsigned>(s->get_parameter(0).get_int());
}

unsigned fpa_util::get_sbits(sort * s) {
    SASSERT(is_float(s));
    return static_cast<unsigned>(s->get_parameter(1).get_int());
}

app * fpa_util::mk_nan(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_nan(ebits, sbits, v);
    return mk_value(v);
}

app * fpa_util::mk_pinf(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_pinf(ebits, sbits, v);
    return mk_value(v);
}

app * fpa_util::mk_ninf(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_ninf(ebits, sbits, v);
    return mk_value(v);
}

app * fpa_util::mk_pzero(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_pzero(ebits, sbits, v);
    return mk_value(v);
}

app * fpa_util::mk_nzero(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_nzero(ebits, sbits, v);
    return mk_value(v);
}

app * fpa_util::mk_internal_to_ubv_unspecified(unsigned width) {    
    parameter ps[] = { parameter(width) };
    sort * range = m_bv_util.mk_sort(width);
    return m().mk_app(get_family_id(), OP_FPA_INTERNAL_TO_UBV_UNSPECIFIED, 1, ps, 0, 0, range);
}

app * fpa_util::mk_internal_to_sbv_unspecified(unsigned width) {
    parameter ps[] = { parameter(width) };
    sort * range = m_bv_util.mk_sort(width);
    return m().mk_app(get_family_id(), OP_FPA_INTERNAL_TO_SBV_UNSPECIFIED, 1, ps, 0, 0, range);
}

app * fpa_util::mk_internal_to_ieee_bv_unspecified(unsigned width) {
    parameter ps[] = { parameter(width) };
    sort * range = m_bv_util.mk_sort(width);
    return m().mk_app(get_family_id(), OP_FPA_INTERNAL_TO_SBV_UNSPECIFIED, 1, ps, 0, 0, range);
}

app * fpa_util::mk_internal_to_real_unspecified() {
    sort * range = m_a_util.mk_real();
    return m().mk_app(get_family_id(), OP_FPA_INTERNAL_TO_REAL_UNSPECIFIED, 0, 0, 0, 0, range);
}
