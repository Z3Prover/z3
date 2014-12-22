/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    float_decl_plugin.cpp

Abstract:

    Floating point decl plugin

Author:

    Leonardo de Moura (leonardo) 2012-01-15.

Revision History:

--*/
#include"float_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"

float_decl_plugin::float_decl_plugin():
    m_values(m_fm),
    m_value_table(mpf_hash_proc(m_values), mpf_eq_proc(m_values)) {
    m_real_sort = 0;
    m_int_sort  = 0;
    m_bv_plugin = 0;
}

void float_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    family_id aid = m_manager->mk_family_id("arith");
    m_real_sort = m_manager->mk_sort(aid, REAL_SORT);
    SASSERT(m_real_sort != 0); // arith_decl_plugin must be installed before float_decl_plugin.
    m_manager->inc_ref(m_real_sort);

    m_int_sort = m_manager->mk_sort(aid, INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before float_decl_plugin.
    m_manager->inc_ref(m_int_sort);
    
    // BV is not optional anymore.
    SASSERT(m_manager->has_plugin(symbol("bv")));        
        m_bv_fid = m_manager->mk_family_id("bv");
        m_bv_plugin = static_cast<bv_decl_plugin*>(m_manager->get_plugin(m_bv_fid));
}

float_decl_plugin::~float_decl_plugin() {
}

unsigned float_decl_plugin::mk_id(mpf const & v) {
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

void float_decl_plugin::recycled_id(unsigned id) {
    SASSERT(m_value_table.contains(id));
    m_value_table.erase(id);
    m_id_gen.recycle(id);
    m_fm.del(m_values[id]);
}

func_decl * float_decl_plugin::mk_value_decl(mpf const & v) {
    parameter p(mk_id(v), true);
    SASSERT(p.is_external());
    sort * s = mk_float_sort(v.get_ebits(), v.get_sbits());
    return m_manager->mk_const_decl(symbol("float"),  s, func_decl_info(m_family_id, OP_FLOAT_VALUE, 1, &p));
}

app * float_decl_plugin::mk_value(mpf const & v) {
    return m_manager->mk_const(mk_value_decl(v));
}

bool float_decl_plugin::is_value(expr * n, mpf & val) {
    if (is_app_of(n, m_family_id, OP_FLOAT_VALUE)) {
        m_fm.set(val, m_values[to_app(n)->get_decl()->get_parameter(0).get_ext_id()]);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FLOAT_MINUS_INF)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_ninf(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FLOAT_PLUS_INF)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_pinf(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FLOAT_NAN)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_nan(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FLOAT_PLUS_ZERO)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_pzero(ebits, sbits, val);
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_FLOAT_MINUS_ZERO)) {
        unsigned ebits = to_app(n)->get_decl()->get_range()->get_parameter(0).get_int();
        unsigned sbits = to_app(n)->get_decl()->get_range()->get_parameter(1).get_int();
        m_fm.mk_nzero(ebits, sbits, val);
        return true;
    }
    return false;
}

bool float_decl_plugin::is_rm_value(expr * n, mpf_rounding_mode & val) {
    if (is_app_of(n, m_family_id, OP_RM_NEAREST_TIES_TO_AWAY)) {
        val = MPF_ROUND_NEAREST_TAWAY;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_RM_NEAREST_TIES_TO_EVEN)) {
        val = MPF_ROUND_NEAREST_TEVEN;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_RM_TOWARD_NEGATIVE)) {
        val = MPF_ROUND_TOWARD_NEGATIVE;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_RM_TOWARD_POSITIVE)) {
        val = MPF_ROUND_TOWARD_POSITIVE;
        return true;
    }
    else if (is_app_of(n, m_family_id, OP_RM_TOWARD_ZERO)) {
        val = MPF_ROUND_TOWARD_ZERO;
        return true;
    }

    return 0;
}

void float_decl_plugin::del(parameter const & p) {
    SASSERT(p.is_external());
    recycled_id(p.get_ext_id());
}

parameter float_decl_plugin::translate(parameter const & p, decl_plugin & target) {
    SASSERT(p.is_external());
    float_decl_plugin & _target = static_cast<float_decl_plugin&>(target);
    return parameter(_target.mk_id(m_values[p.get_ext_id()]), true);
}

void float_decl_plugin::finalize() {
    if (m_real_sort) { m_manager->dec_ref(m_real_sort); }
    if (m_int_sort)  { m_manager->dec_ref(m_int_sort); }
}

decl_plugin * float_decl_plugin::mk_fresh() { 
    return alloc(float_decl_plugin); 
}

sort * float_decl_plugin::mk_float_sort(unsigned ebits, unsigned sbits) {
    parameter p1(ebits), p2(sbits);
    parameter ps[2] = { p1, p2 };
    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("FloatingPoint"), sort_info(m_family_id, FLOAT_SORT, sz, 2, ps));
}

sort * float_decl_plugin::mk_rm_sort() {
    return m_manager->mk_sort(symbol("RoundingMode"), sort_info(m_family_id, ROUNDING_MODE_SORT));
}

sort * float_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case FLOAT_SORT:
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int())) {
            m_manager->raise_exception("expecting two integer parameters to floating point sort");
        }
        if (parameters[0].get_int() <= 1 || parameters[1].get_int() <= 1)
            m_manager->raise_exception("floating point sorts need parameters > 1");
        if (parameters[0].get_int() > parameters[1].get_int())
            m_manager->raise_exception("floating point sorts with ebits > sbits are currently not supported");
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
        return mk_float_sort(15, 133);
    default:
        m_manager->raise_exception("unknown floating point theory sort");
        return 0;
    }
}

func_decl * float_decl_plugin::mk_rm_const_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                unsigned arity, sort * const * domain, sort * range) {
    if (num_parameters != 0)
        m_manager->raise_exception("rounding mode constant does not have parameters");
    if (arity != 0)
        m_manager->raise_exception("rounding mode is a constant");
    sort * s = mk_rm_sort();
    func_decl_info finfo(m_family_id, k);
    switch (k) {
    case OP_RM_NEAREST_TIES_TO_EVEN:
        return m_manager->mk_const_decl(symbol("roundNearestTiesToEven"), s, finfo);
    case OP_RM_NEAREST_TIES_TO_AWAY:
        return m_manager->mk_const_decl(symbol("roundNearestTiesToAway"), s, finfo);
    case OP_RM_TOWARD_POSITIVE:
        return m_manager->mk_const_decl(symbol("roundTowardPositive"), s, finfo);
    case OP_RM_TOWARD_NEGATIVE:
        return m_manager->mk_const_decl(symbol("roundTowardNegative"), s, finfo);
    case OP_RM_TOWARD_ZERO:
        return m_manager->mk_const_decl(symbol("roundTowardZero"), s, finfo);
    default:
        UNREACHABLE();
        return 0;
    }
}

func_decl * float_decl_plugin::mk_float_const_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                   unsigned arity, sort * const * domain, sort * range) {
    sort * s;
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

    SASSERT(is_sort_of(s, m_family_id, FLOAT_SORT));
    
    unsigned ebits = s->get_parameter(0).get_int();
    unsigned sbits = s->get_parameter(1).get_int();
    scoped_mpf val(m_fm);

    switch (k)
    {
    case OP_FLOAT_NAN: m_fm.mk_nan(ebits, sbits, val);
        SASSERT(m_fm.is_nan(val));
        break;
    case OP_FLOAT_MINUS_INF: m_fm.mk_ninf(ebits, sbits, val); break;
    case OP_FLOAT_PLUS_INF: m_fm.mk_pinf(ebits, sbits, val); break;
    case OP_FLOAT_MINUS_ZERO: m_fm.mk_nzero(ebits, sbits, val); break;
    case OP_FLOAT_PLUS_ZERO: m_fm.mk_pzero(ebits, sbits, val); break;
    }

    return mk_value_decl(val);
}

func_decl * float_decl_plugin::mk_bin_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                               unsigned arity, sort * const * domain, sort * range) {
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to floating point relation");
    if (domain[0] != domain[1] || !is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected equal FloatingPoint sorts as arguments");
    symbol name;
    switch (k) {
    case OP_FLOAT_EQ: name = "fp.eq";  break;
    case OP_FLOAT_LT: name = "fp.lt";   break;
    case OP_FLOAT_GT: name = "fp.gt";   break;        
    case OP_FLOAT_LE: name = "fp.lte";  break;        
    case OP_FLOAT_GE: name = "fp.gte";  break;        
    default:
        UNREACHABLE();
        break;
    }
    func_decl_info finfo(m_family_id, k);
    finfo.set_chainable(true);
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), finfo);
}

func_decl * float_decl_plugin::mk_unary_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                 unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to floating point relation");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort");
    symbol name;
    switch (k) {
    case OP_FLOAT_IS_ZERO: name = "fp.isZero";  break;
    case OP_FLOAT_IS_NZERO: name = "fp.isNZero";   break;
    case OP_FLOAT_IS_PZERO: name = "fp.isPZero";   break;        
    case OP_FLOAT_IS_NEGATIVE: name = "fp.isNegative";  break;
    case OP_FLOAT_IS_POSITIVE: name = "fp.isPositive";  break;
    case OP_FLOAT_IS_NAN: name = "fp.isNaN";  break;
    case OP_FLOAT_IS_INF: name = "fp.isInfinite";  break;
    case OP_FLOAT_IS_NORMAL: name = "fp.isNormal";  break;
    case OP_FLOAT_IS_SUBNORMAL: name = "fp.isSubnormal";  break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_unary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                             unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_ABS: name = "fp.abs"; break;
    case OP_FLOAT_NEG: name = "fp.neg"; break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[0], func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_binary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                              unsigned arity, sort * const * domain, sort * range) {
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (domain[0] != domain[1] || !is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected arguments of equal FloatingPoint sorts"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_REM: name = "fp.rem"; break;
    case OP_FLOAT_MIN: name = "fp.min"; break;
    case OP_FLOAT_MAX: name = "fp.max"; break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[0], func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_rm_binary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                 unsigned arity, sort * const * domain, sort * range) {
    if (arity != 3)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
    if (domain[1] != domain[2] || !is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch, expected arguments 1 and 2 of equal FloatingPoint sorts"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_ADD: name = "fp.add";   break;
    case OP_FLOAT_SUB: name = "fp.sub";   break;
    case OP_FLOAT_MUL: name = "fp.mul";   break;
    case OP_FLOAT_DIV: name = "fp.div";   break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_rm_unary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                unsigned arity, sort * const * domain, sort * range) {
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to floating point operator");
    if (!is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected RoundingMode as first argument");
    if (!is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch, expected FloatingPoint as second argument"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_SQRT: name = "fp.sqrt";   break;
    case OP_FLOAT_ROUND_TO_INTEGRAL: name = "fp.roundToIntegral";   break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_fma(decl_kind k, unsigned num_parameters, parameter const * parameters,
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

func_decl * float_decl_plugin::mk_to_float(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {    
    if (m_bv_plugin && arity == 3 && 
        is_sort_of(domain[0], m_bv_fid, BV_SORT) &&
        is_sort_of(domain[1], m_bv_fid, BV_SORT) &&
        is_sort_of(domain[2], m_bv_fid, BV_SORT)) {
        // 3 BVs -> 1 FP
        sort * fp = mk_float_sort(domain[2]->get_parameter(0).get_int(), domain[1]->get_parameter(0).get_int()+1);
        symbol name("fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else if (m_bv_plugin && arity == 1 && is_sort_of(domain[0], m_bv_fid, BV_SORT)) {
        // 1 BV -> 1 FP
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
    else if (m_bv_plugin && arity == 2 && 
             is_sort_of(domain[0], m_family_id, ROUNDING_MODE_SORT) &&
             is_sort_of(domain[1], m_bv_fid, BV_SORT)) {
        // Rounding + 1 BV -> 1 FP
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
             is_sort_of(domain[1], m_family_id, FLOAT_SORT)) {
        // Rounding + 1 FP -> 1 FP
        if (num_parameters != 2)
            m_manager->raise_exception("invalid number of parameters to to_fp");
        if (!parameters[0].is_int() || !parameters[1].is_int())
            m_manager->raise_exception("invalid parameter type to to_fp");
        int ebits = parameters[0].get_int();
        int sbits = parameters[1].get_int();        
        if (!is_rm_sort(domain[0]))
            m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
        if (!is_sort_of(domain[1], m_family_id, FLOAT_SORT))
            m_manager->raise_exception("sort mismatch, expected second argument of FloatingPoint sort");
        
        sort * fp = mk_float_sort(ebits, sbits);
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    else {
        // 1 Real -> 1 FP
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int())) 
            m_manager->raise_exception("expecting two integer parameters to to_fp");        
        if (arity != 2 && arity != 3)
            m_manager->raise_exception("invalid number of arguments to to_fp operator");
        if (arity == 3 && domain[2] != m_int_sort)
            m_manager->raise_exception("sort mismatch, expected second argument of Int sort");     
        if (domain[1] != m_real_sort)
            m_manager->raise_exception("sort mismatch, expected second argument of Real sort");
        
        sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
        symbol name("to_fp");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));            
    }
}

func_decl * float_decl_plugin::mk_float_to_ieee_bv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                             unsigned arity, sort * const * domain, sort * range) {
    if (arity != 1)
        m_manager->raise_exception("invalid number of arguments to asIEEEBV");
    if (!is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected argument of FloatingPoint sort");
    
    unsigned float_sz = domain[0]->get_parameter(0).get_int() + domain[0]->get_parameter(1).get_int();
    parameter ps[] = { parameter(float_sz) };
    sort * bv_srt = m_bv_plugin->mk_sort(m_bv_fid, 1, ps);
    symbol name("asIEEEBV");
    return m_manager->mk_func_decl(name, 1, domain, bv_srt, func_decl_info(m_family_id, k, num_parameters, parameters));        
}

func_decl * float_decl_plugin::mk_from3bv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {
    if (arity != 3)
        m_manager->raise_exception("invalid number of arguments to fp");    
    if (!is_sort_of(domain[0], m_bv_fid, BV_SORT) ||
        !is_sort_of(domain[1], m_bv_fid, BV_SORT) ||
        !is_sort_of(domain[2], m_bv_fid, BV_SORT))
        m_manager->raise_exception("sort mismatch");
        
    sort * fp = mk_float_sort(domain[1]->get_parameter(0).get_int(), domain[2]->get_parameter(0).get_int() + 1);
    symbol name("fp");
    return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_to_ubv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                 unsigned arity, sort * const * domain, sort * range) {
    if (!m_bv_plugin)
        m_manager->raise_exception("to_fp_unsigned unsupported; use a logic with BV support");
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to to_fp_unsigned");
    if (is_rm_sort(domain[0]))
        m_manager->raise_exception("sort mismatch, expected first argument of RoundingMode sort");
    if (!is_sort_of(domain[1], m_bv_fid, BV_SORT))
        m_manager->raise_exception("sort mismatch, expected second argument of BV sort");

    sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
    symbol name("fp.t_ubv");
    return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_to_sbv(decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range) {
    NOT_IMPLEMENTED_YET();
}

func_decl * float_decl_plugin::mk_to_real(decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range) {
    NOT_IMPLEMENTED_YET();
}

func_decl * float_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                            unsigned arity, sort * const * domain, sort * range) {
    switch (k) {
    case OP_TO_FLOAT:
        return mk_to_float(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_MINUS_INF:
    case OP_FLOAT_PLUS_INF:
    case OP_FLOAT_NAN:
        return mk_float_const_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_RM_NEAREST_TIES_TO_EVEN:
    case OP_RM_NEAREST_TIES_TO_AWAY:
    case OP_RM_TOWARD_POSITIVE:
    case OP_RM_TOWARD_NEGATIVE:
    case OP_RM_TOWARD_ZERO:
        return mk_rm_const_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_EQ:
    case OP_FLOAT_LT:
    case OP_FLOAT_GT:
    case OP_FLOAT_LE:
    case OP_FLOAT_GE:
        return mk_bin_rel_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_IS_ZERO:
    case OP_FLOAT_IS_NZERO:
    case OP_FLOAT_IS_PZERO:
    case OP_FLOAT_IS_NEGATIVE: 
    case OP_FLOAT_IS_POSITIVE:
    case OP_FLOAT_IS_NAN:
    case OP_FLOAT_IS_INF:
    case OP_FLOAT_IS_NORMAL:
    case OP_FLOAT_IS_SUBNORMAL:
        return mk_unary_rel_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_ABS: 
    case OP_FLOAT_NEG:
        return mk_unary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_REM:
    case OP_FLOAT_MIN:
    case OP_FLOAT_MAX:
        return mk_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_ADD:
    case OP_FLOAT_MUL:
    case OP_FLOAT_DIV:
        return mk_rm_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_SUB:
        if (arity == 1) 
            return mk_unary_decl(OP_FLOAT_NEG, num_parameters, parameters, arity, domain, range);
        else
            return mk_rm_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_SQRT:
    case OP_FLOAT_ROUND_TO_INTEGRAL:
        return mk_rm_unary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_FMA:
        return mk_fma(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_TO_IEEE_BV:
        return mk_float_to_ieee_bv(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_FP:
        return mk_from3bv(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_TO_UBV:
        return mk_to_ubv(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_TO_SBV:
        return mk_to_sbv(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_TO_REAL:
        return mk_to_real(k, num_parameters, parameters, arity, domain, range);
    default:
        m_manager->raise_exception("unsupported floating point operator");
        return 0;
    }
}

void float_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    // These are the operators from the final draft of the SMT FloatingPoint standard
    op_names.push_back(builtin_name("+oo", OP_FLOAT_PLUS_INF));
    op_names.push_back(builtin_name("-oo", OP_FLOAT_MINUS_INF));
    op_names.push_back(builtin_name("+zero", OP_FLOAT_PLUS_ZERO));
    op_names.push_back(builtin_name("-zero", OP_FLOAT_MINUS_ZERO));
    op_names.push_back(builtin_name("NaN", OP_FLOAT_NAN));

    op_names.push_back(builtin_name("roundNearestTiesToEven", OP_RM_NEAREST_TIES_TO_EVEN));
    op_names.push_back(builtin_name("roundNearestTiesToAway", OP_RM_NEAREST_TIES_TO_AWAY));
    op_names.push_back(builtin_name("roundTowardPositive", OP_RM_TOWARD_POSITIVE));
    op_names.push_back(builtin_name("roundTowardNegative", OP_RM_TOWARD_NEGATIVE));
    op_names.push_back(builtin_name("roundTowardZero", OP_RM_TOWARD_ZERO));
    
    op_names.push_back(builtin_name("RNE", OP_RM_NEAREST_TIES_TO_EVEN));
    op_names.push_back(builtin_name("RNA", OP_RM_NEAREST_TIES_TO_AWAY));
    op_names.push_back(builtin_name("RTP", OP_RM_TOWARD_POSITIVE));
    op_names.push_back(builtin_name("RTN", OP_RM_TOWARD_NEGATIVE));
    op_names.push_back(builtin_name("RTZ", OP_RM_TOWARD_ZERO));

    op_names.push_back(builtin_name("fp.abs", OP_FLOAT_ABS));
    op_names.push_back(builtin_name("fp.neg", OP_FLOAT_NEG)); 
    op_names.push_back(builtin_name("fp.add", OP_FLOAT_ADD)); 
    op_names.push_back(builtin_name("fp.sub", OP_FLOAT_SUB));     
    op_names.push_back(builtin_name("fp.mul", OP_FLOAT_MUL)); 
    op_names.push_back(builtin_name("fp.div", OP_FLOAT_DIV));
    op_names.push_back(builtin_name("fp.fma", OP_FLOAT_FMA)); 
    op_names.push_back(builtin_name("fp.sqrt", OP_FLOAT_SQRT)); 
    op_names.push_back(builtin_name("fp.rem", OP_FLOAT_REM));  
    op_names.push_back(builtin_name("fp.roundToIntegral", OP_FLOAT_ROUND_TO_INTEGRAL));
    op_names.push_back(builtin_name("fp.min", OP_FLOAT_MIN));
    op_names.push_back(builtin_name("fp.max", OP_FLOAT_MAX));      
    op_names.push_back(builtin_name("fp.leq", OP_FLOAT_LE));
    op_names.push_back(builtin_name("fp.lt",  OP_FLOAT_LT));    
    op_names.push_back(builtin_name("fp.geq", OP_FLOAT_GE));
    op_names.push_back(builtin_name("fp.gt",  OP_FLOAT_GT));
    op_names.push_back(builtin_name("fp.eq", OP_FLOAT_EQ));

    op_names.push_back(builtin_name("fp.isNormal", OP_FLOAT_IS_NORMAL));
    op_names.push_back(builtin_name("fp.isSubnormal", OP_FLOAT_IS_SUBNORMAL));
    op_names.push_back(builtin_name("fp.isZero", OP_FLOAT_IS_ZERO));
    op_names.push_back(builtin_name("fp.isInfinite", OP_FLOAT_IS_INF));
    op_names.push_back(builtin_name("fp.isNaN", OP_FLOAT_IS_NAN));
    op_names.push_back(builtin_name("fp.isNegative", OP_FLOAT_IS_NEGATIVE));
    op_names.push_back(builtin_name("fp.isPositive", OP_FLOAT_IS_POSITIVE));    

    op_names.push_back(builtin_name("fp", OP_FLOAT_FP));
    op_names.push_back(builtin_name("fp.to_ubv", OP_FLOAT_TO_UBV));
    op_names.push_back(builtin_name("fp.to_sbv", OP_FLOAT_TO_SBV));
        
    op_names.push_back(builtin_name("to_fp", OP_TO_FLOAT));    
}

void float_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("FloatingPoint", FLOAT_SORT));
    sort_names.push_back(builtin_name("RoundingMode", ROUNDING_MODE_SORT));

    // The final theory supports three common FloatingPoint sorts
    sort_names.push_back(builtin_name("Float16", FLOAT16_SORT));
    sort_names.push_back(builtin_name("Float32", FLOAT32_SORT));
    sort_names.push_back(builtin_name("Float64", FLOAT64_SORT));
    sort_names.push_back(builtin_name("Float128", FLOAT128_SORT));
}

expr * float_decl_plugin::get_some_value(sort * s) {
    SASSERT(s->is_sort_of(m_family_id, FLOAT_SORT));    
    mpf tmp;
    m_fm.mk_nan(s->get_parameter(0).get_int(), s->get_parameter(1).get_int(), tmp);
    expr * res = this->mk_value(tmp);
    m_fm.del(tmp);
    return res;
}

bool float_decl_plugin::is_value(app * e) const {
    if (e->get_family_id() != m_family_id) 
        return false;
    switch (e->get_decl_kind()) {
    case OP_RM_NEAREST_TIES_TO_EVEN:
    case OP_RM_NEAREST_TIES_TO_AWAY:
    case OP_RM_TOWARD_POSITIVE:
    case OP_RM_TOWARD_NEGATIVE:
    case OP_RM_TOWARD_ZERO:
    case OP_FLOAT_VALUE:
    case OP_FLOAT_PLUS_INF:
    case OP_FLOAT_MINUS_INF:
    case OP_FLOAT_PLUS_ZERO:
    case OP_FLOAT_MINUS_ZERO:
    case OP_FLOAT_NAN:
        return true;
    case OP_TO_FLOAT:
        return m_manager->is_value(e->get_arg(0));
    default:
        return false;
    }
}

float_util::float_util(ast_manager & m):
    m_manager(m),
    m_fid(m.mk_family_id("float")),
    m_a_util(m) {
    m_plugin = static_cast<float_decl_plugin*>(m.get_plugin(m_fid));
}

float_util::~float_util() {
}

sort * float_util::mk_float_sort(unsigned ebits, unsigned sbits) {
    parameter ps[2] = { parameter(ebits), parameter(sbits) };
    return m().mk_sort(m_fid, FLOAT_SORT, 2, ps);
}

unsigned float_util::get_ebits(sort * s) {
    SASSERT(is_float(s));
    return static_cast<unsigned>(s->get_parameter(0).get_int());
}

unsigned float_util::get_sbits(sort * s) {
    SASSERT(is_float(s));
    return static_cast<unsigned>(s->get_parameter(1).get_int());
}

app * float_util::mk_nan(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_nan(ebits, sbits, v);
    return mk_value(v);
}

app * float_util::mk_plus_inf(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_pinf(ebits, sbits, v);
    return mk_value(v);
}

app * float_util::mk_minus_inf(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_ninf(ebits, sbits, v);
    return mk_value(v);
}

app * float_util::mk_pzero(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_pzero(ebits, sbits, v);
    return mk_value(v);
}

app * float_util::mk_nzero(unsigned ebits, unsigned sbits) {
    scoped_mpf v(fm());
    fm().mk_nzero(ebits, sbits, v);
    return mk_value(v);
}

