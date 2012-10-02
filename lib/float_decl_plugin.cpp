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

    family_id aid = m_manager->get_family_id("arith");
    m_real_sort = m_manager->mk_sort(aid, REAL_SORT);
    SASSERT(m_real_sort != 0); // arith_decl_plugin must be installed before float_decl_plugin.
    m_manager->inc_ref(m_real_sort);

    m_int_sort = m_manager->mk_sort(aid, INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before float_decl_plugin.
    m_manager->inc_ref(m_int_sort);
    
    if (m_manager->has_plugin(symbol("bv"))) {
        // bv plugin is optional, so m_bv_plugin may be 0
        m_bv_fid = m_manager->get_family_id("bv");
        m_bv_plugin = static_cast<bv_decl_plugin*>(m_manager->get_plugin(m_bv_fid));
    }
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
    return false;
}

bool float_decl_plugin::is_rm(expr * n, mpf_rounding_mode & val) {
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
    return m_manager->mk_sort(symbol("FP"), sort_info(m_family_id, FLOAT_SORT, sz, 2, ps));
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
        return mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
    case ROUNDING_MODE_SORT:
        return mk_rm_sort();
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
    else if (range != 0 && is_float_sort(range)) {
        s = range;
    }
    else {
        m_manager->raise_exception("sort of floating point constant was not specified");
    }

    SASSERT(is_sort_of(s, m_family_id, FLOAT_SORT));
    
    unsigned ebits = s->get_parameter(0).get_int();
    unsigned sbits = s->get_parameter(1).get_int();
    scoped_mpf val(m_fm);
    if (k == OP_FLOAT_NAN) {
        m_fm.mk_nan(ebits, sbits, val);
        SASSERT(m_fm.is_nan(val));
    }
    else if (k == OP_FLOAT_MINUS_INF) {
        m_fm.mk_ninf(ebits, sbits, val);
    }
    else {
        SASSERT(k == OP_FLOAT_PLUS_INF);
        m_fm.mk_pinf(ebits, sbits, val);
    }
    return mk_value_decl(val);
}

func_decl * float_decl_plugin::mk_bin_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                               unsigned arity, sort * const * domain, sort * range) {
    if (arity != 2)
        m_manager->raise_exception("invalid number of arguments to floating point relation");
    if (domain[0] != domain[1] || !is_float_sort(domain[0]))
        m_manager->raise_exception("sort mismatch");
    symbol name;
    switch (k) {
    case OP_FLOAT_EQ: name = "==";  break;
    case OP_FLOAT_LT: name = "<";   break;
    case OP_FLOAT_GT: name = ">";   break;        
    case OP_FLOAT_LE: name = "<=";  break;        
    case OP_FLOAT_GE: name = ">=";  break;        
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
        m_manager->raise_exception("sort mismatch");
    symbol name;
    switch (k) {
    case OP_FLOAT_IS_ZERO: name = "isZero";  break;
    case OP_FLOAT_IS_NZERO: name = "isNZero";   break;
    case OP_FLOAT_IS_PZERO: name = "isPZero";   break;        
    case OP_FLOAT_IS_SIGN_MINUS: name = "isSignMinus";  break;        
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
        m_manager->raise_exception("sort mismatch"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_ABS:    name = "abs";  break;
    case OP_FLOAT_UMINUS: name = "-";   break;
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
        m_manager->raise_exception("sort mismatch"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_REM: name = "remainder";  break;
    case OP_FLOAT_MIN: name = "min";   break;
    case OP_FLOAT_MAX: name = "max";   break;
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
    if (!is_rm_sort(domain[0]) || domain[1] != domain[2] || !is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_ADD: name = "+";   break;
    case OP_FLOAT_SUB: name = "-";   break;
    case OP_FLOAT_MUL: name = "*";   break;
    case OP_FLOAT_DIV: name = "/";   break;
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
    if (!is_rm_sort(domain[0]) || !is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch"); 
    symbol name;
    switch (k) {
    case OP_FLOAT_SQRT: name = "squareRoot";   break;
    case OP_FLOAT_ROUND_TO_INTEGRAL: name = "roundToIntegral";   break;
    default:
        UNREACHABLE();
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_fused_ma(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {
    if (arity != 4)
        m_manager->raise_exception("invalid number of arguments to fused_ma operator");
    if (!is_rm_sort(domain[0]) || domain[1] != domain[2] || domain[1] != domain[3] || !is_float_sort(domain[1]))
        m_manager->raise_exception("sort mismatch"); 
    symbol name("fusedMA");
    return m_manager->mk_func_decl(name, arity, domain, domain[1], func_decl_info(m_family_id, k));
}

func_decl * float_decl_plugin::mk_to_float(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {    
    if (m_bv_plugin && arity == 3 && 
        is_sort_of(domain[0], m_bv_fid, BV_SORT) &&
        is_sort_of(domain[1], m_bv_fid, BV_SORT) &&
        is_sort_of(domain[2], m_bv_fid, BV_SORT)) {
        // When the bv_decl_plugin is installed, then we know how to convert 3 bit-vectors into a float!        
        sort * fp = mk_float_sort(domain[2]->get_parameter(0).get_int(), domain[1]->get_parameter(0).get_int()+1);
        symbol name("asFloat");
        return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));    
    }
    else {
        // .. Otherwise we only know how to convert rationals/reals. 
        if (!(num_parameters == 2 && parameters[0].is_int() && parameters[1].is_int())) 
            m_manager->raise_exception("expecting two integer parameters to asFloat");        
		if (arity != 2 && arity != 3)
			m_manager->raise_exception("invalid number of arguments to asFloat operator");
		if (!is_rm_sort(domain[0]) || domain[1] != m_real_sort)
            m_manager->raise_exception("sort mismatch");
        if (arity == 2) {            
            sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
            symbol name("asFloat");
            return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
        }
        else {
            if (domain[2] != m_int_sort)
                m_manager->raise_exception("sort mismatch");     
            sort * fp = mk_float_sort(parameters[0].get_int(), parameters[1].get_int());
            symbol name("asFloat");
            return m_manager->mk_func_decl(name, arity, domain, fp, func_decl_info(m_family_id, k, num_parameters, parameters));
        }
    }
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
    case OP_FLOAT_IS_SIGN_MINUS: 
        return mk_unary_rel_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_ABS: 
    case OP_FLOAT_UMINUS:
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
            return mk_unary_decl(OP_FLOAT_UMINUS, num_parameters, parameters, arity, domain, range);
        else
            return mk_rm_binary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_SQRT:
    case OP_FLOAT_ROUND_TO_INTEGRAL:
        return mk_rm_unary_decl(k, num_parameters, parameters, arity, domain, range);
    case OP_FLOAT_FUSED_MA:
        return mk_fused_ma(k, num_parameters, parameters, arity, domain, range);
    default:
        m_manager->raise_exception("unsupported floating point operator");
        return 0;
    }
}

void float_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.push_back(builtin_name("plusInfinity",  OP_FLOAT_PLUS_INF));
    op_names.push_back(builtin_name("minusInfinity", OP_FLOAT_MINUS_INF));
    op_names.push_back(builtin_name("NaN", OP_FLOAT_NAN));
    op_names.push_back(builtin_name("roundNearestTiesToEven", OP_RM_NEAREST_TIES_TO_EVEN));
    op_names.push_back(builtin_name("roundNearestTiesToAway", OP_RM_NEAREST_TIES_TO_AWAY));
    op_names.push_back(builtin_name("roundTowardPositive", OP_RM_TOWARD_POSITIVE));
    op_names.push_back(builtin_name("roundTowardNegative", OP_RM_TOWARD_NEGATIVE));
    op_names.push_back(builtin_name("roundTowardZero", OP_RM_TOWARD_ZERO));
    
    op_names.push_back(builtin_name("+", OP_FLOAT_ADD)); 
    op_names.push_back(builtin_name("-", OP_FLOAT_SUB)); 
    op_names.push_back(builtin_name("/", OP_FLOAT_DIV)); 
    op_names.push_back(builtin_name("*", OP_FLOAT_MUL)); 

    op_names.push_back(builtin_name("abs", OP_FLOAT_ABS)); 
    op_names.push_back(builtin_name("remainder", OP_FLOAT_REM));  
    op_names.push_back(builtin_name("fusedMA", OP_FLOAT_FUSED_MA));  
    op_names.push_back(builtin_name("squareRoot", OP_FLOAT_SQRT));  
    op_names.push_back(builtin_name("roundToIntegral", OP_FLOAT_ROUND_TO_INTEGRAL));  
    
    op_names.push_back(builtin_name("==", OP_FLOAT_EQ));
    
    op_names.push_back(builtin_name("<",  OP_FLOAT_LT));
    op_names.push_back(builtin_name(">",  OP_FLOAT_GT));
    op_names.push_back(builtin_name("<=", OP_FLOAT_LE));
    op_names.push_back(builtin_name(">=", OP_FLOAT_GE));

    op_names.push_back(builtin_name("isZero", OP_FLOAT_IS_ZERO));
    op_names.push_back(builtin_name("isNZero", OP_FLOAT_IS_NZERO));
    op_names.push_back(builtin_name("isPZero", OP_FLOAT_IS_PZERO));
    op_names.push_back(builtin_name("isSignMinus", OP_FLOAT_IS_SIGN_MINUS));

    op_names.push_back(builtin_name("min", OP_FLOAT_MIN));
    op_names.push_back(builtin_name("max", OP_FLOAT_MAX));

    op_names.push_back(builtin_name("asFloat", OP_TO_FLOAT));    
}

void float_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("FP", FLOAT_SORT));
    sort_names.push_back(builtin_name("RoundingMode", ROUNDING_MODE_SORT));
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
        return true;
    case OP_TO_FLOAT:
        return m_manager->is_value(e->get_arg(0));
    default:
        return false;
    }
}

float_util::float_util(ast_manager & m):
    m_manager(m),
    m_fid(m.get_family_id("float")),
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

