#include "jlcxx/jlcxx.hpp"
#include "z3++.h"

using namespace z3;

#define MM(CLASS, FUNC) method(#FUNC, &CLASS::FUNC)

#define BINARY_OP(TYPE, FNAME, OP) \
    method(#FNAME, [](const TYPE &a, const TYPE &b) { return a OP b; })
#define UNARY_OP(TYPE, FNAME, OP) \
    method(#FNAME, [](const TYPE &a) { return OP a; })
#define BINARY_FN(TYPE, FNAME, FN) \
    method(#FNAME, static_cast<expr (*)(const TYPE &, const TYPE &)>(&FN))

#define GETINDEX(TYPE) \
    method("getindex", [](const TYPE &x, int i) { return x[i - 1]; })

#define STRING(TYPE)                     \
    method("string", [](const TYPE &x) { \
        std::ostringstream stream;       \
        stream << x;                     \
        return stream.str();             \
    })

#define ADD_TYPE(MODULE, CLASS, NAME) \
    jlcxx::TypeWrapper<CLASS> wrapper_##CLASS = MODULE.add_type<CLASS>(#NAME)

#define ADD_SUBTYPE(MODULE, CLASS, NAME, SUPER) \
    jlcxx::TypeWrapper<CLASS> wrapper_##CLASS = MODULE.add_type<CLASS>(#NAME, jlcxx::julia_base_type<SUPER>())

#define TYPE_OBJ(CLASS) wrapper_##CLASS

namespace jlcxx
{
    template<> struct IsMirroredType<check_result>  : std::true_type {};
    template<> struct IsMirroredType<rounding_mode> : std::true_type {};

    template<> struct SuperType<solver>       { typedef object type; };
    template<> struct SuperType<goal>         { typedef object type; };
    template<> struct SuperType<apply_result> { typedef object type; };
    template<> struct SuperType<tactic>       { typedef object type; };
    template<> struct SuperType<probe>        { typedef object type; };
    template<> struct SuperType<optimize>     { typedef object type; };
    template<> struct SuperType<fixedpoint>   { typedef object type; };
    template<> struct SuperType<param_descrs> { typedef object type; };
    template<> struct SuperType<params>       { typedef object type; };
    template<> struct SuperType<ast>          { typedef object type; };
    template<> struct SuperType<func_entry>   { typedef object type; };
    template<> struct SuperType<func_interp>  { typedef object type; };
    template<> struct SuperType<model>        { typedef object type; };
    template<> struct SuperType<stats>        { typedef object type; };
    template<> struct SuperType<symbol>       { typedef object type; };
    template<> struct SuperType<expr>         { typedef ast type; };
    template<> struct SuperType<sort>         { typedef ast type; };
    template<> struct SuperType<func_decl>    { typedef ast type; };
}

JLCXX_MODULE define_julia_module(jlcxx::Module &m)
{
    m.add_bits<rounding_mode>("RoundingMode", jlcxx::julia_type("CppEnum"));
    m.set_const("RNA", RNA);
    m.set_const("RNE", RNE);
    m.set_const("RTP", RTP);
    m.set_const("RTN", RTN);
    m.set_const("RTZ", RTZ);

    // -------------------------------------------------------------------------

    // First add all types to avoid unknown types later. This is therefore some 
    // kind of foward declaration.
    ADD_TYPE(m, config, Config);
    ADD_TYPE(m, context, Context);
    ADD_TYPE(m, object, Object);

    ADD_SUBTYPE(m, ast, Ast, object);
    ADD_SUBTYPE(m, expr, Expr, ast);
    ADD_SUBTYPE(m, sort, Sort, ast);
    ADD_SUBTYPE(m, func_decl, FuncDecl, ast);

    ADD_SUBTYPE(m, symbol, Symbol, object);
    ADD_SUBTYPE(m, model, Model, object);
    ADD_SUBTYPE(m, solver, Solver, object);
    ADD_SUBTYPE(m, params, Params, object);
    ADD_SUBTYPE(m, param_descrs, ParamDescrs, object);
    ADD_SUBTYPE(m, goal, Goal, object);
    ADD_SUBTYPE(m, tactic, Tactic, object);
    ADD_SUBTYPE(m, probe, Probe, object);
    ADD_SUBTYPE(m, func_interp, FuncInterp, object);
    ADD_SUBTYPE(m, func_entry, FuncEntry, object);
    ADD_SUBTYPE(m, stats, Stats, object);
    ADD_SUBTYPE(m, apply_result, ApplyResult, object);

    // -------------------------------------------------------------------------

    TYPE_OBJ(config)
        .method("set", static_cast<void (config::*)(char const *, char const *)>(&config::set))
        .method("set", [](config &a, char const *b, const jlcxx::StrictlyTypedNumber<bool> &c) { return a.set(b, c.value); })
        .method("set", [](config &a, char const *b, const jlcxx::StrictlyTypedNumber<int>  &c) { return a.set(b, c.value); });

    // -------------------------------------------------------------------------

    TYPE_OBJ(object)
        .constructor<context &>()
        .MM(object, ctx);

    // -------------------------------------------------------------------------

    m.add_type<jlcxx::Parametric<jlcxx::TypeVar<1>>>("AstVectorTpl")
        .apply<ast_vector_tpl<ast>, ast_vector_tpl<expr>, ast_vector_tpl<sort>, ast_vector_tpl<func_decl>>(
            [](auto wrapped) {
                typedef typename decltype(wrapped)::type WrappedT;
                wrapped.template constructor<context &>();
                wrapped.module().set_override_module(jl_base_module);
                wrapped.method("length", &WrappedT::size);
                wrapped.GETINDEX(WrappedT);
                wrapped.method("push!", &WrappedT::push_back);
                wrapped.STRING(WrappedT);
                wrapped.module().unset_override_module();
            });

    // -------------------------------------------------------------------------

    TYPE_OBJ(symbol)
        .MM(symbol, to_int)
        .method("string", &symbol::str);

    // -------------------------------------------------------------------------

    TYPE_OBJ(ast)
        .constructor<context &>()
        .MM(ast, hash)
        .method("string", &ast::to_string);

    m.method("isequal", &eq);

    // -------------------------------------------------------------------------

    TYPE_OBJ(sort)
        .constructor<context &>()
        .MM(sort, id)
        .MM(sort, name)
        .MM(sort, is_bool)
        .MM(sort, is_int)
        .MM(sort, is_real)
        .MM(sort, is_arith)
        .MM(sort, is_bv)
        .MM(sort, is_array)
        .MM(sort, is_datatype)
        .MM(sort, is_relation)
        .MM(sort, is_seq)
        .MM(sort, is_re)
        .MM(sort, is_finite_domain)
        .MM(sort, is_fpa)
        .MM(sort, bv_size)
        .MM(sort, fpa_ebits)
        .MM(sort, fpa_sbits)
        .MM(sort, array_domain)
        .MM(sort, array_range);

    // -------------------------------------------------------------------------

    TYPE_OBJ(expr)
        .constructor<context &>()
        .MM(expr, get_sort)
        .MM(expr, is_bool)
        .MM(expr, is_int)
        .MM(expr, is_real)
        .MM(expr, is_arith)
        .MM(expr, is_algebraic)
        .MM(expr, numerator)
        .MM(expr, denominator)
        .MM(expr, get_numeral_int)
        .MM(expr, get_decimal_string)
        .MM(expr, id)
        .MM(expr, is_true);

    // Friends of z3::expr
    m.method("mk_or", &mk_or);
    m.method("mk_and", &mk_and);
    m.UNARY_OP(expr, not, !);
    m.BINARY_FN(expr, implies, implies);
    m.method("distinct", &distinct);
    m.method("concat", static_cast<expr (*)(expr const &, expr const &)>(&concat));
    m.method("concat", static_cast<expr (*)(expr_vector const &)>(&concat));

    m.set_override_module(jl_base_module);
    m.BINARY_OP(expr, +, +);
    m.BINARY_OP(expr, -, -);
    m.UNARY_OP(expr, -, -);
    m.BINARY_OP(expr, *, *);
    m.BINARY_OP(expr, /, /);
    m.BINARY_FN(expr, ^, pw);
    m.BINARY_FN(expr, mod, mod);
    m.BINARY_FN(expr, rem, rem);

    m.BINARY_OP(expr, &, &);
    m.BINARY_OP(expr, |, |);
    m.BINARY_OP(expr, xor, ^);
    m.UNARY_OP(expr, ~, ~);

    m.BINARY_OP(expr, ==, ==);
    m.BINARY_OP(expr, !=, !=);
    m.BINARY_OP(expr, <=, <=);
    m.BINARY_OP(expr, >=, >=);
    m.BINARY_OP(expr, <, <);
    m.BINARY_OP(expr, >, >);
    m.unset_override_module();


    m.method("ite", &ite);
    m.method("sum", &sum);
    m.method("pble", &pble);
    m.method("pbge", &pbge);
    m.method("pbeq", &pbeq);
    m.method("atmost", &atmost);
    m.method("atleast", &atleast);
    m.method("nand", &nand);
    m.method("nor", &nor);
    m.method("xnor", &xnor);
    m.method("min", &min);
    m.method("max", &max);
    m.method("abs", static_cast<expr (*)(expr const &)>(&abs));
    m.method("sqrt", static_cast<expr (*)(expr const &, expr const &)>(&sqrt));
    m.method("fma", static_cast<expr (*)(expr const &, expr const &, expr const &, expr const &)>(&fma));
    m.method("range", &range);

    // -------------------------------------------------------------------------

    TYPE_OBJ(func_decl)
        .constructor<context &>()
        .MM(func_decl, id)
        .MM(func_decl, arity)
        .MM(func_decl, domain)
        .MM(func_decl, range)
        .MM(func_decl, name)
        .MM(func_decl, transitive_closure)
        .MM(func_decl, is_const)
        .method(static_cast<expr (func_decl::*)() const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr_vector const &) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr const &) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(int) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr const &, expr const &) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr const &, int) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(int, expr const &) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr const &, expr const &, expr const &) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr const &, expr const &, expr const &, expr const &) const>(&func_decl::operator()))
        .method(static_cast<expr (func_decl::*)(expr const &, expr const &, expr const &, expr const &, expr const &) const>(&func_decl::operator()));

    // -------------------------------------------------------------------------

    TYPE_OBJ(model)
        .constructor<context &>()
        .MM(model, size)
        .MM(model, num_consts)
        .MM(model, num_funcs)
        .MM(model, get_const_decl)
        .MM(model, get_func_decl)
        .MM(model, get_const_interp)
        .MM(model, get_func_interp)
        .MM(model, has_interp)
        .MM(model, add_func_interp)
        .MM(model, add_const_interp)
        .method("__eval", &model::eval)
        .STRING(model);

    m.set_override_module(jl_base_module);
    m.GETINDEX(model);
    m.unset_override_module();

    // -------------------------------------------------------------------------

    m.add_bits<check_result>("CheckResult", jlcxx::julia_type("CppEnum"));
    m.set_const("unsat", unsat);
    m.set_const("sat", sat);
    m.set_const("unknown", unknown);

    // -------------------------------------------------------------------------

    TYPE_OBJ(solver)
        .constructor<context &>()
        // .constructor<context &, simple>()
        .constructor<context &, char const *>()
        // .constructor<context &, solver const &, tranlate>()
        .method("set", static_cast<void (solver::*)(params const &)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, double)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, symbol const &)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, char const *)>(&solver::set))
        .method("set", [](solver &a, char const *b, const jlcxx::StrictlyTypedNumber<bool>     &c) { return a.set(b, c.value); })
        .method("set", [](solver &a, char const *b, const jlcxx::StrictlyTypedNumber<unsigned> &c) { return a.set(b, c.value); })
        .MM(solver, push)
        .MM(solver, pop)
        .MM(solver, reset)
        .method("add", static_cast<void (solver::*)(const expr &)>(&solver::add))
        .method("add", static_cast<void (solver::*)(const expr &, const expr &)>(&solver::add))
        .method("add", static_cast<void (solver::*)(const expr &, const char *)>(&solver::add))
        .MM(solver, from_file)
        .MM(solver, from_string)
        .method("check", static_cast<check_result (solver::*)()>(&solver::check))
        .method("check", static_cast<check_result (solver::*)(const expr_vector &)>(&solver::check))
        .MM(solver, get_model)
        .MM(solver, consequences)
        .MM(solver, reason_unknown)
        .MM(solver, statistics)
        .MM(solver, unsat_core)
        .MM(solver, assertions)
        .MM(solver, non_units)
        .MM(solver, units)
        // expr_vector trail()
        // expr_vector trail(array<unsigned>& levels)
        .MM(solver, proof)
        .MM(solver, to_smt2)
        .MM(solver, dimacs)
        .MM(solver, get_param_descrs)
        .MM(solver, cube)
        // .method("cubes", static_cast<cube_generator (solver::*)()>(&solver::cubes))
        // .method("cubes", static_cast<cube_generator (solver::*)(expr_vector &)>(&solver::cubes))
        .STRING(solver);

    // -------------------------------------------------------------------------

    TYPE_OBJ(params)
        .constructor<context &>()
        .method("set", [](params &a, char const *b, const jlcxx::StrictlyTypedNumber<bool>     &c) { return a.set(b, c.value); })
        .method("set", [](params &a, char const *b, const jlcxx::StrictlyTypedNumber<unsigned> &c) { return a.set(b, c.value); })
        .method("set", static_cast<void (params::*)(char const *, double)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, symbol const &)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, char const *)>(&params::set))
        .STRING(params);

    // -------------------------------------------------------------------------
    
    TYPE_OBJ(param_descrs)
        .MM(param_descrs, size)
        .MM(param_descrs, name)
        .MM(param_descrs, documentation)
        .method("string", &param_descrs::to_string);

    // -------------------------------------------------------------------------

    TYPE_OBJ(goal)
        .method("add", static_cast<void (goal::*)(expr const &)>(&goal::add))
        .method("add", static_cast<void (goal::*)(expr_vector const &)>(&goal::add))
        .MM(goal, size)
        // .MM(goal, precision)
        .MM(goal, inconsistent)
        .MM(goal, depth)
        .MM(goal, reset)
        .MM(goal, num_exprs)
        .MM(goal, is_decided_sat)
        .MM(goal, is_decided_unsat)
        .MM(goal, convert_model)
        .MM(goal, get_model)
        .MM(goal, as_expr)
        .MM(goal, dimacs)
        .STRING(goal);

    m.set_override_module(jl_base_module);
    m.GETINDEX(goal);
    m.unset_override_module();

    // -------------------------------------------------------------------------

    TYPE_OBJ(tactic)
        .constructor<context &, char const *>()
        .method(&tactic::operator())
        .MM(tactic, mk_solver)
        .MM(tactic, apply)
        .MM(tactic, help)
        .MM(tactic, get_param_descrs);

    // Friends of z3::tactic
    m.BINARY_OP(tactic, &, &);
    m.BINARY_OP(tactic, |, |);
    m.method("repeat", &repeat);
    m.method("with", &with);
    m.method("try_for", &try_for);
    m.method("par_or", &par_or);
    m.method("par_and_then", &par_and_then);

    // -------------------------------------------------------------------------

    TYPE_OBJ(probe)
        .constructor<context &, char const *>()
        .constructor<context &, double>()
        .method(&probe::operator())
        .MM(probe, apply);

    // Friends of z3::probe
    m.set_override_module(jl_base_module);
    m.BINARY_OP(probe, ==, ==);
    m.BINARY_OP(probe, <=, <=);
    m.BINARY_OP(probe, >=, >=);
    m.BINARY_OP(probe, <, <);
    m.BINARY_OP(probe, >, >);
    m.unset_override_module();

    m.BINARY_OP(probe, and, &&);
    m.BINARY_OP(probe, or, ||);
    m.UNARY_OP(probe, not, !);

    // -------------------------------------------------------------------------

    TYPE_OBJ(func_interp)
        .MM(func_interp, else_value)
        .MM(func_interp, num_entries)
        .MM(func_interp, entry)
        .MM(func_interp, add_entry)
        .MM(func_interp, set_else);

    // -------------------------------------------------------------------------

    TYPE_OBJ(func_entry)
        .MM(func_entry, value)
        .MM(func_entry, num_args)
        .MM(func_entry, arg);

    // -------------------------------------------------------------------------

    TYPE_OBJ(stats)
        .constructor<context &>()
        .MM(stats, size)
        .MM(stats, key)
        .MM(stats, is_uint)
        .MM(stats, is_double)
        .MM(stats, uint_value)
        .MM(stats, double_value);

    // -------------------------------------------------------------------------

    TYPE_OBJ(apply_result)
        .MM(apply_result, size);

    m.set_override_module(jl_base_module);
    m.GETINDEX(apply_result);
    m.unset_override_module();

    // -------------------------------------------------------------------------

    m.method("set_param", [](char const *a, const jlcxx::StrictlyTypedNumber<bool> &b) { return set_param(a, b.value); });
    m.method("set_param", [](char const *a, const jlcxx::StrictlyTypedNumber<int>  &b) { return set_param(a, b.value); });
    m.method("set_param", static_cast<void (*)(char const * param, char const * value)>(&set_param));
    m.method("reset_params", &reset_params);

    // -------------------------------------------------------------------------

    TYPE_OBJ(context)
        .constructor<config &>()
        .method("set", static_cast<void (context::*)(char const *, char const *)>(&context::set))
        .method("set", [](context &a, char const *b, const jlcxx::StrictlyTypedNumber<bool> &c) { return a.set(b, c.value); })
        .method("set", [](context &a, char const *b, const jlcxx::StrictlyTypedNumber<int>  &c) { return a.set(b, c.value); })
        //
        .MM(context, interrupt)
        //
        .MM(context, str_symbol)
        .MM(context, int_symbol)
        .MM(context, bool_sort)
        .MM(context, int_sort)
        .MM(context, real_sort)
        .MM(context, bv_sort)
        .MM(context, string_sort)
        .MM(context, seq_sort)
        .MM(context, re_sort)
        .method("array_sort", static_cast<sort (context::*)(sort, sort)>(&context::array_sort))
        .method("array_sort", static_cast<sort (context::*)(sort_vector const&, sort)>(&context::array_sort))
        .method("fpa_sort", static_cast<sort (context::*)(unsigned, unsigned)>(&context::fpa_sort))
        //  template<size_t precision>
        //  sort fpa_sort();
        .MM(context, fpa_rounding_mode)
        .MM(context, set_rounding_mode)
        // .MM(context, enumeration_sort)
        // .MM(context, tuple_sort)
        .method("uninterpreted_sort", static_cast<sort (context::*)(char const*)>(&context::uninterpreted_sort))
        .method("uninterpreted_sort", static_cast<sort (context::*)(symbol const&)>(&context::uninterpreted_sort))
        //
        .method("func", static_cast<func_decl (context::*)(symbol const &, unsigned, sort const *, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, unsigned, sort const *, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(symbol const &, sort_vector const &, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, sort_vector const &, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &, sort const &, sort const &)>(&context::function))
        .method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &, sort const &, sort const &, sort const &)>(&context::function))
        //
        .method("recfun", static_cast<func_decl (context::*)(symbol const &, unsigned, sort const *, sort const &)>(&context::recfun))
        .method("recfun", static_cast<func_decl (context::*)(char const *, unsigned, sort const *, sort const &)>(&context::recfun))
        .method("recfun", static_cast<func_decl (context::*)(char const *, sort const &, sort const &)>(&context::recfun))
        .method("recfun", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &)>(&context::recfun))
        //
        .MM(context, recdef)
        //
        .method("constant", static_cast<expr (context::*)(symbol const &, sort const &)>(&context::constant))
        .method("constant", static_cast<expr (context::*)(char const *, sort const &)>(&context::constant))
        .MM(context, bool_const)
        .MM(context, int_const)
        .MM(context, real_const)
        .MM(context, bv_const)
        .method("fpa_const", static_cast<expr (context::*)(char const *, unsigned, unsigned)>(&context::fpa_const))
        // template<size_t precision>
        // expr fpa_const(char const * name);
        //
        .MM(context, bool_val)
        //
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<int>      &b) { return a.int_val(b.value); })
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<unsigned> &b) { return a.int_val(b.value); })
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<int64_t>  &b) { return a.int_val(b.value); })
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<uint64_t> &b) { return a.int_val(b.value); })
        .method("int_val", static_cast<expr (context::*)(char const *)>(&context::int_val))
        //
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<int>      &b) { return a.real_val(b.value); })
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<unsigned> &b) { return a.real_val(b.value); })
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<int64_t>  &b) { return a.real_val(b.value); })
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<uint64_t> &b) { return a.real_val(b.value); })
        .method("real_val", static_cast<expr (context::*)(int, int)>(&context::real_val))
        .method("real_val", static_cast<expr (context::*)(char const *)>(&context::real_val))
        //
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<int>      &b, const jlcxx::StrictlyTypedNumber<unsigned> &c) { return a.bv_val(b.value, c.value); })
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<unsigned> &b, const jlcxx::StrictlyTypedNumber<unsigned> &c) { return a.bv_val(b.value, c.value); })
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<int64_t>  &b, const jlcxx::StrictlyTypedNumber<unsigned> &c) { return a.bv_val(b.value, c.value); })
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<uint64_t> &b, const jlcxx::StrictlyTypedNumber<unsigned> &c) { return a.bv_val(b.value, c.value); })
        .method("bv_val", static_cast<expr (context::*)(char const *, unsigned)>(&context::bv_val))
        .method("bv_val", static_cast<expr (context::*)(unsigned, bool const *)>(&context::bv_val))
        //
        .method("fpa_val", static_cast<expr (context::*)(double)>(&context::fpa_val))
        .method("fpa_val", static_cast<expr (context::*)(float)>(&context::fpa_val))        
        //
        .method("string_val", static_cast<expr (context::*)(char const*, unsigned)>(&context::string_val))
        .method("string_val", static_cast<expr (context::*)(std::string const&)>(&context::string_val))
        //
        .MM(context, num_val)
        //
        .method("parse_string", static_cast<expr_vector (context::*)(char const*)>(&context::parse_string))
        .method("parse_string", static_cast<expr_vector (context::*)(char const*, sort_vector const&, func_decl_vector const&)>(&context::parse_string))
        .method("parse_file", static_cast<expr_vector (context::*)(char const*)>(&context::parse_file))
        .method("parse_file", static_cast<expr_vector (context::*)(char const*, sort_vector const&, func_decl_vector const&)>(&context::parse_file));

}