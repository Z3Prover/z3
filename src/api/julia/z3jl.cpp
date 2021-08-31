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

    template<> struct IsMirroredType<solver::simple>    : std::false_type { };
    template<> struct IsMirroredType<solver::translate> : std::false_type { };
    template<> struct IsMirroredType<optimize::handle>  : std::false_type { };
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
    ADD_SUBTYPE(m, fixedpoint, Fixedpoint, object);
    ADD_SUBTYPE(m, optimize, Optimize, object);

    // -------------------------------------------------------------------------

    TYPE_OBJ(config)
        .method("set", static_cast<void (config::*)(char const *, char const *)>(&config::set))
        .method("set", static_cast<void (config::*)(char const *, bool)>(&config::set))
        .method("set", static_cast<void (config::*)(char const *, int)>(&config::set));

    // -------------------------------------------------------------------------

    TYPE_OBJ(object)
        .constructor<context &>()
        .constructor<object const &>()
        .MM(object, ctx);

    m.method("check_context" , &check_context);

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
        .constructor<symbol const &>()
        .MM(symbol, to_int)
        .method("string", &symbol::str);

    // -------------------------------------------------------------------------

    TYPE_OBJ(ast)
        .constructor<context &>()
        .constructor<ast const &>()
        .MM(ast, hash)
        .method("string", &ast::to_string);

    m.method("isequal", &eq);

    // -------------------------------------------------------------------------

    TYPE_OBJ(sort)
        .constructor<context &>()
        .constructor<sort const &>()
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
        .constructor<expr const &>()
        .MM(expr, get_sort)
        .MM(expr, is_bool)
        .MM(expr, is_int)
        .MM(expr, is_real)
        .MM(expr, is_arith)
        .MM(expr, is_bv)
        .MM(expr, is_array)
        .MM(expr, is_datatype)
        .MM(expr, is_relation)
        .MM(expr, is_seq)
        .MM(expr, is_re)
        .MM(expr, is_finite_domain)
        .MM(expr, is_fpa)
        .MM(expr, is_numeral_i64)
        .MM(expr, is_numeral_u64)
        .MM(expr, is_numeral_i)
        .MM(expr, is_numeral_u)
        .method("is_numeral", static_cast<bool (expr::*)() const>(&expr::is_numeral))
        .method("is_numeral", static_cast<bool (expr::*)(std::string &) const>(&expr::is_numeral))
        .method("is_numeral", static_cast<bool (expr::*)(std::string &, unsigned) const>(&expr::is_numeral))
        .method("is_numeral", static_cast<bool (expr::*)(double &) const>(&expr::is_numeral))
        .MM(expr, is_app)
        .MM(expr, is_const)
        .MM(expr, is_quantifier)
        .MM(expr, is_forall)
        .MM(expr, is_exists)
        .MM(expr, is_lambda)
        .MM(expr, is_var)
        .MM(expr, is_algebraic)
        .MM(expr, is_well_sorted)
        .MM(expr, get_decimal_string)
        .MM(expr, id)
        .MM(expr, algebraic_lower)
        .MM(expr, algebraic_upper)
        .MM(expr, algebraic_poly)
        .MM(expr, algebraic_i)
        .MM(expr, get_numeral_int)
        .MM(expr, get_numeral_uint)
        .MM(expr, get_numeral_int64)
        .MM(expr, get_numeral_uint64)
        .MM(expr, numerator)
        .MM(expr, denominator)
        .MM(expr, is_string_value)
        .MM(expr, get_escaped_string)
        .MM(expr, get_string)
        .MM(expr, decl)
        .MM(expr, num_args)
        .MM(expr, arg)
        .MM(expr, body)
        //
        .MM(expr, is_true)
        .MM(expr, is_false)
        .MM(expr, is_not)
        .MM(expr, is_and)
        .MM(expr, is_or)
        .MM(expr, is_xor)
        .MM(expr, is_implies)
        .MM(expr, is_eq)
        .MM(expr, is_ite)
        .MM(expr, is_distinct)
        //
        .MM(expr, rotate_left)
        .MM(expr, rotate_right)
        .MM(expr, repeat)
        //
        .method("extract", static_cast<expr (expr::*)(unsigned, unsigned) const>(&expr::extract))
        .MM(expr, lo)
        .MM(expr, hi)
        //
        .method("extract", static_cast<expr (expr::*)(expr const &, expr const &) const>(&expr::extract))
        .MM(expr, replace)
        .MM(expr, unit)
        .MM(expr, contains)
        .MM(expr, at)
        .MM(expr, nth)
        .MM(expr, length)
        .MM(expr, stoi)
        .MM(expr, itos)
        //
        .method("loop", static_cast<expr (expr::*)(unsigned)>(&expr::loop))
        .method("loop", static_cast<expr (expr::*)(unsigned, unsigned)>(&expr::loop))
        //
        .method("simplify", static_cast<expr (expr::*)() const>(&expr::simplify))
        .method("simplify", static_cast<expr (expr::*)(params const &) const>(&expr::simplify))
        .method("substitute", static_cast<expr (expr::*)(expr_vector const &, expr_vector const &)>(&expr::substitute))
        .method("substitute", static_cast<expr (expr::*)(expr_vector const &)>(&expr::substitute));

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
        .constructor<func_decl const &>()
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
        .constructor<model const &>()
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
        // eval is a core method in Julia, therefore renaming necessary
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

    m.add_type<solver::simple>("SolverSimple");
    m.add_type<solver::translate>("SolverTranslate");

    TYPE_OBJ(solver)
        .constructor<context &>()
        .constructor<context &, solver::simple>()
        .constructor<context &, char const *>()
        .constructor<context &, solver const &, solver::translate>()
        .constructor<solver const &>()
        .method("set", static_cast<void (solver::*)(params const &)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, double)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, symbol const &)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, char const *)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, bool)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, unsigned)>(&solver::set))
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
        .method("trail", static_cast<expr_vector (solver::*)() const>(&solver::trail))
        .method("trail", [](solver &s, jlcxx::ArrayRef<unsigned> levels) {
            int sz = levels.size();
            z3::array<unsigned> _levels(sz);
            for (int i = 0; i < sz; i++) {
                _levels[i] = levels[i];
            }
            return s.trail(_levels);
        })
        .MM(solver, proof)
        .MM(solver, to_smt2)
        .MM(solver, dimacs)
        .MM(solver, get_param_descrs)
        .MM(solver, cube)
        // .method("cubes", static_cast<cube_generator (solver::*)()>(&solver::cubes))
        // .method("cubes", static_cast<cube_generator (solver::*)(expr_vector &)>(&solver::cubes))
        .STRING(solver);

    // -------------------------------------------------------------------------

    TYPE_OBJ(fixedpoint)
        .constructor<context &>()
        .MM(fixedpoint, from_string)
        .MM(fixedpoint, from_file)
        .MM(fixedpoint, add_rule)
        .MM(fixedpoint, add_fact)
        .method("query", static_cast<check_result (fixedpoint::*)(expr &)>(&fixedpoint::query))
        .method("query", static_cast<check_result (fixedpoint::*)(func_decl_vector &)>(&fixedpoint::query))
        .MM(fixedpoint, get_answer)
        .MM(fixedpoint, reason_unknown)
        .MM(fixedpoint, update_rule)
        .MM(fixedpoint, get_num_levels)
        .MM(fixedpoint, get_cover_delta)
        .MM(fixedpoint, add_cover)
        .MM(fixedpoint, statistics)
        .MM(fixedpoint, register_relation)
        .MM(fixedpoint, assertions)
        .MM(fixedpoint, rules)
        .method("set", static_cast<void (fixedpoint::*)(params const &)>(&fixedpoint::set))
        .MM(fixedpoint, help)
        .MM(fixedpoint, get_param_descrs)
        .method("to_string", static_cast<std::string (fixedpoint::*)(expr_vector const &)>(&fixedpoint::to_string))
        .STRING(fixedpoint);

    // -------------------------------------------------------------------------

    m.add_type<optimize::handle>("OptimizeHandle")
        .MM(optimize::handle, h);

    TYPE_OBJ(optimize)
        .constructor<context &>()
        .method("add", static_cast<void (optimize::*)(expr const &)>(&optimize::add))
        .method("add", static_cast<optimize::handle (optimize::*)(expr const &, unsigned)>(&optimize::add))
        .method("add", static_cast<void (optimize::*)(expr const &, expr const &)>(&optimize::add))
        .method("add", static_cast<void (optimize::*)(expr const &, char const *)>(&optimize::add))
        .method("add_soft", static_cast<optimize::handle (optimize::*)(expr const &, unsigned)>(&optimize::add_soft))
        .method("add_soft", static_cast<optimize::handle (optimize::*)(expr const &, char const *)>(&optimize::add_soft))
        .MM(optimize, maximize)
        .MM(optimize, minimize)
        .MM(optimize, push)
        .MM(optimize, pop)
        .method("check", static_cast<check_result (optimize::*)()>(&optimize::check))
        .method("check", static_cast<check_result (optimize::*)(const expr_vector &)>(&optimize::check))
        .MM(optimize, get_model)
        .MM(optimize, unsat_core)
        .MM(optimize, set)
        .MM(optimize, lower)
        .MM(optimize, upper)
        .MM(optimize, assertions)
        .MM(optimize, objectives)
        .MM(optimize, statistics)
        .MM(optimize, from_file)
        .MM(optimize, from_string)
        .MM(optimize, help)
        .STRING(optimize);

    // -------------------------------------------------------------------------

    TYPE_OBJ(params)
        .constructor<context &>()
        .method("set", static_cast<void (params::*)(char const *, bool)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, unsigned)>(&params::set))
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

    m.method("set_param", static_cast<void (*)(char const *, bool)>(&set_param));
    m.method("set_param", static_cast<void (*)(char const *, int)>(&set_param));
    m.method("set_param", static_cast<void (*)(char const *, char const *)>(&set_param));
    m.method("reset_params", &reset_params);

    // -------------------------------------------------------------------------

    TYPE_OBJ(context)
        .constructor<config &>()
        .method("set", static_cast<void (context::*)(char const *, char const *)>(&context::set))
        .method("set", static_cast<void (context::*)(char const *, bool)>(&context::set))
        .method("set", static_cast<void (context::*)(char const *, int)>(&context::set))
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
        .method("fpa_sort_16", static_cast<sort (context::*)()>(&context::fpa_sort<16>))
        .method("fpa_sort_32", static_cast<sort (context::*)()>(&context::fpa_sort<32>))
        .method("fpa_sort_64", static_cast<sort (context::*)()>(&context::fpa_sort<64>))
        .method("fpa_sort_128", static_cast<sort (context::*)()>(&context::fpa_sort<128>))
        .MM(context, fpa_rounding_mode)
        .MM(context, set_rounding_mode)
        .method("enumeration_sort", 
            [](context& c, char const * name, jlcxx::ArrayRef<jl_value_t*,1> names, func_decl_vector &cs, func_decl_vector &ts) {
                int sz = names.size();
                std::vector<const char *> _names;
                for (int i = 0; i < sz; i++) {
                    const char *x = jl_string_data(names[i]);
                    _names.push_back(x);
                }
                return c.enumeration_sort(name, sz, _names.data(), cs, ts);
            })
        .method("tuple_sort", 
            [](context& c, char const * name, jlcxx::ArrayRef<jl_value_t*,1> names, jlcxx::ArrayRef<jl_value_t*,1> sorts, func_decl_vector &projs) {
                int sz = names.size();
                std::vector<sort> _sorts;
                std::vector<const char *> _names;
                for (int i = 0; i < sz; i++) {
                    const sort &x = jlcxx::unbox<sort&>(sorts[i]);
                    const char *y = jl_string_data(names[i]);
                    _sorts.push_back(x);
                    _names.push_back(y);
                }
                return c.tuple_sort(name, sz, _names.data(), _sorts.data(), projs);
            })
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
        .method("fpa_const_16", static_cast<expr (context::*)(char const *)>(&context::fpa_const<16>))
        .method("fpa_const_32", static_cast<expr (context::*)(char const *)>(&context::fpa_const<32>))
        .method("fpa_const_64", static_cast<expr (context::*)(char const *)>(&context::fpa_const<64>))
        .method("fpa_const_128", static_cast<expr (context::*)(char const *)>(&context::fpa_const<128>))
        //
        .MM(context, bool_val)
        //
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<int>      b) { return a.int_val(b.value); })
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<unsigned> b) { return a.int_val(b.value); })
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<int64_t>  b) { return a.int_val(b.value); })
        .method("int_val", [](context &a, const jlcxx::StrictlyTypedNumber<uint64_t> b) { return a.int_val(b.value); })
        .method("int_val", static_cast<expr (context::*)(char const *)>(&context::int_val))
        //
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<int>      b) { return a.real_val(b.value); })
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<unsigned> b) { return a.real_val(b.value); })
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<int64_t>  b) { return a.real_val(b.value); })
        .method("real_val", [](context &a, const jlcxx::StrictlyTypedNumber<uint64_t> b) { return a.real_val(b.value); })
        .method("real_val", static_cast<expr (context::*)(int, int)>(&context::real_val))
        .method("real_val", static_cast<expr (context::*)(char const *)>(&context::real_val))
        //
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<int>      b, unsigned c) { return a.bv_val(b.value, c); })
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<unsigned> b, unsigned c) { return a.bv_val(b.value, c); })
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<int64_t>  b, unsigned c) { return a.bv_val(b.value, c); })
        .method("bv_val", [](context &a, const jlcxx::StrictlyTypedNumber<uint64_t> b, unsigned c) { return a.bv_val(b.value, c); })
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
