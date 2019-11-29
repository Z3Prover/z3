#include "jlcxx/jlcxx.hpp"
#include "z3++.h"

using namespace z3;

#define EXPR_OPCALL(MOD, OP, TYPE) EXPR_NAMED_OPCALL(MOD, OP, OP, TYPE)
#define EXPR_NAMED_OPCALL(MOD, FNAME, OP, TYPE)                              \
    MOD.method(#FNAME, [](const expr &a, const expr &b) { return a OP b; }); \
    MOD.method(#FNAME, [](const expr &a, TYPE b) { return a OP b; });        \
    MOD.method(#FNAME, [](TYPE a, const expr &b) { return a OP b; });
#define EXPR_FNCALL(MOD, FNAME, F, TYPE)                                      \
    MOD.method(#FNAME, [](const expr &a, const expr &b) { return F(a, b); }); \
    MOD.method(#FNAME, [](const expr &a, TYPE b) { return F(a, b); });        \
    MOD.method(#FNAME, [](TYPE a, const expr &b) { return F(a, b); });

#define STRING(TYPE)               \
    method("string", [](TYPE x) {  \
        std::ostringstream stream; \
        stream << x;               \
        return stream.str();       \
    })

#define MM(CLASS, FUNC) method(#FUNC, &CLASS::FUNC)

namespace jlcxx
{
    template<> struct IsBits<check_result> : std::true_type {};
    template<> struct IsBits<rounding_mode> : std::true_type {};
    // template<> struct jlcxx::IsBits<Z3_error_code> : std::true_type {};

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
    template<> struct SuperType<expr>         { typedef ast type; };
    template<> struct SuperType<sort>         { typedef ast type; };
    template<> struct SuperType<func_decl>    { typedef ast type; };
}

JLCXX_MODULE define_context(jlcxx::TypeWrapper<context> &c)
{
    c.constructor<config &>();
    c.method("set", static_cast<void (context::*)(char const *, char const *)>(&context::set));
    c.method("set", static_cast<void (context::*)(char const *, bool)>(&context::set));
    c.method("set", static_cast<void (context::*)(char const *, int)>(&context::set));

    c.MM(context, interrupt);

    c.MM(context, str_symbol);
    c.MM(context, int_symbol);
    c.MM(context, bool_sort);
    c.MM(context, int_sort);
    c.MM(context, real_sort);
    c.MM(context, bv_sort);
    c.MM(context, string_sort);
    c.MM(context, seq_sort);
    c.MM(context, re_sort);
    c.method("array_sort", static_cast<sort (context::*)(sort, sort)>(&context::array_sort));
    c.method("array_sort", static_cast<sort (context::*)(sort_vector const&, sort)>(&context::array_sort));
    c.method("fpa_sort", static_cast<sort (context::*)(unsigned, unsigned)>(&context::fpa_sort));
    //  template<size_t precision>
    //  sort fpa_sort();
    c.MM(context, fpa_rounding_mode);
    c.MM(context, set_rounding_mode);
    // c.MM(context, enumeration_sort);
    // c.MM(context, tuple_sort);
    c.method("uninterpreted_sort", static_cast<sort (context::*)(char const*)>(&context::uninterpreted_sort));
    c.method("uninterpreted_sort", static_cast<sort (context::*)(symbol const&)>(&context::uninterpreted_sort));

    c.method("func", static_cast<func_decl (context::*)(symbol const &, unsigned, sort const *, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, unsigned, sort const *, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(symbol const &, sort_vector const &, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, sort_vector const &, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &, sort const &, sort const &)>(&context::function));
    c.method("func", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &, sort const &, sort const &, sort const &)>(&context::function));

    c.method("recfun", static_cast<func_decl (context::*)(symbol const &, unsigned, sort const *, sort const &)>(&context::recfun));
    c.method("recfun", static_cast<func_decl (context::*)(char const *, unsigned, sort const *, sort const &)>(&context::recfun));
    c.method("recfun", static_cast<func_decl (context::*)(char const *, sort const &, sort const &)>(&context::recfun));
    c.method("recfun", static_cast<func_decl (context::*)(char const *, sort const &, sort const &, sort const &)>(&context::recfun));

    c.MM(context, recdef);

    c.method("constant", static_cast<expr (context::*)(symbol const &, sort const &)>(&context::constant));
    c.method("constant", static_cast<expr (context::*)(char const *, sort const &)>(&context::constant));
    c.MM(context, bool_const);
    c.MM(context, int_const);
    c.MM(context, real_const);
    c.MM(context, bv_const);
    c.method("fpa_const", static_cast<expr (context::*)(char const *, unsigned, unsigned)>(&context::fpa_const));
    // template<size_t precision>
    // expr fpa_const(char const * name);

    c.MM(context, bool_val);

    c.method("int_val", static_cast<expr (context::*)(int)>(&context::int_val));
    c.method("int_val", static_cast<expr (context::*)(unsigned)>(&context::int_val));
    c.method("int_val", static_cast<expr (context::*)(int64_t)>(&context::int_val));
    c.method("int_val", static_cast<expr (context::*)(uint64_t)>(&context::int_val));
    c.method("int_val", static_cast<expr (context::*)(char const *)>(&context::int_val));

    c.method("real_val", static_cast<expr (context::*)(int, int)>(&context::real_val));
    c.method("real_val", static_cast<expr (context::*)(int)>(&context::real_val));
    c.method("real_val", static_cast<expr (context::*)(unsigned)>(&context::real_val));
    c.method("real_val", static_cast<expr (context::*)(int64_t)>(&context::real_val));
    c.method("real_val", static_cast<expr (context::*)(uint64_t)>(&context::real_val));
    c.method("real_val", static_cast<expr (context::*)(char const *)>(&context::real_val));

    c.method("bv_val", static_cast<expr (context::*)(int, unsigned)>(&context::bv_val));
    c.method("bv_val", static_cast<expr (context::*)(unsigned, unsigned)>(&context::bv_val));
    c.method("bv_val", static_cast<expr (context::*)(int64_t, unsigned)>(&context::bv_val));
    c.method("bv_val", static_cast<expr (context::*)(uint64_t, unsigned)>(&context::bv_val));
    c.method("bv_val", static_cast<expr (context::*)(char const *, unsigned)>(&context::bv_val));
    c.method("bv_val", static_cast<expr (context::*)(unsigned, bool const *)>(&context::bv_val));

    c.method("fpa_val", static_cast<expr (context::*)(double)>(&context::fpa_val));
    c.method("fpa_val", static_cast<expr (context::*)(float)>(&context::fpa_val));

    // c.method("string_val", static_cast<expr (context::*)(char const*)>(&context::string_val));
    c.method("string_val", static_cast<expr (context::*)(char const*, unsigned)>(&context::string_val));
    c.method("string_val", static_cast<expr (context::*)(std::string const&)>(&context::string_val));

    c.MM(context, num_val);

    c.method("parse_string", static_cast<expr_vector (context::*)(char const*)>(&context::parse_string));
    c.method("parse_string", static_cast<expr_vector (context::*)(char const*, sort_vector const&, func_decl_vector const&)>(&context::parse_string));
    c.method("parse_file", static_cast<expr_vector (context::*)(char const*)>(&context::parse_file));
    c.method("parse_file", static_cast<expr_vector (context::*)(char const*, sort_vector const&, func_decl_vector const&)>(&context::parse_file));;
}

JLCXX_MODULE define_julia_module(jlcxx::Module &m)
{
    m.add_bits<rounding_mode>("RoundingMode", jlcxx::julia_type("CppEnum"));
    m.set_const("RNA", RNA);
    m.set_const("RNE", RNE);
    m.set_const("RTP", RTP);
    m.set_const("RTN", RTN);
    m.set_const("RTZ", RTZ);

    m.add_type<config>("Config")
        .method("set", static_cast<void (config::*)(char const *, char const *)>(&config::set))
        .method("set", static_cast<void (config::*)(char const *, bool)>(&config::set))
        .method("set", static_cast<void (config::*)(char const *, int)>(&config::set));

    jlcxx::TypeWrapper<context> t = m.add_type<context>("Context");
    define_context(t);

    m.add_type<object>("Object")
        .constructor<context &>()
        .MM(object, ctx);
    // MM(object, check_error);

    m.add_type<ast>("Ast", jlcxx::julia_type<object>())
        .constructor<context &>()
        .MM(ast, hash)
        .method("string", &ast::to_string);

    m.method("isequal", &eq);

    m.add_type<sort>("Sort", jlcxx::julia_type<ast>())
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

    m.add_type<func_decl>("FuncDecl", jlcxx::julia_type<ast>())
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

    m.add_type<expr>("Expr", jlcxx::julia_type<ast>())
        .constructor<context &>()
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

    // Friends of expr
    m.method("mk_or", &mk_or);
    m.method("mk_and", &mk_and);
    m.method("not", [](const expr &a) { return !a; });
    EXPR_FNCALL(m, implies, implies, bool)
    m.method("distinct", &distinct);
    m.method("concat", static_cast<expr (*)(expr const &, expr const &)>(&concat));
    m.method("concat", static_cast<expr (*)(expr_vector const &)>(&concat));

    EXPR_OPCALL(m, +, int)
    EXPR_OPCALL(m, -, int)
    m.method("-", [](const expr &a) { return -a; });
    EXPR_OPCALL(m, *, int)
    EXPR_OPCALL(m, /, int)
    EXPR_FNCALL(m, ^, pw, int)
    EXPR_FNCALL(m, mod, mod, int)
    EXPR_FNCALL(m, rem, rem, int)

    EXPR_OPCALL(m, ==, int)
    EXPR_OPCALL(m, !=, int)
    EXPR_OPCALL(m, <=, int)
    EXPR_OPCALL(m, >=, int)
    EXPR_OPCALL(m, <, int)
    EXPR_OPCALL(m, >, int)

    EXPR_OPCALL(m, &, int)
    EXPR_OPCALL(m, |, int)
    EXPR_NAMED_OPCALL(m, xor, ^, int)
    m.method("~", [](const expr &a) { return ~a; });

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

    m.add_type<jlcxx::Parametric<jlcxx::TypeVar<1>>>("AstVectorTpl")
        .apply<ast_vector_tpl<ast>, ast_vector_tpl<expr>, ast_vector_tpl<sort>, ast_vector_tpl<func_decl>>(
            [](auto wrapped) {
                typedef typename decltype(wrapped)::type WrappedT;
                wrapped.template constructor<context &>();
                wrapped.method("length", &WrappedT::size);
                wrapped.method("getindex", [](const WrappedT &m, int i) { return m[i - 1]; });
                wrapped.method("push!", &WrappedT::push_back);
                wrapped.STRING(const WrappedT &);
            });

    m.add_type<model>("Model", jlcxx::julia_type<object>())
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
        .method("getindex", [](const model &m, int i) { return m[i - 1]; })
        .STRING(const model &);

    m.add_bits<check_result>("CheckResult", jlcxx::julia_type("CppEnum"));
    m.set_const("unsat", unsat);
    m.set_const("sat", sat);
    m.set_const("unknown", unknown);

    m.add_type<solver>("Solver", jlcxx::julia_type<object>())
        .constructor<context &>()
        // .constructor<context &, simple>()
        .constructor<context &, char const *>()
        // .constructor<context &, solver const &, tranlate>()
        .method("set", static_cast<void (solver::*)(params const &)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, bool)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, unsigned)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, double)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, symbol const &)>(&solver::set))
        .method("set", static_cast<void (solver::*)(char const *, char const *)>(&solver::set))
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
        .STRING(const solver &);

    m.add_type<symbol>("Symbol", jlcxx::julia_type<object>())
        .MM(symbol, to_int)
        .method("string", &symbol::str);

    m.add_type<params>("Params", jlcxx::julia_type<object>())
        .constructor<context &>()
        .method("set", static_cast<void (params::*)(char const *, bool)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, unsigned)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, double)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, symbol const &)>(&params::set))
        .method("set", static_cast<void (params::*)(char const *, char const *)>(&params::set))
        .STRING(const params &);
    
    m.add_type<param_descrs>("ParamDescrs", jlcxx::julia_type<object>())
        .MM(param_descrs, size)
        .MM(param_descrs, name)
        .MM(param_descrs, documentation)
        .method("string", &param_descrs::to_string);

    m.add_type<goal>("Goal", jlcxx::julia_type<object>())
        .method("add", static_cast<void (goal::*)(expr const &)>(&goal::add))
        .method("add", static_cast<void (goal::*)(expr_vector const &)>(&goal::add))
        .method("getindex", [](const goal &g, int i) { return g[i - 1]; })
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
        .STRING(const goal &);

    m.add_type<tactic>("Tactic", jlcxx::julia_type<object>())
        .constructor<context &, char const *>()
        .method(&tactic::operator())
        .MM(tactic, mk_solver)
        .MM(tactic, apply)
        .MM(tactic, help)
        .MM(tactic, get_param_descrs);

    m.add_type<probe>("Probe", jlcxx::julia_type<object>())
        .constructor<context &, char const *>()
        .constructor<context &, double>()
        .method(&probe::operator())
        .MM(probe, apply);

    // TODO: Friends of z3::probe

    m.add_type<func_interp>("FuncInterp", jlcxx::julia_type<object>())
        .MM(func_interp, else_value)
        .MM(func_interp, num_entries)
        .MM(func_interp, entry)
        .MM(func_interp, add_entry)
        .MM(func_interp, set_else);

    m.add_type<func_entry>("FuncEntry", jlcxx::julia_type<object>())
        .MM(func_entry, value)
        .MM(func_entry, num_args)
        .MM(func_entry, arg);

    m.add_type<stats>("Stats", jlcxx::julia_type<object>())
        .constructor<context &>()
        .MM(stats, size)
        .MM(stats, key)
        .MM(stats, is_uint)
        .MM(stats, is_double)
        .MM(stats, uint_value)
        .MM(stats, double_value);

    m.add_type<apply_result>("ApplyResult", jlcxx::julia_type<object>())
        .method("getindex", [](const apply_result &r, int i) { return r[i - 1]; })
        .MM(apply_result, size);
}