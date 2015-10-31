/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    basic_cmds.cpp

Abstract:
    Basic commands for SMT2 front end.

Author:

    Leonardo (leonardo) 2011-03-30

Notes:

--*/
#include"cmd_context.h"
#include"version.h"
#include"ast_smt_pp.h"
#include"ast_smt2_pp.h"
#include"ast_pp.h"
#include"model_smt2_pp.h"
#include"array_decl_plugin.h"
#include"pp.h"
#include"cmd_util.h"
#include"simplify_cmd.h"
#include"eval_cmd.h"
#include"gparams.h"
#include"env_params.h"

class help_cmd : public cmd {
    svector<symbol> m_cmds;
    void display_cmd(cmd_context & ctx, symbol const & s, cmd * c) {
        char const * usage = c->get_usage();
        char const * descr = c->get_descr(ctx);
        ctx.regular_stream() << " (" << s;
        if (usage)
            ctx.regular_stream() << " " << escaped(usage, true) << ")\n";
        else 
            ctx.regular_stream() << ")\n";
        if (descr) {
            ctx.regular_stream() << "    " << escaped(descr, true, 4) << "\n";
        }
    }

public:
    help_cmd():cmd("help") {}
    virtual char const * get_usage() const { return "<symbol>*"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "print this help."; }
    virtual unsigned get_arity() const { return VAR_ARITY; }
    virtual void prepare(cmd_context & ctx) { m_cmds.reset(); }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_SYMBOL; }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) {
        cmd * c = ctx.find_cmd(s);
        if (c == 0) {
            std::string err_msg("unknown command '");
            err_msg = err_msg + s.bare_str() + "'";
            throw cmd_exception(err_msg);
        }
        m_cmds.push_back(s);
    }
    
    typedef std::pair<symbol, cmd*> named_cmd;
    struct named_cmd_lt {
        bool operator()(named_cmd const & c1, named_cmd const & c2) const { return c1.first.str() < c2.first.str(); }
    };

    virtual void execute(cmd_context & ctx) {
        ctx.regular_stream() << "\"";
        if (m_cmds.empty()) {
            vector<named_cmd> cmds;
            cmd_context::cmd_iterator it  = ctx.begin_cmds();
            cmd_context::cmd_iterator end = ctx.end_cmds();
            for (; it != end; ++it) {
                cmds.push_back(named_cmd((*it).m_key, (*it).m_value));
            }
            // named_cmd_lt is not a total order for commands, but this is irrelevant for Linux x Windows behavior
            std::sort(cmds.begin(), cmds.end(), named_cmd_lt());
            vector<named_cmd>::const_iterator it2  = cmds.begin();
            vector<named_cmd>::const_iterator end2 = cmds.end();
            for (; it2 != end2; ++it2) {
                display_cmd(ctx, it2->first, it2->second);
            }
        }
        else {
            svector<symbol>::const_iterator it  = m_cmds.begin();
            svector<symbol>::const_iterator end = m_cmds.end();
            for (; it != end; ++it) {
                cmd * c = ctx.find_cmd(*it);
                SASSERT(c);
                display_cmd(ctx, *it, c);
            }
        }
        ctx.regular_stream() << "\"\n";
    }
};

ATOMIC_CMD(exit_cmd, "exit", "exit.", ctx.print_success(); throw stop_parser_exception(););

ATOMIC_CMD(get_model_cmd, "get-model", "retrieve model for the last check-sat command", {
    if (!ctx.is_model_available() || ctx.get_check_sat_result() == 0)
        throw cmd_exception("model is not available");
    model_ref m;
    ctx.get_check_sat_result()->get_model(m);
    ctx.display_model(m);
});

ATOMIC_CMD(get_assignment_cmd, "get-assignment", "retrieve assignment", {
    if (!ctx.is_model_available() || ctx.get_check_sat_result() == 0)
        throw cmd_exception("model is not available");
    model_ref m;
    ctx.get_check_sat_result()->get_model(m);
    ctx.regular_stream() << "(";
    dictionary<cmd_context::macro> const & macros = ctx.get_macros();
    dictionary<cmd_context::macro>::iterator it  = macros.begin();
    dictionary<cmd_context::macro>::iterator end = macros.end();
    for (bool first = true; it != end; ++it) {
        symbol const & name = (*it).m_key;
        cmd_context::macro const & _m    = (*it).m_value;
        if (_m.first == 0 && ctx.m().is_bool(_m.second)) {
            expr_ref val(ctx.m());
            m->eval(_m.second, val, true);
            if (ctx.m().is_true(val) || ctx.m().is_false(val)) {
                if (first)
                    first = false;
                else
                    ctx.regular_stream() << " ";
                ctx.regular_stream() << "(" << name << " " << (ctx.m().is_true(val) ? "true" : "false") << ")";
            }
        }
    }
    ctx.regular_stream() << ")" << std::endl;
});

class cmd_is_declared : public ast_smt_pp::is_declared {
    cmd_context& m_ctx;
public:
    cmd_is_declared(cmd_context& ctx): m_ctx(ctx) {}
    
    virtual bool operator()(func_decl* d) const { 
        return m_ctx.is_func_decl(d->get_name());
    }
    virtual bool operator()(sort* s) const { 
        return m_ctx.is_sort_decl(s->get_name());
    }
};

ATOMIC_CMD(get_proof_cmd, "get-proof", "retrieve proof", {
    if (!ctx.produce_proofs())
        throw cmd_exception("proof construction is not enabled, use command (set-option :produce-proofs true)");
    if (!ctx.has_manager() ||
        ctx.cs_state() != cmd_context::css_unsat)
        throw cmd_exception("proof is not available");
    expr_ref pr(ctx.m());
    pr = ctx.get_check_sat_result()->get_proof();
    if (pr == 0)
        throw cmd_exception("proof is not available");
    // TODO: reimplement a new SMT2 pretty printer 
    ast_smt_pp pp(ctx.m());
    cmd_is_declared isd(ctx);
    pp.set_is_declared(&isd);
    pp.set_logic(ctx.get_logic().str().c_str());
    pp.display_smt2(ctx.regular_stream(), pr);
    ctx.regular_stream() << std::endl;
});

ATOMIC_CMD(get_unsat_core_cmd, "get-unsat-core", "retrieve unsat core", {
    if (!ctx.produce_unsat_cores())
        throw cmd_exception("unsat core construction is not enabled, use command (set-option :produce-unsat-cores true)");
    if (!ctx.has_manager() ||
        ctx.cs_state() != cmd_context::css_unsat)
        throw cmd_exception("unsat core is not available");
    ptr_vector<expr> core;
    ctx.get_check_sat_result()->get_unsat_core(core);
    ctx.regular_stream() << "(";
    ptr_vector<expr>::const_iterator it  = core.begin();
    ptr_vector<expr>::const_iterator end = core.end();
    for (bool first = true; it != end; ++it) {
        if (first)
            first = false;
        else
            ctx.regular_stream() << " ";
        ctx.regular_stream() << mk_ismt2_pp(*it, ctx.m());
    }
    ctx.regular_stream() << ")" << std::endl;
});

ATOMIC_CMD(labels_cmd, "labels", "retrieve Simplify-like labels", {
    if (!ctx.has_manager() ||
        (ctx.cs_state() != cmd_context::css_sat && ctx.cs_state() != cmd_context::css_unknown))
        throw cmd_exception("labels are not available");
    svector<symbol> labels;
    ctx.get_check_sat_result()->get_labels(labels);
    ctx.regular_stream() << "(labels";
    for (unsigned i = 0; i < labels.size(); i++) {
        ctx.regular_stream() << " " << labels[i];
    }
    ctx.regular_stream() << ")" << std::endl;
});

ATOMIC_CMD(get_assertions_cmd, "get-assertions", "retrieve asserted terms when in interactive mode", ctx.display_assertions(););

UNARY_CMD(set_logic_cmd, "set-logic", "<symbol>", "set the background logic.", CPK_SYMBOL, symbol const &, 
          if (ctx.set_logic(arg))
              ctx.print_success();
          else
              ctx.print_unsupported(symbol::null, m_line, m_pos);
          );

UNARY_CMD(pp_cmd, "display", "<term>", "display the given term.", CPK_EXPR, expr *, { 
    ctx.display(ctx.regular_stream(), arg);
    ctx.regular_stream() << std::endl; 
});

UNARY_CMD(echo_cmd, "echo", "<string>", "display the given string", CPK_STRING, char const *, ctx.regular_stream() << arg << std::endl;);

class set_get_option_cmd : public cmd {
protected:
    symbol      m_true;
    symbol      m_false;

    symbol      m_print_success;
    symbol      m_print_warning;
    symbol      m_expand_definitions;
    symbol      m_interactive_mode;
    symbol      m_produce_proofs;
    symbol      m_produce_unsat_cores;
    symbol      m_produce_models;
    symbol      m_produce_assignments;
    symbol      m_produce_interpolants;
    symbol      m_regular_output_channel;
    symbol      m_diagnostic_output_channel;
    symbol      m_random_seed;
    symbol      m_verbosity;
    symbol      m_global_decls;
    symbol      m_numeral_as_real;
    symbol      m_error_behavior;
    symbol      m_int_real_coercions;

    bool is_builtin_option(symbol const & s) const {
        return 
            s == m_print_success || s == m_print_warning || s == m_expand_definitions || 
            s == m_interactive_mode || s == m_produce_proofs || s == m_produce_unsat_cores ||
            s == m_produce_models || s == m_produce_assignments || s == m_produce_interpolants ||
        s == m_regular_output_channel || s == m_diagnostic_output_channel || 
            s == m_random_seed || s == m_verbosity || s == m_global_decls;
    }

public:
    set_get_option_cmd(char const * name):
        cmd(name), 
        m_true("true"),
        m_false("false"),
        m_print_success(":print-success"),
        m_print_warning(":print-warning"),
        m_expand_definitions(":expand-definitions"),
        m_interactive_mode(":interactive-mode"),
        m_produce_proofs(":produce-proofs"),
        m_produce_unsat_cores(":produce-unsat-cores"),
        m_produce_models(":produce-models"),
        m_produce_assignments(":produce-assignments"),
        m_produce_interpolants(":produce-interpolants"),
        m_regular_output_channel(":regular-output-channel"),
        m_diagnostic_output_channel(":diagnostic-output-channel"),
        m_random_seed(":random-seed"),
        m_verbosity(":verbosity"),
        m_global_decls(":global-decls"),
        m_numeral_as_real(":numeral-as-real"),
        m_error_behavior(":error-behavior"),
        m_int_real_coercions(":int-real-coercions") {
    }
    virtual ~set_get_option_cmd() {}

};

class set_option_cmd : public set_get_option_cmd {
    bool        m_unsupported;
    symbol      m_option;
    
    bool to_bool(symbol const & value) const {
        if (value != m_true && value != m_false)
            throw cmd_exception("invalid option value, true/false expected");
        return value == m_true;
    }

    static unsigned to_unsigned(rational const & val) {
        if (!val.is_unsigned())
            throw cmd_exception("option value is too big to fit in a machine integer.");
        return val.get_unsigned();
    }

    static void check_not_initialized(cmd_context & ctx, symbol const & opt_name) {
        if (ctx.has_manager()) {
            std::string msg = "error setting '";
            msg += opt_name.str();
            msg += "', option value cannot be modified after initialization";
            throw cmd_exception(msg);
        }
    }
    
    void set_param(cmd_context & ctx, char const * value) {
        try {
            gparams::set(m_option, value);
            env_params::updt_params();
            ctx.global_params_updated();
        }
        catch (gparams::exception ex) {
            throw cmd_exception(ex.msg());
        }
    }

    void set_symbol(cmd_context & ctx, symbol const & value) {
        if (m_option == m_print_success) {
            ctx.set_print_success(to_bool(value));
        }
        else if (m_option == m_print_warning) {
            enable_warning_messages(to_bool(value));
        }
        else if (m_option == m_expand_definitions) {
            m_unsupported = true;
        }
        else if (m_option == m_interactive_mode) {
            check_not_initialized(ctx, m_interactive_mode);
            ctx.set_interactive_mode(to_bool(value));
        }
        else if (m_option == m_produce_proofs) {
            check_not_initialized(ctx, m_produce_proofs);
            ctx.set_produce_proofs(to_bool(value));
        }
        else if (m_option == m_produce_interpolants) {
            check_not_initialized(ctx, m_produce_interpolants);
            ctx.set_produce_interpolants(to_bool(value));
        }
        else if (m_option == m_produce_unsat_cores) {
            check_not_initialized(ctx, m_produce_unsat_cores);
            ctx.set_produce_unsat_cores(to_bool(value));
        }
        else if (m_option == m_produce_models) {
            ctx.set_produce_models(to_bool(value));
        }
        else if (m_option == m_produce_assignments) {
            ctx.set_produce_assignments(to_bool(value));
        }
        else if (m_option == m_global_decls) {
            check_not_initialized(ctx, m_global_decls);
            ctx.set_global_decls(to_bool(value));
        }
        else if (m_option == m_numeral_as_real) {
            ctx.set_numeral_as_real(to_bool(value));
        }
        else if (m_option == m_int_real_coercions) {
            ctx.m().enable_int_real_coercions(to_bool(value));
        }
#ifdef Z3DEBUG
        else if (m_option == ":enable-assertions") {
            enable_assertions(to_bool(value));
        }
#endif
        else if (m_option == m_error_behavior) {
            if (value == "immediate-exit") {
                ctx.set_exit_on_error(true);
            }
            else if (value == "continued-execution") {
                ctx.set_exit_on_error(false);
            }
            else {
                throw cmd_exception("error setting :error-behavior, 'immediate-execution' or 'continued-execution' expected");
            }
        }
        else if (is_builtin_option(m_option)) {
            throw cmd_exception("option value is not a symbol");
        }
        else {
            set_param(ctx, value.bare_str());
        }
    }

public:
    set_option_cmd():
        set_get_option_cmd("set-option"),
        m_unsupported(false) {
    }

    virtual char const * get_usage() const { return "<keyword> <value>"; }

    virtual char const * get_descr(cmd_context & ctx) const { return "set configuration option."; }

    virtual unsigned get_arity() const { return 2; }

    virtual void prepare(cmd_context & ctx) { m_unsupported = false; m_option = symbol::null; }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        return m_option == symbol::null ? CPK_KEYWORD : CPK_OPTION_VALUE;
    }

    virtual void set_next_arg(cmd_context & ctx, symbol const & opt) { 
        if (m_option == symbol::null) {
            m_option = opt;
        }
        else {
            set_symbol(ctx, opt);
        }
    }

    virtual void set_next_arg(cmd_context & ctx, rational const & val) {
        if (m_option == m_random_seed) {
            ctx.set_random_seed(to_unsigned(val));
        }
        else if (m_option == m_verbosity) {
            set_verbosity_level(to_unsigned(val));
        }
        else if (is_builtin_option(m_option)) {
            throw cmd_exception("option value is not a numeral");
        }
        else {
            std::string str = val.to_string();
            set_param(ctx, str.c_str());
        }
    }

    virtual void set_next_arg(cmd_context & ctx, char const * value) {
        if (m_option == m_regular_output_channel) {
            ctx.set_regular_stream(value);
        }
        else if (m_option == m_diagnostic_output_channel) {
            ctx.set_diagnostic_stream(value);
        }
        else if (is_builtin_option(m_option)) {
            throw cmd_exception("option value is not a string");
        }
        else {
            set_param(ctx, value);
        }
    }

    virtual void execute(cmd_context & ctx) {
        if (m_unsupported)
            ctx.print_unsupported(m_option, m_line, m_pos);
        else
            ctx.print_success();
    }
};

class get_option_cmd : public set_get_option_cmd {
    static void print_bool(cmd_context & ctx, bool b) {
        ctx.regular_stream() << (b ? "true" : "false") << std::endl;
    }
    
    static void print_unsigned(cmd_context & ctx, unsigned v) {
        ctx.regular_stream() << v << std::endl;
    }

    static void print_string(cmd_context & ctx, char const * str) {
        ctx.regular_stream() << str << std::endl;
    }

public:
    get_option_cmd():
        set_get_option_cmd("get-option") {
    }
    virtual char const * get_usage() const { return "<keyword>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "get configuration option."; }
    virtual unsigned get_arity() const { return 1; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_KEYWORD; }
    virtual void set_next_arg(cmd_context & ctx, symbol const & opt) { 
        if (opt == m_print_success) {
            print_bool(ctx, ctx.print_success_enabled()); 
        }
        // TODO: 
        // else if (opt == m_print_warning) {
        // print_bool(ctx, );
        // }
        else if (opt == m_expand_definitions) {
            ctx.print_unsupported(m_expand_definitions, m_line, m_pos);
        }
        else if (opt == m_interactive_mode) {
            print_bool(ctx, ctx.interactive_mode());
        }
        else if (opt == m_produce_proofs) {
            print_bool(ctx, ctx.produce_proofs());
        }
        else if (opt == m_produce_interpolants) {
            print_bool(ctx, ctx.produce_interpolants());
        }
        else if (opt == m_produce_unsat_cores) {
            print_bool(ctx, ctx.produce_unsat_cores());
        }
        else if (opt == m_produce_models) {
            print_bool(ctx, ctx.produce_models());
        }
        else if (opt == m_produce_assignments) {
            print_bool(ctx, ctx.produce_assignments());
        }
        else if (opt == m_global_decls) {
            print_bool(ctx, ctx.global_decls());
        }
        else if (opt == m_random_seed) {
            print_unsigned(ctx, ctx.random_seed());
        }
        else if (opt == m_verbosity) {
            print_unsigned(ctx, get_verbosity_level());
        }
        else if (opt == m_regular_output_channel) {
            print_string(ctx, ctx.get_regular_stream_name());
        }
        else if (opt == m_diagnostic_output_channel) {
            print_string(ctx, ctx.get_diagnostic_stream_name());
        }
        else if (opt == m_error_behavior) {
            if (ctx.exit_on_error()) {
                print_string(ctx, "immediate-exit");
            }
            else {
                print_string(ctx, "continued-execution");
            }
        }
        else if (opt == m_int_real_coercions) {
            print_bool(ctx, ctx.m().int_real_coercions());
        }
        else {
            try {
                ctx.regular_stream() << gparams::get_value(opt) << std::endl;
            }
            catch (gparams::exception ex) {
                ctx.print_unsupported(opt, m_line, m_pos);
            }
        }
    }
};

#define STRINGIZE(x) #x
#define STRINGIZE_VALUE_OF(x) STRINGIZE(x)

class get_info_cmd : public cmd {
    symbol   m_error_behavior;
    symbol   m_name;
    symbol   m_authors;
    symbol   m_version;
    symbol   m_status;
    symbol   m_reason_unknown;
    symbol   m_all_statistics;
public:
    get_info_cmd():
        cmd("get-info"),
        m_error_behavior(":error-behavior"),
        m_name(":name"),
        m_authors(":authors"),
        m_version(":version"),
        m_status(":status"),
        m_reason_unknown(":reason-unknown"),
        m_all_statistics(":all-statistics") {
    }
    virtual char const * get_usage() const { return "<keyword>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "get information."; }
    virtual unsigned get_arity() const { return 1; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_KEYWORD; }
    virtual void set_next_arg(cmd_context & ctx, symbol const & opt) { 
        if (opt == m_error_behavior) {
            if (ctx.exit_on_error())
                ctx.regular_stream() << "(:error-behavior immediate-exit)" << std::endl;
            else
                ctx.regular_stream() << "(:error-behavior continued-execution)" << std::endl;
        }
        else if (opt == m_name) {
            ctx.regular_stream() << "(:name \"Z3\")" << std::endl;
        }
        else if (opt == m_authors) {
            ctx.regular_stream() << "(:authors \"Leonardo de Moura and Nikolaj Bjorner\")" << std::endl;
        }
        else if (opt == m_version) {
            ctx.regular_stream() << "(:version \"" << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER
#ifdef Z3GITHASH
                << " - build hashcode " << STRINGIZE_VALUE_OF(Z3GITHASH)
#endif
                << "\")" << std::endl;
        }
        else if (opt == m_status) {
            ctx.regular_stream() << "(:status " << ctx.get_status() << ")" << std::endl;
        }
        else if (opt == m_reason_unknown) {
            ctx.regular_stream() << "(:reason-unknown " << ctx.reason_unknown() << ")" << std::endl;
        }
        else if (opt == m_all_statistics) {
            ctx.display_statistics();
        }
        else {
            ctx.print_unsupported(opt, m_line, m_pos);
        }
    }
};

class set_info_cmd : public cmd {
    symbol   m_info;
    symbol   m_status;
    symbol   m_unsat;
    symbol   m_sat;
    symbol   m_unknown;
public:
    set_info_cmd():
        cmd("set-info"),
        m_status(":status"),
        m_unsat("unsat"),
        m_sat("sat"),
        m_unknown("unknown") {
    }
    virtual char const * get_usage() const { return "<keyword> <value>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "set information."; }
    virtual unsigned get_arity() const { return 2; }
    virtual void prepare(cmd_context & ctx) { m_info = symbol::null; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        return m_info == symbol::null ? CPK_KEYWORD : CPK_OPTION_VALUE; 
    }
    virtual void set_next_arg(cmd_context & ctx, rational const & val) {}
    virtual void set_next_arg(cmd_context & ctx, char const * val) {}
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) { 
        if (m_info == symbol::null) {
            m_info = s;
        }
        else {
            if (m_info == m_status) {
                if (s == m_unsat) {
                    ctx.set_status(cmd_context::UNSAT);
                }
                else if (s == m_sat) {
                    ctx.set_status(cmd_context::SAT);
                }
                else if (s == m_unknown) {
                    ctx.set_status(cmd_context::UNKNOWN);
                }
                else {
                    throw cmd_exception("invalid ':status' attribute");
                }
            }
        }
    }
    virtual void execute(cmd_context & ctx) {
        ctx.print_success();
    }
};

class declare_map_cmd : public cmd {
    symbol           m_array_sort;
    symbol           m_name;
    ptr_vector<sort> m_domain;
    func_decl *      m_f;
    family_id        m_array_fid;
public:
    declare_map_cmd():
        cmd("declare-map"),
        m_array_sort("Array"),
        m_array_fid(null_family_id) {}

    family_id get_array_fid(cmd_context & ctx) {
        if (m_array_fid == null_family_id) {
            m_array_fid = ctx.m().mk_family_id("array");
        }
        return m_array_fid;
    }
    virtual char const * get_usage() const { return "<symbol> (<sort>+) <func-decl-ref>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "declare a new array map operator with name <symbol> using the given function declaration.\n<func-decl-ref> ::= <symbol>\n                  | (<symbol> (<sort>*) <sort>)\n                  | ((_ <symbol> <numeral>+) (<sort>*) <sort>)\nThe last two cases are used to disumbiguate between declarations with the same name and/or select (indexed) builtin declarations.\nFor more details about the the array map operator, see 'Generalized and Efficient Array Decision Procedures' (FMCAD 2009).\nExample: (declare-map set-union (Int) (or (Bool Bool) Bool))\nDeclares a new function (declare-fun set-union ((Array Int Bool) (Array Int Bool)) (Array Int Bool)).\nThe instance of the map axiom for this new declaration is:\n(forall ((a1 (Array Int Bool)) (a2 (Array Int Bool)) (i Int)) (= (select (set-union a1 a2) i) (or (select a1 i) (select a2 i))))"; }
    virtual unsigned get_arity() const { return 3; }
    virtual void prepare(cmd_context & ctx) { m_name = symbol::null; m_domain.reset(); }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        if (m_name == symbol::null) return CPK_SYMBOL;
        if (m_domain.empty()) return CPK_SORT_LIST;
        return CPK_FUNC_DECL;
    }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) { m_name = s; }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, sort * const * slist) {
        if (num == 0)
            throw cmd_exception("invalid map declaration, empty sort list");
        m_domain.append(num, slist);
    }
    virtual void set_next_arg(cmd_context & ctx, func_decl * f) { 
        m_f = f; 
        if (m_f->get_arity() == 0) 
            throw cmd_exception("invalid map declaration, function declaration must have arity > 0"); 
    }
    virtual void reset(cmd_context & ctx) {
        m_array_fid = null_family_id;
    }
    virtual void execute(cmd_context & ctx) {
        psort_decl * array_sort = ctx.find_psort_decl(m_array_sort);
        if (array_sort == 0)
            throw cmd_exception("Array sort is not available");
        ptr_vector<sort> & array_sort_args = m_domain;
        sort_ref_buffer domain(ctx.m());
        unsigned arity = m_f->get_arity();
        for (unsigned i = 0; i < arity; i++) {
            array_sort_args.push_back(m_f->get_domain(i));
            domain.push_back(array_sort->instantiate(ctx.pm(), array_sort_args.size(), array_sort_args.c_ptr()));
            array_sort_args.pop_back();
        }
        sort_ref range(ctx.m());
        array_sort_args.push_back(m_f->get_range());
        range = array_sort->instantiate(ctx.pm(), array_sort_args.size(), array_sort_args.c_ptr());
        parameter p[1] = { parameter(m_f) };
        func_decl_ref new_map(ctx.m());
        new_map = ctx.m().mk_func_decl(get_array_fid(ctx), OP_ARRAY_MAP, 1, p, domain.size(), domain.c_ptr(), range.get());
        if (new_map == 0)
            throw cmd_exception("invalid array map operator");
        ctx.insert(m_name, new_map);
    }
};

// provides "help" for builtin cmds
class builtin_cmd : public cmd {
    char const * m_usage;
    char const * m_descr;
public:
    builtin_cmd(char const * name, char const * usage, char const * descr):
        cmd(name), m_usage(usage), m_descr(descr) {}
    virtual char const * get_usage() const { return m_usage; }
    virtual char const * get_descr(cmd_context & ctx) const { return m_descr; }
};


void install_basic_cmds(cmd_context & ctx) {
    ctx.insert(alloc(set_logic_cmd));
    ctx.insert(alloc(exit_cmd));
    ctx.insert(alloc(get_assignment_cmd));
    ctx.insert(alloc(get_assertions_cmd));
    ctx.insert(alloc(get_proof_cmd));
    ctx.insert(alloc(get_unsat_core_cmd));
    ctx.insert(alloc(set_option_cmd));
    ctx.insert(alloc(get_option_cmd));
    ctx.insert(alloc(get_info_cmd));
    ctx.insert(alloc(set_info_cmd));
    ctx.insert(alloc(builtin_cmd, "assert", "<term>", "assert term."));
    ctx.insert(alloc(builtin_cmd, "check-sat", "<boolean-constants>*", "check if the current context is satisfiable. If a list of boolean constants B is provided, then check if the current context is consistent with assigning every constant in B to true."));
    ctx.insert(alloc(builtin_cmd, "push", "<number>?", "push 1 (or <number>) scopes."));
    ctx.insert(alloc(builtin_cmd, "pop", "<number>?", "pop 1 (or <number>) scopes."));
    ctx.insert(alloc(builtin_cmd, "get-value", "(<term>+)", "evaluate the given terms in the current model."));
    ctx.insert(alloc(builtin_cmd, "declare-sort", "<symbol> <numeral>?", "declare a new uninterpreted sort of arity <numeral>, if arity is not provided, then it is assumed to be 0."));
    ctx.insert(alloc(builtin_cmd, "define-sort", "<symbol> (<symbol>*) <sort>", "define a new sort."));
    ctx.insert(alloc(builtin_cmd, "declare-fun", "<symbol> (<sort>*) <sort>", "declare a new function/constant."));
    ctx.insert(alloc(builtin_cmd, "declare-const", "<symbol> <sort>", "declare a new constant."));
    ctx.insert(alloc(builtin_cmd, "declare-datatypes", "(<symbol>*) (<datatype-declaration>+)", "declare mutually recursive datatypes.\n<datatype-declaration> ::= (<symbol> <constructor-decl>+)\n<constructor-decl> ::= (<symbol> <accessor-decl>*)\n<accessor-decl> ::= (<symbol> <sort>)\nexample: (declare-datatypes (T) ((BinTree (leaf (value T)) (node (left BinTree) (right BinTree)))))"));
}

void install_ext_basic_cmds(cmd_context & ctx) {
    ctx.insert(alloc(help_cmd));
    ctx.insert(alloc(pp_cmd));
    ctx.insert(alloc(get_model_cmd));
    ctx.insert(alloc(echo_cmd));
    ctx.insert(alloc(labels_cmd));
    ctx.insert(alloc(declare_map_cmd));
    ctx.insert(alloc(builtin_cmd, "reset", 0, "reset the shell (all declarations and assertions will be erased)"));
    install_simplify_cmd(ctx);
    install_eval_cmd(ctx);
}
