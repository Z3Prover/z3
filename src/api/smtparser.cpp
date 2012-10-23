/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtparser.cpp

Abstract:

    SMT parser into ast.

Author:

    Nikolaj Bjorner (nbjorner) 2006-10-4.
    Leonardo de Moura (leonardo) 

Revision History:
--*/

#include<iostream>
#include<istream>
#include<fstream>
#include<sstream>
#include<signal.h>
#include"region.h"
#include"scanner.h"
#include"symbol.h"
#include"vector.h"
#include"symbol_table.h"
#include"smtlib.h"
#include"smtparser.h"
#include"ast_pp.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"warning.h"
#include"error_codes.h"
#include"pattern_validation.h"
#include"unifier.h"
#include"kbo.h"
#include"lpo.h"
#include"substitution_tree.h"
#include"timeit.h"
#include"var_subst.h"
#include"well_sorted.h"
#include "str_hashtable.h"
#include "front_end_params.h"
#include "stopwatch.h"
front_end_params& Z3_API Z3_get_parameters(__in Z3_context c);

class id_param_info {
    symbol    m_string;
    unsigned  m_num_params;
    parameter m_params[0];
public:
    id_param_info(symbol const& s, unsigned n, parameter const* p) : m_string(s), m_num_params(n) {
        for (unsigned i = 0; i < n; ++i) {
            new (&(m_params[i])) parameter();
            m_params[i] = p[i];
        }
    }
    symbol string() const { return m_string; }
    parameter * params() { return m_params; }
    unsigned num_params() const { return m_num_params; }
};

class proto_region {
    ptr_vector<rational>            m_rationals;
    ptr_vector< id_param_info >     m_id_infos;
    region                          m_region;
public:
    proto_region() { }

    ~proto_region() { reset(); }

    rational* allocate(rational const & n) { 
        rational* r = alloc(rational, n); 
        m_rationals.push_back(r);
        return r;
    }

    id_param_info* allocate(vector<parameter> const& params, symbol const & s) {
        unsigned size = sizeof(id_param_info) + sizeof(parameter)*(params.size());
        id_param_info* r = static_cast<id_param_info*>(m_region.allocate(size));
        new (r) id_param_info(s, params.size(), params.c_ptr());
        m_id_infos.push_back(r);
        return r;
    }

    void* allocate(size_t s) { return m_region.allocate(s); }

    void reset() {
        for (unsigned i = 0; i < m_rationals.size(); ++i) {
            dealloc(m_rationals[i]);
        }
        for (unsigned i = 0; i < m_id_infos.size(); ++i) {
            unsigned n = m_id_infos[i]->num_params();
            for (unsigned j = 0; j < n; ++j) {
                m_id_infos[i]->params()[j].~parameter();
            }
        }
        m_rationals.reset();
        m_id_infos.reset();
        m_region.reset();
    }

private:

};

inline void * operator new(size_t s, proto_region& r) { return r.allocate(s); }
inline void * operator new[](size_t s, proto_region & r) { return r.allocate(s); }
inline void operator delete(void*, proto_region& r) {}
inline void operator delete[](void *, proto_region& r) {}

class proto_expr {
public:

    enum kind_t {
        ID,
        STRING,
        COMMENT,
        ANNOTATION,
        INT,
        FLOAT,
        CONS
    };
private:

    int      m_kind:8;
    int      m_line:24;
    int      m_pos;
    union {
        id_param_info* m_id_info;
        rational*      m_number;
        proto_expr**   m_children;
    };

public:

    symbol string() { 
        if (m_kind == INT || m_kind == FLOAT) {
            std::string s = m_number->to_string();
            return symbol(s.c_str());
        }
        if (m_kind == CONS) {
            return symbol("");
        }
        SASSERT(m_kind == STRING || m_kind == COMMENT || m_kind == ID || m_kind == ANNOTATION);
        return m_id_info->string(); 
    }

    rational const& number() { 
        SASSERT(m_kind == INT || m_kind == FLOAT);
        return *m_number; 
    }

    proto_expr* const* children() const { 
        if (m_kind == CONS) {
            return m_children; 
        }
        else {
            return 0;
        }
    }

    int line() { return m_line; }
    int pos() { return m_pos; }
    kind_t kind() { return static_cast<kind_t>(m_kind); }

    unsigned num_params() const { 
        SASSERT(m_kind == ID); 
        return m_id_info->num_params();
    }
    
    parameter *  params() { 
        SASSERT(m_kind == ID); 
        return m_id_info->params();
    }

    proto_expr(proto_region & region, kind_t kind, symbol const & s, vector<parameter> const & params, int line, int pos): 
        m_kind(kind),
        m_line(line),
        m_pos(pos),
        m_id_info(region.allocate(params, s)) {
        SASSERT(kind != CONS);
        SASSERT(kind != INT);
        SASSERT(kind != FLOAT);
    }

    proto_expr(proto_region& region, bool is_int, rational const & n, int line, int pos): 
        m_kind(is_int?INT:FLOAT),
        m_line(line),
        m_pos(pos),
        m_number(region.allocate(n))
    {}

    proto_expr(proto_region& region, ptr_vector<proto_expr>& proto_exprs, int line, int pos): 
        m_kind(CONS),
        m_line(line),
        m_pos(pos) {
        //
        // null terminated list of proto_expression pointers.
        //
        unsigned num_children = proto_exprs.size();
        m_children = new (region) proto_expr*[num_children+1];
        for (unsigned i = 0; i < num_children; ++i) {
            m_children[i] = proto_exprs[i];
        }
        m_children[num_children] = 0;
    }

    ~proto_expr() {}
   

    static proto_expr* copy(proto_region& r, proto_expr* e) {
        switch(e->kind()) {
        case proto_expr::CONS: {
            ptr_vector<proto_expr> args;
            proto_expr* const* children = e->children();
            while (children && *children) {
                args.push_back(copy(r, *children));
                ++children;
            }
            return new (r) proto_expr(r, args, e->line(), e->pos());
        }
        case proto_expr::INT: {
            return new (r) proto_expr(r, true, e->number(), e->line(), e->pos());
        }
        case proto_expr::FLOAT: {
            return new (r) proto_expr(r, false, e->number(), e->line(), e->pos());
        }
        case proto_expr::ID: {
            vector<parameter> params; 
            for (unsigned i = 0; i < e->num_params(); ++i) {
                params.push_back(e->params()[i]);
            }
            return new (r) proto_expr(r, e->kind(), e->string(), params, e->line(), e->pos());
        }
        default: {
            vector<parameter> params; 
            return new (r) proto_expr(r, e->kind(), e->string(), params, e->line(), e->pos());
        }
        }
    }
 
private:

    proto_expr(proto_expr const & other); 
    proto_expr& operator=(proto_expr const & other);    
};


//
// build up proto_expr tree from token stream.
// 

class proto_expr_parser {
    proto_region&  m_region;
    scanner&      m_scanner;
    std::ostream& m_err;
    bool          m_at_eof;
public:
    proto_expr_parser(proto_region& region, scanner& scanner, std::ostream& err):
        m_region(region),
        m_scanner(scanner),
        m_err(err), 
        m_at_eof(false) {
    }

    ~proto_expr_parser() {}

    bool parse(ptr_vector<proto_expr> & proto_exprs, bool parse_single_expr = false) {
        scanner::token   token;
        vector<frame>    stack;
        proto_expr* result = 0;
        
        stack.push_back(frame(PROTO_EXPRS_PRE));

        token = m_scanner.scan();

        if (token == scanner::EOF_TOKEN) {
            proto_exprs.reset();
            return true;
        }
        
        while (!stack.empty()) {

            if (token == scanner::EOF_TOKEN) {
                break;
            }

            if (token == scanner::ERROR_TOKEN) {
                print_error("unexpected token");
                goto done;
            }

            switch(stack.back().m_state) {

            case PROTO_EXPR:
                switch (token) {
                case scanner::LEFT_PAREN:
                    stack.back().m_state = PROTO_EXPRS_PRE;
                    token = m_scanner.scan();
                    break;
                default:
                    stack.back().m_state = ATOM;
                    break;
                }
                break;

            case ATOM: 
                SASSERT(!result);
                switch(token) {
                case scanner::ID_TOKEN:
                    result = new (m_region) proto_expr(m_region, proto_expr::ID, m_scanner.get_id(), m_scanner.get_params(),
                                                       m_scanner.get_line(), m_scanner.get_pos());
                    break;
                case scanner::INT_TOKEN:
                    result = new (m_region) proto_expr(m_region, true, m_scanner.get_number(), m_scanner.get_line(), 
                                                       m_scanner.get_pos());
                    break;
                case scanner::FLOAT_TOKEN:
                    result = new (m_region) proto_expr(m_region, false, m_scanner.get_number(), m_scanner.get_line(), 
                                                       m_scanner.get_pos());
                    break;
                case scanner::STRING_TOKEN:
                    result = new (m_region) proto_expr(m_region, proto_expr::STRING, m_scanner.get_id(), m_scanner.get_params(), 
                                                       m_scanner.get_line(), m_scanner.get_pos());
                    break;
                case scanner::COMMENT_TOKEN:
                    result = new (m_region) proto_expr(m_region, proto_expr::COMMENT, m_scanner.get_id(), m_scanner.get_params(),
                                                       m_scanner.get_line(), m_scanner.get_pos());
                    break;
                case scanner::COLON:
                    token = m_scanner.scan();
                    if (token == scanner::ID_TOKEN) {
                        result = new (m_region) proto_expr(m_region, proto_expr::ANNOTATION, m_scanner.get_id(), 
                                                           m_scanner.get_params(), m_scanner.get_line(), m_scanner.get_pos());
                    }
                    else {
                        print_error("unexpected identifier ':'");
                        token = scanner::ERROR_TOKEN;
                        goto done;
                    }
                    break;
                default:
                    print_error("unexpected token");
                    token = scanner::ERROR_TOKEN;
                    goto done;
                }
                stack.pop_back();
                SASSERT(!stack.empty());
                stack.back().m_proto_exprs.push_back(result);
                result = 0;
                if (parse_single_expr && stack.size() == 1) {
                    goto done;
                }
                token = m_scanner.scan();               
                break;

            case PROTO_EXPRS_PRE:
                SASSERT(!result);
                switch(token) {
                case scanner::RIGHT_PAREN:
                    result = new (m_region) proto_expr(m_region, stack.back().m_proto_exprs, m_scanner.get_line(), 
                                                       m_scanner.get_pos());
                    stack.pop_back();
                    
                    if (stack.empty()) {
                        print_error("unexpected right parenthesis");
                        token = scanner::ERROR_TOKEN;
                        result = 0;
                        goto done;
                    }
                    stack.back().m_proto_exprs.push_back(result);
                    if (parse_single_expr && stack.size() == 1) {
                        goto done;
                    }
                    result = 0;
                    token = m_scanner.scan();
                    break;

                case scanner::EOF_TOKEN:
                    m_at_eof = true;
                    break;

                case scanner::ERROR_TOKEN:                    
                    print_error("could not parse expression");
                    goto done;

                default:
                    stack.back().m_state = PROTO_EXPRS_POST;
                    stack.push_back(frame(PROTO_EXPR));
                    break;
                }
                break;

            case PROTO_EXPRS_POST:
                stack.back().m_state = PROTO_EXPRS_PRE;
                break;
            }
        }

    done:

        if (stack.size() == 1) {
            for (unsigned i = 0; i < stack.back().m_proto_exprs.size(); ++i) {
                proto_exprs.push_back(stack.back().m_proto_exprs[i]);
            }
            return true;
        }

        if (stack.size() == 2) {
            proto_exprs.push_back(new (m_region) proto_expr(m_region, stack.back().m_proto_exprs, m_scanner.get_line(), 
                                                            m_scanner.get_pos()));
            return true;
        }
        
        print_error("unexpected nesting of parenthesis: ", stack.size());
        return false;
    }    

    int get_line() {
        return m_scanner.get_line();
    }

    bool at_eof() const {
        return m_at_eof;
    }

private:

    template<typename T>
    void print_error(char const* msg1, T msg2) {
        m_err << "ERROR: line " << m_scanner.get_line() 
              << " column " << m_scanner.get_pos() << ": " 
              << msg1 << msg2 << "\n";
    }

    void print_error(char const* msg) {
        print_error(msg, "");
    }

    // stack frame:
    enum frame_state {
        PROTO_EXPR,
        PROTO_EXPRS_PRE,
        PROTO_EXPRS_POST,
        ATOM
    };

    class frame {
    public:
        frame_state m_state;
        ptr_vector<proto_expr> m_proto_exprs;
        frame(frame_state state): 
            m_state(state){            
        }
        frame(frame const & other):
            m_state(other.m_state),
            m_proto_exprs(other.m_proto_exprs) {
        }
    private:
        frame& operator=(frame const &);
    };

};

enum smt_cmd_token {
    SMT_CMD_SET_LOGIC,            // logic-name
    SMT_CMD_DECLARE_SORTS,        // sorts-symbols
    SMT_CMD_DECLARE_FUNS,         // func-decls
    SMT_CMD_DECLARE_PREDS,        // pred-decls
    SMT_CMD_DECLARE_DATATYPES,    // datatypes
    SMT_CMD_DEFINE,               // var expr
    SMT_CMD_DEFINE_SORTS,         // (var sort)*
    SMT_CMD_DECLARE_SORT,         // <symbol> <numeral>
    SMT_CMD_DEFINE_SORT,          // <symbol> (<symbol>*) <sort>
    SMT_CMD_DECLARE_FUN,          // <symbol> (<sort>*) <sort>
    SMT_CMD_DECLARE_CONST,        // <symbol> <sort>
    SMT_CMD_DEFINE_FUN,           // <symbol> (<sorted_var>*) <sort> <term>
    SMT_CMD_GET_VALUE,            // (<term>+)
    
    SMT_CMD_PUSH,                 // numeral
    SMT_CMD_POP,                  // numeral
    SMT_CMD_ASSERT,               // expr
    SMT_CMD_CHECK_SAT,            // 
    SMT_CMD_GET_CORE,             // expr+
    SMT_CMD_NEXT_SAT,
    SMT_CMD_SIMPLIFY,             // expr
    SMT_CMD_GET_IMPLIED_EQUALITIES, // expr*
    SMT_CMD_EVAL,                 // expr
    SMT_CMD_GET_ASSERTIONS,       // string
    SMT_CMD_GET_SAT_ASSERTIONS,   // string
    SMT_CMD_KEEP_SAT_ASSERTIONS,  // 
    SMT_CMD_GET_UNSAT_CORE,       // string
    SMT_CMD_GET_PROOF,            // string
    SMT_CMD_SET_OPTION,           // string strings
    SMT_CMD_GET_INFO,             // string
    SMT_CMD_SET_INFO,             // string strings
    SMT_CMD_ECHO,                 // string strings
    SMT_CMD_EXIT,                 // 
    // set-option:
    SMT_CMD_PRINT_SUCCESS,
    SMT_CMD_RANDOM_SEED,
    SMT_CMD_VERBOSITY,
    SMT_CMD_EXPAND_DEFINITIONS,
    SMT_CMD_OUTPUT_CHANNEL,
    SMT_CMD_VERBOSE_OUTPUT_CHANNEL,
    SMT_CMD_ENABLE_CORES,
    SMT_CMD_SET_PARAM,
    SMT_CMD_PRODUCE_MODELS,
    // set-info:
    SMT_CMD_NAME,
    SMT_CMD_VERSION,
    SMT_CMD_AUTHORS,
    SMT_CMD_LAST_FAILURE,
    SMT_CMD_REASON_UNKNOWN,
    SMT_CMD_STATS,
    SMT_CMD_MODEL,
    SMT_CMD_TIME,  
    SMT_CMD_LABELS,
    SMT_CMD_HELP,                 // help

    SMT_CMD_ERROR                 // error token        
};


using namespace smtlib;

class idbuilder {
public:
    virtual ~idbuilder() {}
    virtual bool apply(expr_ref_vector const & args, expr_ref & result) = 0;
};

class builtin_sort_builder : public sort_builder {
    ast_manager& m_manager;
    family_id    m_fid;
    decl_kind    m_kind;
public:
    builtin_sort_builder(ast_manager& m, family_id fid, decl_kind k) : 
        m_manager(m), m_fid(fid), m_kind(k) {}

    virtual bool apply(unsigned num_params, parameter const* params, sort_ref & result) {
        result = m_manager.mk_sort(m_fid, m_kind, num_params, params);
        return result.get() != 0;
    }   
};

class array_sort : public builtin_sort_builder {
public:
    array_sort(ast_manager& m) : 
        builtin_sort_builder(m, m.get_family_id("array"), ARRAY_SORT) {}
};

class bv_sort : public builtin_sort_builder {
public:
    bv_sort(ast_manager& m) : 
        builtin_sort_builder(m, m.get_family_id("bv"), BV_SORT) {}
};

class user_sort : public sort_builder {    
    user_sort_plugin *  m_plugin;
    decl_kind           m_kind;
    symbol              m_name;
    unsigned            m_num_args;
    std::string         m_error_message;
public:
    user_sort(ast_manager& m, unsigned num_args, symbol name): 
        m_name(name),
        m_num_args(num_args) {
        m_plugin = m.get_user_sort_plugin();
        m_kind = m_plugin->register_name(name);
    }
    
    ~user_sort() {}
    
    virtual bool apply(unsigned num_params, parameter const* params, sort_ref & result) {
        if (num_params != m_num_args) {
            std::ostringstream strm;
            strm << "wrong number of arguments passed to " << m_name << " " 
                 << m_num_args << " expected, but " << num_params << " given";
            m_error_message = strm.str();
            return false;
        }
        result = m_plugin->mk_sort(m_kind, num_params, params);
        return true;
    }

    virtual char const* error_message() {
        return m_error_message.c_str();
    }
};




class scoped_stream {
    std::ostream& m_default;
    std::ostream* m_stream;
    bool m_owned;
public:

    scoped_stream(std::ostream& strm) : m_default(strm) {
        m_stream = &strm;
        m_owned = false;
    }

    scoped_stream(proto_expr* e) : m_default(std::cout), m_stream(0), m_owned(false) {
        reset(e, 0);
    }

    scoped_stream(proto_expr* e, std::ostream& out) : m_default(out), m_stream(0), m_owned(false) {
        reset(e, &out);
    }
    
    ~scoped_stream() {
        dealloc_stream();
    }

    void reset(proto_expr* e, std::ostream* out = 0) {
        char const* name = (e && e->kind() == proto_expr::ID)?e->string().bare_str():0;
        reset(name, out);
    }

    void reset(char const* name, std::ostream* out = 0) {
        dealloc_stream();
        m_owned = false;
        if (!out) {
            out = &m_default;
        }
        if (!name) {
            m_stream = out;
        }
        else if (strcmp(name, "stdout")) {
            m_stream = &std::cout;
        }
        else if (strcmp(name, "stderr")) {
            m_stream = &std::cerr;
        }
        else {
            m_stream = alloc(std::ofstream, name, std::ios_base::app);
            m_owned = true;
            if (m_stream->bad() || m_stream->fail()) {
                dealloc(m_stream);
                m_stream = out;
                m_owned = false;
            }
        }
        SASSERT(m_stream);
    }

    std::ostream& operator*() {
        return *m_stream;
    }

private:
    void dealloc_stream() {
        if (m_owned) {
            m_stream->flush();
            dealloc(m_stream);
        }
        m_stream = 0;
        m_owned = false;
    }
};

class cmd_exn {
    Z3_error_code m_code;
public:
    cmd_exn(Z3_error_code code) : m_code(code) {}
    Z3_error_code get() const { return m_code; }
};

static void* g_sw = 0;

#define cmd_context _cmd_context

class cmd_context {
    typedef map<char const *, smt_cmd_token, str_hash_proc, str_eq_proc> str2token;
    str2token               m_str2token;
    ptr_vector<char const>  m_token2str;
    ptr_vector<char const>  m_token2help;
    ptr_vector<char const>  m_token2args;
    svector<bool>           m_is_command;

    struct cmd_info {
        smt_cmd_token m_token;
        void        (*m_action)(cmd_context&);
        cmd_info(smt_cmd_token t, void (*action)(cmd_context&)): 
            m_token(t), m_action(action) {}
    };

    struct opt {
        smt_cmd_token m_token;
        bool        (*m_action)(cmd_context&, proto_expr* const* exprs);
        opt(smt_cmd_token t,  bool (*action)(cmd_context&, proto_expr* const* exprs)): 
            m_token(t), m_action(action) {}
    };

    enum check_sat_state {
        state_unsat,
        state_sat,
        state_unknown,
        state_clear,
        state_new_assertion
    };

    Z3_context               m_context;
    Z3_model                 m_model;
    Z3_ast                   m_proof;
    ast_manager&             m_manager;
    scoped_stream            m_out;
    scoped_stream            m_verbose;
    symbol_table<idbuilder*> m_table;
    region                   m_region;
    ast_ref_vector           m_trail;
    unsigned_vector          m_trail_lim;
    expr_ref_vector          m_asserted;
    unsigned_vector          m_asserted_lim;
    expr_ref_vector          m_asserted_proxies;
    unsigned_vector          m_asserted_proxies_lim;
    bool                     m_print_success;
    bool                     m_enable_cores;
    unsigned                 m_core_size;
    svector<Z3_ast>          m_core;
    check_sat_state          m_check_sat_state;
    svector<check_sat_state> m_check_sat_states;
    stopwatch                m_watch;
    svector<cmd_info>        m_infos;
    svector<opt>             m_options;
    std::ostringstream       m_error_stream;
    
    smtlib::benchmark::status m_status;
    
public:

    cmd_context(ast_manager& m, Z3_context ctx, std::istream& is, std::ostream& out):
        m_context(ctx), 
        m_model(0),
        m_proof(0),
        m_manager(m),
        m_out(out),
        m_verbose(std::cerr),
        m_trail(m),
        m_asserted(m),
        m_asserted_proxies(m),
        m_print_success(Z3_get_parameters(ctx).m_smtlib2_compliant),
        m_enable_cores(false),
        m_core_size(0),
        m_check_sat_state(state_clear),
        m_status(smtlib::benchmark::UNKNOWN)
    {
        add_command("set-logic",     
                    SMT_CMD_SET_LOGIC,     
                    "<string>", "set the background logic");
        add_command("declare-sorts", 
                    SMT_CMD_DECLARE_SORTS, 
                    "<sort declarations>", "declare sorts");
        add_command("declare-funs",  
                    SMT_CMD_DECLARE_FUNS, 
                    "<function and constant declarations>", 
                    "declare functions and constants");
        add_command("declare-preds", 
                    SMT_CMD_DECLARE_PREDS, 
                    "<predicate declarations>", 
                    "declare predicates");
        add_command("declare-datatypes", 
                    SMT_CMD_DECLARE_DATATYPES, 
                    "<data type declarations>", 
                    "declare recursive datatypes");
        add_command("define",        
                    SMT_CMD_DEFINE,        
                    "<id> <expression> or (<id> (<id> <sort>)*) <expression>", 
                    "define an expression shorthand");
        add_command("define-sorts",
                    SMT_CMD_DEFINE_SORTS,
                    "(<id> <sort>)*",
                    "define shorthand for compound sorts, such as arrays");

        add_command("declare-sort", 
                    SMT_CMD_DECLARE_SORT, 
                    "<sort declaration>", "declare sort");
        add_command("define-sort",
                    SMT_CMD_DEFINE_SORT,
                    "<symbol> (<symbol>*) <sort>",
                    "define shorthand for compound sorts, such as arrays");
        add_command("declare-fun",  
                    SMT_CMD_DECLARE_FUN, 
                    "<symbol> (<sort>*) <sort>", 
                    "declare function or constant");
        add_command("declare-const",  
                    SMT_CMD_DECLARE_CONST, 
                    "<symbol> <sort>", 
                    "declare constant");
        add_command("define-fun",        
                    SMT_CMD_DEFINE_FUN,        
                    "<symbol> (<sorted_var>*) <sort> <term>",
                    "define an expression shorthand");
        add_command("get-value",
                    SMT_CMD_GET_VALUE,
                    "(<term>+)",
                    "evaluate list of terms");


        add_command("push",          
                    SMT_CMD_PUSH,          
                    "[<number>]", 
                    "push 1 (or <number>) scopes");
        add_command("pop",           
                    SMT_CMD_POP,           
                    "[<number>]", 
                    "pop 1 (or <number>) scopes");
        add_command("assert",        
                    SMT_CMD_ASSERT,        
                    "<expression>", 
                    "assert expression");
        add_command("check-sat",     
                    SMT_CMD_CHECK_SAT,     
                    "<boolean-constants>*", 
                    "check if the current context is satisfiable. If a list of boolean constants B is provided, then check if the current context is consistent with assigning every constant in B to true.");
        add_command("get-core",     
                    SMT_CMD_GET_CORE,
                    "<boolean-constants>+", 
                    "check if the assumptions are consistent with the current context");
        add_command("next-sat",     
                    SMT_CMD_NEXT_SAT,     
                    "", 
                    "get the next satisfying assignment");
        add_command("simplify",      
                    SMT_CMD_SIMPLIFY,      
                    "<expression>", 
                    "simplify expression and print back result");
        add_command("get-implied-equalities",
                    SMT_CMD_GET_IMPLIED_EQUALITIES,
                    "<expression>*",
                    "obtain list of identifiers for expressions, such that equal expressions have the same identfiers"
                    );
        add_command("eval",
                    SMT_CMD_EVAL,
                    "<expression>",
                    "evaluate expression using the current model and print back result");
        add_command("get-assertions", 
                    SMT_CMD_GET_ASSERTIONS, 
                    "[<file>]", 
                    "retrieve current assertions");
        add_command("get-sat-assertions", 
                    SMT_CMD_GET_SAT_ASSERTIONS, 
                    "[<file>]", 
                    "retrieve current satisfying assignment");
        add_command("keep-sat-assertions", 
                    SMT_CMD_KEEP_SAT_ASSERTIONS, 
                    "", 
                    "assert current satisfying assignment");
        add_command("get-unsat-core", 
                    SMT_CMD_GET_UNSAT_CORE, 
                    "[<file>]", 
                    "retrieve unsatisfiable core of assertions");
        add_command("get-proof",      
                    SMT_CMD_GET_PROOF,      
                    "[<file>]", 
                    "retrieve proof");
        add_command("set-option",     
                    SMT_CMD_SET_OPTION,     
                    "<strings>", 
                    "set auxiliary options");
        add_command("set-info",     
                    SMT_CMD_SET_INFO,     
                    "<attribute> <strings>", 
                    "set auxiliary information");
        add_command("get-info",       
                    SMT_CMD_GET_INFO,       
                    "<attribute>", 
                    "retrieve auxiliary information");
        add_command("echo",       
                    SMT_CMD_ECHO,
                    "<strings>", 
                    "display the given strings");
        add_command("exit",           
                    SMT_CMD_EXIT,           
                    "",         
                    "exit Z3 session");
        m_str2token.insert("quit", SMT_CMD_EXIT);
        add_option("print-success",  
                   SMT_CMD_PRINT_SUCCESS,  
                   "[<bool>]",
                   "toggle printing success",
                   &print_success_option);
        add_option("verbosity",      
                   SMT_CMD_VERBOSITY,
                   "<numeral>",
                   "set verbosity",
                   &verbosity_option);
        add_option("regular-output-channel", 
                   SMT_CMD_OUTPUT_CHANNEL,  
                   "[<file>]",
                   "set name of alternate output channel",
                   &output_channel_option);
        add_option("enable-cores",   
                   SMT_CMD_ENABLE_CORES,
                   "",
                   "enable core extraction during solving",
                   &enable_cores_option);
        add_option("set-param",
                   SMT_CMD_SET_PARAM,
                   "<param-id> <param-value>",
                   "update a mutable configuration parameter",
                   &update_param_option);

        add_option("verbose-output-channel", 
                   SMT_CMD_VERBOSE_OUTPUT_CHANNEL, 
                   "<file>", 
                   "set output channel",
                   &set_verbose_output_channel_option
                   );
        add_option("produce-models",
                    SMT_CMD_PRODUCE_MODELS,
                   "[<bool>]",
                   "toggle model generation",
                   &produce_models_option);
        //
        // other options:
        // add_option("random-seed",    SMT_CMD_RANDOM_SEED,  0, "");
        // add_option("expand-definitions",SMT_CMD_EXPAND_DEFINITIONS, 0, "");
        // "produce-proofs"
        // "produce-models"
        // "produce-assignments"
        //

        add_info("name",           
                 SMT_CMD_NAME, 
                 "",
                 "solver name",
                 &name_info
                 );
        add_info("version",        
                 SMT_CMD_VERSION,
                 "",
                 "solver version",
                 &version_info
                 );
        add_info("authors",        
                 SMT_CMD_AUTHORS,
                 "",
                 "solver authors",
                 &authors_info);
        add_info("statistics",          
                 SMT_CMD_STATS,           
                 "",
                 "search statistics",
                 &stats_info);
        add_info("all-statistics",          
                 SMT_CMD_STATS,           
                 "",
                 "search statistics",
                 &stats_info);
        add_info("model",          
                 SMT_CMD_MODEL,   
                 "",
                 "model from satisfied assertions",
                 &model_info
                 );
        add_info("last-failure",   
                 SMT_CMD_LAST_FAILURE, 
                 "",
                 "reason for previous search failure",
                 &last_failure_info
                 );
        add_info("reason-unknown",   
                 SMT_CMD_REASON_UNKNOWN,
                 "",
                 "reason for previous unknown answer; 'memout' for out of memory, 'incomplete' for everything else",
                 &reason_unknown_info
                 );
        add_info("time",           
                 SMT_CMD_TIME,     
                 "",
                 "time taken by solver",
                 &time_info
                 );
        add_info("labels",         
                 SMT_CMD_LABELS,   
                 "",
                 "retrieve (Boogie) labels from satisfiable assertion",
                 &labels_info);
        add_info("help",           
                 SMT_CMD_HELP,           
                 "", 
                 "print this help",
                 &help_info);



#ifdef _EXTERNAL_RELEASE
        Z3_set_ast_print_mode(m_context, Z3_PRINT_SMTLIB2_COMPLIANT);
#else
        // use internal pretty printer
        Z3_set_ast_print_mode(m_context, Z3_PRINT_SMTLIB_FULL);
        // Z3_set_ast_print_mode(m_context, Z3_PRINT_SMTLIB2_COMPLIANT);
#endif
        Z3_set_error_handler(m_context, error_handler);
        set_error_stream(&m_error_stream);
        set_warning_stream(&m_error_stream);
    }
    
    ~cmd_context() {
        if (m_model) {
            Z3_del_model(m_context, m_model);
        }
        set_error_stream(0);
        set_warning_stream(0);
    }

    //
    // NB. As it is now, the symbol table used in m_benchmark is not
    // scoped. Declarations just live on or get over-written.
    // 
    void push(unsigned num_scopes) {
        while (num_scopes > 0) {
            m_table.begin_scope();
            m_region.push_scope();
            Z3_push(m_context);
            m_trail_lim.push_back(m_trail.size());
            m_asserted_lim.push_back(m_asserted.size());
            m_asserted_proxies_lim.push_back(m_asserted_proxies.size());
            --num_scopes;
            m_check_sat_states.push_back(m_check_sat_state);
        }
    }
    void pop(unsigned num_scopes) {
        if (m_trail_lim.size() < num_scopes) {
            num_scopes = m_trail_lim.size();
        }
        Z3_pop(m_context, num_scopes);
        m_region.pop_scope(num_scopes);
        while (num_scopes > 0) {
            m_table.end_scope();
            --num_scopes;
            m_trail.resize(m_trail_lim.back());
            m_trail_lim.pop_back();
            m_asserted.resize(m_asserted_lim.back());
            m_asserted_lim.pop_back();
            m_asserted_proxies.resize(m_asserted_proxies_lim.back());
            m_asserted_proxies_lim.pop_back();
            m_check_sat_state = m_check_sat_states.back();
            m_check_sat_states.pop_back();
        }
        m_proof = 0;
        m_core_size = 0;
    }

    static void error_handler(Z3_context, Z3_error_code code) {
        throw cmd_exn(code);
    }
    
    symbol_table<idbuilder*>& get_table() { return m_table; }

    Z3_context get_context() { return m_context; }

    std::ostream& get_out() { return *m_out; }

    void print_quoted(const char* str) { get_out() << "\"" << str << "\""; }

    void set_out(proto_expr* e) { m_out.reset(e); }

    void add_trail(ast* a) { m_trail.push_back(a); }

    void add_asserted(expr* e) { 
        if (get_enable_cores()) {
            expr* proxy = m_manager.mk_fresh_const("proxy", m_manager.mk_bool_sort());
            expr_ref imp(m_manager);
            // It is not necessary to use iff (it is just overhead). 
            imp = m_manager.mk_implies(proxy, e);
            TRACE("proxy", tout << "new proxy:\n " << mk_pp(imp, m_manager) << "\n";);
            Z3_assert_cnstr(m_context, reinterpret_cast<Z3_ast>(imp.get()));
            m_asserted_proxies.push_back(proxy);            
        }
        else {
            Z3_assert_cnstr(m_context, reinterpret_cast<Z3_ast>(e));
        }
        m_asserted.push_back(e); 
        if (m_check_sat_state != state_unsat) {
            m_check_sat_state = state_new_assertion;
        }
    }
   
    unsigned get_num_assertions() const { return m_asserted.size(); }

    expr* get_assertion(unsigned idx) { return m_asserted[idx].get(); }

    Z3_ast* get_proxies_ptr() { return reinterpret_cast<Z3_ast*>(m_asserted_proxies.c_ptr()); }

    unsigned* get_core_size_ptr() { return &m_core_size; }

    Z3_ast* get_core_ptr() { 
        m_core.resize(m_asserted_proxies.size());
        if (m_core_size > m_core.size()) {
            m_core_size = m_core.size();
        }
        return m_core.c_ptr();
    }       

    region& get_region() { return m_region; }
    

    void set_print_success(bool b) { m_print_success = b; }

    void set_enable_cores() { m_enable_cores = true; }    

    void unset_enable_cores() { m_enable_cores = false; }    

    void update_param(char const* p, char const* v) {
        Z3_update_param_value(m_context, p, v);
    }

    bool get_enable_cores() const { return m_enable_cores; }

    void print_success() {
        if (m_print_success) {
            *m_out << "success\n";
        }
    }

    void print_unsupported() {
        *m_out << "unsupported\n";
    }
    
    void print_failure(char const* msg, proto_expr* expr) {
        if (Z3_get_parameters(m_context).m_display_error_for_vs) {
            if (msg[0] != 'Z' || msg[1] != '3') {
                *m_out << "Z3";
                if (expr) {
                    *m_out << "(" << expr->line() << "," << expr->pos() << ")";
                }           
                *m_out << ": ERROR: ";
            }
            *m_out << msg;
            if (msg[strlen(msg)-1] != '\n') {
                *m_out << "\n";
            }
        }
        else {
            *m_out << "(error \"";
            if (expr) {
                *m_out << "line " << expr->line() << " column " << expr->pos() << ": ";
            }
            *m_out << escaped(msg, true) << "\")\n";
#ifndef _EXTERNAL_RELEASE
            exit(ERR_PARSER);
#endif
        }
    }

    Z3_model* get_model_ptr() { 
        if (m_model) {
            Z3_del_model(m_context, m_model);
            m_model = 0;
        }
        return &m_model;
    }

    Z3_model get_model() { return m_model; }
    
    Z3_ast* get_proof_ptr() {
        m_proof = 0;
        return &m_proof;
    }
    
    void get_proof(std::ostream& out, proto_expr* p_expr) { 
        Z3_ast pr = m_proof;
        if (pr) {
            out << Z3_ast_to_string(m_context, pr) << "\n";       
        }
        else if (Z3_get_parameters(m_context).m_proof_mode == PGM_DISABLED) {
            print_failure("proofs are disabled - enable them using the configuration PROOF_MODE={1,2}", p_expr);
        }
        else {                
            print_failure("there is no proof to display", p_expr);
        }
    }

    smt_cmd_token string2token(char const * str) {
        str2token::entry * e = m_str2token.find_core(str);
        if (e)
            return e->get_data().m_value;
        else
            return SMT_CMD_ERROR;
    }

    class scoped_stopwatch {
        cmd_context& m_ctx;
        bool         m_first;
        void        (*m_old_handler)(int);

        static scoped_stopwatch* get_sw() { return static_cast<scoped_stopwatch*>(g_sw); }        

        static void on_ctrl_c(int) {
            if (get_sw()->m_first) {
                Z3_soft_check_cancel(get_sw()->m_ctx.get_context());
                get_sw()->m_first = false;
            }
            else {
                signal (SIGINT, get_sw()->m_old_handler); 
                raise (SIGINT);
            }
        }
    public:
        scoped_stopwatch(cmd_context& c) : m_ctx(c), m_first(true) { 
            g_sw = this;
            c.m_watch.reset();
            c.m_watch.start(); 
            m_old_handler = signal(SIGINT, on_ctrl_c); // TBD: parallel?
        }
        ~scoped_stopwatch() { 
            m_ctx.m_watch.stop();
            if (m_old_handler != SIG_ERR) {
                signal(SIGINT, m_old_handler);
            }
        }
    };

    //static scoped_stopwatch* g_sw = 0;

    double get_seconds() { 
        return m_watch.get_seconds(); 
    }

    bool get_command_help(std::ostream& out, smt_cmd_token tok) {
        if (!m_is_command[tok]) {
            return false;
        }
        out << " (" << m_token2str[tok];
        if (m_token2args[tok] && m_token2args[tok][0]) {
            out << " " << m_token2args[tok];
        }
        out << ")\n";
        out << "    " << m_token2help[tok] << "\n\n";
        return true;
    }

    void get_help(std::ostream& out) {
        out << "\" available commands:\n\n";
        for (unsigned i = 0; i < m_token2args.size(); ++i) {
            get_command_help(out, static_cast<smt_cmd_token>(i));
        }
        get_info_help(out, " ");
        out << "\n";
        set_option_help(out, " ");
        out << "\"";
    }

    bool get_info(smt_cmd_token tok) {
        for (unsigned i = 0; i < m_infos.size(); ++i) {
            if (m_infos[i].m_token == tok) {                
                get_out() << ":" << m_token2str[tok] << " ";
                m_infos[i].m_action(*this);
                return true;
            }
        }
        return false;
    }

    void get_info_help(std::ostream& strm, char const* line_start) {
        for (unsigned i = 0; i < m_infos.size(); ++i) {
            smt_cmd_token tok = m_infos[i].m_token;
            strm << line_start << "(get-info " << m_token2str[tok];
            if (m_token2args[tok] && m_token2args[tok][0]) {
                strm << " " << m_token2args[tok];
            }
            strm << ")\n";
            strm << line_start << "   " << m_token2help[tok] << "\n";            
        }   
    }

    bool set_option(smt_cmd_token tok, proto_expr* const* chs) {
        for (unsigned i = 0; i < m_options.size(); ++i) {
            if (m_options[i].m_token == tok) {
                return m_options[i].m_action(*this, chs);
            }
        }
        return update_param_option(*this, chs-1);
        // return false;        
    }

    bool set_info(proto_expr* e0, proto_expr* const* chs) {
        proto_expr* e1 = chs[0];
        symbol s0, s1;
        if (e0)
            s0 = e0->string();
        if (e1)
            s1 = e1->string();

        if (s0 == symbol("status") && s1 == symbol("sat")) {
            m_status = smtlib::benchmark::SAT;
        }
        else if (s0 == symbol("status") && s1 == symbol("unsat")) {
            m_status = smtlib::benchmark::UNSAT;
        }
        else if (s0 == symbol("status") && s1 == symbol("unknown")) {
            m_status = smtlib::benchmark::UNKNOWN;
        }          
        else {
#ifdef Z3DEBUG
            std::cout << s0 << " " << s1 << "\n";
#endif
        }
        
        // :source
        // :smt-lib-version
        // :category
        // :status
        // no-op
        return true;
    }

    void set_option_help(std::ostream& strm, char const* line_start) {
        for (unsigned i = 0; i < m_options.size(); ++i) {
            smt_cmd_token tok = m_options[i].m_token;
            strm << line_start << "(set-option " << m_token2str[tok];
            if (m_token2args[tok] && m_token2args[tok][0]) {
                get_out() << " " << m_token2args[tok];
            }
            strm << ")\n";
            strm << line_start << "   " << m_token2help[tok] << "\n";            
        }           
    }

    unsigned parse_opt_numeral(proto_expr* e, unsigned default_value) {
        if (e && e->kind() == proto_expr::INT) {
            rational r = e->number();
            if (r.is_unsigned()) {
                return r.get_unsigned();
            }
        }
        return default_value;
    }

    bool parse_opt_bool(proto_expr* e, bool default_value) {
        if (e && e->kind() == proto_expr::ID) {      
            if (strcmp(e->string().bare_str(), "true") == 0) {
                return true;
            }
            if (strcmp(e->string().bare_str(), "false") == 0) {
                return false;
            }
        }
        return default_value;            
    }

    
    void get_core(proto_expr* p_expr, std::ostream& out, 
                  unsigned sz, expr** exprs, bool just_get_core) {

        
        Z3_context ctx = get_context();        
        Z3_lbool r;
        scoped_stopwatch stopw(*this);

        if (get_enable_cores()) {
            print_failure("cores should be disabled", p_expr);
            return;
        }

        for (unsigned i = 0; i < sz; ++i) {
            if (!is_uninterp_const(exprs[i]) || !m_manager.is_bool(exprs[i])) {
                print_failure("assumptions must be boolean constants (e.g., p1, p2, q1)", p_expr);
                return;
            }
        }

        // set_enable_cores();
        // push(1);
        // for (unsigned i = 0; i < sz; ++i) {
        //    add_asserted(exprs[i]);
        // }

        unsigned max_core_size = sz;
        unsigned core_size     = sz;
        m_core.reserve(max_core_size);
        Z3_ast * core = m_core.c_ptr();

        r = Z3_check_assumptions(ctx, sz, reinterpret_cast<Z3_ast*>(exprs),
                                 get_model_ptr(), get_proof_ptr(), 
                                 &core_size, core);
        switch(r) {
        case Z3_L_FALSE:
            if (!just_get_core)
                out << "unsat\n";
            print_core_as_is(out, core_size, core);
            m_check_sat_state = state_unsat;
            break;
        case Z3_L_TRUE:
            out << "sat\n";
            m_check_sat_state = state_sat;
            break;
        case Z3_L_UNDEF:
            out << "unknown\n";
            m_check_sat_state = state_unknown;
            break;
        default:                
            throw default_exception("unexpected output of check-sat\n");
            break;
        }
        // unset_enable_cores();
        // pop(1);
    }

    void check_sat(std::ostream& out) {
        Z3_context ctx = get_context();        
        Z3_lbool r;
        scoped_stopwatch stopw(*this);
        
        if (get_enable_cores()) {
            r = Z3_check_assumptions(ctx, get_num_assertions(), get_proxies_ptr(), 
                                     get_model_ptr(), get_proof_ptr(), 
                                     get_core_size_ptr(), get_core_ptr());
            
        }            
        else if (Z3_get_parameters(ctx).m_proof_mode != PGM_DISABLED) {
            unsigned core_size = 0;
            Z3_ast core[1] = { 0 };                
            r = Z3_check_assumptions(ctx, 0, 0, get_model_ptr(), get_proof_ptr(), &core_size, core);
        }
        else if (Z3_get_parameters(ctx).m_model) {
            r = Z3_check_and_get_model(ctx, get_model_ptr());
        }
        else {
            r = Z3_check(ctx);
        }
        switch(r) {
        case Z3_L_FALSE:
            out << "unsat\n";
            m_check_sat_state = state_unsat;
            break;
        case Z3_L_TRUE:
            out << "sat\n";
            m_check_sat_state = state_sat;
            break;
        case Z3_L_UNDEF:
            out << "unknown\n";
            m_check_sat_state = state_unknown;
            break;
        default:                
            throw default_exception("unexpected output of check-sat\n");
            break;
        }

        // check status (duplicate from smtlib_sover)
        // smtlib_solver contains support for
        // - spc
        //   - missing.
        // - dumping statistics / proofs / model / labels
        //   - redundant given additional command-line options
        // 
        switch(m_status) {
        case smtlib::benchmark::SAT:
            if (r == Z3_L_FALSE) {
#ifdef _EXTERNAL_RELEASE
                std::cout << "unsat - check annotation which says sat\n";
#else
                std::cout << "BUG: unsoundness.\n";
                exit(ERR_UNSOUNDNESS);
#endif                
            }
            else if (r == Z3_L_UNDEF) {
#ifndef _EXTERNAL_RELEASE
                std::cout << "BUG: gaveup.\n";
                exit(ERR_UNKNOWN_RESULT);
#endif
            }
            break;
        case smtlib::benchmark::UNSAT:
            if (r == Z3_L_TRUE) {
#ifdef _EXTERNAL_RELEASE
                std::cout << "sat - check annotation which says unsat\n";
#else
                std::cout << "BUG: incompleteness.\n";
                exit(ERR_INCOMPLETENESS);
#endif
            }
            else if (r == Z3_L_UNDEF) {
#ifndef _EXTERNAL_RELEASE
                std::cout << "BUG: gaveup.\n";
                exit(ERR_UNKNOWN_RESULT);
#endif
            }
            break;
        default:
            break;
        }
    }

    void next_sat(std::ostream& out) {
        Z3_context ctx = get_context();
        if (m_check_sat_state == state_sat || m_check_sat_state == state_unknown) {
            Z3_literals lits = Z3_get_relevant_literals(ctx);
            if (lits) {
                Z3_block_literals(ctx, lits);
                Z3_del_literals(ctx, lits);
            }
        }
        check_sat(out);
    }

    void get_sat_assertions(std::ostream& out) {
        if (m_check_sat_state == state_unsat) {
            out << "false\n";
        }
        else {
            Z3_ast assignment = Z3_get_context_assignment(m_context);
            out << Z3_ast_to_string(m_context, reinterpret_cast<Z3_ast>(assignment)) << "\n";
        }
    }

    void get_implied_equalities(std::ostream& out, unsigned num_exprs, expr* const* exprs) {
        buffer<unsigned> class_ids(num_exprs, UINT_MAX);
        Z3_lbool r = Z3_get_implied_equalities(m_context, 
                                               num_exprs,
                                               (Z3_ast*) exprs,
                                               class_ids.c_ptr());
        if (r == Z3_L_FALSE) {
            out << "unsat\n";
            return;
        }
        out << "(";
        for (unsigned i = 0; i < num_exprs; ++i) {
            out << class_ids[i];
            if (i + 1 < num_exprs) {
                out << " ";
            }
        }
        out << ")\n";
    }

    void eval(std::ostream& out, proto_expr* p_expr, expr* e) {
        Z3_model m = get_model();
        if (!m) {
            print_failure("There is no model in the current context", p_expr);
            return;
        }
        Z3_ast result = 0;
        Z3_bool fully_simplified = Z3_eval(m_context, m, reinterpret_cast<Z3_ast>(e), &result);
        if (!result) {
            print_failure("Evaluation was not successful", p_expr);
            return;
        }
        (void) fully_simplified;
        out << Z3_ast_to_string(m_context, result) << "\n";
    }

    void eval(std::ostream& out, proto_expr* p_expr, unsigned num_args, expr*const* args) {
        svector<Z3_ast> results;
        Z3_model m = get_model();
        if (!m) {
            print_failure("There is no model in the current context", p_expr);
            return;
        }
        for (unsigned i = 0; i < num_args; ++i) {
            Z3_ast result = 0;
            Z3_bool fully_simplified = Z3_eval(m_context, m, reinterpret_cast<Z3_ast>(args[i]), &result);
            if (!result) {
                print_failure("Evaluation was not successful", p_expr);
                return;
            }
            (void) fully_simplified;
            results.push_back(result);
        }
        out << "(";
        for (unsigned i = 0; i < num_args; ++i) {
            out << Z3_ast_to_string(m_context, results[i]);
            if (i + 1 < num_args) {
                out << "\n";
            }
        }
        out << ")\n";
    }




    void get_unsat_core(std::ostream& out, proto_expr* p_expr) {
        if (!get_enable_cores()) {
            print_failure("cores have not been enabled, use (set-option enable-cores)", p_expr);
            return;
        }
        print_core(out);
    }

    Z3_ast find_proxy(Z3_ast proxy) {
        for (unsigned i = 0; i < m_asserted.size(); ++i) {
            if (m_asserted_proxies[i] == (expr*)proxy) {
                return reinterpret_cast<Z3_ast>(m_asserted[i].get());
            }
        }
        UNREACHABLE();
        return proxy;
    }

    void print_core(std::ostream& out) {
        unsigned csz = *get_core_size_ptr();
        out << "(";
        for (unsigned i = 0; i < csz; ++i) {
            out << Z3_ast_to_string(m_context, find_proxy(get_core_ptr()[i]));
            if (i + 1 < csz) out << "\n";
        }
        out << ")\n";
    }

    void print_core_as_is(std::ostream & out, unsigned csz, Z3_ast * core) {
        out << "(";
        for (unsigned i = 0; i < csz; ++i) {
            out << Z3_ast_to_string(m_context, core[i]);
            if (i + 1 < csz) out << " ";
        }
        out << ")\n";
    }

    void get_assertions(std::ostream& out) {
        out << "(";
        unsigned num_assertions = get_num_assertions();
        for (unsigned i = 0; i < num_assertions; ++i) {
            out << Z3_ast_to_string(m_context, reinterpret_cast<Z3_ast>(get_assertion(i)));
            if (i + 1 < num_assertions) out << "\n";
        }
        out << ")\n";
    }

    bool has_error() {
        return m_error_stream.tellp() > 0;
    }

    void flush_errors() {
        if (has_error()) {
            m_error_stream.put(0);
            print_failure(m_error_stream.str().c_str(), 0);
            m_error_stream.seekp(0);
            m_error_stream.clear();
        }
    }

    std::ostream& get_error_stream() {
        return m_error_stream;
    }

private:

    void add_command(
        char const* name,
        smt_cmd_token tok, 
        char const* args,
        char const* help,
        bool is_command = true
        ) {
        m_str2token.insert(name, tok);
        if ((unsigned)tok >= m_token2str.size()) {
            m_token2str.resize(tok+1);
            m_token2help.resize(tok+1);
            m_token2args.resize(tok+1);
            m_is_command.resize(tok+1);
        }
        m_token2str[tok] = name;
        m_token2help[tok] = help;
        m_token2args[tok] = args;
        m_is_command[tok] = is_command;
    }

    void add_info(
        char const* name,
        smt_cmd_token t, 
        char const* args,
        char const* help,
        void (*action)(cmd_context&)
        )
    {
        add_command(name, t, args, help, false);
        m_infos.push_back(cmd_info(t, action));
    }

    void add_option(
        char const* name,
        smt_cmd_token t,
        char const* args,
        char const* help,
        bool        (*action)(cmd_context&, proto_expr* const* exprs)
        )
    {
        add_command(name, t, args, help, false);
        m_options.push_back(opt(t, action));
    }

    
    static void name_info(cmd_context& ctx) { ctx.print_quoted("Z3"); }

    static void version_info(cmd_context& ctx) { 
        unsigned maj, min, bn, rn;
        Z3_get_version(&maj,&min,&bn,&rn);
        ctx.get_out() << "\"" << maj << "." << min << "-" << bn << "." << rn << "\"";
    }

    static void authors_info(cmd_context& ctx) { ctx.print_quoted("Leonardo de Moura and Nikolaj Bjorner"); }

    static void last_failure_info(cmd_context& cmd_ctx) {
        Z3_context ctx = cmd_ctx.get_context();
        Z3_search_failure sf = Z3_get_search_failure(ctx);
        static char const * reasons[8] = { "no failure", "unknown", "timeout", "memout", 
                                           "user canceled", "exceeded conflict bound",
                                           "incomplete theory support",
                                           "formulas used quantifiers that may not have been instantiated fully"
        };
        if (sf < 8) {
            cmd_ctx.print_quoted(reasons[sf]);
        }
        else {
            cmd_ctx.print_quoted("not documented");
            UNREACHABLE();
        }
    }

    static void reason_unknown_info(cmd_context& cmd_ctx) {
        Z3_context ctx = cmd_ctx.get_context();
        Z3_search_failure sf = Z3_get_search_failure(ctx);
        
        if (sf == 3)
            cmd_ctx.print_quoted("memout");
        else
            cmd_ctx.print_quoted("incomplete");
    }

    static void stats_info(cmd_context& cmd_ctx) {
        cmd_ctx.get_out() << "\"" << escaped(Z3_statistics_to_string(cmd_ctx.get_context()), true) << "\"";
    }
    
    static void model_info(cmd_context& cmd_ctx) {
        Z3_context ctx = cmd_ctx.get_context();
        Z3_model m = cmd_ctx.get_model();
        if (m) {
            if (Z3_get_parameters(ctx).m_model_v1_pp || Z3_get_parameters(ctx).m_model_v2_pp) {
                cmd_ctx.get_out() << "\"" << escaped(Z3_model_to_string(ctx, m), true) << "\"";
            } else {
              cmd_ctx.get_out() << "(z3_model" << std::endl
                                << Z3_model_to_string(ctx, m)
                                << ")";
            }
        }
        else if (!Z3_get_parameters(ctx).m_model) {
            cmd_ctx.print_quoted("models are disabled - enable them using the configuration MODEL=true");
        }
        else {
            cmd_ctx.print_quoted("there is no model at the current scope");
        }     
    }

    static void time_info(cmd_context& cmd_ctx) {
        cmd_ctx.get_out() << cmd_ctx.get_seconds();
    }

    static void labels_info(cmd_context& cmd_ctx) {
        std::ostream& out = cmd_ctx.get_out();
        Z3_context ctx = cmd_ctx.get_context();
        Z3_literals lits = Z3_get_relevant_labels(ctx);
        unsigned sz = Z3_get_num_literals(ctx, lits);
        if (sz > 0) {
            out << "(z3_labels";
            for (unsigned i = 0; i < sz; ++i) {
                out << " ";
                out << Z3_get_symbol_string(ctx, Z3_get_label_symbol(ctx, lits, i));
            }
            out << ")";
        }    
        Z3_del_literals(ctx, lits);
    }

    static void help_info(cmd_context& cmd_ctx) {
        cmd_ctx.get_help(cmd_ctx.get_out());        
    }

    static bool print_success_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        cmd_ctx.set_print_success(cmd_ctx.parse_opt_bool(chs?*chs:0, true));
        return true;
    }

    static bool produce_models_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        cmd_ctx.update_param("MODEL", cmd_ctx.parse_opt_bool(chs?*chs:0, true) ? "true" : "false");
        return true;
    }

    static bool verbosity_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        unsigned lvl = cmd_ctx.parse_opt_numeral(chs?*chs:0, 0);
        set_verbosity_level(lvl);                
        return true;
    }

    static bool output_channel_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        cmd_ctx.set_out(chs?*chs:0);
        return true;
    }

    static bool enable_cores_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        cmd_ctx.set_enable_cores();
        return true;
    }

    static void print_parameters(cmd_context& cmd_ctx) {
        front_end_params& p = Z3_get_parameters(cmd_ctx.m_context);
        ini_params ini;
        p.register_params(ini);
        ini.display_params(cmd_ctx.get_out());
    }

    static void print_parameter_help(char const* param, cmd_context& cmd_ctx) {
        front_end_params& p = Z3_get_parameters(cmd_ctx.m_context);
        ini_params ini;
        p.register_params(ini);
        ini.display_parameter_help(param,cmd_ctx.get_out());
    }

    static bool update_param_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        if (!chs) {
            print_parameters(cmd_ctx);
            return false;
        }
        if (chs[0] && !chs[1] && chs[0]->kind() == proto_expr::CONS) {
            chs = chs[0]->children();
        }

        proto_expr* p = chs[0];
        proto_expr* v = chs[1];
        char const* p_string = 0;
        char const*v_string = 0;
        std::string v_str;
        if (!p || (p->kind() != proto_expr::ID && p->kind() != proto_expr::STRING && p->kind() != proto_expr::ANNOTATION)) {
            print_parameters(cmd_ctx);
            return false;
        }
        p_string = p->string().bare_str();
        if (v && (v->kind() == proto_expr::INT || v->kind() == proto_expr::FLOAT)) {
            v_str += v->number().to_string();
            v_string = v_str.c_str();
        }
        else if (!v || (v->kind() != proto_expr::ID && v->kind() != proto_expr::STRING)) {
            print_parameter_help(p->string().bare_str(), cmd_ctx);
            return false;
        }
        else {
            v_str = v->string().bare_str();
            if (v_str.length() > 2 && v_str[0] == '|' && v_str[v_str.length() - 1] == '|') {
                // strip the quotes                
                v_str = v_str.substr(1, v_str.length() - 2);
            }
            v_string = v_str.c_str();
        }
        // hack for generating warning message when trying to set PROOF_MODE inside the command context.
        if (strcmp(p_string, "PROOF_MODE") == 0) {
            warning_msg("PROOF_MODE can only be set as a command line option when invoking z3.exe (e.g., \"z3.exe PROOF_MODE=2 file.smt2\"), or when creating a fresh logical context using the Z3 API.");
            return false;
        }
        cmd_ctx.update_param(p_string, v_string);
        return true;
    }

    static bool set_verbose_output_channel_option(cmd_context& cmd_ctx, proto_expr*const* chs) {
        cmd_ctx.m_verbose.reset(chs?(*chs):0);
        set_verbose_stream(*cmd_ctx.m_verbose);
        return true;
    }
};


class smtparser : public parser {
    struct builtin_op {
        family_id m_family_id;
        decl_kind m_kind;
        builtin_op() : m_family_id(null_family_id), m_kind(0) {}
        builtin_op(family_id fid, decl_kind k) : m_family_id(fid), m_kind(k) {}
    };

    class add_plugins {

    public:
        add_plugins(ast_manager& m) {
#define REGISTER_PLUGIN(NAME, MK) {                             \
                family_id fid = m.get_family_id(symbol(NAME));  \
                if (!m.has_plugin(fid)) {                       \
                    m.register_plugin(fid, MK);                 \
                }                                                       \
            } ((void) 0)
            
            REGISTER_PLUGIN("arith",      alloc(arith_decl_plugin));
            REGISTER_PLUGIN("bv",         alloc(bv_decl_plugin));
            REGISTER_PLUGIN("array",      alloc(array_decl_plugin));
            
        };
    };

    ast_manager&             m_manager;
    add_plugins              m_plugins;
    arith_util               m_anum_util;
    bv_util                  m_bvnum_util;
    pattern_validator        m_pattern_validator;
    bool                     m_ignore_user_patterns;
    unsigned                 m_binding_level;     // scope level for bound vars
    benchmark                m_benchmark; // currently parsed benchmark
    sort_ref_vector          m_pinned_sorts;

    typedef map<symbol, builtin_op, symbol_hash_proc, symbol_eq_proc> op_map;
    op_map                   m_builtin_ops;
    op_map                   m_builtin_sorts;

    symbol                   m_let;               // commonly used symbols.
    symbol                   m_flet;
    symbol                   m_forall;
    symbol                   m_exists;
    symbol                   m_lblneg;
    symbol                   m_lblpos;
    symbol                   m_associative;
    symbol                   m_commutative;
    symbol                   m_injective;
    symbol                   m_sorts;
    symbol                   m_funs;
    symbol                   m_preds;
    symbol                   m_definition;
    symbol                   m_axioms;
    symbol                   m_notes;
    symbol                   m_theory;
    symbol                   m_language;
    symbol                   m_extensions;
    symbol                   m_array;
    symbol                   m_bang;
    symbol                   m_underscore;
    sort*                    m_int_sort;
    sort*                    m_real_sort;
    family_id                m_bv_fid;
    family_id                m_arith_fid;
    family_id                m_array_fid;
    family_id                m_rel_fid;
    datatype_decl_plugin *   m_dt_plugin;
    datatype_util            m_dt_util;
    substitution_tree        m_st;
    func_decl *              m_sk_hack;
    std::ostream*            m_err;
    bool                     m_display_error_for_vs;


public:

    smtparser(ast_manager& m, bool ignore_user_patterns):
        m_manager(m),
        m_plugins(m),
        m_anum_util(m),
        m_bvnum_util(m),
        m_pattern_validator(m),
        m_ignore_user_patterns(ignore_user_patterns), 
        m_binding_level(0),
        m_benchmark(m_manager, symbol("")),
        m_pinned_sorts(m),
        m_let("let"),
        m_flet("flet"),
        m_forall("forall"),
        m_exists("exists"),
        m_lblneg("lblneg"),
        m_lblpos("lblpos"),
        m_associative("assoc"),
        m_commutative("comm"),
        m_injective("injective"),
        m_sorts("sorts"),
        m_funs("funs"),
        m_preds("preds"),
        m_definition("definition"),
        m_axioms("axioms"),
        m_notes("notes"),
        m_theory("theory"),
        m_language("language"),
        m_extensions("extensions"),
        m_array("array"),
        m_bang("!"),
        m_underscore("_"),
        m_dt_plugin(0),
        m_dt_util(m),
        m_st(m),
        m_err(0),
        m_display_error_for_vs(false)
    {        
        family_id bfid = m_manager.get_basic_family_id();

        add_builtin_type("bool", bfid, BOOL_SORT);
        m_benchmark.get_symtable()->insert(symbol("Array"),  alloc(array_sort, m));
        m_benchmark.get_symtable()->insert(symbol("BitVec"), alloc(bv_sort, m));


        add_builtins(bfid);
    }

    ~smtparser() {
    }

    void set_error_stream(std::ostream& strm) { m_err = &strm; }

    std::ostream& get_err() { return m_err?(*m_err):std::cerr; }

    bool ignore_user_patterns() const { return m_ignore_user_patterns; }

    bool parse_stream(std::istream& stream) {
        proto_region region;
        scanner     scanner(stream, get_err(), false);
        proto_expr_parser parser(region, scanner, get_err());        
        return parse(parser);
    }

    bool parse_file(char const * filename) {
        timeit tt(get_verbosity_level() >= 100, "parsing file");
        if (filename != 0) {
            std::ifstream stream(filename);
            if (!stream) {
                get_err() << "ERROR: could not open file '" << filename << "'.\n";
                return false;
            }
            return parse_stream(stream);
        }
        else {
            return parse_stream(std::cin);
        }
    }

    bool parse_string(char const * str) {
        std::string s = str;
        std::istringstream is(s);
        return parse_stream(is);
    }

    bool parse_commands(Z3_context ctx, std::istream& is, std::ostream& os) {
        set_error_stream(os);
        cmd_context context(m_manager, ctx, is, os);
        set_error_stream(context.get_error_stream());
        proto_region             proto_region;
        scanner                  scanner(is, context.get_error_stream(), true);
        proto_expr_parser        parser(proto_region, scanner, context.get_error_stream());

        m_display_error_for_vs = Z3_get_parameters(ctx).m_display_error_for_vs;

        ptr_vector<proto_expr> exprs;
        while (!parser.at_eof()) {
            proto_region.reset();
            exprs.reset();
            if (!parser.parse(exprs, true)) {
                context.flush_errors();
                context.get_out().flush();
                break;
            }
            if (exprs.empty()) {
                break;
            }
            SASSERT(exprs.size() == 1);
            try {
                if (!process_command(context, exprs.back())) {
                    break;
                }
            }
            catch(cmd_exn(ex)) {
                context.flush_errors();
                context.get_out().flush();
                context.print_failure(Z3_get_error_msg(ex.get()), exprs.back());
            }
            context.flush_errors();
            context.get_out().flush();
        }
        return true;
    }

    void add_builtin_op(char const * s, family_id fid, decl_kind k) {
        m_builtin_ops.insert(symbol(s), builtin_op(fid, k));
    }

    void add_builtin_type(char const * s, family_id fid, decl_kind k) {
        m_builtin_sorts.insert(symbol(s), builtin_op(fid, k));
    }

    void initialize_smtlib() {

        if (!m_dt_plugin) {
            family_id fid = m_manager.get_family_id("datatype");
            if (!m_manager.has_plugin(fid)) {
                m_manager.register_plugin(fid, alloc(datatype_decl_plugin));
            }
            m_dt_plugin   = static_cast<datatype_decl_plugin*>(m_manager.get_plugin(fid));
        }

        smtlib::symtable* table = m_benchmark.get_symtable();

        symbol arith("arith");
        family_id afid = m_manager.get_family_id(arith);
        m_arith_fid = afid;

        add_builtin_type("Int", afid, INT_SORT);
        add_builtin_type("Real", afid, REAL_SORT);
        add_builtin_type("Bool", m_manager.get_basic_family_id(), BOOL_SORT);

        m_int_sort  = m_manager.mk_sort(m_arith_fid, INT_SORT);
        m_real_sort = m_manager.mk_sort(m_arith_fid, REAL_SORT);

        add_builtins(afid);
        
        symbol bv("bv");
        family_id bfid = m_manager.get_family_id(bv);
        m_bv_fid = bfid;        

        add_builtins(bfid);

        add_builtin_type("BitVec", bfid, BV_SORT);

        symbol array("array");
        afid = m_manager.get_family_id(array);
        m_array_fid = afid;

        add_builtins(afid);

        sort* a1, *a2;
        func_decl* store1, *sel1, *store2, *sel2;

        // Array
        parameter params0[2] = { parameter(m_int_sort), parameter(m_int_sort) };
        a1 = m_manager.mk_sort(afid, ARRAY_SORT, 2, params0);
        table->insert(symbol("Array"), a1);
        parameter param0(a1);
        sort * args0[3] = { a1, m_int_sort, m_int_sort };
        store1 = m_manager.mk_func_decl(afid, OP_STORE, 0, 0, 3, args0);
        table->insert(symbol("store"), store1);
        sel1 = m_manager.mk_func_decl(afid, OP_SELECT, 0, 0, 2, args0);
        table->insert(symbol("select"), sel1);

        // Array1
        parameter params1[2] = { parameter(m_int_sort), parameter(m_real_sort) };
        a1 = m_manager.mk_sort(afid, ARRAY_SORT, 2, params1);
        table->insert(symbol("Array1"), a1);
        parameter param1(a1);
        sort * args1[3] = { a1, m_int_sort, m_real_sort };
        store1 = m_manager.mk_func_decl(afid, OP_STORE, 0, 0, 3, args1);
        table->insert(symbol("store"), store1);
        sel1 = m_manager.mk_func_decl(afid, OP_SELECT, 0, 0, 2, args1);
        table->insert(symbol("select"), sel1);

        // Array2
        parameter params2[2] = { parameter(m_int_sort), parameter(a1) };
        a2 = m_manager.mk_sort(afid, ARRAY_SORT, 2, params2);
        table->insert(symbol("Array2"), a2);
        parameter param2(a2);
        sort * args2[3] = { a2, m_int_sort, a1 };
        store2 = m_manager.mk_func_decl(afid, OP_STORE, 0, 0, 3, args2);
        table->insert(symbol("store"), store2);
        sel2 = m_manager.mk_func_decl(afid, OP_SELECT, 0, 0, 2, args2);
        table->insert(symbol("select"), sel2);

        m_benchmark.declare_sort(symbol("U"));
        
        sort * bool_sort = m_manager.mk_bool_sort();
        m_sk_hack = m_manager.mk_func_decl(symbol("sk_hack"), 1, &bool_sort, bool_sort);
        table->insert(symbol("sk_hack"), m_sk_hack);
    }


    void add_builtins(family_id fid) {
        decl_plugin * plugin = m_manager.get_plugin(fid);
        SASSERT(plugin);
        svector<builtin_name> op_names;
        plugin->get_op_names(op_names);
        for (unsigned i = 0; i < op_names.size(); ++i) {
            add_builtin_op(op_names[i].m_name.bare_str(), fid, op_names[i].m_kind);
        }
    }

    smtlib::benchmark* get_benchmark() { return &m_benchmark; }

private:


    bool parse(proto_expr_parser& parser) {
        symbol benchmark("benchmark");
        symbol name("");
        proto_expr* const* rest = 0;
        ptr_vector<proto_expr> proto_exprs;
        bool result = parser.parse(proto_exprs);
        proto_expr* proto_expr = 0;

        if (!result) {
            get_err() << "ERROR: parse error at line " << parser.get_line() << ".\n";
        }

        for (unsigned i = 0; result && i < proto_exprs.size(); ++i) {

            proto_expr = proto_exprs[i];

            if (match_cons(proto_expr, benchmark, name, rest)) {        
                result = make_benchmark(name, rest);
            }
            else if (proto_expr && proto_expr->kind() != proto_expr::COMMENT) {
                set_error("could not match expression to benchmark ", proto_expr);
            }
            else {
                // proto_expr->kind() == proto_expr::COMMENT.
            }
        }
        return result;
    }

    void error_prefix(proto_expr* e) {
        if (m_display_error_for_vs) {
            if (e) {
                get_err() << "Z3(" << e->line() << "," << e->pos() << "): ERROR: ";
            }            
        }
        else {
            get_err() << "ERROR: ";
            if (e) {
                get_err() << "line " << e->line() << " column " << e->pos() << ": ";
            }
        }
    }
    
    void set_error(char const * str, proto_expr* e) {
        error_prefix(e);
        if (e->kind() == proto_expr::ID) {
            get_err() << str << " '" << e->string() << "'.\n";
        }
        else {
            get_err() << str << ".\n";
        }
    }

    template<typename T1, typename T2>
    void set_error(T1 str1, T2 str2, proto_expr* e) {
        error_prefix(e);
        get_err() << str1 << " " << str2 << ".\n";
    }

    template<typename T1, typename T2, typename T3>
    void set_error(T1 str1, T2 str2, T3 str3, proto_expr* e) {
        error_prefix(e);
        get_err() << str1 << str2 << str3 << ".\n";
    }

    bool match_cons(proto_expr * e, symbol const & sym, symbol & name, proto_expr* const*& proto_exprs) {
        if (e && 
            e->kind() == proto_expr::CONS && 
            e->children() && 
            e->children()[0] &&
            e->children()[0]->string() == sym &&
            e->children()[1]) {
            proto_exprs = e->children() + 2;
            name  = e->children()[1]->string();
            return true;
        }

        return false;
    }

    bool make_benchmark(symbol & name, proto_expr * const* proto_exprs) {
        symbol extrasorts("extrasorts");
        symbol extrafuns("extrafuns");
        symbol extrapreds("extrapreds");
        symbol datatypes("datatypes");
        symbol unify("unify");
        symbol unify_fail("unify-fail");
#if    !defined(SMTCOMP) && !defined(_EXTERNAL_RELEASE)
        symbol kbo_lt("kbo_lt");
        symbol kbo_gt("kbo_gt");
        symbol kbo_eq("kbo_eq");
        symbol kbo_un("kbo_un");
        symbol lpo_lt("lpo_lt");
        symbol lpo_gt("lpo_gt");
        symbol lpo_eq("lpo_eq");
        symbol lpo_un("lpo_un");
        symbol st_insert("st_insert");
        symbol st_erase("st_erase");
        symbol st_reset("st_reset");
        symbol st_unify("st_unify");
        symbol st_inst("st_inst");
        symbol st_gen("st_gen");
        symbol st_display("st_display");
#endif
        symbol assumption("assumption");
        symbol assumption_core("assumption-core");
        symbol define_sorts_sym("define_sorts");
        symbol logic("logic");
        symbol formula("formula");
        symbol status("status");
        symbol sat("sat");
        symbol unsat("unsat");
        symbol unknown("unknown");
        symbol empty("");
        symbol source("source");
        symbol difficulty("difficulty");
        symbol category("category");
        bool   success = true;
        
        push_benchmark(name);
        
        while (proto_exprs && *proto_exprs) {
            proto_expr* e = *proto_exprs;
            ++proto_exprs;
            proto_expr* e1 = *proto_exprs;

            if (logic == e->string() && e1) {
                name = e1->string();
                m_benchmark.set_logic(name);

                set_default_num_sort(name);               

                if (name == symbol("QF_AX")) {
                    // Hack for supporting new QF_AX theory...
                    sort * index   = m_manager.mk_sort(symbol("Index"));
                    sort * element = m_manager.mk_sort(symbol("Element"));
                    parameter params[2] = { parameter(index), parameter(element) };
                    sort * array   = m_manager.mk_sort(m_array_fid, ARRAY_SORT, 2, params);
                    smtlib::symtable* table = m_benchmark.get_symtable();
                    table->insert(symbol("Index"), index);
                    table->insert(symbol("Element"), element);
                    // overwrite Array definition...
                    table->insert(symbol("Array"), array);
                    sort * args[3] = { array, index, element };
                    func_decl * store = m_manager.mk_func_decl(m_array_fid, OP_STORE, 0, 0, 3, args);
                    table->insert(symbol("store"), store);
                    func_decl * sel   = m_manager.mk_func_decl(m_array_fid, OP_SELECT, 0, 0, 2, args);
                    table->insert(symbol("select"), sel);
                }

                ++proto_exprs;
                continue;
            }

            if (assumption == e->string() && e1) {
                expr_ref t(m_manager);
                if (!make_expression(e1, t) ||
                    !push_assumption(t.get())) {                    
                    return false;
                }
                ++proto_exprs;
                continue;
            }

            if (assumption_core == e->string() && e1) {
                expr_ref t(m_manager);
                if (!make_expression(e1, t))
                    return false;
                m_benchmark.add_assumption(t.get());
                ++proto_exprs;
                continue;
            }

            if (define_sorts_sym == e->string() && e1) {
                if (!define_sorts(e1)) {
                    return false;
                }                
                ++proto_exprs;
                continue;
            }

            if (formula == e->string() && e1) {
                expr_ref t(m_manager);
                if (!make_expression(e1, t) ||
                    !push_formula(t.get())) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }

            if (status == e->string() && e1) {
                if (sat == e1->string()) {
                    if (!push_status(smtlib::benchmark::SAT)) {
                        set_error("could not push status ", e1->string(),e1);
                        return false;
                    }
                }
                else if (unsat == e1->string()) {
                    if (!push_status(smtlib::benchmark::UNSAT)) {
                        set_error("could not push status ", e1->string(),e1);
                        return false;
                    }
                }
                else if (unknown == e1->string()) {
                    if (!push_status(smtlib::benchmark::UNKNOWN)) {
                        set_error("could not push status ", e1->string(),e1);
                        return false;
                    }
                }
                else {
                    set_error("could not recognize status ", e1->string(),e1);
                    return false;
                }
                ++proto_exprs;
                continue;
            }

            if (extrasorts == e->string() && e1) {
                if (!declare_sorts(e1)) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if (extrafuns == e->string() && e1) {
                if (!declare_funs(e1)) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if (extrapreds == e->string() && e1) {
                if (!declare_preds(e1)) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if (datatypes == e->string() && e1) {
                if (!declare_datatypes(e1)) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if ((unify == e->string() || unify_fail == e->string()) && e1) {
                if (!test_unify(e1, unify == e->string())) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
#if    !defined(SMTCOMP) && !defined(_EXTERNAL_RELEASE)
            if ((kbo_lt == e->string() || kbo_gt == e->string() || kbo_eq == e->string() || kbo_un == e->string()) && e1) {
                if (!test_kbo(e1, e->string())) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if ((lpo_lt == e->string() || lpo_gt == e->string() || lpo_eq == e->string() || lpo_un == e->string()) && e1) {
                if (!test_lpo(e1, e->string())) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if ((st_insert == e->string() || st_erase == e->string()) && e1) {
                if (!test_st(e1, e->string())) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if ((st_unify == e->string() || st_inst == e->string() || st_gen == e->string()) && e1) {
                if (!test_st_visit(e1, e->string())) {
                    return false;
                }
                ++proto_exprs;
                continue;
            }
            if (st_reset == e->string()) {
                m_st.reset();
                ++proto_exprs;
                continue;
            }
            if (st_display == e->string()) {
                m_st.display(std::cout);
                ++proto_exprs;
                continue;
            }
#endif
            if (m_notes == e->string() && e1) {
                ++proto_exprs;
                continue;
            }            

            if ((source == e->string() || difficulty == e->string() || category == e->string()) && e1) {
                ++proto_exprs;
                continue;
            }
            
            if (e->string() != empty) {
                set_error("ignoring unknown attribute '", e->string().bare_str(), "'", e);
                if (e1) {
                    ++proto_exprs;
                }
                // do not fail.
                // success = false;
                continue;
            }

            TRACE("smtparser",
                  tout  << "skipping: " << e->string() << " " <<
                  e->line() << " " << 
                  e->pos() << ".\n";);
            continue;            
        }    
        return success;
    }

    bool is_id_token(proto_expr* expr) {
        return 
            expr && 
            (expr->kind() == proto_expr::ID || 
             expr->kind() == proto_expr::STRING ||
             expr->kind() == proto_expr::ANNOTATION);
    }
                
    smt_cmd_token get_command_token(cmd_context& ctx, proto_expr* expr) {
        if (!expr) {
            return SMT_CMD_ERROR;
        }
        if (!is_id_token(expr)) {
            return SMT_CMD_ERROR;
        }
        return ctx.string2token(expr->string().bare_str());            
    }
    
    bool process_command(cmd_context& cmd_ctx, proto_expr* p_expr) {
        proto_expr* const* chs = p_expr->children();
        proto_expr* e0 = chs?chs[0]:0;
        proto_expr* e1 = e0?chs[1]:0;
        std::ostream& out = cmd_ctx.get_out();
        Z3_context ctx = cmd_ctx.get_context();

        smt_cmd_token cmd_tok;
        if (p_expr->kind() == proto_expr::ID) {
            cmd_tok = get_command_token(cmd_ctx, p_expr);
        }
        else {
            cmd_tok = get_command_token(cmd_ctx, e0);
        }

        switch(cmd_tok) {
        case SMT_CMD_SET_LOGIC:
            if (!check_id(e1)) {
                cmd_ctx.print_failure("logic identifier expected as argument to logic", p_expr);
                break;
            }
            if (Z3_set_logic(ctx, e1->string().bare_str())) { 
                // m_smtlib_logic param is only used for pretty printing.
                Z3_get_parameters(ctx).m_smtlib_logic = e1->string().bare_str();
                set_default_num_sort(e1->string());
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("failed to set logic", p_expr);
            }
            break;
        case SMT_CMD_DECLARE_SORTS:
            if (!check_valid(cmd_ctx, p_expr, e1, "sort declaration expects an argument")) {
                break;
            }            
            if (e0 && e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (declare_sorts(e1)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse sort declaration", p_expr);
            }
            break;
        case SMT_CMD_DECLARE_FUNS:         // func-decls
            if (!check_valid(cmd_ctx, p_expr, e1, "function declaration expects an argument")) {
                break;
            }
            if (e0 && e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (declare_funs(e1)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse function declaration", p_expr);
            }
            break;
        case SMT_CMD_DECLARE_PREDS:        // pred-decls
            if (!check_valid(cmd_ctx, p_expr, e1, "predicate declaration expects an argument")) {
                break;
            }
            if (e0 && e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (declare_preds(e1)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse predicate declaration", p_expr);
            }
            break;
        case SMT_CMD_DECLARE_DATATYPES:
            if (!check_valid(cmd_ctx, p_expr, e1, "data-type declaration expects an argument")) {
                break;
            }
            if (e0 && e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (declare_datatypes(e1)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse data-type declaration", p_expr);
            }
            break;
        case SMT_CMD_DEFINE: {
            expr_ref macro_expr(m_manager);
            if (define_macro(cmd_ctx.get_table(), cmd_ctx.get_region(), p_expr, macro_expr)) {
                cmd_ctx.add_trail(macro_expr);
                cmd_ctx.print_success();
            }
            break;
        }           
        case SMT_CMD_DEFINE_SORTS: {
            if (!check_valid(cmd_ctx, p_expr, e1, "sort definition expects an argument")) {
                break;
            }
            if (e0 && e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (define_sorts(e1)) {
                cmd_ctx.print_success();
            }
            break;
        }
        case SMT_CMD_DECLARE_SORT: { // <symbol> <numeral>
            if (!check_id(e1)) {
                cmd_ctx.print_failure("identifier argument expected", p_expr);
                break;

            }
            unsigned num_args = cmd_ctx.parse_opt_numeral(chs[2], 0);
            if (e0 && e1 && chs[2] && chs[3]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            m_benchmark.get_symtable()->insert(e1->string(), alloc(user_sort, m_manager, num_args, e1->string()));
            cmd_ctx.print_success();            
            
            break;
        }
        case SMT_CMD_DEFINE_SORT: { // <symbol> (<symbol>*) <sort>
            if (!check_id(e1)) {
                cmd_ctx.print_failure("sort definition expects three arguments", p_expr);
                break;
            }
            proto_expr* e2 = chs[2];
            if (!check_valid(cmd_ctx, p_expr, e2, "sort definition expects three arguments")) {
                break;
            }
            proto_expr* e3 = chs[3];
            if (!check_valid(cmd_ctx, p_expr, e3, "sort definition expects three arguments")) {
                break;
            }
            if (chs[4]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (define_sort(e1, e2, e3)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse sort definition", p_expr);
            }
            break;
        }
        case SMT_CMD_DECLARE_FUN: { // <symbol> (<sort>*) <sort>
            if (!check_id(e1)) {
                cmd_ctx.print_failure("function declaration expects three arguments", p_expr);
                break;
            }
            proto_expr* e2 = chs[2];
            if (!check_valid(cmd_ctx, p_expr, e2, "function declaration expects three arguments")) {
                break;
            }
            proto_expr* e3 = chs[3];
            if (!check_valid(cmd_ctx, p_expr, e3, "function declaration expects three arguments")) {
                break;
            }
            if (chs[4]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (declare_fun(e1,e2,e3)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse function declaration", p_expr);
            }
            break;
        }
        case SMT_CMD_DECLARE_CONST: { // <symbol> <sort>
            if (!check_id(e1)) {
                cmd_ctx.print_failure("constant declaration expects two arguments", p_expr);
                break;
            }
            proto_expr* e2 = chs[2];
            if (!check_valid(cmd_ctx, p_expr, e2, "constant declaration expects two arguments")) {
                break;
            }
            if (chs[3]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            if (declare_fun(e1, 0, e2)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse constant declaration", p_expr);
            }
            break;
        }
        case SMT_CMD_DEFINE_FUN: { // <symbol> (<sorted_var>*) <sort> <term>
            if (!check_id(e1)) {
                cmd_ctx.print_failure("function definition expects four arguments", p_expr);
                break;
            }
            proto_expr* e2 = chs[2];
            if (!check_valid(cmd_ctx, p_expr, e2, "function definition expects four arguments")) {
                break;
            }
            proto_expr* e3 = chs[3];
            if (!check_valid(cmd_ctx, p_expr, e3, "function definition expects four arguments")) {
                break;
            }
            proto_expr* e4 = chs[4];
            if (!check_valid(cmd_ctx, p_expr, e4, "function definition expects four arguments")) {
                break;
            }
            if (chs[5]) {
                cmd_ctx.print_failure("too many arguments passed to declaration", p_expr);
            }
            expr_ref macro_expr(m_manager);
            if (define_fun(cmd_ctx.get_table(), cmd_ctx.get_region(), e1, e2, e3, e4, macro_expr)) {
                cmd_ctx.add_trail(macro_expr);
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_failure("could not parse function definition", p_expr);
            }
            break;
        }
        case SMT_CMD_GET_VALUE: { // (<term>+)
            if (!check_valid(cmd_ctx, p_expr, e1, "get-value expects a list arguments")) {
                break;
            }
            proto_expr* const* children = e1->children();
            expr_ref_vector exprs(m_manager);
            
            while (children && children[0]) {
                expr_ref e(m_manager);
                if (!get_expression(cmd_ctx, cmd_ctx.get_table(), p_expr, children[0], e, "one expression expected to eval")) {
                    break;
                }
                exprs.push_back(e);
                ++children;
            }
            cmd_ctx.eval(out, p_expr, exprs.size(), exprs.c_ptr());
            break;
        }
        case SMT_CMD_PUSH: {               // numeral
            unsigned num_scopes = cmd_ctx.parse_opt_numeral(e1, 1);
            cmd_ctx.push(num_scopes);
            cmd_ctx.print_success();
            if (e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to command", p_expr);
            }
            break;
        }
        case SMT_CMD_POP: {                 // numeral
            unsigned num_scopes = cmd_ctx.parse_opt_numeral(e1, 1);
            cmd_ctx.pop(num_scopes);
            cmd_ctx.print_success();
            if (e1 && chs[2]) {
                cmd_ctx.print_failure("too many arguments passed to command", p_expr);
            }
            break;
        }
        case SMT_CMD_ASSERT: {              // expr+
            expr_ref_vector exprs(m_manager);
            if (!chs) {
                cmd_ctx.print_failure("expecting list of arguments", p_expr);
                break;
            }
            if (!(*chs)) {
                cmd_ctx.print_success();
                break;
            }
            ++chs;
            if (!make_bool_expressions(cmd_ctx.get_table(), chs, exprs)) {
                if (!cmd_ctx.has_error()) {
                    cmd_ctx.print_failure("could not parse expression", *chs);
                }
                return true;
            }
            for (unsigned i = 0; i < exprs.size(); ++i) {
                cmd_ctx.add_asserted(exprs[i].get());
            }            
            cmd_ctx.print_success();
            break;
        }
        case SMT_CMD_CHECK_SAT: {          // boolean-constants*
            if (!chs || !(*chs)) {
                cmd_ctx.check_sat(out);
            }
            else {
                ++chs;
                if (!chs || !(*chs)) {
                    cmd_ctx.check_sat(out);
                }
                else {
                    expr_ref_vector exprs(m_manager);
                    if (!make_bool_expressions(cmd_ctx.get_table(), chs, exprs)) {
                        if (!cmd_ctx.has_error()) {
                            cmd_ctx.print_failure("could not parse expression", *chs);
                        }
                        return true;
                    }
                    cmd_ctx.get_core(p_expr, out, exprs.size(), exprs.c_ptr(), false);
                }
            }
            break;
        }
        case SMT_CMD_GET_CORE: {  // boolean-constants+
            expr_ref_vector exprs(m_manager);
            if (!chs) {
                cmd_ctx.print_failure("expecting list of arguments", p_expr);
                break;
            }
            if (!(*chs)) {
                cmd_ctx.print_success();
                break;
            }
            ++chs;
            if (!make_bool_expressions(cmd_ctx.get_table(), chs, exprs)) {
                if (!cmd_ctx.has_error()) {
                    cmd_ctx.print_failure("could not parse expression", *chs);
                }
                return true;
            }
            cmd_ctx.get_core(p_expr, out, exprs.size(), exprs.c_ptr(), true); // just get the core
            break;
        }
        case SMT_CMD_NEXT_SAT: {          // <no arguments>
            cmd_ctx.next_sat(out);
            break;
        }
        case SMT_CMD_SIMPLIFY: {
            expr_ref e(m_manager);
            if (!get_expression(cmd_ctx, cmd_ctx.get_table(), p_expr, e1, e, "one expression expected to simplify")) {
                break;
            }
            cmd_context::scoped_stopwatch stopw(cmd_ctx);
            Z3_ast result = Z3_simplify(ctx, reinterpret_cast<Z3_ast>(e.get()));
            out << Z3_ast_to_string(ctx, result) << "\n";
            break;
        }
        case SMT_CMD_GET_IMPLIED_EQUALITIES: {
            expr_ref_vector exprs(m_manager);
            expr_ref e(m_manager);
            if (!chs || !(*chs)) {
                cmd_ctx.print_failure("expecting list of arguments", p_expr);
                break;
            }
            ++chs;
            bool ok = true;
            while (*chs) {
                if (!get_expression(cmd_ctx, cmd_ctx.get_table(), p_expr, *chs, e, "list of expressions expected")) {
                    ok = false;
                    break;
                }
                exprs.push_back(e);
                ++chs;
            }
            if (!ok) {
                break;
            }
            cmd_context::scoped_stopwatch stopw(cmd_ctx);
            cmd_ctx.get_implied_equalities(out, exprs.size(), exprs.c_ptr());
            break;
        }
        case SMT_CMD_EVAL: {
            expr_ref e(m_manager);
            if (!get_expression(cmd_ctx, cmd_ctx.get_table(), p_expr, e1, e, "one expression expected to eval")) {
                break;
            }
            cmd_ctx.eval(out, p_expr, e);
            break;
        }
        case SMT_CMD_GET_ASSERTIONS:  {  // string
            scoped_stream strm(e1, out);
            cmd_ctx.get_assertions(*strm);
            break;
        }
        case SMT_CMD_GET_SAT_ASSERTIONS: {  // string          
            scoped_stream strm(e1, out);
            cmd_ctx.get_sat_assertions(out);
            break;
        }
        case SMT_CMD_KEEP_SAT_ASSERTIONS:  { // 
            Z3_ast assignment = Z3_get_context_assignment(ctx);
            cmd_ctx.add_asserted(reinterpret_cast<expr*>(assignment));
            cmd_ctx.print_success();
            break;
        }
        case SMT_CMD_GET_UNSAT_CORE: {      // string
            scoped_stream strm(e1, out);
            cmd_ctx.get_unsat_core(out, p_expr);
            break;
        }
        case SMT_CMD_GET_PROOF:  {          // string
            scoped_stream strm(e1, out);
            cmd_ctx.get_proof(*strm, p_expr);
            break;
        }
        case SMT_CMD_SET_OPTION: {         // string strings
            if (!e1) {
                cmd_ctx.set_option_help(out, "");
                break;
            }
            if (cmd_ctx.set_option(get_command_token(cmd_ctx,e1), chs+2)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_unsupported();
            }
            break;
        }
        case SMT_CMD_SET_INFO: {
            if (!e1) {
                cmd_ctx.set_option_help(out, "");
                break;
            }
            if (cmd_ctx.set_info(e1, chs+2)) {
                cmd_ctx.print_success();
            }
            else {
                cmd_ctx.print_unsupported();
            }
            break;            
        }
        case SMT_CMD_GET_INFO: {           // string+
            if (!e1) {
                cmd_ctx.get_info_help(out, "");
                break;
            }
            ++chs;
            SASSERT(e1 == *chs);
            out << "(";
            while(*chs) {
                if (!get_info(cmd_ctx, get_command_token(cmd_ctx,*chs))) {
                    out << ":" << chs[0]->string() << " \"unsupported\"";
                }
                ++chs;
                if (*chs) {
                    out << "\n";
                }
            }
            out << ")\n";
            break;
        }
        case SMT_CMD_ECHO: {           // string+
            if (!e1) {
                cmd_ctx.get_info_help(out, "");
                break;
            }
            ++chs;
            SASSERT(e1 == *chs);
            while(*chs) {
                out << chs[0]->string() << "\n";
                ++chs;
            }
            break;
        }
        case SMT_CMD_EXIT:                 // <no arguments>
            return false;
        case SMT_CMD_ERROR:                // error token 
            cmd_ctx.print_failure("unrecognized command", p_expr);
            break;        
        default:
            if (get_info(cmd_ctx, cmd_tok)) {
                out << "\n";
                break;
            }
            if (cmd_ctx.get_command_help(out, cmd_tok)) {
                out << "\n";
                break;
            }
            cmd_ctx.print_failure("this is not a top-level command", p_expr);
            break;
        }
        return true;
    }

    void flatten_exprs(expr_ref_vector& exprs) {
        for (unsigned i = 0; i < exprs.size(); ++i) {
            expr* e = exprs[i].get();
            if (m_manager.is_and(e)) {
                for (unsigned j = 1; j < to_app(e)->get_num_args(); ++j) {
                    exprs.push_back(to_app(e)->get_arg(j));
                }
                exprs[i] = to_app(e)->get_arg(0);
                --i;
                continue;
            }
            if (m_manager.is_not(e) &&
                m_manager.is_or(to_app(e)->get_arg(0))) {
                e = to_app(e)->get_arg(0);
                app* a = to_app(e);
                for (unsigned j = 1; j < a->get_num_args(); ++j) {
                    e = a->get_arg(j);
                    if (m_manager.is_not(e)) {
                        exprs.push_back(to_app(e)->get_arg(0));
                    }
                    else {
                        exprs.push_back(m_manager.mk_not(e));
                    }
                }
                e = a->get_arg(0);
                if (m_manager.is_not(e)) {
                    exprs[i] = to_app(e)->get_arg(0);
                }
                else {
                    exprs[i] = m_manager.mk_not(e);
                }
                --i;
                continue;
            }
        }
    }


    bool get_info(cmd_context& cmd_ctx, smt_cmd_token cmd_tok) {
        return cmd_ctx.get_info(cmd_tok);
    }

    bool get_expression(cmd_context& cmd_ctx, symbol_table<idbuilder*>& table, proto_expr* p_expr, proto_expr* e1, expr_ref& e, char const* msg) {
        if (!check_valid(cmd_ctx, p_expr, e1, msg)) {
            return false;
        }
        m_binding_level = 0;
        if (!make_expression(table, e1, e)) {
            return false;
        }            
        return true;
    }


    bool check_valid(cmd_context& cmd_ctx, proto_expr* p_expr, proto_expr* e, char const* msg) {
        if (e == 0) {
            cmd_ctx.print_failure(msg, p_expr);
        }
        return (e != 0);
    }

    bool check_id(proto_expr* e) {
        return is_id_token(e);
    }    

    bool make_expression(proto_expr * e, expr_ref & result) {
        m_binding_level = 0;
        symbol_table<idbuilder*> local_scope;
        return make_expression(local_scope, e, result);
    }

    bool make_func_decl(proto_expr* e, func_decl_ref& result) {
        func_decl* f;
        if (m_benchmark.get_symtable()->find1(e->string(), f)) {
            result = f;
            return true;
        }
        else {
            return false;
        }
    }

    bool make_bool_expression(symbol_table<idbuilder*>& local_scope, proto_expr * e, expr_ref & result) {
        if (!make_expression(local_scope, e, result)) {
            return false;
        }
        if (!m_manager.is_bool(result)) {
            set_error("expecting Boolean expression", e);
            return false;
        }
        return true;
    }

    bool make_bool_expressions(symbol_table<idbuilder*>& local_scope, proto_expr * const* chs, expr_ref_vector & exprs) {
        while (chs && *chs) {
            expr_ref result(m_manager);            
            m_binding_level = 0;
            if (!make_bool_expression(local_scope, *chs, result)) {
                return false;
            }
            exprs.push_back(result);
            ++chs;
        }
        return true;
    }

    bool make_expression(symbol_table<idbuilder*>& local_scope, proto_expr * e, expr_ref & result) {
        // 
        // Walk proto_expr by using the zipper. 
        // That is, maintain a stack of what's 
        // . left  - already processed.
        // . right - to be processed.
        // . up    - above the processed node.
        //

        region                  region;

        expr_ref_vector *       left = alloc(expr_ref_vector, m_manager);
        proto_expr* const*      right = 0;
        ptr_vector<parse_frame> up;
        proto_expr*             current = e;
        bool                    success = false;
        idbuilder*              builder = 0;
        
        while (true) {

            if (!current && right && *right) {
                //
                // pull the current from right.
                //
                current = *right;
                ++right;
            }

            if (!current && up.empty()) {
                //
                // we are done.
                //
                if (left->size() == 0) {
                    // set_error();
                    set_error("there are no expressions to return", e);
                    goto cleanup;
                }
                if (left->size() != 1) {
                    set_error("there are too many expressions to return", e);
                    goto cleanup;
                }
                result = left->back();
                success = true;
                goto cleanup;
            }
            
            if (!current && !up.empty()) {
                //
                // There is nothing more to process at this level.
                //
                // Apply the operator on the stack to the 
                // current 'left' vector. 
                // Adjust the stack by popping the left and right 
                // work-lists.
                // 
                expr_ref term(m_manager);
                parse_frame* above = up.back();
                // symbol sym = above->get_proto_expr()->string();

                if (above->make_term()) {
                    if (!above->make_term()->apply(*left, term)) {
                        set_error("Could not create application", 
                                  above->get_proto_expr());
                        success = false;
                        goto cleanup;
                    }
                }
                else if (!make_app(above->get_proto_expr(), *left, term)) {
                    success = false;
                    goto cleanup;
                }
                dealloc(left);
                left = above->detach_left();
                left->push_back(term.get());
                right = above->right();
                m_binding_level = above->binding_level();
                up.pop_back();                
                continue;
            }

            while (current && 
                   current->kind() == proto_expr::CONS && 
                   current->children() && 
                   current->children()[0] && 
                   !current->children()[1]) {
                current = current->children()[0];
            }

            switch(current->kind()) {

            case proto_expr::ANNOTATION:
                // ignore
                current = 0;
                break;

            case proto_expr::ID: {                
                symbol const& id = current->string();
                expr_ref term(m_manager);
                expr * const_term = 0;
                bool ok = true;

                if (local_scope.find(id, builder)) {
                    expr_ref_vector tmp(m_manager);
                    if (!builder->apply(tmp, term)) {
                        set_error("identifier supplied with the wrong number of arguments ", id, current);
                        goto cleanup;

                    }
                }
                else if (m_benchmark.get_const(id, const_term)) {
                    // found.
                    term = const_term;
                }
                else if (is_builtin_const(id, current, current->num_params(), current->params(), ok, term)) {
                    if (!ok) goto cleanup;
                }
                else if (is_bvconst(id, current->num_params(), current->params(), term)) {
                    // found
                }
                else {
                    set_error("could not locate id ", id, current);
                    goto cleanup;
                } 

                left->push_back(term.get());
                current = 0;
                break;
            }                                

            case proto_expr::STRING:
                // 
                // Ignore strings.
                //
                current = 0;
                break;

            case proto_expr::COMMENT:
                // 
                // Ignore comments.
                //
                current = 0;
                break;

            case proto_expr::INT:

                left->push_back(mk_number(current->number(), true));
                current = 0;
                break;

            case proto_expr::FLOAT:
                left->push_back(mk_number(current->number(), false));
                current = 0;
                break;

            case proto_expr::CONS:

                if (!current->children() ||
                    !current->children()[0]) {                    
                    set_error("cons does not have children", current);
                    current = 0;
                    goto cleanup;
                }

                //
                // expect the head to be a symbol
                // which can be used to build a term of
                // the subterms.
                //

                symbol const& head_symbol = current->children()[0]->string();

                if (head_symbol == m_underscore) {
                    
                    expr_ref term(m_manager);

                    proto_expr * const* chs = current->children() + 1;
                    symbol const& id = chs[0]->string();
                    sort_ref_vector sorts(m_manager);
                    vector<parameter> params;
                    bool ok = true;
                    if (!parse_params(chs+1, params, sorts)) {
                        goto cleanup;
                    }
                    if (is_builtin_const(id, current, params.size(), params.c_ptr(), ok, term)) {
                        if (!ok) goto cleanup;
                    }
                    else if (is_bvconst(id, params.size(), params.c_ptr(), term)) {
                        // ok
                    }
                    else {
                        set_error("Could not parse _ term", current);
                        goto cleanup;
                    }
                    left->push_back(term.get());
                    current = 0;
                    break;                    
                }

                if ((head_symbol == m_let) ||
                    (head_symbol == m_flet)) {

                    if (!current->children()[1] ||
                        !current->children()[2]) {
                        set_error("let does not have two arguments", current);
                        goto cleanup;
                    }

                    proto_expr * let_binding = current->children()[1];
                    proto_expr * const* let_body = current->children()+2;                    

                    //
                    // Collect bound variables and definitions for the bound variables
                    // into vectors 'vars' and 'bound'.
                    // 
                    svector<symbol>         vars;
                    ptr_vector<proto_expr> bound_vec;
                    if (is_binary_let_binding(let_binding)) {
                        vars.push_back(let_binding->children()[0]->string());
                        bound_vec.push_back(let_binding->children()[1]);
                    }
                    else {
                        proto_expr* const* children = let_binding->children();
                        if (!children) {
                            set_error("let binding does not have two arguments", let_binding);
                            goto cleanup;
                        }
                        while (*children) {
                            proto_expr* ch = *children;
                            if (!is_binary_let_binding(ch)) {
                                set_error("let binding does not have two arguments", ch);
                                goto cleanup;
                            }
                            vars.push_back(ch->children()[0]->string());
                            bound_vec.push_back(ch->children()[1]);
                            ++children;
                        }
                    }
                    bound_vec.push_back(0);

                    proto_expr** bound = new (region) proto_expr*[bound_vec.size()];
                    for (unsigned i = 0; i < bound_vec.size(); ++i) {
                        bound[i] = bound_vec[i];
                    }

                    //
                    // Let's justify the transformation that
                    // pushes push_let and pop_let on the stack.
                    // and how it processes the let declaration.
                    //
                    //     walk up left ((let ((v1 x1) (v2 x2)) z)::right)
                    //
                    //  =
                    //
                    //     walk (up::(pop_let(),left,right)::(bind(v1,v2),[],[z])) [] [x1;x2] 
                    //
                    //  =  (* assume x1 -> y1, x2 -> y2 *)
                    //
                    //     walk (up::(pop_let(),left,right)::(bind(v1,v2),[],[z])) [y1;y2] []
                    //
                    //  =  (* apply binding *)
                    // 
                    //     walk (up::(pop_let(),left,right)) [] [z]
                    //
                    //  =  (* assume z -> u *)
                    //
                    //     walk up {left::u] right
                    //
                    // so if pop_let(v) [a,b] has the effect of removing v from the environment
                    // and projecting the second element "b", we obtain the effect of a let-binding.
                    //

                    expr_ref_vector * pinned = alloc(expr_ref_vector, m_manager);
                    pop_let  * popl  = new (region) pop_let(local_scope, pinned);
                    up.push_back(new (region) parse_frame(let_binding, popl, left, right, m_binding_level));


                    push_let_and * pushl = new (region) push_let_and(this, region, local_scope, pinned, vars.size(), vars.c_ptr());                    
                    expr_ref_vector * tmp = alloc(expr_ref_vector, m_manager);
                    up.push_back(new (region) parse_frame(let_binding, pushl, tmp, let_body, m_binding_level));
                    

                    left  = alloc(expr_ref_vector, m_manager);
                    right = bound;
                    current = 0;
                    break;
                }

                if (head_symbol == m_lblneg ||
                    head_symbol == m_lblpos) {
                    if (!current->children()[1] ||
                        !current->children()[2]) {                        
                        set_error("labels require two arguments", current);
                        goto cleanup;
                    }
                    
                    bool is_pos = head_symbol == m_lblpos;
                    idbuilder* lbl = new (region) build_label(this, is_pos, current->children()[1]);
                                                           
                    up.push_back(new (region) parse_frame(current, lbl, left, right, m_binding_level));

                    //
                    // process the body.
                    // 
                    left  = alloc(expr_ref_vector, m_manager);
                    right   = 0;
                    current = current->children()[2];                    
                    break;
                }

                if (head_symbol == m_bang) {
                    proto_expr* const* children = current->children();
                    proto_expr*        body     = children[1];
                    proto_expr*        lblname  = 0;
                    bool               is_pos   = false;

                    children += 2;

                    while (children[0] && 
                           children[0]->kind() == proto_expr::ANNOTATION &&
                           children[1]) {
                        symbol id = children[0]->string();

                        if ((id == m_lblneg) ||
                            (id == m_lblpos)) {
                            is_pos = id == m_lblpos;
                            lblname = children[1];
                        }

                        children += 2;
                    }

                    if (lblname) {
                        idbuilder* lbl = new (region) build_label(this, is_pos, lblname);
                        up.push_back(new (region) parse_frame(current, lbl, left, right, m_binding_level));
                        left    = alloc(expr_ref_vector, m_manager);
                        right   = 0;
                    }

                    //
                    // process the body.
                    // 
                    current = body;
                    break;
                }
                
                if ((head_symbol == m_forall) ||
                    (head_symbol == m_exists)) {
                    
                    expr_ref_buffer     patterns(m_manager);
                    expr_ref_buffer     no_patterns(m_manager);
                    sort_ref_buffer     sorts(m_manager);
                    svector<symbol>     vars;
                    int weight = 1;

                    proto_expr* const* children = current->children();
                    proto_expr*  body = 0;

                    ++children;
                    
                    if (!children[0] || !children[1]) {
                        set_error("quantifier should have at least two arguments", current);
                        goto cleanup;
                    }

                    //
                    // restore 'left' and 'right' working set and m_binding_level.
                    //
                    up.push_back(new (region) parse_frame(current, new (region) identity(), left, right, m_binding_level));
                    left  = alloc(expr_ref_vector, m_manager);

                    //
                    // declare the bound variables.
                    // 

                    local_scope.begin_scope();

                    while (children[0] && children[1] && 
                           (children[1]->kind() != proto_expr::ANNOTATION)) {

                        if (!parse_bound(local_scope, region, *children, vars, sorts)) {
                            goto cleanup;
                        }
                        ++children;
                    }
                    
                    body = children[0];

                    if (is_annotated_cons(body)) {
                        children = body->children()+1;
                        body = body->children()[1];                        
                    }

                    ++children;

                    symbol qid  = symbol(current->line());
                    symbol skid = symbol();

                    read_patterns(vars.size(), local_scope, children, patterns, no_patterns, weight, qid, skid);

                    //
                    // push a parse_frame to undo the scope of the quantifier.
                    //                     

                    SASSERT(sorts.size() > 0);

                    idbuilder* pop_q = new (region) pop_quantifier(this, (head_symbol == m_forall), weight, qid, skid, patterns, no_patterns, sorts, vars, local_scope, current);

                    expr_ref_vector * empty_v = alloc(expr_ref_vector, m_manager);
                    up.push_back(new (region) parse_frame(current, pop_q, empty_v, 0, m_binding_level));

                    //
                    // process the body.
                    // 
                    right   = 0;
                    current = body;
                    break;
                }

                if (is_underscore_op(region, current->children()[0], builder)) {
                    up.push_back(new (region) parse_frame(current, builder, left, right, m_binding_level));
                }
                else if (local_scope.find(head_symbol, builder)) {
                    up.push_back(new (region) parse_frame(current, builder, left, right, m_binding_level));
                }   
                else {
                    up.push_back(new (region) parse_frame(current->children()[0], left, right, m_binding_level));
                }
                left  = alloc(expr_ref_vector, m_manager);
                right = current->children() + 1;
                current = 0;
                break;
            }            
        }

    cleanup:

        if (success && !is_well_sorted(m_manager, result)) {
            set_error("expression is not well sorted", e);
            success = false;
        }

        dealloc(left);
        while (!up.empty()) {
            dealloc(up.back()->detach_left());
            up.pop_back();
        }
        return success;        
    }

    bool read_patterns(unsigned num_bindings, symbol_table<idbuilder*> & local_scope, proto_expr * const * & children, 
                       expr_ref_buffer & patterns, expr_ref_buffer & no_patterns, int& weight, symbol& qid, symbol& skid) {
        proto_region region;
        while (children[0] && 
               children[0]->kind() == proto_expr::ANNOTATION &&
               children[1]) {

            if (children[0]->string() == symbol("qid") || 
                children[0]->string() == symbol("named")) {
                qid = children[1]->string();
                children += 2;
                continue;
            }               

            if (children[0]->string() == symbol("skolemid")) {
                skid = children[1]->string();
                children += 2;
                continue;
            }

            ptr_vector<proto_expr> proto_exprs;

            if (children[1]->kind() == proto_expr::COMMENT) {
                std::string s = children[1]->string().str();
                std::istringstream stream(s);
                scanner scanner(stream, get_err(), false);
                proto_expr_parser parser(region, scanner, get_err());
            
                if (!parser.parse(proto_exprs)) {
                    set_error("could not parse expression", children[1]);
                    return false;
                }                        
            } else if (children[1]->kind() == proto_expr::CONS) {
                for (proto_expr* const* pexpr = children[1]->children(); *pexpr; pexpr++)
                    proto_exprs.push_back(*pexpr);                
            } else {
                proto_exprs.push_back(children[1]);
            }

            expr_ref_buffer ts(m_manager);
            for (unsigned i = 0; i < proto_exprs.size(); ++i) {
                expr_ref t(m_manager);
                if (!make_expression(local_scope, proto_exprs[i], t)) {
                    return false;
                }
                ts.push_back(t.get());
            }

            if (children[0]->string() == symbol("pat") ||
                children[0]->string() == symbol("pats") || 
                children[0]->string() == symbol("pattern")) {
                for (unsigned i = 0; i < ts.size(); ++i) {
                    if (!is_app(ts[i])) {
                        set_error("invalid pattern", children[0]);
                        return false;
                    }
                }
                expr * p = m_manager.mk_pattern(ts.size(), (app*const*)(ts.c_ptr()));
                if (!p || (!ignore_user_patterns() && !m_pattern_validator(num_bindings, p))) {
                    set_error("invalid pattern", children[0]);
                    return false;
                }
                patterns.push_back(p);
            }
            else if (children[0]->string() == symbol("ex_act") && ts.size() == 1) {
                app * sk_hack = m_manager.mk_app(m_sk_hack, 1, ts.c_ptr());
                expr * p = m_manager.mk_pattern(1, &sk_hack);
                if (!p || (!ignore_user_patterns() && !m_pattern_validator(num_bindings, p))) {
                    set_error("invalid pattern", children[0]);
                    return false;
                }
                patterns.push_back(p);
            }
            else if ((children[0]->string() == symbol("nopat") ||
                      children[0]->string() == symbol("no-pattern"))
                     && ts.size() == 1) {
                no_patterns.push_back(ts[0]);
            }
            else if (children[0]->string() == symbol("weight") && ts.size() == 1 && 
                     proto_exprs[0]->kind() == proto_expr::INT &&
                     proto_exprs[0]->number().is_unsigned()) {
                weight = proto_exprs[0]->number().get_unsigned();
            }
            else {
                // TODO: this should be a warning, perferably once per unknown kind of annotation
                set_error("could not understand annotation '", 
                          children[0]->string().bare_str(), "'", children[0]);
            }
                        
            children += 2;                       
        }        
        return true;
    }

    void set_default_num_sort(symbol const& name) {
        if (name == symbol("QF_RDL") ||
            name == symbol("QF_LRA") ||
            name == symbol("LRA") ||
            name == symbol("RDL") ||
            name == symbol("QF_NRA") ||
            name == symbol("QF_UFNRA") ||
            name == symbol("QF_UFLRA")) {
            m_int_sort = m_real_sort;
        }
    }

    bool get_sort(theory* th, char const * s, sort_ref& sort) {
        return make_sort(symbol(s), 0, 0, sort);
    }
        

    bool make_sort(symbol const & id, unsigned num_params, parameter const* params, sort_ref& s) {
        builtin_op info;
        if (m_builtin_sorts.find(id, info)) {
            s = m_manager.mk_sort(info.m_family_id, info.m_kind, num_params, params);
            return true;
        }

        if (num_params == 2 && symbol("Array") == id) {
            // Old HACK to accomodate bit-vector arrays.

            if (!params[0].is_int()) {
                throw default_exception("Non-integer parameter to array");
                return false;
            }
            if (!params[1].is_int()) {
                throw default_exception("Non-integer parameter to array");
                return false;
            }
            parameter bv_params0[1] = { parameter(params[0].get_int()) };
            parameter bv_params1[1] = { parameter(params[1].get_int()) };

            sort * t1 = m_manager.mk_sort(m_bv_fid, BV_SORT, 1, bv_params0);
            sort * t2 = m_manager.mk_sort(m_bv_fid, BV_SORT, 1, bv_params1);
            parameter params[2] = { parameter(t1), parameter(t2) };
            s = m_manager.mk_sort(m_array_fid, ARRAY_SORT, 2, params);
            return true;
        }
        
        sort* srt = 0;
        if (m_benchmark.get_sort(id, srt)) {
            s = srt;
            return true;
        }
        return false;
    }

    bool make_sort(proto_expr * e, sort_ref& s) {
        SASSERT(can_be_sort(e));
        symtable& env = *m_benchmark.get_symtable();
        sort_builder* mk_sort;
        switch(e->kind()) {
        case proto_expr::ID: {
            if (make_sort(e->string(), e->num_params(), e->params(), s)) {
                return true;
            }
            if (env.lookup(e->string(), mk_sort)) {
                if (!mk_sort->apply(e->num_params(), e->params(), s)) {
                    set_error(mk_sort->error_message(), e);
                    return false;
                }
                return true;
            }
            set_error("could not find sort ", e);
            return false;
        }
        case proto_expr::CONS: {
            if (!can_be_sort(e)) {
                set_error("expression cannot be a sort", e);
                return false;
            }
            proto_expr *const* chs = e->children();
            if (is_underscore(e)) {
                ++chs;
            }
            symbol name = (*chs)->string();
            if (!env.lookup(name, mk_sort)) {
                set_error("could not find sort symbol '", name.str(), "'", e);
                return false;
            }
            sort_ref_vector sorts(m_manager);
            vector<parameter> params;
            if (!parse_params(chs+1, params, sorts)) {
                return false;
            }

            if (!mk_sort->apply(params.size(), params.c_ptr(), s)) {
                set_error(mk_sort->error_message(), e);
                return false;
            }
            return true;
        }
        default:
            set_error("could not create sort ", e);
            return false;
        }
    }

    bool parse_params(proto_expr* const* chs,vector<parameter>& params, sort_ref_vector& sorts) {
        while (*chs) {
            if ((*chs)->kind() == proto_expr::INT) {
                rational const& num = (*chs)->number();
                if (num.is_unsigned()) {
                    params.push_back(parameter(num.get_unsigned()));
                    }
                else {
                    params.push_back(parameter(num));
                }
            }           
            else {
                sort_ref s1(m_manager);
                if (!make_sort(*chs, s1)) {
                    return false;
                }
                sorts.push_back(s1);
                params.push_back(parameter((ast*)s1.get()));
            }
            ++chs;
        }
        return true;
    }

    bool parse_bound(
        symbol_table<idbuilder*>& local_scope, 
        region& region, 
        proto_expr* bound, 
        svector<symbol>& vars, 
        sort_ref_buffer& sorts
        ) 
    {
        if (is_cons_list(bound)) {
            proto_expr *const* children = bound->children();
            while (*children) {
                if (!parse_bound(local_scope, region, *children, vars, sorts)) {
                    return false;
                }
                ++children;
            }
            return true;
        }
        if (!can_be_sorted_var(bound)) {
            set_error("bound variable should contain a list of pairs", bound);
            return false;
        }        
        proto_expr* var = bound->children()[0];
        proto_expr* sort_proto_expr = bound->children()[1];
        
        sort_ref sort(m_manager);
        if (!make_sort(sort_proto_expr, sort)) {
            return false;
        }
        sorts.push_back(sort);
        vars.push_back(var->string());
        
        local_scope.insert(
            var->string(), 
            new (region) bound_var(this, sort)
            );
        
        ++m_binding_level; 

        return true;
    }

    bool can_be_sort(proto_expr* e) {
        if (e && e->kind() == proto_expr::ID) {
            return true;
        }
        if (is_underscore(e)) {
            return true;
        }
            
        if (e && 
            e->kind() == proto_expr::CONS && 
            e->children() && 
            e->children()[0] && 
            e->children()[1]) {
            proto_expr* const* ch = e->children();
            while(*ch) {
                if (!can_be_sort(*ch)) {
                    return false;
                }
                ++ch;
            }
            return true;
        }
        return false;        
    }

    bool declare_sorts(proto_expr* e) {
        proto_expr* const * children = e->children();

        while (children && *children) {
            proto_expr* ch = *children;
            switch(ch->kind()) {

            case proto_expr::ID:
                m_benchmark.declare_sort(ch->string());
                break;

            case proto_expr::CONS:
                //
                // The declaration of type constructors
                // consists of an identifier together with
                // a number indicating the arity of the
                // constructor.
                // 
                if (ch->children() && 
                    ch->children()[0] &&
                    ch->children()[0]->kind() == proto_expr::ID &&
                    ch->children()[1] && 
                    ch->children()[1]->kind() == proto_expr::INT) {
                    
                    // unsigned num = (unsigned) ch->children()[1]->number().get_uint64();
                    m_benchmark.declare_sort(ch->children()[0]->string());                    
                }
                break;

            case proto_expr::ANNOTATION:
                break;

            default:
                set_error("unexpected argument to sorts",ch);
                return false;
            }
            ++children;
        }
        return true;
    }

    bool define_sorts(proto_expr* e) {
        proto_expr* const * children = e->children();

        while (children && *children) {
            if (!define_sort(*children)) {
                return false;
            }
            ++children;
        }
        return true;
    }

    bool define_sort(proto_expr* e) {
        proto_expr* const * children = e->children();
        sort_ref_buffer  domain(m_manager);

        //
        // First element in list must be an identifier.
        // there should be just two elements.
        //
        if (!children || 
            !children[0] ||
            !(children[0]->kind() == proto_expr::ID) ||
            !children[1] ||
            children[2]) {
            set_error("unexpected arguments to function declaration", e);
            return false;
        }
        symbol name = children[0]->string();        
        sort_ref s(m_manager);
        if (!can_be_sort(children[1]) ||
            !make_sort(children[1], s)) {
            set_error("unexpected arguments to function declaration", e);
            return false;
        }
        
        m_benchmark.get_symtable()->insert(name, s);

        return true;
    }

    bool declare_funs(proto_expr* e) {
        proto_expr* const * children = e->children();

        while (children && *children) {
            if (!declare_fun(*children)) {
                return false;
            }
            ++children;
        }
        return true;
    }
    class define_sort_cls : public sort_builder {
        smtparser&      m_parser;
        proto_region    m_region;
        proto_expr*     m_expr; 
        svector<symbol> m_params;
        symbol          m_name;
        std::string     m_error_message;

    public:
        define_sort_cls(smtparser& p, symbol const& name, proto_expr* e, unsigned num_params, symbol* params) : 
            m_parser(p),
            m_name(name) {
            for (unsigned i = 0; i < num_params; ++i) {
                m_params.push_back(params[i]);
            }
            m_expr = proto_expr::copy(m_region, e);
        }        
        
        virtual bool apply(unsigned num_params, parameter const* params, sort_ref & result) {
            smtlib::symtable * symtable = m_parser.m_benchmark.get_symtable();
            if (m_params.size() != num_params) {
                std::ostringstream strm;
                strm << "wrong number of arguments passed to " << m_name << " " 
                     << m_params.size() << " expected, but " << num_params << " given";
                m_error_message = strm.str();                
                return false;
            }
            for (unsigned i = 0; i < num_params; ++i) {
                parameter p(params[i]);
                if (!p.is_ast() || !is_sort(p.get_ast())) {
                    symtable->pop_sorts(i);
                    std::ostringstream strm;
                    strm << "argument " << i << " is not a sort";
                    m_error_message = strm.str();
                    return false;
                }
                symtable->push_sort(m_params[i], to_sort(p.get_ast()));
            }
            bool success = m_parser.make_sort(m_expr, result);

            symtable->pop_sorts(num_params);
            return success;
        }

        virtual char const* error_message() {
            return m_error_message.c_str();
        }

    };

    // (define-sort name (<symbol>*) <sort>)
    bool define_sort(proto_expr* id, proto_expr* sorts, proto_expr* srt) {
        symbol name = id->string();
        proto_expr* const * children = sorts->children();
        svector<symbol> names;

        if (!children) {
            set_error("Sort definition expects a list of sort symbols",id);
            return false;
        }

        while (children[0]) {
            id = children[0];
            if(id->kind() != proto_expr::ID) {
                set_error("unexpected argument, expected ID", id);
                return false;
            }
            names.push_back(id->string());
            ++children;                        
        }        

        m_benchmark.get_symtable()->insert(name, alloc(define_sort_cls, *this, name, srt, names.size(), names.c_ptr())); 
        return true;
    }

    bool declare_fun(proto_expr* id, proto_expr* sorts, proto_expr* srt) {
        proto_expr* const * children = sorts?sorts->children():0;
        sort_ref_buffer  domain(m_manager);
        symbol name = id->string();
        
        if (sorts && !children) {
            set_error("Function declaration expects a list of sorts", id);
            return false;
        }
        //
        // parse domain.
        //
        while (sorts && children[0]) {
            sort_ref s(m_manager);
            if (!make_sort(children[0], s)) {
                return false;
            }
            domain.push_back(s);
            ++children;                        
        }

        sort_ref range(m_manager);
        if (!make_sort(srt, range)) {
            return false;
        }
        bool is_associative = false;
        bool is_commutative = false;
        bool is_injective   = false;
        m_benchmark.declare_func(name, domain, range, is_associative, is_commutative, is_injective);
        return true;
    }

    bool declare_fun(proto_expr* e) {
        proto_expr* const * children = e->children();
        sort_ref_buffer  domain(m_manager);
        //
        // Skip declaration of numbers.
        // 
        if (children && 
            children[0] &&
            children[0]->kind() == proto_expr::INT) {
            return true;
        }

        //
        // First element in list must be an identifier.
        //
        if (!children || 
            !children[0] ||
            !(children[0]->kind() == proto_expr::ID)) {
            set_error("unexpected arguments to function declaration", e);
            return false;
        }

        symbol name = children[0]->string();

        ++children;

        
        if (!can_be_sort(children[0])) {
            set_error("unexpected arguments to function declaration", e);
            return false;
        }
        
        //
        // parse domain.
        //
        while (can_be_sort(children[1])) {
            sort_ref s(m_manager);
            if (!make_sort(children[0], s)) {
                return false;
            }
            domain.push_back(s);
            ++children;                        
        }

        //
        // parse range.
        //
        SASSERT(can_be_sort(children[0]));

        sort_ref range(m_manager);
        if (!make_sort(children[0], range)) {
            return false;
        }
        ++children;

        //
        // parse attributes.
        //
        bool is_associative = false;
        bool is_commutative = false;
        bool is_injective   = false;
        
        while(children[0] && children[0]->kind() == proto_expr::ANNOTATION) {

            if (m_associative == children[0]->string()) {
                is_associative = true;
            }
            else if (m_commutative == children[0]->string()) {
                is_commutative = true;
            }
            else if (m_injective == children[0]->string()) {
                is_injective = true;
            }
            ++children;
        }

        m_benchmark.declare_func(name, domain, range, is_associative, is_commutative, is_injective);

        return true;
    }

    bool declare_preds(proto_expr* e) {
        proto_expr* const * children = e->children();

        while (children && *children) {
            if (!declare_pred(*children)) {
                return false;
            }
            ++children;
        }
        return true;
    }


    bool declare_pred(proto_expr* e) {
        proto_expr* const * children = e->children();
        if (!children || !children[0] || !(children[0]->kind() == proto_expr::ID)) {
            set_error("unexpected arguments to predicate declaration", e);
            return false;
        }
        symbol const & name = children[0]->string();
        sort_ref_buffer domain(m_manager);
        sort * bool_sort = m_manager.mk_bool_sort();

        ++children;

        while (can_be_sort(children[0])) {
            sort_ref s(m_manager);
            if (!make_sort(children[0], s)) {
                return false;
            }            
            domain.push_back(s);
            ++children;
        }

        m_benchmark.declare_func(name, domain, bool_sort, false, false, false);

        return true;
    }

    bool declare_datatypes(proto_expr * e) {
        TRACE("datatypes", tout << "new datatype declarion section\n";);
        proto_expr * const* children = e->children();

        buffer<symbol> dt_names;
        
        while (children && *children) {
            proto_expr *  type_decl   = *children;
            proto_expr * const* td_children = type_decl->children();
            if (!td_children || !td_children[0] || !(td_children[0]->kind() == proto_expr::ID)) {
                set_error("invalid datatype declaration", type_decl);
                return false;
            }
            symbol name = td_children[0]->string();
            sort * dummy;
            if (m_benchmark.get_symtable()->find(name, dummy)) {
                set_error("invalid datatype declaration, name was already used", type_decl);
                return false;
            }
            dt_names.push_back(name);
            TRACE("datatypes", tout << name << "\n";);
            ++children;
        }

        children = e->children();

        ptr_buffer<datatype_decl> datatypes;

        while (children && *children) {
            datatype_decl * d = declare_datatype(*children, dt_names);
            if (!d) {
                return false;
            }
            datatypes.push_back(d);
            ++children;
        }

        sort_ref_vector new_types(m_manager);

        bool result = m_dt_plugin->mk_datatypes(datatypes.size(), datatypes.c_ptr(), new_types);
        del_datatype_decls(datatypes.size(), datatypes.c_ptr());

        if (!result) {
            set_error("invalid datatype declaration", e);
        }
        else {
            unsigned num_types = new_types.size();
            for (unsigned i = 0; i < num_types; i++) {
                sort * d = new_types.get(i);
                TRACE("datatype", tout << "new datatype\n" << mk_pp(d, m_manager) << "\n";
                      tout << "num. elements: " << d->get_num_elements() << "\n";
                      tout << "recursive: " << m_dt_util.is_recursive(d) << "\n";
                      tout << "non_rec constructor: " << m_dt_util.get_non_rec_constructor(d)->get_name() << "\n";
                      );
                m_benchmark.insert(d);
                ptr_vector<func_decl> const * constructors = m_dt_util.get_datatype_constructors(d);
                unsigned num_constructors = constructors->size();
                for (unsigned j = 0; j < num_constructors; j++) {
                    func_decl * c = constructors->get(j);
                    m_benchmark.insert(c);
                    func_decl * r = m_dt_util.get_constructor_recognizer(c);
                    TRACE("datatype", 
                          tout << "new constructor\n" << mk_pp(c, m_manager) << "\n";
                          tout << "new recogniser\n" << mk_pp(r, m_manager) << "\n";);
                    m_benchmark.insert(r);
                    ptr_vector<func_decl> const * accessors = m_dt_util.get_constructor_accessors(c);
                    unsigned num_accessors = accessors->size();
                    for (unsigned k = 0; k < num_accessors; k++) {
                        func_decl * a = accessors->get(k);
                        TRACE("datatype", tout << "new accessor\n" << mk_pp(a, m_manager) << "\n";);
                        m_benchmark.insert(a);
                    }
                }
            }
        }
        
        return result;
    }

    datatype_decl * declare_datatype(proto_expr * e, buffer<symbol> const & dt_names) {
        proto_expr* const * children = e->children();
        symbol const& name    = children[0]->string();

        ptr_buffer<constructor_decl> constructors;
        ++children; // consume id
        
        while (children && *children) {
            constructor_decl * c = declare_constructor(*children, dt_names);
            if (!c) {
                del_constructor_decls(constructors.size(), constructors.c_ptr());
                return 0;
            }
            constructors.push_back(c);
            ++children;
        }
        
        if (constructors.size() == 0) {
            set_error("datatype must have at least one constructor", e);
            return 0;
        }

        return mk_datatype_decl(name, constructors.size(), constructors.c_ptr());
    }

    constructor_decl * declare_constructor(proto_expr * e, buffer<symbol> const & dt_names) {
        if (e->kind() == proto_expr::ID) {
            symbol const & name = e->string();
            string_buffer<> tmp;
            tmp << "is_" << name;
            symbol r_name(tmp.c_str());
            return mk_constructor_decl(name, r_name, 0, 0);
        }

        proto_expr* const * children = e->children();
        if (!children || !children[0] || !(children[0]->kind() == proto_expr::ID)) {
            set_error("invalid constructor declaration", e);
            return 0;
        }

        symbol const & name = children[0]->string();
        string_buffer<> tmp;
        tmp << "is_" << name;
        symbol r_name(tmp.c_str());

        ptr_buffer<accessor_decl> accessors;
        ++children; // skip id

        while (children && *children) {
            accessor_decl * d = declare_accessor(*children, dt_names);
            if (!d) {
                del_accessor_decls(accessors.size(), accessors.c_ptr());
                return 0;
            }
            accessors.push_back(d);
            ++children;
        }

        return mk_constructor_decl(name, r_name, accessors.size(), accessors.c_ptr());
    }

    accessor_decl * declare_accessor(proto_expr * e, buffer<symbol> const & dt_names) {
        proto_expr* const * children = e->children();
        if (!children || 
            !children[0] || !(children[0]->kind() == proto_expr::ID) || 
            !children[1] || !(children[1]->kind() == proto_expr::ID) ||
            children[2]) {
            set_error("invalid accessor declaration", e);
            return 0;
        }
        
        symbol const& name  = children[0]->string();
        symbol const& tname = children[1]->string();
        unsigned tid   = 0;
        for (; tid < dt_names.size(); tid++) {
            if (tname == dt_names[tid]) {
                break;
            }
        }

        type_ref ty;
        if (tid < dt_names.size()) {
            ty = type_ref(tid);
        }
        else {
            sort_ref s(m_manager);
            if (!make_sort(tname, children[1]->num_params(), children[1]->params(), s)) {
                set_error("unknown sort", children[1]);
                return 0;
            }
            m_pinned_sorts.push_back(s);
            ty = type_ref(s.get());
        }
        
        return mk_accessor_decl(name, ty);
    }

    //
    // (define-macro (name (x A) (y B)) body[x,y])
    // 

    bool can_be_sorted_var(proto_expr* e) {
        return 
            e &&
            (e->kind() == proto_expr::CONS) &&
            e->children() &&
            e->children()[0] &&
            (e->children()[0]->kind() == proto_expr::ID) &&
            can_be_sort(e->children()[1]);
    }

    bool is_cons_list(proto_expr* e) {
        return 
            e && 
            (e->kind() == proto_expr::CONS) && 
            e->children() && 
            e->children()[0] &&
            e->children()[0]->kind() == proto_expr::CONS;
    }

    bool is_prefixed(proto_expr* e, symbol const& s) {
        return 
            e && 
            (e->kind() == proto_expr::CONS) &&
            e->children() &&
            e->children()[0] &&
            e->children()[1] &&
            e->children()[0]->string() == s;

    }

    bool is_underscore(proto_expr* e) {
        return 
            is_prefixed(e, m_underscore) &&
            e->children()[1]->kind() == proto_expr::ID;
    }

    bool is_annotated_cons(proto_expr* e) {
        return is_prefixed(e, m_bang);
    }

    bool is_builtin_const(symbol const& id, proto_expr* current, unsigned num_params, parameter * params, bool& ok, expr_ref& term) {
        builtin_op info;
        ok = true;
        if (!m_builtin_ops.find(id, info)) {
            return false;
        }
        fix_parameters(num_params, params);
        func_decl* d = m_manager.mk_func_decl(info.m_family_id, info.m_kind, num_params, params, 0, (expr * const *)0);
        if (!d) {
            set_error("could not create a term from constant ", id, current);
            ok = false;
        }
        else if (d->get_arity() != 0) {
            set_error("identifier expects arguments ", id, current);
            ok = false;
        }
        else {
            term = m_manager.mk_const(d);
        }
        return true;
    }

    bool is_underscore_op(region& r, proto_expr* e, idbuilder*& builder) {
        if (!is_underscore(e)) {
            return false;
        }
        builtin_op info;
        proto_expr *const* chs = e->children()+1;
        symbol const& id = (*chs)->string();
        sort_ref_vector sorts(m_manager);
        vector<parameter> params;

        if (!m_builtin_ops.find(id, info)) {
            return false;
        }
        if (!parse_params(chs+1, params, sorts)) {
            return false;
        }

        builder = new (r) builtin_builder(this, info.m_family_id, info.m_kind, params);
        return true;
    }



    bool define_fun(symbol_table<idbuilder*>& table, region& r, proto_expr* name, proto_expr* args, 
                    proto_expr* srt, proto_expr* body, expr_ref & macro_expr) {

        symbol macro_name = name->string();

        proto_expr* const* chs = args->children();
        // parse marco arguments.
        table.begin_scope();
        ptr_vector<sort> sorts;
        sort_ref sort1(m_manager), sort2(m_manager);
        while (chs && *chs) {
            proto_expr* e1 = *chs;
            if (!can_be_sorted_var(e1)) {
                set_error("Macro definition takes a list of pairs", e1);
                goto error_cleanup;
            }
            proto_expr* var = e1->children()[0];
            proto_expr* srt = e1->children()[1];
            sort_ref sort(m_manager);
            if (!make_sort(srt, sort)) {
                goto error_cleanup;
            }
            sorts.push_back(sort);
            m_pinned_sorts.push_back(sort);
            table.insert(var->string(), new (r) bound_var(this, sort));
            ++chs;
            ++m_binding_level; 
        }

        if (!make_expression(table, body, macro_expr)) {
            goto error_cleanup;
        }           

        if (!make_sort(srt, sort1)) {
            goto error_cleanup;
        }
        sort2 = m_manager.get_sort(macro_expr);
        if (sort1.get() != sort2.get()) {
            std::ostringstream strm;
            strm << "The expected sort for macro was " << mk_pp(sort1, m_manager) 
                 << " but the macro body has sort " << mk_pp(sort2, m_manager);
            set_error(strm.str().c_str(), body);
            goto error_cleanup;
        }
        table.end_scope();
        m_binding_level = 0;
        table.insert(macro_name, new (r) macro_builder(r, body, macro_expr, this, sorts.size(), sorts.c_ptr()));   
        return true;

    error_cleanup:
        table.end_scope();
        m_binding_level = 0;
        return false;
    }

    bool define_macro(symbol_table<idbuilder*>& table, region& r, proto_expr* macro_defn, expr_ref & macro_expr) {
        SASSERT(macro_defn);
        proto_expr* const* exprs = macro_defn->children();
        proto_expr* e0 = exprs?exprs[0]:0;
        proto_expr* e1 = e0?exprs[1]:0;
        proto_expr* e2 = e1?exprs[2]:0;

        m_binding_level = 0;
        
        if (!e1) {
            set_error("macro definition requires two arguments, none given", macro_defn);
            return false;
        }
        if (!e2) {
            set_error("macro definition requires two arguments, only one given", macro_defn);
            return false;
        }

        // parse macro name
        symbol macro_name;
        proto_expr* const* chs = e1->children();        
        if (e1->kind() == proto_expr::ID) {
            macro_name = e1->string();
            chs = 0;
        }
        else if (chs && chs[0] && chs[0]->kind() == proto_expr::ID) {
            macro_name = chs[0]->string();
            chs = chs + 1;
        }
        else {
            set_error("first argument to macro definition should be a name or a name applied to arguments", e1);
            return false;
        }  

        // parse marco arguments.
        table.begin_scope();
        ptr_vector<sort> sorts;
        while (chs && *chs) {
            e1 = *chs;
            if (!can_be_sorted_var(e1)) {
                set_error("Macro definition takes a list of pairs", e1);
                goto error_cleanup;
            }
            proto_expr* var = e1->children()[0];
            proto_expr* srt = e1->children()[1];
            sort_ref sort(m_manager);
            if (!make_sort(srt, sort)) {
                goto error_cleanup;
            }
            sorts.push_back(sort);
            m_pinned_sorts.push_back(sort);
            table.insert(var->string(), new (r) bound_var(this, sort));
            ++chs;
            ++m_binding_level; 
        }

        if (!make_expression(table, e2, macro_expr)) {
            goto error_cleanup;
        }                        
        table.end_scope();
        m_binding_level = 0;
        table.insert(macro_name, new (r) macro_builder(r, e2, macro_expr, this, sorts.size(), sorts.c_ptr()));   
        return true;

    error_cleanup:
        table.end_scope();
        m_binding_level = 0;
        return false;
    }

    void fix_parameters(unsigned num_params, parameter* params) {
        for (unsigned i = 0; i < num_params; ++i) {
            func_decl* d = 0;
            sort* s = 0;
            builtin_op info;
            if (params[i].is_symbol() && m_benchmark.get_symtable()->find1(params[i].get_symbol(), d)) {
                params[i] = parameter(d);
            }
            else if (params[i].is_symbol() && m_benchmark.get_symtable()->find(params[i].get_symbol(), s)) {
                params[i] = parameter(s);
            }
            else if (params[i].is_symbol() && m_builtin_sorts.find(params[i].get_symbol(), info)) {
                params[i] = parameter(m_manager.mk_sort(info.m_family_id, info.m_kind, 0, 0));
            }
        }
    }

    bool test_unify(proto_expr * e, bool expected) {
        proto_expr* const * children = e->children();
        if (!children || !children[0] || !children[1]) {
            set_error("invalid unification problem", e);
        }
        
        expr_ref f1(m_manager), f2(m_manager);
        if (!make_expression(children[0], f1) || !make_expression(children[1], f2))
            return false;
        unsigned num_vars1 = 0;
        unsigned num_vars2 = 0;
        if (is_forall(f1)) {
            num_vars1 = to_quantifier(f1)->get_num_decls();
            f1 = to_quantifier(f1)->get_expr();
        }
        if (is_forall(f2)) {
            num_vars2 = to_quantifier(f2)->get_num_decls();
            f2 = to_quantifier(f2)->get_expr();
        }
        substitution s(m_manager);
        s.reserve(2, std::max(num_vars1, num_vars2));
        unifier u(m_manager);
        if (u(f1, f2, s)) {
            std::cout << "unification: succeeded\n";
            if (!expected) {
                get_err() << "WRONG ANSWER\n";
                UNREACHABLE();
            }
            unsigned deltas[2] = { 0, num_vars1 };
            s.display(std::cout, 2, deltas);
        }
        else {
            std::cout << "unification: failed\n";
            if (expected) {
                get_err() << "WRONG ANSWER\n";
                UNREACHABLE();
            }
        }
        return true;
    }

    void dump_substitution(expr_ref_buffer & s) {
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * t = s[i];
            if (t)
                std::cout << "VAR " << i << " -->\n" << mk_pp(t, m_manager) << "\n";
        }
    }

#if    !defined(SMTCOMP) && !defined(_EXTERNAL_RELEASE)
    bool test_order(proto_expr * e, order & ord, symbol expected) {
        proto_expr* const * children = e->children();
        if (!children || !children[0] || !children[1]) {
            set_error("invalid unification problem", e);
        }
        
        expr_ref f1(m_manager), f2(m_manager);
        if (!make_expression(children[0], f1) || !make_expression(children[1], f2))
            return false;
        unsigned num_vars1 = 0;
        unsigned num_vars2 = 0;
        if (is_forall(f1)) {
            num_vars1 = to_quantifier(f1)->get_num_decls();
            f1 = to_quantifier(f1)->get_expr();
        }
        if (is_forall(f2)) {
            num_vars2 = to_quantifier(f2)->get_num_decls();
            f2 = to_quantifier(f2)->get_expr();
        }
        ord.reserve(1, std::max(num_vars1, num_vars2));
        order::result r = ord.compare(f1.get(), f2.get());
        if ((r == order::UNCOMPARABLE && expected != symbol("kbo_un") && expected != symbol("lpo_un")) ||
            (r == order::LESSER && expected != symbol("kbo_lt") && expected != symbol("lpo_lt")) ||
            (r == order::GREATER && expected != symbol("kbo_gt") && expected != symbol("lpo_gt")) ||            
            (r == order::EQUAL && expected != symbol("kbo_eq") && expected != symbol("lpo_eq")) ||
            r == order::UNKNOWN) {
            get_err() << "WRONG ANSWER\n";
            UNREACHABLE();
        }
        else 
            std::cout << "order: succeeded\n";
        return true;
    }

    bool test_kbo(proto_expr * e, symbol expected) {
        precedence * p = alloc(arbitrary_precedence);
        kbo k(m_manager, p);
        return test_order(e, k, expected);
    }

    bool test_lpo(proto_expr * e, symbol expected) {
        precedence * ps[2] = { alloc(arity_precedence), alloc(arbitrary_precedence) };
        precedence * p  = alloc(lex_precedence, 2, ps);
        lpo l(m_manager, p);
        return test_order(e, l, expected);
    }

    bool test_st(proto_expr * e, symbol op) {
        expr_ref f(m_manager);
        if (!make_expression(e, f))
            return false;
        
        if (is_forall(f))
            f = to_quantifier(f)->get_expr();

        if (!is_app(f))
            set_error("invalid st operation", e);

        if (op == symbol("st_insert"))
            m_st.insert(to_app(f));
        else
            m_st.erase(to_app(f));

        return true;
    }

  


    class simple_st_visitor : public st_visitor {
        unsigned m_delta;
    public:
        simple_st_visitor(substitution & s, unsigned d):st_visitor(s), m_delta(d) {}
        virtual bool operator()(expr * e) { 
            std::cout << "found:\n" << mk_pp(e, m_subst.get_manager()) << "\n";
            unsigned deltas[2] = { 0, m_delta };
            std::cout << "substitution:\n";
            // m_subst.display(std::cout); std::cout << "\n";
            m_subst.display(std::cout, 2, deltas);
            std::cout << "\n";
            return true;
        }
    };

    bool test_st_visit(proto_expr * e, symbol op) {
        expr_ref f(m_manager);
        if (!make_expression(e, f))
            return false;

        unsigned num_vars = 0;
        if (is_forall(f)) {
            num_vars = to_quantifier(f)->get_num_decls();
            f = to_quantifier(f)->get_expr();
        }
        if (!is_app(f))
            set_error("invalid st operation", e);
        substitution s(m_manager);
        s.reserve(3, std::max(num_vars, m_st.get_approx_num_regs()));
        
        simple_st_visitor v(s, num_vars);
        
        std::cout << "searching for " << op << ":\n" << mk_pp(f, m_manager) << "\n\n";
        if (op == symbol("st_unify"))
            m_st.unify(to_app(f), v);
        else if (op == symbol("st_inst"))
            m_st.inst(to_app(f), v);
        else 
            m_st.gen(to_app(f), v);
        std::cout << "done.\n";
        return true;
    }
#endif

    bool declare_axioms(proto_expr * e) {
        proto_expr* const * children = e->children();
        while (children && *children) {
            if (!declare_axiom(*children)) {
                return false;
            }
            ++children;
        }
        return true;
    }

    bool declare_axiom(proto_expr * e) {
        expr_ref t(m_manager);
        if (!make_expression(e, t) ||
            !push_assumption(t.get())) {
            return false;
        }
        return true;
    }

    bool make_app(proto_expr * proto_expr, expr_ref_vector const & args, expr_ref & result) {
        symbol const& name = proto_expr->string();
        ptr_vector<sort> sorts;
        func_decl * d = 0;
        smtlib::symtable * symtable = m_benchmark.get_symtable();

        for (unsigned i = 0; i < args.size(); ++i) {
            sorts.push_back(m_manager.get_sort(args.get(i)));
        }

        if (symtable->find_overload(name, sorts, d)) {
            result = m_manager.mk_app(d, args.size(), args.c_ptr());
            return true;
        }

        builtin_op info;
        if (m_builtin_ops.find(name, info)) {
            unsigned num_params = proto_expr->num_params();
            parameter * params = proto_expr->params();     
            fix_parameters(num_params, params);
            d = m_manager.mk_func_decl(info.m_family_id, info.m_kind, num_params, params, args.size(), args.c_ptr());
            if (d) {
                result = m_manager.mk_app(d, args.size(), args.c_ptr());
                return true;
            }
        }

        rational arg2_value;
        bool     arg2_is_int;

        if (name == symbol("store") && 
            args.size() == 3 && 
            m_anum_util.is_numeral(args.get(2), arg2_value, arg2_is_int) &&
            arg2_is_int) {
            expr_ref_vector new_args(m_manager);
            new_args.push_back(args.get(0));
            new_args.push_back(args.get(1));
            new_args.push_back(m_anum_util.mk_numeral(arg2_value, false));
            sorts.reset();
            for (unsigned i = 0; i < args.size(); ++i) {
                sorts.push_back(m_manager.get_sort(new_args.get(i)));
            }
            if (symtable->find_overload(name, sorts, d)) {
                result = m_manager.mk_app(d, new_args.size(), new_args.c_ptr());
                return true;
            }
        }
        
        error_prefix(proto_expr);
        get_err() << "could not find overload for '" << name << "' ";
        for (unsigned i = 0; i < sorts.size(); ++i) {
            get_err() << "Argument: " 
                      << mk_pp(args.get(i), m_manager)
                      << " has type " 
                      << mk_pp(sorts[i], m_manager)
                      << ".\n";
        }            
        return false;
    }

    class nullary : public idbuilder {
        expr*      m_expr;
        smtparser* m_parser;
        unsigned   m_decl_level_save;
    public:
        nullary(expr* e, smtparser* p) : m_expr(e), m_parser(p), m_decl_level_save(p->m_binding_level) {}

        virtual bool apply(expr_ref_vector const& args, expr_ref & result) {
            unsigned decl_level = m_parser->m_binding_level;
            SASSERT(decl_level >= m_decl_level_save);
            shift_vars shifty(m_parser->m_manager);
            shifty(m_expr, decl_level - m_decl_level_save, result);
            return (args.size() == 0);
        }
    };

    class macro_builder : public idbuilder {
        proto_expr* m_p_expr;
        expr*      m_expr;
        smtparser* m_parser;
        unsigned   m_num_sorts;
        sort** m_sorts;
    public:
        macro_builder(region& r, proto_expr* p_expr, expr* e, smtparser* p, unsigned num_sorts, sort* const* sorts) :
            m_p_expr(p_expr), m_expr(e), m_parser(p), m_num_sorts(num_sorts) {
            m_sorts = new (r) sort*[num_sorts];
            for (unsigned i = 0; i < num_sorts; ++i) {
                m_sorts[i] = sorts[i];
            }
        }
        
        virtual bool apply(expr_ref_vector const& args, expr_ref& result) {
            ast_manager& m = m_parser->m_manager;
            if (args.size() != m_num_sorts) {
                m_parser->set_error("wrong number of arguments passed to macro", m_p_expr);
                return false;
            }
            for (unsigned i = 0; i < m_num_sorts; ++i) {
                if (m_sorts[i] != m.get_sort(args[i])) {
                    std::ostringstream strm;
                    strm << "sort miss-match for argument of macro. Expecting sort: ";
                    strm << mk_pp(m_sorts[i], m) << " instead argument ";
                    strm << mk_pp(args[i], m) << " with sort ";
                    strm << mk_pp(m.get_sort(args[i]), m);                                                
                    m_parser->set_error(strm.str().c_str(), m_p_expr);
                    return false;
                }
            }
            if (m_num_sorts == 0) {
                result = m_expr;
            }
            else {
                var_subst subst(m);
                subst(m_expr, args.size(), args.c_ptr(), result);
            }
            return true;            
        }
    };

    class identity : public idbuilder {
    public:
        identity() {}

        virtual bool apply(expr_ref_vector const & args, expr_ref & result) { 
            if (args.size() == 1) {
                result = args.back();
                return true;
            }
            else {
                return false;
            }
        }
    };

    class parse_frame {
    public:

        parse_frame(proto_expr * e, idbuilder * make, expr_ref_vector * left, proto_expr * const* right, unsigned binding_level): 
            m_proto_expr(e),
            m_make_term(make),
            m_left(left),
            m_right(right),
            m_binding_level(binding_level) {
        }

        parse_frame(proto_expr * e, expr_ref_vector * left, proto_expr * const* right, unsigned binding_level): 
            m_proto_expr(e),
            m_make_term(0),
            m_left(left),
            m_right(right),
            m_binding_level(binding_level) {
        }

        expr_ref_vector * detach_left() { 
            expr_ref_vector * result = m_left;
            SASSERT(m_left);
            m_left = 0;
            return result;
        }

        unsigned binding_level() const { return m_binding_level; }

        proto_expr* const * right() const { return m_right; }

        idbuilder* make_term() { return m_make_term; }

        proto_expr* get_proto_expr() const { return m_proto_expr; }

        ~parse_frame() { dealloc(m_left); }

    private:

        proto_expr*          m_proto_expr;
        idbuilder*           m_make_term;
        expr_ref_vector *    m_left;
        proto_expr* const *  m_right;
        unsigned             m_binding_level;

        parse_frame & operator=(parse_frame const & other);

        parse_frame(parse_frame const & other);

    };

    class build_label : public idbuilder {
        bool        m_pos;
        symbol      m_sym;
        smtparser * m_smt;
    public:
        build_label(smtparser * smt, bool is_pos, proto_expr * sym): m_pos(is_pos), m_smt(smt) {
            switch(sym->kind()) {
            case proto_expr::ID:
            case proto_expr::STRING:
                m_sym = sym->string();
                break;
            case proto_expr::INT:
                m_sym = symbol(sym->number().to_string().c_str());
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        
        virtual bool apply(expr_ref_vector const & args, expr_ref & result) {
            if (args.size() >= 1) {
                result = m_smt->m_manager.mk_label(m_pos, m_sym, args.get(0));
                return true;
            }
            else {
                return false;
            }
        }
    };

    class pop_let : public idbuilder {
    public:
        pop_let(symbol_table<idbuilder*> & local_scope, expr_ref_vector* pinned = 0): 
            m_local_scope(local_scope),
            m_pinned(pinned) {
        }

        virtual ~pop_let() {}
        
        virtual bool apply(expr_ref_vector const & args, expr_ref & result) {
            dealloc(m_pinned);
            if (args.size() == 2) {
                m_local_scope.end_scope();
                result = args.get(1);
                return true;
            }
            else {
                return false;
            }
        }
    private:
        symbol_table<idbuilder*> & m_local_scope;
        expr_ref_vector*           m_pinned;
    };

    class push_let : public idbuilder {
        smtparser*                 m_parser;
        region &                   m_region;
        symbol_table<idbuilder*> & m_local_scope;
        symbol                     m_let_var;    

    public:
        push_let(smtparser* p, region & region, symbol_table<idbuilder*> & local_scope, symbol const & let_var): 
            m_parser(p),
            m_region(region),
            m_local_scope(local_scope),
            m_let_var(let_var) {
        }

        virtual bool apply(expr_ref_vector const & args, expr_ref & result) {
            // 
            // . push a scope, 
            // . create a nullary function using the variable/term association.
            // . return the (first) argument.
            // 
            // 
            if (args.size() == 1) {
                m_local_scope.begin_scope();
                m_local_scope.insert(m_let_var, new (m_region) nullary(args.back(), m_parser));
                result = args.back();
                return true;
            }
            else {
                return false;
            }
        }
    };

    // push multiple let bound variables.
    class push_let_and : public idbuilder {
        smtparser*                 m_parser;
        region &                   m_region;
        symbol_table<idbuilder*> & m_local_scope;
        unsigned                   m_num_vars;
        symbol*                    m_vars;
        expr_ref_vector*           m_pinned;

    public:
        push_let_and(smtparser* p, region & region, symbol_table<idbuilder*> & local_scope, expr_ref_vector* pinned, unsigned num_vars, symbol const* vars): 
            m_parser(p),
            m_region(region),
            m_local_scope(local_scope),
            m_num_vars(num_vars),
            m_vars(new (region) symbol[num_vars]),
            m_pinned(pinned) {
            for (unsigned i = 0; i < num_vars; ++i) {
                m_vars[i] = vars[i];
            }
        }

        virtual bool apply(expr_ref_vector const & args, expr_ref & result) {
            if (args.size() != m_num_vars) {
                return false;
            }

            //             
            // . push a scope, 
            // . create a nullary function using the variable/term association.
            // . return the last argument (arbitrary).
            // 

            m_local_scope.begin_scope();
            for (unsigned i = 0; i < m_num_vars; ++i) {
                m_local_scope.insert(m_vars[i], new (m_region) nullary(args[i], m_parser));
                m_pinned->push_back(args[i]);
            }
            result = args.back();
            return true;
        }
    };

    class bound_var : public idbuilder {
    public:
        bound_var(smtparser * smt, sort * sort): 
            m_smt(smt),
            m_decl_level(smt->m_binding_level),
            m_sort(sort) {
        }

        virtual bool apply(expr_ref_vector const & args, expr_ref & result) {
            SASSERT(m_smt->m_binding_level > m_decl_level);
            unsigned idx = m_smt->m_binding_level - m_decl_level - 1;
            result = m_smt->m_manager.mk_var(idx, m_sort);
            return args.empty();
        }

    private:
        smtparser * m_smt;
        unsigned    m_decl_level;
        sort *      m_sort;
    };

    class pop_quantifier : public idbuilder {
    public:
        pop_quantifier(smtparser * smt, bool is_forall, int weight, symbol const& qid, symbol const& skid, expr_ref_buffer & patterns, expr_ref_buffer & no_patterns, sort_ref_buffer & sorts, 
                       svector<symbol>& vars, symbol_table<idbuilder*> & local_scope, proto_expr* p_expr):
            m_smt(smt),
            m_is_forall(is_forall),
            m_weight(weight),
            m_qid(qid),
            m_skid(skid),
            m_patterns(m_smt->m_manager),
            m_no_patterns(m_smt->m_manager),
            m_sorts(m_smt->m_manager),
            m_local_scope(local_scope),
            m_p_expr(p_expr) {
            SASSERT(sorts.size() == vars.size());

            m_vars.append(vars);
            m_sorts.append(sorts);
            m_patterns.append(patterns);
            m_no_patterns.append(no_patterns);
        }

        virtual bool apply(expr_ref_vector const & args, expr_ref & result) {
            if (args.size() != 1) {
                return false;
            }

            m_local_scope.end_scope();

            expr * body = args.back();
            
            if (m_smt->ignore_user_patterns()) {
                TRACE("pat_bug", tout << "ignoring user patterns...: " << m_patterns.size() << "\n";);
                result = m_smt->m_manager.mk_quantifier(m_is_forall, 
                                                        m_sorts.size(),   // num_decls
                                                        m_sorts.c_ptr(),  // decl_sorts
                                                        m_vars.begin(),   // decl_names
                                                        body,
                                                        m_weight, 
                                                        m_qid,
                                                        m_skid,
                                                        0,
                                                        0,
                                                        0,
                                                        0);
            }
            else if (!m_patterns.empty()) {
                if (!m_no_patterns.empty()) {
                    m_smt->set_error("patterns were provided, ignoring :nopat attribute.", ((proto_expr*)0));
                }
                result = m_smt->m_manager.mk_quantifier(m_is_forall, 
                                                        m_sorts.size(),   // num_decls
                                                        m_sorts.c_ptr(),  // decl_sorts
                                                        m_vars.begin(),   // decl_names
                                                        body,
                                                        m_weight, 
                                                        m_qid,
                                                        m_skid,
                                                        m_patterns.size(),
                                                        m_patterns.c_ptr(),
                                                        0,
                                                        0);
            }
            else {
                result = m_smt->m_manager.mk_quantifier(m_is_forall, 
                                                        m_sorts.size(),   // num_decls
                                                        m_sorts.c_ptr(),  // decl_sorts
                                                        m_vars.begin(),   // decl_names
                                                        body,
                                                        m_weight, 
                                                        m_qid,
                                                        m_skid,
                                                        0,
                                                        0,
                                                        m_no_patterns.size(),
                                                        m_no_patterns.c_ptr());
            }

            //
            // reclaim memory resources on application.
            //

            m_vars.finalize();
            m_sorts.finalize();
            m_patterns.finalize();
            m_no_patterns.finalize();
            return true;
        }

    private:
        smtparser*                 m_smt;
        bool                       m_is_forall;
        int                        m_weight;  
        symbol                     m_qid;
        symbol                     m_skid;
        expr_ref_buffer            m_patterns;
        expr_ref_buffer            m_no_patterns;
        sort_ref_buffer            m_sorts;
        svector<symbol>            m_vars;
        symbol_table<idbuilder*>&  m_local_scope;
        proto_expr*                m_p_expr;
    };

    class builtin_builder : public idbuilder {
        smtparser* m_smt;
        family_id  m_fid;
        decl_kind  m_kind;
        vector<parameter> m_params;
        
    public:
        builtin_builder(smtparser* smt, family_id fid, decl_kind k,vector<parameter> const& p):
            m_smt(smt),
            m_fid(fid),
            m_kind(k),
            m_params(p)
        {
        }

        virtual bool apply(expr_ref_vector const& args, expr_ref& result) {
            ast_manager& m = m_smt->m_manager;
            func_decl* d = m.mk_func_decl(m_fid, m_kind, m_params.size(), m_params.c_ptr(), args.size(), args.c_ptr());
            if (d) {
                result = m.mk_app(d, args.size(), args.c_ptr());
            }
            m_params.finalize();
            return d != 0;
        }
    };

    bool push_status(smtlib::benchmark::status status) {
        m_benchmark.set_status( status);
        return true;
    }
   
    expr * mk_number(rational const & r, bool is_int){
        if (m_int_sort == m_real_sort)  // integer constants should be mapped to real
            is_int = false; 
        return m_anum_util.mk_numeral(r, is_int);
    }
    
    void push_benchmark(symbol const & name) {
        m_benchmark.set_name(name);
    }

    bool push_assumption(expr * t) {
        m_benchmark.add_axiom(t);
        return true;
    }

    bool push_formula(expr * t) {
        m_benchmark.add_formula(t);
        return true;
    }

    bool is_binary_let_binding(proto_expr* let_binding) {
        return 
            let_binding &&
            let_binding->children() &&
            let_binding->children()[0] &&
            (let_binding->children()[0]->kind() == proto_expr::ID) &&
            let_binding->children()[1] &&
            !let_binding->children()[2];
    }

    bool is_bvconst(symbol const & fname, unsigned num_params, parameter const* params, expr_ref & term) {
        rational n;
        char const * str = fname.bare_str();
        unsigned sz = 0;

        if (strncmp(str, "bvbin", 5) == 0) {
            str += 5;
            n = rational(0);
            while (*str == '1' || *str == '0') {
                n *= rational(2);
                n += rational(*str - '0');
                ++sz;
                ++str;
            }
            if (sz == 0) {
                return false;
            }
        }
        else if (strncmp(str, "bvhex", 5) == 0) {
            n = rational(0);
            str += 5;
            while (('0' <= *str && *str <= '9') ||
                   ('a' <= *str && *str <= 'f') ||
                   ('A' <= *str && *str <= 'F')) {
                n *= rational(16);
                if ('0' <= *str && *str <= '9') {
                    n += rational(*str - '0');
                }
                else if ('a' <= *str && *str <= 'f') {
                    n += rational(10);
                    n += rational(*str - 'a');
                }
                else {
                    SASSERT('A' <= *str && *str <= 'F');
                    n += rational(10);
                    n += rational(*str - 'A');
                }
                sz += 4;
                ++str;
            }
            if (sz == 0) {
                return false;
            }
        }
        else if (strncmp(str, "bv", 2) == 0 && '0' <= *(str + 2) && *(str + 2) <= '9') {
            n = rational(0);
            str += 2;
            while ('0' <= *str && *str <= '9') {
                n *= rational(10);
                n += rational(*str - '0');
                ++str;
            }
            if (num_params == 1) {
                sz = params[0].get_int();
            }
            else {
                sz = 32;
            }
        }
        else {
            return false;
        }
        
        term = m_bvnum_util.mk_numeral(n, sz);

        return true;
    }    
};


parser * parser::create(ast_manager& ast_manager, bool ignore_user_patterns) {
    return alloc(smtparser, ast_manager, ignore_user_patterns);
}
