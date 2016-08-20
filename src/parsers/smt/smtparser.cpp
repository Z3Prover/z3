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
#include"warning.h"
#include"error_codes.h"
#include"pattern_validation.h"
#include"var_subst.h"
#include"well_sorted.h"
#include"str_hashtable.h"
#include"stopwatch.h"

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
    ptr_vector<id_param_info>       m_id_infos;
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
        builtin_sort_builder(m, m.mk_family_id("array"), ARRAY_SORT) {}
};

class bv_sort : public builtin_sort_builder {
public:
    bv_sort(ast_manager& m) : 
        builtin_sort_builder(m, m.mk_family_id("bv"), BV_SORT) {}
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
                family_id fid = m.mk_family_id(symbol(NAME));  \
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
    symbol                   m_axioms;
    symbol                   m_notes;
    symbol                   m_array;
    symbol                   m_bang;
    symbol                   m_underscore;
    sort*                    m_int_sort;
    sort*                    m_real_sort;
    family_id                m_bv_fid;
    family_id                m_arith_fid;
    family_id                m_array_fid;
    family_id                m_rel_fid;
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
        m_axioms("axioms"),
        m_notes("notes"),
        m_array("array"),
        m_bang("!"),
        m_underscore("_"),
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

    void add_builtin_op(char const * s, family_id fid, decl_kind k) {
        m_builtin_ops.insert(symbol(s), builtin_op(fid, k));
    }

    void add_builtin_type(char const * s, family_id fid, decl_kind k) {
        m_builtin_sorts.insert(symbol(s), builtin_op(fid, k));
    }

    void initialize_smtlib() {
        smtlib::symtable* table = m_benchmark.get_symtable();

        symbol arith("arith");
        family_id afid = m_manager.mk_family_id(arith);
        m_arith_fid = afid;

        add_builtin_type("Int", afid, INT_SORT);
        add_builtin_type("Real", afid, REAL_SORT);
        add_builtin_type("Bool", m_manager.get_basic_family_id(), BOOL_SORT);

        m_int_sort  = m_manager.mk_sort(m_arith_fid, INT_SORT);
        m_real_sort = m_manager.mk_sort(m_arith_fid, REAL_SORT);

        add_builtins(afid);
        
        symbol bv("bv");
        family_id bfid = m_manager.mk_family_id(bv);
        m_bv_fid = bfid;        

        add_builtins(bfid);

        add_builtin_type("BitVec", bfid, BV_SORT);

        symbol array("array");
        afid = m_manager.mk_family_id(array);
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
                    sort * index   = m_manager.mk_uninterpreted_sort(symbol("Index"));
                    sort * element = m_manager.mk_uninterpreted_sort(symbol("Element"));
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

                    idbuilder* pop_q = new (region) pop_quantifier(this, (head_symbol == m_forall), weight, qid, skid, patterns, no_patterns, sorts, vars, local_scope);

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
                expr_ref p(m_manager);
                p = m_manager.mk_pattern(ts.size(), (app*const*)(ts.c_ptr()));
                if (!p || (!ignore_user_patterns() && !m_pattern_validator(num_bindings, p, children[0]->line(), children[0]->pos()))) {
                    set_error("invalid pattern", children[0]);
                    return false;
                }
                patterns.push_back(p);
            }
            else if (children[0]->string() == symbol("ex_act") && ts.size() == 1) {
                app_ref sk_hack(m_manager);
                sk_hack = m_manager.mk_app(m_sk_hack, 1, ts.c_ptr());
                app * sk_hackp = sk_hack.get();
                expr_ref p(m_manager);
                p = m_manager.mk_pattern(1, &sk_hackp);
                if (!p || (!ignore_user_patterns() && !m_pattern_validator(num_bindings, p, children[0]->line(), children[0]->pos()))) {
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
                       svector<symbol>& vars, symbol_table<idbuilder*> & local_scope):
            m_smt(smt),
            m_is_forall(is_forall),
            m_weight(weight),
            m_qid(qid),
            m_skid(skid),
            m_patterns(m_smt->m_manager),
            m_no_patterns(m_smt->m_manager),
            m_sorts(m_smt->m_manager),
            m_local_scope(local_scope) {
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
