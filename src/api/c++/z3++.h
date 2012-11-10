/*++
Copyright (c) 2012 Microsoft Corporation

    Thin C++ layer on top of the Z3 C API.
    Main features:
      - Smart pointers for all Z3 objects.
      - Object-Oriented interface.
      - Operator overloading.
      - Exceptions for signining Z3 errors

    The C API can be used simultaneously with the C++ layer.
    However, if you use the C API directly, you will have to check the error conditions manually.
    Of course, you can invoke the method check_error() of the context object.
Author:

    Leonardo (leonardo) 2012-03-28

Notes:

--*/
#ifndef __Z3PP_H_
#define __Z3PP_H_

#include<cassert>
#include<iostream>
#include<string>
#include<sstream>
#include<z3.h>
#include<limits.h>

namespace z3 {

    class exception;
    class config;
    class context;
    class symbol;
    class params;
    class ast;
    class sort;
    class func_decl;
    class expr;
    class solver;
    class goal;
    class tactic;
    class probe;
    class model;
    class func_interp;
    class func_entry;
    class statistics;
    class apply_result;
    class fixedpoint;
    
    /**
       \brief Exception used to sign API usage errors.
    */
    class exception {
        std::string m_msg;
    public:
        exception(char const * msg):m_msg(msg) {}
        char const * msg() const { return m_msg.c_str(); }
        friend std::ostream & operator<<(std::ostream & out, exception const & e) { out << e.msg(); return out; }
    };

    /**
       \brief Z3 global configuration object.
    */
    class config {
        Z3_config    m_cfg;
        config(config const & s);
        config & operator=(config const & s);
    public:
        config() { m_cfg = Z3_mk_config(); }
        ~config() { Z3_del_config(m_cfg); }
        operator Z3_config() const { return m_cfg; }
        /**
           \brief Add a global configuration.
        */
        void set(char const * param, char const * value) { Z3_set_param_value(m_cfg, param, value); }
        void set(char const * param, bool value) { Z3_set_param_value(m_cfg, param, value ? "true" : "false"); }
        void set(char const * param, int value) { 
            std::ostringstream oss;
            oss << value;
            Z3_set_param_value(m_cfg, param, oss.str().c_str());
        }
    };

    /**
       \brief A Context manages all other Z3 objects, global configuration options, etc.
    */
    class context {
        Z3_context m_ctx;
        static void error_handler(Z3_context c, Z3_error_code e) { /* do nothing */ }
        void init(config & c) {
            m_ctx = Z3_mk_context_rc(c);
            Z3_set_error_handler(m_ctx, error_handler);
            Z3_set_ast_print_mode(m_ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
        }
        context(context const & s);
        context & operator=(context const & s);
    public:
        context() { config c; init(c); }
        context(config & c) { init(c); }
        ~context() { Z3_del_context(m_ctx); }
        operator Z3_context() const { return m_ctx; }

        /**
           \brief Auxiliary method used to check for API usage errors.
        */
        void check_error() const {
            Z3_error_code e = Z3_get_error_code(m_ctx);
            if (e != Z3_OK)
                throw exception(Z3_get_error_msg_ex(m_ctx, e));
        }

        void set(char const * param, char const * value) { Z3_update_param_value(m_ctx, param, value); }
        void set(char const * param, bool value) { Z3_update_param_value(m_ctx, param, value ? "true" : "false"); }
        void set(char const * param, int value) { 
            std::ostringstream oss;
            oss << value;
            Z3_update_param_value(m_ctx, param, oss.str().c_str());
        }

        void interrupt() { Z3_interrupt(m_ctx); }

        symbol str_symbol(char const * s);
        symbol int_symbol(int n);

        sort bool_sort();
        sort int_sort();
        sort real_sort();
        sort bv_sort(unsigned sz);
        sort array_sort(sort d, sort r);

        func_decl function(symbol const & name, unsigned arity, sort const * domain, sort const & range);
        func_decl function(char const * name, unsigned arity, sort const * domain, sort const & range);
        func_decl function(char const * name, sort const & domain, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & d5, sort const & range);

        expr constant(symbol const & name, sort const & s);
        expr constant(char const * name, sort const & s);
        expr bool_const(char const * name);
        expr int_const(char const * name);
        expr real_const(char const * name);
        expr bv_const(char const * name, unsigned sz);
        
        expr bool_val(bool b);
        
        expr int_val(int n);
        expr int_val(unsigned n);
        expr int_val(__int64 n);
        expr int_val(__uint64 n);
        expr int_val(char const * n);

        expr real_val(int n, int d);
        expr real_val(int n);
        expr real_val(unsigned n);
        expr real_val(__int64 n);
        expr real_val(__uint64 n);
        expr real_val(char const * n);

        expr bv_val(int n, unsigned sz);
        expr bv_val(unsigned n, unsigned sz);
        expr bv_val(__int64 n, unsigned sz);
        expr bv_val(__uint64 n, unsigned sz);
        expr bv_val(char const * n, unsigned sz);

        expr num_val(int n, sort const & s);
    };

    template<typename T>
    class array {
        T *      m_array;
        unsigned m_size;
        array(array const & s);
        array & operator=(array const & s);
    public:
        array(unsigned sz):m_size(sz) { m_array = new T[sz]; }
        ~array() { delete[] m_array; }
        unsigned size() const { return m_size; }
        T & operator[](unsigned i) { assert(i < m_size); return m_array[i]; }
        T const & operator[](unsigned i) const { assert(i < m_size); return m_array[i]; }
        T const * ptr() const { return m_array; }
        T * ptr() { return m_array; }
    };

    class object {
    protected:
        context * m_ctx;
    public:
        object(context & c):m_ctx(&c) {}
        object(object const & s):m_ctx(s.m_ctx) {}
        context & ctx() const { return *m_ctx; }
        void check_error() const { m_ctx->check_error(); }
        friend void check_context(object const & a, object const & b) { assert(a.m_ctx == b.m_ctx); }
    };

    class symbol : public object {
        Z3_symbol m_sym;
    public:
        symbol(context & c, Z3_symbol s):object(c), m_sym(s) {}
        symbol(symbol const & s):object(s), m_sym(s.m_sym) {}
        symbol & operator=(symbol const & s) { m_ctx = s.m_ctx; m_sym = s.m_sym; return *this; }
        operator Z3_symbol() const { return m_sym; }
        Z3_symbol_kind kind() const { return Z3_get_symbol_kind(ctx(), m_sym); }
        std::string str() const { assert(kind() == Z3_STRING_SYMBOL); return Z3_get_symbol_string(ctx(), m_sym); }
        int to_int() const { assert(kind() == Z3_INT_SYMBOL); return Z3_get_symbol_int(ctx(), m_sym); }
        friend std::ostream & operator<<(std::ostream & out, symbol const & s) { 
            if (s.kind() == Z3_INT_SYMBOL)
                out << "k!" << s.to_int();
            else
                out << s.str().c_str();
            return out;
        }
    };

    class params : public object {
        Z3_params m_params;
    public:
        params(context & c):object(c) { m_params = Z3_mk_params(c); Z3_params_inc_ref(ctx(), m_params); }
        params(params const & s):object(s), m_params(s.m_params) { Z3_params_inc_ref(ctx(), m_params); }
        ~params() { Z3_params_dec_ref(ctx(), m_params); }
        operator Z3_params() const { return m_params; }
        params & operator=(params const & s) { 
            Z3_params_inc_ref(s.ctx(), s.m_params); 
            Z3_params_dec_ref(ctx(), m_params); 
            m_ctx = s.m_ctx; 
            m_params = s.m_params; 
            return *this; 
        }
        void set(char const * k, bool b) { Z3_params_set_bool(ctx(), m_params, ctx().str_symbol(k), b); }
        void set(char const * k, unsigned n) { Z3_params_set_uint(ctx(), m_params, ctx().str_symbol(k), n); }
        void set(char const * k, double n) { Z3_params_set_double(ctx(), m_params, ctx().str_symbol(k), n); }
        void set(char const * k, symbol const & s) { Z3_params_set_symbol(ctx(), m_params, ctx().str_symbol(k), s); }
        friend std::ostream & operator<<(std::ostream & out, params const & p) { out << Z3_params_to_string(p.ctx(), p); return out; }
    };
    
    class ast : public object {
    protected:
        Z3_ast    m_ast;
    public:
        ast(context & c):object(c), m_ast(0) {}
        ast(context & c, Z3_ast n):object(c), m_ast(n) { Z3_inc_ref(ctx(), m_ast); }
        ast(ast const & s):object(s), m_ast(s.m_ast) { Z3_inc_ref(ctx(), m_ast); }
        ~ast() { if (m_ast) Z3_dec_ref(*m_ctx, m_ast); }
        operator Z3_ast() const { return m_ast; }
        operator bool() const { return m_ast != 0; }
        ast & operator=(ast const & s) { Z3_inc_ref(s.ctx(), s.m_ast); if (m_ast) Z3_dec_ref(ctx(), m_ast); m_ctx = s.m_ctx; m_ast = s.m_ast; return *this; }
        Z3_ast_kind kind() const { Z3_ast_kind r = Z3_get_ast_kind(ctx(), m_ast); check_error(); return r; }
        unsigned hash() const { unsigned r = Z3_get_ast_hash(ctx(), m_ast); check_error(); return r; }
        friend std::ostream & operator<<(std::ostream & out, ast const & n) { out << Z3_ast_to_string(n.ctx(), n.m_ast); return out; }

        /**
           \brief Return true if the ASTs are structurally identical.
        */
        friend bool eq(ast const & a, ast const & b) { return Z3_is_eq_ast(a.ctx(), a, b) != 0; }
    };

    class sort : public ast {
    public:
        sort(context & c):ast(c) {}
        sort(context & c, Z3_sort s):ast(c, reinterpret_cast<Z3_ast>(s)) {}
        sort(sort const & s):ast(s) {}
        operator Z3_sort() const { return reinterpret_cast<Z3_sort>(m_ast); }
        sort & operator=(sort const & s) { return static_cast<sort&>(ast::operator=(s)); }
        Z3_sort_kind sort_kind() const { return Z3_get_sort_kind(*m_ctx, *this); }

        bool is_bool() const { return sort_kind() == Z3_BOOL_SORT; }
        bool is_int() const { return sort_kind() == Z3_INT_SORT; }
        bool is_real() const { return sort_kind() == Z3_REAL_SORT; }
        bool is_arith() const { return is_int() || is_real(); }
        bool is_bv() const { return sort_kind() == Z3_BV_SORT; }
        bool is_array() const { return sort_kind() == Z3_ARRAY_SORT; }
        bool is_datatype() const { return sort_kind() == Z3_DATATYPE_SORT; }
        bool is_relation() const { return sort_kind() == Z3_RELATION_SORT; }
        bool is_finite_domain() const { return sort_kind() == Z3_FINITE_DOMAIN_SORT; }

        unsigned bv_size() const { assert(is_bv()); unsigned r = Z3_get_bv_sort_size(ctx(), *this); check_error(); return r; }

        sort array_domain() const { assert(is_array()); Z3_sort s = Z3_get_array_sort_domain(ctx(), *this); check_error(); return sort(ctx(), s); }
        sort array_range() const { assert(is_array()); Z3_sort s = Z3_get_array_sort_range(ctx(), *this); check_error(); return sort(ctx(), s); }
    };

    class func_decl : public ast {
    public:
        func_decl(context & c):ast(c) {}
        func_decl(context & c, Z3_func_decl n):ast(c, reinterpret_cast<Z3_ast>(n)) {}
        func_decl(func_decl const & s):ast(s) {}
        operator Z3_func_decl() const { return reinterpret_cast<Z3_func_decl>(m_ast); }
        func_decl & operator=(func_decl const & s) { return static_cast<func_decl&>(ast::operator=(s)); }
        
        unsigned arity() const { return Z3_get_arity(ctx(), *this); }
        sort domain(unsigned i) const { assert(i < arity()); Z3_sort r = Z3_get_domain(ctx(), *this, i); check_error(); return sort(ctx(), r); }
        sort range() const { Z3_sort r = Z3_get_range(ctx(), *this); check_error(); return sort(ctx(), r); }
        symbol name() const { Z3_symbol s = Z3_get_decl_name(ctx(), *this); check_error(); return symbol(ctx(), s); }
        Z3_decl_kind decl_kind() const { return Z3_get_decl_kind(ctx(), *this); }

        bool is_const() const { return arity() == 0; }

        expr operator()(unsigned n, expr const * args) const;
        expr operator()(expr const & a) const;
        expr operator()(int a) const;
        expr operator()(expr const & a1, expr const & a2) const;
        expr operator()(expr const & a1, int a2) const;
        expr operator()(int a1, expr const & a2) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
    };

    class expr : public ast {
    public:
        expr(context & c):ast(c) {}
        expr(context & c, Z3_ast n):ast(c, reinterpret_cast<Z3_ast>(n)) {}
        expr(expr const & n):ast(n) {}
        expr & operator=(expr const & n) { return static_cast<expr&>(ast::operator=(n)); }

        sort get_sort() const { Z3_sort s = Z3_get_sort(*m_ctx, m_ast); check_error(); return sort(*m_ctx, s); }

        bool is_bool() const { return get_sort().is_bool(); }
        bool is_int() const { return get_sort().is_int(); }
        bool is_real() const { return get_sort().is_real(); }
        bool is_arith() const { return get_sort().is_arith(); }
        bool is_bv() const { return get_sort().is_bv(); }
        bool is_array() const { return get_sort().is_array(); }
        bool is_datatype() const { return get_sort().is_datatype(); }
        bool is_relation() const { return get_sort().is_relation(); }
        bool is_finite_domain() const { return get_sort().is_finite_domain(); }

        bool is_numeral() const { return kind() == Z3_NUMERAL_AST; }
        bool is_app() const { return kind() == Z3_APP_AST || kind() == Z3_NUMERAL_AST; }
        bool is_const() const { return is_app() && num_args() == 0; }
        bool is_quantifier() const { return kind() == Z3_QUANTIFIER_AST; }
        bool is_var() const { return kind() == Z3_VAR_AST; }

        bool is_well_sorted() const { bool r = Z3_is_well_sorted(ctx(), m_ast) != 0; check_error(); return r; }

        operator Z3_app() const { assert(is_app()); return reinterpret_cast<Z3_app>(m_ast); }
        func_decl decl() const { Z3_func_decl f = Z3_get_app_decl(ctx(), *this); check_error(); return func_decl(ctx(), f); }
        unsigned num_args() const { unsigned r = Z3_get_app_num_args(ctx(), *this); check_error(); return r; }
        expr arg(unsigned i) const { Z3_ast r = Z3_get_app_arg(ctx(), *this, i); check_error(); return expr(ctx(), r); }

        expr body() const { assert(is_quantifier()); Z3_ast r = Z3_get_quantifier_body(ctx(), *this); check_error(); return expr(ctx(), r); }

        friend expr operator!(expr const & a) {
            assert(a.is_bool());
            Z3_ast r = Z3_mk_not(a.ctx(), a);
            a.check_error();
            return expr(a.ctx(), r);
        }

        friend expr operator&&(expr const & a, expr const & b) {
            check_context(a, b);
            assert(a.is_bool() && b.is_bool());
            Z3_ast args[2] = { a, b };
            Z3_ast r = Z3_mk_and(a.ctx(), 2, args);
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator&&(expr const & a, bool b) { return a && a.ctx().bool_val(b); }
        friend expr operator&&(bool a, expr const & b) { return b.ctx().bool_val(a) && b; }

        friend expr operator||(expr const & a, expr const & b) {
            check_context(a, b);
            assert(a.is_bool() && b.is_bool());
            Z3_ast args[2] = { a, b };
            Z3_ast r = Z3_mk_or(a.ctx(), 2, args);
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator||(expr const & a, bool b) { return a || a.ctx().bool_val(b); }
        friend expr operator||(bool a, expr const & b) { return b.ctx().bool_val(a) || b; }
        
        friend expr implies(expr const & a, expr const & b) {
            check_context(a, b);
            assert(a.is_bool() && b.is_bool());
            Z3_ast r = Z3_mk_implies(a.ctx(), a, b);
            a.check_error();
            return expr(a.ctx(), r);
        }

        friend expr operator==(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r = Z3_mk_eq(a.ctx(), a, b);
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator==(expr const & a, int b) { assert(a.is_arith() || a.is_bv()); return a == a.ctx().num_val(b, a.get_sort()); }
        friend expr operator==(int a, expr const & b) { assert(b.is_arith() || b.is_bv()); return b.ctx().num_val(a, b.get_sort()) == b; }

        friend expr operator!=(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast args[2] = { a, b };
            Z3_ast r = Z3_mk_distinct(a.ctx(), 2, args);
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator!=(expr const & a, int b) { assert(a.is_arith() || a.is_bv()); return a != a.ctx().num_val(b, a.get_sort()); }
        friend expr operator!=(int a, expr const & b) { assert(b.is_arith() || b.is_bv()); return b.ctx().num_val(a, b.get_sort()) != b; }

        friend expr operator+(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                Z3_ast args[2] = { a, b };
                r = Z3_mk_add(a.ctx(), 2, args);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvadd(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator+(expr const & a, int b) { return a + a.ctx().num_val(b, a.get_sort()); }
        friend expr operator+(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) + b; }

        friend expr operator*(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                Z3_ast args[2] = { a, b };
                r = Z3_mk_mul(a.ctx(), 2, args);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvmul(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator*(expr const & a, int b) { return a * a.ctx().num_val(b, a.get_sort()); }
        friend expr operator*(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) * b; }

        /**
           \brief Power operator
        */
        friend expr pw(expr const & a, expr const & b) {
            assert(a.is_arith() && b.is_arith());
            check_context(a, b);
            Z3_ast r = Z3_mk_power(a.ctx(), a, b);
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr pw(expr const & a, int b) { return pw(a, a.ctx().num_val(b, a.get_sort())); }
        friend expr pw(int a, expr const & b) { return pw(b.ctx().num_val(a, b.get_sort()), b); }

        friend expr operator/(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                r = Z3_mk_div(a.ctx(), a, b);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvsdiv(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator/(expr const & a, int b) { return a / a.ctx().num_val(b, a.get_sort()); }
        friend expr operator/(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) / b; }

        friend expr operator-(expr const & a) {
            Z3_ast r;
            if (a.is_arith()) {
                r = Z3_mk_unary_minus(a.ctx(), a);
            }
            else if (a.is_bv()) {
                r = Z3_mk_bvneg(a.ctx(), a);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }

        friend expr operator-(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                Z3_ast args[2] = { a, b };
                r = Z3_mk_sub(a.ctx(), 2, args);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvsub(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator-(expr const & a, int b) { return a - a.ctx().num_val(b, a.get_sort()); }
        friend expr operator-(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) - a; }

        friend expr operator<=(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                r = Z3_mk_le(a.ctx(), a, b);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvsle(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator<=(expr const & a, int b) { return a <= a.ctx().num_val(b, a.get_sort()); }
        friend expr operator<=(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) <= a; }

        friend expr operator>=(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                r = Z3_mk_ge(a.ctx(), a, b);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvsge(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator>=(expr const & a, int b) { return a >= a.ctx().num_val(b, a.get_sort()); }
        friend expr operator>=(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) >= a; }

        friend expr operator<(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                r = Z3_mk_lt(a.ctx(), a, b);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvslt(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator<(expr const & a, int b) { return a < a.ctx().num_val(b, a.get_sort()); }
        friend expr operator<(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) < a; }
        
        friend expr operator>(expr const & a, expr const & b) {
            check_context(a, b);
            Z3_ast r;
            if (a.is_arith() && b.is_arith()) {
                r = Z3_mk_gt(a.ctx(), a, b);
            }
            else if (a.is_bv() && b.is_bv()) {
                r = Z3_mk_bvsgt(a.ctx(), a, b);
            }
            else {
                // operator is not supported by given arguments.
                assert(false);
            }
            a.check_error();
            return expr(a.ctx(), r);
        }
        friend expr operator>(expr const & a, int b) { return a > a.ctx().num_val(b, a.get_sort()); }
        friend expr operator>(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) > a; }

        friend expr operator&(expr const & a, expr const & b) { check_context(a, b); Z3_ast r = Z3_mk_bvand(a.ctx(), a, b); return expr(a.ctx(), r); }
        friend expr operator&(expr const & a, int b) { return a & a.ctx().num_val(b, a.get_sort()); }
        friend expr operator&(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) & b; }

        friend expr operator^(expr const & a, expr const & b) { check_context(a, b); Z3_ast r = Z3_mk_bvxor(a.ctx(), a, b); return expr(a.ctx(), r); }
        friend expr operator^(expr const & a, int b) { return a ^ a.ctx().num_val(b, a.get_sort()); }
        friend expr operator^(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) ^ b; }

        friend expr operator|(expr const & a, expr const & b) { check_context(a, b); Z3_ast r = Z3_mk_bvor(a.ctx(), a, b); return expr(a.ctx(), r); }
        friend expr operator|(expr const & a, int b) { return a | a.ctx().num_val(b, a.get_sort()); }
        friend expr operator|(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) | b; }

        friend expr operator~(expr const & a) { Z3_ast r = Z3_mk_bvnot(a.ctx(), a); return expr(a.ctx(), r); }

        expr simplify() const { Z3_ast r = Z3_simplify(ctx(), m_ast); check_error(); return expr(ctx(), r); }
        expr simplify(params const & p) const { Z3_ast r = Z3_simplify_ex(ctx(), m_ast, p); check_error(); return expr(ctx(), r); }
    };
    
    /**                                        
       \brief Wraps a Z3_ast as an expr object. It also checks for errors.
       This function allows the user to use the whole C API with the C++ layer defined in this file.
    */
    inline expr to_expr(context & c, Z3_ast a) {
        c.check_error();
        assert(Z3_get_ast_kind(c, a) == Z3_APP_AST || 
               Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST || 
               Z3_get_ast_kind(c, a) == Z3_VAR_AST || 
               Z3_get_ast_kind(c, a) == Z3_QUANTIFIER_AST);
        return expr(c, a);
    }

    inline sort to_sort(context & c, Z3_sort s) {
        c.check_error();
        return sort(c, s);
    }

    inline func_decl to_func_decl(context & c, Z3_func_decl f) {
        c.check_error();
        return func_decl(c, f);
    }

    /**
       \brief unsigned less than or equal to operator for bitvectors.
    */
    inline expr ule(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvule(a.ctx(), a, b)); }
    inline expr ule(expr const & a, int b) { return ule(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ule(int a, expr const & b) { return ule(b.ctx().num_val(a, b.get_sort()), a); }
    /**
       \brief unsigned less than operator for bitvectors.
    */
    inline expr ult(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvult(a.ctx(), a, b)); }
    inline expr ult(expr const & a, int b) { return ult(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ult(int a, expr const & b) { return ult(b.ctx().num_val(a, b.get_sort()), a); }
    /**
       \brief unsigned greater than or equal to operator for bitvectors.
    */
    inline expr uge(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvuge(a.ctx(), a, b)); }
    inline expr uge(expr const & a, int b) { return uge(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr uge(int a, expr const & b) { return uge(b.ctx().num_val(a, b.get_sort()), a); }
    /**
       \brief unsigned greater than operator for bitvectors.
    */
    inline expr ugt(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvugt(a.ctx(), a, b)); }
    inline expr ugt(expr const & a, int b) { return ugt(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ugt(int a, expr const & b) { return ugt(b.ctx().num_val(a, b.get_sort()), a); }
    /**
       \brief unsigned division operator for bitvectors.
    */
    inline expr udiv(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvudiv(a.ctx(), a, b)); }
    inline expr udiv(expr const & a, int b) { return udiv(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr udiv(int a, expr const & b) { return udiv(b.ctx().num_val(a, b.get_sort()), a); }

    // Basic functions for creating quantified formulas.
    // The C API should be used for creating quantifiers with patterns, weights, many variables, etc.
    inline expr forall(expr const & x, expr const & b) {
        check_context(x, b);
        Z3_app vars[] = {(Z3_app) x}; 
        Z3_ast r = Z3_mk_forall_const(b.ctx(), 0, 1, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr forall(expr const & x1, expr const & x2, expr const & b) {
        check_context(x1, b); check_context(x2, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2}; 
        Z3_ast r = Z3_mk_forall_const(b.ctx(), 0, 2, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr forall(expr const & x1, expr const & x2, expr const & x3, expr const & b) {
        check_context(x1, b); check_context(x2, b); check_context(x3, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3 }; 
        Z3_ast r = Z3_mk_forall_const(b.ctx(), 0, 3, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr forall(expr const & x1, expr const & x2, expr const & x3, expr const & x4, expr const & b) {
        check_context(x1, b); check_context(x2, b); check_context(x3, b); check_context(x4, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3, (Z3_app) x4 }; 
        Z3_ast r = Z3_mk_forall_const(b.ctx(), 0, 4, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr exists(expr const & x, expr const & b) {
        check_context(x, b);
        Z3_app vars[] = {(Z3_app) x}; 
        Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 1, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr exists(expr const & x1, expr const & x2, expr const & b) {
        check_context(x1, b); check_context(x2, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2}; 
        Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 2, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr exists(expr const & x1, expr const & x2, expr const & x3, expr const & b) {
        check_context(x1, b); check_context(x2, b); check_context(x3, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3 }; 
        Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 3, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr exists(expr const & x1, expr const & x2, expr const & x3, expr const & x4, expr const & b) {
        check_context(x1, b); check_context(x2, b); check_context(x3, b); check_context(x4, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3, (Z3_app) x4 }; 
        Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 4, vars, 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    
    template<typename T> class cast_ast;

    template<> class cast_ast<ast> {
    public:
        ast operator()(context & c, Z3_ast a) { return ast(c, a); }
    };

    template<> class cast_ast<expr> {
    public:
        expr operator()(context & c, Z3_ast a) { 
            assert(Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST ||
                   Z3_get_ast_kind(c, a) == Z3_APP_AST || 
                   Z3_get_ast_kind(c, a) == Z3_QUANTIFIER_AST || 
                   Z3_get_ast_kind(c, a) == Z3_VAR_AST);
            return expr(c, a);
        }
    };

    template<> class cast_ast<sort> {
    public:
        sort operator()(context & c, Z3_ast a) { 
            assert(Z3_get_ast_kind(c, a) == Z3_SORT_AST);
            return sort(c, reinterpret_cast<Z3_sort>(a));
        }
    };

    template<> class cast_ast<func_decl> {
    public:
        func_decl operator()(context & c, Z3_ast a) { 
            assert(Z3_get_ast_kind(c, a) == Z3_FUNC_DECL_AST);
            return func_decl(c, reinterpret_cast<Z3_func_decl>(a));
        }
    };

    template<typename T>
    class ast_vector_tpl : public object {
        Z3_ast_vector m_vector;
        void init(Z3_ast_vector v) { Z3_ast_vector_inc_ref(ctx(), v); m_vector = v; }
    public:
        ast_vector_tpl(context & c):object(c) { init(Z3_mk_ast_vector(c)); }
        ast_vector_tpl(context & c, Z3_ast_vector v):object(c) { init(v); }
        ast_vector_tpl(ast_vector_tpl const & s):object(s), m_vector(s.m_vector) { Z3_ast_vector_inc_ref(ctx(), m_vector); }
        ~ast_vector_tpl() { Z3_ast_vector_dec_ref(ctx(), m_vector); }
        operator Z3_ast_vector() const { return m_vector; }
        unsigned size() const { return Z3_ast_vector_size(ctx(), m_vector); }
        T operator[](unsigned i) const { Z3_ast r = Z3_ast_vector_get(ctx(), m_vector, i); check_error(); return cast_ast<T>()(ctx(), r); }
        void push_back(T const & e) { Z3_ast_vector_push(ctx(), m_vector, e); check_error(); }
        void resize(unsigned sz) { Z3_ast_vector_resize(ctx(), m_vector, sz); check_error(); }
        T back() const { return operator[](size() - 1); }
        void pop_back() { assert(size() > 0); resize(size() - 1); }
        bool empty() const { return size() == 0; }
        ast_vector_tpl & operator=(ast_vector_tpl const & s) { 
            Z3_ast_vector_inc_ref(s.ctx(), s.m_vector); 
            Z3_ast_vector_dec_ref(ctx(), m_vector);
            m_ctx = s.m_ctx; 
            m_vector = s.m_vector;
            return *this; 
        }
        friend std::ostream & operator<<(std::ostream & out, ast_vector_tpl const & v) { out << Z3_ast_vector_to_string(v.ctx(), v); return out; }
    };

    typedef ast_vector_tpl<ast>       ast_vector;
    typedef ast_vector_tpl<expr>      expr_vector;
    typedef ast_vector_tpl<sort>      sort_vector;
    typedef ast_vector_tpl<func_decl> func_decl_vector;

    class func_entry : public object {
        Z3_func_entry m_entry;
        void init(Z3_func_entry e) {
            m_entry = e;
            Z3_func_entry_inc_ref(ctx(), m_entry);
        }
    public:
        func_entry(context & c, Z3_func_entry e):object(c) { init(e); }
        func_entry(func_entry const & s):object(s) { init(s.m_entry); }
        ~func_entry() { Z3_func_entry_dec_ref(ctx(), m_entry); }
        operator Z3_func_entry() const { return m_entry; }
        func_entry & operator=(func_entry const & s) {
            Z3_func_entry_inc_ref(s.ctx(), s.m_entry);
            Z3_func_entry_dec_ref(ctx(), m_entry);
            m_ctx = s.m_ctx; 
            m_entry = s.m_entry;
            return *this; 
        }
        expr value() const { Z3_ast r = Z3_func_entry_get_value(ctx(), m_entry); check_error(); return expr(ctx(), r); }
        unsigned num_args() const { unsigned r = Z3_func_entry_get_num_args(ctx(), m_entry); check_error(); return r; }
        expr arg(unsigned i) const { Z3_ast r = Z3_func_entry_get_arg(ctx(), m_entry, i); check_error(); return expr(ctx(), r); }
    };

    class func_interp : public object {
        Z3_func_interp m_interp;
        void init(Z3_func_interp e) {
            m_interp = e;
            Z3_func_interp_inc_ref(ctx(), m_interp);
        }
    public:
        func_interp(context & c, Z3_func_interp e):object(c) { init(e); }
        func_interp(func_interp const & s):object(s) { init(s.m_interp); }
        ~func_interp() { Z3_func_interp_dec_ref(ctx(), m_interp); }
        operator Z3_func_interp() const { return m_interp; }
        func_interp & operator=(func_interp const & s) {
            Z3_func_interp_inc_ref(s.ctx(), s.m_interp);
            Z3_func_interp_dec_ref(ctx(), m_interp);
            m_ctx = s.m_ctx; 
            m_interp = s.m_interp;
            return *this; 
        }
        expr else_value() const { Z3_ast r = Z3_func_interp_get_else(ctx(), m_interp); check_error(); return expr(ctx(), r); }
        unsigned num_entries() const { unsigned r = Z3_func_interp_get_num_entries(ctx(), m_interp); check_error(); return r; }
        func_entry entry(unsigned i) const { Z3_func_entry e = Z3_func_interp_get_entry(ctx(), m_interp, i); check_error(); return func_entry(ctx(), e); }
    };

    class model : public object {
        Z3_model m_model;
        void init(Z3_model m) {
            m_model = m;
            Z3_model_inc_ref(ctx(), m);
        }
    public:
        model(context & c, Z3_model m):object(c) { init(m); }
        model(model const & s):object(s) { init(s.m_model); }
        ~model() { Z3_model_dec_ref(ctx(), m_model); }
        operator Z3_model() const { return m_model; }
        model & operator=(model const & s) {
            Z3_model_inc_ref(s.ctx(), s.m_model);
            Z3_model_dec_ref(ctx(), m_model);
            m_ctx = s.m_ctx; 
            m_model = s.m_model;
            return *this; 
        }
        
        expr eval(expr const & n, bool model_completion=false) const {
            check_context(*this, n);
            Z3_ast r;
            Z3_bool status = Z3_model_eval(ctx(), m_model, n, model_completion, &r);
            check_error();
            if (status == Z3_FALSE)
                throw exception("failed to evaluate expression");
            return expr(ctx(), r);
        }
        
        unsigned num_consts() const { return Z3_model_get_num_consts(ctx(), m_model); }
        unsigned num_funcs() const { return Z3_model_get_num_funcs(ctx(), m_model); }
        func_decl get_const_decl(unsigned i) const { Z3_func_decl r = Z3_model_get_const_decl(ctx(), m_model, i); check_error(); return func_decl(ctx(), r); }
        func_decl get_func_decl(unsigned i) const { Z3_func_decl r = Z3_model_get_func_decl(ctx(), m_model, i); check_error(); return func_decl(ctx(), r); }
        unsigned size() const { return num_consts() + num_funcs(); }
        func_decl operator[](unsigned i) const { return i < num_consts() ? get_const_decl(i) : get_func_decl(i - num_consts()); }

        expr get_const_interp(func_decl c) const {
            check_context(*this, c);
            Z3_ast r = Z3_model_get_const_interp(ctx(), m_model, c);
            check_error();
            return expr(ctx(), r);
        }
        func_interp get_func_interp(func_decl f) const { 
            check_context(*this, f);
            Z3_func_interp r = Z3_model_get_func_interp(ctx(), m_model, f);
            check_error();
            return func_interp(ctx(), r);
        }

        friend std::ostream & operator<<(std::ostream & out, model const & m) { out << Z3_model_to_string(m.ctx(), m); return out; }
    };

    class stats : public object {
        Z3_stats m_stats;
        void init(Z3_stats e) {
            m_stats = e;
            Z3_stats_inc_ref(ctx(), m_stats);
        }
    public:
        stats(context & c):object(c), m_stats(0) {}
        stats(context & c, Z3_stats e):object(c) { init(e); }
        stats(stats const & s):object(s) { init(s.m_stats); }
        ~stats() { if (m_stats) Z3_stats_dec_ref(ctx(), m_stats); }
        operator Z3_stats() const { return m_stats; }
        stats & operator=(stats const & s) {
            Z3_stats_inc_ref(s.ctx(), s.m_stats);
            if (m_stats) Z3_stats_dec_ref(ctx(), m_stats);
            m_ctx = s.m_ctx; 
            m_stats = s.m_stats;
            return *this; 
        }
        unsigned size() const { return Z3_stats_size(ctx(), m_stats); }
        std::string key(unsigned i) const { Z3_string s = Z3_stats_get_key(ctx(), m_stats, i); check_error(); return s; }
        bool is_uint(unsigned i) const { Z3_bool r = Z3_stats_is_uint(ctx(), m_stats, i); check_error(); return r != 0; }
        bool is_double(unsigned i) const { Z3_bool r = Z3_stats_is_double(ctx(), m_stats, i); check_error(); return r != 0; }
        unsigned uint_value(unsigned i) const { unsigned r = Z3_stats_get_uint_value(ctx(), m_stats, i); check_error(); return r; }
        double double_value(unsigned i) const { double r = Z3_stats_get_double_value(ctx(), m_stats, i); check_error(); return r; }
        friend std::ostream & operator<<(std::ostream & out, stats const & s) { out << Z3_stats_to_string(s.ctx(), s); return out; }
    };

    enum check_result {
        unsat, sat, unknown
    };

    inline std::ostream & operator<<(std::ostream & out, check_result r) { 
        if (r == unsat) out << "unsat";
        else if (r == sat) out << "sat";
        else out << "unknown";
        return out;
    }

    inline check_result to_check_result(Z3_lbool l) {
        if (l == Z3_L_TRUE) return sat;
        else if (l == Z3_L_FALSE) return unsat;
        return unknown;
    }

    class solver : public object {
        Z3_solver m_solver;
        void init(Z3_solver s) {
            m_solver = s;
            Z3_solver_inc_ref(ctx(), s);
        }
    public:
        solver(context & c):object(c) { init(Z3_mk_solver(c)); }
        solver(context & c, Z3_solver s):object(c) { init(s); }
        solver(context & c, char const * logic):object(c) { init(Z3_mk_solver_for_logic(c, c.str_symbol(logic))); }
        solver(solver const & s):object(s) { init(s.m_solver); }
        ~solver() { Z3_solver_dec_ref(ctx(), m_solver); }
        operator Z3_solver() const { return m_solver; }
        solver & operator=(solver const & s) {
            Z3_solver_inc_ref(s.ctx(), s.m_solver);
            Z3_solver_dec_ref(ctx(), m_solver);
            m_ctx = s.m_ctx; 
            m_solver = s.m_solver;
            return *this; 
        }
        void set(params const & p) { Z3_solver_set_params(ctx(), m_solver, p); check_error(); }
        void push() { Z3_solver_push(ctx(), m_solver); check_error(); }
        void pop(unsigned n = 1) { Z3_solver_pop(ctx(), m_solver, n); check_error(); }
        void reset() { Z3_solver_reset(ctx(), m_solver); check_error(); }
        void add(expr const & e) { assert(e.is_bool()); Z3_solver_assert(ctx(), m_solver, e); check_error(); }
        void add(expr const & e, expr const & p) { 
            assert(e.is_bool()); assert(p.is_bool()); assert(p.is_const()); 
            Z3_solver_assert_and_track(ctx(), m_solver, e, p); 
            check_error(); 
        }
        void add(expr const & e, char const * p) {
            add(e, ctx().bool_const(p));
        }
        check_result check() { Z3_lbool r = Z3_solver_check(ctx(), m_solver); check_error(); return to_check_result(r); }
        check_result check(unsigned n, expr * const assumptions) {
            array<Z3_ast> _assumptions(n);
            for (unsigned i = 0; i < n; i++) {
                check_context(*this, assumptions[i]);
                _assumptions[i] = assumptions[i];
            }
            Z3_lbool r = Z3_solver_check_assumptions(ctx(), m_solver, n, _assumptions.ptr()); 
            check_error(); 
            return to_check_result(r); 
        }
        check_result check(expr_vector assumptions) { 
            unsigned n = assumptions.size();
            array<Z3_ast> _assumptions(n);
            for (unsigned i = 0; i < n; i++) {
                check_context(*this, assumptions[i]);
                _assumptions[i] = assumptions[i];
            }
            Z3_lbool r = Z3_solver_check_assumptions(ctx(), m_solver, n, _assumptions.ptr()); 
            check_error(); 
            return to_check_result(r); 
        }
        model get_model() const { Z3_model m = Z3_solver_get_model(ctx(), m_solver); check_error(); return model(ctx(), m); }
        std::string reason_unknown() const { Z3_string r = Z3_solver_get_reason_unknown(ctx(), m_solver); check_error(); return r; }
        stats statistics() const { Z3_stats r = Z3_solver_get_statistics(ctx(), m_solver); check_error(); return stats(ctx(), r); }
        expr_vector unsat_core() const { Z3_ast_vector r = Z3_solver_get_unsat_core(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector assertions() const { Z3_ast_vector r = Z3_solver_get_assertions(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr proof() const { Z3_ast r = Z3_solver_get_proof(ctx(), m_solver); check_error(); return expr(ctx(), r); }
        friend std::ostream & operator<<(std::ostream & out, solver const & s) { out << Z3_solver_to_string(s.ctx(), s); return out; }
    };

    class goal : public object {
        Z3_goal m_goal;
        void init(Z3_goal s) {
            m_goal = s;
            Z3_goal_inc_ref(ctx(), s);
        }
    public:
        goal(context & c, bool models=true, bool unsat_cores=false, bool proofs=false):object(c) { init(Z3_mk_goal(c, models, unsat_cores, proofs)); }
        goal(context & c, Z3_goal s):object(c) { init(s); }
        goal(goal const & s):object(s) { init(s.m_goal); }
        ~goal() { Z3_goal_dec_ref(ctx(), m_goal); }
        operator Z3_goal() const { return m_goal; }
        goal & operator=(goal const & s) {
            Z3_goal_inc_ref(s.ctx(), s.m_goal);
            Z3_goal_dec_ref(ctx(), m_goal);
            m_ctx = s.m_ctx; 
            m_goal = s.m_goal;
            return *this; 
        }
        void add(expr const & f) { check_context(*this, f); Z3_goal_assert(ctx(), m_goal, f); check_error(); }
        unsigned size() const { return Z3_goal_size(ctx(), m_goal); }
        expr operator[](unsigned i) const { Z3_ast r = Z3_goal_formula(ctx(), m_goal, i); check_error(); return expr(ctx(), r); }
        Z3_goal_prec precision() const { return Z3_goal_precision(ctx(), m_goal); }
        bool inconsistent() const { return Z3_goal_inconsistent(ctx(), m_goal) != 0; }
        unsigned depth() const { return Z3_goal_depth(ctx(), m_goal); } 
        void reset() { Z3_goal_reset(ctx(), m_goal); }
        unsigned num_exprs() const { return Z3_goal_num_exprs(ctx(), m_goal); }
        bool is_decided_sat() const { return Z3_goal_is_decided_sat(ctx(), m_goal) != 0; }        
        bool is_decided_unsat() const { return Z3_goal_is_decided_unsat(ctx(), m_goal) != 0; }        
        friend std::ostream & operator<<(std::ostream & out, goal const & g) { out << Z3_goal_to_string(g.ctx(), g); return out; }
    };

    class apply_result : public object {
        Z3_apply_result m_apply_result;
        void init(Z3_apply_result s) {
            m_apply_result = s;
            Z3_apply_result_inc_ref(ctx(), s);
        }
    public:
        apply_result(context & c, Z3_apply_result s):object(c) { init(s); }
        apply_result(apply_result const & s):object(s) { init(s.m_apply_result); }
        ~apply_result() { Z3_apply_result_dec_ref(ctx(), m_apply_result); }
        operator Z3_apply_result() const { return m_apply_result; }
        apply_result & operator=(apply_result const & s) {
            Z3_apply_result_inc_ref(s.ctx(), s.m_apply_result);
            Z3_apply_result_dec_ref(ctx(), m_apply_result);
            m_ctx = s.m_ctx; 
            m_apply_result = s.m_apply_result;
            return *this; 
        }
        unsigned size() const { return Z3_apply_result_get_num_subgoals(ctx(), m_apply_result); }
        goal operator[](unsigned i) const { Z3_goal r = Z3_apply_result_get_subgoal(ctx(), m_apply_result, i); check_error(); return goal(ctx(), r); }
        goal operator[](int i) const { assert(i >= 0); return this->operator[](static_cast<unsigned>(i)); }
        model convert_model(model const & m, unsigned i = 0) const { 
            check_context(*this, m); 
            Z3_model new_m = Z3_apply_result_convert_model(ctx(), m_apply_result, i, m);
            check_error();
            return model(ctx(), new_m);
        }
        friend std::ostream & operator<<(std::ostream & out, apply_result const & r) { out << Z3_apply_result_to_string(r.ctx(), r); return out; }
    };

    class tactic : public object {
        Z3_tactic m_tactic;
        void init(Z3_tactic s) {
            m_tactic = s;
            Z3_tactic_inc_ref(ctx(), s);
        }
    public:
        tactic(context & c, char const * name):object(c) { Z3_tactic r = Z3_mk_tactic(c, name); check_error(); init(r); }
        tactic(context & c, Z3_tactic s):object(c) { init(s); }
        tactic(tactic const & s):object(s) { init(s.m_tactic); }
        ~tactic() { Z3_tactic_dec_ref(ctx(), m_tactic); }
        operator Z3_tactic() const { return m_tactic; }
        tactic & operator=(tactic const & s) {
            Z3_tactic_inc_ref(s.ctx(), s.m_tactic);
            Z3_tactic_dec_ref(ctx(), m_tactic);
            m_ctx = s.m_ctx; 
            m_tactic = s.m_tactic;
            return *this; 
        }
        solver mk_solver() const { Z3_solver r = Z3_mk_solver_from_tactic(ctx(), m_tactic); check_error(); return solver(ctx(), r);  }
        apply_result apply(goal const & g) const { 
            check_context(*this, g);
            Z3_apply_result r = Z3_tactic_apply(ctx(), m_tactic, g); 
            check_error(); 
            return apply_result(ctx(), r); 
        }
        apply_result operator()(goal const & g) const {
            return apply(g);
        }
        std::string help() const { char const * r = Z3_tactic_get_help(ctx(), m_tactic); check_error();  return r; }
        friend tactic operator&(tactic const & t1, tactic const & t2) {
            check_context(t1, t2);
            Z3_tactic r = Z3_tactic_and_then(t1.ctx(), t1, t2);
            t1.check_error();
            return tactic(t1.ctx(), r);
        }
        friend tactic operator|(tactic const & t1, tactic const & t2) {
            check_context(t1, t2);
            Z3_tactic r = Z3_tactic_or_else(t1.ctx(), t1, t2);
            t1.check_error();
            return tactic(t1.ctx(), r);
        }
        friend tactic repeat(tactic const & t, unsigned max=UINT_MAX) {
            Z3_tactic r = Z3_tactic_repeat(t.ctx(), t, max);
            t.check_error();
            return tactic(t.ctx(), r);
        }
        friend tactic with(tactic const & t, params const & p) {
            Z3_tactic r = Z3_tactic_using_params(t.ctx(), t, p);
            t.check_error();
            return tactic(t.ctx(), r);
        }
        friend tactic try_for(tactic const & t, unsigned ms) {
            Z3_tactic r = Z3_tactic_try_for(t.ctx(), t, ms);
            t.check_error();
            return tactic(t.ctx(), r);
        }
    };

    class probe : public object {
        Z3_probe m_probe;
        void init(Z3_probe s) {
            m_probe = s;
            Z3_probe_inc_ref(ctx(), s);
        }
    public:
        probe(context & c, char const * name):object(c) { Z3_probe r = Z3_mk_probe(c, name); check_error(); init(r); }
        probe(context & c, double val):object(c) { Z3_probe r = Z3_probe_const(c, val); check_error(); init(r); }
        probe(context & c, Z3_probe s):object(c) { init(s); }
        probe(probe const & s):object(s) { init(s.m_probe); }
        ~probe() { Z3_probe_dec_ref(ctx(), m_probe); }
        operator Z3_probe() const { return m_probe; }
        probe & operator=(probe const & s) {
            Z3_probe_inc_ref(s.ctx(), s.m_probe);
            Z3_probe_dec_ref(ctx(), m_probe);
            m_ctx = s.m_ctx; 
            m_probe = s.m_probe;
            return *this; 
        }
        double apply(goal const & g) const { double r = Z3_probe_apply(ctx(), m_probe, g); check_error(); return r; }
        double operator()(goal const & g) const { return apply(g); }
        friend probe operator<=(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_le(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator<=(probe const & p1, double p2) { return p1 <= probe(p1.ctx(), p2); }
        friend probe operator<=(double p1, probe const & p2) { return probe(p2.ctx(), p1) <= p2; }
        friend probe operator>=(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_ge(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator>=(probe const & p1, double p2) { return p1 >= probe(p1.ctx(), p2); }
        friend probe operator>=(double p1, probe const & p2) { return probe(p2.ctx(), p1) >= p2; }
        friend probe operator<(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_lt(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator<(probe const & p1, double p2) { return p1 < probe(p1.ctx(), p2); }
        friend probe operator<(double p1, probe const & p2) { return probe(p2.ctx(), p1) < p2; }
        friend probe operator>(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_gt(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator>(probe const & p1, double p2) { return p1 > probe(p1.ctx(), p2); }
        friend probe operator>(double p1, probe const & p2) { return probe(p2.ctx(), p1) > p2; }
        friend probe operator==(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_eq(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator==(probe const & p1, double p2) { return p1 == probe(p1.ctx(), p2); }
        friend probe operator==(double p1, probe const & p2) { return probe(p2.ctx(), p1) == p2; }
        friend probe operator&&(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_and(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator||(probe const & p1, probe const & p2) { 
            check_context(p1, p2); Z3_probe r = Z3_probe_or(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r); 
        }
        friend probe operator!(probe const & p) {
            Z3_probe r = Z3_probe_not(p.ctx(), p); p.check_error(); return probe(p.ctx(), r); 
        }
    };

    inline tactic fail_if(probe const & p) {
        Z3_tactic r = Z3_tactic_fail_if(p.ctx(), p);
        p.check_error();
        return tactic(p.ctx(), r);
    }
    inline tactic when(probe const & p, tactic const & t) {
        check_context(p, t);
        Z3_tactic r = Z3_tactic_when(t.ctx(), p, t);
        t.check_error();
        return tactic(t.ctx(), r);
    }
    inline tactic cond(probe const & p, tactic const & t1, tactic const & t2) {
        check_context(p, t1); check_context(p, t2);
        Z3_tactic r = Z3_tactic_cond(t1.ctx(), p, t1, t2);
        t1.check_error();
        return tactic(t1.ctx(), r);
    }

    inline symbol context::str_symbol(char const * s) { Z3_symbol r = Z3_mk_string_symbol(m_ctx, s); check_error(); return symbol(*this, r); }
    inline symbol context::int_symbol(int n) { Z3_symbol r = Z3_mk_int_symbol(m_ctx, n); check_error(); return symbol(*this, r); }

    inline sort context::bool_sort() { Z3_sort s = Z3_mk_bool_sort(m_ctx); check_error(); return sort(*this, s); }
    inline sort context::int_sort() { Z3_sort s = Z3_mk_int_sort(m_ctx); check_error(); return sort(*this, s); }
    inline sort context::real_sort() { Z3_sort s = Z3_mk_real_sort(m_ctx); check_error(); return sort(*this, s); }
    inline sort context::bv_sort(unsigned sz) { Z3_sort s = Z3_mk_bv_sort(m_ctx, sz); check_error(); return sort(*this, s); }
    inline sort context::array_sort(sort d, sort r) { Z3_sort s = Z3_mk_array_sort(m_ctx, d, r); check_error(); return sort(*this, s); }

    inline func_decl context::function(symbol const & name, unsigned arity, sort const * domain, sort const & range) {
        array<Z3_sort> args(arity);
        for (unsigned i = 0; i < arity; i++) {
            check_context(domain[i], range);
            args[i] = domain[i];
        }
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, name, arity, args.ptr(), range);
        check_error();
        return func_decl(*this, f);
    }

    inline func_decl context::function(char const * name, unsigned arity, sort const * domain, sort const & range) {
        return function(range.ctx().str_symbol(name), arity, domain, range);
    }
    
    inline func_decl context::function(char const * name, sort const & domain, sort const & range) {
        check_context(domain, range);
        Z3_sort args[1] = { domain };
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, str_symbol(name), 1, args, range);
        check_error();
        return func_decl(*this, f);
    }

    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & range) {
        check_context(d1, range); check_context(d2, range);
        Z3_sort args[2] = { d1, d2 };
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, str_symbol(name), 2, args, range);
        check_error();
        return func_decl(*this, f);
    }

    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & range) {
        check_context(d1, range); check_context(d2, range); check_context(d3, range);
        Z3_sort args[3] = { d1, d2, d3 };
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, str_symbol(name), 3, args, range);
        check_error();
        return func_decl(*this, f);
    }

    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & range) {
        check_context(d1, range); check_context(d2, range); check_context(d3, range); check_context(d4, range);
        Z3_sort args[4] = { d1, d2, d3, d4 };
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, str_symbol(name), 4, args, range);
        check_error();
        return func_decl(*this, f);
    }
    
    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & d5, sort const & range) {
        check_context(d1, range); check_context(d2, range); check_context(d3, range); check_context(d4, range); check_context(d5, range);
        Z3_sort args[5] = { d1, d2, d3, d4, d5 };
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, str_symbol(name), 5, args, range);
        check_error();
        return func_decl(*this, f);
    }

    inline expr context::constant(symbol const & name, sort const & s) {
        Z3_ast r = Z3_mk_const(m_ctx, name, s); 
        check_error(); 
        return expr(*this, r); 
    }
    inline expr context::constant(char const * name, sort const & s) { return constant(str_symbol(name), s); }
    inline expr context::bool_const(char const * name) { return constant(name, bool_sort()); }
    inline expr context::int_const(char const * name) { return constant(name, int_sort()); }
    inline expr context::real_const(char const * name) { return constant(name, real_sort()); }
    inline expr context::bv_const(char const * name, unsigned sz) { return constant(name, bv_sort(sz)); }

    inline expr context::bool_val(bool b) { return b ? expr(*this, Z3_mk_true(m_ctx)) : expr(*this, Z3_mk_false(m_ctx)); }

    inline expr context::int_val(int n) { Z3_ast r = Z3_mk_int(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(unsigned n) { Z3_ast r = Z3_mk_unsigned_int(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(__int64 n) { Z3_ast r = Z3_mk_int64(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(__uint64 n) { Z3_ast r = Z3_mk_unsigned_int64(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(char const * n) { Z3_ast r = Z3_mk_numeral(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }

    inline expr context::real_val(int n, int d) { Z3_ast r = Z3_mk_real(m_ctx, n, d); check_error(); return expr(*this, r); }
    inline expr context::real_val(int n) { Z3_ast r = Z3_mk_int(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(unsigned n) { Z3_ast r = Z3_mk_unsigned_int(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(__int64 n) { Z3_ast r = Z3_mk_int64(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(__uint64 n) { Z3_ast r = Z3_mk_unsigned_int64(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(char const * n) { Z3_ast r = Z3_mk_numeral(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }

    inline expr context::bv_val(int n, unsigned sz) { Z3_ast r = Z3_mk_int(m_ctx, n, bv_sort(sz)); check_error(); return expr(*this, r); }
    inline expr context::bv_val(unsigned n, unsigned sz) { Z3_ast r = Z3_mk_unsigned_int(m_ctx, n, bv_sort(sz)); check_error(); return expr(*this, r); }
    inline expr context::bv_val(__int64 n, unsigned sz) { Z3_ast r = Z3_mk_int64(m_ctx, n, bv_sort(sz)); check_error(); return expr(*this, r); }
    inline expr context::bv_val(__uint64 n, unsigned sz) { Z3_ast r = Z3_mk_unsigned_int64(m_ctx, n, bv_sort(sz)); check_error(); return expr(*this, r); }
    inline expr context::bv_val(char const * n, unsigned sz) { Z3_ast r = Z3_mk_numeral(m_ctx, n, bv_sort(sz)); check_error(); return expr(*this, r); }

    inline expr context::num_val(int n, sort const & s) { Z3_ast r = Z3_mk_int(m_ctx, n, s); check_error(); return expr(*this, r); }

    inline expr func_decl::operator()(unsigned n, expr const * args) const {
        array<Z3_ast> _args(n);
        for (unsigned i = 0; i < n; i++) {
            check_context(*this, args[i]);
            _args[i] = args[i];
        }
        Z3_ast r = Z3_mk_app(ctx(), *this, n, _args.ptr());
        check_error();
        return expr(ctx(), r);
    
    }
    inline expr func_decl::operator()(expr const & a) const {
        check_context(*this, a);
        Z3_ast args[1] = { a };
        Z3_ast r = Z3_mk_app(ctx(), *this, 1, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(int a) const {
        Z3_ast args[1] = { ctx().num_val(a, domain(0)) };
        Z3_ast r = Z3_mk_app(ctx(), *this, 1, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2) const {
        check_context(*this, a1); check_context(*this, a2);
        Z3_ast args[2] = { a1, a2 };
        Z3_ast r = Z3_mk_app(ctx(), *this, 2, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(expr const & a1, int a2) const {
        check_context(*this, a1); 
        Z3_ast args[2] = { a1, ctx().num_val(a2, domain(1)) };
        Z3_ast r = Z3_mk_app(ctx(), *this, 2, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(int a1, expr const & a2) const {
        check_context(*this, a2);
        Z3_ast args[2] = { ctx().num_val(a1, domain(0)), a2 };
        Z3_ast r = Z3_mk_app(ctx(), *this, 2, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2, expr const & a3) const {
        check_context(*this, a1); check_context(*this, a2); check_context(*this, a3);
        Z3_ast args[3] = { a1, a2, a3 };
        Z3_ast r = Z3_mk_app(ctx(), *this, 3, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const {
        check_context(*this, a1); check_context(*this, a2); check_context(*this, a3); check_context(*this, a4);
        Z3_ast args[4] = { a1, a2, a3, a4 };
        Z3_ast r = Z3_mk_app(ctx(), *this, 4, args);
        ctx().check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const {
        check_context(*this, a1); check_context(*this, a2); check_context(*this, a3); check_context(*this, a4); check_context(*this, a5);
        Z3_ast args[5] = { a1, a2, a3, a4, a5 };
        Z3_ast r = Z3_mk_app(ctx(), *this, 5, args);
        ctx().check_error();
        return expr(ctx(), r);
    }

    inline expr to_real(expr const & a) { Z3_ast r = Z3_mk_int2real(a.ctx(), a); a.check_error(); return expr(a.ctx(), r); }

    inline func_decl function(symbol const & name, unsigned arity, sort const * domain, sort const & range) {
        return range.ctx().function(name, arity, domain, range);
    }
    inline func_decl function(char const * name, unsigned arity, sort const * domain, sort const & range) {
        return range.ctx().function(name, arity, domain, range);
    }
    inline func_decl function(char const * name, sort const & domain, sort const & range) {
        return range.ctx().function(name, domain, range);
    }
    inline func_decl function(char const * name, sort const & d1, sort const & d2, sort const & range) {
        return range.ctx().function(name, d1, d2, range);
    }
    inline func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & range) {
        return range.ctx().function(name, d1, d2, d3, range);
    }
    inline func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & range) {
        return range.ctx().function(name, d1, d2, d3, d4, range);
    }
    inline func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & d5, sort const & range) {
        return range.ctx().function(name, d1, d2, d3, d4, d5, range);
    }
    
    inline expr select(expr const & a, expr const & i) {
        check_context(a, i);
        Z3_ast r = Z3_mk_select(a.ctx(), a, i);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr select(expr const & a, int i) { return select(a, a.ctx().num_val(i, a.get_sort().array_domain())); }
    inline expr store(expr const & a, expr const & i, expr const & v) {
        check_context(a, i); check_context(a, v);
        Z3_ast r = Z3_mk_store(a.ctx(), a, i, v);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr store(expr const & a, int i, expr const & v) { return store(a, a.ctx().num_val(i, a.get_sort().array_domain()), v); }
    inline expr store(expr const & a, expr i, int v) { return store(a, i, a.ctx().num_val(v, a.get_sort().array_range())); }
    inline expr store(expr const & a, int i, int v) { 
        return store(a, a.ctx().num_val(i, a.get_sort().array_domain()), a.ctx().num_val(v, a.get_sort().array_range())); 
    }
    inline expr const_array(sort const & d, expr const & v) {
        check_context(d, v);
        Z3_ast r = Z3_mk_const_array(d.ctx(), d, v);
        d.check_error();
        return expr(d.ctx(), r);
    }
    

};

template class z3::ast_vector_tpl<z3::ast>;
template class z3::ast_vector_tpl<z3::expr>;
template class z3::ast_vector_tpl<z3::sort>;
template class z3::ast_vector_tpl<z3::func_decl>;

#endif

