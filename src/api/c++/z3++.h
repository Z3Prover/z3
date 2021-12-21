/*++
Copyright (c) 2012 Microsoft Corporation

    Thin C++ layer on top of the Z3 C API.
    Main features:
      - Smart pointers for all Z3 objects.
      - Object-Oriented interface.
      - Operator overloading.
      - Exceptions for signaling Z3 errors

    The C API can be used simultaneously with the C++ layer.
    However, if you use the C API directly, you will have to check the error conditions manually.
    Of course, you can invoke the method check_error() of the context object.
Author:

    Leonardo (leonardo) 2012-03-28

Notes:

--*/
#pragma once

#include<cassert>
#include<iostream>
#include<string>
#include<sstream>
#include<memory>
#include<z3.h>
#include<limits.h>
#include<functional>

#undef min
#undef max

/**
   \defgroup cppapi C++ API

*/
/**@{*/

/**
   @name C++ API classes and functions
*/
/**@{*/

/**
   \brief Z3 C++ namespace
*/
namespace z3 {

    class exception;
    class config;
    class context;
    class symbol;
    class params;
    class param_descrs;
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
    template<typename T> class cast_ast;
    template<typename T> class ast_vector_tpl;
    typedef ast_vector_tpl<ast>       ast_vector;
    typedef ast_vector_tpl<expr>      expr_vector;
    typedef ast_vector_tpl<sort>      sort_vector;
    typedef ast_vector_tpl<func_decl> func_decl_vector;

    inline void set_param(char const * param, char const * value) { Z3_global_param_set(param, value); }
    inline void set_param(char const * param, bool value) { Z3_global_param_set(param, value ? "true" : "false"); }
    inline void set_param(char const * param, int value) { auto str = std::to_string(value); Z3_global_param_set(param, str.c_str()); }
    inline void reset_params() { Z3_global_param_reset_all(); }

    /**
       \brief Exception used to sign API usage errors.
    */
    class exception : public std::exception {
        std::string m_msg;
    public:
        virtual ~exception() throw() {}
        exception(char const * msg):m_msg(msg) {}
        char const * msg() const { return m_msg.c_str(); }
        char const * what() const throw() { return m_msg.c_str(); }
        friend std::ostream & operator<<(std::ostream & out, exception const & e);
    };
    inline std::ostream & operator<<(std::ostream & out, exception const & e) { out << e.msg(); return out; }

#if !defined(Z3_THROW)
#if __cpp_exceptions || _CPPUNWIND || __EXCEPTIONS
#define Z3_THROW(x) throw x
#else
#define Z3_THROW(x) {}
#endif
#endif // !defined(Z3_THROW)

    /**
       \brief Z3 global configuration object.
    */
    class config {
        Z3_config    m_cfg;
        config(config const &) = delete;
        config & operator=(config const &) = delete;
    public:
        config() { m_cfg = Z3_mk_config(); }
        ~config() { Z3_del_config(m_cfg); }
        operator Z3_config() const { return m_cfg; }
        /**
           \brief Set global parameter \c param with string \c value.
        */
        void set(char const * param, char const * value) { Z3_set_param_value(m_cfg, param, value); }
        /**
           \brief Set global parameter \c param with Boolean \c value.
        */
        void set(char const * param, bool value) { Z3_set_param_value(m_cfg, param, value ? "true" : "false"); }
        /**
           \brief Set global parameter \c param with integer \c value.
        */
        void set(char const * param, int value) {
            auto str = std::to_string(value);
            Z3_set_param_value(m_cfg, param, str.c_str());
        }
    };

    enum check_result {
        unsat, sat, unknown
    };

    enum rounding_mode {
        RNA,
        RNE,
        RTP,
        RTN,
        RTZ
    };

    inline check_result to_check_result(Z3_lbool l) {
        if (l == Z3_L_TRUE) return sat;
        else if (l == Z3_L_FALSE) return unsat;
        return unknown;
    }


    /**
       \brief A Context manages all other Z3 objects, global configuration options, etc.
    */


    class context {
    private:
        bool       m_enable_exceptions;
        rounding_mode m_rounding_mode;
        Z3_context m_ctx;
        void init(config & c) {
            set_context(Z3_mk_context_rc(c));
        }
        void set_context(Z3_context ctx) {
            m_ctx = ctx;
            m_enable_exceptions = true;
            m_rounding_mode = RNE;
            Z3_set_error_handler(m_ctx, 0);
            Z3_set_ast_print_mode(m_ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
        }


        context(context const &) = delete;
        context & operator=(context const &) = delete;

        friend class scoped_context;
        context(Z3_context c) { set_context(c); }
        void detach() { m_ctx = nullptr; }
    public:
        context() { config c; init(c); }
        context(config & c) { init(c); }
        ~context() { if (m_ctx) Z3_del_context(m_ctx); }
        operator Z3_context() const { return m_ctx; }

        /**
           \brief Auxiliary method used to check for API usage errors.
        */
        Z3_error_code check_error() const {
            Z3_error_code e = Z3_get_error_code(m_ctx);
            if (e != Z3_OK && enable_exceptions())
                Z3_THROW(exception(Z3_get_error_msg(m_ctx, e)));
            return e;
        }

        void check_parser_error() const {
            check_error();
        }

        /**
           \brief The C++ API uses by defaults exceptions on errors.
           For applications that don't work well with exceptions (there should be only few)
           you have the ability to turn off exceptions. The tradeoffs are that applications
           have to be very careful about using check_error() after calls that may result in an
           erroneous state.
         */
        void set_enable_exceptions(bool f) { m_enable_exceptions = f; }

        bool enable_exceptions() const { return m_enable_exceptions; }

        /**
           \brief Update global parameter \c param with string \c value.
        */
        void set(char const * param, char const * value) { Z3_update_param_value(m_ctx, param, value); }
        /**
           \brief Update global parameter \c param with Boolean \c value.
        */
        void set(char const * param, bool value) { Z3_update_param_value(m_ctx, param, value ? "true" : "false"); }
        /**
           \brief Update global parameter \c param with Integer \c value.
        */
        void set(char const * param, int value) {
            auto str = std::to_string(value);
            Z3_update_param_value(m_ctx, param, str.c_str());
        }

        /**
           \brief Interrupt the current procedure being executed by any object managed by this context.
           This is a soft interruption: there is no guarantee the object will actually stop.
        */
        void interrupt() { Z3_interrupt(m_ctx); }

        /**
           \brief Create a Z3 symbol based on the given string.
        */
        symbol str_symbol(char const * s);
        /**
           \brief Create a Z3 symbol based on the given integer.
        */
        symbol int_symbol(int n);
        /**
           \brief Return the Boolean sort.
        */
        sort bool_sort();
        /**
           \brief Return the integer sort.
        */
        sort int_sort();
        /**
           \brief Return the Real sort.
        */
        sort real_sort();
        /**
           \brief Return the Bit-vector sort of size \c sz. That is, the sort for bit-vectors of size \c sz.
        */
        sort bv_sort(unsigned sz);

        /**
           \brief Return the sort for Unicode characters.
         */
        sort char_sort();
        /**
           \brief Return the sort for Unicode strings.
         */
        sort string_sort();
        /**
           \brief Return a sequence sort over base sort \c s.
         */
        sort seq_sort(sort& s);
        /**
           \brief Return a regular expression sort over sequences \c seq_sort.
         */
        sort re_sort(sort& seq_sort);
        /**
           \brief Return an array sort for arrays from \c d to \c r.

           Example: Given a context \c c, <tt>c.array_sort(c.int_sort(), c.bool_sort())</tt> is an array sort from integer to Boolean.
        */
        sort array_sort(sort d, sort r);
        sort array_sort(sort_vector const& d, sort r);
        /**
           \brief Return a floating point sort.
           \c ebits is a number of exponent bits,
           \c sbits is a number of significand bits,
           \pre where ebits must be larger than 1 and sbits must be larger than 2.
         */
        sort fpa_sort(unsigned ebits, unsigned sbits);
        /**
           \brief Return a FloatingPoint sort with given precision bitwidth (16, 32, 64 or 128).
         */
        template<size_t precision>
        sort fpa_sort();
        /**
           \brief Return a RoundingMode sort.
         */
        sort fpa_rounding_mode_sort();
        /**
           \brief Sets RoundingMode of FloatingPoints.
         */
        void set_rounding_mode(rounding_mode rm);
        /**
           \brief Return an enumeration sort: enum_names[0], ..., enum_names[n-1].
           \c cs and \c ts are output parameters. The method stores in \c cs the constants corresponding to the enumerated elements,
           and in \c ts the predicates for testing if terms of the enumeration sort correspond to an enumeration.
        */
        sort enumeration_sort(char const * name, unsigned n, char const * const * enum_names, func_decl_vector & cs, func_decl_vector & ts);

        /**
           \brief Return a tuple constructor.
           \c name is the name of the returned constructor,
           \c n are the number of arguments, \c names and \c sorts are their projected sorts.
           \c projs is an output parameter. It contains the set of projection functions.
        */
        func_decl tuple_sort(char const * name, unsigned n, char const * const * names, sort const* sorts, func_decl_vector & projs);

        /**
           \brief create an uninterpreted sort with the name given by the string or symbol.
         */
        sort uninterpreted_sort(char const* name);
        sort uninterpreted_sort(symbol const& name);

        func_decl function(symbol const & name, unsigned arity, sort const * domain, sort const & range);
        func_decl function(char const * name, unsigned arity, sort const * domain, sort const & range);
        func_decl function(symbol const&  name, sort_vector const& domain, sort const& range);
        func_decl function(char const * name, sort_vector const& domain, sort const& range);
        func_decl function(char const * name, sort const & domain, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & range);
        func_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & d5, sort const & range);

        func_decl recfun(symbol const & name, unsigned arity, sort const * domain, sort const & range);
        func_decl recfun(char const * name, unsigned arity, sort const * domain, sort const & range);
        func_decl recfun(char const * name, sort const & domain, sort const & range);
        func_decl recfun(char const * name, sort const & d1, sort const & d2, sort const & range);

        void      recdef(func_decl, expr_vector const& args, expr const& body);
        func_decl user_propagate_function(symbol const& name, sort_vector const& domain, sort const& range);

        expr constant(symbol const & name, sort const & s);
        expr constant(char const * name, sort const & s);
        expr bool_const(char const * name);
        expr int_const(char const * name);
        expr real_const(char const * name);
        expr string_const(char const * name);
        expr bv_const(char const * name, unsigned sz);
        expr fpa_const(char const * name, unsigned ebits, unsigned sbits);

        template<size_t precision>
        expr fpa_const(char const * name);

        expr fpa_rounding_mode();

        expr bool_val(bool b);

        expr int_val(int n);
        expr int_val(unsigned n);
        expr int_val(int64_t n);
        expr int_val(uint64_t n);
        expr int_val(char const * n);

        expr real_val(int n, int d);
        expr real_val(int n);
        expr real_val(unsigned n);
        expr real_val(int64_t n);
        expr real_val(uint64_t n);
        expr real_val(char const * n);

        expr bv_val(int n, unsigned sz);
        expr bv_val(unsigned n, unsigned sz);
        expr bv_val(int64_t n, unsigned sz);
        expr bv_val(uint64_t n, unsigned sz);
        expr bv_val(char const * n, unsigned sz);
        expr bv_val(unsigned n, bool const* bits);

        expr fpa_val(double n);
        expr fpa_val(float n);
        expr fpa_nan(sort const & s);
        expr fpa_inf(sort const & s, bool sgn);

        expr string_val(char const* s);
        expr string_val(char const* s, unsigned n);
        expr string_val(std::string const& s);
        expr string_val(std::u32string const& s);

        expr num_val(int n, sort const & s);

        /**
           \brief parsing
         */
        expr_vector parse_string(char const* s);
        expr_vector parse_file(char const* file);

        expr_vector parse_string(char const* s, sort_vector const& sorts, func_decl_vector const& decls);
        expr_vector parse_file(char const* s, sort_vector const& sorts, func_decl_vector const& decls);
    };

    class scoped_context final {
        context m_ctx;
    public:
        scoped_context(Z3_context c): m_ctx(c) {}
        ~scoped_context() { m_ctx.detach(); }
        context& operator()() { return m_ctx; }
    };


    template<typename T>
    class array {
        std::unique_ptr<T[]> m_array;
        unsigned m_size;
        array(array const &) = delete;
        array & operator=(array const &) = delete;
    public:
        array(unsigned sz):m_array(new T[sz]),m_size(sz) {}
        template<typename T2>
        array(ast_vector_tpl<T2> const & v);
        void resize(unsigned sz) { m_array.reset(new T[sz]); m_size = sz; }
        unsigned size() const { return m_size; }
        T & operator[](int i) { assert(0 <= i); assert(static_cast<unsigned>(i) < m_size); return m_array[i]; }
        T const & operator[](int i) const { assert(0 <= i); assert(static_cast<unsigned>(i) < m_size); return m_array[i]; }
        T const * ptr() const { return m_array.get(); }
        T * ptr() { return m_array.get(); }
    };

    class object {
    protected:
        context * m_ctx;
    public:
        object(context & c):m_ctx(&c) {}
        context & ctx() const { return *m_ctx; }
        Z3_error_code check_error() const { return m_ctx->check_error(); }
        friend void check_context(object const & a, object const & b);
    };
    inline void check_context(object const & a, object const & b) { (void)a; (void)b; assert(a.m_ctx == b.m_ctx); }

    class symbol : public object {
        Z3_symbol m_sym;
    public:
        symbol(context & c, Z3_symbol s):object(c), m_sym(s) {}
        operator Z3_symbol() const { return m_sym; }
        Z3_symbol_kind kind() const { return Z3_get_symbol_kind(ctx(), m_sym); }
        std::string str() const { assert(kind() == Z3_STRING_SYMBOL); return Z3_get_symbol_string(ctx(), m_sym); }
        int to_int() const { assert(kind() == Z3_INT_SYMBOL); return Z3_get_symbol_int(ctx(), m_sym); }
        friend std::ostream & operator<<(std::ostream & out, symbol const & s);
    };

    inline std::ostream & operator<<(std::ostream & out, symbol const & s) {
        if (s.kind() == Z3_INT_SYMBOL)
            out << "k!" << s.to_int();
        else
            out << s.str();
        return out;
    }


    class param_descrs : public object {
        Z3_param_descrs m_descrs;
    public:
        param_descrs(context& c, Z3_param_descrs d): object(c), m_descrs(d) { Z3_param_descrs_inc_ref(c, d); }
        param_descrs(param_descrs const& o): object(o.ctx()), m_descrs(o.m_descrs) { Z3_param_descrs_inc_ref(ctx(), m_descrs); }
        param_descrs& operator=(param_descrs const& o) {
            Z3_param_descrs_inc_ref(o.ctx(), o.m_descrs);
            Z3_param_descrs_dec_ref(ctx(), m_descrs);
            m_descrs = o.m_descrs;
            object::operator=(o);
            return *this;
        }
        ~param_descrs() { Z3_param_descrs_dec_ref(ctx(), m_descrs); }
        static param_descrs simplify_param_descrs(context& c) { return param_descrs(c, Z3_simplify_get_param_descrs(c)); }

        unsigned size() { return Z3_param_descrs_size(ctx(), m_descrs); }
        symbol name(unsigned i) { return symbol(ctx(), Z3_param_descrs_get_name(ctx(), m_descrs, i)); }
        Z3_param_kind kind(symbol const& s) { return Z3_param_descrs_get_kind(ctx(), m_descrs, s); }
        std::string documentation(symbol const& s) { char const* r = Z3_param_descrs_get_documentation(ctx(), m_descrs, s); check_error(); return r; }
        std::string to_string() const { return Z3_param_descrs_to_string(ctx(), m_descrs); }
    };

    inline std::ostream& operator<<(std::ostream & out, param_descrs const & d) { return out << d.to_string(); }

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
            object::operator=(s);
            m_params = s.m_params;
            return *this;
        }
        void set(char const * k, bool b) { Z3_params_set_bool(ctx(), m_params, ctx().str_symbol(k), b); }
        void set(char const * k, unsigned n) { Z3_params_set_uint(ctx(), m_params, ctx().str_symbol(k), n); }
        void set(char const * k, double n) { Z3_params_set_double(ctx(), m_params, ctx().str_symbol(k), n); }
        void set(char const * k, symbol const & s) { Z3_params_set_symbol(ctx(), m_params, ctx().str_symbol(k), s); }
        void set(char const * k, char const* s) { Z3_params_set_symbol(ctx(), m_params, ctx().str_symbol(k), ctx().str_symbol(s)); }
        friend std::ostream & operator<<(std::ostream & out, params const & p);
    };

    inline std::ostream & operator<<(std::ostream & out, params const & p) {
        out << Z3_params_to_string(p.ctx(), p); return out;
    }

    class ast : public object {
    protected:
        Z3_ast    m_ast;
    public:
        ast(context & c):object(c), m_ast(0) {}
        ast(context & c, Z3_ast n):object(c), m_ast(n) { Z3_inc_ref(ctx(), m_ast); }
        ast(ast const & s) :object(s), m_ast(s.m_ast) { Z3_inc_ref(ctx(), m_ast); }
        ~ast() { if (m_ast) Z3_dec_ref(*m_ctx, m_ast); }
        operator Z3_ast() const { return m_ast; }
        operator bool() const { return m_ast != 0; }
        ast & operator=(ast const & s) {
            Z3_inc_ref(s.ctx(), s.m_ast);
            if (m_ast)
                Z3_dec_ref(ctx(), m_ast);
            object::operator=(s);
            m_ast = s.m_ast;
            return *this;
        }
        Z3_ast_kind kind() const { Z3_ast_kind r = Z3_get_ast_kind(ctx(), m_ast); check_error(); return r; }
        unsigned hash() const { unsigned r = Z3_get_ast_hash(ctx(), m_ast); check_error(); return r; }
        friend std::ostream & operator<<(std::ostream & out, ast const & n);
        std::string to_string() const { return std::string(Z3_ast_to_string(ctx(), m_ast)); }


        /**
           \brief Return true if the ASTs are structurally identical.
        */
        friend bool eq(ast const & a, ast const & b);
    };
    inline std::ostream & operator<<(std::ostream & out, ast const & n) {
        out << Z3_ast_to_string(n.ctx(), n.m_ast); return out;
    }

    inline bool eq(ast const & a, ast const & b) { return Z3_is_eq_ast(a.ctx(), a, b); }

    template<typename T>
    class ast_vector_tpl : public object {
        Z3_ast_vector m_vector;
        void init(Z3_ast_vector v) { Z3_ast_vector_inc_ref(ctx(), v); m_vector = v; }
    public:
        ast_vector_tpl(context & c):object(c) { init(Z3_mk_ast_vector(c)); }
        ast_vector_tpl(context & c, Z3_ast_vector v):object(c) { init(v); }
        ast_vector_tpl(ast_vector_tpl const & s):object(s), m_vector(s.m_vector) { Z3_ast_vector_inc_ref(ctx(), m_vector); }
        ast_vector_tpl(context& c, ast_vector_tpl const& src): object(c) { init(Z3_ast_vector_translate(src.ctx(), src, c)); }

        ~ast_vector_tpl() { Z3_ast_vector_dec_ref(ctx(), m_vector); }
        operator Z3_ast_vector() const { return m_vector; }
        unsigned size() const { return Z3_ast_vector_size(ctx(), m_vector); }
        T operator[](int i) const { assert(0 <= i); Z3_ast r = Z3_ast_vector_get(ctx(), m_vector, i); check_error(); return cast_ast<T>()(ctx(), r); }
        void push_back(T const & e) { Z3_ast_vector_push(ctx(), m_vector, e); check_error(); }
        void resize(unsigned sz) { Z3_ast_vector_resize(ctx(), m_vector, sz); check_error(); }
        T back() const { return operator[](size() - 1); }
        void pop_back() { assert(size() > 0); resize(size() - 1); }
        bool empty() const { return size() == 0; }
        ast_vector_tpl & operator=(ast_vector_tpl const & s) {
            Z3_ast_vector_inc_ref(s.ctx(), s.m_vector);
            Z3_ast_vector_dec_ref(ctx(), m_vector);
            object::operator=(s);
            m_vector = s.m_vector;
            return *this;
        }
        ast_vector_tpl& set(unsigned idx, ast& a) {
            Z3_ast_vector_set(ctx(), m_vector, idx, a);
            return *this;
        }
        /*
          Disabled pending C++98 build upgrade
        bool contains(T const& x) const {
            for (T y : *this) if (eq(x, y)) return true;
            return false;
        }
        */

        class iterator final {
            ast_vector_tpl const* m_vector;
            unsigned m_index;
        public:
            iterator(ast_vector_tpl const* v, unsigned i): m_vector(v), m_index(i) {}

            bool operator==(iterator const& other) const noexcept {
                return other.m_index == m_index;
            };
            bool operator!=(iterator const& other) const noexcept {
                return other.m_index != m_index;
            };
            iterator& operator++() noexcept {
                ++m_index;
                return *this;
            }
            void set(T& arg) {
                Z3_ast_vector_set(m_vector->ctx(), *m_vector, m_index, arg);
            }
            iterator operator++(int) noexcept { iterator tmp = *this; ++m_index; return tmp; }
            T * operator->() const { return &(operator*()); }
            T operator*() const { return (*m_vector)[m_index]; }
        };
        iterator begin() const noexcept { return iterator(this, 0); }
        iterator end() const { return iterator(this, size()); }
        friend std::ostream & operator<<(std::ostream & out, ast_vector_tpl const & v) { out << Z3_ast_vector_to_string(v.ctx(), v); return out; }
        std::string to_string() const { return std::string(Z3_ast_vector_to_string(ctx(), m_vector)); }
    };


    /**
       \brief A Z3 sort (aka type). Every expression (i.e., formula or term) in Z3 has a sort.
    */
    class sort : public ast {
    public:
        sort(context & c):ast(c) {}
        sort(context & c, Z3_sort s):ast(c, reinterpret_cast<Z3_ast>(s)) {}
        sort(context & c, Z3_ast a):ast(c, a) {}
        operator Z3_sort() const { return reinterpret_cast<Z3_sort>(m_ast); }

        /**
           \brief retrieve unique identifier for func_decl.
         */
        unsigned id() const { unsigned r = Z3_get_sort_id(ctx(), *this); check_error(); return r; }

        /**
           \brief Return the internal sort kind.
        */
        Z3_sort_kind sort_kind() const { return Z3_get_sort_kind(*m_ctx, *this); }
        /**
           \brief Return name of sort.
        */
        symbol name() const { Z3_symbol s = Z3_get_sort_name(ctx(), *this); check_error(); return symbol(ctx(), s); }
        /**
            \brief Return true if this sort is the Boolean sort.
        */
        bool is_bool() const { return sort_kind() == Z3_BOOL_SORT; }
        /**
            \brief Return true if this sort is the Integer sort.
        */
        bool is_int() const { return sort_kind() == Z3_INT_SORT; }
        /**
            \brief Return true if this sort is the Real sort.
        */
        bool is_real() const { return sort_kind() == Z3_REAL_SORT; }
        /**
            \brief Return true if this sort is the Integer or Real sort.
        */
        bool is_arith() const { return is_int() || is_real(); }
        /**
            \brief Return true if this sort is a Bit-vector sort.
        */
        bool is_bv() const { return sort_kind() == Z3_BV_SORT; }
        /**
            \brief Return true if this sort is a Array sort.
        */
        bool is_array() const { return sort_kind() == Z3_ARRAY_SORT; }
        /**
            \brief Return true if this sort is a Datatype sort.
        */
        bool is_datatype() const { return sort_kind() == Z3_DATATYPE_SORT; }
        /**
            \brief Return true if this sort is a Relation sort.
        */
        bool is_relation() const { return sort_kind() == Z3_RELATION_SORT; }
        /**
            \brief Return true if this sort is a Sequence sort.
        */
        bool is_seq() const { return sort_kind() == Z3_SEQ_SORT; }
        /**
            \brief Return true if this sort is a regular expression sort.
        */
        bool is_re() const { return sort_kind() == Z3_RE_SORT; }
        /**
            \brief Return true if this sort is a Finite domain sort.
        */
        bool is_finite_domain() const { return sort_kind() == Z3_FINITE_DOMAIN_SORT; }
        /**
            \brief Return true if this sort is a Floating point sort.
        */
        bool is_fpa() const { return sort_kind() == Z3_FLOATING_POINT_SORT; }

        /**
            \brief Return the size of this Bit-vector sort.

            \pre is_bv()
        */
        unsigned bv_size() const { assert(is_bv()); unsigned r = Z3_get_bv_sort_size(ctx(), *this); check_error(); return r; }

        unsigned fpa_ebits() const { assert(is_fpa()); unsigned r = Z3_fpa_get_ebits(ctx(), *this); check_error(); return r; }

        unsigned fpa_sbits() const { assert(is_fpa()); unsigned r = Z3_fpa_get_sbits(ctx(), *this); check_error(); return r; }
        /**
            \brief Return the domain of this Array sort.

            \pre is_array()
        */
        sort array_domain() const { assert(is_array()); Z3_sort s = Z3_get_array_sort_domain(ctx(), *this); check_error(); return sort(ctx(), s); }
        /**
            \brief Return the range of this Array sort.

            \pre is_array()
        */
        sort array_range() const { assert(is_array()); Z3_sort s = Z3_get_array_sort_range(ctx(), *this); check_error(); return sort(ctx(), s); }

        friend std::ostream & operator<<(std::ostream & out, sort const & s) { return out << Z3_sort_to_string(s.ctx(), Z3_sort(s.m_ast)); }
    };

    /**
       \brief Function declaration (aka function definition). It is the signature of interpreted and uninterpreted functions in Z3.
       The basic building block in Z3 is the function application.
    */
    class func_decl : public ast {
    public:
        func_decl(context & c):ast(c) {}
        func_decl(context & c, Z3_func_decl n):ast(c, reinterpret_cast<Z3_ast>(n)) {}
        operator Z3_func_decl() const { return reinterpret_cast<Z3_func_decl>(m_ast); }

        /**
           \brief retrieve unique identifier for func_decl.
         */
        unsigned id() const { unsigned r = Z3_get_func_decl_id(ctx(), *this); check_error(); return r; }

        unsigned arity() const { return Z3_get_arity(ctx(), *this); }
        sort domain(unsigned i) const { assert(i < arity()); Z3_sort r = Z3_get_domain(ctx(), *this, i); check_error(); return sort(ctx(), r); }
        sort range() const { Z3_sort r = Z3_get_range(ctx(), *this); check_error(); return sort(ctx(), r); }
        symbol name() const { Z3_symbol s = Z3_get_decl_name(ctx(), *this); check_error(); return symbol(ctx(), s); }
        Z3_decl_kind decl_kind() const { return Z3_get_decl_kind(ctx(), *this); }

        func_decl transitive_closure(func_decl const&) {
            Z3_func_decl tc = Z3_mk_transitive_closure(ctx(), *this); check_error(); return func_decl(ctx(), tc); 
        }

        bool is_const() const { return arity() == 0; }

        expr operator()() const;
        expr operator()(unsigned n, expr const * args) const;
        expr operator()(expr_vector const& v) const;
        expr operator()(expr const & a) const;
        expr operator()(int a) const;
        expr operator()(expr const & a1, expr const & a2) const;
        expr operator()(expr const & a1, int a2) const;
        expr operator()(int a1, expr const & a2) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
    };

    /**
       \brief forward declarations
     */
    expr select(expr const & a, expr const& i);
    expr select(expr const & a, expr_vector const & i);

    /**
       \brief A Z3 expression is used to represent formulas and terms. For Z3, a formula is any expression of sort Boolean.
       Every expression has a sort.
    */
    class expr : public ast {
    public:
        expr(context & c):ast(c) {}
        expr(context & c, Z3_ast n):ast(c, reinterpret_cast<Z3_ast>(n)) {}

        /**
           \brief Return the sort of this expression.
        */
        sort get_sort() const { Z3_sort s = Z3_get_sort(*m_ctx, m_ast); check_error(); return sort(*m_ctx, s); }

        /**
           \brief Return true if this is a Boolean expression.
        */
        bool is_bool() const { return get_sort().is_bool(); }
        /**
           \brief Return true if this is an integer expression.
        */
        bool is_int() const { return get_sort().is_int(); }
        /**
           \brief Return true if this is a real expression.
        */
        bool is_real() const { return get_sort().is_real(); }
        /**
           \brief Return true if this is an integer or real expression.
        */
        bool is_arith() const { return get_sort().is_arith(); }
        /**
           \brief Return true if this is a Bit-vector expression.
        */
        bool is_bv() const { return get_sort().is_bv(); }
        /**
           \brief Return true if this is a Array expression.
        */
        bool is_array() const { return get_sort().is_array(); }
        /**
           \brief Return true if this is a Datatype expression.
        */
        bool is_datatype() const { return get_sort().is_datatype(); }
        /**
           \brief Return true if this is a Relation expression.
        */
        bool is_relation() const { return get_sort().is_relation(); }
        /**
           \brief Return true if this is a sequence expression.
        */
        bool is_seq() const { return get_sort().is_seq(); }
        /**
           \brief Return true if this is a regular expression.
        */
        bool is_re() const { return get_sort().is_re(); }

        /**
           \brief Return true if this is a Finite-domain expression.

           \remark Finite-domain is special kind of interpreted sort:
           is_bool(), is_bv() and is_finite_domain() are mutually
           exclusive.

        */
        bool is_finite_domain() const { return get_sort().is_finite_domain(); }
        /**
            \brief Return true if this is a FloatingPoint expression. .
        */
        bool is_fpa() const { return get_sort().is_fpa(); }

        /**
           \brief Return true if this expression is a numeral.
           Specialized functions also return representations for the numerals as
           small integers, 64 bit integers or rational or decimal strings.
        */
        bool is_numeral() const { return kind() == Z3_NUMERAL_AST; }
        bool is_numeral_i64(int64_t& i) const { bool r = Z3_get_numeral_int64(ctx(), m_ast, &i); check_error(); return r;}
        bool is_numeral_u64(uint64_t& i) const { bool r = Z3_get_numeral_uint64(ctx(), m_ast, &i); check_error(); return r;}
        bool is_numeral_i(int& i) const { bool r = Z3_get_numeral_int(ctx(), m_ast, &i); check_error(); return r;}
        bool is_numeral_u(unsigned& i) const { bool r = Z3_get_numeral_uint(ctx(), m_ast, &i); check_error(); return r;}
        bool is_numeral(std::string& s) const { if (!is_numeral()) return false; s = Z3_get_numeral_string(ctx(), m_ast); check_error(); return true; }
        bool is_numeral(std::string& s, unsigned precision) const { if (!is_numeral()) return false; s = Z3_get_numeral_decimal_string(ctx(), m_ast, precision); check_error(); return true; }
        bool is_numeral(double& d) const { if (!is_numeral()) return false; d = Z3_get_numeral_double(ctx(), m_ast); check_error(); return true; }
        bool as_binary(std::string& s) const { if (!is_numeral()) return false; s = Z3_get_numeral_binary_string(ctx(), m_ast); check_error(); return true; }

        double as_double() const { double d = 0; is_numeral(d); return d; }
        uint64_t as_uint64() const { uint64_t r = 0; is_numeral_u64(r); return r; }
        int64_t as_int64() const { int64_t r = 0; is_numeral_i64(r); return r; }
        

        /**
           \brief Return true if this expression is an application.
        */
        bool is_app() const { return kind() == Z3_APP_AST || kind() == Z3_NUMERAL_AST; }
        /**
           \brief Return true if this expression is a constant (i.e., an application with 0 arguments).
        */
        bool is_const() const { return is_app() && num_args() == 0; }
        /**
           \brief Return true if this expression is a quantifier.
        */
        bool is_quantifier() const { return kind() == Z3_QUANTIFIER_AST; }

        /**
           \brief Return true if this expression is a universal quantifier.
        */
        bool is_forall() const { return Z3_is_quantifier_forall(ctx(), m_ast); }
        /**
           \brief Return true if this expression is an existential quantifier.
        */
        bool is_exists() const { return Z3_is_quantifier_exists(ctx(), m_ast); }
        /**
           \brief Return true if this expression is a lambda expression.
        */
        bool is_lambda() const { return Z3_is_lambda(ctx(), m_ast); }
        /**

           \brief Return true if this expression is a variable.
        */
        bool is_var() const { return kind() == Z3_VAR_AST; }
        /**
           \brief Return true if expression is an algebraic number.
        */
        bool is_algebraic() const { return Z3_is_algebraic_number(ctx(), m_ast); }

        /**
           \brief Return true if this expression is well sorted (aka type correct).
        */
        bool is_well_sorted() const { bool r = Z3_is_well_sorted(ctx(), m_ast); check_error(); return r; }

        /**
           \brief Return Boolean expression to test for whether an FP expression is inf
        */
        expr mk_is_inf() const {
            assert(is_fpa());
            Z3_ast r = Z3_mk_fpa_is_infinite(ctx(), m_ast);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Return Boolean expression to test for whether an FP expression is a NaN
        */
        expr mk_is_nan() const {
            assert(is_fpa());
            Z3_ast r = Z3_mk_fpa_is_nan(ctx(), m_ast);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Return Boolean expression to test for whether an FP expression is a normal
        */
        expr mk_is_normal() const {
            assert(is_fpa());
            Z3_ast r = Z3_mk_fpa_is_normal(ctx(), m_ast);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Return Boolean expression to test for whether an FP expression is a subnormal
        */
        expr mk_is_subnormal() const {
            assert(is_fpa());
            Z3_ast r = Z3_mk_fpa_is_subnormal(ctx(), m_ast);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Return Boolean expression to test for whether an FP expression is a zero
        */
        expr mk_is_zero() const {
            assert(is_fpa());
            Z3_ast r = Z3_mk_fpa_is_zero(ctx(), m_ast);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Convert this fpa into an IEEE BV
        */
        expr mk_to_ieee_bv() const {
            assert(is_fpa());
            Z3_ast r = Z3_mk_fpa_to_ieee_bv(ctx(), m_ast);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Convert this IEEE BV into a fpa
        */
        expr mk_from_ieee_bv(sort const &s) const {
            assert(is_bv());
            Z3_ast r = Z3_mk_fpa_to_fp_bv(ctx(), m_ast, s);
            check_error();
            return expr(ctx(), r);
        }

        /**
           \brief Return string representation of numeral or algebraic number
           This method assumes the expression is numeral or algebraic

           \pre is_numeral() || is_algebraic()
        */
        std::string get_decimal_string(int precision) const {
            assert(is_numeral() || is_algebraic());
            return std::string(Z3_get_numeral_decimal_string(ctx(), m_ast, precision));
        }

        /**
         * Retrieve lower and upper bounds for algebraic numerals based on a decimal precision
         */
        expr algebraic_lower(unsigned precision) const { 
            assert(is_algebraic());      
            Z3_ast r = Z3_get_algebraic_number_lower(ctx(), m_ast, precision);
            check_error();
            return expr(ctx(), r);
        }

        expr algebraic_upper(unsigned precision) const { 
            assert(is_algebraic());      
            Z3_ast r = Z3_get_algebraic_number_upper(ctx(), m_ast, precision);
            check_error();
            return expr(ctx(), r);
        }
        
        /**
           \brief Return coefficients for p of an algebraic number (root-obj p i)
         */
        expr_vector algebraic_poly() const {
            assert(is_algebraic());
            Z3_ast_vector r = Z3_algebraic_get_poly(ctx(), m_ast);
            check_error();
            return expr_vector(ctx(), r);
        }

        /**
           \brief Return i of an algebraic number (root-obj p i)
         */
        unsigned algebraic_i() const {
            assert(is_algebraic());
            unsigned i = Z3_algebraic_get_i(ctx(), m_ast);
            check_error();
            return i;
        }

        /**
           \brief retrieve unique identifier for expression.
         */
        unsigned id() const { unsigned r = Z3_get_ast_id(ctx(), m_ast); check_error(); return r; }

        /**
           \brief Return int value of numeral, throw if result cannot fit in
           machine int

           It only makes sense to use this function if the caller can ensure that
           the result is an integer or if exceptions are enabled.
           If exceptions are disabled, then use the is_numeral_i function.

           \pre is_numeral()
        */
        int get_numeral_int() const {
            int result = 0;
            if (!is_numeral_i(result)) {
                assert(ctx().enable_exceptions());
                if (!ctx().enable_exceptions()) return 0;
                Z3_THROW(exception("numeral does not fit in machine int"));
            }
            return result;
        }

        /**
           \brief Return uint value of numeral, throw if result cannot fit in
           machine uint

           It only makes sense to use this function if the caller can ensure that
           the result is an integer or if exceptions are enabled.
           If exceptions are disabled, then use the is_numeral_u function.
           \pre is_numeral()
        */
        unsigned get_numeral_uint() const {
            assert(is_numeral());
            unsigned result = 0;
            if (!is_numeral_u(result)) {
                assert(ctx().enable_exceptions());
                if (!ctx().enable_exceptions()) return 0;
                Z3_THROW(exception("numeral does not fit in machine uint"));
            }
            return result;
        }

        /**
           \brief Return \c int64_t value of numeral, throw if result cannot fit in
           \c int64_t.

           \pre is_numeral()
        */
        int64_t get_numeral_int64() const {
            assert(is_numeral());
            int64_t result = 0;
            if (!is_numeral_i64(result)) {
                assert(ctx().enable_exceptions());
                if (!ctx().enable_exceptions()) return 0;
                Z3_THROW(exception("numeral does not fit in machine int64_t"));
            }
            return result;
        }

        /**
           \brief Return \c uint64_t value of numeral, throw if result cannot fit in
           \c uint64_t.

           \pre is_numeral()
        */
        uint64_t get_numeral_uint64() const {
            assert(is_numeral());
            uint64_t result = 0;
            if (!is_numeral_u64(result)) {
                assert(ctx().enable_exceptions());
                if (!ctx().enable_exceptions()) return 0;
                Z3_THROW(exception("numeral does not fit in machine uint64_t"));
            }
            return result;
        }

        Z3_lbool bool_value() const {
            return Z3_get_bool_value(ctx(), m_ast);
        }

        expr numerator() const {
            assert(is_numeral());
            Z3_ast r = Z3_get_numerator(ctx(), m_ast);
            check_error();
            return expr(ctx(),r);
        }


        expr denominator() const {
            assert(is_numeral());
            Z3_ast r = Z3_get_denominator(ctx(), m_ast);
            check_error();
            return expr(ctx(),r);
        }


        /**
           \brief Return true if this expression is a string literal. 
           The string can be accessed using \c get_string() and \c get_escaped_string()
         */
        bool is_string_value() const { return Z3_is_string(ctx(), m_ast); }

        /**
           \brief for a string value expression return an escaped string value.
           \pre expression is for a string value.
         */

        std::string get_string() const {            
            assert(is_string_value());
            char const* s = Z3_get_string(ctx(), m_ast);
            check_error();
            return std::string(s);
        }

        /**
           \brief for a string value expression return an unespaced string value.
           \pre expression is for a string value.
        */

        std::u32string get_u32string() const {
            assert(is_string_value());
            unsigned n = Z3_get_string_length(ctx(), m_ast);
            std::u32string s;
            s.resize(n);
            Z3_get_string_contents(ctx(), m_ast, n, (unsigned*)s.data());
            return s;
        }

        operator Z3_app() const { assert(is_app()); return reinterpret_cast<Z3_app>(m_ast); }

        /**
           \brief Return the declaration associated with this application.
           This method assumes the expression is an application.

           \pre is_app()
        */
        func_decl decl() const { Z3_func_decl f = Z3_get_app_decl(ctx(), *this); check_error(); return func_decl(ctx(), f); }
        /**
           \brief Return the number of arguments in this application.
           This method assumes the expression is an application.

           \pre is_app()
        */
        unsigned num_args() const { unsigned r = Z3_get_app_num_args(ctx(), *this); check_error(); return r; }
        /**
           \brief Return the i-th argument of this application.
           This method assumes the expression is an application.

           \pre is_app()
           \pre i < num_args()
        */
        expr arg(unsigned i) const { Z3_ast r = Z3_get_app_arg(ctx(), *this, i); check_error(); return expr(ctx(), r); }

        /**
           \brief Return the 'body' of this quantifier.

           \pre is_quantifier()
        */
        expr body() const { assert(is_quantifier()); Z3_ast r = Z3_get_quantifier_body(ctx(), *this); check_error(); return expr(ctx(), r); }

        /**
           \brief Return an expression representing <tt>not(a)</tt>.

           \pre a.is_bool()
        */
        friend expr operator!(expr const & a);

        /**
           \brief Return an expression representing <tt>a and b</tt>.

           \pre a.is_bool()
           \pre b.is_bool()
        */
        friend expr operator&&(expr const & a, expr const & b);


        /**
           \brief Return an expression representing <tt>a and b</tt>.
           The C++ Boolean value \c b is automatically converted into a Z3 Boolean constant.

           \pre a.is_bool()
        */
        friend expr operator&&(expr const & a, bool b);
        /**
           \brief Return an expression representing <tt>a and b</tt>.
           The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

           \pre b.is_bool()
        */
        friend expr operator&&(bool a, expr const & b);

        /**
           \brief Return an expression representing <tt>a or b</tt>.

           \pre a.is_bool()
           \pre b.is_bool()
        */
        friend expr operator||(expr const & a, expr const & b);
        /**
           \brief Return an expression representing <tt>a or b</tt>.
           The C++ Boolean value \c b is automatically converted into a Z3 Boolean constant.

           \pre a.is_bool()
        */
        friend expr operator||(expr const & a, bool b);

        /**
           \brief Return an expression representing <tt>a or b</tt>.
           The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

           \pre b.is_bool()
        */
        friend expr operator||(bool a, expr const & b);

        friend expr implies(expr const & a, expr const & b);
        friend expr implies(expr const & a, bool b);
        friend expr implies(bool a, expr const & b);

        friend expr mk_or(expr_vector const& args);
        friend expr mk_xor(expr_vector const& args);
        friend expr mk_and(expr_vector const& args);

        friend expr ite(expr const & c, expr const & t, expr const & e);

        bool is_true() const { return is_app() && Z3_OP_TRUE == decl().decl_kind(); }
        bool is_false() const { return is_app() && Z3_OP_FALSE == decl().decl_kind(); }
        bool is_not() const { return is_app() && Z3_OP_NOT == decl().decl_kind(); }
        bool is_and() const { return is_app() && Z3_OP_AND == decl().decl_kind(); }
        bool is_or() const  { return is_app() && Z3_OP_OR  == decl().decl_kind(); }
        bool is_xor() const { return is_app() && Z3_OP_XOR  == decl().decl_kind(); }
        bool is_implies() const { return is_app() && Z3_OP_IMPLIES  == decl().decl_kind(); }
        bool is_eq() const { return is_app() && Z3_OP_EQ == decl().decl_kind(); }
        bool is_ite() const { return is_app() && Z3_OP_ITE == decl().decl_kind(); }
        bool is_distinct() const { return is_app() && Z3_OP_DISTINCT == decl().decl_kind(); }

        friend expr distinct(expr_vector const& args);
        friend expr concat(expr const& a, expr const& b);
        friend expr concat(expr_vector const& args);

        friend expr operator==(expr const & a, expr const & b);
        friend expr operator==(expr const & a, int b);
        friend expr operator==(int a, expr const & b);

        friend expr operator!=(expr const & a, expr const & b);
        friend expr operator!=(expr const & a, int b);
        friend expr operator!=(int a, expr const & b);

        friend expr operator+(expr const & a, expr const & b);
        friend expr operator+(expr const & a, int b);
        friend expr operator+(int a, expr const & b);
        friend expr sum(expr_vector const& args);

        friend expr operator*(expr const & a, expr const & b);
        friend expr operator*(expr const & a, int b);
        friend expr operator*(int a, expr const & b);

        /*  \brief Power operator  */
        friend expr pw(expr const & a, expr const & b);
        friend expr pw(expr const & a, int b);
        friend expr pw(int a, expr const & b);

        /* \brief mod operator */
        friend expr mod(expr const& a, expr const& b);
        friend expr mod(expr const& a, int b);
        friend expr mod(int a, expr const& b);

        /* \brief rem operator */
        friend expr rem(expr const& a, expr const& b);
        friend expr rem(expr const& a, int b);
        friend expr rem(int a, expr const& b);

        friend expr is_int(expr const& e);

        friend expr operator/(expr const & a, expr const & b);
        friend expr operator/(expr const & a, int b);
        friend expr operator/(int a, expr const & b);

        friend expr operator-(expr const & a);

        friend expr operator-(expr const & a, expr const & b);
        friend expr operator-(expr const & a, int b);
        friend expr operator-(int a, expr const & b);

        friend expr operator<=(expr const & a, expr const & b);
        friend expr operator<=(expr const & a, int b);
        friend expr operator<=(int a, expr const & b);


        friend expr operator>=(expr const & a, expr const & b);
        friend expr operator>=(expr const & a, int b);
        friend expr operator>=(int a, expr const & b);

        friend expr operator<(expr const & a, expr const & b);
        friend expr operator<(expr const & a, int b);
        friend expr operator<(int a, expr const & b);

        friend expr operator>(expr const & a, expr const & b);
        friend expr operator>(expr const & a, int b);
        friend expr operator>(int a, expr const & b);

        friend expr pble(expr_vector const& es, int const * coeffs, int bound);
        friend expr pbge(expr_vector const& es, int const * coeffs, int bound);
        friend expr pbeq(expr_vector const& es, int const * coeffs, int bound);
        friend expr atmost(expr_vector const& es, unsigned bound);
        friend expr atleast(expr_vector const& es, unsigned bound);

        friend expr operator&(expr const & a, expr const & b);
        friend expr operator&(expr const & a, int b);
        friend expr operator&(int a, expr const & b);

        friend expr operator^(expr const & a, expr const & b);
        friend expr operator^(expr const & a, int b);
        friend expr operator^(int a, expr const & b);

        friend expr operator|(expr const & a, expr const & b);
        friend expr operator|(expr const & a, int b);
        friend expr operator|(int a, expr const & b);
        friend expr nand(expr const& a, expr const& b);
        friend expr nor(expr const& a, expr const& b);
        friend expr xnor(expr const& a, expr const& b);

        friend expr min(expr const& a, expr const& b);
        friend expr max(expr const& a, expr const& b);

        friend expr bv2int(expr const& a, bool is_signed); 
        friend expr int2bv(unsigned n, expr const& a);
        friend expr bvadd_no_overflow(expr const& a, expr const& b, bool is_signed);
        friend expr bvadd_no_underflow(expr const& a, expr const& b);
        friend expr bvsub_no_overflow(expr const& a, expr const& b);
        friend expr bvsub_no_underflow(expr const& a, expr const& b, bool is_signed);
        friend expr bvsdiv_no_overflow(expr const& a, expr const& b);
        friend expr bvneg_no_overflow(expr const& a);
        friend expr bvmul_no_overflow(expr const& a, expr const& b, bool is_signed);
        friend expr bvmul_no_underflow(expr const& a, expr const& b);
        
        expr rotate_left(unsigned i) { Z3_ast r = Z3_mk_rotate_left(ctx(), i, *this); ctx().check_error(); return expr(ctx(), r); }
        expr rotate_right(unsigned i) { Z3_ast r = Z3_mk_rotate_right(ctx(), i, *this); ctx().check_error(); return expr(ctx(), r); }
        expr repeat(unsigned i) { Z3_ast r = Z3_mk_repeat(ctx(), i, *this); ctx().check_error(); return expr(ctx(), r); }

        friend expr bvredor(expr const & a);
        friend expr bvredand(expr const & a);

        friend expr abs(expr const & a);
        friend expr sqrt(expr const & a, expr const & rm);
        friend expr fp_eq(expr const & a, expr const & b);

        friend expr operator~(expr const & a);
        expr extract(unsigned hi, unsigned lo) const { Z3_ast r = Z3_mk_extract(ctx(), hi, lo, *this); ctx().check_error(); return expr(ctx(), r); }
        unsigned lo() const { assert (is_app() && Z3_get_decl_num_parameters(ctx(), decl()) == 2); return static_cast<unsigned>(Z3_get_decl_int_parameter(ctx(), decl(), 1)); }
        unsigned hi() const { assert (is_app() && Z3_get_decl_num_parameters(ctx(), decl()) == 2); return static_cast<unsigned>(Z3_get_decl_int_parameter(ctx(), decl(), 0)); }

        /**
           \brief FloatingPoint fused multiply-add.
          */
        friend expr fma(expr const& a, expr const& b, expr const& c, expr const& rm);

        /**
           \brief Create an expression of FloatingPoint sort from three bit-vector expressions
        */
        friend expr fpa_fp(expr const& sgn, expr const& exp, expr const& sig);

        /**
           \brief Conversion of a floating-point term into a signed bit-vector.
        */
        friend expr fpa_to_sbv(expr const& t, unsigned sz);

        /**
           \brief Conversion of a floating-point term into an unsigned bit-vector.
        */
        friend expr fpa_to_ubv(expr const& t, unsigned sz);

        /**
           \brief Conversion of a signed bit-vector term into a floating-point.
        */
        friend expr sbv_to_fpa(expr const& t, sort s);

        /**
           \brief Conversion of an unsigned bit-vector term into a floating-point.
        */
        friend expr ubv_to_fpa(expr const& t, sort s);

        /**
           \brief Conversion of a floating-point term into another floating-point.
        */
        friend expr fpa_to_fpa(expr const& t, sort s);

        /**
           \brief Round a floating-point term into its closest integer.
        */
        friend expr round_fpa_to_closest_integer(expr const& t);

        /**
           \brief sequence and regular expression operations.
           + is overloaded as sequence concatenation and regular expression union.
           concat is overloaded to handle sequences and regular expressions
        */
        expr extract(expr const& offset, expr const& length) const {
            check_context(*this, offset); check_context(offset, length);
            Z3_ast r = Z3_mk_seq_extract(ctx(), *this, offset, length); check_error(); return expr(ctx(), r);
        }
        expr replace(expr const& src, expr const& dst) const {
            check_context(*this, src); check_context(src, dst);
            Z3_ast r = Z3_mk_seq_replace(ctx(), *this, src, dst);
            check_error();
            return expr(ctx(), r);
        }
        expr unit() const {
            Z3_ast r = Z3_mk_seq_unit(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr contains(expr const& s) const {
            check_context(*this, s);
            Z3_ast r = Z3_mk_seq_contains(ctx(), *this, s);
            check_error();
            return expr(ctx(), r);
        }
        expr at(expr const& index) const {
            check_context(*this, index);
            Z3_ast r = Z3_mk_seq_at(ctx(), *this, index);
            check_error();
            return expr(ctx(), r);
        }
        expr nth(expr const& index) const {
            check_context(*this, index);
            Z3_ast r = Z3_mk_seq_nth(ctx(), *this, index);
            check_error();
            return expr(ctx(), r);
        }
        expr length() const {
            Z3_ast r = Z3_mk_seq_length(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr stoi() const {
            Z3_ast r = Z3_mk_str_to_int(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr itos() const {
            Z3_ast r = Z3_mk_int_to_str(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr ubvtos() const {
            Z3_ast r = Z3_mk_ubv_to_str(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr sbvtos() const {
            Z3_ast r = Z3_mk_sbv_to_str(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr char_to_int() const {
            Z3_ast r = Z3_mk_char_to_int(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr char_to_bv() const {
            Z3_ast r = Z3_mk_char_to_bv(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr char_from_bv() const {
            Z3_ast r = Z3_mk_char_from_bv(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
        expr is_digit() const {
            Z3_ast r = Z3_mk_char_is_digit(ctx(), *this);
            check_error();
            return expr(ctx(), r);
        }
 
        friend expr range(expr const& lo, expr const& hi);
        /**
           \brief create a looping regular expression.
        */
        expr loop(unsigned lo) {
            Z3_ast r = Z3_mk_re_loop(ctx(), m_ast, lo, 0);
            check_error();
            return expr(ctx(), r);
        }
        expr loop(unsigned lo, unsigned hi) {
            Z3_ast r = Z3_mk_re_loop(ctx(), m_ast, lo, hi);
            check_error();
            return expr(ctx(), r);
        }

        /**
         * index operator defined on arrays and sequences.
         */
        expr operator[](expr const& index) const {
            assert(is_array() || is_seq());
            if (is_array()) {
                return select(*this, index);
            }
            return nth(index);            
        }

        expr operator[](expr_vector const& index) const {
            return select(*this, index);
        }

        /**
           \brief Return a simplified version of this expression.
        */
        expr simplify() const { Z3_ast r = Z3_simplify(ctx(), m_ast); check_error(); return expr(ctx(), r); }
        /**
           \brief Return a simplified version of this expression. The parameter \c p is a set of parameters for the Z3 simplifier.
        */
        expr simplify(params const & p) const { Z3_ast r = Z3_simplify_ex(ctx(), m_ast, p); check_error(); return expr(ctx(), r); }

        /**
           \brief Apply substitution. Replace src expressions by dst.
        */
        expr substitute(expr_vector const& src, expr_vector const& dst);

        /**
           \brief Apply substitution. Replace bound variables by expressions.
        */
        expr substitute(expr_vector const& dst);


    class iterator {
            expr& e;
            unsigned i;
        public:
            iterator(expr& e, unsigned i): e(e), i(i) {}
            bool operator==(iterator const& other) noexcept {
                return i == other.i;
            }
            bool operator!=(iterator const& other) noexcept {
                return i != other.i;
            }
            expr operator*() const { return e.arg(i); }
            iterator& operator++() { ++i; return *this; }
            iterator operator++(int) { assert(false); return *this; }
        };

        iterator begin() { return iterator(*this, 0); }
        iterator end() { return iterator(*this, is_app() ? num_args() : 0); }

   };

#define _Z3_MK_BIN_(a, b, binop)                        \
    check_context(a, b);                                \
    Z3_ast r = binop(a.ctx(), a, b);                    \
    a.check_error();                                    \
    return expr(a.ctx(), r);                            \


    inline expr implies(expr const & a, expr const & b) {
        assert(a.is_bool() && b.is_bool());
        _Z3_MK_BIN_(a, b, Z3_mk_implies);
    }
    inline expr implies(expr const & a, bool b) { return implies(a, a.ctx().bool_val(b)); }
    inline expr implies(bool a, expr const & b) { return implies(b.ctx().bool_val(a), b); }


    inline expr pw(expr const & a, expr const & b) { _Z3_MK_BIN_(a, b, Z3_mk_power);   }
    inline expr pw(expr const & a, int b) { return pw(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr pw(int a, expr const & b) { return pw(b.ctx().num_val(a, b.get_sort()), b); }

    inline expr mod(expr const& a, expr const& b) { 
        if (a.is_bv()) {
            _Z3_MK_BIN_(a, b, Z3_mk_bvsmod);   
        }
        else {
            _Z3_MK_BIN_(a, b, Z3_mk_mod);   
        }
    }
    inline expr mod(expr const & a, int b) { return mod(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr mod(int a, expr const & b) { return mod(b.ctx().num_val(a, b.get_sort()), b); }

    inline expr operator%(expr const& a, expr const& b) { return mod(a, b); }
    inline expr operator%(expr const& a, int b) { return mod(a, b); }
    inline expr operator%(int a, expr const& b) { return mod(a, b); }


    inline expr rem(expr const& a, expr const& b) {
        if (a.is_fpa() && b.is_fpa()) {
            _Z3_MK_BIN_(a, b, Z3_mk_fpa_rem);
        } else {
            _Z3_MK_BIN_(a, b, Z3_mk_rem);
        }
    }
    inline expr rem(expr const & a, int b) { return rem(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr rem(int a, expr const & b) { return rem(b.ctx().num_val(a, b.get_sort()), b); }

#undef _Z3_MK_BIN_

#define _Z3_MK_UN_(a, mkun)                     \
    Z3_ast r = mkun(a.ctx(), a);                \
    a.check_error();                            \
    return expr(a.ctx(), r);                    \


    inline expr operator!(expr const & a) { assert(a.is_bool()); _Z3_MK_UN_(a, Z3_mk_not); }

    inline expr is_int(expr const& e) { _Z3_MK_UN_(e, Z3_mk_is_int); }

#undef _Z3_MK_UN_

    inline expr operator&&(expr const & a, expr const & b) {
        check_context(a, b);
        assert(a.is_bool() && b.is_bool());
        Z3_ast args[2] = { a, b };
        Z3_ast r = Z3_mk_and(a.ctx(), 2, args);
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr operator&&(expr const & a, bool b) { return a && a.ctx().bool_val(b); }
    inline expr operator&&(bool a, expr const & b) { return b.ctx().bool_val(a) && b; }

    inline expr operator||(expr const & a, expr const & b) {
        check_context(a, b);
        assert(a.is_bool() && b.is_bool());
        Z3_ast args[2] = { a, b };
        Z3_ast r = Z3_mk_or(a.ctx(), 2, args);
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr operator||(expr const & a, bool b) { return a || a.ctx().bool_val(b); }

    inline expr operator||(bool a, expr const & b) { return b.ctx().bool_val(a) || b; }

    inline expr operator==(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = Z3_mk_eq(a.ctx(), a, b);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator==(expr const & a, int b) { assert(a.is_arith() || a.is_bv() || a.is_fpa()); return a == a.ctx().num_val(b, a.get_sort()); }
    inline expr operator==(int a, expr const & b) { assert(b.is_arith() || b.is_bv() || b.is_fpa()); return b.ctx().num_val(a, b.get_sort()) == b; }
    inline expr operator==(expr const & a, double b) { assert(a.is_fpa()); return a == a.ctx().fpa_val(b); }
    inline expr operator==(double a, expr const & b) { assert(b.is_fpa()); return b.ctx().fpa_val(a) == b; }

    inline expr operator!=(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast args[2] = { a, b };
        Z3_ast r = Z3_mk_distinct(a.ctx(), 2, args);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator!=(expr const & a, int b) { assert(a.is_arith() || a.is_bv() || a.is_fpa()); return a != a.ctx().num_val(b, a.get_sort()); }
    inline expr operator!=(int a, expr const & b) { assert(b.is_arith() || b.is_bv() || b.is_fpa()); return b.ctx().num_val(a, b.get_sort()) != b; }
    inline expr operator!=(expr const & a, double b) { assert(a.is_fpa()); return a != a.ctx().fpa_val(b); }
    inline expr operator!=(double a, expr const & b) { assert(b.is_fpa()); return b.ctx().fpa_val(a) != b; }

    inline expr operator+(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            Z3_ast args[2] = { a, b };
            r = Z3_mk_add(a.ctx(), 2, args);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvadd(a.ctx(), a, b);
        }
        else if (a.is_seq() && b.is_seq()) {
            return concat(a, b);
        }
        else if (a.is_re() && b.is_re()) {
            Z3_ast _args[2] = { a, b };
            r = Z3_mk_re_union(a.ctx(), 2, _args);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_add(a.ctx(), a.ctx().fpa_rounding_mode(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator+(expr const & a, int b) { return a + a.ctx().num_val(b, a.get_sort()); }
    inline expr operator+(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) + b; }

    inline expr operator*(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            Z3_ast args[2] = { a, b };
            r = Z3_mk_mul(a.ctx(), 2, args);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvmul(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_mul(a.ctx(), a.ctx().fpa_rounding_mode(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator*(expr const & a, int b) { return a * a.ctx().num_val(b, a.get_sort()); }
    inline expr operator*(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) * b; }


    inline expr operator>=(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            r = Z3_mk_ge(a.ctx(), a, b);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvsge(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_geq(a.ctx(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr operator/(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            r = Z3_mk_div(a.ctx(), a, b);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvsdiv(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_div(a.ctx(), a.ctx().fpa_rounding_mode(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator/(expr const & a, int b) { return a / a.ctx().num_val(b, a.get_sort()); }
    inline expr operator/(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) / b; }

    inline expr operator-(expr const & a) {
        Z3_ast r = 0;
        if (a.is_arith()) {
            r = Z3_mk_unary_minus(a.ctx(), a);
        }
        else if (a.is_bv()) {
            r = Z3_mk_bvneg(a.ctx(), a);
        }
        else if (a.is_fpa()) {
            r = Z3_mk_fpa_neg(a.ctx(), a);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr operator-(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            Z3_ast args[2] = { a, b };
            r = Z3_mk_sub(a.ctx(), 2, args);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvsub(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_sub(a.ctx(), a.ctx().fpa_rounding_mode(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator-(expr const & a, int b) { return a - a.ctx().num_val(b, a.get_sort()); }
    inline expr operator-(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) - b; }

    inline expr operator<=(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            r = Z3_mk_le(a.ctx(), a, b);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvsle(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_leq(a.ctx(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator<=(expr const & a, int b) { return a <= a.ctx().num_val(b, a.get_sort()); }
    inline expr operator<=(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) <= b; }

    inline expr operator>=(expr const & a, int b) { return a >= a.ctx().num_val(b, a.get_sort()); }
    inline expr operator>=(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) >= b; }

    inline expr operator<(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            r = Z3_mk_lt(a.ctx(), a, b);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvslt(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_lt(a.ctx(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator<(expr const & a, int b) { return a < a.ctx().num_val(b, a.get_sort()); }
    inline expr operator<(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) < b; }

    inline expr operator>(expr const & a, expr const & b) {
        check_context(a, b);
        Z3_ast r = 0;
        if (a.is_arith() && b.is_arith()) {
            r = Z3_mk_gt(a.ctx(), a, b);
        }
        else if (a.is_bv() && b.is_bv()) {
            r = Z3_mk_bvsgt(a.ctx(), a, b);
        }
        else if (a.is_fpa() && b.is_fpa()) {
            r = Z3_mk_fpa_gt(a.ctx(), a, b);
        }
        else {
            // operator is not supported by given arguments.
            assert(false);
        }
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator>(expr const & a, int b) { return a > a.ctx().num_val(b, a.get_sort()); }
    inline expr operator>(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) > b; }

    inline expr operator&(expr const & a, expr const & b) { if (a.is_bool()) return a && b; check_context(a, b); Z3_ast r = Z3_mk_bvand(a.ctx(), a, b); return expr(a.ctx(), r); }
    inline expr operator&(expr const & a, int b) { return a & a.ctx().num_val(b, a.get_sort()); }
    inline expr operator&(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) & b; }

    inline expr operator^(expr const & a, expr const & b) { check_context(a, b); Z3_ast r = a.is_bool() ? Z3_mk_xor(a.ctx(), a, b) : Z3_mk_bvxor(a.ctx(), a, b); return expr(a.ctx(), r); }
    inline expr operator^(expr const & a, int b) { return a ^ a.ctx().num_val(b, a.get_sort()); }
    inline expr operator^(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) ^ b; }

    inline expr operator|(expr const & a, expr const & b) { if (a.is_bool()) return a || b; check_context(a, b); Z3_ast r = Z3_mk_bvor(a.ctx(), a, b); return expr(a.ctx(), r); }
    inline expr operator|(expr const & a, int b) { return a | a.ctx().num_val(b, a.get_sort()); }
    inline expr operator|(int a, expr const & b) { return b.ctx().num_val(a, b.get_sort()) | b; }

    inline expr nand(expr const& a, expr const& b) { if (a.is_bool()) return !(a && b); check_context(a, b); Z3_ast r = Z3_mk_bvnand(a.ctx(), a, b); return expr(a.ctx(), r); }
    inline expr nor(expr const& a, expr const& b) { if (a.is_bool()) return !(a || b); check_context(a, b); Z3_ast r = Z3_mk_bvnor(a.ctx(), a, b); return expr(a.ctx(), r); }
    inline expr xnor(expr const& a, expr const& b) { if (a.is_bool()) return !(a ^ b); check_context(a, b); Z3_ast r = Z3_mk_bvxnor(a.ctx(), a, b); return expr(a.ctx(), r); }
    inline expr min(expr const& a, expr const& b) { 
        check_context(a, b); 
        Z3_ast r;
        if (a.is_arith()) {
            r = Z3_mk_ite(a.ctx(), Z3_mk_ge(a.ctx(), a, b), b, a);
        }
        else if (a.is_bv()) {
            r = Z3_mk_ite(a.ctx(), Z3_mk_bvuge(a.ctx(), a, b), b, a);
        }
        else {
            assert(a.is_fpa());
            r = Z3_mk_fpa_min(a.ctx(), a, b); 
        }
        return expr(a.ctx(), r); 
    }
    inline expr max(expr const& a, expr const& b) { 
        check_context(a, b); 
        Z3_ast r;
        if (a.is_arith()) {
            r = Z3_mk_ite(a.ctx(), Z3_mk_ge(a.ctx(), a, b), a, b);
        }
        else if (a.is_bv()) {
            r = Z3_mk_ite(a.ctx(), Z3_mk_bvuge(a.ctx(), a, b), a, b);
        }
        else {
            assert(a.is_fpa());
            r = Z3_mk_fpa_max(a.ctx(), a, b); 
        }
        return expr(a.ctx(), r); 
    }
    inline expr bvredor(expr const & a) {
        assert(a.is_bv());
        Z3_ast r = Z3_mk_bvredor(a.ctx(), a);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr bvredand(expr const & a) {
        assert(a.is_bv());
        Z3_ast r = Z3_mk_bvredand(a.ctx(), a);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr abs(expr const & a) { 
        Z3_ast r;
        if (a.is_int()) {
            expr zero = a.ctx().int_val(0);
        expr ge = a >= zero;
        expr na = -a;
            r = Z3_mk_ite(a.ctx(), ge, a, na);	    
        }
        else if (a.is_real()) {
            expr zero = a.ctx().real_val(0);
        expr ge = a >= zero;
        expr na = -a;
            r = Z3_mk_ite(a.ctx(), ge, a, na);
        }
        else {
            r = Z3_mk_fpa_abs(a.ctx(), a); 
        }
        a.check_error();
        return expr(a.ctx(), r); 
    }
    inline expr sqrt(expr const & a, expr const& rm) {
        check_context(a, rm);
        assert(a.is_fpa());
        Z3_ast r = Z3_mk_fpa_sqrt(a.ctx(), rm, a);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr fp_eq(expr const & a, expr const & b) {
        check_context(a, b);
        assert(a.is_fpa());
        Z3_ast r = Z3_mk_fpa_eq(a.ctx(), a, b);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr operator~(expr const & a) { Z3_ast r = Z3_mk_bvnot(a.ctx(), a); return expr(a.ctx(), r); }

    inline expr fma(expr const& a, expr const& b, expr const& c, expr const& rm) {
        check_context(a, b); check_context(a, c); check_context(a, rm);
        assert(a.is_fpa() && b.is_fpa() && c.is_fpa());
        Z3_ast r = Z3_mk_fpa_fma(a.ctx(), rm, a, b, c);
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr fpa_fp(expr const& sgn, expr const& exp, expr const& sig) {
        check_context(sgn, exp); check_context(exp, sig);
        assert(sgn.is_bv() && exp.is_bv() && sig.is_bv());
        Z3_ast r = Z3_mk_fpa_fp(sgn.ctx(), sgn, exp, sig);
        sgn.check_error();
        return expr(sgn.ctx(), r);
    }

    inline expr fpa_to_sbv(expr const& t, unsigned sz) {
        assert(t.is_fpa());
        Z3_ast r = Z3_mk_fpa_to_sbv(t.ctx(), t.ctx().fpa_rounding_mode(), t, sz);
        t.check_error();
        return expr(t.ctx(), r);
    }

    inline expr fpa_to_ubv(expr const& t, unsigned sz) {
        assert(t.is_fpa());
        Z3_ast r = Z3_mk_fpa_to_ubv(t.ctx(), t.ctx().fpa_rounding_mode(), t, sz);
        t.check_error();
        return expr(t.ctx(), r);
    }

    inline expr sbv_to_fpa(expr const& t, sort s) {
        assert(t.is_bv());
        Z3_ast r = Z3_mk_fpa_to_fp_signed(t.ctx(), t.ctx().fpa_rounding_mode(), t, s);
        t.check_error();
        return expr(t.ctx(), r);
    }

    inline expr ubv_to_fpa(expr const& t, sort s) {
        assert(t.is_bv());
        Z3_ast r = Z3_mk_fpa_to_fp_unsigned(t.ctx(), t.ctx().fpa_rounding_mode(), t, s);
        t.check_error();
        return expr(t.ctx(), r);
    }

    inline expr fpa_to_fpa(expr const& t, sort s) {
        assert(t.is_fpa());
        Z3_ast r = Z3_mk_fpa_to_fp_float(t.ctx(), t.ctx().fpa_rounding_mode(), t, s);
        t.check_error();
        return expr(t.ctx(), r);
    }

    inline expr round_fpa_to_closest_integer(expr const& t) {
        assert(t.is_fpa());
        Z3_ast r = Z3_mk_fpa_round_to_integral(t.ctx(), t.ctx().fpa_rounding_mode(), t);
        t.check_error();
        return expr(t.ctx(), r);
    }

    /**
       \brief Create the if-then-else expression <tt>ite(c, t, e)</tt>

       \pre c.is_bool()
    */
    inline expr ite(expr const & c, expr const & t, expr const & e) {
        check_context(c, t); check_context(c, e);
        assert(c.is_bool());
        Z3_ast r = Z3_mk_ite(c.ctx(), c, t, e);
        c.check_error();
        return expr(c.ctx(), r);
    }


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
       \brief signed less than or equal to operator for bitvectors.
    */
    inline expr sle(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvsle(a.ctx(), a, b)); }
    inline expr sle(expr const & a, int b) { return sle(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr sle(int a, expr const & b) { return sle(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief signed less than operator for bitvectors.
    */
    inline expr slt(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvslt(a.ctx(), a, b)); }
    inline expr slt(expr const & a, int b) { return slt(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr slt(int a, expr const & b) { return slt(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief signed greater than or equal to operator for bitvectors.
    */
    inline expr sge(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvsge(a.ctx(), a, b)); }
    inline expr sge(expr const & a, int b) { return sge(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr sge(int a, expr const & b) { return sge(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief signed greater than operator for bitvectors.
    */
    inline expr sgt(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvsgt(a.ctx(), a, b)); }
    inline expr sgt(expr const & a, int b) { return sgt(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr sgt(int a, expr const & b) { return sgt(b.ctx().num_val(a, b.get_sort()), b); }


    /**
       \brief unsigned less than or equal to operator for bitvectors.
    */
    inline expr ule(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvule(a.ctx(), a, b)); }
    inline expr ule(expr const & a, int b) { return ule(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ule(int a, expr const & b) { return ule(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief unsigned less than operator for bitvectors.
    */
    inline expr ult(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvult(a.ctx(), a, b)); }
    inline expr ult(expr const & a, int b) { return ult(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ult(int a, expr const & b) { return ult(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief unsigned greater than or equal to operator for bitvectors.
    */
    inline expr uge(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvuge(a.ctx(), a, b)); }
    inline expr uge(expr const & a, int b) { return uge(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr uge(int a, expr const & b) { return uge(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief unsigned greater than operator for bitvectors.
    */
    inline expr ugt(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvugt(a.ctx(), a, b)); }
    inline expr ugt(expr const & a, int b) { return ugt(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ugt(int a, expr const & b) { return ugt(b.ctx().num_val(a, b.get_sort()), b); }
    /**
       \brief unsigned division operator for bitvectors.
    */
    inline expr udiv(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvudiv(a.ctx(), a, b)); }
    inline expr udiv(expr const & a, int b) { return udiv(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr udiv(int a, expr const & b) { return udiv(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief signed remainder operator for bitvectors
    */
    inline expr srem(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvsrem(a.ctx(), a, b)); }
    inline expr srem(expr const & a, int b) { return srem(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr srem(int a, expr const & b) { return srem(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief signed modulus operator for bitvectors
    */
    inline expr smod(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvsmod(a.ctx(), a, b)); }
    inline expr smod(expr const & a, int b) { return smod(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr smod(int a, expr const & b) { return smod(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief unsigned reminder operator for bitvectors
    */
    inline expr urem(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvurem(a.ctx(), a, b)); }
    inline expr urem(expr const & a, int b) { return urem(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr urem(int a, expr const & b) { return urem(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief shift left operator for bitvectors
    */
    inline expr shl(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvshl(a.ctx(), a, b)); }
    inline expr shl(expr const & a, int b) { return shl(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr shl(int a, expr const & b) { return shl(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief logic shift right operator for bitvectors
    */
    inline expr lshr(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvlshr(a.ctx(), a, b)); }
    inline expr lshr(expr const & a, int b) { return lshr(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr lshr(int a, expr const & b) { return lshr(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief arithmetic shift right operator for bitvectors
    */
    inline expr ashr(expr const & a, expr const & b) { return to_expr(a.ctx(), Z3_mk_bvashr(a.ctx(), a, b)); }
    inline expr ashr(expr const & a, int b) { return ashr(a, a.ctx().num_val(b, a.get_sort())); }
    inline expr ashr(int a, expr const & b) { return ashr(b.ctx().num_val(a, b.get_sort()), b); }

    /**
       \brief Extend the given bit-vector with zeros to the (unsigned) equivalent bitvector of size m+i, where m is the size of the given bit-vector.
    */
    inline expr zext(expr const & a, unsigned i) { return to_expr(a.ctx(), Z3_mk_zero_ext(a.ctx(), i, a)); }

    /**
       \brief bit-vector and integer conversions.
    */
    inline expr bv2int(expr const& a, bool is_signed) { Z3_ast r = Z3_mk_bv2int(a.ctx(), a, is_signed); a.check_error(); return expr(a.ctx(), r); }
    inline expr int2bv(unsigned n, expr const& a) { Z3_ast r = Z3_mk_int2bv(a.ctx(), n, a); a.check_error(); return expr(a.ctx(), r); }

    /**
       \brief bit-vector overflow/underflow checks
    */
    inline expr bvadd_no_overflow(expr const& a, expr const& b, bool is_signed) { 
        check_context(a, b); Z3_ast r = Z3_mk_bvadd_no_overflow(a.ctx(), a, b, is_signed); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvadd_no_underflow(expr const& a, expr const& b) {
        check_context(a, b); Z3_ast r = Z3_mk_bvadd_no_underflow(a.ctx(), a, b); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvsub_no_overflow(expr const& a, expr const& b) {
        check_context(a, b); Z3_ast r = Z3_mk_bvsub_no_overflow(a.ctx(), a, b); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvsub_no_underflow(expr const& a, expr const& b, bool is_signed) {
        check_context(a, b); Z3_ast r = Z3_mk_bvsub_no_underflow(a.ctx(), a, b, is_signed); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvsdiv_no_overflow(expr const& a, expr const& b) {
        check_context(a, b); Z3_ast r = Z3_mk_bvsdiv_no_overflow(a.ctx(), a, b); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvneg_no_overflow(expr const& a) {
        Z3_ast r = Z3_mk_bvneg_no_overflow(a.ctx(), a); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvmul_no_overflow(expr const& a, expr const& b, bool is_signed) {
        check_context(a, b); Z3_ast r = Z3_mk_bvmul_no_overflow(a.ctx(), a, b, is_signed); a.check_error(); return expr(a.ctx(), r); 
    }
    inline expr bvmul_no_underflow(expr const& a, expr const& b) {
        check_context(a, b); Z3_ast r = Z3_mk_bvmul_no_underflow(a.ctx(), a, b); a.check_error(); return expr(a.ctx(), r); 
    }


    /**
       \brief Sign-extend of the given bit-vector to the (signed) equivalent bitvector of size m+i, where m is the size of the given bit-vector.
    */
    inline expr sext(expr const & a, unsigned i) { return to_expr(a.ctx(), Z3_mk_sign_ext(a.ctx(), i, a)); }

    inline func_decl linear_order(sort const& a, unsigned index) {
        return to_func_decl(a.ctx(), Z3_mk_linear_order(a.ctx(), a, index));
    }
    inline func_decl partial_order(sort const& a, unsigned index) {
        return to_func_decl(a.ctx(), Z3_mk_partial_order(a.ctx(), a, index));
    }
    inline func_decl piecewise_linear_order(sort const& a, unsigned index) {
        return to_func_decl(a.ctx(), Z3_mk_piecewise_linear_order(a.ctx(), a, index));
    }
    inline func_decl tree_order(sort const& a, unsigned index) {
        return to_func_decl(a.ctx(), Z3_mk_tree_order(a.ctx(), a, index));
    }

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
    template<typename T2>
    array<T>::array(ast_vector_tpl<T2> const & v):m_array(new T[v.size()]), m_size(v.size()) {
        for (unsigned i = 0; i < m_size; i++) {
            m_array[i] = v[i];
        }
    }

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
    inline expr forall(expr_vector const & xs, expr const & b) {
        array<Z3_app> vars(xs);
        Z3_ast r = Z3_mk_forall_const(b.ctx(), 0, vars.size(), vars.ptr(), 0, 0, b); b.check_error(); return expr(b.ctx(), r);
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
    inline expr exists(expr_vector const & xs, expr const & b) {
        array<Z3_app> vars(xs);
        Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, vars.size(), vars.ptr(), 0, 0, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr lambda(expr const & x, expr const & b) {
        check_context(x, b);
        Z3_app vars[] = {(Z3_app) x};
        Z3_ast r = Z3_mk_lambda_const(b.ctx(), 1, vars, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr lambda(expr const & x1, expr const & x2, expr const & b) {
        check_context(x1, b); check_context(x2, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2};
        Z3_ast r = Z3_mk_lambda_const(b.ctx(), 2, vars, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr lambda(expr const & x1, expr const & x2, expr const & x3, expr const & b) {
        check_context(x1, b); check_context(x2, b); check_context(x3, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3 };
        Z3_ast r = Z3_mk_lambda_const(b.ctx(), 3, vars, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr lambda(expr const & x1, expr const & x2, expr const & x3, expr const & x4, expr const & b) {
        check_context(x1, b); check_context(x2, b); check_context(x3, b); check_context(x4, b);
        Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3, (Z3_app) x4 };
        Z3_ast r = Z3_mk_lambda_const(b.ctx(), 4, vars, b); b.check_error(); return expr(b.ctx(), r);
    }
    inline expr lambda(expr_vector const & xs, expr const & b) {
        array<Z3_app> vars(xs);
        Z3_ast r = Z3_mk_lambda_const(b.ctx(), vars.size(), vars.ptr(), b); b.check_error(); return expr(b.ctx(), r);
    }

    inline expr pble(expr_vector const& es, int const* coeffs, int bound) {
        assert(es.size() > 0);
        context& ctx = es[0].ctx();
        array<Z3_ast> _es(es);
        Z3_ast r = Z3_mk_pble(ctx, _es.size(), _es.ptr(), coeffs, bound);
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr pbge(expr_vector const& es, int const* coeffs, int bound) {
        assert(es.size() > 0);
        context& ctx = es[0].ctx();
        array<Z3_ast> _es(es);
        Z3_ast r = Z3_mk_pbge(ctx, _es.size(), _es.ptr(), coeffs, bound);
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr pbeq(expr_vector const& es, int const* coeffs, int bound) {
        assert(es.size() > 0);
        context& ctx = es[0].ctx();
        array<Z3_ast> _es(es);
        Z3_ast r = Z3_mk_pbeq(ctx, _es.size(), _es.ptr(), coeffs, bound);
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr atmost(expr_vector const& es, unsigned bound) {
        assert(es.size() > 0);
        context& ctx = es[0].ctx();
        array<Z3_ast> _es(es);
        Z3_ast r = Z3_mk_atmost(ctx, _es.size(), _es.ptr(), bound);
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr atleast(expr_vector const& es, unsigned bound) {
        assert(es.size() > 0);
        context& ctx = es[0].ctx();
        array<Z3_ast> _es(es);
        Z3_ast r = Z3_mk_atleast(ctx, _es.size(), _es.ptr(), bound);
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr sum(expr_vector const& args) {
        assert(args.size() > 0);
        context& ctx = args[0].ctx();
        array<Z3_ast> _args(args);
        Z3_ast r = Z3_mk_add(ctx, _args.size(), _args.ptr());
        ctx.check_error();
        return expr(ctx, r);
    }

    inline expr distinct(expr_vector const& args) {
        assert(args.size() > 0);
        context& ctx = args[0].ctx();
        array<Z3_ast> _args(args);
        Z3_ast r = Z3_mk_distinct(ctx, _args.size(), _args.ptr());
        ctx.check_error();
        return expr(ctx, r);
    }

    inline expr concat(expr const& a, expr const& b) {
        check_context(a, b);
        Z3_ast r;
        if (Z3_is_seq_sort(a.ctx(), a.get_sort())) {
            Z3_ast _args[2] = { a, b };
            r = Z3_mk_seq_concat(a.ctx(), 2, _args);
        }
        else if (Z3_is_re_sort(a.ctx(), a.get_sort())) {
            Z3_ast _args[2] = { a, b };
            r = Z3_mk_re_concat(a.ctx(), 2, _args);
        }
        else {
            r = Z3_mk_concat(a.ctx(), a, b);
        }
        a.ctx().check_error();
        return expr(a.ctx(), r);
    }

    inline expr concat(expr_vector const& args) {
        Z3_ast r;
        assert(args.size() > 0);
        if (args.size() == 1) {
            return args[0];
        }
        context& ctx = args[0].ctx();
        array<Z3_ast> _args(args);
        if (Z3_is_seq_sort(ctx, args[0].get_sort())) {
            r = Z3_mk_seq_concat(ctx, _args.size(), _args.ptr());
        }
        else if (Z3_is_re_sort(ctx, args[0].get_sort())) {
            r = Z3_mk_re_concat(ctx, _args.size(), _args.ptr());
        }
        else {
            r = _args[args.size()-1];
            for (unsigned i = args.size()-1; i > 0; ) {
                --i;
                r = Z3_mk_concat(ctx, _args[i], r);
                ctx.check_error();
            }
        }
        ctx.check_error();
        return expr(ctx, r);
    }

    inline expr mk_or(expr_vector const& args) {
        array<Z3_ast> _args(args);
        Z3_ast r = Z3_mk_or(args.ctx(), _args.size(), _args.ptr());
        args.check_error();
        return expr(args.ctx(), r);
    }
    inline expr mk_and(expr_vector const& args) {
        array<Z3_ast> _args(args);
        Z3_ast r = Z3_mk_and(args.ctx(), _args.size(), _args.ptr());
        args.check_error();
        return expr(args.ctx(), r);
    }
    inline expr mk_xor(expr_vector const& args) {
        if (args.empty())
            return args.ctx().bool_val(false);
        expr r = args[0];
        for (unsigned i = 1; i < args.size(); ++i)
            r = r ^ args[i];
        return r;
    }


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
            object::operator=(s);
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
            object::operator=(s);
            m_interp = s.m_interp;
            return *this;
        }
        expr else_value() const { Z3_ast r = Z3_func_interp_get_else(ctx(), m_interp); check_error(); return expr(ctx(), r); }
        unsigned num_entries() const { unsigned r = Z3_func_interp_get_num_entries(ctx(), m_interp); check_error(); return r; }
        func_entry entry(unsigned i) const { Z3_func_entry e = Z3_func_interp_get_entry(ctx(), m_interp, i); check_error(); return func_entry(ctx(), e); }
        void add_entry(expr_vector const& args, expr& value) {
            Z3_func_interp_add_entry(ctx(), m_interp, args, value);
            check_error();
        }
        void set_else(expr& value) {
            Z3_func_interp_set_else(ctx(), m_interp, value);
            check_error();
        }
    };

    class model : public object {
        Z3_model m_model;
        void init(Z3_model m) {
            m_model = m;
            Z3_model_inc_ref(ctx(), m);
        }
    public:
        struct translate {};
        model(context & c):object(c) { init(Z3_mk_model(c)); }
        model(context & c, Z3_model m):object(c) { init(m); }
        model(model const & s):object(s) { init(s.m_model); }
        model(model& src, context& dst, translate) : object(dst) { init(Z3_model_translate(src.ctx(), src, dst)); }
        ~model() { Z3_model_dec_ref(ctx(), m_model); }
        operator Z3_model() const { return m_model; }
        model & operator=(model const & s) {
            Z3_model_inc_ref(s.ctx(), s.m_model);
            Z3_model_dec_ref(ctx(), m_model);
            object::operator=(s);
            m_model = s.m_model;
            return *this;
        }

        expr eval(expr const & n, bool model_completion=false) const {
            check_context(*this, n);
            Z3_ast r = 0;
            bool status = Z3_model_eval(ctx(), m_model, n, model_completion, &r);
            check_error();
            if (status == false && ctx().enable_exceptions())
                Z3_THROW(exception("failed to evaluate expression"));
            return expr(ctx(), r);
        }

        unsigned num_consts() const { return Z3_model_get_num_consts(ctx(), m_model); }
        unsigned num_funcs() const { return Z3_model_get_num_funcs(ctx(), m_model); }
        func_decl get_const_decl(unsigned i) const { Z3_func_decl r = Z3_model_get_const_decl(ctx(), m_model, i); check_error(); return func_decl(ctx(), r); }
        func_decl get_func_decl(unsigned i) const { Z3_func_decl r = Z3_model_get_func_decl(ctx(), m_model, i); check_error(); return func_decl(ctx(), r); }
        unsigned size() const { return num_consts() + num_funcs(); }
        func_decl operator[](int i) const {
            assert(0 <= i);
            return static_cast<unsigned>(i) < num_consts() ? get_const_decl(i) : get_func_decl(i - num_consts());
        }

        // returns interpretation of constant declaration c.
        // If c is not assigned any value in the model it returns
        // an expression with a null ast reference.
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

        // returns true iff the model contains an interpretation
        // for function f.
        bool has_interp(func_decl f) const {
            check_context(*this, f);
            return Z3_model_has_interp(ctx(), m_model, f);
        }

        func_interp add_func_interp(func_decl& f, expr& else_val) {
            Z3_func_interp r = Z3_add_func_interp(ctx(), m_model, f, else_val);
            check_error();
            return func_interp(ctx(), r);
        }

        void add_const_interp(func_decl& f, expr& value) {
            Z3_add_const_interp(ctx(), m_model, f, value);
            check_error();
        }

        friend std::ostream & operator<<(std::ostream & out, model const & m);

        std::string to_string() const { return std::string(Z3_model_to_string(ctx(), m_model)); }
    };
    inline std::ostream & operator<<(std::ostream & out, model const & m) { out << Z3_model_to_string(m.ctx(), m); return out; }

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
            object::operator=(s);
            m_stats = s.m_stats;
            return *this;
        }
        unsigned size() const { return Z3_stats_size(ctx(), m_stats); }
        std::string key(unsigned i) const { Z3_string s = Z3_stats_get_key(ctx(), m_stats, i); check_error(); return s; }
        bool is_uint(unsigned i) const { bool r = Z3_stats_is_uint(ctx(), m_stats, i); check_error(); return r; }
        bool is_double(unsigned i) const { bool r = Z3_stats_is_double(ctx(), m_stats, i); check_error(); return r; }
        unsigned uint_value(unsigned i) const { unsigned r = Z3_stats_get_uint_value(ctx(), m_stats, i); check_error(); return r; }
        double double_value(unsigned i) const { double r = Z3_stats_get_double_value(ctx(), m_stats, i); check_error(); return r; }
        friend std::ostream & operator<<(std::ostream & out, stats const & s);
    };
    inline std::ostream & operator<<(std::ostream & out, stats const & s) { out << Z3_stats_to_string(s.ctx(), s); return out; }


    inline std::ostream & operator<<(std::ostream & out, check_result r) {
        if (r == unsat) out << "unsat";
        else if (r == sat) out << "sat";
        else out << "unknown";
        return out;
    }


    class solver : public object {
        Z3_solver m_solver;
        void init(Z3_solver s) {
            m_solver = s;
            Z3_solver_inc_ref(ctx(), s);
        }
    public:
        struct simple {};
        struct translate {};
        solver(context & c):object(c) { init(Z3_mk_solver(c)); }
        solver(context & c, simple):object(c) { init(Z3_mk_simple_solver(c)); }
        solver(context & c, Z3_solver s):object(c) { init(s); }
        solver(context & c, char const * logic):object(c) { init(Z3_mk_solver_for_logic(c, c.str_symbol(logic))); }
        solver(context & c, solver const& src, translate): object(c) { init(Z3_solver_translate(src.ctx(), src, c)); }
        solver(solver const & s):object(s) { init(s.m_solver); }
        ~solver() { Z3_solver_dec_ref(ctx(), m_solver); }
        operator Z3_solver() const { return m_solver; }
        solver & operator=(solver const & s) {
            Z3_solver_inc_ref(s.ctx(), s.m_solver);
            Z3_solver_dec_ref(ctx(), m_solver);
            object::operator=(s);
            m_solver = s.m_solver;
            return *this;
        }
        void set(params const & p) { Z3_solver_set_params(ctx(), m_solver, p); check_error(); }
        void set(char const * k, bool v) { params p(ctx()); p.set(k, v); set(p); }
        void set(char const * k, unsigned v) { params p(ctx()); p.set(k, v); set(p); }
        void set(char const * k, double v) { params p(ctx()); p.set(k, v); set(p); }
        void set(char const * k, symbol const & v) { params p(ctx()); p.set(k, v); set(p); }
        void set(char const * k, char const* v) { params p(ctx()); p.set(k, v); set(p); }
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
        void add(expr_vector const& v) { 
            check_context(*this, v); 
            for (unsigned i = 0; i < v.size(); ++i) 
                add(v[i]); 
        }
        void from_file(char const* file) { Z3_solver_from_file(ctx(), m_solver, file); ctx().check_parser_error(); }
        void from_string(char const* s) { Z3_solver_from_string(ctx(), m_solver, s); ctx().check_parser_error(); }

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
        check_result check(expr_vector const& assumptions) {
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
        check_result consequences(expr_vector& assumptions, expr_vector& vars, expr_vector& conseq) {
            Z3_lbool r = Z3_solver_get_consequences(ctx(), m_solver, assumptions, vars, conseq);
            check_error();
            return to_check_result(r);
        }
        std::string reason_unknown() const { Z3_string r = Z3_solver_get_reason_unknown(ctx(), m_solver); check_error(); return r; }
        stats statistics() const { Z3_stats r = Z3_solver_get_statistics(ctx(), m_solver); check_error(); return stats(ctx(), r); }
        expr_vector unsat_core() const { Z3_ast_vector r = Z3_solver_get_unsat_core(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector assertions() const { Z3_ast_vector r = Z3_solver_get_assertions(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector non_units() const { Z3_ast_vector r = Z3_solver_get_non_units(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector units() const { Z3_ast_vector r = Z3_solver_get_units(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector trail() const { Z3_ast_vector r = Z3_solver_get_trail(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector trail(array<unsigned>& levels) const { 
            Z3_ast_vector r = Z3_solver_get_trail(ctx(), m_solver); 
            check_error(); 
            expr_vector result(ctx(), r);
            unsigned sz = result.size();
            levels.resize(sz);
            Z3_solver_get_levels(ctx(), m_solver, r, sz, levels.ptr());
            check_error(); 
            return result; 
        }
        expr proof() const { Z3_ast r = Z3_solver_get_proof(ctx(), m_solver); check_error(); return expr(ctx(), r); }
        friend std::ostream & operator<<(std::ostream & out, solver const & s);

        std::string to_smt2(char const* status = "unknown") {
            array<Z3_ast> es(assertions());
            Z3_ast const* fmls = es.ptr();
            Z3_ast fml = 0;
            unsigned sz = es.size();
            if (sz > 0) {
                --sz;
                fml = fmls[sz];
            }
            else {
                fml = ctx().bool_val(true);
            }
            return std::string(Z3_benchmark_to_smtlib_string(
                                   ctx(),
                                   "", "", status, "",
                                   sz,
                                   fmls,
                                   fml));
        }

        std::string dimacs(bool include_names = true) const { return std::string(Z3_solver_to_dimacs_string(ctx(), m_solver, include_names)); }

        param_descrs get_param_descrs() { return param_descrs(ctx(), Z3_solver_get_param_descrs(ctx(), m_solver)); }


        expr_vector cube(expr_vector& vars, unsigned cutoff) {
            Z3_ast_vector r = Z3_solver_cube(ctx(), m_solver, vars, cutoff);
            check_error();
            return expr_vector(ctx(), r);
        }

        class cube_iterator {
            solver&      m_solver;
            unsigned&    m_cutoff;
            expr_vector& m_vars;
            expr_vector  m_cube;
            bool         m_end;
            bool         m_empty;

            void inc() {
                assert(!m_end && !m_empty);
                m_cube = m_solver.cube(m_vars, m_cutoff);
                m_cutoff = 0xFFFFFFFF;
                if (m_cube.size() == 1 && m_cube[0].is_false()) {
                    m_cube = z3::expr_vector(m_solver.ctx());
                    m_end = true;
                }
                else if (m_cube.empty()) {
                    m_empty = true;
                }
            }
        public:
            cube_iterator(solver& s, expr_vector& vars, unsigned& cutoff, bool end):
                m_solver(s),
                m_cutoff(cutoff),
                m_vars(vars),
                m_cube(s.ctx()),
                m_end(end),
                m_empty(false) {
                if (!m_end) {
                    inc();
                }
            }

            cube_iterator& operator++() {
                assert(!m_end);
                if (m_empty) {
                    m_end = true;
                }
                else {
                    inc();
                }
                return *this;
            }
            cube_iterator operator++(int) { assert(false); return *this; }
            expr_vector const * operator->() const { return &(operator*()); }
            expr_vector const& operator*() const noexcept { return m_cube; }

            bool operator==(cube_iterator const& other) noexcept {
                return other.m_end == m_end;
            };
            bool operator!=(cube_iterator const& other) noexcept {
                return other.m_end != m_end;
            };

        };

        class cube_generator {
            solver&      m_solver;
            unsigned     m_cutoff;
            expr_vector  m_default_vars;
            expr_vector& m_vars;
        public:
            cube_generator(solver& s):
                m_solver(s),
                m_cutoff(0xFFFFFFFF),
                m_default_vars(s.ctx()),
                m_vars(m_default_vars)
            {}

            cube_generator(solver& s, expr_vector& vars):
                m_solver(s),
                m_cutoff(0xFFFFFFFF),
                m_default_vars(s.ctx()),
                m_vars(vars)
            {}

            cube_iterator begin() { return cube_iterator(m_solver, m_vars, m_cutoff, false); }
            cube_iterator end() { return cube_iterator(m_solver, m_vars, m_cutoff, true); }
            void set_cutoff(unsigned c) noexcept { m_cutoff = c; }
        };

        cube_generator cubes() { return cube_generator(*this); }
        cube_generator cubes(expr_vector& vars) { return cube_generator(*this, vars); }

    };
    inline std::ostream & operator<<(std::ostream & out, solver const & s) { out << Z3_solver_to_string(s.ctx(), s); return out; }

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
            object::operator=(s);
            m_goal = s.m_goal;
            return *this;
        }
        void add(expr const & f) { check_context(*this, f); Z3_goal_assert(ctx(), m_goal, f); check_error(); }
        void add(expr_vector const& v) { check_context(*this, v); for (unsigned i = 0; i < v.size(); ++i) add(v[i]); }
        unsigned size() const { return Z3_goal_size(ctx(), m_goal); }
        expr operator[](int i) const { assert(0 <= i); Z3_ast r = Z3_goal_formula(ctx(), m_goal, i); check_error(); return expr(ctx(), r); }
        Z3_goal_prec precision() const { return Z3_goal_precision(ctx(), m_goal); }
        bool inconsistent() const { return Z3_goal_inconsistent(ctx(), m_goal); }
        unsigned depth() const { return Z3_goal_depth(ctx(), m_goal); }
        void reset() { Z3_goal_reset(ctx(), m_goal); }
        unsigned num_exprs() const { return Z3_goal_num_exprs(ctx(), m_goal); }
        bool is_decided_sat() const { return Z3_goal_is_decided_sat(ctx(), m_goal); }
        bool is_decided_unsat() const { return Z3_goal_is_decided_unsat(ctx(), m_goal); }
        model convert_model(model const & m) const {
            check_context(*this, m);
            Z3_model new_m = Z3_goal_convert_model(ctx(), m_goal, m);
            check_error();
            return model(ctx(), new_m);
        }
        model get_model() const {
            Z3_model new_m = Z3_goal_convert_model(ctx(), m_goal, 0);
            check_error();
            return model(ctx(), new_m);
        }
        expr as_expr() const {
            unsigned n = size();
            if (n == 0)
                return ctx().bool_val(true);
            else if (n == 1)
                return operator[](0);
            else {
                array<Z3_ast> args(n);
                for (unsigned i = 0; i < n; i++)
                    args[i] = operator[](i);
                return expr(ctx(), Z3_mk_and(ctx(), n, args.ptr()));
            }
        }
        std::string dimacs(bool include_names = true) const { return std::string(Z3_goal_to_dimacs_string(ctx(), m_goal, include_names)); }
        friend std::ostream & operator<<(std::ostream & out, goal const & g);
    };
    inline std::ostream & operator<<(std::ostream & out, goal const & g) { out << Z3_goal_to_string(g.ctx(), g); return out; }

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
            object::operator=(s);
            m_apply_result = s.m_apply_result;
            return *this;
        }
        unsigned size() const { return Z3_apply_result_get_num_subgoals(ctx(), m_apply_result); }
        goal operator[](int i) const { assert(0 <= i); Z3_goal r = Z3_apply_result_get_subgoal(ctx(), m_apply_result, i); check_error(); return goal(ctx(), r); }
        friend std::ostream & operator<<(std::ostream & out, apply_result const & r);
    };
    inline std::ostream & operator<<(std::ostream & out, apply_result const & r) { out << Z3_apply_result_to_string(r.ctx(), r); return out; }

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
            object::operator=(s);
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
        friend tactic operator&(tactic const & t1, tactic const & t2);
        friend tactic operator|(tactic const & t1, tactic const & t2);
        friend tactic repeat(tactic const & t, unsigned max);
        friend tactic with(tactic const & t, params const & p);
        friend tactic try_for(tactic const & t, unsigned ms);
        friend tactic par_or(unsigned n, tactic const* tactics);
        friend tactic par_and_then(tactic const& t1, tactic const& t2);
        param_descrs get_param_descrs() { return param_descrs(ctx(), Z3_tactic_get_param_descrs(ctx(), m_tactic)); }
    };

    inline tactic operator&(tactic const & t1, tactic const & t2) {
        check_context(t1, t2);
        Z3_tactic r = Z3_tactic_and_then(t1.ctx(), t1, t2);
        t1.check_error();
        return tactic(t1.ctx(), r);
    }

    inline tactic operator|(tactic const & t1, tactic const & t2) {
        check_context(t1, t2);
        Z3_tactic r = Z3_tactic_or_else(t1.ctx(), t1, t2);
        t1.check_error();
        return tactic(t1.ctx(), r);
    }

    inline tactic repeat(tactic const & t, unsigned max=UINT_MAX) {
        Z3_tactic r = Z3_tactic_repeat(t.ctx(), t, max);
        t.check_error();
        return tactic(t.ctx(), r);
    }

    inline tactic with(tactic const & t, params const & p) {
        Z3_tactic r = Z3_tactic_using_params(t.ctx(), t, p);
        t.check_error();
        return tactic(t.ctx(), r);
    }
    inline tactic try_for(tactic const & t, unsigned ms) {
        Z3_tactic r = Z3_tactic_try_for(t.ctx(), t, ms);
        t.check_error();
        return tactic(t.ctx(), r);
    }
    inline tactic par_or(unsigned n, tactic const* tactics) {
        if (n == 0) {
            Z3_THROW(exception("a non-zero number of tactics need to be passed to par_or"));
        }
        array<Z3_tactic> buffer(n);
        for (unsigned i = 0; i < n; ++i) buffer[i] = tactics[i];
        return tactic(tactics[0].ctx(), Z3_tactic_par_or(tactics[0].ctx(), n, buffer.ptr()));
    }

    inline tactic par_and_then(tactic const & t1, tactic const & t2) {
        check_context(t1, t2);
        Z3_tactic r = Z3_tactic_par_and_then(t1.ctx(), t1, t2);
        t1.check_error();
        return tactic(t1.ctx(), r);
    }

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
            object::operator=(s);
            m_probe = s.m_probe;
            return *this;
        }
        double apply(goal const & g) const { double r = Z3_probe_apply(ctx(), m_probe, g); check_error(); return r; }
        double operator()(goal const & g) const { return apply(g); }
        friend probe operator<=(probe const & p1, probe const & p2);
        friend probe operator<=(probe const & p1, double p2);
        friend probe operator<=(double p1, probe const & p2);
        friend probe operator>=(probe const & p1, probe const & p2);
        friend probe operator>=(probe const & p1, double p2);
        friend probe operator>=(double p1, probe const & p2);
        friend probe operator<(probe const & p1, probe const & p2);
        friend probe operator<(probe const & p1, double p2);
        friend probe operator<(double p1, probe const & p2);
        friend probe operator>(probe const & p1, probe const & p2);
        friend probe operator>(probe const & p1, double p2);
        friend probe operator>(double p1, probe const & p2);
        friend probe operator==(probe const & p1, probe const & p2);
        friend probe operator==(probe const & p1, double p2);
        friend probe operator==(double p1, probe const & p2);
        friend probe operator&&(probe const & p1, probe const & p2);
        friend probe operator||(probe const & p1, probe const & p2);
        friend probe operator!(probe const & p);
    };

    inline probe operator<=(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_le(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator<=(probe const & p1, double p2) { return p1 <= probe(p1.ctx(), p2); }
    inline probe operator<=(double p1, probe const & p2) { return probe(p2.ctx(), p1) <= p2; }
    inline probe operator>=(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_ge(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator>=(probe const & p1, double p2) { return p1 >= probe(p1.ctx(), p2); }
    inline probe operator>=(double p1, probe const & p2) { return probe(p2.ctx(), p1) >= p2; }
    inline probe operator<(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_lt(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator<(probe const & p1, double p2) { return p1 < probe(p1.ctx(), p2); }
    inline probe operator<(double p1, probe const & p2) { return probe(p2.ctx(), p1) < p2; }
    inline probe operator>(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_gt(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator>(probe const & p1, double p2) { return p1 > probe(p1.ctx(), p2); }
    inline probe operator>(double p1, probe const & p2) { return probe(p2.ctx(), p1) > p2; }
    inline probe operator==(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_eq(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator==(probe const & p1, double p2) { return p1 == probe(p1.ctx(), p2); }
    inline probe operator==(double p1, probe const & p2) { return probe(p2.ctx(), p1) == p2; }
    inline probe operator&&(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_and(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator||(probe const & p1, probe const & p2) {
        check_context(p1, p2); Z3_probe r = Z3_probe_or(p1.ctx(), p1, p2); p1.check_error(); return probe(p1.ctx(), r);
    }
    inline probe operator!(probe const & p) {
        Z3_probe r = Z3_probe_not(p.ctx(), p); p.check_error(); return probe(p.ctx(), r);
    }

    class optimize : public object {
        Z3_optimize m_opt;

    public:
        class handle final {
            unsigned m_h;
        public:
            handle(unsigned h): m_h(h) {}
            unsigned h() const { return m_h; }
        };
        optimize(context& c):object(c) { m_opt = Z3_mk_optimize(c); Z3_optimize_inc_ref(c, m_opt); }
        optimize(optimize const & o):object(o), m_opt(o.m_opt) {
            Z3_optimize_inc_ref(o.ctx(), o.m_opt);
        }
        optimize(context& c, optimize& src):object(c) {
            m_opt = Z3_mk_optimize(c); 
            Z3_optimize_inc_ref(c, m_opt);
            add(expr_vector(c, src.assertions()));
            expr_vector v(c, src.objectives());
            for (expr_vector::iterator it = v.begin(); it != v.end(); ++it) minimize(*it);
        }
        optimize& operator=(optimize const& o) {
            Z3_optimize_inc_ref(o.ctx(), o.m_opt);
            Z3_optimize_dec_ref(ctx(), m_opt);
            m_opt = o.m_opt;
            object::operator=(o);
            return *this;
        }
        ~optimize() { Z3_optimize_dec_ref(ctx(), m_opt); }
        operator Z3_optimize() const { return m_opt; }
        void add(expr const& e) {
            assert(e.is_bool());
            Z3_optimize_assert(ctx(), m_opt, e);
        }
        void add(expr_vector const& es) {
            for (expr_vector::iterator it = es.begin(); it != es.end(); ++it) add(*it);
        }
        void add(expr const& e, expr const& t) {
            assert(e.is_bool());
            Z3_optimize_assert_and_track(ctx(), m_opt, e, t);
        }
        void add(expr const& e, char const* p) {
            assert(e.is_bool());
            add(e, ctx().bool_const(p));
        }
        handle add_soft(expr const& e, unsigned weight) {
            assert(e.is_bool());
            auto str = std::to_string(weight);
            return handle(Z3_optimize_assert_soft(ctx(), m_opt, e, str.c_str(), 0));
        }
        handle add_soft(expr const& e, char const* weight) {
            assert(e.is_bool());
            return handle(Z3_optimize_assert_soft(ctx(), m_opt, e, weight, 0));
        }
        handle add(expr const& e, unsigned weight) {
            return add_soft(e, weight);
        }
        handle maximize(expr const& e) {
            return handle(Z3_optimize_maximize(ctx(), m_opt, e));
        }
        handle minimize(expr const& e) {
            return handle(Z3_optimize_minimize(ctx(), m_opt, e));
        }
        void push() {
            Z3_optimize_push(ctx(), m_opt);
        }
        void pop() {
            Z3_optimize_pop(ctx(), m_opt);
        }
        check_result check() { Z3_lbool r = Z3_optimize_check(ctx(), m_opt, 0, 0); check_error(); return to_check_result(r); }
        check_result check(expr_vector const& asms) {
            unsigned n = asms.size();
            array<Z3_ast> _asms(n);
            for (unsigned i = 0; i < n; i++) {
                check_context(*this, asms[i]);
                _asms[i] = asms[i];
            }
            Z3_lbool r = Z3_optimize_check(ctx(), m_opt, n, _asms.ptr());
            check_error();
            return to_check_result(r);
        }
        model get_model() const { Z3_model m = Z3_optimize_get_model(ctx(), m_opt); check_error(); return model(ctx(), m); }
        expr_vector unsat_core() const { Z3_ast_vector r = Z3_optimize_get_unsat_core(ctx(), m_opt); check_error(); return expr_vector(ctx(), r); }
        void set(params const & p) { Z3_optimize_set_params(ctx(), m_opt, p); check_error(); }
        expr lower(handle const& h) {
            Z3_ast r = Z3_optimize_get_lower(ctx(), m_opt, h.h());
            check_error();
            return expr(ctx(), r);
        }
        expr upper(handle const& h) {
            Z3_ast r = Z3_optimize_get_upper(ctx(), m_opt, h.h());
            check_error();
            return expr(ctx(), r);
        }
        expr_vector assertions() const { Z3_ast_vector r = Z3_optimize_get_assertions(ctx(), m_opt); check_error(); return expr_vector(ctx(), r); }
        expr_vector objectives() const { Z3_ast_vector r = Z3_optimize_get_objectives(ctx(), m_opt); check_error(); return expr_vector(ctx(), r); }
        stats statistics() const { Z3_stats r = Z3_optimize_get_statistics(ctx(), m_opt); check_error(); return stats(ctx(), r); }
        friend std::ostream & operator<<(std::ostream & out, optimize const & s);
        void from_file(char const* filename) { Z3_optimize_from_file(ctx(), m_opt, filename); check_error(); }
        void from_string(char const* constraints) { Z3_optimize_from_string(ctx(), m_opt, constraints); check_error(); }
        std::string help() const { char const * r = Z3_optimize_get_help(ctx(), m_opt); check_error();  return r; }
    };
    inline std::ostream & operator<<(std::ostream & out, optimize const & s) { out << Z3_optimize_to_string(s.ctx(), s.m_opt); return out; }

    class fixedpoint : public object {
        Z3_fixedpoint m_fp;
    public:
        fixedpoint(context& c):object(c) { m_fp = Z3_mk_fixedpoint(c); Z3_fixedpoint_inc_ref(c, m_fp); }
        fixedpoint(fixedpoint const & o):object(o), m_fp(o.m_fp) { Z3_fixedpoint_inc_ref(ctx(), m_fp); }
        ~fixedpoint() { Z3_fixedpoint_dec_ref(ctx(), m_fp); }
        fixedpoint & operator=(fixedpoint const & o) {
            Z3_fixedpoint_inc_ref(o.ctx(), o.m_fp);
            Z3_fixedpoint_dec_ref(ctx(), m_fp);
            m_fp = o.m_fp;
            object::operator=(o);
            return *this;
        }
        operator Z3_fixedpoint() const { return m_fp; }
        expr_vector from_string(char const* s) { 
            Z3_ast_vector r = Z3_fixedpoint_from_string(ctx(), m_fp, s); 
            check_error(); 
            return expr_vector(ctx(), r);
        }
        expr_vector from_file(char const* s) { 
            Z3_ast_vector r = Z3_fixedpoint_from_file(ctx(), m_fp, s); 
            check_error(); 
            return expr_vector(ctx(), r);
        }
        void add_rule(expr& rule, symbol const& name) { Z3_fixedpoint_add_rule(ctx(), m_fp, rule, name); check_error(); }
        void add_fact(func_decl& f, unsigned * args) { Z3_fixedpoint_add_fact(ctx(), m_fp, f, f.arity(), args); check_error(); }
        check_result query(expr& q) { Z3_lbool r = Z3_fixedpoint_query(ctx(), m_fp, q); check_error(); return to_check_result(r); }
        check_result query(func_decl_vector& relations) {
            array<Z3_func_decl> rs(relations);
            Z3_lbool r = Z3_fixedpoint_query_relations(ctx(), m_fp, rs.size(), rs.ptr());
            check_error();
            return to_check_result(r);
        }
        expr get_answer() { Z3_ast r = Z3_fixedpoint_get_answer(ctx(), m_fp); check_error(); return expr(ctx(), r); }
        std::string reason_unknown() { return Z3_fixedpoint_get_reason_unknown(ctx(), m_fp); }
        void update_rule(expr& rule, symbol const& name) { Z3_fixedpoint_update_rule(ctx(), m_fp, rule, name); check_error(); }
        unsigned get_num_levels(func_decl& p) { unsigned r = Z3_fixedpoint_get_num_levels(ctx(), m_fp, p); check_error(); return r; }
        expr get_cover_delta(int level, func_decl& p) {
            Z3_ast r = Z3_fixedpoint_get_cover_delta(ctx(), m_fp, level, p);
            check_error();
            return expr(ctx(), r);
        }
        void add_cover(int level, func_decl& p, expr& property) { Z3_fixedpoint_add_cover(ctx(), m_fp, level, p, property); check_error();  }
        stats statistics() const { Z3_stats r = Z3_fixedpoint_get_statistics(ctx(), m_fp); check_error(); return stats(ctx(), r); }
        void register_relation(func_decl& p) { Z3_fixedpoint_register_relation(ctx(), m_fp, p); }
        expr_vector assertions() const { Z3_ast_vector r = Z3_fixedpoint_get_assertions(ctx(), m_fp); check_error(); return expr_vector(ctx(), r); }
        expr_vector rules() const { Z3_ast_vector r = Z3_fixedpoint_get_rules(ctx(), m_fp); check_error(); return expr_vector(ctx(), r); }
        void set(params const & p) { Z3_fixedpoint_set_params(ctx(), m_fp, p); check_error(); }
        std::string help() const { return Z3_fixedpoint_get_help(ctx(), m_fp); }
        param_descrs get_param_descrs() { return param_descrs(ctx(), Z3_fixedpoint_get_param_descrs(ctx(), m_fp)); }
        std::string to_string() { return Z3_fixedpoint_to_string(ctx(), m_fp, 0, 0); }
        std::string to_string(expr_vector const& queries) {
            array<Z3_ast> qs(queries);
            return Z3_fixedpoint_to_string(ctx(), m_fp, qs.size(), qs.ptr());
        }
    };
    inline std::ostream & operator<<(std::ostream & out, fixedpoint const & f) { return out << Z3_fixedpoint_to_string(f.ctx(), f, 0, 0); }

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
    inline sort context::string_sort() { Z3_sort s = Z3_mk_string_sort(m_ctx); check_error(); return sort(*this, s); }
    inline sort context::char_sort() { Z3_sort s = Z3_mk_char_sort(m_ctx); check_error(); return sort(*this, s); }
    inline sort context::seq_sort(sort& s) { Z3_sort r = Z3_mk_seq_sort(m_ctx, s); check_error(); return sort(*this, r); }
    inline sort context::re_sort(sort& s) { Z3_sort r = Z3_mk_re_sort(m_ctx, s); check_error(); return sort(*this, r); }
    inline sort context::fpa_sort(unsigned ebits, unsigned sbits) { Z3_sort s = Z3_mk_fpa_sort(m_ctx, ebits, sbits); check_error(); return sort(*this, s); }

    template<>
    inline sort context::fpa_sort<16>() { return fpa_sort(5, 11); }

    template<>
    inline sort context::fpa_sort<32>() { return fpa_sort(8, 24); }

    template<>
    inline sort context::fpa_sort<64>() { return fpa_sort(11, 53); }

    template<>
    inline sort context::fpa_sort<128>() { return fpa_sort(15, 113); }

    inline sort context::fpa_rounding_mode_sort() { Z3_sort r = Z3_mk_fpa_rounding_mode_sort(m_ctx); check_error(); return sort(*this, r); }

    inline sort context::array_sort(sort d, sort r) { Z3_sort s = Z3_mk_array_sort(m_ctx, d, r); check_error(); return sort(*this, s); }
    inline sort context::array_sort(sort_vector const& d, sort r) {
        array<Z3_sort> dom(d);
        Z3_sort s = Z3_mk_array_sort_n(m_ctx, dom.size(), dom.ptr(), r); check_error(); return sort(*this, s);
    }
    inline sort context::enumeration_sort(char const * name, unsigned n, char const * const * enum_names, func_decl_vector & cs, func_decl_vector & ts) {
        array<Z3_symbol> _enum_names(n);
        for (unsigned i = 0; i < n; i++) { _enum_names[i] = Z3_mk_string_symbol(*this, enum_names[i]); }
        array<Z3_func_decl> _cs(n);
        array<Z3_func_decl> _ts(n);
        Z3_symbol _name = Z3_mk_string_symbol(*this, name);
        sort s = to_sort(*this, Z3_mk_enumeration_sort(*this, _name, n, _enum_names.ptr(), _cs.ptr(), _ts.ptr()));
        check_error();
        for (unsigned i = 0; i < n; i++) { cs.push_back(func_decl(*this, _cs[i])); ts.push_back(func_decl(*this, _ts[i])); }
        return s;
    }
    inline func_decl context::tuple_sort(char const * name, unsigned n, char const * const * names, sort const* sorts, func_decl_vector & projs) {
        array<Z3_symbol> _names(n);
        array<Z3_sort> _sorts(n);
        for (unsigned i = 0; i < n; i++) { _names[i] = Z3_mk_string_symbol(*this, names[i]); _sorts[i] = sorts[i]; }
        array<Z3_func_decl> _projs(n);
        Z3_symbol _name = Z3_mk_string_symbol(*this, name);
        Z3_func_decl tuple;
        sort _ignore_s = to_sort(*this, Z3_mk_tuple_sort(*this, _name, n, _names.ptr(), _sorts.ptr(), &tuple, _projs.ptr()));
        check_error();
        for (unsigned i = 0; i < n; i++) { projs.push_back(func_decl(*this, _projs[i])); }
        return func_decl(*this, tuple);
    }

    inline sort context::uninterpreted_sort(char const* name) {
        Z3_symbol _name = Z3_mk_string_symbol(*this, name);
        return to_sort(*this, Z3_mk_uninterpreted_sort(*this, _name));
    }
    inline sort context::uninterpreted_sort(symbol const& name) {
        return to_sort(*this, Z3_mk_uninterpreted_sort(*this, name));
    }

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

    inline func_decl context::function(symbol const& name, sort_vector const& domain, sort const& range) {
        array<Z3_sort> args(domain.size());
        for (unsigned i = 0; i < domain.size(); i++) {
            check_context(domain[i], range);
            args[i] = domain[i];
        }
        Z3_func_decl f = Z3_mk_func_decl(m_ctx, name, domain.size(), args.ptr(), range);
        check_error();
        return func_decl(*this, f);
    }

    inline func_decl context::function(char const * name, sort_vector const& domain, sort const& range) {
        return function(range.ctx().str_symbol(name), domain, range);
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

    inline func_decl context::recfun(symbol const & name, unsigned arity, sort const * domain, sort const & range) {
        array<Z3_sort> args(arity);
        for (unsigned i = 0; i < arity; i++) {
            check_context(domain[i], range);
            args[i] = domain[i];
        }
        Z3_func_decl f = Z3_mk_rec_func_decl(m_ctx, name, arity, args.ptr(), range);
        check_error();
        return func_decl(*this, f);

    }

    inline func_decl context::recfun(char const * name, unsigned arity, sort const * domain, sort const & range) {
        return recfun(str_symbol(name), arity, domain, range);
    }

    inline func_decl context::recfun(char const * name, sort const& d1, sort const & range) {
        return recfun(str_symbol(name), 1, &d1, range);
    }

    inline func_decl context::recfun(char const * name, sort const& d1, sort const& d2, sort const & range) {
        sort dom[2] = { d1, d2 };
        return recfun(str_symbol(name), 2, dom, range);
    }

    inline void context::recdef(func_decl f, expr_vector const& args, expr const& body) {
        check_context(f, args); check_context(f, body);
        array<Z3_ast> vars(args);
        Z3_add_rec_def(f.ctx(), f, vars.size(), vars.ptr(), body);
    }

    inline func_decl context::user_propagate_function(symbol const& name, sort_vector const& domain, sort const& range) {
        check_context(domain, range);
        array<Z3_sort> domain1(domain);
        Z3_func_decl f = Z3_solver_propagate_declare(range.ctx(), name, domain1.size(), domain1.ptr(), range);
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
    inline expr context::string_const(char const * name) { return constant(name, string_sort()); }
    inline expr context::bv_const(char const * name, unsigned sz) { return constant(name, bv_sort(sz)); }
    inline expr context::fpa_const(char const * name, unsigned ebits, unsigned sbits) { return constant(name, fpa_sort(ebits, sbits)); }

    template<size_t precision>
    inline expr context::fpa_const(char const * name) { return constant(name, fpa_sort<precision>()); }

    inline void context::set_rounding_mode(rounding_mode rm) { m_rounding_mode = rm; }

    inline expr context::fpa_rounding_mode() {
        switch (m_rounding_mode) {
        case RNA: return expr(*this, Z3_mk_fpa_rna(m_ctx));
        case RNE: return expr(*this, Z3_mk_fpa_rne(m_ctx));
        case RTP: return expr(*this, Z3_mk_fpa_rtp(m_ctx));
        case RTN: return expr(*this, Z3_mk_fpa_rtn(m_ctx));
        case RTZ: return expr(*this, Z3_mk_fpa_rtz(m_ctx));
        default: return expr(*this);
        }
    }

    inline expr context::bool_val(bool b) { return b ? expr(*this, Z3_mk_true(m_ctx)) : expr(*this, Z3_mk_false(m_ctx)); }

    inline expr context::int_val(int n) { Z3_ast r = Z3_mk_int(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(unsigned n) { Z3_ast r = Z3_mk_unsigned_int(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(int64_t n) { Z3_ast r = Z3_mk_int64(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(uint64_t n) { Z3_ast r = Z3_mk_unsigned_int64(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }
    inline expr context::int_val(char const * n) { Z3_ast r = Z3_mk_numeral(m_ctx, n, int_sort()); check_error(); return expr(*this, r); }

    inline expr context::real_val(int n, int d) { Z3_ast r = Z3_mk_real(m_ctx, n, d); check_error(); return expr(*this, r); }
    inline expr context::real_val(int n) { Z3_ast r = Z3_mk_int(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(unsigned n) { Z3_ast r = Z3_mk_unsigned_int(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(int64_t n) { Z3_ast r = Z3_mk_int64(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(uint64_t n) { Z3_ast r = Z3_mk_unsigned_int64(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }
    inline expr context::real_val(char const * n) { Z3_ast r = Z3_mk_numeral(m_ctx, n, real_sort()); check_error(); return expr(*this, r); }

    inline expr context::bv_val(int n, unsigned sz) { sort s = bv_sort(sz); Z3_ast r = Z3_mk_int(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::bv_val(unsigned n, unsigned sz) { sort s = bv_sort(sz); Z3_ast r = Z3_mk_unsigned_int(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::bv_val(int64_t n, unsigned sz) { sort s = bv_sort(sz); Z3_ast r = Z3_mk_int64(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::bv_val(uint64_t n, unsigned sz) { sort s = bv_sort(sz); Z3_ast r = Z3_mk_unsigned_int64(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::bv_val(char const * n, unsigned sz) { sort s = bv_sort(sz); Z3_ast r = Z3_mk_numeral(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::bv_val(unsigned n, bool const* bits) {
        array<bool> _bits(n);
        for (unsigned i = 0; i < n; ++i) _bits[i] = bits[i] ? 1 : 0;
        Z3_ast r = Z3_mk_bv_numeral(m_ctx, n, _bits.ptr()); check_error(); return expr(*this, r);
    }

    inline expr context::fpa_val(double n) { sort s = fpa_sort<64>(); Z3_ast r = Z3_mk_fpa_numeral_double(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::fpa_val(float n) { sort s = fpa_sort<32>(); Z3_ast r = Z3_mk_fpa_numeral_float(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::fpa_nan(sort const & s) { Z3_ast r = Z3_mk_fpa_nan(m_ctx, s); check_error(); return expr(*this, r); }
    inline expr context::fpa_inf(sort const & s, bool sgn) { Z3_ast r = Z3_mk_fpa_inf(m_ctx, s, sgn); check_error(); return expr(*this, r); }

    inline expr context::string_val(char const* s, unsigned n) { Z3_ast r = Z3_mk_lstring(m_ctx, n, s); check_error(); return expr(*this, r); }
    inline expr context::string_val(char const* s) { Z3_ast r = Z3_mk_string(m_ctx, s); check_error(); return expr(*this, r); }
    inline expr context::string_val(std::string const& s) { Z3_ast r = Z3_mk_string(m_ctx, s.c_str()); check_error(); return expr(*this, r); }
    inline expr context::string_val(std::u32string const& s) { Z3_ast r = Z3_mk_u32string(m_ctx, (unsigned)s.size(), (unsigned const*)s.c_str()); check_error(); return expr(*this, r); }

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
    inline expr func_decl::operator()(expr_vector const& args) const {
        array<Z3_ast> _args(args.size());
        for (unsigned i = 0; i < args.size(); i++) {
            check_context(*this, args[i]);
            _args[i] = args[i];
        }
        Z3_ast r = Z3_mk_app(ctx(), *this, args.size(), _args.ptr());
        check_error();
        return expr(ctx(), r);
    }
    inline expr func_decl::operator()() const {
        Z3_ast r = Z3_mk_app(ctx(), *this, 0, 0);
        ctx().check_error();
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
    inline func_decl function(char const* name, sort_vector const& domain, sort const& range) {
        return range.ctx().function(name, domain, range);
    }
    inline func_decl function(std::string const& name, sort_vector const& domain, sort const& range) {
        return range.ctx().function(name.c_str(), domain, range);
    }

    inline func_decl recfun(symbol const & name, unsigned arity, sort const * domain, sort const & range) {
        return range.ctx().recfun(name, arity, domain, range);
    }
    inline func_decl recfun(char const * name, unsigned arity, sort const * domain, sort const & range) {
        return range.ctx().recfun(name, arity, domain, range);
    }
    inline func_decl recfun(char const * name, sort const& d1, sort const & range) {
        return range.ctx().recfun(name, d1, range);
    }
    inline func_decl recfun(char const * name, sort const& d1, sort const& d2, sort const & range) {
        return range.ctx().recfun(name, d1, d2, range);
    }

    inline expr select(expr const & a, expr const & i) {
        check_context(a, i);
        Z3_ast r = Z3_mk_select(a.ctx(), a, i);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr select(expr const & a, int i) {
        return select(a, a.ctx().num_val(i, a.get_sort().array_domain()));
    }
    inline expr select(expr const & a, expr_vector const & i) {
        check_context(a, i);
        array<Z3_ast> idxs(i);
        Z3_ast r = Z3_mk_select_n(a.ctx(), a, idxs.size(), idxs.ptr());
        a.check_error();
        return expr(a.ctx(), r);
    }

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
    inline expr store(expr const & a, expr_vector const & i, expr const & v) {
        check_context(a, i); check_context(a, v);
        array<Z3_ast> idxs(i);
        Z3_ast r = Z3_mk_store_n(a.ctx(), a, idxs.size(), idxs.ptr(), v);
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr as_array(func_decl & f) {
        Z3_ast r = Z3_mk_as_array(f.ctx(), f);
        f.check_error();
        return expr(f.ctx(), r);
    }

#define MK_EXPR1(_fn, _arg)                     \
    Z3_ast r = _fn(_arg.ctx(), _arg);           \
    _arg.check_error();                         \
    return expr(_arg.ctx(), r);

#define MK_EXPR2(_fn, _arg1, _arg2)             \
    check_context(_arg1, _arg2);                \
    Z3_ast r = _fn(_arg1.ctx(), _arg1, _arg2);  \
    _arg1.check_error();                        \
    return expr(_arg1.ctx(), r);

    inline expr const_array(sort const & d, expr const & v) {
        MK_EXPR2(Z3_mk_const_array, d, v);
    }

    inline expr empty_set(sort const& s) {
        MK_EXPR1(Z3_mk_empty_set, s);
    }

    inline expr full_set(sort const& s) {
        MK_EXPR1(Z3_mk_full_set, s);
    }

    inline expr set_add(expr const& s, expr const& e) {
        MK_EXPR2(Z3_mk_set_add, s, e);
    }

    inline expr set_del(expr const& s, expr const& e) {
        MK_EXPR2(Z3_mk_set_del, s, e);
    }

    inline expr set_union(expr const& a, expr const& b) {
        check_context(a, b);
        Z3_ast es[2] = { a, b };
        Z3_ast r = Z3_mk_set_union(a.ctx(), 2, es);
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr set_intersect(expr const& a, expr const& b) {
        check_context(a, b);
        Z3_ast es[2] = { a, b };
        Z3_ast r = Z3_mk_set_intersect(a.ctx(), 2, es);
        a.check_error();
        return expr(a.ctx(), r);
    }

    inline expr set_difference(expr const& a, expr const& b) {
        MK_EXPR2(Z3_mk_set_difference, a, b);
    }

    inline expr set_complement(expr const& a) {
        MK_EXPR1(Z3_mk_set_complement, a);
    }

    inline expr set_member(expr const& s, expr const& e) {
        MK_EXPR2(Z3_mk_set_member, s, e);
    }

    inline expr set_subset(expr const& a, expr const& b) {
        MK_EXPR2(Z3_mk_set_subset, a, b);
    }

    // sequence and regular expression operations.
    // union is +
    // concat is overloaded to handle sequences and regular expressions

    inline expr empty(sort const& s) {
        Z3_ast r = Z3_mk_seq_empty(s.ctx(), s);
        s.check_error();
        return expr(s.ctx(), r);
    }
    inline expr suffixof(expr const& a, expr const& b) {
        check_context(a, b);
        Z3_ast r = Z3_mk_seq_suffix(a.ctx(), a, b);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr prefixof(expr const& a, expr const& b) {
        check_context(a, b);
        Z3_ast r = Z3_mk_seq_prefix(a.ctx(), a, b);
        a.check_error();
        return expr(a.ctx(), r);
    }
    inline expr indexof(expr const& s, expr const& substr, expr const& offset) {
        check_context(s, substr); check_context(s, offset);
        Z3_ast r = Z3_mk_seq_index(s.ctx(), s, substr, offset);
        s.check_error();
        return expr(s.ctx(), r);
    }
    inline expr last_indexof(expr const& s, expr const& substr) {
        check_context(s, substr); 
        Z3_ast r = Z3_mk_seq_last_index(s.ctx(), s, substr);
        s.check_error();
        return expr(s.ctx(), r);
    }
    inline expr to_re(expr const& s) {
        MK_EXPR1(Z3_mk_seq_to_re, s);
    }
    inline expr in_re(expr const& s, expr const& re) {
        MK_EXPR2(Z3_mk_seq_in_re, s, re);
    }
    inline expr plus(expr const& re) {
        MK_EXPR1(Z3_mk_re_plus, re);
    }
    inline expr option(expr const& re) {
        MK_EXPR1(Z3_mk_re_option, re);
    }
    inline expr star(expr const& re) {
        MK_EXPR1(Z3_mk_re_star, re);
    }
    inline expr re_empty(sort const& s) {
        Z3_ast r = Z3_mk_re_empty(s.ctx(), s);
        s.check_error();
        return expr(s.ctx(), r);
    }
    inline expr re_full(sort const& s) {
        Z3_ast r = Z3_mk_re_full(s.ctx(), s);
        s.check_error();
        return expr(s.ctx(), r);
    }
    inline expr re_intersect(expr_vector const& args) {
        assert(args.size() > 0);
        context& ctx = args[0].ctx();
        array<Z3_ast> _args(args);
        Z3_ast r = Z3_mk_re_intersect(ctx, _args.size(), _args.ptr());
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr re_diff(expr const& a, expr const& b) {
        check_context(a, b);
        context& ctx = a.ctx();
        Z3_ast r = Z3_mk_re_diff(ctx, a, b);
        ctx.check_error();
        return expr(ctx, r);
    }
    inline expr re_complement(expr const& a) {
        MK_EXPR1(Z3_mk_re_complement, a);
    }
    inline expr range(expr const& lo, expr const& hi) {
        check_context(lo, hi);
        Z3_ast r = Z3_mk_re_range(lo.ctx(), lo, hi);
        lo.check_error();
        return expr(lo.ctx(), r);
    }





    inline expr_vector context::parse_string(char const* s) {
        Z3_ast_vector r = Z3_parse_smtlib2_string(*this, s, 0, 0, 0, 0, 0, 0);
        check_error();
        return expr_vector(*this, r);

    }
    inline expr_vector context::parse_file(char const* s) {
        Z3_ast_vector r = Z3_parse_smtlib2_file(*this, s, 0, 0, 0, 0, 0, 0);
        check_error();
        return expr_vector(*this, r);
    }

    inline expr_vector context::parse_string(char const* s, sort_vector const& sorts, func_decl_vector const& decls) {
        array<Z3_symbol> sort_names(sorts.size());
        array<Z3_symbol> decl_names(decls.size());
        array<Z3_sort>   sorts1(sorts);
        array<Z3_func_decl> decls1(decls);
        for (unsigned i = 0; i < sorts.size(); ++i) {
            sort_names[i] = sorts[i].name();
        }
        for (unsigned i = 0; i < decls.size(); ++i) {
            decl_names[i] = decls[i].name();
        }

        Z3_ast_vector r = Z3_parse_smtlib2_string(*this, s, sorts.size(), sort_names.ptr(), sorts1.ptr(), decls.size(), decl_names.ptr(), decls1.ptr());
        check_error();
        return expr_vector(*this, r);
    }

    inline expr_vector context::parse_file(char const* s, sort_vector const& sorts, func_decl_vector const& decls) {
        array<Z3_symbol> sort_names(sorts.size());
        array<Z3_symbol> decl_names(decls.size());
        array<Z3_sort>   sorts1(sorts);
        array<Z3_func_decl> decls1(decls);
        for (unsigned i = 0; i < sorts.size(); ++i) {
            sort_names[i] = sorts[i].name();
        }
        for (unsigned i = 0; i < decls.size(); ++i) {
            decl_names[i] = decls[i].name();
        }
        Z3_ast_vector r = Z3_parse_smtlib2_file(*this, s, sorts.size(), sort_names.ptr(), sorts1.ptr(), decls.size(), decl_names.ptr(), decls1.ptr());
        check_error();
        return expr_vector(*this, r);
    }


    inline expr expr::substitute(expr_vector const& src, expr_vector const& dst) {
        assert(src.size() == dst.size());
        array<Z3_ast> _src(src.size());
        array<Z3_ast> _dst(dst.size());
        for (unsigned i = 0; i < src.size(); ++i) {
            _src[i] = src[i];
            _dst[i] = dst[i];
        }
        Z3_ast r = Z3_substitute(ctx(), m_ast, src.size(), _src.ptr(), _dst.ptr());
        check_error();
        return expr(ctx(), r);
    }

    inline expr expr::substitute(expr_vector const& dst) {
        array<Z3_ast> _dst(dst.size());
        for (unsigned i = 0; i < dst.size(); ++i) {
            _dst[i] = dst[i];
        }
        Z3_ast r = Z3_substitute_vars(ctx(), m_ast, dst.size(), _dst.ptr());
        check_error();
        return expr(ctx(), r);
    }


    class user_propagator_base {

        typedef std::function<void(unsigned, expr const&)> fixed_eh_t;
        typedef std::function<void(void)> final_eh_t;
        typedef std::function<void(unsigned, unsigned)> eq_eh_t;
        typedef std::function<void(unsigned, expr const&)> created_eh_t;

        final_eh_t m_final_eh;
        eq_eh_t    m_eq_eh;
        fixed_eh_t m_fixed_eh;
        created_eh_t m_created_eh;
        solver*    s;
        Z3_context c;
        Z3_solver_callback cb { nullptr };

        Z3_context ctx() {
            return c ? c : (Z3_context)s->ctx();
        }

        struct scoped_cb {
            user_propagator_base& p;
            scoped_cb(void* _p, Z3_solver_callback cb):p(*static_cast<user_propagator_base*>(_p)) {
                p.cb = cb;
            }
            ~scoped_cb() { 
                p.cb = nullptr; 
            }
        };

        static void push_eh(void* p) {
            static_cast<user_propagator_base*>(p)->push();
        }

        static void pop_eh(void* p, unsigned num_scopes) {
            static_cast<user_propagator_base*>(p)->pop(num_scopes);
        }

        static void* fresh_eh(void* p, Z3_context ctx) {
            return static_cast<user_propagator_base*>(p)->fresh(ctx);
        }

        static void fixed_eh(void* _p, Z3_solver_callback cb, unsigned id, Z3_ast _value) {
            user_propagator_base* p = static_cast<user_propagator_base*>(_p);
            scoped_cb _cb(p, cb);
            scoped_context ctx(p->ctx());
            expr value(ctx(), _value);
            static_cast<user_propagator_base*>(p)->m_fixed_eh(id, value);
        }

        static void eq_eh(void* p, Z3_solver_callback cb, unsigned x, unsigned y) {
            scoped_cb _cb(p, cb);
            static_cast<user_propagator_base*>(p)->m_eq_eh(x, y);
        }

        static void final_eh(void* p, Z3_solver_callback cb) {
            scoped_cb _cb(p, cb);
            static_cast<user_propagator_base*>(p)->m_final_eh(); 
        }

        static void created_eh(void* _p, Z3_solver_callback cb, Z3_ast _e, unsigned id) {
            user_propagator_base* p = static_cast<user_propagator_base*>(_p);
            scoped_cb _cb(p, cb);
            scoped_context ctx(p->ctx());
            expr e(ctx(), _e);
            static_cast<user_propagator_base*>(p)->m_created_eh(id, e);
        }


    public:
        user_propagator_base(Z3_context c) : s(nullptr), c(c) {}
        
        user_propagator_base(solver* s): s(s), c(nullptr) {
              Z3_solver_propagate_init(ctx(), *s, this, push_eh, pop_eh, fresh_eh);
        }

        virtual void push() = 0;
        virtual void pop(unsigned num_scopes) = 0;

        virtual ~user_propagator_base() = default;

        /**
           \brief user_propagators created using \c fresh() are created during 
           search and their lifetimes are restricted to search time. They should
           be garbage collected by the propagator used to invoke \c fresh().
           The life-time of the Z3_context object can only be assumed valid during
           callbacks, such as \c fixed(), which contains expressions based on the
           context.
        */
        virtual user_propagator_base* fresh(Z3_context ctx) = 0;

        /**
           \brief register callbacks.
           Callbacks can only be registered with user_propagators
           that were created using a solver. 
        */

        void register_fixed(fixed_eh_t& f) { 
            assert(s);
            m_fixed_eh = f; 
            Z3_solver_propagate_fixed(ctx(), *s, fixed_eh); 
        }

        void register_fixed() {
            assert(s);
            m_fixed_eh = [this](unsigned id, expr const& e) {
                fixed(id, e);
            };
            Z3_solver_propagate_fixed(ctx(), *s, fixed_eh);
        }

        void register_eq(eq_eh_t& f) { 
            assert(s);
            m_eq_eh = f; 
            Z3_solver_propagate_eq(ctx(), *s, eq_eh); 
        }

        void register_eq() {
            assert(s);
            m_eq_eh = [this](unsigned x, unsigned y) {
                eq(x, y);
            };
            Z3_solver_propagate_eq(ctx(), *s, eq_eh);
        }

        /**
           \brief register a callback on final-check.
           During the final check stage, all propagations have been processed.
           This is an opportunity for the user-propagator to delay some analysis
           that could be expensive to perform incrementally. It is also an opportunity
           for the propagator to implement branch and bound optimization. 
        */

        void register_final(final_eh_t& f) { 
            assert(s);
            m_final_eh = f; 
            Z3_solver_propagate_final(ctx(), *s, final_eh); 
        }
        
        void register_final() { 
            assert(s);
            m_final_eh = [this]() {
                final();
            };
            Z3_solver_propagate_final(ctx(), *s, final_eh); 
        }

        void register_created(created_eh_t& c) {
            assert(s);
            m_created_eh = c;
            Z3_solver_propagate_created(ctx(), *s, created_eh);
        }

        void register_created() {
            m_created_eh = [this](unsigned id, expr const& e) {
                created(id, e);
            };
            Z3_solver_propagate_created(ctx(), *s, created_eh);
        }

        virtual void fixed(unsigned /*id*/, expr const& /*e*/) { }

        virtual void eq(unsigned /*x*/, unsigned /*y*/) { }

        virtual void final() { }

        virtual void created(unsigned /*id*/, expr const& /*e*/) {}

        /**
           \brief tracks \c e by a unique identifier that is returned by the call.

           If the \c fixed() callback is registered and if \c e is a Boolean or Bit-vector, 
           the \c fixed() callback gets invoked when \c e is bound to a value.
           If the \c eq() callback is registered, then equalities between registered expressions
           are reported. 
           A consumer can use the \c propagate or \c conflict functions to invoke propagations
           or conflicts as a consequence of these callbacks. These functions take a list of identifiers
           for registered expressions that have been fixed. The list of identifiers must correspond to
           already fixed values. Similarly, a list of propagated equalities can be supplied. These must
           correspond to equalities that have been registered during a callback.
         */

        unsigned add(expr const& e) {
            if (cb)
                return Z3_solver_propagate_register_cb(ctx(), cb, e);
            if (s)
                return Z3_solver_propagate_register(ctx(), *s, e);
            assert(false);
            return 0;
        }

        void conflict(unsigned num_fixed, unsigned const* fixed) {
            assert(cb);
            scoped_context _ctx(ctx());
            expr conseq = _ctx().bool_val(false);
            Z3_solver_propagate_consequence(ctx(), cb, num_fixed, fixed, 0, nullptr, nullptr, conseq);
        }

        void propagate(unsigned num_fixed, unsigned const* fixed, expr const& conseq) {
            assert(cb);
            assert(conseq.ctx() == ctx());
            Z3_solver_propagate_consequence(ctx(), cb, num_fixed, fixed, 0, nullptr, nullptr, conseq);
        }

        void propagate(unsigned num_fixed, unsigned const* fixed, 
                       unsigned num_eqs, unsigned const* lhs, unsigned const * rhs, 
                       expr const& conseq) {
            assert(cb);
            assert(conseq.ctx() == ctx());
            Z3_solver_propagate_consequence(ctx(), cb, num_fixed, fixed, num_eqs, lhs, rhs, conseq);
        }
    };


    

}

/**@}*/
/**@}*/
#undef Z3_THROW

