/*++
  Copyright (c) 2012 Microsoft Corporation

  Module Name:

  duality_wrapper.h

  Abstract:

  wrap various Z3 classes in the style expected by duality

  Author:

  Ken McMillan (kenmcmil)

  Revision History:


  --*/
#ifndef DUALITY_WRAPPER_H_
#define DUALITY_WRAPPER_H_

#include<cassert>
#include<iostream>
#include<string>
#include<sstream>
#include<vector>
#include<list>
#include <set>
#include"version.h"
#include<limits.h>

#include "iz3hash.h"
#include "model.h"
#include "solver.h"

#include"well_sorted.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"array_decl_plugin.h"
#include"ast_translation.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"ast_smt_pp.h"
#include"ast_smt2_pp.h"
#include"th_rewriter.h"
#include"var_subst.h"
#include"expr_substitution.h"
#include"pp.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"
#include"scoped_timer.h"
#include"scoped_proof.h"

namespace Duality {

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
    class literals;

    /**
       Duality global configuration object.
    */

    class config {
        params_ref m_params;
        config & operator=(config const & s);
    public:
    config(config const & s) : m_params(s.m_params) {}
    config(const params_ref &_params) : m_params(_params) {}
        config() { } // TODO: create a new params object here
        ~config() { }
        void set(char const * param, char const * value) { m_params.set_str(param,value); }
        void set(char const * param, bool value) { m_params.set_bool(param,value); }
        void set(char const * param, int value) { m_params.set_uint(param,value); }
        params_ref &get() {return m_params;}
        const params_ref &get() const {return m_params;}
    };

    enum decl_kind {
        True,
        False,
        And,
        Or,
        Not,
        Iff,
        Ite,
        Equal,
        Implies,
        Distinct,
        Xor,
        Oeq,
        Interp,
        Leq,
        Geq,
        Lt,
        Gt,
        Plus,
        Sub,
        Uminus,
        Times,
        Div,
        Idiv,
        Rem,
        Mod,
        Power,
        ToReal,
        ToInt,
        IsInt,
        Select,
        Store,
        ConstArray,
        ArrayDefault,
        ArrayMap,
        SetUnion,
        SetIntersect,
        SetDifference,
        SetComplement,
        SetSubSet,
        AsArray,
        Numeral,
        Forall,
        Exists,
        Variable,
        Uninterpreted,
        OtherBasic,
        OtherArith,
        OtherArray,
        Other
    };

    enum sort_kind {BoolSort,IntSort,RealSort,ArraySort,UninterpretedSort,UnknownSort};

    /**
       A context has an ast manager global configuration options, etc.
    */

    class context {
    protected:
        ast_manager &mgr;
        config m_config;

        family_id                  m_basic_fid;
        family_id                  m_array_fid;
        family_id                  m_arith_fid;
        family_id                  m_bv_fid;
        family_id                  m_dt_fid;
        family_id                  m_datalog_fid;
        arith_util                 m_arith_util;

    public:
    context(ast_manager &_manager, const config &_config) : mgr(_manager), m_config(_config), m_arith_util(_manager) {
            m_basic_fid = m().get_basic_family_id();
            m_arith_fid = m().mk_family_id("arith");
            m_bv_fid    = m().mk_family_id("bv");
            m_array_fid = m().mk_family_id("array");
            m_dt_fid    = m().mk_family_id("datatype");
            m_datalog_fid = m().mk_family_id("datalog_relation");
        }
        ~context() { }
      
        ast_manager &m() const {return *(ast_manager *)&mgr;}

        void set(char const * param, char const * value) { m_config.set(param,value); }
        void set(char const * param, bool value) { m_config.set(param,value); }
        void set(char const * param, int value) { m_config.set(param,value); }
        config &get_config() {return m_config;}

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
        func_decl fresh_func_decl(char const * name, const std::vector<sort> &domain, sort const & range);
        func_decl fresh_func_decl(char const * name, sort const & range);

        expr constant(symbol const & name, sort const & s);
        expr constant(char const * name, sort const & s);
        expr constant(const std::string &name, sort const & s);
        expr bool_const(char const * name);
        expr int_const(char const * name);
        expr real_const(char const * name);
        expr bv_const(char const * name, unsigned sz);
      
        expr bool_val(bool b);
      
        expr int_val(int n);
        expr int_val(unsigned n);
        expr int_val(char const * n);
      
        expr real_val(int n, int d);
        expr real_val(int n);
        expr real_val(unsigned n);
        expr real_val(char const * n);
      
        expr bv_val(int n, unsigned sz);
        expr bv_val(unsigned n, unsigned sz);
        expr bv_val(char const * n, unsigned sz);
      
        expr num_val(int n, sort const & s);

        expr mki(family_id fid, ::decl_kind dk, int n, ::expr **args);
        expr make(decl_kind op, int n, ::expr **args);
        expr make(decl_kind op, const std::vector<expr> &args);
        expr make(decl_kind op);
        expr make(decl_kind op, const expr &arg0);
        expr make(decl_kind op, const expr &arg0, const expr &arg1);
        expr make(decl_kind op, const expr &arg0, const expr &arg1, const expr &arg2);

        expr make_quant(decl_kind op, const std::vector<expr> &bvs, const expr &body);
        expr make_quant(decl_kind op, const std::vector<sort> &_sorts, const std::vector<symbol> &_names, const expr &body);
        expr make_var(int idx, const sort &s);

        decl_kind get_decl_kind(const func_decl &t);

        sort_kind get_sort_kind(const sort &s);

        expr translate(const expr &e);
        func_decl translate(const func_decl &);

        void print_expr(std::ostream &s, const ast &e);

        fixedpoint mk_fixedpoint();

        expr cook(::expr *a);
        std::vector<expr> cook(ptr_vector< ::expr> v);
        ::expr *uncook(const expr &a);
    };

    template<typename T>
        class z3array {
        T *      m_array;
        unsigned m_size;
        z3array(z3array const & s);
        z3array & operator=(z3array const & s);
    public:
    z3array(unsigned sz):m_size(sz) { m_array = new T[sz]; }
        ~z3array() { delete[] m_array; }
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
    object(): m_ctx((context *)0) {}
    object(context & c):m_ctx(&c) {}
    object(object const & s):m_ctx(s.m_ctx) {}
        context & ctx() const { return *m_ctx; }
        friend void check_context(object const & a, object const & b) { assert(a.m_ctx == b.m_ctx); }
	ast_manager &m() const {return m_ctx->m();}
    };

    class symbol : public object {
        ::symbol m_sym;
    public:
    symbol(context & c, ::symbol s):object(c), m_sym(s) {}
    symbol(symbol const & s):object(s), m_sym(s.m_sym) {}
        symbol & operator=(symbol const & s) { m_ctx = s.m_ctx; m_sym = s.m_sym; return *this; }
	operator ::symbol() const {return m_sym;} 
	std::string str() const {
            if (m_sym.is_numerical()) {
                std::ostringstream buffer;
                buffer << m_sym.get_num();
                return buffer.str();
            }
            else {
                return m_sym.bare_str();
            }
	}
        friend std::ostream & operator<<(std::ostream & out, symbol const & s){
            return out << s.str();
	}
	friend bool operator==(const symbol &x, const symbol &y){
            return x.m_sym == y.m_sym;
	}
    };

    class params : public config {};

    /** Wrapper around an ast pointer */
    class ast_i : public object {
    protected:
        ::ast *_ast;
    public:
        ::ast * const &raw() const {return _ast;}
    ast_i(context & c, ::ast *a = 0) : object(c) {_ast = a;}
      
        ast_i(){_ast = 0;}
        bool eq(const ast_i &other) const {
            return _ast == other._ast;
        }
        bool lt(const ast_i &other) const {
            return _ast < other._ast;
        }
        friend bool operator==(const ast_i &x, const ast_i&y){
            return x.eq(y);
        }
        friend bool operator!=(const ast_i &x, const ast_i&y){
            return !x.eq(y);
        }
        friend bool operator<(const ast_i &x, const ast_i&y){
            return x.lt(y);
        }
        size_t hash() const {return (size_t)_ast;}
        bool null() const {return !_ast;}
    };

    /** Reference counting verison of above */
    class ast : public ast_i {
    public:
        operator ::ast*() const { return raw(); }
        friend bool eq(ast const & a, ast const & b) { return a.raw() == b.raw(); }

      
    ast(context &c, ::ast *a = 0) : ast_i(c,a) {
            if(_ast)
                m().inc_ref(a);
        }
      
        ast() {}
      
    ast(const ast &other) : ast_i(other) {
            if(_ast)
                m().inc_ref(_ast);
        }
      
        ast &operator=(const ast &other) {
            if(_ast)
                m().dec_ref(_ast);
            _ast = other._ast;
            m_ctx = other.m_ctx;
            if(_ast)
                m().inc_ref(_ast);
            return *this;
        }
      
        ~ast(){
            if(_ast)
                m().dec_ref(_ast);
        }

        void show() const;

    };

    class sort : public ast {
    public:
    sort(context & c):ast(c) {}
    sort(context & c, ::sort *s):ast(c, s) {}
    sort(sort const & s):ast(s) {}
        operator ::sort*() const { return to_sort(raw()); }
        sort & operator=(sort const & s) { return static_cast<sort&>(ast::operator=(s)); }

        bool is_bool() const { return m().is_bool(*this); }
        bool is_int() const { return ctx().get_sort_kind(*this) == IntSort; } 
        bool is_real() const { return ctx().get_sort_kind(*this) == RealSort; } 
        bool is_arith() const;
        bool is_array() const { return ctx().get_sort_kind(*this) == ArraySort; } 
        bool is_datatype() const; 
        bool is_relation() const; 
        bool is_finite_domain() const; 

      
        sort array_domain() const;
        sort array_range() const;

        friend std::ostream & operator<<(std::ostream & out, sort const & m){
            m.ctx().print_expr(out,m);
            return out;
        }
    };

    
    class func_decl : public ast {
    public:
    func_decl() : ast() {}
    func_decl(context & c):ast(c) {}
    func_decl(context & c, ::func_decl *n):ast(c, n) {}
    func_decl(func_decl const & s):ast(s) {}
        operator ::func_decl*() const { return to_func_decl(*this); }
        func_decl & operator=(func_decl const & s) { return static_cast<func_decl&>(ast::operator=(s)); }
        
        unsigned arity() const;
        sort domain(unsigned i) const;
        sort range() const;
        symbol name() const {return symbol(ctx(),to_func_decl(raw())->get_name());}
        decl_kind get_decl_kind() const;

        bool is_const() const { return arity() == 0; }

        expr operator()(unsigned n, expr const * args) const;
        expr operator()(const std::vector<expr> &args) const;
        expr operator()() const;
        expr operator()(expr const & a) const;
        expr operator()(int a) const;
        expr operator()(expr const & a1, expr const & a2) const;
        expr operator()(expr const & a1, int a2) const;
        expr operator()(int a1, expr const & a2) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
        expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;

	func_decl get_func_decl_parameter(unsigned idx){
            return func_decl(ctx(),to_func_decl(to_func_decl(raw())->get_parameters()[idx].get_ast()));
	}

    };

    class expr : public ast {
    public:
    expr() : ast() {}
    expr(context & c):ast(c) {}
    expr(context & c, ::ast *n):ast(c, n) {}
    expr(expr const & n):ast(n) {}
        expr & operator=(expr const & n) { return static_cast<expr&>(ast::operator=(n)); }
	operator ::expr*() const { return to_expr(raw()); }
	unsigned get_id() const {return to_expr(raw())->get_id();}

        sort get_sort() const { return sort(ctx(),m().get_sort(to_expr(raw()))); }

        bool is_bool() const { return get_sort().is_bool(); }
        bool is_int() const { return get_sort().is_int(); }
        bool is_real() const { return get_sort().is_real(); }
        bool is_arith() const { return get_sort().is_arith(); }
        bool is_array() const { return get_sort().is_array(); }
        bool is_datatype() const { return get_sort().is_datatype(); }
        bool is_relation() const { return get_sort().is_relation(); }
        bool is_finite_domain() const { return get_sort().is_finite_domain(); }
	bool is_true() const {return is_app() && decl().get_decl_kind() == True; }

        bool is_numeral() const {
            return is_app() && decl().get_decl_kind() == OtherArith && m().is_unique_value(to_expr(raw()));
	}
	bool is_app() const {return raw()->get_kind() == AST_APP;}
        bool is_quantifier() const {return raw()->get_kind() == AST_QUANTIFIER;}
        bool is_var() const {return raw()->get_kind() == AST_VAR;}
	bool is_label (bool &pos,std::vector<symbol> &names) const ;
	bool is_ground() const {return to_app(raw())->is_ground();}
	bool has_quantifiers() const {return to_app(raw())->has_quantifiers();}
	bool has_free(int idx) const {
            used_vars proc;
            proc.process(to_expr(raw()));
            return proc.contains(idx);
	}
	unsigned get_max_var_idx_plus_1() const {
            used_vars proc;
            proc.process(to_expr(raw()));
            return proc.get_max_found_var_idx_plus_1();
	}

        // operator Z3_app() const { assert(is_app()); return reinterpret_cast<Z3_app>(m_ast); }
        func_decl decl() const {return func_decl(ctx(),to_app(raw())->get_decl());}
        unsigned num_args() const {
            ast_kind dk = raw()->get_kind();
            switch(dk){
            case AST_APP:
                return to_app(raw())->get_num_args();
            case AST_QUANTIFIER:
                return 1;
            case AST_VAR:
                return 0;
            default:;    
            }
            SASSERT(0);
            return 0;
	}
        expr arg(unsigned i) const {
            ast_kind dk = raw()->get_kind();
            switch(dk){
            case AST_APP:
                return ctx().cook(to_app(raw())->get_arg(i));
            case AST_QUANTIFIER:
                return ctx().cook(to_quantifier(raw())->get_expr());
            default:;
            }
            assert(0);
            return expr();
	}

        expr body() const {
            return ctx().cook(to_quantifier(raw())->get_expr());
	}

        friend expr operator!(expr const & a) {
            // ::expr *e = a;
            return expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_NOT,a));
	}

        friend expr operator&&(expr const & a, expr const & b) {
            return expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_AND,a,b));
	}

        friend expr operator||(expr const & a, expr const & b) {
            return expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_OR,a,b));
        }
        
        friend expr implies(expr const & a, expr const & b) {
            return expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_IMPLIES,a,b));
        }

        friend expr operator==(expr const & a, expr const & b) {
            return expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_EQ,a,b));
        }

        friend expr operator!=(expr const & a, expr const & b) {
            return expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_DISTINCT,a,b));
        }

        friend expr operator+(expr const & a, expr const & b) {
            return a.ctx().make(Plus,a,b); // expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_ADD,a,b));
        }

        friend expr operator*(expr const & a, expr const & b) {
            return a.ctx().make(Times,a,b); // expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_MUL,a,b));
	}

        friend expr operator/(expr const & a, expr const & b) {
            return a.ctx().make(Div,a,b); //  expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_DIV,a,b));
        }
	
        friend expr operator-(expr const & a) {
            return a.ctx().make(Uminus,a); // expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_UMINUS,a));
        }

        friend expr operator-(expr const & a, expr const & b) {
            return a.ctx().make(Sub,a,b); // expr(a.ctx(),a.m().mk_app(a.ctx().m_arith_fid,OP_SUB,a,b));
        }

        friend expr operator<=(expr const & a, expr const & b) {
            return a.ctx().make(Leq,a,b); // expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_LE,a,b));
	}

        friend expr operator>=(expr const & a, expr const & b) {
            return a.ctx().make(Geq,a,b); //expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_GE,a,b));
        }
	
        friend expr operator<(expr const & a, expr const & b) {
            return a.ctx().make(Lt,a,b); expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_LT,a,b));
        }
        
        friend expr operator>(expr const & a, expr const & b) {
            return a.ctx().make(Gt,a,b); expr(a.ctx(),a.m().mk_app(a.m().get_basic_family_id(),OP_GT,a,b));
	}

        expr simplify() const;

        expr simplify(params const & p) const;
	
        expr qe_lite() const;

	expr qe_lite(const std::set<int> &idxs, bool index_of_bound) const;

	friend expr clone_quantifier(const expr &, const expr &);

        friend expr clone_quantifier(const expr &q, const expr &b, const std::vector<expr> &patterns);

	friend expr clone_quantifier(decl_kind, const expr &, const expr &);

        friend std::ostream & operator<<(std::ostream & out, expr const & m){
            m.ctx().print_expr(out,m);
            return out;
	}

	void get_patterns(std::vector<expr> &pats) const ;

	unsigned get_quantifier_num_bound() const {
            return to_quantifier(raw())->get_num_decls();
	}

	unsigned get_index_value() const {
            var* va = to_var(raw());
            return va->get_idx();
	}

        bool is_quantifier_forall() const {
            return to_quantifier(raw())->is_forall();
	}

	sort get_quantifier_bound_sort(unsigned n) const {
            return sort(ctx(),to_quantifier(raw())->get_decl_sort(n));
	}

	symbol get_quantifier_bound_name(unsigned n) const {
            return symbol(ctx(),to_quantifier(raw())->get_decl_names()[n]);
	}

	friend expr forall(const std::vector<expr> &quants, const expr &body);

	friend expr exists(const std::vector<expr> &quants, const expr &body);

    };
    

    typedef ::decl_kind pfrule;
    
    class proof : public ast {
    public:
    proof(context & c):ast(c) {}
    proof(context & c, ::proof *s):ast(c, s) {}
    proof(proof const & s):ast(s) {}
        operator ::proof*() const { return to_app(raw()); }
        proof & operator=(proof const & s) { return static_cast<proof&>(ast::operator=(s)); }

        pfrule rule() const {
            ::func_decl *d = to_app(raw())->get_decl();
            return d->get_decl_kind();
        }

        unsigned num_prems() const {
            return to_app(raw())->get_num_args() - 1;
        }
      
        expr conc() const {
            return ctx().cook(to_app(raw())->get_arg(num_prems()));
        }
      
        proof prem(unsigned i) const {
            return proof(ctx(),to_app(to_app(raw())->get_arg(i)));
        }
      
        void get_assumptions(std::vector<expr> &assumps);
    };

#if 0

#if Z3_MAJOR_VERSION > 4 || Z3_MAJOR_VERSION == 4 && Z3_MINOR_VERSION >= 3
    template<typename T>
        class ast_vector_tpl : public object {
        Z3_ast_vector m_vector;
        void init(Z3_ast_vector v) { Z3_ast_vector_inc_ref(ctx(), v); m_vector = v; }
    public:
    ast_vector_tpl(context & c):object(c) { init(Z3_mk_ast_vector(c)); }
    ast_vector_tpl(context & c, Z3_ast_vector v):object(c) { init(v); }
    ast_vector_tpl(ast_vector_tpl const & s):object(s), m_vector(s.m_vector) { Z3_ast_vector_inc_ref(ctx(), m_vector); }
        ~ast_vector_tpl() { /* Z3_ast_vector_dec_ref(ctx(), m_vector); */ }
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
            // Z3_ast_vector_dec_ref(ctx(), m_vector);
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

#endif

#endif

    class func_interp : public object {
        ::func_interp * m_interp;
        void init(::func_interp * e) {
            m_interp = e;
        }
    public:
    func_interp(context & c, ::func_interp * e):object(c) { init(e); }
    func_interp(func_interp const & s):object(s) { init(s.m_interp); }
        ~func_interp() { }
        operator ::func_interp *() const { return m_interp; }
        func_interp & operator=(func_interp const & s) {
            m_ctx = s.m_ctx; 
            m_interp = s.m_interp;
            return *this; 
        }
        unsigned num_entries() const { return m_interp->num_entries(); }
        expr get_arg(unsigned ent, unsigned arg) const {
            return expr(ctx(),m_interp->get_entry(ent)->get_arg(arg));
        }
        expr get_value(unsigned ent) const {
            return expr(ctx(),m_interp->get_entry(ent)->get_result());
        }
        expr else_value() const {
            return expr(ctx(),m_interp->get_else());
        }
    };



    class model : public object {
        model_ref m_model;
        void init(::model *m) {
            m_model = m;
        }
    public:
    model(context & c, ::model * m = 0):object(c), m_model(m) { }
    model(model const & s):object(s), m_model(s.m_model) { }
	~model() { }
        operator ::model *() const { return m_model.get(); }
        model & operator=(model const & s) {
            // ::model *_inc_ref(s.ctx(), s.m_model);
            // ::model *_dec_ref(ctx(), m_model);
            m_ctx = s.m_ctx; 
            m_model = s.m_model.get();
            return *this; 
        }
        model & operator=(::model *s) {
  	    m_model = s;
            return *this; 
        }
	bool null() const {return !m_model;}
        
        expr eval(expr const & n, bool model_completion=true) const {
            ::model * _m = m_model.get();
            expr_ref result(ctx().m());
            _m->eval(n, result, model_completion);
            return expr(ctx(), result);
        }
        
        void show() const;
	void show_hash() const;

        unsigned num_consts() const {return m_model.get()->get_num_constants();}
        unsigned num_funcs() const {return m_model.get()->get_num_functions();}
        func_decl get_const_decl(unsigned i) const {return func_decl(ctx(),m_model.get()->get_constant(i));}
        func_decl get_func_decl(unsigned i) const {return func_decl(ctx(),m_model.get()->get_function(i));}
        unsigned size() const;
        func_decl operator[](unsigned i) const;

        expr get_const_interp(func_decl f) const {
            return ctx().cook(m_model->get_const_interp(to_func_decl(f.raw())));
	}

        func_interp get_func_interp(func_decl f) const {
            return func_interp(ctx(),m_model->get_func_interp(to_func_decl(f.raw())));
	} 

#if 0
        friend std::ostream & operator<<(std::ostream & out, model const & m) { out << Z3_model_to_string(m.ctx(), m); return out; }
#endif
    };

#if 0
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
#endif

    enum check_result {
        unsat, sat, unknown
    };

    class fixedpoint : public object {

    public:
        void get_rules(std::vector<expr> &rules);
        void get_assertions(std::vector<expr> &rules);
        void register_relation(const func_decl &rela);
        void add_rule(const expr &clause, const symbol &name);
        void assert_cnst(const expr &cnst);
    };

    inline std::ostream & operator<<(std::ostream & out, check_result r) { 
        if (r == unsat) out << "unsat";
        else if (r == sat) out << "sat";
        else out << "unknown";
        return out;
    }

    inline check_result to_check_result(lbool l) {
        if (l == l_true) return sat;
        else if (l == l_false) return unsat;
        return unknown;
    }

    class solver : public object {
    protected:
        ::solver *m_solver;
        model the_model;
	bool canceled;
	proof_gen_mode m_mode;
	bool extensional;
    public:
        solver(context & c, bool extensional = false, bool models = true);
    solver(context & c, ::solver *s):object(c),the_model(c) { m_solver = s; canceled = false;}
    solver(solver const & s):object(s), the_model(s.the_model) { m_solver = s.m_solver; canceled = false;}
        ~solver() {
            if(m_solver)
                dealloc(m_solver);
	}
	operator ::solver*() const { return m_solver; }
        solver & operator=(solver const & s) {
            m_ctx = s.m_ctx; 
            m_solver = s.m_solver;
	    the_model = s.the_model;
	    m_mode = s.m_mode;
            return *this; 
        }
	struct cancel_exception {};
	void checkpoint(){
            if(canceled)
                throw(cancel_exception());
	}
        // void set(params const & p) { Z3_solver_set_params(ctx(), m_solver, p); check_error(); }
        void push() { scoped_proof_mode spm(m(),m_mode); m_solver->push(); }
        void pop(unsigned n = 1) { scoped_proof_mode spm(m(),m_mode); m_solver->pop(n); }
        // void reset() { Z3_solver_reset(ctx(), m_solver); check_error(); }
        void add(expr const & e) { scoped_proof_mode spm(m(),m_mode); m_solver->assert_expr(e); }
        check_result check() { 
            scoped_proof_mode spm(m(),m_mode); 
            checkpoint();
            lbool r = m_solver->check_sat(0,0);
            model_ref m;
            m_solver->get_model(m);
            the_model = m.get();
            return to_check_result(r);
	}
        check_result check_keep_model(unsigned n, expr * const assumptions, unsigned *core_size = 0, expr *core = 0) { 
            scoped_proof_mode spm(m(),m_mode); 
            model old_model(the_model);
            check_result res = check(n,assumptions,core_size,core);
            if(the_model == 0)
                the_model = old_model;
            return res;
	}
        check_result check(unsigned n, expr * const assumptions, unsigned *core_size = 0, expr *core = 0) {
            scoped_proof_mode spm(m(),m_mode); 
            checkpoint();
            std::vector< ::expr *> _assumptions(n);
            for (unsigned i = 0; i < n; i++) {
                _assumptions[i] = to_expr(assumptions[i]);
            }
            the_model = 0;
            lbool r = m_solver->check_sat(n,&_assumptions[0]);
	  
            if(core_size && core){
                ptr_vector< ::expr> _core;
                m_solver->get_unsat_core(_core);
                *core_size = _core.size();
                for(unsigned i = 0; i < *core_size; i++)
                    core[i] = expr(ctx(),_core[i]);
            }

            model_ref m;
            m_solver->get_model(m);
            the_model = m.get();

            return to_check_result(r); 
        }
#if 0
        check_result check(expr_vector assumptions) { 
            scoped_proof_mode spm(m(),m_mode); 
            unsigned n = assumptions.size();
            z3array<Z3_ast> _assumptions(n);
            for (unsigned i = 0; i < n; i++) {
                check_context(*this, assumptions[i]);
                _assumptions[i] = assumptions[i];
            }
            Z3_lbool r = Z3_check_assumptions(ctx(), m_solver, n, _assumptions.ptr()); 
            check_error(); 
            return to_check_result(r); 
        }
#endif
        model get_model() const { return model(ctx(), the_model); }
        // std::string reason_unknown() const { Z3_string r = Z3_solver_get_reason_unknown(ctx(), m_solver); check_error(); return r; }
        // stats statistics() const { Z3_stats r = Z3_solver_get_statistics(ctx(), m_solver); check_error(); return stats(ctx(), r); }
#if 0
        expr_vector unsat_core() const { Z3_ast_vector r = Z3_solver_get_unsat_core(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
        expr_vector assertions() const { Z3_ast_vector r = Z3_solver_get_assertions(ctx(), m_solver); check_error(); return expr_vector(ctx(), r); }
#endif
        // expr proof() const { Z3_ast r = Z3_solver_proof(ctx(), m_solver); check_error(); return expr(ctx(), r); }
        // friend std::ostream & operator<<(std::ostream & out, solver const & s) { out << Z3_solver_to_string(s.ctx(), s); return out; }
	
	int get_num_decisions(); 

	void cancel(){
            scoped_proof_mode spm(m(),m_mode); 
            canceled = true;
            if(m_solver)
                m_solver->cancel();
	}

	unsigned get_scope_level(){ scoped_proof_mode spm(m(),m_mode); return m_solver->get_scope_level();}

	void show();
	void print(const char *filename);
	void show_assertion_ids();

	proof get_proof(){
            scoped_proof_mode spm(m(),m_mode); 
            return proof(ctx(),m_solver->get_proof());
	}

	bool extensional_array_theory() {return extensional;}
    };

#if 0
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
        unsigned num_exprs() const { Z3_goal_num_exprs(ctx(), m_goal); }
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

#endif

    inline expr context::bool_val(bool b){return b ? make(True) : make(False);}

    inline symbol context::str_symbol(char const * s) { ::symbol r = ::symbol(s); return symbol(*this, r); }
    inline symbol context::int_symbol(int n) { ::symbol r = ::symbol(n); return symbol(*this, r); }

    inline sort context::bool_sort() {
        ::sort *s = m().mk_sort(m_basic_fid, BOOL_SORT); 
        return sort(*this, s);
    }
    inline sort context::int_sort()  {
        ::sort *s = m().mk_sort(m_arith_fid, INT_SORT); 
        return sort(*this, s);
    }
    inline sort context::real_sort()  {
        ::sort *s = m().mk_sort(m_arith_fid, REAL_SORT); 
        return sort(*this, s);
    }
    inline sort context::array_sort(sort d, sort r) {
        parameter params[2]  = { parameter(d), parameter(to_sort(r)) };
        ::sort * s =  m().mk_sort(m_array_fid, ARRAY_SORT, 2, params);
        return sort(*this, s);
    }


    inline func_decl context::function(symbol const & name, unsigned arity, sort const * domain, sort const & range) {
        std::vector< ::sort *> sv(arity);
        for(unsigned i = 0; i < arity; i++)
            sv[i] = domain[i];
        ::func_decl* d = m().mk_func_decl(name,arity,&sv[0],range);
        return func_decl(*this,d);
    }

    inline func_decl context::function(char const * name, unsigned arity, sort const * domain, sort const & range) {
        return function(str_symbol(name), arity, domain, range);
    }
    
    inline func_decl context::function(char const * name, sort const & domain, sort const & range) {
        sort args[1] = { domain };
        return function(name, 1, args, range);
    }

    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & range) {
        sort args[2] = { d1, d2 };
	return function(name, 2, args, range);
    }

    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & range) {
        sort args[3] = { d1, d2, d3 };
        return function(name, 3, args, range);
    }

    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & range) {
        sort args[4] = { d1, d2, d3, d4 };
        return function(name, 4, args, range);
    }
    
    inline func_decl context::function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & d4, sort const & d5, sort const & range) {
        sort args[5] = { d1, d2, d3, d4, d5 };
        return function(name, 5, args, range);
    }


    inline expr context::constant(symbol const & name, sort const & s) {
        ::expr *r = m().mk_const(m().mk_const_decl(name, s));
        return expr(*this, r); 
    }
    inline expr context::constant(char const * name, sort const & s) { return constant(str_symbol(name), s); }
    inline expr context::bool_const(char const * name) { return constant(name, bool_sort()); }
    inline expr context::int_const(char const * name) { return constant(name, int_sort()); }
    inline expr context::real_const(char const * name) { return constant(name, real_sort()); }
    inline expr context::bv_const(char const * name, unsigned sz) { return constant(name, bv_sort(sz)); }

    inline expr func_decl::operator()(const std::vector<expr> &args) const {
        return operator()(args.size(),&args[0]);
    }
    inline expr func_decl::operator()() const {
        return operator()(0,0);
    }
    inline expr func_decl::operator()(expr const & a) const {
        return operator()(1,&a);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2) const {
        expr args[2] = {a1,a2};
        return operator()(2,args);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2, expr const & a3) const {
        expr args[3] = {a1,a2,a3};
        return operator()(3,args);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const {
        expr args[4] = {a1,a2,a3,a4};
        return operator()(4,args);
    }
    inline expr func_decl::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const {
        expr args[5] = {a1,a2,a3,a4,a5};
        return operator()(5,args);
    }
    
    
    inline expr select(expr const & a, expr const & i) { return a.ctx().make(Select,a,i); }
    inline expr store(expr const & a, expr const & i, expr const & v) { return a.ctx().make(Store,a,i,v); }
    
    inline expr forall(const std::vector<expr> &quants, const expr &body){
        return body.ctx().make_quant(Forall,quants,body);
    }

    inline expr exists(const std::vector<expr> &quants, const expr &body){
        return body.ctx().make_quant(Exists,quants,body);
    }

    inline expr context::int_val(int n){
        :: sort *r = m().mk_sort(m_arith_fid, INT_SORT);
        return cook(m_arith_util.mk_numeral(rational(n),r));
    }


    class literals : public object {
    };

    class TermTree {
    public:

        TermTree(expr _term){
            term = _term;
        }

        TermTree(expr _term, const std::vector<TermTree *> &_children){
            term = _term;
            children = _children;
        }

        inline expr getTerm(){return term;}

        inline std::vector<expr> &getTerms(){return terms;}

        inline std::vector<TermTree *> &getChildren(){
            return children;
        }

        inline int number(int from){
            for(unsigned i = 0; i < children.size(); i++)
                from = children[i]->number(from);
            num = from;
            return from + 1;
        }

        inline int getNumber(){
            return num;
        }

        inline void setTerm(expr t){term = t;}
      
        inline void addTerm(expr t){terms.push_back(t);}

        inline void setChildren(const std::vector<TermTree *> & _children){
            children = _children;
        }

        inline void setNumber(int _num){
            num = _num;
        }

        ~TermTree(){
            for(unsigned i = 0; i < children.size(); i++)
                delete children[i];
        }

    private:
        expr term;
        std::vector<expr> terms;
        std::vector<TermTree *> children;
        int num;
    };
    
    typedef context interpolating_context;

    class interpolating_solver : public solver {
    public:
    interpolating_solver(context &ctx, bool models = true)
        : solver(ctx, true, models)
            {
                weak_mode = false;
            }
      
    public:
        lbool interpolate(const std::vector<expr> &assumptions,
                          std::vector<expr> &interpolants,
                          model &_model,
                          literals &lits,
                          bool incremental
                          );
      
        lbool interpolate_tree(TermTree *assumptions,
                               TermTree *&interpolants,
                               model &_model,
                               literals &lits,
                               bool incremental
                               );
      
        bool read_interpolation_problem(const std::string &file_name,
                                        std::vector<expr> &assumptions,
                                        std::vector<expr> &theory,
                                        std::string &error_message
                                        );
      
        void write_interpolation_problem(const std::string &file_name,
                                         const std::vector<expr> &assumptions,
                                         const std::vector<expr> &theory
                                         );
      
        void AssertInterpolationAxiom(const expr &expr);
        void RemoveInterpolationAxiom(const expr &expr);
      
        void SetWeakInterpolants(bool weak);
        void SetPrintToFile(const std::string &file_name);
      
        const std::vector<expr> &GetInterpolationAxioms() {return theory;}
        const char *profile();
      
    private:
        bool weak_mode;
        std::string print_filename;
        std::vector<expr> theory;
    };
    
    
    inline expr context::cook(::expr *a) {return expr(*this,a);}

    inline std::vector<expr> context::cook(ptr_vector< ::expr> v) {
        std::vector<expr> _v(v.size());
        for(unsigned i = 0; i < v.size(); i++)
            _v[i] = cook(v[i]);
        return _v;
    }

    inline ::expr *context::uncook(const expr &a) {
        m().inc_ref(a.raw());
        return to_expr(a.raw());
    }

    inline expr context::translate(const expr &e) {
        ::expr *f = to_expr(e.raw());
        if(&e.ctx().m() != &m()) // same ast manager -> no translation
            throw "ast manager mismatch";
        return cook(f);
    }

    inline func_decl context::translate(const func_decl &e) {
        ::func_decl *f = to_func_decl(e.raw());
        if(&e.ctx().m() != &m()) // same ast manager -> no translation
            throw "ast manager mismatch";
        return func_decl(*this,f);
    }

    typedef double clock_t;
    clock_t current_time();
    inline void output_time(std::ostream &os, clock_t time){os << time;}

    template <class X> class uptr {
    public:
        X *ptr;
        uptr(){ptr = 0;}
        void set(X *_ptr){
            if(ptr) delete ptr;
            ptr = _ptr;
        }
        X *get(){ return ptr;}
        ~uptr(){
            if(ptr) delete ptr;
        }
    };

};

// to make Duality::ast hashable
namespace hash_space {
    template <>
        class hash<Duality::ast> {
    public:
        size_t operator()(const Duality::ast &s) const {
            return s.raw()->get_id();
        }
    };
}


// to make Duality::ast usable in ordered collections
namespace std {
    template <>
        class less<Duality::ast> {
    public:
        bool operator()(const Duality::ast &s, const Duality::ast &t) const {
            // return s.raw() < t.raw();
            return s.raw()->get_id() < t.raw()->get_id();
        }
    };
}

// to make Duality::ast usable in ordered collections
namespace std {
    template <>
        class less<Duality::expr> {
    public:
        bool operator()(const Duality::expr &s, const Duality::expr &t) const {
            // return s.raw() < t.raw();
            return s.raw()->get_id() < t.raw()->get_id();
        }
    };
}

// to make Duality::func_decl hashable
namespace hash_space {
    template <>
        class hash<Duality::func_decl> {
    public:
        size_t operator()(const Duality::func_decl &s) const {
            return s.raw()->get_id();
        }
    };
}


// to make Duality::func_decl usable in ordered collections
namespace std {
    template <>
        class less<Duality::func_decl> {
    public:
        bool operator()(const Duality::func_decl &s, const Duality::func_decl &t) const {
            // return s.raw() < t.raw();
            return s.raw()->get_id() < t.raw()->get_id();
        }
    };
}

#endif
