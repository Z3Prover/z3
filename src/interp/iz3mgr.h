/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3mgr.h

  Abstract:

  A wrapper around an ast manager, providing convenience methods.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifndef IZ3MGR_H
#define IZ3MGR_H


#include <assert.h>
#include <vector>
#include <functional>

#include "iz3hash.h"

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
//#  include"pp_params.hpp"

/* A wrapper around an ast manager, providing convenience methods. */

/** Shorthands for some built-in operators. */



// rename this to keep it accessible, as we use ast for something else
typedef ast raw_ast;

/** Wrapper around an ast pointer */
class ast_i {
 protected:
    raw_ast *_ast;
 public:
    raw_ast * const &raw() const {return _ast;}
    ast_i(raw_ast *a){_ast = a;}
  
    ast_i(){_ast = 0;}
    bool eq(const ast_i &other) const {
        return _ast == other._ast;
    }
    bool lt(const ast_i &other) const {
        return _ast->get_id() < other._ast->get_id();
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
    size_t hash() const {return _ast->get_id();}
    bool null() const {return !_ast;}
};

/** Reference counting verison of above */
class ast_r : public ast_i {
    ast_manager *_m;
 public:
 ast_r(ast_manager *m, raw_ast *a) : ast_i(a) {
        _m = m;
        m->inc_ref(a);
    }
  
    ast_r() {_m = 0;}

 ast_r(const ast_r &other) : ast_i(other) {
        _m = other._m;
        _m->inc_ref(_ast);
    }

    ast_r &operator=(const ast_r &other) {
        if(_ast)
            _m->dec_ref(_ast);
        _ast = other._ast;
        _m = other._m;
        _m->inc_ref(_ast);
        return *this;
    }

    ~ast_r(){
        if(_ast)
            _m->dec_ref(_ast);
    }
  
    ast_manager *mgr() const {return _m;}

};

// to make ast_r hashable
namespace hash_space {
    template <>
        class hash<ast_r> {
    public:
        size_t operator()(const ast_r &s) const {
            return s.raw()->get_id();
        }
    };
}


// to make ast_r usable in ordered collections
namespace std {
    template <>
        class less<ast_r> {
    public:
        bool operator()(const ast_r &s, const ast_r &t) const {
            // return s.raw() < t.raw(); 
            return s.raw()->get_id() < t.raw()->get_id();
        }
    };
}


/** Wrapper around an AST manager, providing convenience methods. */

class iz3mgr  {

 public:
    typedef ast_r ast;
    // typedef decl_kind opr;
    typedef func_decl *symb;
    typedef sort *type;
    typedef ast_r z3pf;
    typedef decl_kind pfrule;

    enum opr {
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
        Other
    };

    opr op(const ast &t);

    unsigned ast_id(const ast &x)
    {
        return to_expr(x.raw())->get_id();
    }

    /** Overloads for constructing ast. */

    ast make_var(const std::string &name, type ty);
    ast make(opr op, const std::vector<ast> &args);
    ast make(opr op);
    ast make(opr op, const ast &arg0);
    ast make(opr op, const ast &arg0, const ast &arg1);
    ast make(opr op, const ast &arg0, const ast &arg1, const ast &arg2);
    ast make(symb sym, const std::vector<ast> &args);
    ast make(symb sym);
    ast make(symb sym, const ast &arg0);
    ast make(symb sym, const ast &arg0, const ast &arg1);
    ast make(symb sym, const ast &arg0, const ast &arg1, const ast &arg2);
    ast make_quant(opr op, const std::vector<ast> &bvs, ast &body);
    ast clone(const ast &t, const std::vector<ast> &args);

    ast_manager &m() {return m_manager;}

    ast cook(raw_ast *a) {return ast(&m_manager,a);}

    std::vector<ast> cook(ptr_vector<raw_ast> v) {
        std::vector<ast> _v(v.size());
        for(unsigned i = 0; i < v.size(); i++)
            _v[i] = cook(v[i]);
        return _v;
    }

    raw_ast *uncook(const ast &a) {
        m_manager.inc_ref(a.raw());
        return a.raw();
    }

    /** Methods for destructing ast. */


    int num_args(ast t){
        ast_kind dk = t.raw()->get_kind();
        switch(dk){
        case AST_APP:
            return to_app(t.raw())->get_num_args();
        case AST_QUANTIFIER:
            return 1;
        case AST_VAR:
            return 0;
        default:;    
        }
        assert(0);
        return 0;
    }

    ast arg(const ast &t, int i){
        ast_kind dk = t.raw()->get_kind();
        switch(dk){
        case AST_APP:
            return cook(to_app(t.raw())->get_arg(i));
        case AST_QUANTIFIER:
            return cook(to_quantifier(t.raw())->get_expr());
        default:;
        }
        assert(0);
        return ast();
    }
  
    void get_args(const ast &t, std::vector<ast> &res){
        res.resize(num_args(t));
        for(unsigned i = 0; i < res.size(); i++)
            res[i] = arg(t,i);
    }

    std::vector<ast> args(const ast &t){
        std::vector<ast> res;
        get_args(t,res);
        return res;
    }

    symb sym(ast t){
        raw_ast *_ast = t.raw();
        return is_app(_ast) ? to_app(_ast)->get_decl() : 0;
    }

    std::string string_of_symbol(symb s){
        symbol _s = s->get_name();
        if (_s.is_numerical()) {
            std::ostringstream buffer;
            buffer << _s.get_num();
            return buffer.str();
        }
        else {
            return _s.bare_str();
        }
    }

    type get_type(ast t){
        return m().get_sort(to_expr(t.raw()));
    }
  
    std::string string_of_numeral(const ast& t){
        rational r;
        expr* e = to_expr(t.raw());
        assert(e);
        if (m_arith_util.is_numeral(e, r))
            return r.to_string();
        assert(0);
        return "NaN";
    }

    bool is_numeral(const ast& t, rational &r){
        expr* e = to_expr(t.raw());
        assert(e);
        return m_arith_util.is_numeral(e, r);
    }

    rational get_coeff(const ast& t){
        rational res;
        if(op(t) == Times && is_numeral(arg(t,0),res))
            return res;
        return rational(1);
    }

    ast get_linear_var(const ast& t){
        rational res;
        if(op(t) == Times && is_numeral(arg(t,0),res))
            return arg(t,1);
        return t;
    }

    int get_quantifier_num_bound(const ast &t) {
        return to_quantifier(t.raw())->get_num_decls();
    }

    std::string get_quantifier_bound_name(const ast &t, unsigned i) {
        return to_quantifier(t.raw())->get_decl_names()[i].bare_str();
    }

    type get_quantifier_bound_type(const ast &t, unsigned i) {
        return to_quantifier(t.raw())->get_decl_sort(i);
    }

    ast get_quantifier_body(const ast &t) {
        return cook(to_quantifier(t.raw())->get_expr());
    }

    unsigned get_variable_index_value(const ast &t) {
        var* va = to_var(t.raw());
        return va->get_idx();
    }

    bool is_bool_type(type t){
        family_id fid = to_sort(t)->get_family_id(); 
        decl_kind k = to_sort(t)->get_decl_kind();
        return fid == m().get_basic_family_id() && k == BOOL_SORT;
    }

    bool is_array_type(type t){
        family_id fid = to_sort(t)->get_family_id(); 
        decl_kind k = to_sort(t)->get_decl_kind();
        return fid == m_array_fid && k == ARRAY_SORT;
    }

    type get_range_type(symb s){
        return to_func_decl(s)->get_range();
    }

    int get_num_parameters(const symb &s){
        return to_func_decl(s)->get_num_parameters();
    }

    ast get_ast_parameter(const symb &s, int idx){
        return cook(to_func_decl(s)->get_parameters()[idx].get_ast());
    }

    enum lemma_theory {ArithTheory,ArrayTheory,UnknownTheory};

    lemma_theory get_theory_lemma_theory(const ast &proof){
        symb s = sym(proof);
        ::symbol p0;
        bool ok = s->get_parameter(0).is_symbol(p0);
        if(!ok) return UnknownTheory;
        std::string foo(p0.bare_str());
        if(foo == "arith")
            return ArithTheory;
        if(foo == "array")
            return ArrayTheory;
        return UnknownTheory;
    }

    enum lemma_kind {FarkasKind,Leq2EqKind,Eq2LeqKind,GCDTestKind,AssignBoundsKind,EqPropagateKind,ArithMysteryKind,UnknownKind};

    lemma_kind get_theory_lemma_kind(const ast &proof){
        symb s = sym(proof);
        if(s->get_num_parameters() < 2) {
            return ArithMysteryKind;  // Bad -- Z3 hasn't told us
        }
        ::symbol p0;
        bool ok = s->get_parameter(1).is_symbol(p0);
        if(!ok) return UnknownKind;
        std::string foo(p0.bare_str());
        if(foo == "farkas")
            return FarkasKind;
        if(foo == "triangle-eq")
            return is_not(arg(conc(proof),0)) ? Eq2LeqKind : Leq2EqKind;
        if(foo == "gcd-test")
            return GCDTestKind;
        if(foo == "assign-bounds")
            return AssignBoundsKind;
        if(foo == "eq-propagate")
            return EqPropagateKind;
        return UnknownKind;
    }

    void get_farkas_coeffs(const ast &proof, std::vector<ast>& coeffs);

    void get_farkas_coeffs(const ast &proof, std::vector<rational>& rats);

    void get_assign_bounds_coeffs(const ast &proof, std::vector<rational>& rats);

    void get_assign_bounds_coeffs(const ast &proof, std::vector<ast>& rats);

    void get_assign_bounds_rule_coeffs(const ast &proof, std::vector<rational>& rats);
  
    void get_assign_bounds_rule_coeffs(const ast &proof, std::vector<ast>& rats);

    bool is_farkas_coefficient_negative(const ast &proof, int n);

    bool is_true(ast t){
        return op(t) == True;
    }
  
    bool is_false(ast t){
        return op(t) == False;
    }

    bool is_iff(ast t){
        return op(t) == Iff;
    }

    bool is_or(ast t){
        return op(t) == Or;
    }

    bool is_not(ast t){
        return op(t) == Not;
    }
  
    /** Simplify an expression using z3 simplifier */

    ast z3_simplify(const ast& e);

    /** Simplify, sorting sums */
    ast z3_really_simplify(const ast &e);


    // Some constructors that simplify things

    ast mk_not(ast x){
        opr o = op(x);
        if(o == True) return make(False);
        if(o == False) return make(True);
        if(o == Not) return arg(x,0);
        return make(Not,x);
    }

    ast mk_and(ast x, ast y){
        opr ox = op(x);
        opr oy = op(y);
        if(ox == True) return y;
        if(oy == True) return x;
        if(ox == False) return x;
        if(oy == False) return y;
        if(x == y) return x;
        return make(And,x,y);
    }

    ast mk_or(ast x, ast y){
        opr ox = op(x);
        opr oy = op(y);
        if(ox == False) return y;
        if(oy == False) return x;
        if(ox == True) return x;
        if(oy == True) return y;
        if(x == y) return x;
        return make(Or,x,y);
    }

    ast mk_implies(ast x, ast y){
        opr ox = op(x);
        opr oy = op(y);
        if(ox == True) return y;
        if(oy == False) return mk_not(x);
        if(ox == False) return mk_true();
        if(oy == True) return y;
        if(x == y) return mk_true();
        return make(Implies,x,y);
    }

    ast mk_or(const std::vector<ast> &x){
        ast res = mk_false();
        for(unsigned i = 0; i < x.size(); i++)
            res = mk_or(res,x[i]);
        return res;
    }

    ast mk_and(const std::vector<ast> &x){
        std::vector<ast> conjs;
        for(unsigned i = 0; i < x.size(); i++){
            const ast &e = x[i];
            opr o = op(e);
            if(o == False)
                return mk_false();
            if(o != True)
                conjs.push_back(e);
        }
        if(conjs.size() == 0)
            return mk_true();
        if(conjs.size() == 1)
            return conjs[0];
        return make(And,conjs);
    }

    ast mk_equal(ast x, ast y){
        if(x == y) return make(True);
        opr ox = op(x);
        opr oy = op(y);
        if(ox == True) return y;
        if(oy == True) return x;
        if(ox == False) return mk_not(y);
        if(oy == False) return mk_not(x);
        if(ox == False && oy == True) return make(False);
        if(oy == False && ox == True) return make(False);
        return make(Equal,x,y);
    }
  
    ast z3_ite(ast x, ast y, ast z){
        opr ox = op(x);
        opr oy = op(y);
        opr oz = op(z);
        if(ox == True) return y;
        if(ox == False) return z;
        if(y == z) return y;
        if(oy == True && oz == False) return x;
        if(oz == True && oy == False) return mk_not(x);
        return make(Ite,x,y,z);
    }

    ast make_int(const std::string &s) {
        sort *r = m().mk_sort(m_arith_fid, INT_SORT);
        return cook(m_arith_util.mk_numeral(rational(s.c_str()),r));
    }

    ast make_int(const rational &s) {
        sort *r = m().mk_sort(m_arith_fid, INT_SORT);
        return cook(m_arith_util.mk_numeral(s,r));
    }

    ast make_real(const std::string &s) {
        sort *r = m().mk_sort(m_arith_fid, REAL_SORT);
        return cook(m_arith_util.mk_numeral(rational(s.c_str()),r));
    }

    ast make_real(const rational &s) {
        sort *r = m().mk_sort(m_arith_fid, REAL_SORT);
        return cook(m_arith_util.mk_numeral(s,r));
    }

    ast mk_false() { return make(False); }

    ast mk_true() { return make(True); }

    ast mk_fresh_constant(char const * prefix, type s){
        return cook(m().mk_fresh_const(prefix, s));
    }

    type bool_type() {
        ::sort *s = m().mk_sort(m_basic_fid, BOOL_SORT); 
        return s;
    }

    type int_type()  {
        ::sort *s = m().mk_sort(m_arith_fid, INT_SORT); 
        return s;
    }

    type real_type()  {
        ::sort *s = m().mk_sort(m_arith_fid, REAL_SORT); 
        return s;
    }

    type array_type(type d, type r) {
        parameter params[2]  = { parameter(d), parameter(to_sort(r)) };
        ::sort * s =  m().mk_sort(m_array_fid, ARRAY_SORT, 2, params);
        return s;
    }

    symb function(const std::string &str_name, unsigned arity, type *domain, type range) {
        ::symbol name = ::symbol(str_name.c_str());
        std::vector< ::sort *> sv(arity);
        for(unsigned i = 0; i < arity; i++)
            sv[i] = domain[i];
        ::func_decl* d = m().mk_func_decl(name,arity,&sv[0],range);
        return d;
    }
  
    void linear_comb(ast &P, const ast &c, const ast &Q, bool round_off = false);

    ast sum_inequalities(const std::vector<ast> &coeffs, const std::vector<ast> &ineqs, bool round_off = false);

    ast simplify_ineq(const ast &ineq){
        ast res = make(op(ineq),arg(ineq,0),z3_simplify(arg(ineq,1)));
        return res;
    }

    void mk_idiv(const ast& t, const rational &d, ast &whole, ast &frac);

    ast mk_idiv(const ast& t, const rational &d);

    ast mk_idiv(const ast& t, const ast &d);
  
    /** methods for destructing proof terms */

    pfrule pr(const z3pf &t);

    int num_prems(const z3pf &t){return to_app(t.raw())->get_num_args()-1;}
  
    z3pf prem(const z3pf &t, int n){return arg(t,n);}

    z3pf conc(const z3pf &t){return arg(t,num_prems(t));}
  

    /* quantifier handling */

    // substitute a term t for unbound occurrences of variable v in e
  
    ast subst(ast var, ast t, ast e);

    // apply a substitution defined by a map
    ast subst(stl_ext::hash_map<ast,ast> &map, ast e);

    // apply a quantifier to a formula, with some optimizations
    // 1) bound variable does not occur -> no quantifier
    // 2) bound variable must be equal to some term -> substitute

    ast apply_quant(opr quantifier, ast var, ast e);


    /** For debugging */
    void show(ast);

    void show_symb(symb s);

    /** Constructor */

    void print_lit(ast lit);

    void print_expr(std::ostream &s, const ast &e);

    void print_clause(std::ostream &s, std::vector<ast> &cls);

    void print_sat_problem(std::ostream &out, const ast &t);

    void show_clause(std::vector<ast> &cls);

    static void pretty_print(std::ostream &f, const std::string &s);

 iz3mgr(ast_manager &_m_manager)
     : m_manager(_m_manager),
        m_arith_util(_m_manager)
        {
            m_basic_fid = m().get_basic_family_id();
            m_arith_fid = m().mk_family_id("arith");
            m_bv_fid    = m().mk_family_id("bv");
            m_array_fid = m().mk_family_id("array");
            m_dt_fid    = m().mk_family_id("datatype");
            m_datalog_fid = m().mk_family_id("datalog_relation");
        }
  
 iz3mgr(const iz3mgr& other)
     : m_manager(other.m_manager),
        m_arith_util(other.m_manager)
            {
                m_basic_fid = m().get_basic_family_id();
                m_arith_fid = m().mk_family_id("arith");
                m_bv_fid    = m().mk_family_id("bv");
                m_array_fid = m().mk_family_id("array");
                m_dt_fid    = m().mk_family_id("datatype");
                m_datalog_fid = m().mk_family_id("datalog_relation");
            }

 protected:
    ast_manager &m_manager;
    int occurs_in(ast var, ast e);

 private:
    ast mki(family_id fid, decl_kind sk, int n, raw_ast **args);
    ast make(opr op, int n, raw_ast **args);
    ast make(symb sym, int n, raw_ast **args);
    int occurs_in1(stl_ext::hash_map<ast,bool> &occurs_in_memo, ast var, ast e);
    bool solve_arith(const ast &v, const ast &x, const ast &y, ast &res);
    ast cont_eq(stl_ext::hash_set<ast> &cont_eq_memo, bool truth, ast v, ast e);
    ast subst(stl_ext::hash_map<ast,ast> &subst_memo, ast var, ast t, ast e);


    family_id                  m_basic_fid;
    family_id                  m_array_fid;
    family_id                  m_arith_fid;
    family_id                  m_bv_fid;
    family_id                  m_dt_fid;
    family_id                  m_datalog_fid;
    arith_util                 m_arith_util;
};

#endif 

