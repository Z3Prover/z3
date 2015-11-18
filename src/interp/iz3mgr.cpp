/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3mgr.cpp

  Abstract:

  A wrapper around an ast manager, providing convenience methods.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/


#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#pragma warning(disable:4805)
#pragma warning(disable:4800)
#endif

#include "iz3mgr.h"

#include <stdio.h>
#include <fstream>
#include <iostream>
#include <ostream>

#include "expr_abstract.h"
#include "params.h"


using namespace stl_ext;


std::ostream &operator <<(std::ostream &s, const iz3mgr::ast &a){
    return s;
}


iz3mgr::ast iz3mgr::make_var(const std::string &name, type ty){ 
    symbol s = symbol(name.c_str());
    return cook(m().mk_const(m().mk_const_decl(s, ty)));
}

iz3mgr::ast iz3mgr::make(opr op, int n, raw_ast **args){
    switch(op) {
    case True:     return mki(m_basic_fid,OP_TRUE,n,args);
    case False:    return mki(m_basic_fid,OP_FALSE,n,args);
    case Equal:    return mki(m_basic_fid,OP_EQ,n,args);
    case Distinct: return mki(m_basic_fid,OP_DISTINCT,n,args);
    case Ite:      return mki(m_basic_fid,OP_ITE,n,args);
    case And:      return mki(m_basic_fid,OP_AND,n,args);
    case Or:       return mki(m_basic_fid,OP_OR,n,args);
    case Iff:      return mki(m_basic_fid,OP_IFF,n,args);
    case Xor:      return mki(m_basic_fid,OP_XOR,n,args);
    case Not:      return mki(m_basic_fid,OP_NOT,n,args);
    case Implies:  return mki(m_basic_fid,OP_IMPLIES,n,args);
    case Oeq:      return mki(m_basic_fid,OP_OEQ,n,args);
    case Interp:   return mki(m_basic_fid,OP_INTERP,n,args);
    case Leq:      return mki(m_arith_fid,OP_LE,n,args);
    case Geq:      return mki(m_arith_fid,OP_GE,n,args);
    case Lt:       return mki(m_arith_fid,OP_LT,n,args);
    case Gt:       return mki(m_arith_fid,OP_GT,n,args);
    case Plus:     return mki(m_arith_fid,OP_ADD,n,args);
    case Sub:      return mki(m_arith_fid,OP_SUB,n,args);
    case Uminus:   return mki(m_arith_fid,OP_UMINUS,n,args);
    case Times:    return mki(m_arith_fid,OP_MUL,n,args);
    case Div:      return mki(m_arith_fid,OP_DIV,n,args);
    case Idiv:     return mki(m_arith_fid,OP_IDIV,n,args);
    case Rem:      return mki(m_arith_fid,OP_REM,n,args);
    case Mod:      return mki(m_arith_fid,OP_MOD,n,args);
    case Power:    return mki(m_arith_fid,OP_POWER,n,args);
    case ToReal:   return mki(m_arith_fid,OP_TO_REAL,n,args);
    case ToInt:    return mki(m_arith_fid,OP_TO_INT,n,args);
    case IsInt:    return mki(m_arith_fid,OP_IS_INT,n,args);
    case Store:    return mki(m_array_fid,OP_STORE,n,args);
    case Select:   return mki(m_array_fid,OP_SELECT,n,args);
    case ConstArray: return mki(m_array_fid,OP_CONST_ARRAY,n,args);
    case ArrayDefault: return mki(m_array_fid,OP_ARRAY_DEFAULT,n,args);
    case ArrayMap: return mki(m_array_fid,OP_ARRAY_MAP,n,args);
    case SetUnion: return mki(m_array_fid,OP_SET_UNION,n,args);
    case SetIntersect: return mki(m_array_fid,OP_SET_INTERSECT,n,args);
    case SetDifference: return mki(m_array_fid,OP_SET_DIFFERENCE,n,args);
    case SetComplement: return mki(m_array_fid,OP_SET_COMPLEMENT,n,args);
    case SetSubSet: return mki(m_array_fid,OP_SET_SUBSET,n,args);
    case AsArray:   return mki(m_array_fid,OP_AS_ARRAY,n,args);
    default:
        assert(0);
        return ast();
    }
}

iz3mgr::ast iz3mgr::mki(family_id fid, decl_kind dk, int n, raw_ast **args){
    return cook(m().mk_app(fid, dk, 0, 0, n, (expr **)args));        
}

iz3mgr::ast iz3mgr::make(opr op, const std::vector<ast> &args){
    static std::vector<raw_ast*> a(10);
    if(a.size() < args.size())
        a.resize(args.size());
    for(unsigned i = 0; i < args.size(); i++)
        a[i] = args[i].raw();
    return make(op,args.size(), args.size() ? &a[0] : 0);
}

iz3mgr::ast iz3mgr::make(opr op){
    return make(op,0,0);
}

iz3mgr::ast iz3mgr::make(opr op, const ast &arg0){
    raw_ast *a = arg0.raw();
    return make(op,1,&a);
}

iz3mgr::ast iz3mgr::make(opr op, const ast &arg0, const ast &arg1){
    raw_ast *args[2];
    args[0] = arg0.raw();
    args[1] = arg1.raw();
    return make(op,2,args);
}

iz3mgr::ast iz3mgr::make(opr op, const ast &arg0, const ast &arg1, const ast &arg2){
    raw_ast *args[3];
    args[0] = arg0.raw();
    args[1] = arg1.raw();
    args[2] = arg2.raw();
    return make(op,3,args);
}

iz3mgr::ast iz3mgr::make(symb sym, int n, raw_ast **args){
    return cook(m().mk_app(sym, n, (expr **) args));   
}

iz3mgr::ast iz3mgr::make(symb sym, const std::vector<ast> &args){
    static std::vector<raw_ast*> a(10);
    if(a.size() < args.size())
        a.resize(args.size());
    for(unsigned i = 0; i < args.size(); i++)
        a[i] = args[i].raw();
    return make(sym,args.size(), args.size() ? &a[0] : 0);
}

iz3mgr::ast iz3mgr::make(symb sym){
    return make(sym,0,0);
}

iz3mgr::ast iz3mgr::make(symb sym, const ast &arg0){
    raw_ast *a = arg0.raw();
    return make(sym,1,&a);
}

iz3mgr::ast iz3mgr::make(symb sym, const ast &arg0, const ast &arg1){
    raw_ast *args[2];
    args[0] = arg0.raw();
    args[1] = arg1.raw();
    return make(sym,2,args);
}

iz3mgr::ast iz3mgr::make(symb sym, const ast &arg0, const ast &arg1, const ast &arg2){
    raw_ast *args[3];
    args[0] = arg0.raw();
    args[1] = arg1.raw();
    args[2] = arg2.raw();
    return make(sym,3,args);
}

iz3mgr::ast iz3mgr::make_quant(opr op, const std::vector<ast> &bvs, ast &body){
    if(bvs.size() == 0) return body;
    std::vector<raw_ast *> foo(bvs.size());


    std::vector<symbol> names;
    std::vector<class sort *> types;
    std::vector<expr *>  bound_asts;
    unsigned num_bound = bvs.size();

    for (unsigned i = 0; i < num_bound; ++i) {
        app* a = to_app(bvs[i].raw());
        symbol s(to_app(a)->get_decl()->get_name());
        names.push_back(s);
        types.push_back(m().get_sort(a));
        bound_asts.push_back(a);
    }
    expr_ref abs_body(m());
    expr_abstract(m(), 0, num_bound, &bound_asts[0], to_expr(body.raw()), abs_body);
    expr_ref result(m());
    result = m().mk_quantifier(
        op == Forall, 
        names.size(), &types[0], &names[0], abs_body.get(),            
        0, 
        symbol("itp"),
        symbol(),
        0, 0,
        0, 0
                               );
    return cook(result.get());
}

// FIXME replace this with existing Z3 functionality

iz3mgr::ast iz3mgr::clone(const ast &t, const std::vector<ast> &_args){
    if(_args.size() == 0)
        return t;

    ast_manager& m = m_manager;
    expr* a = to_expr(t.raw());
    static std::vector<raw_ast*> rargs(10);
    if(rargs.size() < _args.size())
        rargs.resize(_args.size());
    for(unsigned i = 0; i < _args.size(); i++)
        rargs[i] = _args[i].raw();
    expr* const* args =  (expr **)&rargs[0];
    switch(a->get_kind()) {
    case AST_APP: {
        app* e = to_app(a);
        if (e->get_num_args() != _args.size()) {
            assert(0);
        }
        else {
            a = m.mk_app(e->get_decl(), _args.size(), args);
        }
        break;
    }
    case AST_QUANTIFIER: {
        if (_args.size() != 1) {
            assert(0);
        }
        else {
            a = m.update_quantifier(to_quantifier(a), args[0]);
        }
        break;
    }
    default:
        break;
    }            
    return cook(a);
}


void iz3mgr::show(ast t){
    if(t.null()){
        std::cout  << "(null)" << std::endl;
    }
    params_ref p;
    p.set_bool("flat_assoc",false);
    std::cout  << mk_pp(t.raw(), m(), p) << std::endl;
}

void iz3mgr::show_symb(symb s){
    std::cout  << mk_pp(s, m()) << std::endl;
}

void iz3mgr::print_expr(std::ostream &s, const ast &e){
    params_ref p;
    p.set_bool("flat_assoc",false);
    s << mk_pp(e.raw(), m(), p);
}


void iz3mgr::print_clause(std::ostream &s, std::vector<ast> &cls){
    s << "(";
    for(unsigned i = 0; i < cls.size(); i++){
        if(i > 0) s << ",";
        print_expr(s,cls[i]);
    }
    s << ")";
}

void iz3mgr::show_clause(std::vector<ast> &cls){
    print_clause(std::cout,cls);
    std::cout << std::endl;
}

void iz3mgr::print_lit(ast lit){
    ast abslit = is_not(lit) ? arg(lit,0) : lit;
    int f = op(abslit);
    if(f == And || f == Or || f == Iff){
        if(is_not(lit)) std::cout << "~";
        std::cout << "[" << abslit << "]";
    }
    else
        std::cout << lit;
}  


static int pretty_cols = 79;
static int pretty_indent_chars = 2;

static int pretty_find_delim(const std::string &s, int pos){
    int level = 0;
    int end = s.size();
    for(; pos < end; pos++){
        int ch = s[pos];
        if(ch == '(')level++;
        if(ch == ')')level--;
        if(level < 0 || (level == 0 && ch == ','))break;
    }
    return pos;
}

static void pretty_newline(std::ostream &f, int indent){
    f << std::endl;
    for(int i = 0; i < indent; i++)
        f << " ";
}

void iz3mgr::pretty_print(std::ostream &f, const std::string &s){
    int cur_indent = 0;
    int indent = 0;
    int col = 0;
    int pos = 0;
    while(pos < (int)s.size()){
        int delim = pretty_find_delim(s,pos);
        if(s[pos] != ')' && s[pos] != ',' && cur_indent > indent){
            pretty_newline(f,indent);
            cur_indent = indent;
            col = indent;
            continue;
        }
        if (col + delim - pos > pretty_cols) {
            if (col > indent) {
                pretty_newline(f,indent);
                cur_indent = indent;
                col = indent;
                continue;
            }
            int paren = s.find('(',pos);
            if(paren != (int)std::string::npos){
                int chars = paren - pos + 1;
                f << s.substr(pos,chars);
                indent += pretty_indent_chars;
                if(col) pretty_newline(f,indent);
                cur_indent = indent;
                pos += chars;
                col = indent;
                continue;
            }
        }
        int chars = delim - pos + 1;
        f << s.substr(pos,chars);
        pos += chars;
        col += chars;
        if(s[delim] == ')')
            indent -= pretty_indent_chars;
    }
}


iz3mgr::opr iz3mgr::op(const ast &t){
    ast_kind dk = t.raw()->get_kind();
    switch(dk){
    case AST_APP: {
        expr * e = to_expr(t.raw());
        func_decl *d = to_app(t.raw())->get_decl();
        if (null_family_id == d->get_family_id())
            return Uninterpreted;
        // return (opr)d->get_decl_kind();
        if (m_basic_fid == d->get_family_id()) {
            switch(d->get_decl_kind()) {
            case OP_TRUE:     return True;
            case OP_FALSE:    return False;
            case OP_EQ:       return Equal;
            case OP_DISTINCT: return Distinct;
            case OP_ITE:      return Ite;
            case OP_AND:      return And;
            case OP_OR:       return Or;
            case OP_IFF:      return Iff;
            case OP_XOR:      return Xor;
            case OP_NOT:      return Not;
            case OP_IMPLIES:  return Implies;
            case OP_OEQ:      return Oeq;
            case OP_INTERP:   return Interp;
            default:
                return Other;
            }
        }
        if (m_arith_fid == d->get_family_id()) {
            switch(d->get_decl_kind()) {
            case OP_LE: return Leq;
            case OP_GE: return Geq;
            case OP_LT: return Lt;
            case OP_GT: return Gt;
            case OP_ADD: return Plus;
            case OP_SUB: return Sub;
            case OP_UMINUS: return Uminus;
            case OP_MUL: return Times;
            case OP_DIV: return Div;
            case OP_IDIV: return Idiv;
            case OP_REM: return Rem;
            case OP_MOD: return Mod;
            case OP_POWER: return Power;
            case OP_TO_REAL: return ToReal;
            case OP_TO_INT: return ToInt;
            case OP_IS_INT: return IsInt;
            default:
                if (m().is_unique_value(e)) 
                    return Numeral;
                return Other;
            }
        }
        if (m_array_fid == d->get_family_id()) {
            switch(d->get_decl_kind()) {
            case OP_STORE: return Store;
            case OP_SELECT: return Select;
            case OP_CONST_ARRAY: return ConstArray;
            case OP_ARRAY_DEFAULT: return ArrayDefault;
            case OP_ARRAY_MAP: return ArrayMap;
            case OP_SET_UNION: return SetUnion;
            case OP_SET_INTERSECT: return SetIntersect;
            case OP_SET_DIFFERENCE: return SetDifference;
            case OP_SET_COMPLEMENT: return SetComplement;
            case OP_SET_SUBSET: return SetSubSet;
            case OP_AS_ARRAY: return AsArray;
            default:
                return Other;
            }
        }
      
        return Other;
    }


    case AST_QUANTIFIER:
        return to_quantifier(t.raw())->is_forall() ? Forall : Exists;
    case AST_VAR:
        return Variable;
    default:;
    }
    return Other;
}


iz3mgr::pfrule iz3mgr::pr(const ast &t){
    func_decl *d = to_app(t.raw())->get_decl();
    assert(m_basic_fid == d->get_family_id());
    return d->get_decl_kind();
}

void iz3mgr::print_sat_problem(std::ostream &out, const ast &t){
    ast_smt_pp pp(m());
    pp.set_simplify_implies(false);
    pp.display_smt2(out, to_expr(t.raw()));
}

iz3mgr::ast iz3mgr::z3_simplify(const ast &e){
    ::expr * a = to_expr(e.raw());
    params_ref p; 
    th_rewriter m_rw(m(), p);
    expr_ref    result(m());
    m_rw(a, result);
    return cook(result);
}

iz3mgr::ast iz3mgr::z3_really_simplify(const ast &e){
    ::expr * a = to_expr(e.raw());
    params_ref simp_params;
    simp_params.set_bool(":som",true);
    simp_params.set_bool(":sort-sums",true);
    th_rewriter m_rw(m(), simp_params);
    expr_ref    result(m());
    m_rw(a, result);
    return cook(result);
}


#if 0
static rational lcm(const rational &x, const rational &y){
    int a = x.numerator();
    int b = y.numerator();
    return rational(a * b / gcd(a, b));
}
#endif

static rational extract_lcd(std::vector<rational> &res){
    if(res.size() == 0) return rational(1); // shouldn't happen
    rational lcd = denominator(res[0]);
    for(unsigned i = 1; i < res.size(); i++)
        lcd = lcm(lcd,denominator(res[i]));
    for(unsigned i = 0; i < res.size(); i++)
        res[i] *= lcd;
    return lcd;
}

void iz3mgr::get_farkas_coeffs(const ast &proof, std::vector<ast>& coeffs){
    std::vector<rational> rats;
    get_farkas_coeffs(proof,rats);
    coeffs.resize(rats.size());
    for(unsigned i = 0; i < rats.size(); i++){
        class sort *is = m().mk_sort(m_arith_fid, INT_SORT);
        ast coeff = cook(m_arith_util.mk_numeral(rats[i],is));
        coeffs[i] = coeff;
    }
}

static void abs_rat(std::vector<rational> &rats){
    // check that they are all non-neg -- if neg, take abs val and warn!
    for(unsigned i = 0; i < rats.size(); i++)
        if(rats[i].is_neg()){
            //      std::cout << "negative Farkas coeff!\n";
            rats[i] = -rats[i];
        }
}

bool iz3mgr::is_farkas_coefficient_negative(const ast &proof, int n){
    rational r;
    symb s = sym(proof);
    bool ok = s->get_parameter(n+2).is_rational(r);
    if(!ok)
        throw iz3_exception("Bad Farkas coefficient");
    return r.is_neg();
}

void iz3mgr::get_farkas_coeffs(const ast &proof, std::vector<rational>& rats){
    symb s = sym(proof);
    int numps = s->get_num_parameters();
    rats.resize(numps-2);
#if 0
    if(num_prems(proof) < numps-2){
        std::cout << "bad farkas rule: " << num_prems(proof) << " premises should be " << numps-2 << "\n";
    }
#endif
    for(int i = 2; i < numps; i++){
        rational r;
        bool ok = s->get_parameter(i).is_rational(r);
        if(!ok)
            throw iz3_exception("Bad Farkas coefficient");
#if 0 
        {
            ast con = conc(prem(proof,i-2));
            ast temp = make_real(r); // for debugging
            opr o = is_not(con) ? op(arg(con,0)) : op(con);
            if(is_not(con) ? (o == Leq || o == Lt) : (o == Geq || o == Gt))
                r = -r;
        }
#endif
        rats[i-2] = r;
    }
#if 0
    if(rats.size() != 0 && rats[0].is_neg()){
        for(unsigned i = 0; i < rats.size(); i++){
            assert(rats[i].is_neg());
            rats[i] = -rats[i];
        }
    }
#endif
    abs_rat(rats);
    extract_lcd(rats);
}

void iz3mgr::get_broken_gcd_test_coeffs(const ast &proof, std::vector<rational>& rats){
    symb s = sym(proof);
    int numps = s->get_num_parameters();
    rats.resize(numps-2);
    for(int i = 2; i < numps; i++){
        rational r;
        bool ok = s->get_parameter(i).is_rational(r);
        if(!ok)
            throw "Bad Farkas coefficient";
        rats[i-2] = r;
    }
    extract_lcd(rats);
}

void iz3mgr::get_assign_bounds_coeffs(const ast &proof, std::vector<ast>& coeffs){
    std::vector<rational> rats;
    get_assign_bounds_coeffs(proof,rats);
    coeffs.resize(rats.size());
    for(unsigned i = 0; i < rats.size(); i++){
        coeffs[i] = make_int(rats[i]);
    }
}

void iz3mgr::get_assign_bounds_coeffs(const ast &proof, std::vector<rational>& rats){
    symb s = sym(proof);
    int numps = s->get_num_parameters();
    rats.resize(numps-1);
    rats[0] = rational(1);
    ast conseq = arg(conc(proof),0);
    opr conseq_o = is_not(conseq) ? op(arg(conseq,0)) : op(conseq);
    bool conseq_neg = is_not(conseq) ? (conseq_o == Leq || conseq_o == Lt) : (conseq_o == Geq || conseq_o == Gt);
    for(int i = 2; i < numps; i++){
        rational r;
        bool ok = s->get_parameter(i).is_rational(r);
        if(!ok)
            throw iz3_exception("Bad Farkas coefficient");
        {
            ast con = arg(conc(proof),i-1);
            ast temp = make_real(r); // for debugging
            opr o = is_not(con) ? op(arg(con,0)) : op(con);
            if(is_not(con) ? (o == Leq || o == Lt) : (o == Geq || o == Gt))
                r = -r;
            if(conseq_neg)
                r = -r;
        }
        rats[i-1] = r;
    }
#if 0
    if(rats[1].is_neg()){ // work around bug -- if all coeffs negative, negate them
        for(unsigned i = 1; i < rats.size(); i++){
            if(!rats[i].is_neg())
                throw iz3_exception("Bad Farkas coefficients");
            rats[i] = -rats[i];
        }
    }
#endif
    abs_rat(rats);
    extract_lcd(rats);
}

void iz3mgr::get_gomory_cut_coeffs(const ast &proof, std::vector<ast>& coeffs){
    std::vector<rational> rats;
    get_gomory_cut_coeffs(proof,rats);
    coeffs.resize(rats.size());
    for(unsigned i = 0; i < rats.size(); i++){
        coeffs[i] = make_int(rats[i]);
    }
}

void iz3mgr::get_gomory_cut_coeffs(const ast &proof, std::vector<rational>& rats){
    symb s = sym(proof);
    int numps = s->get_num_parameters();
    rats.resize(numps-2);
    for(int i = 2; i < numps; i++){
        rational r;
        bool ok = s->get_parameter(i).is_rational(r);
        if(!ok)
            throw "Bad Farkas coefficient";
        rats[i-2] = r;
    }
    abs_rat(rats);
    extract_lcd(rats);
}

void iz3mgr::get_assign_bounds_rule_coeffs(const ast &proof, std::vector<ast>& coeffs){
    std::vector<rational> rats;
    get_assign_bounds_rule_coeffs(proof,rats);
    coeffs.resize(rats.size());
    for(unsigned i = 0; i < rats.size(); i++){
        coeffs[i] = make_int(rats[i]);
    }
}

void iz3mgr::get_assign_bounds_rule_coeffs(const ast &proof, std::vector<rational>& rats){
    symb s = sym(proof);
    int numps = s->get_num_parameters();
    rats.resize(numps-1);
    rats[0] = rational(1);
    ast conseq = arg(conc(proof),0);
    opr conseq_o = is_not(conseq) ? op(arg(conseq,0)) : op(conseq);
    bool conseq_neg = is_not(conseq) ? (conseq_o == Leq || conseq_o == Lt) : (conseq_o == Geq || conseq_o == Gt);
    for(int i = 2; i < numps; i++){
        rational r;
        bool ok = s->get_parameter(i).is_rational(r);
        if(!ok)
            throw iz3_exception("Bad Farkas coefficient");
        {
            ast con = conc(prem(proof,i-2));
            ast temp = make_real(r); // for debugging
            opr o = is_not(con) ? op(arg(con,0)) : op(con);
            if(is_not(con) ? (o == Leq || o == Lt) : (o == Geq || o == Gt))
                r = -r;
            if(conseq_neg)
                r = -r;
        }
        rats[i-1] = r;
    }
#if 0
    if(rats[1].is_neg()){ // work around bug -- if all coeffs negative, negate them
        for(unsigned i = 1; i < rats.size(); i++){
            if(!rats[i].is_neg())
                throw iz3_exception("Bad Farkas coefficients");
            rats[i] = -rats[i];
        }
    }
#endif
    abs_rat(rats);
    extract_lcd(rats);
}

/** Set P to P + cQ, where P and Q are linear inequalities. Assumes P is 0 <= y or 0 < y. */

void iz3mgr::linear_comb(ast &P, const ast &c, const ast &Q, bool round_off){
    ast Qrhs;
    bool qstrict = false;
    if(is_not(Q)){
        ast nQ = arg(Q,0);
        switch(op(nQ)){
        case Gt:
            Qrhs = make(Sub,arg(nQ,1),arg(nQ,0));
            break;
        case Lt: 
            Qrhs = make(Sub,arg(nQ,0),arg(nQ,1));
            break;
        case Geq:
            Qrhs = make(Sub,arg(nQ,1),arg(nQ,0));
            qstrict = true;
            break;
        case Leq: 
            Qrhs = make(Sub,arg(nQ,0),arg(nQ,1));
            qstrict = true;
            break;
        default:
            throw iz3_exception("not an inequality");
        }
    }
    else {
        switch(op(Q)){
        case Leq:
            Qrhs = make(Sub,arg(Q,1),arg(Q,0));
            break;
        case Geq: 
            Qrhs = make(Sub,arg(Q,0),arg(Q,1));
            break;
        case Lt:
            Qrhs = make(Sub,arg(Q,1),arg(Q,0));
            qstrict = true;
            break;
        case Gt: 
            Qrhs = make(Sub,arg(Q,0),arg(Q,1));
            qstrict = true;
            break;
        default:
            throw iz3_exception("not an inequality");
        }
    }
    bool pstrict = op(P) == Lt;
    if (round_off && get_type(Qrhs) != int_type())
        round_off = false;
    if(qstrict && round_off && (pstrict || !(c == make_int(rational(1))))){
        Qrhs = make(Sub,Qrhs,make_int(rational(1)));
        qstrict = false;
    }
    Qrhs = make(Times,c,Qrhs);
    bool strict = pstrict || qstrict;
    if(strict)
        P = make(Lt,arg(P,0),make(Plus,arg(P,1),Qrhs));
    else
        P = make(Leq,arg(P,0),make(Plus,arg(P,1),Qrhs));
}

iz3mgr::ast iz3mgr::sum_inequalities(const std::vector<ast> &coeffs, const std::vector<ast> &ineqs, bool round_off){
    ast zero = make_int("0");
    ast thing = make(Leq,zero,zero);
    for(unsigned i = 0; i < ineqs.size(); i++){
        linear_comb(thing,coeffs[i],ineqs[i], round_off);
    }
    thing = simplify_ineq(thing);
    return thing;
}

void iz3mgr::mk_idiv(const ast& t, const rational &d, ast &whole, ast &frac){
    opr o = op(t);
    if(o == Plus){
        int nargs = num_args(t);
        for(int i = 0; i < nargs; i++)
            mk_idiv(arg(t,i),d,whole,frac);
        return;
    }
    else if(o == Times){
        rational coeff;
        if(is_numeral(arg(t,0),coeff)){
            if(gcd(coeff,d) == d){
                whole = make(Plus,whole,make(Times,make_int(coeff/d),arg(t,1)));
                return;
            }
        }
    }
    frac = make(Plus,frac,t);
}

iz3mgr::ast iz3mgr::mk_idiv(const ast& q, const rational &d){
    ast t = z3_simplify(q);
    if(d == rational(1))
        return t;
    else {
        ast whole = make_int("0");
        ast frac = whole;
        mk_idiv(t,d,whole,frac);
        return z3_simplify(make(Plus,whole,make(Idiv,z3_simplify(frac),make_int(d))));
    }
}

iz3mgr::ast iz3mgr::mk_idiv(const ast& t, const ast &d){
    rational r;
    if(is_numeral(d,r))
        return mk_idiv(t,r);
    return make(Idiv,t,d);
}


// does variable occur in expression?
int iz3mgr::occurs_in1(stl_ext::hash_map<ast,bool> &occurs_in_memo,ast var, ast e){
    std::pair<ast,bool> foo(e,false);
    std::pair<hash_map<ast,bool>::iterator,bool> bar = occurs_in_memo.insert(foo);
    bool &res = bar.first->second;
    if(bar.second){
        if(e == var) res = true;
        int nargs = num_args(e);
        for(int i = 0; i < nargs; i++)
            res |= occurs_in1(occurs_in_memo,var,arg(e,i));
    }
    return res;
}

int iz3mgr::occurs_in(ast var, ast e){
    hash_map<ast,bool> memo;
    return occurs_in1(memo,var,e);
}


bool iz3mgr::solve_arith(const ast &v, const ast &x, const ast &y, ast &res){
    if(occurs_in(v,y))
        return false;
    if(op(x) == Plus){
        int n = num_args(x);
        for(int i = 0; i < n; i++){
            if(arg(x,i) == v){
                res = z3_simplify(make(Sub, y, make(Sub, x, v)));
                return true;
            }
        }
    }
    return false;
}

// find a controlling equality for a given variable v in a term
// a controlling equality is of the form v = t, which, being
// false would force the formula to have the specifid truth value
// returns t, or null if no such

iz3mgr::ast iz3mgr::cont_eq(stl_ext::hash_set<ast> &cont_eq_memo, bool truth, ast v, ast e){
    if(is_not(e)) return cont_eq(cont_eq_memo, !truth,v,arg(e,0));
    if(cont_eq_memo.find(e) != cont_eq_memo.end())
        return ast();
    cont_eq_memo.insert(e);
    if(!truth && op(e) == Equal){
        if(arg(e,0) == v && !occurs_in(v,arg(e,1))) return(arg(e,1));
        if(arg(e,1) == v && !occurs_in(v,arg(e,0))) return(arg(e,0));
        ast res;
        if(solve_arith(v,arg(e,0),arg(e,1),res)) return res;
        if(solve_arith(v,arg(e,1),arg(e,0),res)) return res;
    }
    if((!truth && op(e) == And) || (truth && op(e) == Or)){
        int nargs = num_args(e);
        for(int i = 0; i < nargs; i++){
            ast res = cont_eq(cont_eq_memo, truth, v, arg(e,i));
            if(!res.null()) return res;
        }
    }
    if(truth && op(e) == Implies){
        ast res = cont_eq(cont_eq_memo, !truth, v, arg(e,0));
        if(!res.null()) return res;
        res = cont_eq(cont_eq_memo, truth, v, arg(e,1));
        if(!res.null()) return res;
    }
    return ast();
}

// substitute a term t for unbound occurrences of variable v in e
  
iz3mgr::ast iz3mgr::subst(stl_ext::hash_map<ast,ast> &subst_memo, ast var, ast t, ast e){
    if(e == var) return t;
    std::pair<ast,ast> foo(e,ast());
    std::pair<hash_map<ast,ast>::iterator,bool> bar = subst_memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
        int nargs = num_args(e);
        std::vector<ast> args(nargs);
        for(int i = 0; i < nargs; i++)
            args[i] = subst(subst_memo,var,t,arg(e,i));
        opr f = op(e);
        if(f == Equal && args[0] == args[1]) res = mk_true();
        else res = clone(e,args);
    }
    return res;
}

iz3mgr::ast iz3mgr::subst(ast var, ast t, ast e){
    hash_map<ast,ast> memo;
    return subst(memo,var,t,e);
}

iz3mgr::ast iz3mgr::subst(stl_ext::hash_map<ast,ast> &subst_memo,ast e){
    std::pair<ast,ast> foo(e,ast());
    std::pair<hash_map<ast,ast>::iterator,bool> bar = subst_memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
        int nargs = num_args(e);
        std::vector<ast> args(nargs);
        for(int i = 0; i < nargs; i++)
            args[i] = subst(subst_memo,arg(e,i));
        opr f = op(e);
        if(f == Equal && args[0] == args[1]) res = mk_true();
        else res = clone(e,args);
    }
    return res;
}

// apply a quantifier to a formula, with some optimizations
// 1) bound variable does not occur -> no quantifier
// 2) bound variable must be equal to some term -> substitute

iz3mgr::ast iz3mgr::apply_quant(opr quantifier, ast var, ast e){
    if((quantifier == Forall && op(e) == And)
       || (quantifier == Exists && op(e) == Or)){
        int n = num_args(e);
        std::vector<ast> args(n);
        for(int i = 0; i < n; i++)
            args[i] = apply_quant(quantifier,var,arg(e,i));
        return make(op(e),args);
    }
    if(!occurs_in(var,e))return e;
    hash_set<ast> cont_eq_memo; 
    ast cterm = cont_eq(cont_eq_memo, quantifier == Forall, var, e);
    if(!cterm.null()){
        return subst(var,cterm,e);
    }
    std::vector<ast> bvs; bvs.push_back(var);
    return make_quant(quantifier,bvs,e);
}

#if 0
void iz3mgr::get_bound_substitutes(stl_ext::hash_map<ast,bool> &memo, const ast &e, const ast &var, std::vector<ast> &substs){
    std::pair<ast,bool> foo(e,false);
    std::pair<hash_map<ast,bool>::iterator,bool> bar = memo.insert(foo);
    if(bar.second){
        if(op(e) == 
           }
 
    }
#endif
