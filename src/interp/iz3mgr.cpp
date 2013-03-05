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


#include "iz3mgr.h"

#include <stdio.h>
#include <fstream>
#include <iostream>
#include <ostream>

#include "expr_abstract.h"


#ifndef WIN32
using namespace stl_ext;
#endif


std::ostream &operator <<(std::ostream &s, const iz3mgr::ast &a){
  return s;
}


iz3mgr::ast iz3mgr::make_var(const std::string &name, type ty){ 
  symbol s = symbol(name.c_str());
  return m().mk_const(m().mk_const_decl(s, ty));
}

iz3mgr::ast iz3mgr::make(opr op, int n, raw_ast **args){
  return m().mk_app(m().get_basic_family_id(), op, 0, 0, n, (expr **)args);        
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

iz3mgr::ast iz3mgr::make(opr op, ast &arg0){
  raw_ast *a = arg0.raw();
  return make(op,1,&a);
}

iz3mgr::ast iz3mgr::make(opr op, const ast &arg0, const ast &arg1){
  raw_ast *args[2];
  args[0] = arg0.raw();
  args[1] = arg1.raw();
  return make(op,2,args);
}

iz3mgr::ast iz3mgr::make(opr op, ast &arg0, ast &arg1, ast &arg2){
  raw_ast *args[3];
  args[0] = arg0.raw();
  args[1] = arg1.raw();
  args[2] = arg2.raw();
  return make(op,3,args);
}

iz3mgr::ast iz3mgr::make(symb sym, int n, raw_ast **args){
  return m().mk_app(sym, n, (expr **) args);   
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

iz3mgr::ast iz3mgr::make(symb sym, ast &arg0){
  raw_ast *a = arg0.raw();
  return make(sym,1,&a);
}

iz3mgr::ast iz3mgr::make(symb sym, ast &arg0, ast &arg1){
  raw_ast *args[2];
  args[0] = arg0.raw();
  args[1] = arg1.raw();
  return make(sym,2,args);
}

iz3mgr::ast iz3mgr::make(symb sym, ast &arg0, ast &arg1, ast &arg2){
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
  std::vector<sort *> types;
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
			     symbol(),
			     symbol(),
			     0, 0,
			     0, 0
			     );
  return result.get();
}

iz3mgr::ast iz3mgr::clone(ast &t, const std::vector<ast> &_args){
  if(_args.size() == 0)
    return t;

  ast_manager& m = *m_manager.get();
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
  return a;
}


void iz3mgr::show(ast t){
  std::cout  << mk_pp(t.raw(), m()) << std::endl;
}

void iz3mgr::print_expr(std::ostream &s, const ast &e){
  s << mk_pp(e.raw(), m());
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


iz3mgr::opr iz3mgr::op(ast &t){
    ast_kind dk = t.raw()->get_kind();
    switch(dk){
    case AST_APP: {
      expr * e = to_expr(t.raw());
      if (m().is_unique_value(e)) 
	return Numeral;
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
