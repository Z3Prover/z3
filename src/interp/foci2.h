/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  foci2.h

  Abstract:

  An interface class for foci2.   

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifndef FOCI2_H
#define FOCI2_H

#include <vector>
#include <string>

#ifdef _WINDOWS
#define FOCI2_EXPORT __declspec(dllexport)
#else
#define FOCI2_EXPORT __attribute__ ((visibility ("default")))
#endif

class foci2 {
 public:
    virtual ~foci2(){}

    typedef int ast;
    typedef int symb;

    /** Built-in operators */
    enum ops {
        And = 0, Or, Not, Iff, Ite, Equal, Plus, Times, Floor, Leq, Div, Bool, Int, Array, Tsym, Fsym, Forall, Exists, Distinct, LastOp
    };
  
    virtual symb mk_func(const std::string &s) = 0;
    virtual symb mk_pred(const std::string &s) = 0;
    virtual ast mk_op(ops op, const std::vector<ast> args) = 0;
    virtual ast mk_op(ops op, ast) = 0;
    virtual ast mk_op(ops op, ast, ast) = 0;
    virtual ast mk_op(ops op, ast, ast, ast) = 0;
    virtual ast mk_int(const std::string &) = 0;
    virtual ast mk_rat(const std::string &) = 0;
    virtual ast mk_true() = 0;
    virtual ast mk_false() = 0;
    virtual ast mk_app(symb,const std::vector<ast> args) = 0;
  
    virtual bool get_func(ast, symb &) = 0;
    virtual bool get_pred(ast, symb &) = 0;
    virtual bool get_op(ast, ops &) = 0;
    virtual bool get_true(ast id) = 0;
    virtual bool get_false(ast id) = 0;
    virtual bool get_int(ast id, std::string &res) = 0;
    virtual bool get_rat(ast id, std::string &res) = 0;
    virtual const std::string &get_symb(symb) = 0;
  
    virtual int get_num_args(ast) = 0;
    virtual ast get_arg(ast, int) = 0;
  
    virtual void show_ast(ast) = 0;
  
    virtual bool interpolate(const std::vector<ast> &frames, std::vector<ast> &itps, std::vector<int> parents) = 0;

    FOCI2_EXPORT static foci2 *create(const std::string &);
};

#endif
