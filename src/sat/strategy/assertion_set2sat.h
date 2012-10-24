/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set2sat.h

Abstract:

    "Compile" an assertion set into the SAT engine.
    Atoms are "abstracted" into boolean variables.
    The mapping between boolean variables and atoms
    can be used to convert back the state of the 
    SAT engine into an assertion set.

    The idea is to support scenarios such as:
    1) simplify, blast, convert into SAT, and solve
    2) convert into SAT, apply SAT for a while, learn new units, and translate back into an assertion set.
    3) convert into SAT, apply SAT preprocessor (failed literal propagation, resolution, etc) and translate back into an assertion set.
    4) Convert boolean structure into SAT, convert atoms into another engine, combine engines using lazy combination, solve.

Author:

    Leonardo (leonardo) 2011-05-22

Notes:

--*/
#ifndef _ASSERTION_SET2SAT_H_
#define _ASSERTION_SET2SAT_H_

#include"assertion_set.h"
#include"sat_solver.h"
#include"strategy_exception.h"
#include"model_converter.h"
#include"atom2bool_var.h"

class assertion_set; // TODO: delete
void collect_boolean_interface(assertion_set const & s, obj_hashtable<expr> & r);

MK_ST_EXCEPTION(assertion_set2sat_exception);

class assertion_set2sat {
    struct imp;
    imp *  m_imp;
    struct scoped_set_imp;
public:
    assertion_set2sat();

    static void collect_param_descrs(param_descrs & r);

    static bool has_unsupported_bool(assertion_set const & s);

    /**
       \brief "Compile" the assertion set into the given sat solver.
       Store a mapping from atoms to boolean variables into m.
       
       \remark m doesn't need to be empty. the definitions there are 
       reused.
    */
    void operator()(assertion_set const & s, params_ref const & p, sat::solver & t, atom2bool_var & m);

    /**
       \brief "Compile" the formulas fs into the given sat solver.
       Store a mapping from atoms to boolean variables into m.

       \remark m doesn't need to be empty. the definitions there are 
       reused.
    */
    void operator()(ast_manager & mng, unsigned num, expr * const * fs, params_ref const & p, sat::solver & t, atom2bool_var & m);
    
    void operator()(ast_manager & mng, expr * f, params_ref const & p, sat::solver & t, atom2bool_var & m) { operator()(mng, 1, &f, p, t, m); }

    void set_cancel(bool f);
};

MK_ST_EXCEPTION(sat2assertion_set_exception);

class sat2assertion_set {
    struct imp;
    imp *  m_imp;
    struct scoped_set_imp;
public:
    sat2assertion_set();

    static void collect_param_descrs(param_descrs & r);

    /**
       \brief Translate the state of the SAT engine back into an assertion set.
       The SAT solver may use variables that are not in \c m. The translator
       creates fresh boolean AST variables for them. They are stored in fvars.
    */
    void operator()(sat::solver const & t, atom2bool_var const & m, params_ref const & p, assertion_set & s, model_converter_ref & mc);
    
    void set_cancel(bool f);
};

#endif
