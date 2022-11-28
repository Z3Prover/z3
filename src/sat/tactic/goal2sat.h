/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal2sat.h

Abstract:

    "Compile" a goal into the SAT engine.
    Atoms are "abstracted" into boolean variables.
    The mapping between boolean variables and atoms
    can be used to convert back the state of the 
    SAT engine into a goal.

    The idea is to support scenarios such as:
    1) simplify, blast, convert into SAT, and solve
    2) convert into SAT, apply SAT for a while, learn new units, and translate back into a goal.
    3) convert into SAT, apply SAT preprocessor (failed literal propagation, resolution, etc) and translate back into a goal.
    4) Convert boolean structure into SAT, convert atoms into another engine, combine engines using lazy combination, solve.

Author:

    Leonardo (leonardo) 2011-10-26

Notes:

--*/
#pragma once

#include "tactic/goal.h"
#include "sat/sat_solver_core.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_internalizer.h"

namespace euf {
    class solver;
}

class goal2sat {
public:
    typedef obj_map<expr, sat::literal> dep2asm_map;
private:
    struct imp;
    imp *  m_imp;
    unsigned m_scopes = 0;


public:
    goal2sat();
    ~goal2sat();


    static void collect_param_descrs(param_descrs & r);

    static bool has_unsupported_bool(goal const & s);

    /**
       \brief "Compile" the goal into the given sat solver.
       Store a mapping from atoms to boolean variables into m.
       
       \remark m doesn't need to be empty. the definitions there are 
       reused.
       
       \warning conversion throws a tactic_exception, if it is interrupted (by set_cancel),
       an unsupported operator is found, or memory consumption limit is reached (set with param :max-memory).
    */
    void operator()(goal const & g, params_ref const & p, sat::solver_core & t, atom2bool_var & m, dep2asm_map& dep2asm, bool default_external = false);

    void operator()(unsigned n, expr* const* fmls);

    void init(ast_manager& m, params_ref const & p, sat::solver_core & t, atom2bool_var & map, dep2asm_map& dep2asm, bool default_external);

    void assumptions(unsigned n, expr* const* fmls);

    sat::literal internalize(expr* a);

    void get_interpreted_funs(func_decl_ref_vector& funs);

    bool has_interpreted_funs() const;

    bool has_euf() const;

    sat::sat_internalizer& si(ast_manager& m, params_ref const& p, sat::solver_core& t, atom2bool_var& a2b, dep2asm_map& dep2asm, bool default_external = false);

    void update_model(model_ref& mdl);

    void user_push();
    
    void user_pop(unsigned n);

    euf::solver* ensure_euf();

};
