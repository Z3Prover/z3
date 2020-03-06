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
#ifndef GOAL2SAT_H_
#define GOAL2SAT_H_

#include "tactic/goal.h"
#include "sat/sat_solver.h"
#include "tactic/model_converter.h"
#include "tactic/generic_model_converter.h"
#include "sat/tactic/atom2bool_var.h"

class goal2sat {
    struct imp;
    imp *  m_imp;
    struct scoped_set_imp;
    expr_ref_vector* m_interpreted_atoms;

public:
    goal2sat();
    ~goal2sat() { dealloc(m_interpreted_atoms); }

    typedef obj_map<expr, sat::literal> dep2asm_map;

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
    void operator()(goal const & g, params_ref const & p, sat::solver_core & t, atom2bool_var & m, dep2asm_map& dep2asm, bool default_external = false, bool is_lemma = false);

    void get_interpreted_atoms(expr_ref_vector& atoms);

};


class sat2goal {
    struct imp;
    imp *  m_imp;
    struct scoped_set_imp;
public:

    class mc : public model_converter {
        ast_manager&            m;
        sat::model_converter    m_smc;
        generic_model_converter_ref m_gmc;
        app_ref_vector          m_var2expr;

        // flushes from m_smc to m_gmc;
        void flush_gmc();
        
    public:
        mc(ast_manager& m);
        ~mc() override {}
        // flush model converter from SAT solver to this structure.
        void flush_smc(sat::solver_core& s, atom2bool_var const& map);
        void operator()(sat::model& m);
        void operator()(model_ref& md) override;
        void operator()(expr_ref& fml) override; 
        model_converter* translate(ast_translation& translator) override;
        void set_env(ast_pp_util* visitor) override;
        void display(std::ostream& out) override;
        void get_units(obj_map<expr, bool>& units) override;
        unsigned num_vars() const { return m_var2expr.size(); }
        app* var2expr(sat::bool_var v) const { return m_var2expr.get(v, nullptr); }
        expr_ref lit2expr(sat::literal l);
        void insert(sat::bool_var v, app * atom, bool aux);
    };

    sat2goal();


    static void collect_param_descrs(param_descrs & r);

    /**
       \brief Translate the state of the SAT engine back into a goal.
       The SAT solver may use variables that are not in \c m. The translator
       creates fresh boolean AST variables for them. They are stored in fvars.
       
       \warning conversion throws a tactic_exception, if it is interrupted (by set_cancel),
       or memory consumption limit is reached (set with param :max-memory).
    */
    void operator()(sat::solver_core & t, atom2bool_var const & m, params_ref const & p, goal & s, ref<mc> & mc);
    
};

#endif
