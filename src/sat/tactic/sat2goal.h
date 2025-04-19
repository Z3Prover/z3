/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat2goal.h

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
#include "sat/sat_model_converter.h"
#include "sat/sat_solver.h"
#include "ast/converters/generic_model_converter.h"
#include "sat/smt/atom2bool_var.h"

class sat2goal {
    struct imp;
    imp *  m_imp;
    struct scoped_set_imp;
public:

    class mc : public model_converter {
        ast_manager&            m;
        sat::model_converter    m_smc;
        generic_model_converter_ref m_gmc;
        expr_ref_vector          m_var2expr;

        // flushes from m_smc to m_gmc;
        void flush_gmc();
        
    public:
        mc(ast_manager& m);
        // flush model converter from SAT solver to this structure.
        void flush_smc(sat::solver& s, atom2bool_var const& map);
        using model_converter::operator();
        void operator()(sat::model& m);
        void operator()(model_ref& md) override;
        void operator()(expr_ref& fml) override; 
        model_converter* translate(ast_translation& translator) override;
        void set_env(ast_pp_util* visitor) override;
        void display(std::ostream& out) override;
        void get_units(obj_map<expr, bool>& units) override;
        expr* var2expr(sat::bool_var v) const { return m_var2expr.get(v, nullptr); }
        expr_ref lit2expr(sat::literal l);
        void insert(sat::bool_var v, expr * atom, bool aux);
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
    void operator()(sat::solver & t, atom2bool_var const & m, params_ref const & p, goal & s, ref<mc> & mc);
    
};
