/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_arith.h

Abstract:

    Arithmetic solver for smt::solver
    
Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:

--*/
#ifndef _SMT_ARITH_H_
#define _SMT_ARITH_H_

#include"ast.h"
#include"smt_solver_types.h"
#include"params.h"
#include"statistics.h"
class model;

namespace smt {

    class arith {
        struct imp;
        imp *       m_imp;
        params_ref  m_params;  
    public:
        arith(ast_manager & m, params_ref const & p);
        ~arith();
        void updt_params(params_ref const & p);
        void assert_axiom(expr * t, bool neg);
        void mk_atom(expr * t, atom_id id);
        void asserted(atom_id id, bool is_true);
        bool inconsistent() const;
        void push();
        void pop(unsigned num_scopes);
        void set_cancel(bool f);
        void simplify();
        void display(std::ostream & out) const;
        void reset();
        void preprocess();
        void collect_statistics(statistics & st) const;
        void reset_statistics();
        lbool check();
        void mk_model(model * md);
    };
};

#endif
