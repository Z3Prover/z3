/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_solver.h

Abstract:

    Nonlinear arithmetic satisfiability procedure.  The procedure is
    complete for nonlinear real arithmetic, but it also has limited
    support for integers.

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#ifndef _NLSAT_SOLVER_H_
#define _NLSAT_SOLVER_H_

#include"nlsat_types.h"
#include"params.h"
#include"statistics.h"

namespace nlsat {

    class solver {
        struct imp;
        imp * m_imp;
    public:
        solver(params_ref const & p);
        ~solver();

        /**
           \brief Return reference to rational manager.
        */
        unsynch_mpq_manager & qm();
        
        /**
           \brief Return reference to algebraic number manager.
        */
        anum_manager & am();

        /**
           \brief Return a reference to the polynomial manager used by the solver.
        */
        pmanager & pm();

        void set_display_var(display_var_proc const & proc);

        // -----------------------
        //
        // Variable, Atoms, Clauses & Assumption creation
        //
        // -----------------------

        /**
           \brief Create a fresh boolean variable that is not associated with any 
                  nonlinear arithmetic atom.
        */
        bool_var mk_bool_var();
    
        /**
           \brief Create a real/integer variable.
        */
        var mk_var(bool is_int);
        
        /**
           \brief Create an atom of the form: p=0, p<0, p>0
           Where p = ps[0]^e[0]*...*ps[sz-1]^e[sz-1]

           e[i] = 1 if is_even[i] is false
           e[i] = 2 if is_even[i] is true

           \pre sz > 0
        */
        bool_var mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even);

        /**
           \brief Create a literal for the p=0, p<0, p>0.
           Where p = ps[0]^e[0]*...*ps[sz-1]^e[sz-1]  for sz > 0
                 p = 1                                for sz = 0

           e[i] = 1 if is_even[i] is false
           e[i] = 2 if is_even[i] is true
        */
        literal mk_ineq_literal(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even);

        /**
           \brief Create an atom of the form: x=root[i](p), x<root[i](p), x>root[i](p)
        */
        bool_var mk_root_atom(atom::kind k, var x, unsigned i, poly * p);

        void inc_ref(bool_var b);
        void inc_ref(literal l) { inc_ref(l.var()); }
        void dec_ref(bool_var b);
        void dec_ref(literal l) { dec_ref(l.var()); }
        
        /**
           \brief Create a new clause.
        */
        void mk_clause(unsigned num_lits, literal * lits, assumption a = 0);

        // -----------------------
        //
        // Basic
        //
        // -----------------------

        /**
           \brief Return the number of Boolean variables.
        */
        unsigned num_bool_vars() const;
        
        /**
           \brief Get atom associated with Boolean variable. Return 0 if there is none.
        */
        atom * bool_var2atom(bool_var b);

        /**
           \brief Return number of integer/real variables
        */
        unsigned num_vars() const;

        bool is_int(var x) const;

        // -----------------------
        //
        // Search
        //
        // -----------------------
        lbool check();

        // -----------------------
        //
        // Model
        //
        // -----------------------
        anum const & value(var x) const;
        lbool bvalue(bool_var b) const;
        bool is_interpreted(bool_var b) const;

        lbool value(literal l) const;

        // -----------------------
        //
        // Misc
        //
        // -----------------------
        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void set_cancel(bool f);
        void collect_statistics(statistics & st);
        void reset_statistics();
        void display_status(std::ostream & out) const;

        // -----------------------
        //
        // Pretty printing
        //
        // -----------------------
   
        /**
           \brief Display solver's state.
        */
        void display(std::ostream & out) const;

        /**
           \brief Display literal
        */
        void display(std::ostream & out, literal l) const;

        /**
           \brief Display variable
        */
        void display(std::ostream & out, var x) const;
        
        display_var_proc const & display_proc() const;
    };

};

#endif
