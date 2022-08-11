/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver_core.h

Abstract:

    SAT solver API class.

Author:

    Nikolaj Bjorner (nbjorner) 2019-02-06

Revision History:

--*/
#pragma once

#include "sat/sat_model_converter.h"
#include "sat/sat_types.h"

namespace sat {

    class cut_simplifier;
    class extension;

    class solver_core {
    protected:
        reslimit&               m_rlimit;
    public:
        solver_core(reslimit& l) : m_rlimit(l) {}
        virtual ~solver_core() = default;

        // add clauses
        virtual void add_clause(unsigned n, literal* lits, status st) = 0;
        
        void add_clause(literal l1, literal l2, literal l3, status st) {
            literal lits[3] = {l1, l2, l3};
            add_clause(3, lits, st);
        }
        // create boolean variable, tagged as external (= true) or internal (can be eliminated).
        virtual bool_var add_var(bool ext) = 0;

        virtual void set_external(bool_var v) {}
        virtual void set_eliminated(bool_var v, bool f) {}
        virtual void set_phase(literal l) { }

        // optional support for user-scopes. Not relevant for sat_tactic integration. 
        // it is only relevant for incremental mode SAT, which isn't wrapped (yet)
        virtual void user_push() { throw default_exception("optional API not supported"); }
        virtual void user_pop(unsigned num_scopes) {};
        virtual unsigned num_user_scopes() const { return 0;}
        virtual unsigned num_scopes() const { return 0; }


        // hooks for extension solver. really just ba_solver atm.
        virtual extension* get_extension() const { return nullptr; }
        virtual void       set_extension(extension* e) { if (e) throw default_exception("optional API not supported"); }

        virtual cut_simplifier* get_cut_simplifier() { return nullptr; }
    };
};

