/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    pb_solver_interface.h

Abstract:
 
    Abstract interface for a solver,
    covers functionality exposed by the sat and lookahead solvers.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/

#pragma once 

#include "sat/sat_types.h"
#include "sat/sat_solver.h"
#include "sat/smt/sat_smt.h"


namespace pb {

    typedef sat::literal literal;
    typedef sat::bool_var bool_var;
    typedef sat::literal_vector literal_vector;
    typedef std::pair<unsigned, literal> wliteral;
    class constraint;

    class solver_interface {
    public:
        virtual lbool value(bool_var v) const = 0;
        virtual lbool value(literal lit) const = 0;
        virtual bool is_false(literal lit) const = 0;
        virtual unsigned lvl(literal lit) const = 0;
        virtual unsigned lvl(bool_var v) const = 0;
        virtual bool inconsistent() const = 0;
        virtual sat::watch_list& get_wlist(literal l) = 0;
        virtual sat::watch_list const& get_wlist(literal l) const = 0;
        virtual void assign(literal l, sat::justification j) = 0; 
        virtual void set_conflict(sat::justification j, literal l) = 0;
        virtual sat::config const& get_config() const = 0;
        virtual void assign(constraint& c, literal lit) = 0;
        virtual void set_conflict(constraint& c, literal lit) = 0;
    };
}
