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


#include "sat/sat_types.h"

namespace sat {

    class cut_simplifier;
    class extension;
    class drat;

    class solver_core {
    protected:
        reslimit&               m_rlimit;
    public:
        solver_core(reslimit& l) : m_rlimit(l) {}
        virtual ~solver_core() {}

        virtual void pop_to_base_level() {}
        virtual bool at_base_lvl() const { return true; }

        // retrieve model if solver return sat
        virtual model const & get_model() const = 0;

        // retrieve core from assumptions
        virtual literal_vector const& get_core() const = 0;

        // is the state inconsistent?
        virtual bool inconsistent() const = 0;

        // number of variables and clauses
        virtual unsigned num_vars() const = 0;
        virtual unsigned num_clauses() const = 0;

        // check satisfiability
        virtual lbool check(unsigned num_lits = 0, literal const* lits = nullptr) = 0;

        virtual char const* get_reason_unknown() const { return "reason unavailable"; }

        // add clauses
        virtual void add_clause(unsigned n, literal* lits, status st) = 0;
        void add_clause(literal l1, literal l2, status st) {
            literal lits[2] = {l1, l2};
            add_clause(2, lits, st);
        }
        void add_clause(literal l1, literal l2, literal l3, status st) {
            literal lits[3] = {l1, l2, l3};
            add_clause(3, lits, st);
        }
        // create boolean variable, tagged as external (= true) or internal (can be eliminated).
        virtual bool_var add_var(bool ext) = 0;

        // update parameters
        virtual void updt_params(params_ref const& p) {}
        

        virtual bool check_invariant() const { return true; }
        virtual void display_status(std::ostream& out) const {}
        virtual void display_dimacs(std::ostream& out) const {}

        virtual bool is_external(bool_var v) const { return true; }
        bool is_external(literal l) const { return is_external(l.var()); }
        virtual void set_external(bool_var v) {}
        virtual void set_non_external(bool_var v) {}
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

        virtual drat* get_drat_ptr() { return nullptr;  }


        // The following methods are used when converting the state from the SAT solver back
        // to a set of assertions. 

        // retrieve model converter that handles variable elimination and other transformations
        virtual void flush(model_converter& mc) {}

        // size of initial trail containing unit clauses
        virtual unsigned init_trail_size() const = 0;

        // literal at trail index i
        virtual literal trail_literal(unsigned i) const = 0;

        // collect n-ary clauses
        virtual clause_vector const& clauses() const = 0;

        // collect binary clauses
        typedef std::pair<literal, literal> bin_clause;
        virtual void collect_bin_clauses(svector<bin_clause> & r, bool learned, bool learned_only) const = 0;

        // collect statistics from sat solver
        virtual void collect_statistics(statistics & st) const {}

    };
};

