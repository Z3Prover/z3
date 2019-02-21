/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_extension.h

Abstract:

    An abstract class for SAT extensions.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef SAT_EXTENSION_H_
#define SAT_EXTENSION_H_

#include "sat/sat_types.h"
#include "util/params.h"
#include "util/statistics.h"

namespace sat {

    enum check_result {
        CR_DONE, CR_CONTINUE, CR_GIVEUP
    };

    class literal_occs_fun {
    public:
        virtual double operator()(literal l) = 0;        
    };


    typedef svector<ext_constraint_idx> ext_constraint_list;

    class ext_use_list {
        vector<ext_constraint_list> m_use_list;
    public:
        void init(unsigned num_vars) { m_use_list.reset(); m_use_list.resize(num_vars*2); }
        void insert(literal l, ext_constraint_idx idx) { get(l).push_back(idx); }
        ext_constraint_list & get(literal l) { return m_use_list[l.index()]; }
        ext_constraint_list const & get(literal l) const { return m_use_list[l.index()]; }
        void finalize() { m_use_list.finalize(); }
    };

    class extension {
    public:
        virtual ~extension() {}
        virtual void set_solver(solver* s) = 0;
        virtual void set_lookahead(lookahead* s) = 0;
        virtual void set_unit_walk(unit_walk* u) = 0;
        virtual bool propagate(literal l, ext_constraint_idx idx) = 0;
        virtual double get_reward(literal l, ext_constraint_idx idx, literal_occs_fun& occs) const = 0;
        virtual void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) = 0;
        virtual bool is_extended_binary(ext_justification_idx idx, literal_vector & r) = 0;
        virtual void asserted(literal l) = 0;
        virtual check_result check() = 0;
        virtual lbool resolve_conflict() { return l_undef; } // stores result in sat::solver::m_lemma
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual void simplify() = 0;
        // have a way to replace l by r in all constraints
        virtual bool set_root(literal l, literal r) { return false; }
        virtual void flush_roots() {}
        virtual void clauses_modifed() = 0;
        virtual lbool get_phase(bool_var v) = 0;
        virtual std::ostream& display(std::ostream& out) const = 0;
        virtual std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const = 0;
        virtual std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const = 0;
        virtual void collect_statistics(statistics& st) const = 0;
        virtual extension* copy(solver* s) = 0;       
        virtual extension* copy(lookahead* s, bool learned) = 0;       
        virtual void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) = 0;
        virtual void gc() = 0;
        virtual void pop_reinit() = 0;
        virtual bool validate() = 0;
        virtual void init_use_list(ext_use_list& ul) = 0;
        virtual bool is_blocked(literal l, ext_constraint_idx) = 0;
        virtual bool check_model(model const& m) const = 0;
        virtual unsigned max_var(unsigned w) const = 0;
    };

};

#endif
