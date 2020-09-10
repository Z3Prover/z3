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
#pragma once

#include <functional>
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
        bool contains(bool_var v) const {
            if (m_use_list.size() <= 2*v)
                return false;
            literal lit(v, false);
            return !get(lit).empty() || !get(~lit).empty();
        }
    };

    class extension {
    public:        
        virtual ~extension() {}
        virtual unsigned get_id() const { return 0; }
        virtual void set_solver(solver* s) = 0;
        virtual void set_lookahead(lookahead* s) {};
        virtual void init_search() {}
        virtual bool propagate(literal l, ext_constraint_idx idx) = 0;
        virtual bool unit_propagate() = 0;
        virtual bool is_external(bool_var v) = 0;
        virtual double get_reward(literal l, ext_constraint_idx idx, literal_occs_fun& occs) const { return 0; }
        virtual void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r, bool probing) = 0;
        virtual bool is_extended_binary(ext_justification_idx idx, literal_vector & r) { return false; }
        virtual void asserted(literal l) = 0;
        virtual check_result check() = 0;
        virtual lbool resolve_conflict() { return l_undef; } // stores result in sat::solver::m_lemma
        virtual void push() = 0;
        void push_scopes(unsigned n) { for (unsigned i = 0; i < n; ++i) push(); }
        virtual void pop(unsigned n) = 0;
        virtual void pre_simplify() {}
        virtual void simplify() {}
        // have a way to replace l by r in all constraints
        virtual bool set_root(literal l, literal r) { return false; }
        virtual void flush_roots() {}
        virtual void clauses_modifed() {}
        virtual lbool get_phase(bool_var v) { return l_undef; }
        virtual std::ostream& display(std::ostream& out) const = 0;
        virtual std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const = 0;
        virtual std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const = 0;
        virtual void collect_statistics(statistics& st) const = 0;
        virtual extension* copy(solver* s) { UNREACHABLE(); return nullptr; }       
        virtual void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {}
        virtual void gc() {}
        virtual void pop_reinit() {}
        virtual bool validate() { return true; }
        virtual void init_use_list(ext_use_list& ul) {}
        virtual bool is_blocked(literal l, ext_constraint_idx) { return false; }
        virtual bool check_model(model const& m) const { return true; }
        virtual unsigned max_var(unsigned w) const { return w; }

        virtual bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                                std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) {                                
            return false;
        }
    };

};

