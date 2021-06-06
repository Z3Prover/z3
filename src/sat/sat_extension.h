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

    enum class check_result {
        CR_DONE, CR_CONTINUE, CR_GIVEUP
    };

    inline std::ostream& operator<<(std::ostream& out, check_result const& r) {
        switch (r) {
        case check_result::CR_DONE: return out << "done";
        case check_result::CR_CONTINUE: return out << "continue";
        default: return out << "giveup";
        }
    }

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
    protected:
        bool m_drating { false };
        int  m_id { 0 };
        symbol m_name;
        solver* m_solver { nullptr };
    public:        
        extension(symbol const& name, int id): m_id(id), m_name(name) { }
        virtual ~extension() {}
        int get_id() const { return m_id; }
        void set_solver(solver* s) { m_solver = s; }        
        solver& s() { return *m_solver; }
        solver const& s() const { return *m_solver; }
        symbol const& name() const { return m_name;  }

        virtual void set_lookahead(lookahead* s) {};
        class scoped_drating {
            extension& ext;
        public:
            scoped_drating(extension& e) :ext(e) { ext.m_drating = true;  }
            ~scoped_drating() { ext.m_drating = false;  }
        };
        virtual void init_search() {}
        virtual bool propagated(sat::literal l, sat::ext_constraint_idx idx) { UNREACHABLE(); return false; }
        virtual bool unit_propagate() = 0;        
        virtual bool is_external(bool_var v) { return false; }
        virtual double get_reward(literal l, ext_constraint_idx idx, literal_occs_fun& occs) const { return 0; }
        virtual void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r, bool probing) = 0;
        virtual bool is_extended_binary(ext_justification_idx idx, literal_vector & r) { return false; }
        virtual void asserted(literal l) {};
        virtual void set_eliminated(bool_var v) {};
        virtual check_result check() = 0;
        virtual lbool resolve_conflict() { return l_undef; } // stores result in sat::solver::m_lemma
        virtual void push() = 0;
        void push_scopes(unsigned n) { for (unsigned i = 0; i < n; ++i) push(); }
        virtual void pop(unsigned n) = 0;
        virtual void user_push() { push(); }
        virtual void user_pop(unsigned n) { pop(n); }
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
        virtual void collect_statistics(statistics& st) const {}
        virtual extension* copy(solver* s) { UNREACHABLE(); return nullptr; }       
        virtual void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {}
        virtual void gc() {}
        virtual void pop_reinit() {}
        virtual bool validate() { return true; }
        virtual void init_use_list(ext_use_list& ul) {}
        virtual bool is_blocked(literal l, ext_constraint_idx) { return false; }
        virtual bool check_model(model const& m) const { return true; }
        virtual void gc_vars(unsigned num_vars) {}
        virtual bool should_research(sat::literal_vector const& core) { return false;}
        virtual void add_assumptions() {}
        virtual bool tracking_assumptions() { return false; }
        virtual bool enable_self_propagate() const { return false; }

        virtual bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                                std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) {                                
            return false;
        }
        virtual bool is_pb() { return false; }
    };

};

