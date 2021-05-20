/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_types.h

Abstract:

    Basic types used in the SAT solver

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#pragma once

#include "util/debug.h"
#include "util/approx_set.h"
#include "util/lbool.h"
#include "util/z3_exception.h"
#include "util/common_msgs.h"
#include "util/vector.h"
#include "util/uint_set.h"
#include "util/stopwatch.h"
#include "util/symbol.h"
#include "util/sat_literal.h"

class params_ref;
class reslimit;
class statistics;

namespace sat {
#define SAT_VB_LVL 10


    typedef size_t clause_offset;
    typedef size_t ext_constraint_idx;
    typedef size_t ext_justification_idx;


    typedef approx_set_tpl<literal, literal2unsigned, unsigned> literal_approx_set;

    typedef approx_set_tpl<bool_var, u2u, unsigned> var_approx_set;

    class solver;
    class parallel;
    class lookahead;
    class unit_walk;
    class clause;
    class clause_wrapper;
    class integrity_checker;
    typedef ptr_vector<clause> clause_vector;

    class solver_exception : public default_exception {
    public:
        solver_exception(char const * msg):default_exception(msg) {}
    };

    typedef default_exception sat_param_exception;

    typedef svector<lbool> model;

    inline lbool value_at(bool_var v, model const & m) { return  m[v]; }
    inline lbool value_at(literal l, model const & m) { lbool r = value_at(l.var(), m); return l.sign() ? ~r : r; }

    inline std::ostream & operator<<(std::ostream & out, model const & m) {
        bool first = true;
        for (bool_var v = 0; v < m.size(); v++) {
            if (m[v] == l_undef) continue;
            if (first) first = false; else out << " ";
            if (m[v] == l_true) out << v; else out << "-" << v;
        }
        return out;
    }

    class i_local_search {
    public:
        virtual ~i_local_search() {}
        virtual void add(solver const& s) = 0;
        virtual void updt_params(params_ref const& p) = 0;
        virtual void set_seed(unsigned s) = 0;
        virtual lbool check(unsigned sz, literal const* assumptions, parallel* par) = 0;
        virtual void reinit(solver& s) = 0;        
        virtual unsigned num_non_binary_clauses() const = 0;
        virtual reslimit& rlimit() = 0;
        virtual model const& get_model() const = 0;
        virtual void collect_statistics(statistics& st) const = 0;        
        virtual double get_priority(bool_var v) const { return 0; }

    };

    class status {
    public:
        enum class st { input, asserted, redundant, deleted };
        st m_st;
        int m_orig;
    public:
        status(st s, int o) : m_st(s), m_orig(o) {};
        status(status const& s) : m_st(s.m_st), m_orig(s.m_orig) {}
        status(status&& s) noexcept { m_st = st::asserted; m_orig = -1; std::swap(m_st, s.m_st); std::swap(m_orig, s.m_orig); }
        status& operator=(status const& other) { m_st = other.m_st; m_orig = other.m_orig; return *this; }
        static status redundant() { return status(status::st::redundant, -1); }
        static status asserted() { return status(status::st::asserted, -1); }
        static status deleted() { return status(status::st::deleted, -1); }
        static status input() { return status(status::st::input, -1); }

        static status th(bool redundant, int id) { return status(redundant ? st::redundant : st::asserted, id); }

        bool is_input() const { return st::input == m_st; }
        bool is_redundant() const { return st::redundant == m_st; }
        bool is_asserted() const { return st::asserted == m_st; }
        bool is_deleted() const { return st::deleted == m_st; }

        bool is_sat() const { return -1 == m_orig; }
        int  get_th() const { return m_orig;  }
    };

    struct status_pp {
        status const& st;
        std::function<symbol(int)>& th;
        status_pp(status const& st, std::function<symbol(int)>& th) : st(st), th(th) {}
    };

    std::ostream& operator<<(std::ostream& out, sat::status const& st);
    std::ostream& operator<<(std::ostream& out, sat::status_pp const& p);

};



