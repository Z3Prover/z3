/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/


#pragma once 
#include "sat/smt/polysat_types.h"

namespace polysat {

    class core;

    using pdd = dd::pdd;
    using pvar = unsigned;

    enum ckind_t { ule_t, umul_ovfl_t, smul_fl_t, op_t };

    class constraint {
        unsigned_vector     m_vars;
    public:
        virtual ~constraint() {}
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned var(unsigned idx) const { return m_vars[idx]; }
        bool contains_var(pvar v) const { return m_vars.contains(v); }
    };

    class ule_constraint : public constraint {
        pdd m_lhs, m_rhs;
    public:
        ule_constraint(pdd const& lhs, pdd const& rhs) : m_lhs(lhs), m_rhs(rhs) {}
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
    };

    class umul_ovfl_constraint : public constraint {
        pdd m_lhs, m_rhs;
    public:
        umul_ovfl_constraint(pdd const& lhs, pdd const& rhs) : m_lhs(lhs), m_rhs(rhs) {}
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
    };

    class signed_constraint {
        bool m_sign = false;
        ckind_t m_op = ule_t;
        constraint* m_constraint = nullptr;
    public:
        signed_constraint() {}
        signed_constraint(ckind_t c, constraint* p) : m_op(c), m_constraint(p) {}
        signed_constraint operator~() const { signed_constraint r(*this); r.m_sign = !r.m_sign; return r; }
        bool sign() const { return m_sign; }
        unsigned_vector& vars() { return m_constraint->vars(); }
        unsigned_vector const& vars() const { return m_constraint->vars(); }
        unsigned var(unsigned idx) const { return m_constraint->var(idx); }
        bool contains_var(pvar v) const { return m_constraint->contains_var(v); }
        ckind_t op() const { return m_op; }
        bool is_ule() const { return m_op == ule_t; }
        bool is_umul_ovfl() const { return m_op == umul_ovfl_t; }
        bool is_smul_fl() const { return m_op == smul_fl_t; }
        ule_constraint const& to_ule() const { return *reinterpret_cast<ule_constraint*>(m_constraint); }
        umul_ovfl_constraint const& to_umul_ovfl() const { return *reinterpret_cast<umul_ovfl_constraint*>(m_constraint); }
        bool is_eq(pvar& v, rational& val) { throw default_exception("nyi"); }
    };

    using dependent_constraint = std::pair<signed_constraint, stacked_dependency*>;

    class constraints {
        trail_stack& m_trail;
    public:
        constraints(trail_stack& c) : m_trail(c) {}

        signed_constraint eq(pdd const& p) { return ule(p, p.manager().mk_val(0)); }
        signed_constraint eq(pdd const& p, rational const& v) { return eq(p - p.manager().mk_val(v)); }
        signed_constraint ule(pdd const& p, pdd const& q);
        signed_constraint sle(pdd const& p, pdd const& q) { throw default_exception("nyi"); }
        signed_constraint ult(pdd const& p, pdd const& q) { throw default_exception("nyi"); }
        signed_constraint slt(pdd const& p, pdd const& q) { throw default_exception("nyi"); }
        signed_constraint umul_ovfl(pdd const& p, pdd const& q) { throw default_exception("nyi"); }
        signed_constraint smul_ovfl(pdd const& p, pdd const& q) { throw default_exception("nyi"); }
        signed_constraint smul_udfl(pdd const& p, pdd const& q) { throw default_exception("nyi"); }
        signed_constraint bit(pdd const& p, unsigned i) { throw default_exception("nyi"); }

        signed_constraint diseq(pdd const& p) { return ~eq(p); }
        signed_constraint diseq(pdd const& p, pdd const& q) { return diseq(p - q); }
        signed_constraint diseq(pdd const& p, rational const& q) { return diseq(p - q); }
        signed_constraint diseq(pdd const& p, int             q) { return diseq(p, rational(q)); }
        signed_constraint diseq(pdd const& p, unsigned        q) { return diseq(p, rational(q)); }

        signed_constraint ule(pdd const& p, rational const& q) { return ule(p, p.manager().mk_val(q)); }
        signed_constraint ule(rational const& p, pdd const& q) { return ule(q.manager().mk_val(p), q); }
        signed_constraint ule(pdd const& p, int             q) { return ule(p, rational(q)); }
        signed_constraint ule(pdd const& p, unsigned        q) { return ule(p, rational(q)); }
        signed_constraint ule(int             p, pdd const& q) { return ule(rational(p), q); }
        signed_constraint ule(unsigned        p, pdd const& q) { return ule(rational(p), q); }

        signed_constraint uge(pdd const& p, pdd const& q) { return ule(q, p); }
        signed_constraint uge(pdd const& p, rational const& q) { return ule(q, p); }

        signed_constraint ult(pdd const& p, rational const& q) { return ult(p, p.manager().mk_val(q)); }
        signed_constraint ult(rational const& p, pdd const& q) { return ult(q.manager().mk_val(p), q); }
        signed_constraint ult(int             p, pdd const& q) { return ult(rational(p), q); }
        signed_constraint ult(unsigned        p, pdd const& q) { return ult(rational(p), q); }
        signed_constraint ult(pdd const& p, int q) { return ult(p, rational(q)); }
        signed_constraint ult(pdd const& p, unsigned q) { return ult(p, rational(q)); }

        signed_constraint slt(pdd const& p, rational const& q) { return slt(p, p.manager().mk_val(q)); }
        signed_constraint slt(rational const& p, pdd const& q) { return slt(q.manager().mk_val(p), q); }
        signed_constraint slt(pdd const& p, int             q) { return slt(p, rational(q)); }
        signed_constraint slt(pdd const& p, unsigned        q) { return slt(p, rational(q)); }
        signed_constraint slt(int             p, pdd const& q) { return slt(rational(p), q); }
        signed_constraint slt(unsigned        p, pdd const& q) { return slt(rational(p), q); }


        signed_constraint sgt(pdd const& p, pdd const& q) { return slt(q, p); }
        signed_constraint sgt(pdd const& p, int        q) { return slt(q, p); }
        signed_constraint sgt(pdd const& p, unsigned   q) { return slt(q, p); }
        signed_constraint sgt(int        p, pdd const& q) { return slt(q, p); }
        signed_constraint sgt(unsigned   p, pdd const& q) { return slt(q, p); }

        signed_constraint umul_ovfl(pdd const& p, rational const& q) { return umul_ovfl(p, p.manager().mk_val(q)); }
        signed_constraint umul_ovfl(rational const& p, pdd const& q) { return umul_ovfl(q.manager().mk_val(p), q); }
        signed_constraint umul_ovfl(pdd const& p, int             q) { return umul_ovfl(p, rational(q)); }
        signed_constraint umul_ovfl(pdd const& p, unsigned        q) { return umul_ovfl(p, rational(q)); }
        signed_constraint umul_ovfl(int             p, pdd const& q) { return umul_ovfl(rational(p), q); }
        signed_constraint umul_ovfl(unsigned        p, pdd const& q) { return umul_ovfl(rational(p), q); }


        //signed_constraint even(pdd const& p) { return parity_at_least(p, 1); }
        //signed_constraint odd(pdd const& p) { return ~even(p); }
    };
}