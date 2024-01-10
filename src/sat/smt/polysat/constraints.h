/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/


#pragma once 
#include "util/trail.h"
#include "sat/smt/polysat/types.h"

namespace polysat {

    class core;
    class ule_constraint;
    class umul_ovfl_constraint;
    class op_constraint;

    class assignment;

    using pdd = dd::pdd;
    using pvar = unsigned;

    enum ckind_t { ule_t, umul_ovfl_t, smul_fl_t, op_t };

    class constraint {
        unsigned_vector     m_vars;
        unsigned            m_num_watch = 0;
    public:
        virtual ~constraint() {}
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned var(unsigned idx) const { return m_vars[idx]; }
        bool contains_var(pvar v) const { return m_vars.contains(v); }
        unsigned num_watch() const { return m_num_watch;  }
        void set_num_watch(unsigned n) { SASSERT(n <= 2);  m_num_watch = n; }
        virtual unsigned_vector const& unfold_vars() const { return m_vars; }
        virtual std::ostream& display(std::ostream& out, lbool status) const = 0;
        virtual std::ostream& display(std::ostream& out) const = 0;
        virtual lbool eval() const = 0;
        virtual lbool weak_eval(assignment const& a) const = 0;
        virtual lbool strong_eval(assignment const& a) const = 0;
        virtual void activate(core& c, bool sign, dependency const& d) = 0;
        virtual void propagate(core& c, lbool value, dependency const& d) = 0;
        virtual bool is_linear() const { return false; }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }


    class signed_constraint {
        bool m_sign = false;
        ckind_t m_op = ule_t;
        constraint* m_constraint = nullptr;
    public:
        signed_constraint() {}
        signed_constraint(ckind_t c, constraint* p) : m_op(c), m_constraint(p) {}
        signed_constraint operator~() const { signed_constraint r(*this); r.m_sign = !r.m_sign; return r; }
        bool sign() const { return m_sign; }
        bool is_positive() const { return !m_sign; }
        bool is_negative() const { return m_sign; }
        unsigned_vector& vars() { return m_constraint->vars(); }
        unsigned_vector const& vars() const { return m_constraint->vars(); }
        unsigned_vector const& unfold_vars() const { return m_constraint->unfold_vars(); }
        unsigned var(unsigned idx) const { return m_constraint->var(idx); }
        bool contains_var(pvar v) const { return m_constraint->contains_var(v); }
        unsigned num_watch() const { return m_constraint->num_watch(); }
        void set_num_watch(unsigned n) { m_constraint->set_num_watch(n); }
        void activate(core& c, dependency const& d) { m_constraint->activate(c, m_sign, d); }
        void propagate(core& c, lbool value, dependency const& d) { m_constraint->propagate(c, value, d); }
        bool is_always_true() const { return eval() == l_true; }
        bool is_always_false() const { return eval() == l_false; }
        bool is_linear() const { return m_constraint->is_linear(); }
        lbool weak_eval(assignment& a) const;
        lbool strong_eval(assignment& a) const;
        lbool eval() const { return m_sign ? ~m_constraint->eval() : m_constraint->eval();}
        ckind_t op() const { return m_op; }
        bool is_ule() const { return m_op == ule_t; }
        bool is_umul_ovfl() const { return m_op == umul_ovfl_t; }
        bool is_smul_fl() const { return m_op == smul_fl_t; }
        bool is_op() const { return m_op == op_t; }
        ule_constraint const& to_ule() const { SASSERT(is_ule()); return *reinterpret_cast<ule_constraint*>(m_constraint); }
        umul_ovfl_constraint const& to_umul_ovfl() const { SASSERT(is_umul_ovfl()); return *reinterpret_cast<umul_ovfl_constraint*>(m_constraint); }
        op_constraint const& to_op() const { SASSERT(is_op()); return *reinterpret_cast<op_constraint*>(m_constraint); }
        bool is_eq(pvar& v, rational& val);
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, signed_constraint const& c) { return c.display(out); }

    class constraints {
        core& c;
    public:
        constraints(core& c) : c(c) {}

        signed_constraint eq(pdd const& p) { return ule(p, p.manager().mk_val(0)); }
        signed_constraint eq(pdd const& p, rational const& v) { return eq(p - p.manager().mk_val(v)); }
        signed_constraint eq(pdd const& p, unsigned v) { return eq(p - p.manager().mk_val(v)); }
        signed_constraint eq(pdd const& p, pdd const& q) { return eq(p - q); }
        signed_constraint ule(pdd const& p, pdd const& q);
        signed_constraint sle(pdd const& p, pdd const& q) { auto sh = rational::power_of_two(p.power_of_2() - 1); return ule(p + sh, q + sh); }
        signed_constraint ult(pdd const& p, pdd const& q) { return ~ule(q, p); }
        signed_constraint slt(pdd const& p, pdd const& q) { return ~sle(q, p); }
        signed_constraint umul_ovfl(pdd const& p, pdd const& q);
        signed_constraint smul_ovfl(pdd const& p, pdd const& q) { throw default_exception("smul ovfl nyi"); }
        signed_constraint smul_udfl(pdd const& p, pdd const& q) { throw default_exception("smult-udfl nyi"); }
        signed_constraint bit(pdd const& p, unsigned i);

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
        signed_constraint uge(pdd const& p, int             q) { return ule(q, p); }

        signed_constraint ult(pdd const& p, rational const& q) { return ult(p, p.manager().mk_val(q)); }
        signed_constraint ult(rational const& p, pdd const& q) { return ult(q.manager().mk_val(p), q); }
        signed_constraint ult(int             p, pdd const& q) { return ult(rational(p), q); }
        signed_constraint ult(unsigned        p, pdd const& q) { return ult(rational(p), q); }
        signed_constraint ult(pdd const& p, int q) { return ult(p, rational(q)); }
        signed_constraint ult(pdd const& p, unsigned q) { return ult(p, rational(q)); }

        signed_constraint ugt(pdd const& p, pdd const& q) { return ult(q, p); }
        signed_constraint ugt(pdd const& p, rational const& q) { return ugt(p, p.manager().mk_val(q)); }
        signed_constraint ugt(rational const& p, pdd const& q) { return ugt(q.manager().mk_val(p), q); }
        signed_constraint ugt(int             p, pdd const& q) { return ugt(rational(p), q); }
        signed_constraint ugt(unsigned        p, pdd const& q) { return ugt(rational(p), q); }
        signed_constraint ugt(pdd const& p, int q) { return ugt(p, rational(q)); }
        signed_constraint ugt(pdd const& p, unsigned q) { return ugt(p, rational(q)); }

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

        signed_constraint sge(pdd const& p, pdd const& q) { return ~slt(q, p); }
        signed_constraint sge(pdd const& p, int q) { return ~slt(q, p); }

        signed_constraint umul_ovfl(pdd const& p, rational const& q) { return umul_ovfl(p, p.manager().mk_val(q)); }
        signed_constraint umul_ovfl(rational const& p, pdd const& q) { return umul_ovfl(q.manager().mk_val(p), q); }
        signed_constraint umul_ovfl(pdd const& p, int             q) { return umul_ovfl(p, rational(q)); }
        signed_constraint umul_ovfl(pdd const& p, unsigned        q) { return umul_ovfl(p, rational(q)); }
        signed_constraint umul_ovfl(int             p, pdd const& q) { return umul_ovfl(rational(p), q); }
        signed_constraint umul_ovfl(unsigned        p, pdd const& q) { return umul_ovfl(rational(p), q); }

        signed_constraint parity_at_least(pdd const& p, unsigned k);

        signed_constraint lshr(pdd const& a, pdd const& b, pdd const& r);
        signed_constraint ashr(pdd const& a, pdd const& b, pdd const& r);
        signed_constraint shl(pdd const& a, pdd const& b, pdd const& r);
        signed_constraint band(pdd const& a, pdd const& b, pdd const& r);
        signed_constraint bor(pdd const& a, pdd const& b, pdd const& r);

        //signed_constraint even(pdd const& p) { return parity_at_least(p, 1); }
        //signed_constraint odd(pdd const& p) { return ~even(p); }
    };
}
