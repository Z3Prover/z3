/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include "sat/smt/polysat/constraints.h"

namespace polysat {

    /// Normalized inequality:
    ///     lhs <= rhs, if !is_strict
    ///     lhs < rhs, otherwise
    class inequality {
        core& c;
        constraint_id m_id;
        pdd m_lhs;
        pdd m_rhs;
        signed_constraint m_src;
        
        inequality(core& c, constraint_id id, pdd lhs, pdd rhs, signed_constraint src) :
            c(c), m_id(id), m_lhs(std::move(lhs)), m_rhs(std::move(rhs)), m_src(std::move(src)) {}

        void set(pdd& dst, pdd const& src) const {
            dst.reset(src.manager());
            dst = src;
        }

        // p := coeff*x*y where coeff_x = coeff*x, x a variable
        bool is_coeffxY(pdd const& x, pdd const& p, pdd& y) const { 
            pdd xy = x.manager().zero();
            return x.is_unary() && p.try_div(x.hi().val(), xy) && xy.factor(x.var(), 1, y);
        }
        
    public:
        static inequality from_ule(core& c, constraint_id id);
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
        bool is_strict() const { return m_src.is_negative(); }
        constraint_id id() const { return m_id; }
        dependency dep() const;
        signed_constraint as_signed_constraint() const { return m_src; }
        operator signed_constraint() const { return m_src; }

        // c := lhs ~ v
        //  where ~ is < or <=
        bool is_l_v(pvar v) const { return rhs() == c.var(v); }    
        static bool is_l_v(pdd const& v, signed_constraint const& sc);

        // c := v ~ rhs
        bool is_g_v(pvar v) const { return lhs() == c.var(v); }
        static bool is_g_v(pdd const& v, signed_constraint const& sc);

        // c := x ~ Y
        bool is_x_l_Y(pvar x, pdd& y) const { return is_g_v(x) && (set(y, rhs()), true); }
 
        // c := Y ~ x
        bool is_Y_l_x(pvar x, pdd& y) const { return is_l_v(x) && (set(y, lhs()), true); }

        // c := Y ~ Ax
        bool is_Y_l_Ax(pvar x, pdd& a, pdd& y) const { return is_xY(x, rhs(), a) && (set(y, lhs()), true); }
        bool verify_Y_l_Ax(pvar x, pdd const& a, pdd const& y) const { return lhs() == y && rhs() == a * c.var(x); }

        // c := X*y ~ X*Z
        bool is_Xy_l_XZ(pvar y, pdd& x, pdd& z) const { return is_xY(y, lhs(), x) && (false); }
        bool verify_Xy_l_XZ(pvar y, pdd const& x, pdd const& z) const { return lhs() == c.var(y) * x && rhs() == z * x; }

        // c := Ax ~ Y
        bool is_Ax_l_Y(pvar x,  pdd& a, pdd& y) const;
        bool verify_Ax_l_Y(pvar x, pdd const& a, pdd const& y) const;

        // c := Ax + B ~ Y
        bool is_AxB_l_Y(pvar x, pdd& a, pdd& b, pdd& y) const {
            return lhs().degree(x) == 1 && (set(y, rhs()), lhs().factor(x, 1, a, b), true);
        }
        bool verify_AxB_l_Y(pvar x, pdd const& a, pdd const& b, pdd const& y) const { return rhs() == y && lhs() == a * c.var(x) + b; }

        // c := Y ~ Ax + B
        bool is_Y_l_AxB(pvar x, pdd& y, pdd& a, pdd& b) const { return rhs().degree(x) == 1 && (set(y, lhs()), rhs().factor(x, 1, a, b), true); }
        bool verify_Y_l_AxB(pvar x,  pdd const& y, pdd const& a, pdd& b) const;

        // c := Ax + B ~ Y, val(Y) = 0
        bool is_AxB_eq_0(pvar x, pdd& a, pdd& b, pdd& y) const;
        bool verify_AxB_eq_0(pvar x, pdd const& a, pdd const& b, pdd const& y) const;

        // c := Ax + B != Y, val(Y) = 0
        bool is_AxB_diseq_0(pvar x, pdd& a, pdd& b, pdd& y) const;

        // c := Y*X ~ z*X
        bool is_YX_l_zX(pvar z, pdd& x, pdd& y) const { return is_xY(z, rhs(), x) && is_coeffxY(x, lhs(), y); }
        bool verify_YX_l_zX(pvar z, pdd const& x, pdd const& y) const;

        // c := xY <= xZ
        bool is_xY_l_xZ(pvar x, pdd& y, pdd& z) const { return is_xY_2(x, lhs(), y) && is_xY_2(x, rhs(), z); }

        /// Match xy = x * Y s.t. Y is free of x
        static bool is_xY(pvar x, pdd const& xy, pdd& y) { return xy.degree(x) == 1 && xy.factor(x, 1, y); }

        /// Match xy = x * Y
        static bool is_xY_2(pvar x, pdd const& xy, pdd& y) { return xy.factor(x, 1, y); }

        /**
         * Rewrite to one of six equivalent forms:
         *
         *      i=0     p <= q                  (unchanged)
         *      i=1     p <= p - q - 1
         *      i=2     q - p <= q
         *      i=3     q - p <= -p - 1
         *      i=4     -q - 1 <= -p - 1
         *      i=5     -q - 1 <= p - q - 1
         */
        //inequality rewrite_equiv(int i) const;

        //std::ostream& display(std::ostream& out) const;
    };


    struct bilinear {
        rational a, b, c, d;

        rational eval(rational const& x, rational const& y) const {
            return a*x*y + b*x + c*y + d;
        }

        bilinear operator-() const {
            bilinear r(*this);
            r.a = -r.a;
            r.b = -r.b;
            r.c = -r.c;
            r.d = -r.d;
            return r;
        }

        bilinear operator-(bilinear const& other) const {
            bilinear r(*this);
            r.a -= other.a;
            r.b -= other.b;
            r.c -= other.c;
            r.d -= other.d;
            return r;
        }

        bilinear operator+(rational const& d) const {
            bilinear r(*this);
            r.d += d;
            return r;
        }
        
        bilinear operator-(rational const& d) const {
            bilinear r(*this);
            r.d -= d;
            return r;
        }

        bilinear operator-(int d) const {
            bilinear r(*this);
            r.d -= d;
            return r;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, bilinear const& b) {
        return out << b.a << "*x*y + " << b.b << "*x + " << b.c << "*y + " << b.d;
    }
}
