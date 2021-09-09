/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/conflict_core.h"

namespace polysat {

    class solver;
    class constraint_manager;

    class inference_engine {
        friend class conflict_core;
        solver* m_solver = nullptr;
        void set_solver(solver& s) { m_solver = &s; }
    protected:
        solver& s() { return *m_solver; }
        constraint_manager& cm();
    public:
        virtual ~inference_engine() {}
        /** Try to apply an inference rule.
         *  Derive new constraints from constraints containing the variable v (i.e., at least one premise must contain v).
         *  Returns true if a new constraint was added to the core.
         */
        virtual bool perform(pvar v, conflict_core& core) = 0;
    };

    class inf_saturate : public inference_engine {
        bool find_upper_bound(pvar x, signed_constraint& c, rational& bound);

        void push_omega(clause_builder& reason, unsigned level, pdd const& x, pdd const& y);
        void push_omega_bisect(clause_builder& reason, unsigned level, pdd const& x, rational x_max, pdd const& y, rational y_max);
        signed_constraint ineq(unsigned level, bool strict, pdd const& lhs, pdd const& rhs);
        bool push_c(conflict_core& core, signed_constraint const& c, clause_builder& reason);
        bool push_l(conflict_core& core, unsigned level, bool strict, pdd const& lhs, pdd const& rhs, clause_builder& reason);

        bool try_ugt_x(pvar v, conflict_core& core, inequality const& c);

        bool try_ugt_y(pvar v, conflict_core& core, inequality const& c);
        bool try_ugt_y(pvar v, conflict_core& core, inequality const& l_y, inequality const& yx_l_zx, pdd const& x, pdd const& z);

        bool try_y_l_ax_and_x_l_z(pvar x, conflict_core& core, inequality const& c);
        bool try_y_l_ax_and_x_l_z(pvar x, conflict_core& core, inequality const& x_l_z, inequality const& y_l_ax, pdd const& a, pdd const& y);
            
        bool try_ugt_z(pvar z, conflict_core& core, inequality const& c);
        bool try_ugt_z(pvar z, conflict_core& core, inequality const& x_l_z0, inequality const& yz_l_xz, pdd const& y, pdd const& x);

        // c := lhs ~ v 
        //  where ~ is < or <=         
        bool is_l_v(pvar v, inequality const& c);

        // c := v ~ rhs
        bool is_g_v(pvar v, inequality const& c);

        // c := x ~ Y
        bool is_x_l_Y(pvar x, inequality const& c, pdd& y);

        // c := X*y ~ X*Z
        bool is_Xy_l_XZ(pvar y, inequality const& c, pdd& x, pdd& z);
        bool verify_Xy_l_XZ(pvar y, inequality const& c, pdd const& x, pdd const& z);

        // c := Y ~ Ax
        bool is_Y_l_Ax(pvar x, inequality const& d, pdd& a, pdd& y);
        bool verify_Y_l_Ax(pvar x, inequality const& d, pdd const& a, pdd const& y); 

        // c := Y*X ~ z*X
        bool is_YX_l_zX(pvar z, inequality const& c, pdd& x, pdd& y);
        bool verify_YX_l_zX(pvar z, inequality const& c, pdd const& x, pdd const& y); 

        // c := xY <= xZ
        bool is_xY_l_xZ(pvar x, inequality const& c, pdd& y, pdd& z);

        // xy := x * Y
        bool is_xY(pvar x, pdd const& xy, pdd& y);

        // a * b does not overflow
        bool is_non_overflow(pdd const& a, pdd const& b);

    public:

        bool perform(pvar v, conflict_core& core) override;
    };

    /*
     * TODO: we could resolve constraints in cjust[v] against each other to
     * obtain stronger propagation. Example:
     *  (x + 1)*P = 0 and (x + 1)*Q = 0, where gcd(P,Q) = 1, then we have x + 1 = 0.
     * We refer to this process as narrowing.
     * In general form it can rely on factoring.
     * Root finding can further prune viable.
     */

}
