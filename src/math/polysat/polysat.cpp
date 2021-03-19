/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/polysat.h"

namespace polysat {

    std::ostream& poly::display(std::ostream& out) const {
        return out;
    }

    std::ostream& constraint::display(std::ostream& out) const {
        return out;
    }
    
    std::ostream& linear::display(std::ostream& out) const {
        return out;
    }

    std::ostream& mono::display(std::ostream& out) const {
        return out;
    }

    unsigned solver::poly2size(poly const& p) const {
        return 0;
    }

    bool solver::is_viable(unsigned var, rational const& val) const {
        return false;
    }

    /*
        struct del_var;
        struct del_constraint;
        struct var_unassign;

        void push();
        void pop(unsigned n);

        solver(trail_stack& s);
        ~solver() {}

        lbool check_sat();
        
        unsigned add_var(unsigned sz);

        poly var(unsigned v);
        poly mul(rational cons& r, poly const& p);
        poly num(rational const& r, unsigned sz);
        poly add(poly const& p, poly const& q);

        vector<mono> poly2monos(poly const& p) const;        

        void add_eq(poly const& p, unsigned dep);
        void add_diseq(poly const& p, unsigned dep);
        void add_ule(poly const& p, poly const& q, unsigned dep);
        void add_sle(poly const& p, poly const& q, unsigned dep);
        void assign(unsigned var, unsigned index, bool value, unsigned dep);        

        bool  can_propagate();
        lbool propagate();

        bool can_decide();
        void decide(rational & val, unsigned& var);
        void assign(unsigned var, rational const& val);
        
        bool is_conflict();
        unsigned resolve_conflict(unsigned_vector& deps);            
        
        bool can_learn();
        void learn(constraint& c, unsigned_vector& deps); 
        void learn(vector<constraint>& cs, unsigned_vector& deps); 

        std::ostream& display(std::ostream& out) const;

        */

}


