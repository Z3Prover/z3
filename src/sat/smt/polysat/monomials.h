/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat monomials

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include "math/dd/dd_pdd.h"
#include "sat/smt/polysat/types.h"

namespace polysat {

    class core;
    class constraints;

    using pdd_vector = vector<pdd>;
    using rational_vector = vector<rational>;
    
    class monomials {
        core& c;
        constraints& C;

        struct monomial {
            pdd_vector args;
            pdd        var;
            pdd        def;
            rational_vector arg_vals;
            rational   val;
            unsigned size() const { return args.size(); }
            unsigned num_bits() const { return args[0].manager().power_of_2(); }
            std::ostream& display(std::ostream& out) const;
        };
        vector<monomial>   m_monomials;
        pdd_vector         m_tmp;
        

        unsigned_vector m_to_refine;
        void init_to_refine();
        bool eval_to_false(unsigned i);

        bool mul0(monomial const& mon);
        bool mul1(monomial const& mon);
        bool mulp2(monomial const& mon);
        bool mul_parametric_inverse(monomial const& mon);
        bool mul(monomial const& mon, std::function<bool(rational const&)> const& p);
        bool parity(monomial const& mon);
        bool non_overflow_monotone(monomial const& mon);
        bool mul1_inverse(monomial const& mon);
        bool mul0_inverse(monomial const& mon);
        bool prefix_overflow(monomial const& mon);

        bool bit_blast(monomial const& mon);
        
    public:

        monomials(core& c);

        pvar mk(unsigned n, pdd const* args);

        pdd subst(pdd const& p);
        
        lbool refine();

        lbool bit_blast();

        std::ostream& display(std::ostream& out) const;
               
    };


    inline std::ostream& operator<<(std::ostream& out, monomials const& m) {
        return m.display(out);
    }
}
