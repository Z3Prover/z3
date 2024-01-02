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
        };
        vector<monomial>   m_monomials;
        pdd_vector         m_tmp;
        
        struct mon_eq {
            monomials& m;
            mon_eq(monomials& m):m(m) {}
            bool operator()(unsigned i, unsigned j) const {
                auto const& a = m.m_monomials[i].args;
                auto const& b = m.m_monomials[j].args;
                return a == b;
            };
        };

        struct pdd_hash {
            typedef pdd data_t;
            unsigned operator()(pdd const& p) const { return p.hash(); }
        };
        struct mon_hash {
            monomials& m;
            mon_hash(monomials& m):m(m) {}
            unsigned operator()(unsigned i) const {
                auto const& a = m.m_monomials[i].args;
                return vector_hash<pdd_hash>()(a);
            }
        };
        mon_hash m_hash;
        mon_eq   m_eq;
        hashtable<unsigned, mon_hash, mon_eq> m_table;

        unsigned_vector m_to_refine;
        void init_to_refine();
        bool eval_to_false(unsigned i);

        bool mul0(monomial const& mon);
        bool mul1(monomial const& mon);
        bool mulp2(monomial const& mon);
        bool mul(monomial const& mon, std::function<bool(rational const&)> const& p);
        bool parity(monomial const& mon);
        bool non_overflow_monotone(monomial const& mon);
        bool non_overflow_unit(monomial const& mon);
        bool non_overflow_zero(monomial const& mon);
        bool parity0(monomial const& mon);
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
