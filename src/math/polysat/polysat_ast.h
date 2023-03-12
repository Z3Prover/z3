/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat to ast conversion

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/types.h"

class expr;
class ast_manager;
class bv_util;

namespace polysat {

    struct polysat_ast_d;
    class signed_constraint;

    class polysat_ast {
        solver& s;
        scoped_ptr<polysat_ast_d> d;
        std::string m_description;
        lbool m_status = l_undef;
        bool m_ok = true;

        ast_manager& m() const;
        bv_util& bv() const;

    public:
        polysat_ast(solver&);
        ~polysat_ast();

        void set_description(std::string description) { m_description = description; }
        void set_status(lbool status) { m_status = status; }
        bool is_ok() { return m_ok; }

        expr* mk_val(rational const& val, unsigned bit_width);
        expr* mk_var(pvar x);
        expr* mk_mono(dd::pdd_monomial const& mono, unsigned bit_width);
        expr* mk_poly(pdd const& p);

        // p <= q
        expr* mk_ule(pdd const& p, pdd const& q);
        expr* mk_ule(pdd const& p, pdd const& q, bool sign);
        // p >= q
        expr* mk_uge(pdd const& p, pdd const& q, bool sign) { return mk_ule(q, p, sign); }
        // p > q
        expr* mk_ugt(pdd const& p, pdd const& q, bool sign) { return mk_ule(p, q, !sign); }
        // p < q
        expr* mk_ult(pdd const& p, pdd const& q, bool sign) { return mk_ugt(q, p, sign); }

        // ovfl*(p, q)
        expr* mk_umul_ovfl(pdd const& p, pdd const& q, bool sign);

        expr* mk_not(expr* e);

        expr* mk_lit(sat::literal lit);
        expr* mk_lit(signed_constraint c);

        expr* mk_clause(clause& cl);

        void add(expr* e);

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, polysat_ast const& x) { return x.display(out); }

}
