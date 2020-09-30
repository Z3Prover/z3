/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    a_solver.h

Abstract:

    Quantifier solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/
#pragma once

#include "util/obj_hashtable.h"
#include "ast/ast_trail.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/q_mbi.h"

namespace euf {
    class solver;
}

namespace q {

    class solver : public euf::th_euf_solver {

        typedef obj_map<quantifier, sat::literal> skolem_table;
        friend class mbqi;

        struct stats {
            unsigned m_num_inst;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        stats                  m_stats;
        mbqi                   m_mbqi;

        skolem_table           m_skolems;
        sat::literal_vector    m_universal;

        sat::literal skolemize(quantifier* q);
        sat::literal uskolemize(quantifier* q);

    public:

        solver(euf::solver& ctx);
        ~solver() override {}
        static char const* name() { return "quant"; }
        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override {}
        void asserted(sat::literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { UNREACHABLE(); return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { UNREACHABLE(); return out; }
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(sat::solver* s, euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override { UNREACHABLE(); }
        euf::theory_var mk_var(euf::enode* n) override;
        void init_search() override;

        ast_manager& get_manager() { return m; }
    };
}
