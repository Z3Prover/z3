/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_solver.h

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
#include "sat/smt/q_ematch.h"

namespace euf {
    class solver;
}

namespace q {

    class solver : public euf::th_euf_solver {

        typedef obj_map<quantifier, quantifier*> flat_table;
        friend class mbqi;

        struct stats {
            unsigned m_num_quantifier_asserts;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        stats                  m_stats;
        mbqi                   m_mbqi;
        ematch                 m_ematch;

        flat_table             m_flat;
        sat::literal_vector    m_universal;
        obj_map<sort, expr*>   m_unit_table;
        expr_ref_vector        m_expanded;

        sat::literal instantiate(quantifier* q, bool negate, std::function<expr* (quantifier*, unsigned)>& mk_var);
        sat::literal skolemize(quantifier* q);
        sat::literal specialize(quantifier* q);
        void init_units();
        expr* get_unit(sort* s);
        
        expr_ref_vector const& expand(quantifier* q);

        friend class ematch;

    public:

        solver(euf::solver& ctx, family_id fid);
        ~solver() override {}
        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override;
        void asserted(sat::literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return display_constraint(out, idx); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override { internalize(e, false, false, redundant); }
        euf::theory_var mk_var(euf::enode* n) override;
        void init_search() override;
        void finalize_model(model& mdl) override;
        bool is_shared(euf::theory_var v) const override { return true; }

        ast_manager& get_manager() { return m; }
        sat::literal_vector const& universal() const { return m_universal; }
        quantifier* flatten(quantifier* q);

    };
}
