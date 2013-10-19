/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    aig_exporter.h

Abstract:

    Export AIG files from horn clauses

--*/

#ifndef _AIG_EXPORTER_H_
#define _AIG_EXPORTER_H_

#include "aig.h"
#include "dl_rule_set.h"
#include <map>
#include <sstream>
#include "rel_context.h"

namespace datalog {
    class aig_exporter {
    public:
        aig_exporter(const rule_set& rules, context& ctx, const fact_vector *facts = 0);
        void operator()(std::ostream& out);

    private:
        typedef obj_map<func_decl, unsigned> decl_id_map;
        typedef obj_map<const expr, unsigned> aig_expr_id_map;
        typedef std::map<std::pair<unsigned,unsigned>, unsigned> and_gates_map;

        const rule_set&    m_rules;
        const fact_vector *m_facts;
        ast_manager&       m;
        rule_manager&      m_rm;
        aig_manager        m_aigm;
        decl_id_map        m_decl_id_map;
        unsigned           m_next_decl_id;
        aig_expr_id_map    m_aig_expr_id_map;
        unsigned           m_next_aig_expr_id;
        and_gates_map      m_and_gates_map;
        unsigned           m_num_and_gates;

        expr_ref_vector m_latch_vars, m_latch_varsp;
        expr_ref_vector m_ruleid_var_set, m_ruleid_varp_set;
        unsigned_vector m_input_vars;

        std::stringstream m_buffer;

        void mk_latch_vars(unsigned n);
        expr* get_latch_var(unsigned i, const expr_ref_vector& vars);
        void assert_pred_id(func_decl *decl, const expr_ref_vector& vars, expr_ref_vector& exprs);
        void collect_var_substs(substitution& subst, const app *h,
            const expr_ref_vector& vars, expr_ref_vector& eqs);
        unsigned expr_to_aig(const expr *e);
        unsigned neg(unsigned id) const;
        unsigned mk_and(unsigned id1, unsigned id2);
        unsigned mk_or(unsigned id1, unsigned id2);
        unsigned get_var(const expr *e);
        unsigned mk_var(const expr *e);
        unsigned mk_input_var(const expr *e = 0);
        unsigned mk_expr_id();
    };
}

#endif
