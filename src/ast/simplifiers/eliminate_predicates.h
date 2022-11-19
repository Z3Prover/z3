/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    eliminate_predicates.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

Notes:

 Eliminate predicates through Davis-Putnam rules
 
 (forall (x y) (or (P x) Q)) (forall (x y) (or (not (P x)) R))
is converted to 
 (forall (x y) (or Q R))
when P occurs only in positive or only in negative polarities and the
expansion does not increase the formula size.

Macros are also eliminated


create clause abstractions, index into fmls, indicator if it was removed
map from predicates to clauses where they occur in unitary role.
process predicates to check if they can be eliminated, creating new clauses and updated use-list.


--*/


#pragma once

#include "util/scoped_ptr_vector.h"
#include "ast/rewriter/der.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/simplifiers/dependent_expr_state.h"


class eliminate_predicates : public dependent_expr_simplifier {

public:
    struct clause {
        ptr_vector<sort>                  m_bound;                // bound variables
        vector<std::pair<expr_ref, bool>> m_literals;             // clause literals
        expr_dependency_ref               m_dep;                  // dependencies
        expr_ref                          m_fml;                  // formula corresponding to clause
        unsigned                          m_fml_index = UINT_MAX; // index of formula where clause came from
        bool                              m_alive = true;
        
        clause(ast_manager& m, expr_dependency* d) :
            m_dep(d, m), m_fml(m)
        {}

        std::ostream& display(std::ostream& out) const;
    };
private:
    struct stats {
        unsigned m_num_eliminated = 0;
        unsigned m_num_macros = 0;
        void reset() { m_num_eliminated = 0; m_num_macros = 0; }
    };

    struct macro_def {
        app_ref m_head;
        expr_ref m_def;
        expr_dependency_ref m_dep;
        macro_def(app_ref& head, expr_ref& def, expr_dependency_ref& dep) :
            m_head(head), m_def(def), m_dep(dep) {}
    };

    typedef ptr_vector<clause> clause_use_list;

    class use_list {
        vector<clause_use_list> m_use_list;
        unsigned index(func_decl* f, bool sign) const { return 2*f->get_small_id() + sign; }
        void reserve(func_decl* f, bool sign) {
            m_use_list.reserve(index(f, sign) + 3);
        }
    public:
        clause_use_list& get(func_decl* f, bool sign) { reserve(f, sign);  return m_use_list[index(f, sign)]; }
        void reset() { m_use_list.reset(); }
    };

    scoped_ptr_vector<clause>    m_clauses;
    ast_mark              m_disable_elimination, m_disable_macro, m_predicate_decls, m_is_macro;
    ptr_vector<func_decl> m_predicates;
    ptr_vector<expr>      m_to_exclude;
    stats                 m_stats;
    use_list              m_use_list;
    der_rewriter          m_der;
    th_rewriter           m_rewriter;
    obj_map<func_decl, macro_def*> m_macros;

    struct macro_expander_cfg;
    struct macro_expander_rw;
    
    void rewrite(expr_ref& t);

    clause* init_clause(unsigned i);
    clause* init_clause(expr* f, expr_dependency* d, unsigned i);
    clause* resolve(func_decl* p, clause& pos, clause& neg);
    void add_use_list(clause& cl);

    bool try_find_binary_definition(func_decl* p, app_ref& head, expr_ref& def, expr_dependency_ref& dep);
    void try_resolve_definition(func_decl* p);
    void insert_macro(app_ref& head, expr_ref& def, expr_dependency_ref& dep);
    bool has_macro(func_decl* p, app_ref& head, expr_ref& def, expr_dependency_ref& dep);
    bool is_macro_safe(expr* e);

    void try_resolve(func_decl* p);
    void update_model(func_decl* p);
    expr_ref create_residue_formula(func_decl* p, clause& cl);
    void process_to_exclude(ast_mark&);

    void init_clauses();
    void find_definitions();
    void reduce_definitions();
    void try_resolve();
    void decompile();
    void reset();
    
public:

    eliminate_predicates(ast_manager& m, dependent_expr_state& fmls);

    ~eliminate_predicates() override { reset(); }
    
    void reduce() override;

    void collect_statistics(statistics& st) const override { 
        st.update("elim-predicates", m_stats.m_num_eliminated); 
        st.update("elim-predicates-macros", m_stats.m_num_macros);
    }

    void reset_statistics() override { m_stats.reset(); }
};


inline std::ostream& operator<<(std::ostream& out, eliminate_predicates::clause const& c) {
    return c.display(out);
}