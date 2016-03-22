/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qsat.h

Abstract:

    Quantifier Satisfiability Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#ifndef QE_QSAT_H__
#define QE_QSAT_H__

#include "tactic.h"
#include "filter_model_converter.h"

namespace qe {

    struct max_level {
        unsigned m_ex, m_fa;
        max_level(): m_ex(UINT_MAX), m_fa(UINT_MAX) {}
        void merge(max_level const& other) {
            merge(m_ex, other.m_ex);
            merge(m_fa, other.m_fa);
        }
        static unsigned max(unsigned a, unsigned b) {
            if (a == UINT_MAX) return b;
            if (b == UINT_MAX) return a;
            return std::max(a, b);
        }
        unsigned max() const {
            return max(m_ex, m_fa);
        }
        void merge(unsigned& lvl, unsigned other) {
            lvl = max(lvl, other);
        }
        std::ostream& display(std::ostream& out) const {
            if (m_ex != UINT_MAX) out << "e" << m_ex << " ";
            if (m_fa != UINT_MAX) out << "a" << m_fa << " ";
            return out;
        }
        
        bool operator==(max_level const& other) const {
            return 
                m_ex == other.m_ex &&
                m_fa == other.m_fa;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, max_level const& lvl) {
        return lvl.display(out);
    }

    class pred_abs {
        ast_manager&            m;
        vector<app_ref_vector>  m_preds;
        expr_ref_vector         m_asms;
        unsigned_vector         m_asms_lim;
        obj_map<expr, expr*>    m_pred2lit;    // maintain definitions of predicates.
        obj_map<expr, app*>     m_lit2pred;    // maintain reverse mapping to predicates
        obj_map<expr, app*>     m_asm2pred;    // maintain map from assumptions to predicates
        obj_map<expr, expr*>    m_pred2asm;    // predicates |-> assumptions
        expr_ref_vector         m_trail;
        filter_model_converter_ref m_fmc;
        ptr_vector<expr>        todo;
        obj_map<expr, max_level>      m_elevel;
        obj_map<func_decl, max_level> m_flevel;

        template <typename T>
        void dec_keys(obj_map<expr, T*>& map) {
            typename obj_map<expr, T*>::iterator it = map.begin(), end = map.end();
            for (; it != end; ++it) {
                m.dec_ref(it->m_key);
            }
        }
        void add_lit(app* p, app* lit);
        void add_asm(app* p, expr* lit);        
        bool is_predicate(app* a, unsigned l);
        void mk_concrete(expr_ref_vector& fmls, obj_map<expr, expr*> const& map);
    public:
        
        pred_abs(ast_manager& m);
        filter_model_converter* fmc();
        void reset();
        max_level compute_level(app* e);
        void push();
        void pop(unsigned num_scopes);
        void insert(app* a, max_level const& lvl);
        void get_assumptions(model* mdl, expr_ref_vector& asms);
        void set_expr_level(app* v, max_level const& lvl);
        void set_decl_level(func_decl* v, max_level const& lvl);
        void abstract_atoms(expr* fml, max_level& level, expr_ref_vector& defs);
        void abstract_atoms(expr* fml, expr_ref_vector& defs);
        expr_ref mk_abstract(expr* fml);
        void pred2lit(expr_ref_vector& fmls);
        expr_ref pred2asm(expr* fml);
        void get_free_vars(expr* fml, app_ref_vector& vars);
        expr_ref mk_assumption_literal(expr* a, model* mdl, max_level const& lvl, expr_ref_vector& defs);
        void add_pred(app* p, app* lit);
        app_ref fresh_bool(char const* name);
        void display(std::ostream& out) const;
        void display(std::ostream& out, expr_ref_vector const& asms) const;
        void collect_statistics(statistics& st) const;
    };


}

tactic * mk_qsat_tactic(ast_manager & m, params_ref const& p = params_ref());

tactic * mk_qe2_tactic(ast_manager & m, params_ref const& p = params_ref());

tactic * mk_qe_rec_tactic(ast_manager & m, params_ref const& p = params_ref());


/*
  ADD_TACTIC("qsat", "apply a QSAT solver.", "mk_qsat_tactic(m, p)") 

  ADD_TACTIC("qe2", "apply a QSAT based quantifier elimination.", "mk_qe2_tactic(m, p)") 

  ADD_TACTIC("qe_rec", "apply a QSAT based quantifier elimination recursively.", "mk_qe_rec_tactic(m, p)") 

*/

#endif 
