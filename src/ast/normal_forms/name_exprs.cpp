/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    name_exprs.h

Abstract:

    Goodies for naming nested expressions.

Author:

    Leonardo (leonardo) 2011-10-06

Notes:

--*/
#include "ast/normal_forms/name_exprs.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_smt2_pp.h"

class name_exprs_core : public name_exprs {
    struct cfg : public default_rewriter_cfg {
        ast_manager &           m;
        defined_names &         m_defined_names;
        expr_predicate &        m_pred;
        
        app_ref                 m_r;
        proof_ref               m_pr;

        expr_ref_vector *       m_def_exprs;
        proof_ref_vector *      m_def_proofs;

        cfg(ast_manager & m, defined_names & n, expr_predicate & pred):
            m(m),
            m_defined_names(n),
            m_pred(pred),
            m_r(m),
            m_pr(m),
            m_def_exprs(nullptr),
            m_def_proofs(nullptr) {
        }

        void gen_name_for_expr(expr * n, expr * & t, proof * & t_pr) {
            expr_ref  new_def(m);
            proof_ref new_def_pr(m);
            
            if (m_defined_names.mk_name(n, new_def, new_def_pr, m_r, m_pr)) {
                m_def_exprs->push_back(new_def);
                if (m.proofs_enabled())
                    m_def_proofs->push_back(new_def_pr);
            }

            t    = m_r.get();
            t_pr = m_pr.get();
        }

        bool get_subst(expr * s, expr * & t, proof * & t_pr) {
            TRACE("name_exprs", tout << "get_subst:\n" << mk_ismt2_pp(s, m) << "\n";);
            if (m_pred(s)) {
                gen_name_for_expr(s, t, t_pr);
                return true;
            }
            return false;
        }
    };

    typedef rewriter_tpl<cfg> rw;
    
    cfg                      m_cfg;
    rw                       m_rw;

public:
    name_exprs_core(ast_manager & m, defined_names & n, expr_predicate & pred):
        m_cfg(m, n, pred),
        m_rw(m, m.proofs_enabled(), m_cfg) {
    }

    ~name_exprs_core() override {
    }

    void operator()(expr * n, expr_ref_vector & new_defs, proof_ref_vector & new_def_proofs, expr_ref & r, proof_ref & p) override {
        m_cfg.m_def_exprs  = &new_defs;
        m_cfg.m_def_proofs = &new_def_proofs;
        m_rw(n, r, p);
        TRACE("name_exprs", tout << mk_ismt2_pp(n, m_rw.m()) << "\n---->\n" << r << "\n";);
    }
    

    void reset() override {
        m_rw.reset();
    }
};

name_exprs * mk_expr_namer(ast_manager & m, defined_names & n, expr_predicate & pred) {
    return alloc(name_exprs_core, m, n, pred);
}

class name_quantifier_labels : public name_exprs_core {
    class pred : public expr_predicate {
        ast_manager & m;
    public:
        pred(ast_manager & m):m(m) {}
        bool operator()(expr * t) override {
            return is_quantifier(t) || m.is_label(t);
        }
    };
    
    pred m_pred;
public:
    name_quantifier_labels(ast_manager & m, defined_names & n):
        name_exprs_core(m, n, m_pred),
        m_pred(m) {
    }

    ~name_quantifier_labels() override {
    }
};

name_exprs * mk_quantifier_label_namer(ast_manager & m, defined_names & n) {
    return alloc(name_quantifier_labels, m, n);
}

class name_nested_formulas : public name_exprs_core {
    struct pred : public expr_predicate {
        ast_manager & m;
        expr *        m_root;

        pred(ast_manager & m):m(m), m_root(nullptr) {}

        bool operator()(expr * t) override {
            TRACE("name_exprs", tout << "name_nested_formulas::pred:\n" << mk_ismt2_pp(t, m) << "\n";);
            if (is_app(t)) 
                return to_app(t)->get_family_id() == m.get_basic_family_id() && to_app(t)->get_num_args() > 0 && t != m_root;
            return m.is_label(t) || is_quantifier(t);
        }
    };
    
    pred m_pred;

public:
    name_nested_formulas(ast_manager & m, defined_names & n):
        name_exprs_core(m, n, m_pred),
        m_pred(m) {
    }

    ~name_nested_formulas() override {
    }

    void operator()(expr * n, expr_ref_vector & new_defs, proof_ref_vector & new_def_proofs, expr_ref & r, proof_ref & p) override {
        m_pred.m_root = n;
        TRACE("name_exprs", tout << "operator()\n";);
        name_exprs_core::operator()(n, new_defs, new_def_proofs, r, p);
    }
};

name_exprs * mk_nested_formula_namer(ast_manager & m, defined_names & n) {
    return alloc(name_nested_formulas, m, n);
}

void del_name_exprs(name_exprs * functor) {
    dealloc(functor);
}
