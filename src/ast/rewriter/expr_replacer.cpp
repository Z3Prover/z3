/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr_replacer.cpp

Abstract:

    Abstract (functor) for replacing constants with expressions.

Author:

    Leonardo (leonardo) 2011-04-29

Notes:

--*/
#include"expr_replacer.h"
#include"rewriter_def.h"
#include"th_rewriter.h"
#include"cooperate.h"

void expr_replacer::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    expr_dependency_ref result_dep(m());
    operator()(t, result, result_pr, result_dep);
}

void expr_replacer::operator()(expr * t, expr_ref & result) {
    proof_ref pr(m());
    operator()(t, result, pr);
}

struct expr_replacer::scoped_set_subst {
    expr_replacer & m_r;
    scoped_set_subst(expr_replacer & r, expr_substitution & s):m_r(r) { m_r.set_substitution(&s); }
    ~scoped_set_subst() { m_r.set_substitution(0); }
};

void expr_replacer::apply_substitution(expr * s, expr * def, proof * def_pr, expr_ref & t) { 
    expr_substitution sub(m()); 
    sub.insert(s, def, def_pr);
    scoped_set_subst set(*this, sub);
    (*this)(t);
}
    
void expr_replacer::apply_substitution(expr * s, expr * def, expr_ref & t) { 
    expr_substitution sub(m()); 
    sub.insert(s, def);
    scoped_set_subst set(*this, sub);
    (*this)(t);
}

struct default_expr_replacer_cfg : public default_rewriter_cfg  {
    ast_manager &        m;
    expr_substitution *  m_subst;
    expr_dependency_ref  m_used_dependencies;

    default_expr_replacer_cfg(ast_manager & _m):
        m(_m),
        m_subst(0),
        m_used_dependencies(_m) {
    }

    bool get_subst(expr * s, expr * & t, proof * & pr) { 
        if (m_subst == 0)
            return false;
        expr_dependency * d = 0;
        if (m_subst->find(s, t, pr, d)) {
            m_used_dependencies = m.mk_join(m_used_dependencies, d);
            return true;
        }
        return false;
    }

    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("simplifier");
        return false;
    }
};

template class rewriter_tpl<default_expr_replacer_cfg>;

class default_expr_replacer : public expr_replacer {
    default_expr_replacer_cfg               m_cfg;
    rewriter_tpl<default_expr_replacer_cfg> m_replacer;
public:
    default_expr_replacer(ast_manager & m):
        m_cfg(m),
        m_replacer(m, m.proofs_enabled(), m_cfg) {
    }
    
    virtual ast_manager & m() const { return m_replacer.m(); }

    virtual void set_substitution(expr_substitution * s) { 
        m_replacer.cleanup();
        m_replacer.cfg().m_subst = s;
    }
    
    virtual void operator()(expr * t, expr_ref & result, proof_ref & result_pr, expr_dependency_ref & result_dep) {
        result_dep = 0;
        m_replacer.operator()(t, result, result_pr);
        if (m_cfg.m_used_dependencies != 0) {
            result_dep = m_cfg.m_used_dependencies;
            m_replacer.reset(); // reset cache
            m_cfg.m_used_dependencies = 0;
        }
    }

    virtual void set_cancel(bool f) {
        m_replacer.set_cancel(f);
    }

    virtual unsigned get_num_steps() const {
        return m_replacer.get_num_steps();
    }

    virtual void reset() {
        m_replacer.reset();
    }
};

expr_replacer * mk_default_expr_replacer(ast_manager & m) {
    return alloc(default_expr_replacer, m);
}

/**
   \brief Adapter for using th_rewriter as an expr_replacer.
 */
class th_rewriter2expr_replacer : public expr_replacer {
    th_rewriter m_r;
public:
    th_rewriter2expr_replacer(ast_manager & m, params_ref const & p):
        m_r(m, p) {
    }

    virtual ~th_rewriter2expr_replacer() {}

    virtual ast_manager & m() const { return m_r.m(); }

    virtual void set_substitution(expr_substitution * s) { m_r.set_substitution(s); }

    virtual void operator()(expr * t, expr_ref & result, proof_ref & result_pr, expr_dependency_ref & result_dep) {
        m_r(t, result, result_pr);
        result_dep = m_r.get_used_dependencies();
        m_r.reset_used_dependencies();
    }

    virtual void set_cancel(bool f) {
        m_r.set_cancel(f);
    }

    virtual unsigned get_num_steps() const { 
        return m_r.get_num_steps();
    }

    virtual void reset() {
        m_r.reset();
    }

};

expr_replacer * mk_expr_simp_replacer(ast_manager & m, params_ref const & p) {
    return alloc(th_rewriter2expr_replacer, m, p);
}
