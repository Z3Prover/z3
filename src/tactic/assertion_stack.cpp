/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    assertion_stack.cpp

Abstract:
    
    Assertion stacks
    
Author:

    Leonardo de Moura (leonardo) 2012-02-17

Revision History:

--*/
#include"assertion_stack.h"
#include"well_sorted.h"
#include"ast_smt2_pp.h"
#include"ref_util.h"
#include"expr_replacer.h"
#include"model.h"
#include"expr_substitution.h"

struct assertion_stack::imp {
    ast_manager &                m_manager;
    bool                         m_models_enabled;  // model generation is enabled.
    bool                         m_proofs_enabled;  // proof production is enabled. m_manager.proofs_enabled() must be true if m_proofs_enabled == true
    bool                         m_core_enabled;    // unsat core extraction is enabled.
    bool                         m_inconsistent; 
    ptr_vector<expr>             m_forms;
    ptr_vector<proof>            m_proofs;
    ptr_vector<expr_dependency>  m_deps;
    unsigned                     m_form_qhead; // position of first uncommitted assertion
    unsigned                     m_mc_qhead;

    // Set of declarations that can't be eliminated
    obj_hashtable<func_decl>     m_forbidden_set;
    func_decl_ref_vector         m_forbidden;
    
    // Limited model converter support, it supports only extensions and filters.
    // It should be viewed as combination of extension_model_converter and 
    // filter_model_converter for goals.
    expr_substitution            m_csubst;  // substitution for eliminated constants

    // Model converter is just two sequences: func_decl and tag.
    // Tag 0 (extension) func_decl was eliminated, and its definition is in m_vsubst or m_fsubst.
    // Tag 1 (filter) func_decl was introduced by tactic, and must be removed from model.
    ptr_vector<func_decl>        m_mc;      
    char_vector                  m_mc_tag;
    
    struct scope {
        unsigned                 m_forms_lim;
        unsigned                 m_forbidden_lim;
        unsigned                 m_mc_lim;
        bool                     m_inconsistent_old;
    };
    
    svector<scope>               m_scopes;

    imp(ast_manager & m, bool models_enabled, bool core_enabled):
        m_manager(m),
        m_forbidden(m),
        m_csubst(m, core_enabled) {
        init(m.proofs_enabled(), models_enabled, core_enabled);
    }

    imp(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
        m_manager(m),
        m_forbidden(m),
        m_csubst(m, core_enabled, proofs_enabled) {
        init(proofs_enabled, models_enabled, core_enabled);
    }

    void init(bool proofs_enabled, bool models_enabled, bool core_enabled) {
        m_models_enabled = models_enabled;
        m_proofs_enabled = proofs_enabled;
        m_core_enabled   = core_enabled;
        m_inconsistent   = false;
        m_form_qhead     = 0;
    }

    ~imp() {
        reset();
    }

    ast_manager & m() const { return m_manager; }

    bool models_enabled() const { return m_models_enabled; }

    bool proofs_enabled() const { return m_proofs_enabled; }

    bool unsat_core_enabled() const { return m_core_enabled; }

    bool inconsistent() const { return m_inconsistent; }

    unsigned size() const { return m_forms.size(); }

    unsigned qhead() const { return m_form_qhead; }

    expr * form(unsigned i) const { return m_forms[i];  }

    proof * pr(unsigned i) const { 
        if (proofs_enabled())
            return m_proofs[i];
        else
            return 0;
    }

    expr_dependency * dep(unsigned i) const { 
        if (unsat_core_enabled())
            return m_deps[i];
        else
            return 0;
    }

    void reset() {
        m_inconsistent = false;
        m_form_qhead   = 0;
        m_mc_qhead     = 0;
        dec_ref_collection_values(m_manager, m_forms);
        dec_ref_collection_values(m_manager, m_proofs);
        dec_ref_collection_values(m_manager, m_deps);
        dec_ref_collection_values(m_manager, m_forbidden);
        m_forbidden_set.reset();
        dec_ref_collection_values(m_manager, m_mc);
        m_mc_tag.reset();
        m_csubst.reset();
        m_scopes.reset();
    }
    
    void expand(expr * f, proof * pr, expr_dependency * dep, expr_ref & new_f, proof_ref & new_pr, expr_dependency_ref & new_dep) {
        scoped_ptr<expr_replacer> r = mk_default_expr_replacer(m());
        (*r)(f, new_f, new_pr, new_dep);
        // new_pr   is a proof for  f == new_f
        // new_dep  are the dependencies for showing f == new_f
        if (proofs_enabled()) {
            new_pr = m_manager.mk_modus_ponens(pr, new_pr); 
        }
        if (unsat_core_enabled()) {
            new_dep = m().mk_join(dep, new_dep);
        }
    }
    
    void push_back(expr * f, proof * pr, expr_dependency * d) {
        if (m().is_true(f))
            return;
        if (m().is_false(f)) {
            m_inconsistent = true;
        }
        else {
            SASSERT(!m_inconsistent);
        }
        m().inc_ref(f);
        m_forms.push_back(f);
        if (proofs_enabled()) {
            m().inc_ref(pr);
            m_proofs.push_back(pr);
        }
        if (unsat_core_enabled()) {
            m().inc_ref(d);
            m_deps.push_back(d);
        }
    }

    void quick_process(bool save_first, expr * & f, expr_dependency * d) {
        if (!m().is_and(f) && !(m().is_not(f) && m().is_or(to_app(f)->get_arg(0)))) {
            if (!save_first) {
                push_back(f, 0, d);
            }
            return; 
        }
        typedef std::pair<expr *, bool> expr_pol;
        sbuffer<expr_pol, 64> todo;
        todo.push_back(expr_pol(f, true));
        while (!todo.empty()) {
            if (m_inconsistent)
                return;
            expr_pol p  = todo.back();
            expr * curr = p.first;
            bool   pol  = p.second;
            todo.pop_back();
            if (pol && m().is_and(curr)) {
                app * t = to_app(curr);
                unsigned i = t->get_num_args();
                while (i > 0) {
                    --i;
                    todo.push_back(expr_pol(t->get_arg(i), true));
                }
            }
            else if (!pol && m().is_or(curr)) {
                app * t = to_app(curr);
                unsigned i = t->get_num_args();
                while (i > 0) {
                    --i;
                    todo.push_back(expr_pol(t->get_arg(i), false));
                }
            }
            else if (m().is_not(curr)) {
                todo.push_back(expr_pol(to_app(curr)->get_arg(0), !pol));
            }
            else {
                if (!pol) 
                    curr = m().mk_not(curr);
                if (save_first) {
                    f  = curr;
                    save_first = false;
                }
                else {
                    push_back(curr, 0, d);
                }
            }
        }
    }
    
    void process_and(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
        unsigned num = f->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            if (m_inconsistent)
                return;
            slow_process(save_first && i == 0, f->get_arg(i), m().mk_and_elim(pr, i), d, out_f, out_pr);
        }
    }
    
    void process_not_or(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
        unsigned num = f->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            if (m_inconsistent)
                return;
            expr * child = f->get_arg(i);
            if (m().is_not(child)) {
                expr * not_child = to_app(child)->get_arg(0);
                slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), d, out_f, out_pr);
            }
            else {
                expr_ref not_child(m());
                not_child = m().mk_not(child);
                slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), d, out_f, out_pr);
            }
        }
    }
    
    void slow_process(bool save_first, expr * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
        if (m().is_and(f)) 
            process_and(save_first, to_app(f), pr, d, out_f, out_pr);
        else if (m().is_not(f) && m().is_or(to_app(f)->get_arg(0))) 
            process_not_or(save_first, to_app(to_app(f)->get_arg(0)), pr, d, out_f, out_pr);
        else if (save_first) {
            out_f  = f;
            out_pr = pr;
        }
        else {
            push_back(f, pr, d);
        }
    }
    
    void slow_process(expr * f, proof * pr, expr_dependency * d) {
        expr_ref out_f(m());
        proof_ref out_pr(m());
        slow_process(false, f, pr, d, out_f, out_pr);
    }
    
    void assert_expr(expr * f, proof * pr, expr_dependency * d) {
        SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
        if (m_inconsistent)
            return;
        expr_ref new_f(m()); proof_ref new_pr(m()); expr_dependency_ref new_d(m());
        expand(f, pr, d, new_f, new_pr, new_d);
        if (proofs_enabled())
            slow_process(f, pr, d);
        else
            quick_process(false, f, d);
    }
    
    void update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
        SASSERT(i >= m_form_qhead);
        SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
        if (m_inconsistent)
            return;
        if (proofs_enabled()) {
            expr_ref out_f(m());
            proof_ref out_pr(m());
            slow_process(true, f, pr, d, out_f, out_pr);
            if (!m_inconsistent) {
                if (m().is_false(out_f)) {
                    push_back(out_f, out_pr, d);
                }
                else {
                    m().inc_ref(out_f);
                    m().dec_ref(m_forms[i]);
                    m_forms[i] = out_f;
                    
                    m().inc_ref(out_pr);
                    m().dec_ref(m_proofs[i]);
                    m_proofs[i] = out_pr;
                    
                    if (unsat_core_enabled()) {
                        m().inc_ref(d);
                        m().dec_ref(m_deps[i]);
                        m_deps[i] = d;
                    }
                }
            }
        }
        else {
            quick_process(true, f, d);
            if (!m_inconsistent) {
                if (m().is_false(f)) {
                    push_back(f, 0, d);
                }
                else {
                    m().inc_ref(f);
                    m().dec_ref(m_forms[i]);
                    m_forms[i] = f;
                    
                    if (unsat_core_enabled()) {
                        m().inc_ref(d);
                        m().dec_ref(m_deps[i]);
                        m_deps[i] = d;
                    }
                }
            }
        }
    }
    
    void expand_and_update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
        SASSERT(i >= m_form_qhead);
        SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
        if (m_inconsistent)
            return;
        expr_ref new_f(m()); proof_ref new_pr(m()); expr_dependency_ref new_d(m());
        expand(f, pr, d, new_f, new_pr, new_d);
        update(i, new_f, new_pr, new_d);
    }
    
    void push() {
        commit();
        m_scopes.push_back(scope());
        scope & s            = m_scopes.back();
        s.m_forms_lim        = m_forms.size();
        s.m_forbidden_lim    = m_forbidden.size();
        s.m_mc_lim           = m_mc.size();
        s.m_inconsistent_old = m_inconsistent;
    }
    
    void pop(unsigned num_scopes) {
    }
    
    void commit() {
    }

    unsigned scope_lvl() const { 
        return m_scopes.size(); 
    }

    bool is_forbidden(func_decl * f) const { 
        return m_forbidden_set.contains(f); 
    }
    
#define MC_TAG_EXTENSION 0
#define MC_TAG_FILTER    1
    
    void add_filter(func_decl * f) {
        m().inc_ref(f);
        m_mc.push_back(f);
        m_mc_tag.push_back(MC_TAG_FILTER);
    }
    
    void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
        SASSERT(c->get_num_args() == 0);
        SASSERT(!m_csubst.contains(c));
        m_csubst.insert(c, def, pr, dep);
        func_decl * d = c->get_decl();
        m().inc_ref(d);
        m_mc.push_back(d);
        m_mc_tag.push_back(MC_TAG_EXTENSION);
    }

    void convert(model_ref & m) {
    }
    
    void display(std::ostream & out) const {
        out << "(assertion-stack";
        unsigned sz = size();
        for (unsigned i = 0; i < sz; i++) {
            out << "\n  ";
            if (i == m_form_qhead) 
                out << "==>\n";
            out << mk_ismt2_pp(form(i), m(), 2);
        }
        out << ")" << std::endl;
    }

    bool is_well_sorted() const {
        unsigned sz = size();
        for (unsigned i = 0; i < sz; i++) {
            expr * t = form(i);
            if (!::is_well_sorted(m(), t))
                return false;
        }
        return true;
    }
};

assertion_stack::assertion_stack(ast_manager & m, bool models_enabled, bool core_enabled) {
    m_imp = alloc(imp, m, models_enabled, core_enabled);
}

assertion_stack::assertion_stack(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled) {
    m_imp = alloc(imp, m, proofs_enabled, models_enabled, core_enabled);
}

assertion_stack::~assertion_stack() {
    dealloc(m_imp);
}

void assertion_stack::reset() {
    m_imp->reset();
}

ast_manager & assertion_stack::m() const { 
    return m_imp->m(); 
}

bool assertion_stack::models_enabled() const { 
    return m_imp->models_enabled();
}

bool assertion_stack::proofs_enabled() const { 
    return m_imp->proofs_enabled(); 
}

bool assertion_stack::unsat_core_enabled() const { 
    return m_imp->unsat_core_enabled(); 
}

bool assertion_stack::inconsistent() const { 
    return m_imp->inconsistent(); 
}

unsigned assertion_stack::size() const { 
    return m_imp->size();
}

unsigned assertion_stack::qhead() const { 
    return m_imp->qhead();
}

expr * assertion_stack::form(unsigned i) const { 
    return m_imp->form(i);
}

proof * assertion_stack::pr(unsigned i) const { 
    return m_imp->pr(i);
}

expr_dependency * assertion_stack::dep(unsigned i) const { 
    return m_imp->dep(i);
}

void assertion_stack::assert_expr(expr * f, proof * pr, expr_dependency * d) {
    return m_imp->assert_expr(f, pr, d);
}

void assertion_stack::assert_expr(expr * f) {
    assert_expr(f, proofs_enabled() ? m().mk_asserted(f) : 0, 0);
}

void assertion_stack::update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    m_imp->update(i, f, pr, d);
}

void assertion_stack::expand_and_update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    m_imp->expand_and_update(i, f, pr, d);
}

void assertion_stack::commit() {
    m_imp->commit();
}

void assertion_stack::push() {
    m_imp->push();
}

void assertion_stack::pop(unsigned num_scopes) {
    m_imp->pop(num_scopes);
}

unsigned assertion_stack::scope_lvl() const {
    return m_imp->scope_lvl();
}
  
bool assertion_stack::is_well_sorted() const {
    return m_imp->is_well_sorted();
}


bool assertion_stack::is_forbidden(func_decl * f) const {
    return m_imp->is_forbidden(f);
}

void assertion_stack::add_filter(func_decl * f) {
    m_imp->add_filter(f);
}

void assertion_stack::add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
    m_imp->add_definition(c, def, pr, dep);
}

void assertion_stack::convert(model_ref & m) {
    m_imp->convert(m);
}

void assertion_stack::display(std::ostream & out) const {
    m_imp->display(out);
}
