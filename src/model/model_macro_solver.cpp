/*++
Copyright (c) 2006 Microsoft Corporation

Abstract:

    Macro solving utilities

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

--*/

#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "model/model_macro_solver.h"
#include "model/model_core.h"

void base_macro_solver::set_else_interp(func_decl* f, expr* f_else) {
    SASSERT(f_else != nullptr);
    func_interp* fi = m_model->get_func_interp(f);
    if (fi == nullptr) {
        fi = alloc(func_interp, m, f->get_arity());
        m_model->register_decl(f, fi);
    }
    fi->set_else(f_else);
    TRACE("model_finder", tout << f->get_name() << " " << mk_pp(f_else, m) << "\n";);
}

void base_macro_solver::operator()(model_core& m, ptr_vector<quantifier>& qs, ptr_vector<quantifier>& residue) {
    m_model = &m;
    ptr_vector<quantifier> curr_qs(qs), new_qs;
    while (process(curr_qs, new_qs, residue)) {
        curr_qs.swap(new_qs);
        new_qs.reset();
    }
    std::swap(qs, new_qs);
}

/**
   \brief Return true if \c f is in (qs\{q})
*/
bool simple_macro_solver::contains(func_decl* f, ptr_vector<quantifier> const& qs, quantifier* q) {
    for (quantifier* other : qs) {
        if (q == other)
            continue;
        quantifier_macro_info* other_qi = get_qinfo(other);
        if (other_qi->contains_ng_decl(f))
            return true;
    }
    return false;
}

bool simple_macro_solver::process(quantifier* q, ptr_vector<quantifier> const& qs) {
    quantifier_macro_info* qi = get_qinfo(q);
    for (cond_macro* m : qi->macros()) {
        if (!m->satisfy_atom())
            continue;
        func_decl* f = m->get_f();
        if (!contains(f, qs, q)) {
            qi->set_the_one(f);
            expr* f_else = m->get_def();
            SASSERT(f_else != nullptr);
            // Remark: I can ignore the conditions of m because
            // I know the (partial) interpretation of f satisfied the ground part.
            // MBQI will force extra instantiations if the (partial) interpretation of f
            // does not satisfy the quantifier.
            // In all other cases the "else" of f will satisfy the quantifier.
            set_else_interp(f, f_else);
            TRACE("model_finder", tout << "satisfying the quantifier using simple macro:\n";
            m->display(tout); tout << "\n";);
            return true; // satisfied quantifier
        }
    }
    return false;
}

bool simple_macro_solver::process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) {
    bool removed = false;
    for (quantifier* q : qs) {
        if (process(q, qs))
            removed = true;
        else
            new_qs.push_back(q);
    }
    return removed;
}



void hint_macro_solver::insert_q_f(quantifier* q, func_decl* f) {
    SASSERT(!m_forbidden.contains(f));
    quantifier_set* s = nullptr;
    if (!m_q_f.find(f, s)) {
        s = alloc(quantifier_set);
        m_q_f.insert(f, s);
        m_qsets.push_back(s);
    }
    SASSERT(s != nullptr);
    s->insert(q);
}

void hint_macro_solver::insert_f2def(func_decl* f, expr* def) {
    expr_set* s = nullptr;
    if (!m_f2defs.find(f, s)) {
        s = alloc(expr_set);
        m_f2defs.insert(f, s);
        m_esets.push_back(s);
    }
    SASSERT(s != nullptr);
    s->insert(def);
}

void hint_macro_solver::insert_q_f_def(quantifier* q, func_decl* f, expr* def) {
    SASSERT(!m_forbidden.contains(f));
    quantifier_set* s = nullptr;
    if (!m_q_f_def.find(f, def, s)) {
        s = alloc(quantifier_set);
        m_q_f_def.insert(f, def, s);
        insert_f2def(f, def);
        m_qsets.push_back(s);
    }
    SASSERT(s != nullptr);
    s->insert(q);
}


hint_macro_solver::quantifier_set* hint_macro_solver::get_q_f_def(func_decl* f, expr* def) {
    quantifier_set* s = nullptr;
    m_q_f_def.find(f, def, s);
    SASSERT(s != nullptr);
    return s;
}


void hint_macro_solver::reset_q_fs() {
    std::for_each(m_qsets.begin(), m_qsets.end(), delete_proc<quantifier_set>());
    std::for_each(m_esets.begin(), m_esets.end(), delete_proc<expr_set>());
    m_q_f.reset();
    m_q_f_def.reset();
    m_qsets.reset();
    m_f2defs.reset();
    m_esets.reset();
}


bool hint_macro_solver::is_candidate(quantifier* q) const {
    quantifier_macro_info* qi = get_qinfo(q);
    for (cond_macro* m : qi->macros()) {
        if (m->satisfy_atom() && !m_forbidden.contains(m->get_f()))
            return true;
    }
    return false;
}

void hint_macro_solver::register_decls_as_forbidden(quantifier* q) {
    quantifier_macro_info* qi = get_qinfo(q);
    func_decl_set const& ng_decls = qi->get_ng_decls();
    for (func_decl* f : ng_decls) {
        m_forbidden.insert(f);
    }
}

void hint_macro_solver::preprocess(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& qcandidates, ptr_vector<quantifier>& non_qcandidates) {
    ptr_vector<quantifier> curr(qs);
    while (true) {
        for (quantifier* q : curr) {
            if (is_candidate(q)) {
                qcandidates.push_back(q);
            }
            else {
                register_decls_as_forbidden(q);
                non_qcandidates.push_back(q);
            }
        }
        if (curr.size() == qcandidates.size())
            return;
        SASSERT(qcandidates.size() < curr.size());
        curr.swap(qcandidates);
        qcandidates.reset();
    }
}

void hint_macro_solver::mk_q_f_defs(ptr_vector<quantifier> const& qs) {
    for (quantifier* q : qs) {
        quantifier_macro_info* qi = get_qinfo(q);
        func_decl_set const& ng_decls = qi->get_ng_decls();
        for (func_decl* f : ng_decls) {
            if (!m_forbidden.contains(f))
                insert_q_f(q, f);
        }
        for (cond_macro* m : qi->macros()) {
            if (m->satisfy_atom() && !m_forbidden.contains(m->get_f())) {
                insert_q_f_def(q, m->get_f(), m->get_def());
                m_candidates.insert(m->get_f());
            }
        }
    }
}

void hint_macro_solver::display_quantifier_set(std::ostream& out, quantifier_set const* s) {
    for (quantifier* q : *s) {
        out << q->get_qid() << " ";
    }
    out << "\n";
}

void hint_macro_solver::display_qcandidates(std::ostream& out, ptr_vector<quantifier> const& qcandidates) const {
    for (quantifier* q : qcandidates) {
        out << q->get_qid() << " ->\n" << mk_pp(q, m) << "\n";
        quantifier_macro_info* qi = get_qinfo(q);
        qi->display(out);
        out << "------\n";
    }
    out << "Sets Q_f\n";
    for (auto const& kv : m_q_f) {
        func_decl* f = kv.m_key;
        quantifier_set* s = kv.m_value;
        out << f->get_name() << " -> "; display_quantifier_set(out, s);
    }
    out << "Sets Q_{f = def}\n";
    for (auto const& kv : m_q_f_def) {
        func_decl* f = kv.get_key1();
        expr* def = kv.get_key2();
        quantifier_set* s = kv.get_value();
        out << f->get_name() << " " << mk_pp(def, m) << " ->\n"; display_quantifier_set(out, s);
    }
}


void hint_macro_solver::display_search_state(std::ostream& out) const {
    out << "fs:\n";
    for (auto const& kv : m_fs) {
        out << kv.m_key->get_name() << " ";
    }
    out << "\nsatisfied:\n";
    for (auto q : m_satisfied) {
        out << q->get_qid() << " ";
    }
    out << "\nresidue:\n";
    for (auto q : m_residue) {
        out << q->get_qid() << " ";
    }
    out << "\n";
}

bool hint_macro_solver::check_satisfied_residue_invariant() {
    DEBUG_CODE(
        for (quantifier* q : m_satisfied) {
            SASSERT(!m_residue.contains(q));
            auto* qi = get_qinfo(q);
            SASSERT(qi != nullptr);
            SASSERT(qi->get_the_one() != nullptr);
        });
    return true;
}


bool hint_macro_solver::update_satisfied_residue(func_decl* f, expr* def) {
    bool useful = false;
    SASSERT(check_satisfied_residue_invariant());
    quantifier_set* q_f = get_q_f(f);
    quantifier_set* q_f_def = get_q_f_def(f, def);
    for (quantifier* q : *q_f_def) {
        if (!m_satisfied.contains(q)) {
            useful = true;
            m_residue.erase(q);
            m_satisfied.insert(q);
            quantifier_macro_info* qi = get_qinfo(q);
            SASSERT(qi->get_the_one() == 0);
            qi->set_the_one(f); // remark... event handler will reset it during backtracking.
        }
    }
    if (!useful)
        return false;
    for (quantifier* q : *q_f) {
        if (!m_satisfied.contains(q)) {
            m_residue.insert(q);
        }
    }
    SASSERT(check_satisfied_residue_invariant());
    return true;
}

/**
   \brief Extract from m_residue, func_decls that can be used as macros to satisfy it.
   The candidates must not be elements of m_fs.
*/
void hint_macro_solver::get_candidates_from_residue(func_decl_set& candidates) {
    for (quantifier* q : m_residue) {
        quantifier_macro_info* qi = get_qinfo(q);
        for (cond_macro* m : qi->macros()) {
            func_decl* f = m->get_f();
            if (m->satisfy_atom() && !m_forbidden.contains(f) && !m_fs.contains(f)) {
                candidates.insert(f);
            }
        }
    }
}

#define GREEDY_MAX_DEPTH 10 /* to avoid too expensive search spaces */

/**
  \brief Try to reduce m_residue using the macros of f.
*/
void hint_macro_solver::greedy(func_decl* f, unsigned depth) {
    if (depth >= GREEDY_MAX_DEPTH)
        return; // failed

    TRACE("model_finder_hint",
        tout << "greedy depth: " << depth << ", f: " << f->get_name() << "\n";
    display_search_state(tout););

    expr_set* s = get_f_defs(f);
    for (expr* def : *s) {

        SASSERT(!m_fs.contains(f));

        m_satisfied.push_scope();
        m_residue.push_scope();
        TRACE("model_finder", tout << f->get_name() << " " << mk_pp(def, m) << "\n";);
        m_fs.insert(f, def);

        if (update_satisfied_residue(f, def)) {
            // update was useful
            greedy(depth + 1); // greedy throws exception in case of success
            // reachable iff greedy failed.
        }

        m_satisfied.pop_scope();
        m_residue.pop_scope();
        m_fs.erase(f);
    }
}

/**
   \brief check if satisfied subset introduces a cyclic dependency.

   f_1 = def_1(f_2), ..., f_n = def_n(f_1)
 */

bool hint_macro_solver::is_cyclic() {
    m_acyclic.reset();
    while (true) {
        unsigned sz = m_acyclic.size();
        if (sz == m_fs.size()) return false; // there are no cyclic dependencies
        for (auto const& kv : m_fs) {
            func_decl* f = kv.m_key;
            if (m_acyclic.contains(f)) continue;
            if (is_acyclic(kv.m_value))
                m_acyclic.insert(f);
        }
        if (sz == m_acyclic.size()) return true; // no progress, so dependency cycle found.                    
    }
}

bool hint_macro_solver::is_acyclic(expr* def) {
    m_visited.reset();
    occurs_check oc(*this);
    try {
        for_each_expr(oc, m_visited, def);
    }
    catch (const occurs&) {
        return false;
    }
    return true;
}

/**
   \brief Try to reduce m_residue (if not empty) by selecting a function f
   that is a macro in the residue.
*/
void hint_macro_solver::greedy(unsigned depth) {
    if (m_residue.empty()) {
        if (is_cyclic()) return;
        TRACE("model_finder_hint",
            tout << "found subset that is satisfied by macros\n";
        display_search_state(tout););
        throw found_satisfied_subset();
    }
    func_decl_set candidates;
    get_candidates_from_residue(candidates);

    TRACE("model_finder_hint", tout << "candidates from residue:\n";
    for (func_decl* f : candidates) {
        tout << f->get_name() << " ";
    }
    tout << "\n";);

    for (func_decl* f : candidates) {
        greedy(f, depth);
    }
}

/**
   \brief Try to find a set of quantifiers by starting to use the macros of f.
   This is the "find" procedure in the comments above.
   The set of satisfied quantifiers is in m_satisfied, and the remaining to be
   satisfied in m_residue. When the residue becomes empty we throw the exception found_satisfied_subset.
*/
void hint_macro_solver::process(func_decl* f) {
    SASSERT(m_satisfied.empty());
    SASSERT(m_residue.empty());
    greedy(f, 0);
}

/**
   \brief Copy the quantifiers from qcandidates to new_qs that are not in m_satisfied.
*/
void hint_macro_solver::copy_non_satisfied(ptr_vector<quantifier> const& qcandidates, ptr_vector<quantifier>& new_qs) {
    for (quantifier* q : qcandidates) {
        if (!m_satisfied.contains(q))
            new_qs.push_back(q);
    }
}

/**
   \brief Use m_fs to set the interpretation of the function symbols that were used to satisfy the
   quantifiers in m_satisfied.
*/
void hint_macro_solver::set_interp() {
    for (auto const& kv : m_fs) {
        func_decl* f = kv.m_key;
        expr* def = kv.m_value;
        set_else_interp(f, def);
    }
}

void hint_macro_solver::reset() {
    reset_q_fs();
    m_forbidden.reset();
    m_candidates.reset();
    m_satisfied.reset();
    m_residue.reset();
    m_fs.reset();
}

bool hint_macro_solver::process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) {
    reset();
    ptr_vector<quantifier> qcandidates;
    preprocess(qs, qcandidates, new_qs);
    if (qcandidates.empty()) {
        SASSERT(new_qs.size() == qs.size());
        return false;
    }
    mk_q_f_defs(qcandidates);
    TRACE("model_finder_hint", tout << "starting hint-solver search using:\n"; display_qcandidates(tout, qcandidates););
    for (func_decl* f : m_candidates) {
        try {
            process(f);
        }
        catch (const found_satisfied_subset&) {
            set_interp();
            copy_non_satisfied(qcandidates, new_qs);
            return true;
        }
    }
    // failed... copy everything to new_qs
    new_qs.append(qcandidates);
    return false;
}

/**
\brief Satisfy clauses that are not in the AUF fragment but define conditional macros.
These clauses are eliminated even if the symbol being defined occurs in other quantifiers.
The auf_solver is ineffective in these clauses.

\remark Full macros are used even if they are in the AUF fragment.
*/

bool non_auf_macro_solver::add_macro(func_decl* f, expr* f_else) {
    TRACE("model_finder", tout << "trying to add macro for " << f->get_name() << "\n" << mk_pp(f_else, m) << "\n";);
    func_decl_set* s = m_dependencies.mk_func_decl_set();
    m_dependencies.collect_ng_func_decls(f_else, s);
    if (!m_dependencies.insert(f, s)) {
        TRACE("model_finder", tout << "failed to add macro\n";);
        return false; // cyclic dependency
    }
    set_else_interp(f, f_else);
    return true;
}

// Return true if r1 is a better macro than r2.
bool non_auf_macro_solver::is_better_macro(cond_macro* r1, cond_macro* r2) {
    if (r2 == nullptr || !r1->is_hint())
        return true;
    if (!r2->is_hint())
        return false;
    SASSERT(r1->is_hint() && r2->is_hint());
    if (is_ground(r1->get_def()) && !is_ground(r2->get_def()))
        return true;
    return false;
}

cond_macro* non_auf_macro_solver::get_macro_for(func_decl* f, quantifier* q) {
    cond_macro* r = nullptr;
    quantifier_macro_info* qi = get_qinfo(q);
    for (cond_macro* m : qi->macros()) {
        if (m->get_f() == f && !m->is_hint() && is_better_macro(m, r))
            r = m;
    }
    return r;
}

typedef std::pair<cond_macro*, quantifier*> mq_pair;

void non_auf_macro_solver::collect_candidates(ptr_vector<quantifier> const& qs, obj_map<func_decl, mq_pair>& full_macros, func_decl_set& cond_macros) {
    for (quantifier* q : qs) {
        quantifier_macro_info* qi = get_qinfo(q);
        for (cond_macro* m : qi->macros()) {
            if (!m->is_hint()) {
                func_decl* f = m->get_f();
                TRACE("model_finder", tout << "considering macro for: " << f->get_name() << "\n";
                m->display(tout); tout << "\n";);
                if (m->is_unconditional() && (!qi->is_auf() || m->get_weight() >= m_mbqi_force_template)) {
                    full_macros.insert(f, std::make_pair(m, q));
                    cond_macros.erase(f);
                }
                else if (!full_macros.contains(f) && !qi->is_auf())
                    cond_macros.insert(f);
            }
        }
    }
}

void non_auf_macro_solver::process_full_macros(obj_map<func_decl, mq_pair> const& full_macros, obj_hashtable<quantifier>& removed) {
    for (auto const& kv : full_macros) {
        func_decl* f = kv.m_key;
        cond_macro* m = kv.m_value.first;
        quantifier* q = kv.m_value.second;
        SASSERT(m->is_unconditional());
        if (add_macro(f, m->get_def())) {
            get_qinfo(q)->set_the_one(f);
            removed.insert(q);
        }
    }
}

void non_auf_macro_solver::process(func_decl* f, ptr_vector<quantifier> const& qs, obj_hashtable<quantifier>& removed) {
    expr_ref fi_else(m);
    ptr_buffer<quantifier> to_remove;
    for (quantifier* q : qs) {
        if (removed.contains(q))
            continue;
        cond_macro* cm = get_macro_for(f, q);
        if (!cm)
            continue;
        SASSERT(!cm->is_hint());
        if (cm->is_unconditional())
            return; // f is part of a full macro... ignoring it.
        to_remove.push_back(q);
        if (fi_else.get() == nullptr) {
            fi_else = cm->get_def();
        }
        else {
            fi_else = m.mk_ite(cm->get_cond(), cm->get_def(), fi_else);
        }
    }
    if (fi_else.get() != nullptr && add_macro(f, fi_else)) {
        for (quantifier* q : to_remove) {
            get_qinfo(q)->set_the_one(f);
            removed.insert(q);
        }
    }
}

void non_auf_macro_solver::process_cond_macros(func_decl_set const& cond_macros, ptr_vector<quantifier> const& qs, obj_hashtable<quantifier>& removed) {
    for (func_decl* f : cond_macros) {
        process(f, qs, removed);
    }
}

bool non_auf_macro_solver::process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) {
    obj_map<func_decl, mq_pair> full_macros;
    func_decl_set cond_macros;
    obj_hashtable<quantifier> removed;

    // Possible improvement: sort full_macros & cond_macros using an user provided precedence function.

    collect_candidates(qs, full_macros, cond_macros);
    process_full_macros(full_macros, removed);
    process_cond_macros(cond_macros, qs, removed);

    for (quantifier* q : qs) {
        if (removed.contains(q))
            continue;
        new_qs.push_back(q);
        residue.push_back(q);
    }
    return !removed.empty();
}


