/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pattern_inference.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-12-08.

Revision History:

--*/

#include "util/warning.h"
#include "ast/pattern/pattern_inference.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/normal_forms/pull_quant.h"
#include "ast/well_sorted.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter_def.h"

void smaller_pattern::save(expr * p1, expr * p2) {
    expr_pair e(p1, p2);
    if (!m_cache.contains(e)) {
        TRACE("smaller_pattern_proc", tout << "saving: " << p1->get_id() << " " << p2->get_id() << "\n";);
        m_cache.insert(e);
        m_todo.push_back(e);
    }
}

bool smaller_pattern::process(expr * p1, expr * p2) {
    m_todo.reset();
    m_cache.reset();
    save(p1, p2);
    while (!m_todo.empty()) {
        expr_pair & curr = m_todo.back();
        p1 = curr.first;
        p2 = curr.second;
        m_todo.pop_back();
        ast_kind k1 = p1->get_kind();
        if (k1 != AST_VAR && k1 != p2->get_kind())
            return false;
        switch (k1) {
        case AST_APP: {
            app * app1 = to_app(p1);
            app * app2 = to_app(p2);
            unsigned num1  = app1->get_num_args();
            if (num1 != app2->get_num_args() || app1->get_decl() != app2->get_decl())
                return false;
            for (unsigned i = 0; i < num1; i++)
                save(app1->get_arg(i), app2->get_arg(i));
            break;
        }
        case AST_VAR: {
            unsigned idx = to_var(p1)->get_idx();
            if (idx < m_bindings.size()) {
                if (m_bindings[idx] == 0)
                    m_bindings[idx] = p2;
                else if (m_bindings[idx] != p2)
                    return false;
            }
            // it is a variable bound by an external quantifier
            else if (p1 != p2)
                return false;
            break;
        }
        default:
            if (p1 != p2)
                return false;
            break;
        }
    }
    return true;
}

bool smaller_pattern::operator()(unsigned num_bindings, expr * p1, expr * p2) {
    m_bindings.resize(num_bindings);
    for (unsigned i = 0; i < num_bindings; i++)
        m_bindings[i] = 0;
    return process(p1, p2);
}


#ifdef _TRACE
static void dump_app_vector(std::ostream & out, ptr_vector<app> const & v, ast_manager & m) {
    for (app * e : v) 
        out << mk_pp(e, m) << "\n";
}
#endif


#include "ast/pattern/database.h"


pattern_inference_cfg::pattern_inference_cfg(ast_manager & m, pattern_inference_params const & params):
    m(m),
    m_params(params),
    m_bfid(m.get_basic_family_id()),
    m_afid(m.mk_family_id("arith")),
    m_le(m),
    m_nested_arith_only(true),
    m_block_loop_patterns(params.m_pi_block_loop_patterns),
    m_candidates(m),
    m_pattern_weight_lt(m_candidates_info),
    m_collect(m, *this),
    m_contains_subpattern(*this),
    m_database(m) {
    if (params.m_pi_arith == AP_NO)
        register_forbidden_family(m_afid);
}

void pattern_inference_cfg::collect::operator()(expr * n, unsigned num_bindings) {
    SASSERT(m_info.empty());
    SASSERT(m_todo.empty());
    SASSERT(m_cache.empty());
    m_num_bindings = num_bindings;
    m_todo.push_back(entry(n, 0));
    while (!m_todo.empty()) {
        entry & e      = m_todo.back();
        n              = e.m_node;
        unsigned delta = e.m_delta;
        TRACE("collect", tout << "processing: " << n->get_id() << " " << delta << " kind: " << n->get_kind() << "\n";);
        TRACE("collect_info", tout << mk_pp(n, m) << "\n";);
        if (visit_children(n, delta)) {
            m_todo.pop_back();
            save_candidate(n, delta);
        }
    }
    reset();
}

inline void pattern_inference_cfg::collect::visit(expr * n, unsigned delta, bool & visited) {
    entry e(n, delta);
    if (!m_cache.contains(e)) {
        m_todo.push_back(e);
        visited = false;
    }
}

bool pattern_inference_cfg::collect::visit_children(expr * n, unsigned delta) {
    bool visited = true;
    unsigned i;
    switch (n->get_kind()) {
    case AST_APP:
        i = to_app(n)->get_num_args();
        while (i > 0) {
            --i;
            visit(to_app(n)->get_arg(i), delta, visited);
        }
        break;
    case AST_QUANTIFIER:
        visit(to_quantifier(n)->get_expr(), delta + to_quantifier(n)->get_num_decls(), visited);
        break;
    default:
        break;
    }
    return visited;
}

inline void pattern_inference_cfg::collect::save(expr * n, unsigned delta, info * i) {
    m_cache.insert(entry(n, delta), i);
    if (i != nullptr)
        m_info.push_back(i);
}

void pattern_inference_cfg::collect::save_candidate(expr * n, unsigned delta) {
    switch (n->get_kind()) {
    case AST_VAR: {
        unsigned idx = to_var(n)->get_idx();
        if (idx >= delta) {
            idx = idx - delta;
            uint_set free_vars;
            if (idx < m_num_bindings)
                free_vars.insert(idx);
            info * i = nullptr;
            if (delta == 0)
                i = alloc(info, m, n, free_vars, 1);
            else
                i = alloc(info, m, m.mk_var(idx, to_var(n)->get_sort()), free_vars, 1);
            save(n, delta, i);
        }
        else {
            save(n, delta, nullptr);
        }
        return;
    }
    case AST_APP: {
        app *       c    = to_app(n);
        func_decl * decl = c->get_decl();
        if (m_owner.is_forbidden(c)) {
            save(n, delta, nullptr);
            return;
        }

        if (c->get_num_args() == 0) {
            save(n, delta, alloc(info, m, n, uint_set(), 1));
            return;
        }

        ptr_buffer<expr> buffer;
        bool changed   = false; // false if none of the children is mapped to a node different from itself.
        uint_set free_vars;
        unsigned size  = 1;
        unsigned num   = c->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            expr * child      = c->get_arg(i);
            info * child_info = nullptr;
#ifdef Z3DEBUG
            bool found =
#endif
            m_cache.find(entry(child, delta), child_info);
            SASSERT(found);
            if (child_info == nullptr) {
                save(n, delta, nullptr);
                return;
            }
            buffer.push_back(child_info->m_node.get());
            free_vars |= child_info->m_free_vars;
            size      += child_info->m_size;
            if (child != child_info->m_node.get())
                changed = true;
        }

        app * new_node = nullptr;
        if (changed)
            new_node = m.mk_app(decl, buffer.size(), buffer.data());
        else
            new_node = to_app(n);
        save(n, delta, alloc(info, m, new_node, free_vars, size));
        // Remark: arithmetic patterns are only used if they are nested inside other terms.
        // That is, we never consider x + 1 as pattern. On the other hand, f(x+1) can be a pattern
        // if arithmetic is not in the forbidden list.
        //
        // Remark: The rule above has an exception. The operators (div, idiv, mod) are allowed to be
        // used as patterns even when they are not nested in other terms. The motivation is that
        // Z3 currently doesn't implement them (i.e., they are uninterpreted). So, some users add axioms
        // stating properties about these operators.
        family_id fid = c->get_family_id();
        decl_kind k   = c->get_decl_kind();
        if (!free_vars.empty() &&            
            (fid != m_afid || (fid == m_afid && !m_owner.m_nested_arith_only && (k == OP_DIV || k == OP_IDIV || k == OP_MOD || k == OP_REM || k == OP_MUL)))) {
            TRACE("pattern_inference", tout << "potential candidate: \n" << mk_pp(new_node, m) << "\n";);
            m_owner.add_candidate(new_node, free_vars, size);
        }
        return;
    }
    default:
        save(n, delta, nullptr);
        return;
    }
}


void pattern_inference_cfg::collect::reset() {
    m_cache.reset();
    std::for_each(m_info.begin(), m_info.end(), delete_proc<info>());
    m_info.reset();
    SASSERT(m_todo.empty());
}

void pattern_inference_cfg::add_candidate(app * n, uint_set const & free_vars, unsigned size) {
    for (unsigned i = 0; i < m_num_no_patterns; i++) {
        if (n == m_no_patterns[i])
            return;
    }

    if (!m_candidates_info.contains(n)) {
        m_candidates_info.insert(n, info(free_vars, size));
        m_candidates.push_back(n);
    }
}


/**
   \brief Copy the non-looping patterns in m_candidates to result when m_params.m_pi_block_loop_patterns = true.
   Otherwise, copy m_candidates to result.
*/
void pattern_inference_cfg::filter_looping_patterns(ptr_vector<app> & result) {
    unsigned num = m_candidates.size();
    for (unsigned i1 = 0; i1 < num; i1++) {
        app * n1 = m_candidates.get(i1);
        expr2info::obj_map_entry * e1 = m_candidates_info.find_core(n1);
        SASSERT(e1);
        uint_set const & s1 = e1->get_data().m_value.m_free_vars;
        if (m_block_loop_patterns) {
            bool smaller = false;
            for (unsigned i2 = 0; i2 < num; i2++) {
                if (i1 != i2) {
                    app * n2 = m_candidates.get(i2);
                    expr2info::obj_map_entry * e2 = m_candidates_info.find_core(n2);
                    if (e2) {
                        uint_set const & s2 = e2->get_data().m_value.m_free_vars;
                        // Remark: the comparison operator only makes sense if both AST nodes
                        // contain the same number of variables.
                        // Example:
                        // (f X Y) <: (f (g X Z W) Y)
                        if (s1 == s2 && m_le(m_num_bindings, n1, n2) && !m_le(m_num_bindings, n2, n1)) {
                            smaller = true;
                            break;
                        }
                    }
                }
            }
            if (!smaller)
                result.push_back(n1);
            else
                m_candidates_info.erase(n1);
        }
        else {
            result.push_back(n1);
        }
    }
}



inline void pattern_inference_cfg::contains_subpattern::save(expr * n) {
    unsigned id = n->get_id();
    m_already_processed.assure_domain(id);
    if (!m_already_processed.contains(id)) {
        m_todo.push_back(n);
        m_already_processed.insert(id);
    }
}

bool pattern_inference_cfg::contains_subpattern::operator()(expr * n) {
    m_already_processed.reset();
    m_todo.reset();
    expr2info::obj_map_entry * _e = m_owner.m_candidates_info.find_core(n);
    SASSERT(_e);
    uint_set const & s1 = _e->get_data().m_value.m_free_vars;
    save(n);
    unsigned num;
    while (!m_todo.empty()) {
        expr * curr = m_todo.back();
        m_todo.pop_back();
        switch (curr->get_kind()) {
        case AST_APP:
            if (curr != n) {
                expr2info::obj_map_entry * e = m_owner.m_candidates_info.find_core(curr);
                if (e) {
                    uint_set const & s2 = e->get_data().m_value.m_free_vars;
                    SASSERT(s2.subset_of(s1));
                    if (s1 == s2) {
                        TRACE("pattern_inference", tout << mk_pp(n, m_owner.m) << "\nis bigger than\n" << mk_pp(to_app(curr), m_owner.m) << "\n";);
                        return true;
                    }
                }
            }
            num = to_app(curr)->get_num_args();
            for (unsigned i = 0; i < num; i++)
                save(to_app(curr)->get_arg(i));
            break;
        case AST_VAR:
            break;
        default:
            UNREACHABLE();
        }
    }
    return false;
}

/**
   Return true if n contains a direct/indirect child that is also a
   pattern, and contains the same number of free variables.
*/
inline bool pattern_inference_cfg::contains_subpattern(expr * n) {
    return m_contains_subpattern(n);
}

/**
   \brief Copy a pattern p in patterns to result, if there is no
   direct/indirect child of p in patterns which contains the same set
   of variables.

   Remark: Every pattern p in patterns is also a member of
   m_pattern_map.
*/
void pattern_inference_cfg::filter_bigger_patterns(ptr_vector<app> const & patterns, ptr_vector<app> & result) {
    for (app * curr : patterns) {
        if (!contains_subpattern(curr))
            result.push_back(curr);
    }
}


bool pattern_inference_cfg::pattern_weight_lt::operator()(expr * n1, expr * n2) const {
    expr2info::obj_map_entry * e1 = m_candidates_info.find_core(n1);
    expr2info::obj_map_entry * e2 = m_candidates_info.find_core(n2);
    SASSERT(e1 != 0);
    SASSERT(e2 != 0);
    info const & i1 = e1->get_data().m_value;
    info const & i2 = e2->get_data().m_value;
    unsigned num_free_vars1 = i1.m_free_vars.num_elems();
    unsigned num_free_vars2 = i2.m_free_vars.num_elems();
    return num_free_vars1 > num_free_vars2 || (num_free_vars1 == num_free_vars2 && i1.m_size < i2.m_size);
}

/**
   \brief Create unary patterns (single expressions that contain all
   bound variables).  If a candidate does not contain all bound
   variables, then it is copied to remaining_candidate_patterns.  The
   new patterns are stored in result.
*/
void pattern_inference_cfg::candidates2unary_patterns(ptr_vector<app> const & candidate_patterns,
                                                  ptr_vector<app> & remaining_candidate_patterns,
                                                  app_ref_buffer  & result) {
    for (app * candidate : candidate_patterns) {
        expr2info::obj_map_entry * e = m_candidates_info.find_core(candidate);
        info const & i = e->get_data().m_value;
        if (i.m_free_vars.num_elems() == m_num_bindings) {
            app * new_pattern = m.mk_pattern(candidate);
            result.push_back(new_pattern);
        }
        else {
            remaining_candidate_patterns.push_back(candidate);
        }
    }
}

// TODO: this code is too inefficient when the number of candidate
// patterns is too big.
// HACK: limit the number of case-splits:
#define MAX_SPLITS 32

void pattern_inference_cfg::candidates2multi_patterns(unsigned max_num_patterns,
                                                  ptr_vector<app> const & candidate_patterns,
                                                  app_ref_buffer & result) {
    SASSERT(!candidate_patterns.empty());
    m_pre_patterns.push_back(alloc(pre_pattern));
    unsigned sz = candidate_patterns.size();
    unsigned num_splits = 0;
    for (unsigned j = 0; j < m_pre_patterns.size(); j++) {
        pre_pattern * curr = m_pre_patterns[j];
        if (curr->m_free_vars.num_elems() == m_num_bindings) {
            app * new_pattern = m.mk_pattern(curr->m_exprs.size(), curr->m_exprs.data());
            result.push_back(new_pattern);
            if (result.size() >= max_num_patterns)
                return;
        }
        else if (curr->m_idx < sz) {
            app * n                     = candidate_patterns[curr->m_idx];
            expr2info::obj_map_entry * e = m_candidates_info.find_core(n);
            uint_set const & s           = e->get_data().m_value.m_free_vars;
            if (!s.subset_of(curr->m_free_vars)) {
                pre_pattern * new_p = alloc(pre_pattern,*curr);
                new_p->m_exprs.push_back(n);
                new_p->m_free_vars |= s;
                new_p->m_idx++;
                m_pre_patterns.push_back(new_p);

                if (num_splits < MAX_SPLITS) {
                    m_pre_patterns[j] = 0;
                    curr->m_idx++;
                    m_pre_patterns.push_back(curr);
                    num_splits++;
                }
            }
            else {
                m_pre_patterns[j] = 0;
                curr->m_idx++;
                m_pre_patterns.push_back(curr);
            }
        }
        TRACE("pattern_inference", tout << "m_pre_patterns.size(): " << m_pre_patterns.size() <<
              "\nnum_splits: " << num_splits << "\n";);
    }
}

void pattern_inference_cfg::reset_pre_patterns() {
    std::for_each(m_pre_patterns.begin(), m_pre_patterns.end(), delete_proc<pre_pattern>());
    m_pre_patterns.reset();
}


bool pattern_inference_cfg::is_forbidden(app * n) const {
    func_decl const * decl = n->get_decl();
    if (is_ground(n))
        return false;
    // Remark: skolem constants should not be used in patterns, since they do not
    // occur outside of the quantifier. That is, Z3 will never match this kind of
    // pattern.
    if (m_params.m_pi_avoid_skolems && decl->is_skolem()) {
        CTRACE("pattern_inference_skolem", decl->is_skolem(), tout << "ignoring: " << mk_pp(n, m) << "\n";);
        return true;
    }
    if (is_forbidden(decl))
        return true;
    return false;
}

bool pattern_inference_cfg::has_preferred_patterns(ptr_vector<app> & candidate_patterns, app_ref_buffer & result) {
    if (m_preferred.empty())
        return false;
    bool found = false;
    for (app * candidate : candidate_patterns) {
        if (m_preferred.contains(to_app(candidate)->get_decl())) {
            expr2info::obj_map_entry * e = m_candidates_info.find_core(candidate);
            info const & i = e->get_data().m_value;
            if (i.m_free_vars.num_elems() == m_num_bindings) {
                TRACE("pattern_inference", tout << "found preferred pattern:\n" << mk_pp(candidate, m) << "\n";);
                app * p = m.mk_pattern(candidate);
                result.push_back(p);
                found = true;
            }
        }
    }
    return found;
}

void pattern_inference_cfg::mk_patterns(unsigned num_bindings,
                                    expr *   n,
                                    unsigned num_no_patterns,
                                    expr * const * no_patterns,
                                    app_ref_buffer & result) {
    m_num_bindings    = num_bindings;
    m_num_no_patterns = num_no_patterns;
    m_no_patterns     = no_patterns;

    m_collect(n, num_bindings);

    TRACE("pattern_inference",
          tout << mk_pp(n, m);
          tout << "\ncandidates:\n";
          unsigned num = m_candidates.size();
          for (unsigned i = 0; i < num; i++) {
              tout << mk_pp(m_candidates.get(i), m) << "\n";
          });

    if (!m_candidates.empty()) {
        m_tmp1.reset();
        filter_looping_patterns(m_tmp1);
        TRACE("pattern_inference",
              tout << "candidates after removing looping-patterns:\n";
              dump_app_vector(tout, m_tmp1, m););
        SASSERT(!m_tmp1.empty());
        if (!has_preferred_patterns(m_tmp1, result)) {
            // continue if there are no preferred patterns
            m_tmp2.reset();
            filter_bigger_patterns(m_tmp1, m_tmp2);
            SASSERT(!m_tmp2.empty());
            TRACE("pattern_inference",
                  tout << "candidates after removing bigger patterns:\n";
                  dump_app_vector(tout, m_tmp2, m););
            m_tmp1.reset();
            candidates2unary_patterns(m_tmp2, m_tmp1, result);
            unsigned num_extra_multi_patterns = m_params.m_pi_max_multi_patterns;
            if (result.empty())
                num_extra_multi_patterns++;
            if (num_extra_multi_patterns > 0 && !m_tmp1.empty()) {
                // m_pattern_weight_lt is not a total order
                std::stable_sort(m_tmp1.begin(), m_tmp1.end(), m_pattern_weight_lt);
                TRACE("pattern_inference",
                      tout << "candidates after sorting:\n";
                      dump_app_vector(tout, m_tmp1, m););
                candidates2multi_patterns(num_extra_multi_patterns, m_tmp1, result);
            }
        }
    }

    reset_pre_patterns();
    m_candidates_info.reset();
    m_candidates.reset();
}


bool pattern_inference_cfg::reduce_quantifier(
    quantifier * q, 
    expr * new_body, 
    expr * const *, // new_patterns 
    expr * const * new_no_patterns,
    expr_ref & result,
    proof_ref & result_pr) {

    TRACE("pattern_inference", tout << "processing:\n" << mk_pp(q, m) << "\n";);
    if (!is_forall(q)) {
        return false;
    }

    int weight = q->get_weight();

    if (m_params.m_pi_use_database) {
        app_ref_vector new_patterns(m);
        m_database.initialize(g_pattern_database);
        unsigned new_weight;
        if (m_database.match_quantifier(q, new_patterns, new_weight)) {
            DEBUG_CODE(for (unsigned i = 0; i < new_patterns.size(); i++) { SASSERT(is_well_sorted(m, new_patterns.get(i))); });
            if (q->get_num_patterns() > 0) {
                // just update the weight...
                TRACE("pattern_inference", tout << "updating weight to: " << new_weight << "\n" << mk_pp(q, m) << "\n";);
                result = m.update_quantifier_weight(q, new_weight);
            }
            else {
                quantifier_ref tmp(m);
                tmp    = m.update_quantifier(q, new_patterns.size(), (expr**) new_patterns.data(), q->get_expr());
                result = m.update_quantifier_weight(tmp, new_weight);
                TRACE("pattern_inference", tout << "found patterns in database, weight: " << new_weight << "\n" << mk_pp(result, m) << "\n";);
            }
            if (m.proofs_enabled())
                result_pr = m.mk_rewrite(q, result);
            return true;
        }
    }

    if (q->get_num_patterns() > 0) {
        return false;
    }

    if (m_params.m_pi_nopat_weight >= 0)
        weight = m_params.m_pi_nopat_weight;

    SASSERT(q->get_num_patterns() == 0);

    if (m_params.m_pi_arith == AP_CONSERVATIVE)
        m_forbidden.push_back(m_afid);

    app_ref_buffer new_patterns(m);
    unsigned num_no_patterns = q->get_num_no_patterns();
    mk_patterns(q->get_num_decls(), new_body, num_no_patterns, new_no_patterns, new_patterns);

    if (new_patterns.empty() && num_no_patterns > 0) {
        if (new_patterns.empty()) {
            mk_patterns(q->get_num_decls(), new_body, 0, nullptr, new_patterns);
            if (m_params.m_pi_warnings && !new_patterns.empty()) {
                auto str = q->get_qid().str();
                warning_msg("ignoring nopats annotation because Z3 couldn't find any other pattern (quantifier id: %s)", str.c_str());
            }
        }
    }

    if (m_params.m_pi_arith == AP_CONSERVATIVE) {
        m_forbidden.pop_back();
        if (new_patterns.empty()) {
            flet<bool> l1(m_block_loop_patterns, false); // allow looping patterns
            mk_patterns(q->get_num_decls(), new_body, num_no_patterns, new_no_patterns, new_patterns);
            if (!new_patterns.empty()) {
                weight = std::max(weight, static_cast<int>(m_params.m_pi_arith_weight));
                if (m_params.m_pi_warnings) {
                    auto str = q->get_qid().str();
                    warning_msg("using arith. in pattern (quantifier id: %s), the weight was increased to %d (this value can be modified using PI_ARITH_WEIGHT=<val>).",
                                str.c_str(), weight);
                }
            }
        }
    }

    if (m_params.m_pi_arith != AP_NO && new_patterns.empty()) {
        if (new_patterns.empty()) {
            flet<bool> l1(m_nested_arith_only, false); // try to find a non-nested arith pattern
            flet<bool> l2(m_block_loop_patterns, false); // allow looping patterns
            mk_patterns(q->get_num_decls(), new_body, num_no_patterns, new_no_patterns, new_patterns);
            if (!new_patterns.empty()) {
                weight = std::max(weight, static_cast<int>(m_params.m_pi_non_nested_arith_weight));
                if (m_params.m_pi_warnings) {
                    auto str = q->get_qid().str();
                    warning_msg("using non nested arith. pattern (quantifier id: %s), the weight was increased to %d (this value can be modified using PI_NON_NESTED_ARITH_WEIGHT=<val>).",
                                str.c_str(), weight);
                }
                // verbose_stream() << mk_pp(q, m) << "\n";
            }
        }
    }

    quantifier_ref new_q(m.update_quantifier(q, new_patterns.size(), (expr**) new_patterns.data(), new_body), m);
    if (weight != q->get_weight())
        new_q = m.update_quantifier_weight(new_q, weight);
    if (m.proofs_enabled()) {
        proof* new_body_pr = m.mk_reflexivity(new_body);
        new_body_pr = m.mk_bind_proof(new_q, new_body_pr);
        result_pr = m.mk_quant_intro(q, new_q, new_body_pr);
    }

    if (new_patterns.empty() && m_params.m_pi_pull_quantifiers) {
        pull_quant pull(m);
        expr_ref   new_expr(m);
        proof_ref  new_pr(m);
        pull(new_q, new_expr, new_pr);
        quantifier * result2 = to_quantifier(new_expr);
        if (result2 != new_q) {
            mk_patterns(result2->get_num_decls(), result2->get_expr(), 0, nullptr, new_patterns);
            if (!new_patterns.empty()) {
                if (m_params.m_pi_warnings) {
                    auto str = q->get_qid().str();
                    warning_msg("pulled nested quantifier to be able to find an usable pattern (quantifier id: %s)", str.c_str());
                }
                new_q = m.update_quantifier(result2, new_patterns.size(), (expr**) new_patterns.data(), result2->get_expr());
                if (m.proofs_enabled()) {
                    result_pr = m.mk_transitivity(new_pr, m.mk_quant_intro(result2, new_q, m.mk_bind_proof(new_q, m.mk_reflexivity(new_q->get_expr()))));
                }
                TRACE("pattern_inference", tout << "pulled quantifier:\n" << mk_pp(new_q, m) << "\n";);
            }
        }
    }

    if (new_patterns.empty()) {
        if (m_params.m_pi_warnings) {
            auto str = q->get_qid().str();
            warning_msg("failed to find a pattern for quantifier (quantifier id: %s)", str.c_str());
        }
        TRACE("pi_failed", tout << mk_pp(q, m) << "\n";);
    }

    if (new_patterns.empty() && new_body == q->get_expr()) {
        return false;
    }

    result = new_q;

    IF_VERBOSE(10,
        verbose_stream() << "(smt.inferred-patterns :qid " << q->get_qid() << "\n";
        for (unsigned i = 0; i < new_patterns.size(); i++)
            verbose_stream() << "  " << mk_ismt2_pp(new_patterns[i], m, 2) << "\n";
        verbose_stream() << ")\n"; );

    return true;
}

pattern_inference_rw::pattern_inference_rw(ast_manager& m, pattern_inference_params const & params):
    rewriter_tpl<pattern_inference_cfg>(m, m.proofs_enabled(), m_cfg),
    m_cfg(m, params)
{}    
