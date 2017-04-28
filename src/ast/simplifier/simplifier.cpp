/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    simplifier.cpp

Abstract:

    Expression simplifier.

Author:

    Leonardo (leonardo) 2008-01-03

Notes:

--*/
#include"simplifier.h"
#include"var_subst.h"
#include"ast_ll_pp.h"
#include"ast_pp.h"
#include"well_sorted.h"
#include"ast_smt_pp.h"

simplifier::simplifier(ast_manager & m):
    base_simplifier(m),
    m_proofs(m),
    m_subst_proofs(m),
    m_need_reset(false),
    m_use_oeq(false),
    m_visited_quantifier(false),
    m_ac_support(true) {
}

void simplifier::register_plugin(plugin * p) {
    m_plugins.register_plugin(p);
}

simplifier::~simplifier() {
    flush_cache();
}

void simplifier::enable_ac_support(bool flag) {
    m_ac_support = flag;
    ptr_vector<plugin>::const_iterator it  = m_plugins.begin();
    ptr_vector<plugin>::const_iterator end = m_plugins.end();
    for (; it != end; ++it) {
        if (*it != 0)
            (*it)->enable_ac_support(flag);
    }
}

/**
   \brief External interface for the simplifier.
   A client will invoke operator()(s, r, p) to simplify s.
   The result is stored in r.
   When proof generation is enabled, a proof for the equivalence (or equisatisfiability)
   of s and r is stored in p.
   When proof generation is disabled, this method stores the "undefined proof" object in p.
*/
void simplifier::operator()(expr * s, expr_ref & r, proof_ref & p) {
    m_need_reset = true;
    reinitialize();
    expr  * s_orig = s;
    (void)s_orig;
    expr  * old_s;
    expr  * result;
    proof * result_proof;
    switch (m.proof_mode()) {
    case PGM_DISABLED: // proof generation is disabled.
        reduce_core(s);
        // after executing reduce_core, the result of the simplification is in the cache
        get_cached(s, result, result_proof);
        r = result;
        p = m.mk_undef_proof();
        break;
    case PGM_COARSE: // coarse proofs... in this case, we do not produce a step by step (fine grain) proof to show the equivalence (or equisatisfiability) of s an r.
        m_subst_proofs.reset(); // m_subst_proofs is an auxiliary vector that is used to justify substitutions. See comment on method get_subst.
        reduce_core(s);
        get_cached(s, result, result_proof);
        r = result;
        if (result == s)
            p = m.mk_reflexivity(s);
        else {
            remove_duplicates(m_subst_proofs);
            p = m.mk_rewrite_star(s, result, m_subst_proofs.size(), m_subst_proofs.c_ptr());
        }
        break;
    case PGM_FINE: // fine grain proofs... in this mode, every proof step (or most of them) is described.
        m_proofs.reset();
        old_s = 0;
        // keep simplyfing until no further simplifications are possible.
        while (s != old_s) {
            TRACE("simplifier", tout << "simplification pass... " << s->get_id() << "\n";);
            TRACE("simplifier_loop", tout << mk_ll_pp(s, m) << "\n";);
            reduce_core(s);
            get_cached(s, result, result_proof);
            SASSERT(is_rewrite_proof(s, result, result_proof));
            if (result_proof != 0) {
                m_proofs.push_back(result_proof);
            }
            old_s = s;
            s     = result;
        }
        SASSERT(s != 0);
        r = s;
        p = m_proofs.empty() ? m.mk_reflexivity(s) : m.mk_transitivity(m_proofs.size(), m_proofs.c_ptr());
        SASSERT(is_rewrite_proof(s_orig, r, p));
        break;
    default:
        UNREACHABLE();
    }
}

void simplifier::flush_cache() {
    m_cache.flush();
    ptr_vector<plugin>::const_iterator it  = m_plugins.begin();
    ptr_vector<plugin>::const_iterator end = m_plugins.end();
    for (; it != end; ++it) {
        if (*it != 0) {
            (*it)->flush_caches();
        }
    }
}

bool simplifier::get_subst(expr * n, expr_ref & r, proof_ref & p) {
    return false;
}

void simplifier::reduce_core(expr * n1) {
    if (!is_cached(n1)) {
        // We do not assume m_todo is empty... So, we store the current size of the todo-stack.
        unsigned sz = m_todo.size();
        m_todo.push_back(n1);
        while (m_todo.size() != sz) {
            expr * n = m_todo.back();
            if (is_cached(n))
                m_todo.pop_back();
            else if (visit_children(n)) {
                // if all children were already simplified, then remove n from the todo stack and apply a
                // simplification step to it.
                m_todo.pop_back();
                reduce1(n);
            }
            if (m.canceled()) {
                cache_result(n1, n1, 0);
                break;
            }
        }
    }
}

/**
   \brief Return true if all children of n have been already simplified.
*/
bool simplifier::visit_children(expr * n) {
    switch(n->get_kind()) {
    case AST_VAR:
        return true;
    case AST_APP:
        // The simplifier has support for flattening AC (associative-commutative) operators.
        // The method ast_manager::mk_app is used to create the flat version of an AC operator.
        // In Z3 1.x, we used multi-ary operators. This creates problems for the superposition engine.
        // So, starting at Z3 2.x, only boolean operators can be multi-ary.
        // Example:
        //    (and (and a b) (and c d)) --> (and a b c d)
        //    (+ (+ a b) (+ c d)) --> (+ a (+ b (+ c d)))
        // Remark: The flattening is only applied if m_ac_support is true.
        if (m_ac_support && to_app(n)->get_decl()->is_associative() && to_app(n)->get_decl()->is_commutative())
            return visit_ac(to_app(n));
        else {
            bool visited = true;
            unsigned j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                visit(to_app(n)->get_arg(j), visited);
            }
            return visited;
        }
    case AST_QUANTIFIER:
        return visit_quantifier(to_quantifier(n));
    default:
        UNREACHABLE();
        return true;
    }
}

/**
   \brief Visit the children of n assuming it is an AC (associative-commutative) operator.

   For example, if n is of the form (+ (+ a b) (+ c d)), this method
   will return true if the nodes a, b, c and d have been already simplified.
   The nodes (+ a b) and (+ c d) are not really checked.
*/
bool simplifier::visit_ac(app * n) {
    bool visited = true;
    func_decl * decl = n->get_decl();
    SASSERT(m_ac_support);
    SASSERT(decl->is_associative());
    SASSERT(decl->is_commutative());
    m_ac_marked.reset();
    ptr_buffer<app> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        app * n = todo.back();
        todo.pop_back();
        if (m_ac_mark.is_marked(n))
            continue;
        m_ac_mark.mark(n, true);
        m_ac_marked.push_back(n);
        SASSERT(n->get_decl() == decl);
        unsigned i = n->get_num_args();
        while (i > 0) {
            --i;
            expr * arg  = n->get_arg(i);
            if (is_app_of(arg, decl))
                todo.push_back(to_app(arg));
            else
                visit(arg, visited);
        }
    }
    ptr_vector<expr>::const_iterator it  = m_ac_marked.begin();
    ptr_vector<expr>::const_iterator end = m_ac_marked.end();
    for (; it != end; ++it)
        m_ac_mark.mark(*it, false);
    return visited;
}

bool simplifier::visit_quantifier(quantifier * n) {
    m_visited_quantifier = true;
    bool visited         = true;
    unsigned j = to_quantifier(n)->get_num_patterns();
    while (j > 0) {
        --j;
        visit(to_quantifier(n)->get_pattern(j), visited);
    }
    j = to_quantifier(n)->get_num_no_patterns();
    while (j > 0) {
        --j;
        visit(to_quantifier(n)->get_no_pattern(j), visited);
    }
    visit(to_quantifier(n)->get_expr(), visited);
    return visited;
}

/**
   \brief Simplify n and store the result in the cache.
*/
void simplifier::reduce1(expr * n) {
    switch (n->get_kind()) {
    case AST_VAR:
        cache_result(n, n, 0);
        break;
    case AST_APP:
        reduce1_app(to_app(n));
        break;
    case AST_QUANTIFIER:
        reduce1_quantifier(to_quantifier(n));
        break;
    default:
        UNREACHABLE();
    }
}

/**
   \brief Simplify the given application using the cached values,
   associativity flattening, the given substitution, and family/theory
   specific simplifications via plugins.
*/
void simplifier::reduce1_app(app * n) {
    expr_ref r(m);
    proof_ref p(m);
    TRACE("reduce", tout << "reducing...\n" << mk_pp(n, m) << "\n";);
    if (get_subst(n, r, p)) {
        TRACE("reduce", tout << "applying substitution...\n";);
        cache_result(n, r, p);
        return;
    }

    func_decl * decl = n->get_decl();
    if (m_ac_support && decl->is_associative() && decl->is_commutative())
        reduce1_ac_app_core(n);
    else
        reduce1_app_core(n);
}


void simplifier::reduce1_app_core(app * n) {
    m_args.reset();
    func_decl * decl = n->get_decl();
    proof_ref p1(m);
    // Stores the new arguments of n in m_args.
    // Let n be of the form
    // (decl arg_0 ... arg_{n-1})
    // then
    // m_args contains [arg_0', ..., arg_{n-1}'],
    // where arg_i' is the simplification of arg_i
    // and
    // p1 is a proof for
    // (decl arg_0 ... arg_{n-1}) is equivalente/equisatisfiable to (decl arg_0' ... arg_{n-1}')
    // p1 is built using the congruence proof step and the proofs for arg_0' ... arg_{n-1}'.
    // Of course, p1 is 0 if proofs are not enabled or coarse grain proofs are used.
    bool has_new_args = get_args(n, m_args, p1);
    // The following if implements a simple trick.
    //   If none of the arguments have been simplified, and n is not a theory symbol,
    //   Then no simplification is possible, and we can cache the result of the simplification of n as n.
    if (has_new_args || decl->get_family_id() != null_family_id) {
        expr_ref r(m);
        TRACE("reduce", tout << "reduce1_app\n"; for(unsigned i = 0; i < m_args.size(); i++) tout << mk_ll_pp(m_args[i], m););
        // the method mk_app invokes get_subst and plugins to simplify
        // (decl arg_0' ... arg_{n-1}')
        mk_app(decl, m_args.size(), m_args.c_ptr(), r);
        if (!m.fine_grain_proofs()) {
            cache_result(n, r, 0);
        }
        else {
            expr * s = m.mk_app(decl, m_args.size(), m_args.c_ptr());
            proof * p;
            if (n == r)
                p = 0;
            else if (r != s)
                // we use a "theory rewrite generic proof" to justify the step
                // s = (decl arg_0' ... arg_{n-1}') --> r
                p = m.mk_transitivity(p1, m.mk_rewrite(s, r));
            else
                p = p1;
            cache_result(n, r, p);
        }
    }
    else {
        cache_result(n, n, 0);
    }
}

bool is_ac_list(app * n, ptr_vector<expr> & args) {
    args.reset();
    func_decl * f = n->get_decl();
    app * curr    = n;
    while (true) {
        if (curr->get_num_args() != 2)
            return false;
        expr * arg1 = curr->get_arg(0);
        if (is_app_of(arg1, f))
            return false;
        args.push_back(arg1);
        expr * arg2 = curr->get_arg(1);
        if (!is_app_of(arg2, f)) {
            args.push_back(arg2);
            return true;
        }
        curr = to_app(arg2);
    }
}

bool is_ac_vector(app * n) {
    func_decl * f     = n->get_decl();
    unsigned num_args = n->get_num_args();
    for (unsigned i = 0; i < num_args; i++) {
        if (is_app_of(n->get_arg(i), f))
            return false;
    }
    return true;
}

void simplifier::reduce1_ac_app_core(app * n) {
    app_ref    n_c(m);
    proof_ref  p1(m);
    mk_ac_congruent_term(n, n_c, p1);
    TRACE("ac", tout << "expr:\n" << mk_pp(n, m) << "\ncongruent term:\n" << mk_pp(n_c, m) << "\n";);
    expr_ref r(m);
    func_decl * decl = n->get_decl();
    family_id fid    = decl->get_family_id();
    plugin * p       = get_plugin(fid);
    if (is_ac_vector(n_c)) {
        if (p != 0 && p->reduce(decl, n_c->get_num_args(), n_c->get_args(), r)) {
            // done...
        }
        else {
            r = n_c;
        }
    }
    else if (is_ac_list(n_c, m_args)) {
        // m_args contains the arguments...
        if (p != 0 && p->reduce(decl, m_args.size(), m_args.c_ptr(), r)) {
            // done...
        }
        else {
            r = m.mk_app(decl, m_args.size(), m_args.c_ptr());
        }
    }
    else {
        m_args.reset();
        m_mults.reset();
        get_ac_args(n_c, m_args, m_mults);
        TRACE("ac", tout << "AC args:\n";
              for (unsigned i = 0; i < m_args.size(); i++) {
                  tout << mk_pp(m_args[i], m) << " * " << m_mults[i] << "\n";
              });
        if (p != 0 && p->reduce(decl, m_args.size(), m_mults.c_ptr(), m_args.c_ptr(), r)) {
            // done...
        }
        else {
            ptr_buffer<expr> new_args;
            expand_args(m_args.size(), m_mults.c_ptr(), m_args.c_ptr(), new_args);
            r = m.mk_app(decl, new_args.size(), new_args.c_ptr());
        }
    }
    TRACE("ac", tout << "AC result:\n" << mk_pp(r, m) << "\n";);

    if (!m.fine_grain_proofs()) {
        cache_result(n, r, 0);
    }
    else {
        proof * p;
        if (n == r.get())
            p = 0;
        else if (r.get() != n_c.get())
            p = m.mk_transitivity(p1, m.mk_rewrite(n_c, r));
        else
            p = p1;
        cache_result(n, r, p);
    }
}

static unsigned g_rewrite_lemma_id = 0;

void simplifier::dump_rewrite_lemma(func_decl * decl, unsigned num_args, expr * const * args, expr* result) {
    expr_ref arg(m);
    arg = m.mk_app(decl, num_args, args);
    if (arg.get() != result) {
        char buffer[128];
#ifdef _WINDOWS
        sprintf_s(buffer, ARRAYSIZE(buffer), "lemma_%d.smt", g_rewrite_lemma_id);
#else
        sprintf(buffer, "rewrite_lemma_%d.smt", g_rewrite_lemma_id);
#endif
        ast_smt_pp pp(m);
        pp.set_benchmark_name("rewrite_lemma");
        pp.set_status("unsat");
        expr_ref n(m);
        n = m.mk_not(m.mk_eq(arg.get(), result));
        std::ofstream out(buffer);
        pp.display(out, n);
        out.close();
        ++g_rewrite_lemma_id;
    }
}

/**
   \brief Return in \c result an expression \c e equivalent to <tt>(f args[0] ... args[num_args - 1])</tt>, and
   store in \c pr a proof for <tt>(= (f args[0] ... args[num_args - 1]) e)</tt>

   If e is identical to (f args[0] ... args[num_args - 1]), then pr is set to 0.
*/
void simplifier::mk_app(func_decl * decl, unsigned num_args, expr * const * args, expr_ref & result) {
    m_need_reset = true;
    if (m.is_eq(decl)) {
        sort * s = m.get_sort(args[0]);
        plugin * p = get_plugin(s->get_family_id());
        if (p != 0 && p->reduce_eq(args[0], args[1], result))
            return;
    }
    else if (m.is_distinct(decl)) {
        sort * s = m.get_sort(args[0]);
        plugin * p = get_plugin(s->get_family_id());
        if (p != 0 && p->reduce_distinct(num_args, args, result))
            return;
    }
    family_id fid = decl->get_family_id();
    plugin * p = get_plugin(fid);
    if (p != 0 && p->reduce(decl, num_args, args, result)) {
        //uncomment this line if you want to trace rewrites as lemmas:
        //dump_rewrite_lemma(decl, num_args, args, result.get());
        return;
    }

    result = m.mk_app(decl, num_args, args);
}

/**
   \brief Create a term congruence to n (f a[0] ... a[num_args-1]) using the
   cached values for the a[i]'s. Store the result in r, and the proof for (= n r) in p.
   If n and r are identical, then set p to 0.
*/
void simplifier::mk_congruent_term(app * n, app_ref & r, proof_ref & p) {
    bool has_new_args  = false;
    ptr_vector<expr>   args;
    ptr_vector<proof>  proofs;
    unsigned num       = n->get_num_args();
    for (unsigned j = 0; j < num; j++) {
        expr * arg     = n->get_arg(j);
        expr * new_arg;
        proof * arg_proof;
        get_cached(arg, new_arg, arg_proof);

        CTRACE("simplifier_bug", (arg != new_arg) != (arg_proof != 0),
               tout << mk_ll_pp(arg, m) << "\n---->\n" << mk_ll_pp(new_arg, m) << "\n";
               tout << "#" << arg->get_id() << " #" << new_arg->get_id() << "\n";
               tout << arg << " " << new_arg << "\n";);


        if (arg != new_arg) {
            has_new_args = true;
            proofs.push_back(arg_proof);
            SASSERT(arg_proof);
        }
        else {
            SASSERT(arg_proof == 0);
        }
        args.push_back(new_arg);
    }
    if (has_new_args) {
        r = m.mk_app(n->get_decl(), args.size(), args.c_ptr());
        if (m_use_oeq)
            p = m.mk_oeq_congruence(n, r, proofs.size(), proofs.c_ptr());
        else
            p = m.mk_congruence(n, r, proofs.size(), proofs.c_ptr());
    }
    else {
        r = n;
        p = 0;
    }
}

/**
   \brief Store the new arguments of \c n in result. Store in p a proof for
   (= n (f result[0] ... result[num_args - 1])), where f is the function symbol of n.

   If there are no new arguments or fine grain proofs are disabled, then p is set to 0.

   Return true there are new arguments.
*/
bool simplifier::get_args(app * n, ptr_vector<expr> & result, proof_ref & p) {
    bool has_new_args  = false;
    unsigned num       = n->get_num_args();
    if (m.fine_grain_proofs()) {
        app_ref r(m);
        mk_congruent_term(n, r, p);
        result.append(r->get_num_args(), r->get_args());
        SASSERT(n->get_num_args() == result.size());
        has_new_args = r != n;
    }
    else {
        p = 0;
        for (unsigned j = 0; j < num; j++) {
            expr * arg     = n->get_arg(j);
            expr * new_arg;
            proof * arg_proof;
            get_cached(arg, new_arg, arg_proof);
            if (arg != new_arg) {
                has_new_args = true;
            }
            result.push_back(new_arg);
        }
    }
    return has_new_args;
}

/**
   \brief Create a term congruence to n (where n is an expression such as: (f (f a_1 a_2) (f a_3 (f a_4 a_5))) using the
   cached values for the a_i's. Store the result in r, and the proof for (= n r) in p.
   If n and r are identical, then set p to 0.
*/
void simplifier::mk_ac_congruent_term(app * n, app_ref & r, proof_ref & p) {
    SASSERT(m_ac_support);
    func_decl * f = n->get_decl();

    m_ac_cache.reset();
    m_ac_pr_cache.reset();

    ptr_buffer<app>   todo;
    ptr_buffer<expr>  new_args;
    ptr_buffer<proof> new_arg_prs;
    todo.push_back(n);
    while (!todo.empty()) {
        app * curr    = todo.back();
        if (m_ac_cache.contains(curr)) {
            todo.pop_back();
            continue;
        }
        bool visited     = true;
        bool has_new_arg = false;
        new_args.reset();
        new_arg_prs.reset();
        unsigned num_args = curr->get_num_args();
        for (unsigned j = 0; j < num_args; j ++) {
            expr * arg = curr->get_arg(j);
            if (is_app_of(arg, f)) {
                app * new_arg = 0;
                if (m_ac_cache.find(to_app(arg), new_arg)) {
                    SASSERT(new_arg != 0);
                    new_args.push_back(new_arg);
                    if (arg != new_arg)
                        has_new_arg = true;
                    if (m.fine_grain_proofs()) {
                        proof * pr = 0;
                        m_ac_pr_cache.find(to_app(arg), pr);
                        if (pr != 0)
                            new_arg_prs.push_back(pr);
                    }
                }
                else {
                    visited = false;
                    todo.push_back(to_app(arg));
                }
            }
            else {
                expr * new_arg = 0;
                proof * pr;
                get_cached(arg, new_arg, pr);
                new_args.push_back(new_arg);
                if (arg != new_arg)
                    has_new_arg = true;
                if (m.fine_grain_proofs() && pr != 0)
                    new_arg_prs.push_back(pr);
            }
        }
        if (visited) {
            SASSERT(new_args.size() == curr->get_num_args());
            todo.pop_back();
            if (!has_new_arg) {
                m_ac_cache.insert(curr, curr);
                if (m.fine_grain_proofs())
                    m_ac_pr_cache.insert(curr, 0);
            }
            else {
                app * new_curr = m.mk_app(f, new_args.size(), new_args.c_ptr());
                m_ac_cache.insert(curr, new_curr);
                if (m.fine_grain_proofs()) {
                    proof * p = m.mk_congruence(curr, new_curr, new_arg_prs.size(), new_arg_prs.c_ptr());
                    m_ac_pr_cache.insert(curr, p);
                }
            }
        }
    }

    SASSERT(m_ac_cache.contains(n));
    app *   new_n = 0;
    m_ac_cache.find(n, new_n);
    r = new_n;
    if (m.fine_grain_proofs()) {
        proof * new_pr = 0;
        m_ac_pr_cache.find(n, new_pr);
        p = new_pr;
    }
}

#define White 0
#define Grey  1
#define Black 2

#ifdef Z3DEBUG
static int get_color(obj_map<expr, int> & colors, expr * n) {
    obj_map<expr, int>::obj_map_entry * entry = colors.insert_if_not_there2(n, White);
    return entry->get_data().m_value;
}
#endif

static bool visit_ac_children(func_decl * f, expr * n, obj_map<expr, int> & colors, ptr_buffer<expr> & todo, ptr_buffer<expr> & result) {
    if (is_app_of(n, f)) {
        unsigned num_args = to_app(n)->get_num_args();
        bool visited      = true;
        // Put the arguments in 'result' in reverse order.
        // Reason: preserve the original order of the arguments in the final result.
        // Remark: get_ac_args will traverse 'result' backwards.
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = to_app(n)->get_arg(i);
            obj_map<expr, int>::obj_map_entry * entry = colors.insert_if_not_there2(arg, White);
            if (entry->get_data().m_value == White) {
                todo.push_back(arg);
                visited = false;
            }
        }
        return visited;
    }
    else {
        return true;
    }
}

void simplifier::ac_top_sort(app * n, ptr_buffer<expr> & result) {
    ptr_buffer<expr> todo;
    func_decl * f = n->get_decl();
    obj_map<expr, int> & colors = m_colors;
    colors.reset();
    todo.push_back(n);
    while (!todo.empty()) {
        expr * curr = todo.back();
        int color;
        obj_map<expr, int>::obj_map_entry * entry = colors.insert_if_not_there2(curr, White);
        SASSERT(entry);
        color = entry->get_data().m_value;
        switch (color) {
        case White:
            // Remark: entry becomes invalid if an element is inserted into the hashtable.
            // So, I must set Grey before executing visit_ac_children.
            entry->get_data().m_value = Grey;
            SASSERT(get_color(colors, curr) == Grey);
            if (visit_ac_children(f, curr, colors, todo, result)) {
                // If visit_ac_children succeeded, then the hashtable was not modified,
                // and entry is still valid.
                SASSERT(todo.back() == curr);
                entry->get_data().m_value = Black;
                SASSERT(get_color(colors, curr) == Black);
                result.push_back(curr);
                todo.pop_back();
            }
            break;
        case Grey:
            SASSERT(visit_ac_children(f, curr, colors, todo, result));
            SASSERT(entry);
            entry->get_data().m_value = Black;
            SASSERT(get_color(colors, curr) == Black);
            result.push_back(curr);
            SASSERT(todo.back() == curr);
            todo.pop_back();
            break;
        case Black:
            todo.pop_back();
            break;
        default:
            UNREACHABLE();
        }
    }
}

void simplifier::get_ac_args(app * n, ptr_vector<expr> & args, vector<rational> & mults) {
    SASSERT(m_ac_support);
    ptr_buffer<expr> sorted_exprs;
    ac_top_sort(n, sorted_exprs);
    SASSERT(!sorted_exprs.empty());
    SASSERT(sorted_exprs[sorted_exprs.size()-1] == n);

    TRACE("ac", tout << mk_ll_pp(n, m, true, false) << "#" << n->get_id() << "\nsorted expressions...\n";
          for (unsigned i = 0; i < sorted_exprs.size(); i++) {
              tout << "#" << sorted_exprs[i]->get_id() << " ";
          }
          tout << "\n";);

    m_ac_mults.reset();
    m_ac_mults.insert(n, rational(1));
    func_decl * decl = n->get_decl();
    unsigned j = sorted_exprs.size();
    while (j > 0) {
        --j;
        expr * curr = sorted_exprs[j];
        rational mult;
        m_ac_mults.find(curr, mult);
        SASSERT(!mult.is_zero());
        if (is_app_of(curr, decl)) {
            unsigned num_args = to_app(curr)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg = to_app(curr)->get_arg(i);
                rational zero;
                obj_map<expr, rational>::obj_map_entry * entry = m_ac_mults.insert_if_not_there2(arg, zero);
                entry->get_data().m_value += mult;
            }
        }
        else {
            args.push_back(curr);
            mults.push_back(mult);
        }
    }
}

void simplifier::reduce1_quantifier(quantifier * q) {
    expr *  new_body;
    proof * new_body_pr;
    SASSERT(is_well_sorted(m, q));
    get_cached(q->get_expr(), new_body, new_body_pr);

    quantifier_ref q1(m);
    proof * p1 = 0;

    if (is_quantifier(new_body) &&
        to_quantifier(new_body)->is_forall() == q->is_forall() &&
        !to_quantifier(q)->has_patterns() &&
        !to_quantifier(new_body)->has_patterns()) {

        quantifier * nested_q = to_quantifier(new_body);

        ptr_buffer<sort> sorts;
        buffer<symbol>   names;
        sorts.append(q->get_num_decls(), q->get_decl_sorts());
        names.append(q->get_num_decls(), q->get_decl_names());
        sorts.append(nested_q->get_num_decls(), nested_q->get_decl_sorts());
        names.append(nested_q->get_num_decls(), nested_q->get_decl_names());

        q1 = m.mk_quantifier(q->is_forall(),
                                     sorts.size(),
                                     sorts.c_ptr(),
                                     names.c_ptr(),
                                     nested_q->get_expr(),
                                     std::min(q->get_weight(), nested_q->get_weight()),
                                     q->get_qid(),
                                     q->get_skid(),
                                     0, 0, 0, 0);
        SASSERT(is_well_sorted(m, q1));

        if (m.fine_grain_proofs()) {
            quantifier * q0 = m.update_quantifier(q, new_body);
            proof * p0 = q == q0 ? 0 : m.mk_quant_intro(q, q0, new_body_pr);
            p1 = m.mk_pull_quant(q0, q1);
            p1 = m.mk_transitivity(p0, p1);
        }
    }
    else {
        ptr_buffer<expr> new_patterns;
        ptr_buffer<expr> new_no_patterns;
        expr  * new_pattern;
        proof * new_pattern_pr;

        // Remark: we can ignore the proofs for the patterns.
        unsigned num = q->get_num_patterns();
        for (unsigned i = 0; i < num; i++) {
            get_cached(q->get_pattern(i), new_pattern, new_pattern_pr);
            if (m.is_pattern(new_pattern)) {
                new_patterns.push_back(new_pattern);
            }
        }
        num = q->get_num_no_patterns();
        for (unsigned i = 0; i < num; i++) {
            get_cached(q->get_no_pattern(i), new_pattern, new_pattern_pr);
            new_no_patterns.push_back(new_pattern);
        }

        remove_duplicates(new_patterns);
        remove_duplicates(new_no_patterns);

        q1 = m.mk_quantifier(q->is_forall(),
                                     q->get_num_decls(),
                                     q->get_decl_sorts(),
                                     q->get_decl_names(),
                                     new_body,
                                     q->get_weight(),
                                     q->get_qid(),
                                     q->get_skid(),
                                     new_patterns.size(),
                                     new_patterns.c_ptr(),
                                     new_no_patterns.size(),
                                     new_no_patterns.c_ptr());
        SASSERT(is_well_sorted(m, q1));

        TRACE("simplifier", tout << mk_pp(q, m) << "\n" << mk_pp(q1, m) << "\n";);
        if (m.fine_grain_proofs()) {
            if (q != q1 && !new_body_pr) {
                new_body_pr = m.mk_rewrite(q->get_expr(), new_body);
            }
            p1 = q == q1 ? 0 : m.mk_quant_intro(q, q1, new_body_pr);
        }
    }

    expr_ref r(m);
    elim_unused_vars(m, q1, params_ref(), r);

    proof * pr = 0;
    if (m.fine_grain_proofs()) {
        proof * p2 = 0;
        if (q1.get() != r.get())
            p2 = m.mk_elim_unused_vars(q1, r);
        pr = m.mk_transitivity(p1, p2);
    }

    cache_result(q, r, pr);
}

/**
   \see release_plugins
*/
void simplifier::borrow_plugins(simplifier const & s) {
    ptr_vector<plugin>::const_iterator it  = s.begin_plugins();
    ptr_vector<plugin>::const_iterator end = s.end_plugins();
    for (; it != end; ++it)
        register_plugin(*it);
}

/**
   \brief Make the simplifier behave as a pre-simplifier: No AC, and plugins are marked in pre-simplification mode.
*/
void simplifier::enable_presimp() {
    enable_ac_support(false);
    ptr_vector<plugin>::const_iterator it  = begin_plugins();
    ptr_vector<plugin>::const_iterator end = end_plugins();
    for (; it != end; ++it)
        (*it)->enable_presimp(true);
}

/**
   \brief This method should be invoked if the plugins of this simplifier were borrowed from a different simplifier.
*/
void simplifier::release_plugins() {
    m_plugins.release();
}

void subst_simplifier::set_subst_map(expr_map * s) {
    flush_cache();
    m_subst_map = s;
}

bool subst_simplifier::get_subst(expr * n, expr_ref & r, proof_ref & p) {
    if (m_subst_map && m_subst_map->contains(n)) {
        expr *  _r;
        proof * _p = 0;
        m_subst_map->get(n, _r, _p);
        r = _r;
        p = _p;
        if (m.coarse_grain_proofs())
            m_subst_proofs.push_back(p);
        return true;
    }
    return false;
}

static void push_core(ast_manager & m, expr * e, proof * pr, expr_ref_vector & result, proof_ref_vector & result_prs) {
    SASSERT(pr == 0 || m.is_undef_proof(pr) || e == m.get_fact(pr));
    TRACE("preprocessor",
          tout << mk_pp(e, m) << "\n";
          if (pr) tout << mk_ll_pp(pr, m) << "\n\n";);
    if (m.is_true(e))
        return;
    result.push_back(e);
    if (m.proofs_enabled())
        result_prs.push_back(pr);
}

static void push_and(ast_manager & m, app * e, proof * pr, expr_ref_vector & result, proof_ref_vector & result_prs) {
    unsigned num = e->get_num_args();
    TRACE("push_and", tout << mk_pp(e, m) << "\n";);
    for (unsigned i = 0; i < num; i++)
        push_assertion(m, e->get_arg(i), m.mk_and_elim(pr, i), result, result_prs);
}

static void push_not_or(ast_manager & m, app * e, proof * pr, expr_ref_vector & result, proof_ref_vector & result_prs) {
    unsigned num = e->get_num_args();
    TRACE("push_not_or", tout << mk_pp(e, m) << "\n";);
    for (unsigned i = 0; i < num; i++) {
        expr * child = e->get_arg(i);
        if (m.is_not(child)) {
            expr * not_child = to_app(child)->get_arg(0);
            push_assertion(m, not_child, m.mk_not_or_elim(pr, i), result, result_prs);
        }
        else {
            expr_ref not_child(m);
            not_child = m.mk_not(child);
            push_assertion(m, not_child, m.mk_not_or_elim(pr, i), result, result_prs);
        }
    }
}

void push_assertion(ast_manager & m, expr * e, proof * pr, expr_ref_vector & result, proof_ref_vector & result_prs) {
    CTRACE("push_assertion", !(pr == 0 || m.is_undef_proof(pr) || m.get_fact(pr) == e),
           tout << mk_pp(e, m) << "\n" << mk_pp(m.get_fact(pr), m) << "\n";);
    SASSERT(pr == 0 || m.is_undef_proof(pr) || m.get_fact(pr) == e);
    if (m.is_and(e))
        push_and(m, to_app(e), pr, result, result_prs);
    else if (m.is_not(e) && m.is_or(to_app(e)->get_arg(0)))
        push_not_or(m, to_app(to_app(e)->get_arg(0)), pr, result, result_prs);
    else
        push_core(m, e, pr, result, result_prs);
}

