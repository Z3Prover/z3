/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cnf.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-23.

Revision History:

--*/

#include"cnf.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

unsigned cnf_entry::hash() const {
    unsigned a = m_node->get_id();
    unsigned b = m_polarity;
    unsigned c = m_in_q;
    mix(a,b,c);
    return c;
}

bool cnf_entry::operator==(cnf_entry const & k) const {
    return m_node == k.m_node && m_polarity == k.m_polarity && m_in_q == k.m_in_q;
}

cnf_cache::cnf_cache(ast_manager & m):
    m_manager(m) {
}

void cnf_cache::insert(cnf_entry const & k, expr * r, proof * pr) { 
    SASSERT(!m_cache.contains(k));
    m_manager.inc_ref(r);
    m_manager.inc_ref(pr);
    m_cache.insert(k, expr_proof_pair(r, pr));
}

void cnf_cache::reset() {
    cache::iterator it  = m_cache.begin();
    cache::iterator end = m_cache.end();
    for (; it != end; ++it) {
        expr_proof_pair & pair = (*it).m_value;
        m_manager.dec_ref(pair.first);
        m_manager.dec_ref(pair.second);
    }
    m_cache.reset();
}

void cnf::cache_result(expr * e, bool in_q, expr * r, proof * pr) {
    SASSERT(r);
    TRACE("cnf", tout << "caching result for: " << e->get_id() <<  " " << r->get_id() << "\n";);
    m_cache.insert(cnf_entry(e, true, in_q), r, pr);
}

void cnf::visit(expr * n, bool in_q, bool & visited) {
    if (!is_cached(n, in_q)) {
        m_todo.push_back(std::make_pair(n, in_q));
        visited = false;
    }
}

bool cnf::visit_children(expr * n, bool in_q) {
    bool visited = true;
    switch(n->get_kind()) {
    case AST_APP: 
        if (m_manager.is_or(n) || m_manager.is_and(n) || m_manager.is_label(n)) {
            unsigned j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                visit(to_app(n)->get_arg(j), in_q, visited);
            }
        }
        break;
    case AST_QUANTIFIER:
        visit(to_quantifier(n)->get_expr(), true, visited);
        break;
    default:
        break;
    }
    return visited;
}
    
void cnf::reduce1(expr * n, bool in_q) {
    switch(n->get_kind()) {
    case AST_APP: 
        if (m_manager.is_or(n)) 
            reduce1_or(to_app(n), in_q);
        else if (m_manager.is_and(n))
            reduce1_and(to_app(n), in_q);
        else if (m_manager.is_label(n))
            reduce1_label(to_app(n), in_q);
        else
            cache_result(n, in_q, n, 0);
        break;
    case AST_QUANTIFIER:
        reduce1_quantifier(to_quantifier(n), in_q);
        break;
    default:
        cache_result(n, in_q, n, 0);
        break;
    }
}

void cnf::get_args(app * n, bool in_q, ptr_buffer<expr> & new_args, ptr_buffer<proof> & new_arg_prs) {
    unsigned num = n->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        expr * new_arg     = 0;
        proof * new_arg_pr = 0;
        get_cached(n->get_arg(i), in_q, new_arg, new_arg_pr);
        SASSERT(new_arg);
        new_args.push_back(new_arg);
        if (new_arg_pr)
            new_arg_prs.push_back(new_arg_pr);
    }
}

void cnf::flat_args(func_decl * d, ptr_buffer<expr> const & args, ptr_buffer<expr> & flat_args) {
    ptr_buffer<expr>::const_iterator it  = args.begin();
    ptr_buffer<expr>::const_iterator end = args.end();
    for (; it != end; ++it) {
        expr * arg = *it;
        if (is_app_of(arg, d))
            flat_args.append(to_app(arg)->get_num_args(), to_app(arg)->get_args());
        else
            flat_args.push_back(arg);
    }
}

/**
   \brief Return the approximated size of distributing OR over AND on
   (OR args[0] .... args[sz-1])
*/
approx_nat cnf::approx_result_size_for_disj(ptr_buffer<expr> const & args) {
    approx_nat r(1);
    ptr_buffer<expr>::const_iterator it  = args.begin();
    ptr_buffer<expr>::const_iterator end = args.end();
    for (; it != end; ++it) {
        expr * arg = *it;
        if (m_manager.is_and(arg))
            r *= to_app(arg)->get_num_args();
    }
    return r;
}

/**
   \brief Return true if it is too expensive to process the disjunction of args
*/
inline bool cnf::is_too_expensive(approx_nat approx_result_size, ptr_buffer<expr> const & args) {
    // (OR A (AND B C)) is always considered cheap.
    if (args.size() == 2 && (!m_manager.is_and(args[0]) || !m_manager.is_and(args[1])))
        return false;
    return !(approx_result_size < m_params.m_cnf_factor);
}

/**
   \brief Create a (positive) name for the expressions of the form (AND ...) in args.
   Store the result in new_args. 
*/
void cnf::name_args(ptr_buffer<expr> const & args, expr_ref_buffer & new_args, proof_ref_buffer & new_arg_prs) {
    ptr_buffer<expr>::const_iterator it  = args.begin();
    ptr_buffer<expr>::const_iterator end = args.end();
    for (; it != end; ++it) {
        expr * arg = *it;
        if (m_manager.is_and(arg)) {
            expr_ref  new_def(m_manager);
            proof_ref new_def_pr(m_manager);
            app_ref   new_arg(m_manager);
            proof_ref new_arg_pr(m_manager);
                                               
            if (m_defined_names.mk_pos_name(to_app(arg), new_def, new_def_pr, new_arg, new_arg_pr)) {
                m_todo_defs.push_back(new_def);
                if (m_manager.proofs_enabled())
                    m_todo_proofs.push_back(new_def_pr);
            }
            new_args.push_back(new_arg);

            if (m_manager.fine_grain_proofs())
                new_arg_prs.push_back(new_arg_pr);
            else
                m_coarse_proofs.push_back(new_arg_pr);
        }
        else 
            new_args.push_back(arg);
    }
}

void cnf::distribute(app * n, app * & r, proof * & pr) {
    SASSERT(m_manager.is_or(n));
    buffer<unsigned> sz;
    buffer<unsigned> it;
    ptr_buffer<expr> new_args;
    unsigned num = n->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        expr * arg = n->get_arg(i);
        it.push_back(0);
        if (m_manager.is_and(arg))
            sz.push_back(to_app(arg)->get_num_args());
        else
            sz.push_back(1);
    }

    do {
        ptr_buffer<expr> lits;
        for (unsigned i = 0; i < num; i++) {
            expr * arg = n->get_arg(i);
            if (m_manager.is_and(arg)) {
                SASSERT(it[i] < to_app(arg)->get_num_args());
                lits.push_back(to_app(arg)->get_arg(it[i]));
            }
            else {
                SASSERT(it[i] == 0);
                lits.push_back(arg);
            }
        }
        app * n = m_manager.mk_or(lits.size(), lits.c_ptr());
        new_args.push_back(n);
    }
    while (product_iterator_next(sz.size(), sz.c_ptr(), it.c_ptr()));
    SASSERT(!new_args.empty());
    if (new_args.size() == 1) 
        r = to_app(new_args[0]);
    else
        r = m_manager.mk_and(new_args.size(), new_args.c_ptr());
    pr = 0;
    if (m_manager.fine_grain_proofs() && r != n)
        pr = m_manager.mk_iff_oeq(m_manager.mk_distributivity(n, r));
}

void cnf::push_quant(quantifier * q, expr * & r, proof * & pr) {
    SASSERT(is_forall(q));
    expr * e = q->get_expr();
    pr = 0;
    if (m_manager.is_and(e)) {
        expr_ref_buffer new_args(m_manager);
        unsigned num = to_app(e)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            quantifier_ref aux(m_manager);
            aux = m_manager.update_quantifier(q, 0, 0, 0, 0, to_app(e)->get_arg(i));
            expr_ref new_arg(m_manager);
            elim_unused_vars(m_manager, aux, new_arg);
            new_args.push_back(new_arg);
        }
        r  = m_manager.mk_and(new_args.size(), new_args.c_ptr());
        if (m_manager.fine_grain_proofs()) 
            pr = m_manager.mk_iff_oeq(m_manager.mk_push_quant(q, r));
    }
    else {
        r  = q;
    }
}

void cnf::reduce1_or(app * n, bool in_q) {
    ptr_buffer<expr>  new_args;
    ptr_buffer<proof> new_arg_prs;
    get_args(n, in_q, new_args, new_arg_prs);
    expr *   r;
    proof * pr = 0;
    if (in_q || m_params.m_cnf_mode == CNF_OPPORTUNISTIC || m_params.m_cnf_mode == CNF_FULL) {
        ptr_buffer<expr>  f_args;
        flat_args(n->get_decl(), new_args, f_args);
        TRACE("cnf_or", for (unsigned i = 0; i < f_args.size(); i++) tout << mk_pp(f_args[i], m_manager) << "\n";);
        approx_nat result_size = approx_result_size_for_disj(f_args);
        TRACE("cnf_or", tout << mk_pp(n, m_manager) << "\napprox. result: " << result_size << "\n";);
        if (m_params.m_cnf_mode != CNF_OPPORTUNISTIC || result_size < m_params.m_cnf_factor) {
            expr_ref_buffer  cheap_args(m_manager);
            proof_ref_buffer cheap_args_pr(m_manager);
            if (is_too_expensive(result_size, f_args)) {
                name_args(f_args, cheap_args, cheap_args_pr);
            }
            else {
                cheap_args.append(f_args.size(), f_args.c_ptr());
            }
            
            app_ref r1(m_manager);
            r1 = m_manager.mk_or(cheap_args.size(), cheap_args.c_ptr());

            // Proof gen support ---------------------------
            // r1 is (OR cheap_args) it is only built if proofs are enabled.
            // p1 is a proof for (= n r1)
            proof * p1 = 0;
            if (m_manager.fine_grain_proofs()) {
                proof * prs[3];
                app   * r[2];
                r[0]       = m_manager.mk_or(new_args.size(), new_args.c_ptr());
                prs[0]     = n == r[0] ? 0 : m_manager.mk_oeq_congruence(n, r[0], new_arg_prs.size(), new_arg_prs.c_ptr());
                r[1]       = m_manager.mk_or(f_args.size(), f_args.c_ptr());
                prs[1]     = r[0] == r[1] ? 0 : m_manager.mk_iff_oeq(m_manager.mk_rewrite(r[0], r[1]));
                prs[2]     = r[1] == r1 ? 0 : m_manager.mk_oeq_congruence(r[1], r1, cheap_args_pr.size(), cheap_args_pr.c_ptr());
                p1         = m_manager.mk_transitivity(3, prs);
            }
            // --------------------------------------------

            expr_ref  r2(m_manager);
            proof_ref p2(m_manager);
            m_pull.pull_quant2(r1, r2, p2);

            if (is_quantifier(r2)) {
                expr * e = to_quantifier(r2)->get_expr();
                SASSERT(m_manager.is_or(e));
                app *  d_r;
                proof * d_pr;
                distribute(to_app(e), d_r, d_pr);
                quantifier_ref r3(m_manager);
                r3 = m_manager.update_quantifier(to_quantifier(r2), d_r);
                proof * push_pr;
                push_quant(r3, r, push_pr);
                if (m_manager.fine_grain_proofs()) {
                    // p1 is a proof of n == r1
                    // p2 is a proof of r1 == r2
                    p2         = p2 == 0  ? 0 : m_manager.mk_iff_oeq(p2);
                    proof * p3 = r2 == r3 ? 0 : m_manager.mk_oeq_quant_intro(to_quantifier(r2), r3, d_pr);
                    CTRACE("cnf_or", p1, tout << "p1:\n" << mk_pp(m_manager.get_fact(p1), m_manager) << "\n";);
                    CTRACE("cnf_or", p2, tout << "p2:\n" << mk_pp(m_manager.get_fact(p2), m_manager) << "\n";);
                    CTRACE("cnf_or", p3, tout << "p3:\n" << mk_pp(m_manager.get_fact(p3), m_manager) << "\n";);
                    TRACE("cnf_or", tout << "r2 == r3: " << (r2 == r3) << "\n" 
                          << mk_pp(r2, m_manager) << "\n" << mk_pp(r3, m_manager) << "\n";);
                    pr = m_manager.mk_transitivity(p1, p2, p3, push_pr);
                }
                cache_result(n, in_q, r, pr);
            }
            else {
                SASSERT(p2 == 0);
                SASSERT(r1 == r2);
                SASSERT(m_manager.is_or(r2));
                app * r3;
                distribute(to_app(r2), r3, pr);
                r = r3;
                pr = m_manager.mk_transitivity(p1, pr);
                cache_result(n, in_q, r, pr);
            }
            return;
        }
    }

    r = m_manager.mk_or(new_args.size(), new_args.c_ptr());
    if (m_manager.fine_grain_proofs() && n != r) 
        pr = m_manager.mk_oeq_congruence(n, to_app(r), new_arg_prs.size(), new_arg_prs.c_ptr());
    cache_result(n, in_q, r, pr);
}

void cnf::reduce1_and(app * n, bool in_q) {
    ptr_buffer<expr>  new_args;
    ptr_buffer<proof> new_arg_prs;
    get_args(n, in_q, new_args, new_arg_prs);
    app * r;
    proof * pr = 0;
    if (in_q || m_params.m_cnf_mode == CNF_OPPORTUNISTIC || m_params.m_cnf_mode == CNF_FULL) {
        ptr_buffer<expr> f_args;
        flat_args(n->get_decl(), new_args, f_args);
        r    = m_manager.mk_and(f_args.size(), f_args.c_ptr());
        if (m_manager.fine_grain_proofs() && n != r) {
            app * r0   = m_manager.mk_and(new_args.size(), new_args.c_ptr());
            proof * p0 = r0 == n ? 0 : m_manager.mk_oeq_congruence(n, r0, new_arg_prs.size(), new_arg_prs.c_ptr());
            proof * p1 = r0 == r ? 0 : m_manager.mk_iff_oeq(m_manager.mk_rewrite(r0, r));
            pr         = m_manager.mk_transitivity(p0, p1);
        }
    }
    else {
        r    = m_manager.mk_and(new_args.size(), new_args.c_ptr());
        if (m_manager.fine_grain_proofs() && n != r) 
            pr = m_manager.mk_oeq_congruence(n, r, new_arg_prs.size(), new_arg_prs.c_ptr());
    }
    cache_result(n, in_q, r, pr);
}

void cnf::reduce1_label(app * n, bool in_q) {
    expr * r;
    proof * pr = 0;
    expr * new_arg;
    proof * new_arg_pr;
    get_cached(n->get_arg(0), true, new_arg, new_arg_pr);
    if (in_q || m_params.m_cnf_mode == CNF_FULL) {
        // TODO: in the current implementation, labels are removed during CNF translation.
        // This is satisfactory for Boogie, since it does not use labels inside quantifiers,
        // and we only need CNF_QUANT for Superposition Calculus.
        r   = new_arg;
        if (m_manager.fine_grain_proofs()) {
            proof * p0 = m_manager.mk_iff_oeq(m_manager.mk_rewrite(n, n->get_arg(0)));
            pr         = m_manager.mk_transitivity(p0, new_arg_pr);
        }
    }
    else {
        r = m_manager.mk_app(n->get_decl(), new_arg);
        if (m_manager.fine_grain_proofs() && n != r) 
            pr = m_manager.mk_oeq_congruence(n, to_app(r), 1, &new_arg_pr);
    }
    cache_result(n, in_q, r, pr);
}

void cnf::reduce1_quantifier(quantifier * q, bool in_q) {
    expr *  new_expr;
    proof * new_expr_pr;
    get_cached(q->get_expr(), true, new_expr, new_expr_pr);
    expr_ref  r(m_manager);
    proof_ref pr(m_manager);
    if (m_manager.is_and(new_expr) && q->is_forall()) {
        quantifier_ref q1(m_manager);
        q1 = m_manager.update_quantifier(q, new_expr);
        expr_ref  q2(m_manager);
        proof_ref p2(m_manager);
        m_pull.pull_quant2(q1, q2, p2);
        expr *  q3;
        proof * p3;
        push_quant(to_quantifier(q2), q3, p3);
        r = q3;
        if (m_manager.fine_grain_proofs()) {
            proof * p1 = q == q1 ? 0 : m_manager.mk_oeq_quant_intro(q, q1, new_expr_pr);
            p2         = p2 == 0 ? 0 : m_manager.mk_iff_oeq(p2);
            pr         = m_manager.mk_transitivity(p1, p2, p3);
        }
    }
    else if ((m_manager.is_or(new_expr) || is_forall(new_expr)) && q->is_forall()) {
        quantifier_ref q1(m_manager);
        q1 = m_manager.update_quantifier(q, new_expr);
        m_pull.pull_quant2(q1, r, pr);
        if (m_manager.fine_grain_proofs()) {
            pr = pr == 0 ? 0 : m_manager.mk_iff_oeq(pr);
            proof * p1 = q == q1 ? 0 : m_manager.mk_oeq_quant_intro(q, q1, new_expr_pr);
            pr = m_manager.mk_transitivity(p1, pr);
        }
    }
    else {
        r = m_manager.update_quantifier(q, new_expr);
        if (m_manager.fine_grain_proofs() && r != q)
            pr = q == r ? 0 : m_manager.mk_oeq_quant_intro(q, to_quantifier(r), new_expr_pr);
    }
    
    cache_result(q, in_q, r, pr);
    TRACE("cnf_quant", tout << mk_pp(q, m_manager) << "\n" << mk_pp(r, m_manager) << "\n";);
}

cnf::cnf(ast_manager & m, defined_names & n, cnf_params & params):
    m_params(params),
    m_manager(m),
    m_defined_names(n),
    m_pull(m),
    m_cache(m),
    m_todo_defs(m),
    m_todo_proofs(m),
    m_coarse_proofs(m) {
}

cnf::~cnf() {
}

void cnf::reduce(expr * n, expr_ref & r, proof_ref & pr) {
    m_coarse_proofs.reset();
    m_todo.reset();
    m_todo.push_back(expr_bool_pair(n, false));
    while (!m_todo.empty()) {
        expr_bool_pair pair = m_todo.back();
        expr * n  = pair.first;
        bool in_q = pair.second;
        if (is_cached(n, in_q)) {
            m_todo.pop_back();
        }
        else if (visit_children(n, in_q)) {
            m_todo.pop_back();
            reduce1(n, in_q);
        }
    }
    expr * r2;
    proof * pr2;
    get_cached(n, false, r2, pr2);
    r = r2;
    switch (m_manager.proof_mode()) {
    case PGM_DISABLED:
        pr = m_manager.mk_undef_proof();
        break;
    case PGM_COARSE:
        remove_duplicates(m_coarse_proofs);
        pr = n == r2 ? m_manager.mk_reflexivity(n) : m_manager.mk_cnf_star(n, r2, m_coarse_proofs.size(), m_coarse_proofs.c_ptr());
        break;
    case PGM_FINE:
        pr = pr2 == 0 ? m_manager.mk_reflexivity(n) : pr2;
        break;
    }
}

void cnf::operator()(expr * n, expr_ref_vector & new_defs, proof_ref_vector & new_def_proofs, expr_ref & r, proof_ref & pr) {
    if (m_params.m_cnf_mode == CNF_DISABLED) {
        r  = n;
        pr = m_manager.mk_reflexivity(n); 
        return;
    }

    reset();
    reduce(n, r, pr);
    for (unsigned i = 0; i < m_todo_defs.size(); i++) {
        expr_ref  dr(m_manager);
        proof_ref dpr(m_manager);
        reduce(m_todo_defs.get(i), dr, dpr);
        m_result_defs.push_back(dr);
        if (m_manager.proofs_enabled()) {
            proof * new_pr = m_manager.mk_modus_ponens(m_todo_proofs.get(i), dpr);
            m_result_def_proofs.push_back(new_pr); 
        }
        else
            m_result_def_proofs.push_back(m_manager.mk_undef_proof());
    }
    std::reverse(m_result_defs.begin(), m_result_defs.end()); 
    new_defs.append(m_result_defs.size(), m_result_defs.c_ptr());
    std::reverse(m_result_def_proofs.begin(), m_result_def_proofs.end());
    new_def_proofs.append(m_result_def_proofs.size(), m_result_def_proofs.c_ptr());
}

void cnf::reset() {
    m_cache.reset();
    m_todo.reset();
    m_todo_defs.reset();
    m_todo_proofs.reset();
    m_result_defs.reset();
    m_result_def_proofs.reset();
}
