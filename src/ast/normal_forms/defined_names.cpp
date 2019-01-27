/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    defined_names.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/
#include "util/obj_hashtable.h"
#include "ast/normal_forms/defined_names.h"
#include "ast/used_vars.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/array_decl_plugin.h"

struct defined_names::impl {
    typedef obj_map<expr, app *>   expr2name;
    typedef obj_map<expr, proof *> expr2proof;
    ast_manager &    m;
    symbol           m_z3name;

    /**
       \brief Mapping from expressions to their names. A name is an application.
       If the expression does not have free variables, then the name is just a constant.
    */
    expr2name        m_expr2name;
    /**
       \brief Mapping from expressions to the apply-def proof.
       That is, for each expression e, m_expr2proof[e] is the
       proof e and m_expr2name[2] are observ. equivalent.

       This mapping is not used if proof production is disabled.
    */
    expr2proof       m_expr2proof;

    /**
       \brief Domain of m_expr2name. It is used to keep the expressions
       alive and for backtracking
    */
    expr_ref_vector  m_exprs;
    expr_ref_vector  m_names;        //!< Range of m_expr2name. It is used to keep the names alive.
    proof_ref_vector m_apply_proofs; //!< Range of m_expr2proof. It is used to keep the def-intro proofs alive.


    unsigned_vector m_lims;          //!< Backtracking support.

    impl(ast_manager & m, char const * prefix);
    virtual ~impl();

    app * gen_name(expr * e, sort_ref_buffer & var_sorts, buffer<symbol> & var_names);
    void cache_new_name(expr * e, app * name);
    void cache_new_name_intro_proof(expr * e, proof * pr);
    void bound_vars(sort_ref_buffer const & sorts, buffer<symbol> const & names, expr * def_conjunct, app * name, expr_ref & result, symbol const& qid = symbol::null);
    void bound_vars(sort_ref_buffer const & sorts, buffer<symbol> const & names, expr * def_conjunct, app * name, expr_ref_buffer & result, symbol const& qid = symbol::null);
    virtual void mk_definition(expr * e, app * n, sort_ref_buffer & var_sorts, buffer<symbol> & var_names, expr_ref & new_def);
    bool mk_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr);
    void push_scope();
    void pop_scope(unsigned num_scopes);
    void reset();

    unsigned get_num_names() const { return m_names.size(); }
    func_decl * get_name_decl(unsigned i) const { return to_app(m_names.get(i))->get_decl(); }
};

struct defined_names::pos_impl : public defined_names::impl {
    pos_impl(ast_manager & m, char const * fresh_prefix):impl(m, fresh_prefix) {}
    void mk_definition(expr * e, app * n, sort_ref_buffer & var_sorts, buffer<symbol> & var_names, expr_ref & new_def) override;

};


defined_names::impl::impl(ast_manager & m, char const * prefix):
    m(m),
    m_exprs(m),
    m_names(m),
    m_apply_proofs(m) {
    if (prefix)
        m_z3name = prefix;
}

defined_names::impl::~impl() {
}

/**
   \brief Given an expression \c e that may contain free variables, return an application (sk x_1 ... x_n),
   where sk is a fresh variable name, and x_i's are the free variables of \c e.

   Store in var_sorts and var_names information about the free variables of \c e. This data
   is used to create an universal quantifier over the definition of the new name.
*/
app * defined_names::impl::gen_name(expr * e, sort_ref_buffer & var_sorts, buffer<symbol> & var_names) {
    used_vars uv;
    uv(e);
    unsigned num_vars = uv.get_max_found_var_idx_plus_1();
    ptr_buffer<expr> new_args;
    ptr_buffer<sort> domain;
    for (unsigned i = 0; i < num_vars; i++) {
        sort * s = uv.get(i);
        if (s) {
            domain.push_back(s);
            new_args.push_back(m.mk_var(i, s));
            var_sorts.push_back(s);
        }
        else {
            var_sorts.push_back(m.mk_bool_sort()); // could be any sort.
        }
        var_names.push_back(symbol(i));
    }

    sort * range = m.get_sort(e);
    func_decl * new_skolem_decl = m.mk_fresh_func_decl(m_z3name, symbol::null, domain.size(), domain.c_ptr(), range);
    app * n = m.mk_app(new_skolem_decl, new_args.size(), new_args.c_ptr());
    TRACE("mk_definition_bug", tout << "gen_name: " << mk_ismt2_pp(n, m) << "\n";
          for (unsigned i = 0; i < var_sorts.size(); i++) tout << mk_pp(var_sorts[i], m) << " ";
          tout << "\n";);
    return n;
}

/**
   \brief Cache \c n as a name for expression \c e.
*/
void defined_names::impl::cache_new_name(expr * e, app * n) {
    m_expr2name.insert(e, n);
    m_exprs.push_back(e);
    m_names.push_back(n);
}

/**
   \brief Cache \c pr as a proof that m_expr2name[e] is a name for expression \c e.
*/
void defined_names::impl::cache_new_name_intro_proof(expr * e, proof * pr) {
    SASSERT(m_expr2name.contains(e));
    m_expr2proof.insert(e, pr);
    m_apply_proofs.push_back(pr);
}

/**
   \brief Given a definition conjunct \c def of the name \c name, store in \c result this definition.
   A quantifier is added around \c def_conjunct, if sorts and names are not empty.
   In this case, The application \c name is used as a pattern for the new quantifier.
*/
void defined_names::impl::bound_vars(sort_ref_buffer const & sorts, buffer<symbol> const & names, expr * def_conjunct, app * name, expr_ref & result, symbol const& qid) {
    SASSERT(sorts.size() == names.size());
    if (sorts.empty())
        result = def_conjunct;
    else {
        expr * patterns[1] = { m.mk_pattern(name) };
        quantifier_ref q(m);
        q = m.mk_forall(sorts.size(),
                                sorts.c_ptr(),
                                names.c_ptr(),
                                def_conjunct,
                                1, qid, symbol::null,
                                1, patterns);
        TRACE("mk_definition_bug", tout << "before elim_unused_vars:\n" << mk_ismt2_pp(q, m) << "\n";);
        result = elim_unused_vars(m, q, params_ref());
        TRACE("mk_definition_bug", tout << "after elim_unused_vars:\n" << result << "\n";);
    }
}

/**
   \brief Given a definition conjunct \c def of the name \c name, store in \c result this definition.
   A quantifier is added around \c def_conjunct, if sorts and names are not empty.
   In this case, The application \c name is used as a pattern for the new quantifier.
*/
void defined_names::impl::bound_vars(sort_ref_buffer const & sorts, buffer<symbol> const & names, expr * def_conjunct, app * name, expr_ref_buffer & result, symbol const& qid) {
    expr_ref tmp(m);
    bound_vars(sorts, names, def_conjunct, name, tmp, qid);
    result.push_back(tmp);
}

#define MK_OR      m.mk_or
#define MK_NOT     m.mk_not
#define MK_EQ      m.mk_eq

void defined_names::impl::mk_definition(expr * e, app * n, sort_ref_buffer & var_sorts, buffer<symbol> & var_names, expr_ref & new_def) {
    expr_ref_buffer defs(m);
    if (m.is_bool(e)) {
        bound_vars(var_sorts, var_names, MK_OR(MK_NOT(n), e), n, defs);
        bound_vars(var_sorts, var_names, MK_OR(n, MK_NOT(e)), n, defs);
    }
    else if (m.is_term_ite(e)) {
        bound_vars(var_sorts, var_names, MK_OR(MK_NOT(to_app(e)->get_arg(0)), MK_EQ(n, to_app(e)->get_arg(1))), n, defs);
        bound_vars(var_sorts, var_names, MK_OR(to_app(e)->get_arg(0),         MK_EQ(n, to_app(e)->get_arg(2))), n, defs);
    }
    else if (is_lambda(e)) {
        //    n(y) = \x . M[x,y]
        // => 
        //    n(y)[x] = M,  forall x y
        // 
        // NB. The pattern is incomplete.
        // consider store(a, i, v) == \lambda j . if i = j then v else a[j]
        // the instantiation rules for store(a, i, v) are:
        //     sotre(a, i, v)[j] = if i = j then v else a[j] with patterns {a[j], store(a, i, v)} { store(a, i, v)[j] }
        // The first pattern is not included.
        // TBD use a model-based scheme for exracting instantiations instead of
        // using multi-patterns.
        // 

        quantifier* q = to_quantifier(e);
        expr_ref_vector args(m);
        expr_ref n2(m), n3(m);
        var_shifter vs(m);
        vs(n, q->get_num_decls(), n2);        
        args.push_back(n2);
        var_sorts.append(q->get_num_decls(), q->get_decl_sorts());
        var_names.append(q->get_num_decls(), q->get_decl_names());
        for (unsigned i = 0; i < q->get_num_decls(); ++i) {
            args.push_back(m.mk_var(q->get_num_decls() - i - 1, q->get_decl_sort(i)));
        }
        array_util autil(m);
        func_decl * f = nullptr;
        if (autil.is_as_array(n2, f)) {
            n3 = m.mk_app(f, args.size()-1, args.c_ptr() + 1);
        }
        else {
            n3 = autil.mk_select(args.size(), args.c_ptr());
        }
        bound_vars(var_sorts, var_names, MK_EQ(q->get_expr(), n3), to_app(n3), defs, m.lambda_def_qid());
        
    }
    else {
        bound_vars(var_sorts, var_names, MK_EQ(e, n), n, defs);
    }
    new_def = mk_and(m, defs.size(), defs.c_ptr());
}


void defined_names::pos_impl::mk_definition(expr * e, app * n, sort_ref_buffer & var_sorts, buffer<symbol> & var_names, expr_ref & new_def) {
    bound_vars(var_sorts, var_names, MK_OR(MK_NOT(n), e), n, new_def);
}

bool defined_names::impl::mk_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr) {
    TRACE("mk_definition_bug", tout << "making name for:\n" << mk_ismt2_pp(e, m) << "\n";);

    app *   n_ptr;
    if (m_expr2name.find(e, n_ptr)) {
        TRACE("mk_definition_bug", tout << "name for expression is already cached..., returning false...\n";);
        n = n_ptr;
        if (m.proofs_enabled()) {
            proof * pr_ptr = nullptr;
            m_expr2proof.find(e, pr_ptr);
            SASSERT(pr_ptr);
            pr = pr_ptr;
        }
        return false;
    }
    else {
        sort_ref_buffer  var_sorts(m);
        buffer<symbol>   var_names;

        n = gen_name(e, var_sorts, var_names);
        cache_new_name(e, n);

        TRACE("mk_definition_bug", tout << "name: " << mk_ismt2_pp(n, m) << "\n";);
        // variables are in reverse order in quantifiers
        std::reverse(var_sorts.c_ptr(), var_sorts.c_ptr() + var_sorts.size());
        std::reverse(var_names.c_ptr(), var_names.c_ptr() + var_names.size());

        mk_definition(e, n, var_sorts, var_names, new_def);

        TRACE("mk_definition_bug", tout << "new_def:\n" << mk_ismt2_pp(new_def, m) << "\n";);

        if (m.proofs_enabled()) {
            new_def_pr = m.mk_def_intro(new_def);
            pr         = m.mk_apply_def(e, n, new_def_pr);
            cache_new_name_intro_proof(e, pr);
        }
        return true;
    }
}

void defined_names::impl::push_scope() {
    SASSERT(m_exprs.size() == m_names.size());
    m_lims.push_back(m_exprs.size());
}

void defined_names::impl::pop_scope(unsigned num_scopes) {
    unsigned lvl     = m_lims.size();
    SASSERT(num_scopes <= lvl);
    unsigned new_lvl = lvl - num_scopes;
    unsigned old_sz  = m_lims[new_lvl];
    unsigned sz      = m_exprs.size();
    SASSERT(old_sz <= sz);
    SASSERT(sz == m_names.size());
    while (old_sz != sz) {
        --sz;
        if (m.proofs_enabled()) {
            m_expr2proof.erase(m_exprs.back());
            m_apply_proofs.pop_back();
        }
        m_expr2name.erase(m_exprs.back());
        m_exprs.pop_back();
        m_names.pop_back();
    }
    SASSERT(m_exprs.size() == old_sz);
    m_lims.shrink(new_lvl);
}

void defined_names::impl::reset() {
    m_expr2name.reset();
    m_expr2proof.reset();
    m_exprs.reset();
    m_names.reset();
    m_apply_proofs.reset();
    m_lims.reset();
}

defined_names::defined_names(ast_manager & m, char const * fresh_prefix) {
    m_impl = alloc(impl, m, fresh_prefix);
    m_pos_impl = alloc(pos_impl, m, fresh_prefix);
}

defined_names::~defined_names() {
    dealloc(m_impl);
    dealloc(m_pos_impl);
}

bool defined_names::mk_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr) {
    return m_impl->mk_name(e, new_def, new_def_pr, n, pr);
}

bool defined_names::mk_pos_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr) {
    return m_pos_impl->mk_name(e, new_def, new_def_pr, n, pr);
}

expr_ref defined_names::mk_definition(expr * e, app * n) {
    ast_manager& m = m_impl->m;
    sort_ref_buffer  var_sorts(m);
    expr_ref new_def(m);
    buffer<symbol>   var_names;
    m_impl->mk_definition(e, n, var_sorts, var_names, new_def);
    return new_def;
}

void defined_names::push() {
    m_impl->push_scope();
    m_pos_impl->push_scope();
}

void defined_names::pop(unsigned num_scopes) {
    m_impl->pop_scope(num_scopes);
    m_pos_impl->pop_scope(num_scopes);
}

void defined_names::reset() {
    m_impl->reset();
    m_pos_impl->reset();
}

unsigned defined_names::get_num_names() const {
    return m_impl->get_num_names() + m_pos_impl->get_num_names();
}

func_decl * defined_names::get_name_decl(unsigned i) const {
    SASSERT(i < get_num_names());
    unsigned n1 = m_impl->get_num_names();
    return i < n1 ? m_impl->get_name_decl(i) : m_pos_impl->get_name_decl(i - n1);
}





