/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_manager.cpp

Abstract:

    A manager class for SPACER, taking care of creating of AST
    objects and conversions between them.

Author:

    Krystof Hoder (t-khoder) 2011-8-25.

Revision History:

--*/

#include <sstream>

#include "muz/spacer/spacer_manager.h"
#include "ast/ast_smt2_pp.h"
#include "ast/for_each_expr.h"
#include "ast/has_free_vars.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/expr_abstract.h"
#include "model/model2expr.h"
#include "model/model_smt2_pp.h"
#include "tactic/model_converter.h"

#include "smt/smt_solver.h"
namespace spacer {

class collect_decls_proc {
    func_decl_set& m_bound_decls;
    func_decl_set& m_aux_decls;
public:
    collect_decls_proc(func_decl_set& bound_decls, func_decl_set& aux_decls):
        m_bound_decls(bound_decls),
        m_aux_decls(aux_decls)
    {
    }

    void operator()(app* a)
    {
        if (a->get_family_id() == null_family_id) {
            func_decl* f = a->get_decl();
            if (!m_bound_decls.contains(f)) {
                m_aux_decls.insert(f);
            }
        }
    }
    void operator()(var* v) {}
    void operator()(quantifier* q) {}
};

typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;

expr_ref inductive_property::fixup_clause(expr* fml) const
{
    expr_ref_vector disjs(m);
    flatten_or(fml, disjs);    
    return bool_rewriter(m).mk_or(disjs);
}

expr_ref inductive_property::fixup_clauses(expr* fml) const
{
    expr_ref_vector conjs(m);
    flatten_and(fml, conjs);
    unsigned i = 0;
    for (expr* c : conjs) {
        conjs[i++] = fixup_clause(c);
    }
    return bool_rewriter(m).mk_and(conjs);
}

std::string inductive_property::to_string() const
{
    std::stringstream stm;
    model_ref md;
    to_model(md);
    stm << *md;
    return stm.str();
}

void inductive_property::to_model(model_ref& md) const {
    md = alloc(model, m);
    for (relation_info const& ri : m_relation_info) {
        expr_ref prop = fixup_clauses(ri.m_body);
        func_decl_ref_vector const& sig = ri.m_vars;
        expr_ref_vector sig_vars(m);
        for (unsigned j = 0; j < sig.size(); ++j) {
            sig_vars.push_back(m.mk_const(sig[sig.size() - j - 1]));
        }
        expr_ref q = expr_abstract(sig_vars, prop);
        md->register_decl(ri.m_pred, q);
    }
    TRACE("spacer", tout << *md;);
    apply(const_cast<model_converter_ref&>(m_mc), md);
}

expr_ref inductive_property::to_expr() const
{
    model_ref md;
    expr_ref result(m);
    to_model(md);
    md->compress();
    model2expr(md, result);
    return result;
}


void inductive_property::display(datalog::rule_manager& rm, ptr_vector<datalog::rule> const& rules, std::ostream& out) const
{
    func_decl_set bound_decls, aux_decls;
    collect_decls_proc collect_decls(bound_decls, aux_decls);

    for (auto const& ri : m_relation_info) {
        bound_decls.insert(ri.m_pred);
        for (func_decl* b : ri.m_vars) {
            bound_decls.insert(b);
        }
        for_each_expr(collect_decls, ri.m_body);
    }
    for (auto* r : rules) {
        bound_decls.insert(r->get_decl());
    }
    for (auto* r : rules) {
        unsigned u_sz = r->get_uninterpreted_tail_size();
        unsigned t_sz =  r->get_tail_size();
        for (unsigned j = u_sz; j < t_sz; ++j) {
            for_each_expr(collect_decls, r->get_tail(j));
        }
    }
    smt2_pp_environment_dbg env(m);
    for (func_decl* f : aux_decls) {
        ast_smt2_pp(out, f, env) << "\n";
    }

    out << to_string() << "\n";
    for (auto* r : rules) {
        out << "(push 1)\n";
        out << "(assert (not\n";
        rm.display_smt2(*r, out);
        out << "))\n";
        out << "(check-sat)\n";
        out << "(pop 1)\n";
    }
}



manager::manager(ast_manager& manager) : m(manager), m_mux(m) {}

func_decl * manager::get_o_pred(func_decl* s, unsigned idx) {
    func_decl * res = m_mux.find_by_decl(s, o_index(idx));
    if (!res) {
        m_mux.register_decl(s);
        res = m_mux.find_by_decl(s, o_index(idx));
    }
    SASSERT(res);
    return res;
}

func_decl * manager::get_n_pred(func_decl* s) {
    func_decl * res = m_mux.find_by_decl(s, n_index());
    if (!res) {
        m_mux.register_decl(s);
        res = m_mux.find_by_decl(s, n_index());
    }
    SASSERT(res);
    return res;
}

/**
 * Create a new skolem constant
 */
app* mk_zk_const(ast_manager &m, unsigned idx, sort *s) {
    std::stringstream name;
    name << "sk!" << idx;
    return m.mk_const(symbol(name.str()), s);
}

namespace find_zk_const_ns {
struct proc {
    int m_max;
    app_ref_vector &m_out;
    proc (app_ref_vector &out) : m_max(-1), m_out(out) {}
    void operator() (var const * n) const {}
    void operator() (app *n) {
        int idx;
        if (is_zk_const(n, idx)) {
            m_out.push_back(n);
            if (idx > m_max) {
                m_max = idx;
            }
        }
    }
    void operator() (quantifier const *n) const {}
};
}

int find_zk_const(expr *e, app_ref_vector &res) {
    find_zk_const_ns::proc p(res);
    for_each_expr (p, e);
    return p.m_max;
}

namespace has_zk_const_ns {
struct found {};
struct proc {
    void operator() (var const *n) const {}
    void operator() (app const *n) const {
        int idx;
        if (is_zk_const(n, idx)) {
            throw found();
        }
    }
    void operator() (quantifier const *n) const {}
};
}


bool has_zk_const(expr *e){
    has_zk_const_ns::proc p;
    try {
        for_each_expr(p, e);
    }
    catch (const has_zk_const_ns::found &) {
        return true;
    }
    return false;
}

bool is_zk_const (const app *a, int &n) {
    if (!is_uninterp_const(a)) return false;

    const symbol &name = a->get_decl()->get_name();
    if (name.str().compare (0, 3, "sk!") != 0) {
        return false;
    }

    n = std::stoi(name.str().substr(3));
    return true;
}
bool sk_lt_proc::operator()(const app *a1, const app *a2) {
    if (a1 == a2) return false;
    int n1, n2;
    bool z1, z2;
    z1 = is_zk_const(a1, n1);
    z2 = is_zk_const(a2, n2);
    if (z1 && z2) return n1 < n2;
    if (z1 != z2) return z1;
    return ast_lt_proc()(a1, a2);
}

}
