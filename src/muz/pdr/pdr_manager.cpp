/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_manager.cpp

Abstract:

    A manager class for PDR, taking care of creating of AST 
    objects and conversions between them.

Author:

    Krystof Hoder (t-khoder) 2011-8-25.

Revision History:

--*/

#include <sstream>
#include "muz/pdr/pdr_manager.h"
#include "ast/ast_smt2_pp.h"
#include "ast/for_each_expr.h"
#include "ast/has_free_vars.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/expr_abstract.h"
#include "model/model2expr.h"
#include "model/model_smt2_pp.h"
#include "tactic/model_converter.h"

namespace pdr {

    class collect_decls_proc {
        func_decl_set& m_bound_decls;
        func_decl_set& m_aux_decls;
    public:
        collect_decls_proc(func_decl_set& bound_decls, func_decl_set& aux_decls):
            m_bound_decls(bound_decls),
            m_aux_decls(aux_decls) {
        }
        
        void operator()(app* a) {
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

    expr_ref inductive_property::fixup_clause(expr* fml) const {        
        expr_ref_vector disjs(m);
        flatten_or(fml, disjs);
        expr_ref result(m);
        bool_rewriter(m).mk_or(disjs.size(), disjs.c_ptr(), result);
        return result;
    }

    expr_ref inductive_property::fixup_clauses(expr* fml) const {
        expr_ref_vector conjs(m);
        expr_ref result(m);
        flatten_and(fml, conjs);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            conjs[i] = fixup_clause(conjs[i].get());
        }
        bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), result);
        return result;
    }

    std::string inductive_property::to_string() const {
        std::stringstream stm;
        model_ref md;
        expr_ref result(m);
        to_model(md);
        model_smt2_pp(stm, m, *md.get(), 0); 
        return stm.str();
    }

    void inductive_property::to_model(model_ref& md) const {
        md = alloc(model, m);
        vector<relation_info> const& rs = m_relation_info;
        expr_ref_vector conjs(m);
        for (unsigned i = 0; i < rs.size(); ++i) {
            relation_info ri(rs[i]);
            func_decl * pred = ri.m_pred;
            expr_ref prop = fixup_clauses(ri.m_body);
            func_decl_ref_vector const& sig = ri.m_vars;
            expr_ref q(m);
            expr_ref_vector sig_vars(m);
            for (unsigned j = 0; j < sig.size(); ++j) {
                sig_vars.push_back(m.mk_const(sig[sig.size()-j-1]));
            }
            expr_abstract(m, 0, sig_vars.size(), sig_vars.c_ptr(), prop, q);
            if (sig.empty()) {
                md->register_decl(pred, q);
            }
            else {
                func_interp* fi = alloc(func_interp, m, sig.size());
                fi->set_else(q);
                md->register_decl(pred, fi);
            }
        }
        TRACE("pdr", model_smt2_pp(tout, m, *md, 0););
        apply(const_cast<model_converter_ref&>(m_mc), md);
    }

    expr_ref inductive_property::to_expr() const {
        model_ref md;
        expr_ref result(m);
        to_model(md);
        model2expr(md, result);
        return result;        
    }

    
    void inductive_property::display(datalog::rule_manager& rm, ptr_vector<datalog::rule> const& rules, std::ostream& out) const {
        func_decl_set bound_decls, aux_decls;
        collect_decls_proc collect_decls(bound_decls, aux_decls);

        for (unsigned i = 0; i < m_relation_info.size(); ++i) {
            bound_decls.insert(m_relation_info[i].m_pred);
            func_decl_ref_vector const& sig = m_relation_info[i].m_vars;
            for (unsigned j = 0; j < sig.size(); ++j) {
                bound_decls.insert(sig[j]);
            }
            for_each_expr(collect_decls, m_relation_info[i].m_body);
        }
        for (unsigned i = 0; i < rules.size(); ++i) {
            bound_decls.insert(rules[i]->get_decl());
        }
        for (unsigned i = 0; i < rules.size(); ++i) {
            unsigned u_sz = rules[i]->get_uninterpreted_tail_size();
            unsigned t_sz = rules[i]->get_tail_size();
            for (unsigned j = u_sz; j < t_sz; ++j) {
                for_each_expr(collect_decls, rules[i]->get_tail(j));
            }
        }
        smt2_pp_environment_dbg env(m);
        func_decl_set::iterator it = aux_decls.begin(), end = aux_decls.end();
        for (; it != end; ++it) {
            func_decl* f = *it;
            ast_smt2_pp(out, f, env);
            out << "\n";
        }

        out << to_string() << "\n";
        for (unsigned i = 0; i < rules.size(); ++i) {
            out << "(push)\n";
            out << "(assert (not\n";
            rm.display_smt2(*rules[i], out);
            out << "))\n";
            out << "(check-sat)\n";
            out << "(pop)\n";
        }
    }
    
    manager::manager(smt_params& fparams, unsigned max_num_contexts, ast_manager& manager) :
        m(manager),
        m_fparams(fparams),
        m_brwr(m),        
        m_mux(m),
        m_background(m.mk_true(), m),
        m_contexts(fparams, max_num_contexts, m),
        m_next_unique_num(0)
    {        
    }


    void manager::add_new_state(func_decl * s) {
        SASSERT(s->get_arity()==0); //we currently don't support non-constant states
        decl_vector vect;
        SASSERT(o_index(0)==1); //we assume this in the number of retrieved symbols
        m_mux.create_tuple(s, s->get_arity(), s->get_domain(), s->get_range(), 2, vect);
        m_o0_preds.push_back(vect[o_index(0)]);
    }
    
    func_decl * manager::get_o_pred(func_decl* s, unsigned idx)
    {
        func_decl * res = m_mux.try_get_by_prefix(s, o_index(idx));
        if(res) { return res; }
        add_new_state(s);
        res = m_mux.try_get_by_prefix(s, o_index(idx));
        SASSERT(res);
        return res;
    }
    
    func_decl * manager::get_n_pred(func_decl* s)
    {
        func_decl * res = m_mux.try_get_by_prefix(s, n_index());
        if(res) { return res; }
        add_new_state(s);
        res = m_mux.try_get_by_prefix(s, n_index());
        SASSERT(res);
        return res;
    }
    
    void manager::mk_model_into_cube(const expr_ref_vector & mdl, expr_ref & res) {
        m_brwr.mk_and(mdl.size(), mdl.c_ptr(), res);
    }
    
    void manager::mk_core_into_cube(const expr_ref_vector & core, expr_ref & res) {
        m_brwr.mk_and(core.size(), core.c_ptr(), res);
    }
    
    void manager::mk_cube_into_lemma(expr * cube, expr_ref & res) {
        m_brwr.mk_not(cube, res);
    }
    
    void manager::mk_lemma_into_cube(expr * lemma, expr_ref & res) {
        m_brwr.mk_not(lemma, res);
    }
    
    expr_ref manager::mk_and(unsigned sz, expr* const* exprs) {
        expr_ref result(m);
        m_brwr.mk_and(sz, exprs, result);
        return result;
    }
    
    expr_ref manager::mk_or(unsigned sz, expr* const* exprs) {
        expr_ref result(m);
        m_brwr.mk_or(sz, exprs, result);
        return result;
    }

    expr_ref manager::mk_not_and(expr_ref_vector const& conjs) {
        expr_ref result(m), e(m);
        expr_ref_vector es(conjs);
        flatten_and(es);
        for (unsigned i = 0; i < es.size(); ++i) {
            m_brwr.mk_not(es[i].get(), e);
            es[i] = e;
        }
        m_brwr.mk_or(es.size(), es.c_ptr(), result);
        return result;
    }
    
    void manager::get_or(expr* e, expr_ref_vector& result) {
        result.push_back(e);
        for (unsigned i = 0; i < result.size(); ) {
            e = result[i].get();
            if (m.is_or(e)) {
                result.append(to_app(e)->get_num_args(), to_app(e)->get_args());
                result[i] = result.back();
                result.pop_back();
            }
            else {
                ++i;
            }
        }
    }
    
    bool manager::try_get_state_and_value_from_atom(expr * atom0, app *& state, app_ref& value)
    {
        if(!is_app(atom0)) {
            return false;
        }
        app * atom = to_app(atom0);
        expr * arg1;
        expr * arg2;
        app * candidate_state;
        app_ref candidate_value(m);
        if(m.is_not(atom, arg1)) {
            if(!is_app(arg1)) {
                return false;
            }
            candidate_state = to_app(arg1);
            candidate_value = m.mk_false();
        }
        else if(m.is_eq(atom, arg1, arg2)) {
            if(!is_app(arg1) || !is_app(arg2)) {
                return false;
            }
            if(!m_mux.is_muxed(to_app(arg1)->get_decl())) {
                std::swap(arg1, arg2);
            }
            candidate_state = to_app(arg1);
            candidate_value = to_app(arg2);
        }
        else {
            candidate_state = atom;
            candidate_value = m.mk_true();
        }
        if(!m_mux.is_muxed(candidate_state->get_decl())) {
            return false;
        }
        state = candidate_state;
        value = candidate_value;
        return true;
    }
    
    bool manager::try_get_state_decl_from_atom(expr * atom, func_decl *& state) {
        app_ref dummy_value_holder(m);
        app * s;
        if(try_get_state_and_value_from_atom(atom, s, dummy_value_holder)) {
            state = s->get_decl();
            return true;
        }
        else {
            return false;
        }
    }       
        
    bool manager::implication_surely_holds(expr * lhs, expr * rhs, expr * bg) {
        smt::kernel sctx(m, get_fparams());
        if(bg) {
            sctx.assert_expr(bg);
        }
        sctx.assert_expr(lhs);
        expr_ref neg_rhs(m.mk_not(rhs),m);
        sctx.assert_expr(neg_rhs);
        lbool smt_res = sctx.check();
        return smt_res==l_false;
    }

};
