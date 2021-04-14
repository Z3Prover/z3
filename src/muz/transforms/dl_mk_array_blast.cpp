/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_array_blast.cpp

Abstract:

    Remove array stores from rules.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

Revision History:

--*/

#include "muz/transforms/dl_mk_array_blast.h"
#include "ast/ast_util.h"
#include "ast/scoped_proof.h"


namespace datalog {


    mk_array_blast::mk_array_blast(context & ctx, unsigned priority) : 
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()), 
        a(m),
        rm(ctx.get_rule_manager()),
        m_rewriter(m, m_params),
        m_simplifier(ctx),
        m_next_var(0) {
        m_params.set_bool("expand_select_store",true);
        m_rewriter.updt_params(m_params);
    }

    mk_array_blast::~mk_array_blast() {
    }

    bool mk_array_blast::is_store_def(expr* e, expr*& x, expr*& y) {
        if (m.is_eq(e, x, y)) {
            if (!a.is_store(y)) {
                std::swap(x,y);
            }
            if (is_var(x) && a.is_store(y)) {
                return true;
            }
        }
        return false;
    }

    expr* mk_array_blast::get_select(expr* e) const {
        while (a.is_select(e)) {
            e = to_app(e)->get_arg(0);
        }
        return e;
    }

    void mk_array_blast::get_select_args(expr* e, ptr_vector<expr>& args) const {
        while (a.is_select(e)) {
            app* ap = to_app(e);
            for (unsigned i = 1; i < ap->get_num_args(); ++i) {
                args.push_back(ap->get_arg(i));
            }
            e = ap->get_arg(0);
        }
    }
     
    bool mk_array_blast::insert_def(rule const& r, app* e, var* v) {
        //
        // For the Ackermann reduction we would like the arrays 
        // to be variables, so that variables can be 
        // assumed to represent difference (alias) 
        // classes. Ehm., Soundness of this approach depends on 
        // if the arrays are finite domains...
        // 

        if (!is_var(get_select(e))) {
            return false;
        }
        if (v) {
            m_defs.insert(e, to_var(v));
        }
        else {
            if (m_next_var == 0) {
                ptr_vector<sort> vars;
                r.get_vars(m, vars);
                m_next_var = vars.size() + 1;
            }
            v = m.mk_var(m_next_var, e->get_sort());
            m_defs.insert(e, v);
            ++m_next_var;
        }
        return true;
    }

    bool mk_array_blast::is_select_eq_var(expr* e, app*& s, var*& v) const {
        expr* x, *y;
        if (m.is_eq(e, x, y) || m.is_iff(e, x, y)) {
            if (a.is_select(y)) {
                std::swap(x,y);
            }
            if (a.is_select(x) && is_var(y)) {
                s = to_app(x);
                v = to_var(y);
                return true;
            }
        }
        return false;
    }

    
    bool mk_array_blast::ackermanize(rule const& r, expr_ref& body, expr_ref& head) {
        expr_ref_vector conjs(m), trail(m);
        flatten_and(body, conjs);
        m_defs.reset();
        m_next_var = 0;
        ptr_vector<expr> todo;
        obj_map<expr, expr*> cache;
        ptr_vector<expr> args;
        app_ref e1(m);
        app* s;
        var* v;

        // disable Ackerman reduction if head contains a non-variable or non-constant argument.
        for (unsigned i = 0; i < to_app(head)->get_num_args(); ++i) {
            expr* arg = to_app(head)->get_arg(i);            
            if (!is_var(arg) && !m.is_value(arg)) return false;
        }

        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* e = conjs[i].get();
            if (is_select_eq_var(e, s, v)) {
                todo.append(s->get_num_args(), s->get_args());
            }
            else {
                todo.push_back(e);
            }
        }
        while (!todo.empty()) {
            expr* e = todo.back();
            if (cache.contains(e)) {
                todo.pop_back();
                continue;
            }
            if (is_var(e)) {
                cache.insert(e, e);
                todo.pop_back();
                continue;
            }
            if (!is_app(e)) {
                return false;
            }
            app* ap = to_app(e);
            bool valid = true;
            args.reset();
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                expr* arg;
                if (cache.find(ap->get_arg(i), arg)) {
                    args.push_back(arg);
                }
                else {
                    todo.push_back(ap->get_arg(i));
                    valid = false;
                }
            }
            if (valid) {
                todo.pop_back();
                e1 = m.mk_app(ap->get_decl(), args.size(), args.data());
                trail.push_back(e1);
                if (a.is_select(ap)) {
                    if (m_defs.find(e1, v)) {
                        cache.insert(e, v);
                    }
                    else if (!insert_def(r, e1, nullptr)) {
                        return false;                        
                    }
                    else {
                        cache.insert(e, m_defs.find(e1));
                    }
                }
                else {
                    cache.insert(e, e1);
                }
            }            
        }
        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* e = conjs[i].get();
            if (is_select_eq_var(e, s, v)) {
                args.reset();
                for (unsigned j = 0; j < s->get_num_args(); ++j) {
                    args.push_back(cache.find(s->get_arg(j)));
                }
                e1 = m.mk_app(s->get_decl(), args.size(), args.data());
                if (!m_defs.contains(e1) && !insert_def(r, e1, v)) {
                    return false;
                }
                conjs[i] = m.mk_eq(v, m_defs.find(e1));
            }
            else {
                conjs[i] = cache.find(e);
            }
        }

        // perform the Ackermann reduction by creating implications
        // i1 = i2 => val1 = val2 for each equality pair:
        // (= val1 (select a_i i1))
        // (= val2 (select a_i i2))
        defs_t::iterator it1 = m_defs.begin(), end = m_defs.end();
        for (; it1 != end; ++it1) {
            app* a1 = it1->m_key;
            var* v1 = it1->m_value;
            defs_t::iterator it2 = it1;
            ++it2;
            for (; it2 != end; ++it2) {
                app* a2 = it2->m_key;
                var* v2 = it2->m_value;
                TRACE("dl", tout << mk_pp(a1, m) << " " << mk_pp(a2, m) << "\n";);
                if (get_select(a1) != get_select(a2)) {
                    continue;
                }
                expr_ref_vector eqs(m);
                ptr_vector<expr> args1, args2;
                get_select_args(a1, args1);
                get_select_args(a2, args2);
                for (unsigned j = 0; j < args1.size(); ++j) {
                    eqs.push_back(m.mk_eq(args1[j], args2[j]));
                }
                conjs.push_back(m.mk_implies(m.mk_and(eqs.size(), eqs.data()), m.mk_eq(v1, v2)));
            }
        }
        body = m.mk_and(conjs.size(), conjs.data());        
        m_rewriter(body);   
        return true;
    }

    bool mk_array_blast::blast(rule& r, rule_set& rules) {
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector conjs(m), new_conjs(m);
        expr_ref tmp(m);
        expr_safe_replace sub(m);
        bool change = false;
        bool inserted = false;

        for (unsigned i = 0; i < utsz; ++i) {
            new_conjs.push_back(r.get_tail(i));
        }
        for (unsigned i = utsz; i < tsz; ++i) {
            conjs.push_back(r.get_tail(i));
        }
        flatten_and(conjs);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* x, *y, *e = conjs[i].get();
            
            if (is_store_def(e, x, y)) {
                // enforce topological order consistency:
                uint_set lhs = rm.collect_vars(x);
                uint_set rhs_vars = rm.collect_vars(y);
                lhs &= rhs_vars;
                if (!lhs.empty()) {
                    TRACE("dl", tout << "unusable equality " << mk_pp(e, m) << "\n";);
                    new_conjs.push_back(e);
                }
                else {
                    sub.insert(x, y);
                    inserted = true;
                }
            }
            else {
                m_rewriter(e, tmp);
                new_conjs.push_back(tmp);
            }
        }
        if (!inserted) {
            rules.add_rule(&r);
            return false;        
        }
        expr_ref fml1(m), fml2(m), body(m), head(m);
        body = m.mk_and(new_conjs.size(), new_conjs.data());
        head = r.get_head();
        sub(body);
        m_rewriter(body);
        sub(head);
        m_rewriter(head);
        TRACE("dl", tout << body << " => " << head << "\n";);
        change = ackermanize(r, body, head);
        if (!change) {
            rules.add_rule(&r);
            return false;
        }

        fml2 = m.mk_implies(body, head);
        proof_ref p(m);
        rule_set new_rules(m_ctx);
        TRACE("dl", tout << fml2 << "\n";);
        rm.mk_rule(fml2, p, new_rules, r.name());
        

        rule_ref new_rule(rm);
        if (m_simplifier.transform_rule(new_rules.last(), new_rule)) {
            if (r.get_proof()) {
                scoped_proof _sc(m);
                rm.to_formula(r, fml1);
                p = m.mk_rewrite(fml1, fml2);
                p = m.mk_modus_ponens(r.get_proof(), p);
                new_rule->set_proof(m, p);                
            }
            rules.add_rule(new_rule.get());
            rm.mk_rule_rewrite_proof(r, *new_rule.get());
            TRACE("dl", new_rule->display(m_ctx, tout << "new rule\n"););
        }
        return true;
    }
    
    rule_set * mk_array_blast::operator()(rule_set const & source) {

        if (!m_ctx.array_blast ()) {
            return nullptr;
        }
        scoped_ptr<rule_set> rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);
        bool change = false;
        for (rule* r : source) {
            if (m_ctx.canceled())
                return nullptr;
            change = blast(*r, *rules) || change;
        }
        if (!change) {
            rules = nullptr;
        }        
        return rules.detach();        
    }

};


