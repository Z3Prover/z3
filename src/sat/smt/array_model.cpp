/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_model.cpp

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "model/array_factory.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {


    void solver::init_model() {
        collect_defaults();
        collect_selects();
    }

    void solver::finalize_model(model& mdl) {
        std::for_each(m_selects_range.begin(), m_selects_range.end(), delete_proc<select_set>());
    }
    
    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!a.is_array(n->get_expr())) {
            dep.insert(n, nullptr);
            return true;
        }
        if (a.is_array(n->get_expr())) {
            for (euf::enode* p : euf::enode_parents(n->get_root())) 
                if (a.is_default(p->get_expr())) 
                    dep.add(n, p);
                            
            for (euf::enode* p : *get_select_set(n)) {
                dep.add(n, p);
                for (unsigned i = 1; i < p->num_args(); ++i)
                    dep.add(n, p->get_arg(i));
            }
        }
        for (euf::enode* k : euf::enode_class(n)) 
            if (a.is_const(k->get_expr())) 
                dep.add(n, k->get_arg(0));
        theory_var v = get_th_var(n);
        euf::enode* d = get_default(v);
        if (d)
            dep.add(n, d);
        if (!dep.contains_dep(n))
            dep.insert(n, nullptr);
        return true;
    }


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(a.is_array(n->get_expr()));
        ptr_vector<expr> args;
        sort* srt = n->get_sort();
        n = n->get_root();
        if (a.is_as_array(n->get_expr())) {
            values.set(n->get_expr_id(), n->get_expr());
            return;
        }
        theory_var v = get_th_var(n);
        euf::enode* d = get_default(v);

        if (a.is_const(n->get_expr())) {
            expr* val = values.get(d->get_root_id());
            SASSERT(val);
            values.set(n->get_expr_id(), a.mk_const_array(n->get_sort(), val));
            return;
        }
        
        unsigned arity = get_array_arity(srt);
        func_decl * f    = mk_aux_decl_for_array_sort(m, srt);
        func_interp * fi = alloc(func_interp, m, arity);
        mdl.register_decl(f, fi);

        if (d && !fi->get_else())
            fi->set_else(values.get(d->get_root_id()));

        if (!fi->get_else() && get_else(v))
            fi->set_else(get_else(v));
    
        if (!fi->get_else()) {
            expr* else_value = nullptr;
            unsigned max_occ_num = 0;
            obj_map<expr, unsigned> num_occ;
            for (euf::enode* p : euf::enode_parents(n->get_root())) {
                if (a.is_select(p->get_expr()) && p->get_arg(0)->get_root() == n->get_root()) {
                    expr* v = values.get(p->get_root_id(), nullptr);
                    if (!v)
                        continue;
                    unsigned no = 0;
                    num_occ.find(v, no);
                    ++no;
                    num_occ.insert(v, no);
                    if (no > max_occ_num) {
                        else_value = v;
                        max_occ_num = no;
                    }
                }
            }
            if (else_value)
                fi->set_else(else_value);
        }

        if (!get_else(v) && fi->get_else())
            set_else(v, fi->get_else());

        if (!get_else(v)) {
            expr* else_value = mdl.get_some_value(get_array_range(srt));
            fi->set_else(else_value);
            set_else(v, else_value);
        }

        for (euf::enode* p : *get_select_set(n)) {
            expr* value = values.get(p->get_root_id(), nullptr);
            if (!value || value == fi->get_else())
                continue;
            args.reset();
            for (unsigned i = 1; i < p->num_args(); ++i) {
                if (!values.get(p->get_arg(i)->get_root_id())) {
                    TRACE("array", tout << ctx.bpp(p->get_arg(i)) << "\n");
                }
                SASSERT(values.get(p->get_arg(i)->get_root_id()));
            }
            for (unsigned i = 1; i < p->num_args(); ++i) 
                args.push_back(values.get(p->get_arg(i)->get_root_id()));    
            fi->insert_entry(args.data(), value);
        }
        
        TRACE("array", tout << "array-as-function " << ctx.bpp(n) << " := " << mk_pp(f, m) << "\n" << "default " << mk_pp(fi->get_else(), m) << "\n";);
        parameter p(f);
        values.set(n->get_expr_id(), m.mk_app(get_id(), OP_AS_ARRAY, 1, &p));
    }


    bool solver::must_have_different_model_values(theory_var v1, theory_var v2) {
        euf::enode* else1 = nullptr, * else2 = nullptr;
        euf::enode* n1 = var2enode(v1);
        expr* e1 = n1->get_expr();
        if (!a.is_array(e1))
            return true;
        
        else1 = get_default(v1);
        else2 = get_default(v2);
        if (else1 && else2 && else1->get_root() != else2->get_root() && has_large_domain(e1))
            return true;

        return false;
    }

    unsigned solver::sel_hash::operator()(euf::enode * n) const {
        return get_composite_hash<euf::enode *, sel_khasher, sel_chasher>(n, n->num_args() - 1, sel_khasher(), sel_chasher());
    }

    bool solver::sel_eq::operator()(euf::enode * n1, euf::enode * n2) const {
        SASSERT(n1->num_args() == n2->num_args());
        unsigned num_args = n1->num_args();
        for (unsigned i = 1; i < num_args; i++) 
            if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                return false;
        return true;
    }


    void solver::collect_selects() {
        int num_vars = get_num_vars();

        m_selects.reset();
        m_selects_domain.reset();
        m_selects_range.reset();

        for (theory_var v = 0; v < num_vars; ++v) {
            euf::enode * r = var2enode(v)->get_root();                
            if (is_representative(v) && ctx.is_relevant(r)) {
                for (euf::enode * parent : euf::enode_parents(r)) {
                    if (parent->get_cg() == parent &&
                        ctx.is_relevant(parent) &&
                        a.is_select(parent->get_expr()) &&
                        parent->get_arg(0)->get_root() == r) {
                        select_set * s = get_select_set(r);
                        SASSERT(!s->contains(parent) || (*(s->find(parent)))->get_root() == parent->get_root());
                        s->insert(parent);
                    }
                }
            }
        }
        euf::enode_pair_vector todo;
        for (euf::enode * r : m_selects_domain)
            for (euf::enode* sel : *get_select_set(r))
                propagate_select_to_store_parents(r, sel, todo);
        for (unsigned qhead = 0; qhead < todo.size(); qhead++) {
            euf::enode_pair & pair = todo[qhead];
            euf::enode * r   = pair.first;
            euf::enode * sel = pair.second;
            propagate_select_to_store_parents(r, sel, todo);
        }
    }

    void solver::propagate_select_to_store_parents(euf::enode* r, euf::enode* sel, euf::enode_pair_vector& todo) {
        SASSERT(r->get_root() == r);
        SASSERT(a.is_select(sel->get_expr()));
        if (!ctx.is_relevant(r)) 
            return;
        
        for (euf::enode * parent : euf::enode_parents(r)) {
            if (ctx.is_relevant(parent) &&
                a.is_store(parent->get_expr()) &&
                parent->get_arg(0)->get_root() == r) {
                // propagate upward
                select_set * parent_sel_set = get_select_set(parent);
                euf::enode * parent_root = parent->get_root();
                
                if (parent_sel_set->contains(sel))
                    continue;

                SASSERT(sel->num_args() + 1 == parent->num_args());
                    
                // check whether the sel idx was overwritten by the store
                unsigned num_args = sel->num_args();
                unsigned i = 1;
                for (; i < num_args; i++) {
                    if (sel->get_arg(i)->get_root() != parent->get_arg(i)->get_root())
                        break;
                }

                if (i < num_args) {
                    SASSERT(!parent_sel_set->contains(sel) || (*(parent_sel_set->find(sel)))->get_root() == sel->get_root());
                    parent_sel_set->insert(sel);
                    todo.push_back(std::make_pair(parent_root, sel));
                }
            }
        }
    }

    solver::select_set* solver::get_select_set(euf::enode* n) {
        euf::enode * r = n->get_root();
        select_set * set = nullptr;
        m_selects.find(r, set);
        if (set == nullptr) {
            set = alloc(select_set);
            m_selects.insert(r, set);
            m_selects_domain.push_back(r);
            m_selects_range.push_back(set);
        }
        return set;
    }

    void solver::collect_defaults() {
        unsigned num_vars = get_num_vars();
        m_defaults.reset();
        m_else_values.reset();
        m_parents.reset();
        m_parents.resize(num_vars, -1);
        m_defaults.resize(num_vars);
        m_else_values.resize(num_vars);
    
        //
        // Create equivalence classes for defaults.
        //
        for (unsigned v = 0; v < num_vars; ++v) {
            euf::enode * n  = var2enode(v);
            expr* e = n->get_expr();
                       
            theory_var r = get_representative(v);

            mg_merge(v, r);

            if (a.is_const(e)) 
                set_default(v, n->get_arg(0));
            else if (a.is_store(e)) {
                theory_var w = get_th_var(n->get_arg(0));
                SASSERT(w != euf::null_theory_var);
                mg_merge(v, get_representative(w));                                
                TRACE("array", tout << "merge: " << ctx.bpp(n) << " " << v << " " << w << "\n";);
            }
            else if (a.is_default(e)) {
                theory_var w = get_th_var(n->get_arg(0));
                SASSERT(w != euf::null_theory_var);
                set_default(w, n);
            }
        }
    }

    void solver::set_default(theory_var v, euf::enode* n) {
        v = mg_find(v);
        CTRACE("array", !m_defaults[v], tout << "set default: " << v << " " << ctx.bpp(n) << "\n";);
        if (!m_defaults[v]) 
            m_defaults[v] = n;
    }

    euf::enode* solver::get_default(theory_var v) {
        return m_defaults[mg_find(v)];
    }

    void solver::set_else(theory_var v, expr* e) {
        m_else_values[mg_find(v)] = e;
    }

    expr* solver::get_else(theory_var v) {
        return m_else_values[mg_find(v)];
    }

    euf::theory_var solver::mg_find(theory_var n) {
        if (m_parents[n] < 0) 
            return n;
        theory_var n0 = n;
        n = m_parents[n0];
        if (m_parents[n] < -1) 
            return n;
        while (m_parents[n] >= 0) 
            n = m_parents[n];        
        // compress path.
        while (m_parents[n0] >= 0) {
            theory_var n1 = m_parents[n0];
            m_parents[n0] = n;
            n0 = n1;
        }
        return n;
    }

    void solver::mg_merge(theory_var u, theory_var v) {
        u = mg_find(u);
        v = mg_find(v);
        if (u != v) {
            SASSERT(m_parents[u] < 0);
            SASSERT(m_parents[v] < 0);
            if (m_parents[u] > m_parents[v]) 
                std::swap(u, v);
            m_parents[u] += m_parents[v];
            m_parents[v] = u;

            if (!m_defaults[u]) 
                m_defaults[u] = m_defaults[v];

            CTRACE("array", m_defaults[v], 
                   tout << ctx.bpp(m_defaults[v]->get_root()) << "\n";
                   tout << ctx.bpp(m_defaults[u]->get_root()) << "\n";
                  );

            // NB. it may be the case that m_defaults[u] != m_defaults[v]
            //     when m and n are finite arrays.

        }
    }



}
