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
    }
    
    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) { 
        if (!a.is_array(n->get_expr())) {
            dep.insert(n, nullptr);
            return true;
        }       
        for (euf::enode* p : euf::enode_parents(n->get_root())) {
            if (a.is_default(p->get_expr())) {
                dep.add(n, p);
                continue;
            }
            if (!a.is_select(p->get_expr()))
                continue;
            dep.add(n, p);
            for (unsigned i = 1; i < p->num_args(); ++i)
                dep.add(n, p->get_arg(i));
        }
        for (euf::enode* k : euf::enode_class(n)) 
            if (a.is_const(k->get_expr())) 
                dep.add(n, k->get_arg(0)); 
        theory_var v = get_th_var(n);
        euf::enode* d = get_default(v);
        if (d)
            dep.add(n, d);
        if (!dep.deps().contains(n))
            dep.insert(n, nullptr);
        return true;
    }


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(a.is_array(n->get_expr()));
        ptr_vector<expr> args;
        sort* srt = n->get_sort();
        n = n->get_root();
        unsigned arity = get_array_arity(srt);
        func_decl * f    = mk_aux_decl_for_array_sort(m, srt);
        func_interp * fi = alloc(func_interp, m, arity);
        mdl.register_decl(f, fi);

        theory_var v = get_th_var(n);
        euf::enode* d = get_default(v);
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
        
        for (euf::enode* p : euf::enode_parents(n)) {
            if (a.is_select(p->get_expr()) && p->get_arg(0)->get_root() == n) {
                expr* value = values.get(p->get_root_id(), nullptr);
                if (!value || value == fi->get_else())
                    continue;
                args.reset();
                for (unsigned i = 1; i < p->num_args(); ++i) 
                    args.push_back(values.get(p->get_arg(i)->get_root_id()));    
                fi->insert_entry(args.data(), value);
            }
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
#if 0
        struct eq {
            solver& s;
            eq(solver& s) :s(s) {}
            bool operator()(euf::enode* n1, euf::enode* n2) const {
                SASSERT(s.a.is_select(n1->get_expr()));
                SASSERT(s.a.is_select(n2->get_expr()));
                for (unsigned i = n1->num_args(); i-- > 1; ) 
                    if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                        return false;
                return true;                
            }
        };
        struct hash {
            solver& s;
            hash(solver& s) :s(s) {}
            unsigned operator()(euf::enode* n) const {
                SASSERT(s.a.is_select(n->get_expr()));
                unsigned h = 33;
                for (unsigned i = n->num_args(); i-- > 1; )
                    h = hash_u_u(h, n->get_arg(i)->get_root_id());
                return h;
            }
        };
        eq eq_proc(*this);
        hash hash_proc(*this);
        hashtable<euf::enode*, hash, eq> table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, hash_proc, eq_proc);
        euf::enode* p2 = nullptr;
        auto maps_diff = [&](euf::enode* p, euf::enode* else_, euf::enode* r) {
            return table.find(p, p2) ? p2->get_root() != r : (else_ && else_ != r);
        };
        auto table_diff = [&](euf::enode* r1, euf::enode* r2, euf::enode* else1) {
            table.reset();
            for (euf::enode* p : euf::enode_parents(r1))
                if (a.is_select(p->get_expr()) && r1 == p->get_arg(0)->get_root())
                    table.insert(p);
            for (euf::enode* p : euf::enode_parents(r2))
                if (a.is_select(p->get_expr()) && r2 == p->get_arg(0)->get_root())
                    if (maps_diff(p, else1, p->get_root()))
                        return true;
            return false;
        };
        
        return table_diff(r1, r2, else1) || table_diff(r2, r1, else2);

#endif
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
