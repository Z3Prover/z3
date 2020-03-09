/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe.cpp

Abstract:

    Quantifier elimination procedures 

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:


--*/

#include "qe/qe.h"
#include "smt/smt_theory.h"
#include "ast/bv_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/theory_bv.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt_pp.h"
#include "ast/expr_abstract.h"
#include "ast/rewriter/var_subst.h"
#include "ast/for_each_expr.h"
#include "ast/dl_decl_plugin.h"
#include "qe/nlarith_util.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/factor_rewriter.h"
#include "ast/expr_functors.h"
#include "ast/rewriter/quant_hoist.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_kernel.h"
#include "model/model_evaluator.h"
#include "ast/has_free_vars.h"
#include "ast/rewriter/rewriter_def.h"
#include "tactic/tactical.h"
#include "model/model_v2_pp.h"
#include "util/obj_hashtable.h"


namespace qe {
    
    class conjunctions {
        ast_manager& m;
        ptr_vector<qe_solver_plugin> m_plugins;      // family_id -> plugin

    public:
        conjunctions(ast_manager& m) : m(m) {}
        
        void add_plugin(qe_solver_plugin* p) {
            family_id fid = p->get_family_id();
            if (static_cast<family_id>(m_plugins.size()) <= fid) {
                m_plugins.resize(fid + 1);
            }
            m_plugins[fid] = p;
        }

        void get_partition(
            expr*      fml, 
            unsigned   num_vars,
            app* const* vars,
            expr_ref&  fml_closed, // conjuncts that don't contain any variables from vars.
            expr_ref&  fml_mixed,  // conjuncts that contain terms from vars and non-vars.
            expr_ref&  fml_open    // conjuncts that contain vars (mixed or pure).
            )
        {
            expr_ref_vector conjs(m);
            ast_mark visited;
            ast_mark contains_var;
            ast_mark contains_uf;
            ptr_vector<expr> todo;
            ptr_vector<expr> conjs_closed, conjs_mixed, conjs_open;
            
            flatten_and(fml, conjs);

            for (unsigned i = 0; i < conjs.size(); ++i) {
                todo.push_back(conjs[i].get());
            }
            while (!todo.empty()) {
                expr* e = todo.back();
                if (visited.is_marked(e)) {
                    todo.pop_back();
                    continue;
                }

                if (is_var(to_app(e), num_vars, vars)) {
                    contains_var.mark(e, true);
                    visited.mark(e, true);
                    todo.pop_back();
                    continue;
                }

                if (!is_app(e)) {
                    visited.mark(e, true);
                    todo.pop_back();
                    continue;
                }
                
                bool all_visited = true;
                app* a = to_app(e);
                if (is_uninterpreted(a)) {
                    contains_uf.mark(e, true);
                }
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    expr* arg = a->get_arg(i);
                    if (!visited.is_marked(arg)) {
                        all_visited = false;
                        todo.push_back(arg);
                    }
                    else {
                        if (contains_var.is_marked(arg)) {
                            contains_var.mark(e, true);
                        }
                        if (contains_uf.is_marked(arg)) {
                            contains_uf.mark(e, true);
                        }
                    }
                }
                if (all_visited) {
                    todo.pop_back();
                    visited.mark(e, true);
                }            
            }
            for (expr* e : conjs) {
                bool cv = contains_var.is_marked(e);
                bool cu = contains_uf.is_marked(e);
                if (cv && cu) {
                    conjs_mixed.push_back(e);
                    conjs_open.push_back(e);
                }
                else if (cv) {
                    conjs_open.push_back(e);
                }
                else {
                    conjs_closed.push_back(e);
                }
            }
            bool_rewriter rewriter(m);
            rewriter.mk_and(conjs_closed.size(), conjs_closed.c_ptr(), fml_closed);
            rewriter.mk_and(conjs_mixed.size(), conjs_mixed.c_ptr(), fml_mixed);
            rewriter.mk_and(conjs_open.size(), conjs_open.c_ptr(), fml_open);
            
            TRACE("qe",
                  tout << "closed\n" << mk_ismt2_pp(fml_closed, m) << "\n";
                  tout << "open\n"   << mk_ismt2_pp(fml_open,   m) << "\n";
                  tout << "mixed\n"  << mk_ismt2_pp(fml_mixed,  m) << "\n";
                  );
        }

        //
        // Partition variables into buckets.
        // The var_paritions buckets covering disjoint subsets of
        // the conjuncts. The remaining variables in vars are non-partioned.
        // 
        bool partition_vars(
            unsigned               num_vars,
            contains_app**         vars,
            unsigned               num_args,
            expr* const*           args,
            vector<unsigned_vector>& partition
            ) 
        {
            unsigned_vector contains_index;
            unsigned_vector non_shared;
            unsigned_vector non_shared_vars;
            union_find_default_ctx df;
            union_find<union_find_default_ctx> uf(df);
            
            partition.reset();
            
            for (unsigned v = 0; v < num_vars; ++v) {
                contains_app& contains_x = *vars[v];
                contains_index.reset();
                for (unsigned i = 0; i < num_args; ++i) {
                    if (contains_x(args[i])) {
                        contains_index.push_back(i);
                        TRACE("qe_verbose", tout << "var " << v << " in " << i << "\n";);
                    }                
                }
                //
                // x occurs in more than half of conjuncts.
                // Mark it as shared.
                // 
                if (2*contains_index.size() > num_args) {
                    if (partition.empty()) {
                        partition.push_back(unsigned_vector());
                    }
                    partition.back().push_back(v);
                    TRACE("qe_verbose", tout << "majority " << v << "\n";);
                    continue;
                }
                // 
                // Create partition of variables that share conjuncts.
                //
                unsigned var_x = uf.mk_var();
                SASSERT(var_x == non_shared_vars.size());
                non_shared_vars.push_back(v);
                for (unsigned i = 0; i < contains_index.size(); ++i) {
                    unsigned idx = contains_index[i];
                    if (non_shared.size() <= idx) {
                        non_shared.resize(idx+1,UINT_MAX);
                    }
                    unsigned var_y = non_shared[idx];
                    if (var_y != UINT_MAX) {
                        uf.merge(var_x, var_y);
                    }
                    else {
                        non_shared[idx] = var_x;
                    }
                }
            }
            if (non_shared_vars.empty()) {
                return false;
            }
            
            unsigned root0 = uf.find(0);
            bool is_partitioned = false;
            for (unsigned idx = 1; !is_partitioned && idx < non_shared_vars.size(); ++idx) {
                is_partitioned = (uf.find(idx) != root0);
            }
            if (!is_partitioned) {
                return false;
            }
            
            // 
            // variables are partitioned into more than one
            // class.
            // 
            
            unsigned_vector roots;
            if (!partition.empty()) {
                roots.push_back(UINT_MAX);
            }
            for (unsigned idx = 0; idx < non_shared_vars.size(); ++idx) {
                unsigned x = non_shared_vars[idx];
                unsigned r = non_shared_vars[uf.find(idx)];
                TRACE("qe_verbose", tout << "x: " << x << " r: " << r << "\n";);
                bool found = false;
                for (unsigned i = 0; !found && i < roots.size(); ++i) {
                    if (roots[i] == r) {
                        found = true;
                        partition[i].push_back(x);
                    }
                }
                if (!found) {
                    roots.push_back(r);
                    partition.push_back(unsigned_vector());
                    partition.back().push_back(x);
                }
            }            
            
            TRACE("qe_verbose", 
                  for (unsigned i = 0; i < partition.size(); ++i) {
                      for (unsigned j = 0; j < partition[i].size(); ++j) {
                          tout << " " << mk_ismt2_pp(vars[partition[i][j]]->x(), m);;
                      }
                      tout << "\n";
                  });

            SASSERT(partition.size() != 1);
            SASSERT(!partition.empty() || roots.size() > 1);

            return true;
        }

    private:
        
        bool is_var(app* x, unsigned num_vars, app* const* vars) {
            for (unsigned i = 0; i < num_vars; ++i) {
                if (vars[i] == x) {
                    return true;
                }
            }
            return false;
        }

        bool is_uninterpreted(app* a) {
            family_id fid = a->get_family_id();
            if (null_family_id == fid) {
                return true;
            }
            if (static_cast<unsigned>(fid) >= m_plugins.size()) {
                return true;
            }
            qe_solver_plugin* p = m_plugins[fid];
            if (!p) {
                return true;
            }
            return p->is_uninterpreted(a);            
        }

    };

    // ---------------
    // conj_enum

    conj_enum::conj_enum(ast_manager& m, expr* e): m(m), m_conjs(m) {
        flatten_and(e, m_conjs);
    }

    void conj_enum::extract_equalities(expr_ref_vector& eqs) {
        arith_util arith(m);
        obj_hashtable<expr> leqs;
        expr_ref_vector trail(m);
        expr_ref tmp1(m), tmp2(m);
        expr *a0, *a1;
        eqs.reset();
        conj_enum::iterator it = begin();
        for (; it != end(); ++it) {
            expr* e = *it;
            
            if (m.is_eq(e, a0, a1) && (arith.is_int(a0) || arith.is_real(a0))) {
                tmp1 = arith.mk_sub(a0, a1);
                eqs.push_back(tmp1);
            }
            else if (arith.is_le(e, a0, a1) || arith.is_ge(e, a1, a0)) {
                tmp1 = arith.mk_sub(a0, a1);
                tmp2 = arith.mk_sub(a1, a0);

                if (leqs.contains(tmp2)) {
                    eqs.push_back(tmp1);
                    TRACE("qe", tout << "found:  " << mk_ismt2_pp(tmp1, m) << "\n";);
                }
                else {
                    trail.push_back(tmp1);
                    leqs.insert(tmp1);
                    TRACE("qe_verbose", tout << "insert: " << mk_ismt2_pp(tmp1, m) << "\n";);
                }
            }
            else {
                // drop equality.
            }
        }
    }
 
    // -----------------
    // Lift ite from sub-formulas.
    //
    class lift_ite {
        ast_manager& m;
        i_expr_pred& m_is_relevant; 
        th_rewriter  m_rewriter;
        scoped_ptr<expr_replacer> m_replace;
    public:
        lift_ite(ast_manager& m, i_expr_pred& is_relevant) : 
            m(m), m_is_relevant(is_relevant), m_rewriter(m), m_replace(mk_default_expr_replacer(m)) {}

        bool operator()(expr* fml, expr_ref& result) {
            if (m.is_ite(fml)) {
                result = fml;
                return true;
            }
            app* ite;
            if (find_ite(fml, ite)) {
                expr* cond = nullptr, *th = nullptr, *el = nullptr;
                VERIFY(m.is_ite(ite, cond, th, el));
                expr_ref tmp1(fml, m), tmp2(fml, m);
                m_replace->apply_substitution(ite, th, tmp1);
                m_replace->apply_substitution(ite, el, tmp2);
                result = m.mk_ite(cond, tmp1, tmp2);
                m_rewriter(result);
                return true;
            }
            else {
                return false;
            }
        }

    private:

        bool find_ite(expr* e, app*& ite) {
            ptr_vector<expr> todo;
            ast_mark visited;
            todo.push_back(e);
            while(!todo.empty()) {
                e = todo.back();
                todo.pop_back();
                if (visited.is_marked(e)) {
                    continue;
                }        
                visited.mark(e, true);
                if (!m_is_relevant(e)) {
                    continue;
                }
                if (m.is_ite(e)) {
                    ite = to_app(e);
                    return true;
                }
                if (is_app(e)) {
                    app* a = to_app(e);
                    unsigned num_args = a->get_num_args();
                    for (unsigned i = 0; i < num_args; ++i) {
                        todo.push_back(a->get_arg(i));
                    }
                }
            }
            return false;
        }        
    };

    // convert formula to NNF.
    class nnf {
        ast_manager& m;
        i_expr_pred& m_is_relevant;
        lift_ite     m_lift_ite; 
        obj_map<expr, expr*> m_pos, m_neg; // memoize positive/negative sub-formulas
        expr_ref_vector  m_trail;          // trail for generated terms
        expr_ref_vector  m_args; 
        ptr_vector<expr> m_todo;           // stack of formulas to visit
        svector<bool>    m_pols;           // stack of polarities
        bool_rewriter    m_rewriter;
        
    public:
        nnf(ast_manager& m, i_expr_pred& is_relevant): 
            m(m), 
            m_is_relevant(is_relevant),
            m_lift_ite(m, is_relevant),
            m_trail(m),
            m_args(m),
            m_rewriter(m) {}

        void operator()(expr_ref& fml) {  
            reset();
            get_nnf(fml, true);
        }

        void reset() {
            m_todo.reset();
            m_trail.reset();
            m_pols.reset();
            m_pos.reset();
            m_neg.reset();
        }
        
    private:

        bool contains(expr* e, bool p) {
            return p?m_pos.contains(e):m_neg.contains(e);
        }

        expr* lookup(expr* e, bool p) {
            expr* r = nullptr;
            if (p && m_pos.find(e, r)) {
                return r;
            }
            if (!p && m_neg.find(e, r)) {
                return r;
            }
            m_todo.push_back(e);
            m_pols.push_back(p);
            return nullptr;
        }

        void insert(expr* e, bool p, expr* r) {
            if (p) {
                m_pos.insert(e, r);
            }
            else {
                m_neg.insert(e, r);
            }
            TRACE("nnf", 
                  tout << mk_ismt2_pp(e, m) << " " << p << "\n";
                  tout << mk_ismt2_pp(r, m) << "\n";);

            m_trail.push_back(r);
        }

        void pop() {
            m_todo.pop_back();
            m_pols.pop_back();
        }

        void nnf_iff(app* a, bool p) {
            SASSERT(m.is_iff(a) || m.is_xor(a) || m.is_eq(a));
            expr* a0 = a->get_arg(0);
            expr* a1 = a->get_arg(1);

            expr* r1 = lookup(a0, true);
            expr* r2 = lookup(a0, false);
            expr* p1 = lookup(a1, true);
            expr* p2 = lookup(a1, false);
            if (r1 && r2 && p1 && p2) {
                expr_ref tmp1(m), tmp2(m), tmp(m);
                pop();
                if (p) {
                    m_rewriter.mk_and(r1, p1, tmp1);
                    m_rewriter.mk_and(r2, p2, tmp2);
                    m_rewriter.mk_or(tmp1, tmp2, tmp);
                }
                else {
                    m_rewriter.mk_or(r1, p1, tmp1);
                    m_rewriter.mk_or(r2, p2, tmp2);
                    m_rewriter.mk_and(tmp1, tmp2, tmp);
                }
                insert(a, p, tmp);
            }                    
        }

        void nnf_ite(app* a, bool p) {
            SASSERT(m.is_ite(a));
            expr* r1 = lookup(a->get_arg(0), true);
            expr* r2 = lookup(a->get_arg(0), false);
            expr* th = lookup(a->get_arg(1), p);
            expr* el = lookup(a->get_arg(2), p);
            if (r1 && r2 && th && el) {
                expr_ref tmp1(m), tmp2(m), tmp(m);
                pop();
                m_rewriter.mk_and(r1, th, tmp1);
                m_rewriter.mk_and(r2, el, tmp2);
                m_rewriter.mk_or(tmp1, tmp2, tmp);  
                TRACE("nnf", 
                      tout << mk_ismt2_pp(a, m) << "\n";
                      tout << mk_ismt2_pp(tmp, m) << "\n";);
                insert(a, p, tmp);
            }                    
        }

        void nnf_implies(app* a, bool p) {
            SASSERT(m.is_implies(a));
            expr* r1 = lookup(a->get_arg(0), !p);
            expr* r2 = lookup(a->get_arg(1), p);
            if (r1 && r2) {
                expr_ref tmp(m);
                if (p) {
                    m_rewriter.mk_or(r1, r2, tmp);
                }
                else {
                    m_rewriter.mk_and(r1, r2, tmp);
                }
                insert(a, p, tmp);
            }
        }

        void nnf_not(app* a, bool p) {
            SASSERT(m.is_not(a));
            expr* arg = a->get_arg(0);
            expr* e = lookup(arg, !p);
            if (e) {
                insert(a, p, e);
            }
        }

        void nnf_and_or(bool is_and, app* a, bool p) {
            m_args.reset();
            unsigned num_args = a->get_num_args();
            expr_ref tmp(m);
            bool visited = true;
            for (unsigned i = 0; i < num_args; ++i) {
                expr* arg = a->get_arg(i);
                expr* r = lookup(arg, p);
                if (r) {
                    m_args.push_back(r);
                }
                else {
                    visited = false;
                }
            }
            if (visited) {
                pop();
                if ((p && is_and) || (!p && !is_and)) {
                    m_rewriter.mk_and(num_args, m_args.c_ptr(), tmp);
                }
                else {
                    m_rewriter.mk_or(num_args, m_args.c_ptr(), tmp);
                }
                insert(a, p, tmp);
            }
        }

        bool get_nnf(expr_ref& fml, bool p0) {
            TRACE("nnf", tout << mk_ismt2_pp(fml.get(), m) << "\n";);
            bool p = p0;
            unsigned sz = m_todo.size();
            expr_ref tmp(m);

            expr* e = lookup(fml, p);
            if (e) {
                fml = e;
                return true;
            }
            m_trail.push_back(fml);
            
            while (sz < m_todo.size()) {
                e = m_todo.back();
                p = m_pols.back();
                if (!m_is_relevant(e)) {
                    pop();
                    insert(e, p, p?e:mk_not(m, e));
                    continue;
                }
                if (!is_app(e)) {
                    return false;
                }
                if (contains(e, p)) {
                    pop();
                    continue;
                }
                app* a = to_app(e);
                if (m.is_and(e) || m.is_or(e)) {
                    nnf_and_or(m.is_and(a), a, p);
                }
                else if (m.is_not(a)) {
                    nnf_not(a, p);
                }
                else if (m.is_ite(a)) {
                    nnf_ite(a, p);
                }
                else if (m.is_iff(a)) {
                    nnf_iff(a, p);
                }
                else if (m.is_xor(a)) {
                    nnf_iff(a, !p);
                }
                else if (m.is_implies(a)) {
                    nnf_implies(a, p);
                }      
                else if (m_lift_ite(e, tmp)) {
                    if (!get_nnf(tmp, p)) {
                        return false;
                    }
                    pop();
                    insert(e, p, tmp);
                }
                else {
                    pop();
                    insert(e, p, p?e:mk_not(m, e));
                }

            }
            fml = lookup(fml, p0);
            SASSERT(fml.get());
            return true;
        }
    };     

    // ----------------------------------
    // Normalize literals in NNF formula.

    class nnf_normalize_literals {
        ast_manager&         m;
        i_expr_pred&         m_is_relevant;
        i_nnf_atom&          m_mk_atom;
        obj_map<expr, expr*> m_cache;
        ptr_vector<expr>     m_todo;          
        expr_ref_vector      m_trail;
        ptr_vector<expr>     m_args;
    public:
        nnf_normalize_literals(ast_manager& m, i_expr_pred& is_relevant, i_nnf_atom& mk_atom): 
            m(m), m_is_relevant(is_relevant), m_mk_atom(mk_atom), m_trail(m) {}
        
        void operator()(expr_ref& fml) {
            SASSERT(m_todo.empty());
            m_todo.push_back(fml);
            while (!m_todo.empty()) {
                expr* e = m_todo.back();                
                if (m_cache.contains(e)) {
                    m_todo.pop_back();
                }
                else if (!is_app(e)) {
                    m_todo.pop_back();
                    m_cache.insert(e, e);
                }
                else if (visit(to_app(e))) {
                    m_todo.pop_back();
                }
            }
            fml = m_cache.find(fml);
            reset();
        }

        void reset() {
            m_cache.reset();
            m_todo.reset();
            m_trail.reset();
        }

    private:

        bool visit(app* e) {
            bool all_visit = true;            
            expr* f = nullptr;
            expr_ref tmp(m);
            if (!m_is_relevant(e)) {
                m_cache.insert(e, e);               
            }
            else if (m.is_and(e) || m.is_or(e)) {
                m_args.reset();
                for (unsigned i = 0; i < e->get_num_args(); ++i) {
                    if (m_cache.find(e->get_arg(i), f)) {
                        m_args.push_back(f);
                    }
                    else {
                        all_visit = false;
                        m_todo.push_back(e->get_arg(i));
                    }
                }
                if (all_visit) {
                    m_cache.insert(e, m.mk_app(e->get_decl(), m_args.size(), m_args.c_ptr()));
                }
            }
            else if (m.is_not(e, f)) {
                SASSERT(!m.is_not(f) && !m.is_and(f) && !m.is_or(f));
                m_mk_atom(f, false, tmp);
                m_cache.insert(e, tmp);
                m_trail.push_back(tmp);
            }
            else {
                m_mk_atom(e, true, tmp);
                m_trail.push_back(tmp);
                m_cache.insert(e, tmp);
            }
            return all_visit;                
        }
    };

    // ----------------------------
    // def_vector

    void def_vector::normalize() {
        // apply nested definitions into place.
        ast_manager& m = m_vars.get_manager();
        expr_substitution sub(m);
        scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
        if (size() <= 1) {
            return;
        }
        for (unsigned i = size(); i > 0; ) {
            --i;
            expr_ref e(m);
            e = def(i);
            rep->set_substitution(&sub);
            (*rep)(e);
            sub.insert(m.mk_const(var(i)), e);
            def_ref(i) = e;
        }
    }        

    void def_vector::project(unsigned num_vars, app* const* vars) {
        obj_hashtable<func_decl> fns;
        for (unsigned i = 0; i < num_vars; ++i) {
            fns.insert(vars[i]->get_decl());
        }
        for (unsigned i = 0; i < size(); ++i) {
            if (fns.contains(m_vars[i].get())) {
                // 
                // retain only first occurrence of eliminated variable.
                // later occurrences are just recycling the name.
                // 
                fns.remove(m_vars[i].get());
            }
            else {
                for (unsigned j = i+1; j < size(); ++j) {
                    m_vars.set(j-1, m_vars.get(j));
                    m_defs.set(j-1, m_defs.get(j));
                }
                m_vars.pop_back();
                m_defs.pop_back();
                --i;
            }
        }
    }

    // ----------------------------
    // guarded_defs

    std::ostream& guarded_defs::display(std::ostream& out) const {
        ast_manager& m = m_guards.get_manager();
        for (unsigned i = 0; i < size(); ++i) {            
            for (unsigned j = 0; j < defs(i).size(); ++j) {
                out << defs(i).var(j)->get_name() << " := " << mk_pp(defs(i).def(j), m) << "\n";
            }
            out << "if " << mk_pp(guard(i), m) << "\n";
        }       
        return out;
    }

    bool guarded_defs::inv() {
        return m_defs.size() == m_guards.size();
    }

    void guarded_defs::add(expr* guard, def_vector const& defs) {
        SASSERT(inv());
        m_defs.push_back(defs);
        m_guards.push_back(guard);
        m_defs.back().normalize();
        SASSERT(inv());
    }

    void guarded_defs::project(unsigned num_vars, app* const* vars) {
        for (unsigned i = 0; i < size(); ++i) {
            m_defs[i].project(num_vars, vars);
        }
    }

    // ----------------------------
    // Obtain atoms in NNF formula.
    
    class nnf_collect_atoms {
        ast_manager&         m;
        i_expr_pred&         m_is_relevant;
        ptr_vector<expr>     m_todo;
        ast_mark             m_visited;
    public:
        nnf_collect_atoms(ast_manager& m, i_expr_pred& is_relevant):
            m(m), m_is_relevant(is_relevant) {}
        
        void operator()(expr* fml, atom_set& pos, atom_set& neg) {
            m_todo.push_back(fml);
            while (!m_todo.empty()) {
                expr* e = m_todo.back();
                m_todo.pop_back();
                if (m_visited.is_marked(e)) {
                    continue;
                }
                m_visited.mark(e, true);
                if (!is_app(e) || !m_is_relevant(e)) {
                    continue;
                }
                app* a = to_app(e);
                if (m.is_and(a) || m.is_or(a)) {
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        m_todo.push_back(a->get_arg(i));
                    }
                }
                else if (m.is_not(a, e) && is_app(e)) {
                    neg.insert(to_app(e));
                }
                else {
                    pos.insert(a);
                }
            }
            SASSERT(m_todo.empty());
            m_visited.reset();
        }        
    };


    // --------------------------------
    // Bring formula to NNF, normalize atoms, collect literals.

    class nnf_normalizer {
        nnf                    m_nnf_core;
        nnf_collect_atoms      m_collect_atoms;
        nnf_normalize_literals m_normalize_literals;
    public:
        nnf_normalizer(ast_manager& m, i_expr_pred& is_relevant, i_nnf_atom& mk_atom):
            m_nnf_core(m, is_relevant),
            m_collect_atoms(m, is_relevant),
            m_normalize_literals(m, is_relevant, mk_atom)
        {}

        void operator()(expr_ref& fml, atom_set& pos, atom_set& neg) {
            expr_ref orig(fml);
            m_nnf_core(fml);
            m_normalize_literals(fml);
            m_collect_atoms(fml, pos, neg);
            TRACE("qe",
                  ast_manager& m = fml.get_manager(); 
                  tout << mk_ismt2_pp(orig, m) << "\n-->\n" << mk_ismt2_pp(fml, m) << "\n";);
        }      

        void reset() {
            m_nnf_core.reset();
            m_normalize_literals.reset();
        }
    };

    void get_nnf(expr_ref& fml, i_expr_pred& pred, i_nnf_atom& mk_atom, atom_set& pos, atom_set& neg) {
        nnf_normalizer nnf(fml.get_manager(), pred, mk_atom);
        nnf(fml, pos, neg);
    }

    //
    // Theory plugin for quantifier elimination.
    //

    class quant_elim {
    public:
        virtual ~quant_elim() {}
    
        virtual lbool eliminate_exists(
            unsigned num_vars, app* const* vars, 
            expr_ref& fml, app_ref_vector& free_vars, bool get_first, guarded_defs* defs) = 0;

        virtual void set_assumption(expr* fml) = 0;

        virtual void collect_statistics(statistics & st) const = 0;

        virtual void eliminate(bool is_forall, unsigned num_vars, app* const* vars, expr_ref& fml) = 0;      


        virtual void updt_params(params_ref const& p) {}
        
    };

    class search_tree {
        typedef map<rational, unsigned, rational::hash_proc, rational::eq_proc> branch_map;
        ast_manager&             m;
        app_ref_vector           m_vars;         // free variables
        app_ref                  m_var;          // 0 or selected free variable
        def_vector               m_def;          // substitution for the variable eliminated relative to the parent.
        expr_ref                 m_fml;          // formula whose variables are to be eliminated
        app_ref                  m_assignment;   // assignment that got us here.
        search_tree*             m_parent;       // parent pointer
        rational                 m_num_branches; // number of possible branches
        ptr_vector<search_tree>  m_children;     // list of children
        branch_map               m_branch_index; // branch_id -> child search tree index
        atom_set                 m_pos;
        atom_set                 m_neg;
        bool                     m_pure;      // is the node pure (no variables deleted).

        // The invariant captures that search tree nodes are either 
        // - unit branches (with only one descendant), or 
        // - unassigned variable and formula
        // - assigned formula, but unassigned variable for branching
        // - assigned variable and formula with 0 or more branches.
        // 
#define CHECK_COND(_cond_) if (!(_cond_)) { TRACE("qe", tout << "violated: " << #_cond_ << "\n";); return false; }
        bool invariant() const {
            CHECK_COND(assignment());
            CHECK_COND(m_children.empty() || fml());
            CHECK_COND(!is_root() || fml());
            CHECK_COND(!fml() || has_var() || m_num_branches.is_zero() || is_unit());
            branch_map::iterator it = m_branch_index.begin(), end = m_branch_index.end();
            for (; it != end; ++it) {
                CHECK_COND(it->m_value < m_children.size());
                CHECK_COND(it->m_key < get_num_branches());
            }
            for (unsigned i = 0; i < m_children.size(); ++i) {
                CHECK_COND(m_children[i]);
                CHECK_COND(this == m_children[i]->m_parent);
                CHECK_COND(m_children[i]->invariant());
            }
            return true;
        }
#undef CHECKC_COND

    public:
        search_tree(search_tree* parent, ast_manager& m, app* assignment):
            m(m),
            m_vars(m),
            m_var(m),
            m_def(m),
            m_fml(m),
            m_assignment(assignment, m),
            m_parent(parent),
            m_pure(true)
        {}

        ~search_tree() {
            reset();
        }

        expr* fml() const { return m_fml; }

        expr_ref& fml_ref() { return m_fml; }

        def_vector const& def() const { return m_def; }

        app* assignment() const { return m_assignment; }

        app* var() const { SASSERT(has_var()); return m_var; }

        bool has_var() const { return nullptr != m_var.get(); }

        search_tree* parent() const { return m_parent; }

        bool is_root() const { return !parent(); }

        rational const& get_num_branches() const { SASSERT(has_var()); return m_num_branches; }

        // extract disjunctions
        void get_leaves(expr_ref_vector& result) {
            SASSERT(is_root());
            ptr_vector<search_tree> todo;
            todo.push_back(this);
            while (!todo.empty()) {
                search_tree* st = todo.back();
                todo.pop_back();
                if (st->m_children.empty() && st->fml() && 
                    st->m_vars.empty() && !st->has_var()) {
                    TRACE("qe", st->display(tout << "appending leaf\n");); 
                    result.push_back(st->fml());
                }
                for (auto * ch : st->m_children)
                    todo.push_back(ch);
            }
        }

        void get_leaves_rec(def_vector& defs, guarded_defs& gdefs) {
            expr* f = this->fml();
            unsigned sz = defs.size();
            defs.append(def());
            if (m_children.empty() && f && !m.is_false(f) &&
                m_vars.empty() && !has_var()) {
                gdefs.add(f, defs); 
            }
            else {
                for (unsigned i = 0; i < m_children.size(); ++i) {
                    m_children[i]->get_leaves_rec(defs, gdefs);
                }
            }
            defs.shrink(sz);
        }

        void get_leaves(guarded_defs& gdefs) {
            def_vector defs(m);
            get_leaves_rec(defs, gdefs);
        }

        void reset() {
            TRACE("qe",tout << "resetting\n";);
            for (auto* ch : m_children) dealloc(ch);
            m_pos.reset();
            m_neg.reset();
            m_children.reset();
            m_vars.reset();
            m_branch_index.reset();
            m_var = nullptr;
            m_def.reset();
            m_num_branches = rational::zero();
            m_pure = true;
        }

        void init(expr* fml) {            
            m_fml = fml;
            SASSERT(invariant());
        }

        void add_def(app* v, expr* def) {
            if (v && def) {
                m_def.push_back(v->get_decl(), def);
            }
        }

        unsigned num_free_vars() const { return m_vars.size(); }
        // app* const* free_vars() const { return m_vars.c_ptr(); }
        app_ref_vector const& free_vars() const { return m_vars; }
        app*        free_var(unsigned i) const { return m_vars[i]; }
        void        reset_free_vars() { TRACE("qe", tout << m_vars << "\n";); m_vars.reset(); }

        atom_set const& pos_atoms() const { return m_pos; }   
        atom_set const& neg_atoms() const { return m_neg; }    

        atom_set& pos_atoms() { return m_pos; }   
        atom_set& neg_atoms() { return m_neg; }    

        // set the branch variable.
        void set_var(app* x, rational const& num_branches) {
            SASSERT(!m_var.get());
            SASSERT(m_vars.contains(x));
            m_var = x;            
            m_vars.erase(x);
            m_num_branches = num_branches;
            SASSERT(invariant());
        }

        // include new variables.
        void consume_vars(app_ref_vector& vars) {
            while (!vars.empty()) {
                m_vars.push_back(vars.back());
                vars.pop_back();
            }
        }

        bool is_pure() const {
            search_tree const* node = this;
            while (node) {
                if (!node->m_pure) return false;
                node = node->parent();
            }
            return true;
        }

        bool is_unit() const { 
            return m_children.size() == 1 && 
                   m_branch_index.empty(); 
        }

        bool has_branch(rational const& branch_id) const { return m_branch_index.contains(branch_id); }

        search_tree* child(rational const& branch_id) const {
            unsigned idx = m_branch_index.find(branch_id);
            return m_children[idx];
        }

        search_tree* child() const {
            SASSERT(is_unit());
            return m_children[0];
        }

        // remove variable from branch.
        void del_var(app* x) {
            SASSERT(m_children.empty());
            SASSERT(m_vars.contains(x));
            m_vars.erase(x);
            m_pure = false;
        }

        // add branch with a given formula
        search_tree* add_child(expr* fml) {
            SASSERT(m_branch_index.empty());
            SASSERT(m_children.empty());
            m_num_branches = rational(1);
            search_tree* st = alloc(search_tree, this, m, m.mk_true());
            m_children.push_back(st);
            st->init(fml);
            st->m_vars.append(m_vars.size(), m_vars.c_ptr());
            SASSERT(invariant());
            TRACE("qe", display_node(tout); st->display_node(tout););
            return st;
        }

        search_tree* add_child(rational const& branch_id, app* assignment) {
            SASSERT(!m_branch_index.contains(branch_id));
            SASSERT(has_var());
            SASSERT(branch_id.is_nonneg() && branch_id < m_num_branches);
            unsigned index = m_children.size();
            search_tree* st = alloc(search_tree, this, m, assignment);
            m_children.push_back(st);
            m_branch_index.insert(branch_id, index);
            st->m_vars.append(m_vars.size(), m_vars.c_ptr());
            SASSERT(invariant());
            TRACE("qe", display_node(tout); st->display_node(tout););
            return st;
        }

        void display(std::ostream& out) const {
            display(out, "");
        }

        void display_node(std::ostream& out, char const* indent = "") const {
            out << indent << "node " << std::hex << this << std::dec << "\n";
            if (m_var) {
                out << indent << " var:  " << m_var << "\n";
            }
            for (app* v : m_vars) {
                out << indent << " free: " << mk_pp(v, m) << "\n";            
            }
            if (m_fml) {
                out << indent << " fml:  " << m_fml << "\n";
            }
            for (unsigned i = 0; i < m_def.size(); ++i) {
                out << indent << " def:  " << m_def.var(i)->get_name() << " = " << mk_ismt2_pp(m_def.def(i), m) << "\n";
            }
            out << indent << " branches: " << m_num_branches << "\n";
        }

        void display(std::ostream& out, char const* indent) const {
            display_node(out, indent);
            std::string new_indent(indent);
            new_indent += " ";
            for (auto * ch : m_children) {
                ch->display(out, new_indent.c_str());
            }
        }

        expr_ref abstract_variable(app* x, expr* fml) const {
            expr_ref result(m);
            expr* y = x;
            expr_abstract(m, 0, 1, &y, fml, result);            
            symbol X(x->get_decl()->get_name());
            sort* s = m.get_sort(x);
            result = m.mk_exists(1, &s, &X, result);
            return result;
        }

        void display_validate(std::ostream& out) const {
            if (m_children.empty()) {
                return;
            }
            expr_ref q(m);
            expr* x = m_var;
            if (x) {
                q = abstract_variable(m_var, m_fml);

                expr_ref_vector fmls(m);
                expr_ref fml(m);
                for (unsigned i = 0; i < m_children.size(); ++i) {
                    search_tree const& child = *m_children[i];
                    fml = child.fml();
                    if (fml) {
                        // abstract free variables in children.
                        ptr_vector<app> child_vars, new_vars;
                        child_vars.append(child.m_vars.size(), child.m_vars.c_ptr());
                        if (child.m_var) {
                            child_vars.push_back(child.m_var);
                        }
                        for (unsigned j = 0; j < child_vars.size(); ++j) {
                            if (!m_vars.contains(child_vars[j]) &&
                                !new_vars.contains(child_vars[j])) {
                                fml = abstract_variable(child_vars[j], fml);
                                new_vars.push_back(child_vars[j]);
                            }
                        }
                        fmls.push_back(fml);
                    }
                }
                bool_rewriter(m).mk_or(fmls.size(), fmls.c_ptr(), fml);
                
                fml = mk_not(m, m.mk_iff(q, fml));
                ast_smt_pp pp(m);
                out << "; eliminate " << mk_pp(m_var, m) << "\n";
                out << "(push)\n";
                pp.display_smt2(out, fml);                
                out << "(pop)\n\n";      
#if 0
                DEBUG_CODE(
                    smt_params params;
                    params.m_simplify_bit2int = true;
                    params.m_arith_enum_const_mod = true;
                    params.m_bv_enable_int2bv2int = true;
                    params.m_relevancy_lvl = 0;
                    smt::kernel ctx(m, params);
                    ctx.assert_expr(fml);
                    lbool is_sat = ctx.check();
                    if (is_sat == l_true) {
                        std::cout << "; Validation failed:\n";
                        std::cout << mk_pp(fml, m) << "\n";
                    }
                           );
#endif

            }
            for (unsigned i = 0; i < m_children.size(); ++i) {
                if (m_children[i]->fml()) {
                    m_children[i]->display_validate(out);
                }
            }
        }        
    };  

    // -------------------------
    // i_solver_context

    i_solver_context::~i_solver_context() {
        for (unsigned i = 0; i < m_plugins.size(); ++i) {
            dealloc(m_plugins[i]);
        }
    }

    bool i_solver_context::is_relevant::operator()(expr* e) {
        for (unsigned i = 0; i < m_s.get_num_vars(); ++i) {
            if (m_s.contains(i)(e)) {
                return true;
            }
        }
        TRACE("qe_verbose", tout << "Not relevant: " << mk_ismt2_pp(e, m_s.get_manager()) << "\n";);
        return false;
    }

    bool i_solver_context::is_var(expr* x, unsigned& idx) const {
        unsigned nv = get_num_vars();
        for (unsigned i = 0; i < nv; ++i) {
            if (get_var(i) == x) {
                idx = i;
                return true;
            }
        }
        return false;
    }

    void i_solver_context::add_plugin(qe_solver_plugin* p) {
        family_id fid = p->get_family_id();
        SASSERT(fid != null_family_id);
        if (static_cast<int>(m_plugins.size()) <= fid) {
            m_plugins.resize(fid+1);
        }
        SASSERT(!m_plugins[fid]);
        m_plugins[fid] = p;
    }

    bool i_solver_context::has_plugin(app* x) {
        ast_manager& m = get_manager();
        family_id fid = m.get_sort(x)->get_family_id();
        return 
            0 <= fid && 
            fid < static_cast<int>(m_plugins.size()) &&
            m_plugins[fid] != 0;
    }
    
    qe_solver_plugin& i_solver_context::plugin(app* x) {
        ast_manager& m = get_manager();
        SASSERT(has_plugin(x));
        return *(m_plugins[m.get_sort(x)->get_family_id()]);               
    }

    void i_solver_context::mk_atom(expr* e, bool p, expr_ref& result) {
        ast_manager& m = get_manager();
        TRACE("qe_verbose", tout << mk_ismt2_pp(e, m) << "\n";);
        for (unsigned i = 0; i < m_plugins.size(); ++i) {
            qe_solver_plugin* pl = m_plugins[i];
            if (pl && pl->mk_atom(e, p, result)) {
                return;
            }
        }
        TRACE("qe_verbose", tout << "No plugin for " << mk_ismt2_pp(e, m) << "\n";);
        result = p?e:mk_not(m, e);
    }

    void i_solver_context::mk_atom_fn::operator()(expr* e, bool p, expr_ref& result) {
        m_s.mk_atom(e, p, result);
    }    

    void i_solver_context::collect_statistics(statistics& st) const {
       // tbd
    }

    typedef ref_vector_ptr_hash<expr, ast_manager> expr_ref_vector_hash;
    typedef ref_vector_ptr_eq<expr, ast_manager>   expr_ref_vector_eq;
    typedef hashtable<expr_ref_vector*, expr_ref_vector_hash, expr_ref_vector_eq> clause_table;
    typedef value_trail<smt::context, unsigned> _value_trail;


    class quant_elim_plugin : public i_solver_context {

        ast_manager&                m;
        quant_elim&                 m_qe;
        th_rewriter                 m_rewriter;
        smt::kernel                 m_solver;
        bv_util                     m_bv;
        expr_ref_vector             m_literals;

        bool_rewriter               m_bool_rewriter;
        conjunctions                m_conjs;

        // maintain queue for variables.

        app_ref_vector               m_free_vars;    // non-quantified variables
        app_ref_vector               m_trail;

        expr_ref                     m_fml;
        expr_ref                     m_subfml;   

        obj_map<app, app*>           m_var2branch;   // var -> bv-var, identify explored branch.
        obj_map<app, contains_app*>  m_var2contains; // var -> contains_app
        obj_map<app, ptr_vector<app> > m_children;   // var -> list of dependent children
        search_tree                  m_root;
        search_tree*                 m_current;      // current branch
        
        vector<unsigned_vector>      m_partition;    // cached latest partition of variables.

        app_ref_vector               m_new_vars;     // variables added by solvers
        bool                         m_get_first;    // get first satisfying branch.
        guarded_defs*                m_defs;
        nnf_normalizer               m_nnf;          // nnf conversion

    
    public:

        quant_elim_plugin(ast_manager& m, quant_elim& qe, smt_params& p): 
            m(m),
            m_qe(qe),
            m_rewriter(m),
            m_solver(m, p),
            m_bv(m),        
            m_literals(m),
            m_bool_rewriter(m),
            m_conjs(m),
            m_free_vars(m),
            m_trail(m), 
            m_fml(m),
            m_subfml(m),
            m_root(nullptr, m, m.mk_true()),
            m_current(nullptr),
            m_new_vars(m),
            m_get_first(false),
            m_defs(nullptr),
            m_nnf(m, get_is_relevant(), get_mk_atom())
        {
            params_ref params;
            params.set_bool("gcd_rounding", true);
            m_rewriter.updt_params(params);
        }

        ~quant_elim_plugin() override {
            reset();
        }
        
        void reset() {
            m_free_vars.reset();
            m_trail.reset();
            obj_map<app, contains_app*>::iterator it = m_var2contains.begin(), end = m_var2contains.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
            m_var2contains.reset();
            m_var2branch.reset();
            m_root.reset();
            m_new_vars.reset();
            m_fml = nullptr;
            m_defs = nullptr;
            m_nnf.reset();
        }

        void add_plugin(qe_solver_plugin* p) {
            i_solver_context::add_plugin(p);
            m_conjs.add_plugin(p);
        }


        void check(unsigned num_vars, app* const* vars, 
                   expr* assumption, expr_ref& fml, bool get_first,
                   app_ref_vector& free_vars, guarded_defs* defs) {

            reset();
            m_solver.push();
            m_get_first = get_first;
            m_defs = defs;
            for (unsigned i = 0; i < num_vars; ++i) {
                if (has_plugin(vars[i])) {
                    add_var(vars[i]);
                }
                else {
                    m_free_vars.push_back(vars[i]);
                }
            }            
            m_root.consume_vars(m_new_vars);
            m_current = &m_root; 
            
            // set sub-formula
            m_fml = fml;
            normalize(m_fml, m_root.pos_atoms(), m_root.neg_atoms());
            expr_ref f(m_fml);
            get_max_relevant(get_is_relevant(), f, m_subfml);
            if (f.get() != m_subfml.get()) {
                m_fml = f;
                f = m_subfml;                
                m_solver.assert_expr(f);
            }
            m_root.init(f);                       
            TRACE("qe", 
                  for (unsigned i = 0; i < num_vars; ++i) tout << mk_ismt2_pp(vars[i], m) << "\n";
                  tout << mk_ismt2_pp(f, m) << "\n";);  
        
            m_solver.assert_expr(m_fml);
            if (assumption) m_solver.assert_expr(assumption);
            bool is_sat = false;   
            lbool res = l_true;
            while (res == l_true) {
                res = m_solver.check();
                if (res == l_true) {
                    is_sat = true;
                    final_check();
                }
                else {
                    break;
                }
            }
            if (res == l_undef) {
                free_vars.append(num_vars, vars);
                reset();
                m_solver.pop(1);
                return;
            }

            if (!is_sat) {
                fml = m.mk_false();
                if (m_fml.get() != m_subfml.get()) {
                    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
                    rp->apply_substitution(to_app(m_subfml.get()), fml, m_fml);
                    fml = m_fml;
                }
                reset();
                m_solver.pop(1);
                return;
            }

            if (!get_first) {
                expr_ref_vector result(m);
                m_root.get_leaves(result);
                m_bool_rewriter.mk_or(result.size(), result.c_ptr(), fml);
            }            

            if (defs) {
                m_root.get_leaves(*defs);
                defs->project(num_vars, vars);
            }
            
            TRACE("qe", 
                  tout << "result:" << mk_ismt2_pp(fml, m) << "\n";
                  tout << "input: " << mk_ismt2_pp(m_fml, m) << "\n";
                  tout << "subformula: " << mk_ismt2_pp(m_subfml, m) << "\n";
                  m_root.display(tout); 
                  m_root.display_validate(tout); 
                  tout << "free: " << m_free_vars << "\n";);

            free_vars.append(m_free_vars);
            if (!m_free_vars.empty() || m_solver.inconsistent()) {

                if (m_fml.get() != m_subfml.get()) {
                    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
                    rp->apply_substitution(to_app(m_subfml.get()), fml, m_fml);
                    fml = m_fml;
                }
            }
            reset();
            m_solver.pop(1);
            f = nullptr;
        }

        void collect_statistics(statistics& st) {
            m_solver.collect_statistics(st);
        }

    private:

        void final_check() {
            model_ref model;
            m_solver.get_model(model);
            scoped_ptr<model_evaluator> model_eval = alloc(model_evaluator, *model);

            while (true) {
                TRACE("qe", model_v2_pp(tout, *model););
                while (can_propagate_assignment(*model_eval)) {
                    propagate_assignment(*model_eval);
                }
                VERIFY(CHOOSE_VAR == update_current(*model_eval, true));
                SASSERT(m_current->fml());
                if (l_true != m_solver.check()) {
                    return;
                }
                m_solver.get_model(model);
                model_eval = alloc(model_evaluator, *model);
                search_tree* st = m_current;
                update_current(*model_eval, false);
                if (st == m_current) {
                    break;
                }
            }            
            pop(*model_eval);                    
        } 

        ast_manager& get_manager() override { return m; }

        atom_set const& pos_atoms() const override { return m_current->pos_atoms(); }

        atom_set const& neg_atoms() const override { return m_current->neg_atoms(); }

        unsigned get_num_vars() const override { return m_current->num_free_vars(); }

        app* get_var(unsigned idx) const override { return m_current->free_var(idx); }

        app_ref_vector const& get_vars() const override { return m_current->free_vars(); }

        contains_app& contains(unsigned idx) override { return contains(get_var(idx)); }

        //
        // The variable at idx is eliminated (without branching).
        // 
        void elim_var(unsigned idx, expr* _fml, expr* def) override {
            app* x = get_var(idx);
            expr_ref fml(_fml, m);
            TRACE("qe", tout << mk_pp(x,m) << " " << mk_pp(def, m) << "\n";);
            m_current->set_var(x, rational(1));
            m_current = m_current->add_child(fml);
            m_current->add_def(x, def);
            m_current->consume_vars(m_new_vars);
            normalize(*m_current);
        }
        
        void add_var(app* x) override {
            m_new_vars.push_back(x);
            if (m_var2branch.contains(x)) {
                return;
            }
            contains_app* ca = alloc(contains_app, m, x);
            m_var2contains.insert(x, ca);
            app* bv = nullptr;
            if (m.is_bool(x) || m_bv.is_bv(x)) {
                bv = x;
            }
            else {
                bv = m.mk_fresh_const("b", m_bv.mk_sort(20));
                m_trail.push_back(bv);                                    
            }
            TRACE("qe", tout << "Add branch var: " << mk_ismt2_pp(x, m) << " " << mk_ismt2_pp(bv, m) << "\n";);
            m_var2branch.insert(x, bv);
        }

        void add_constraint(bool use_current_val, expr* l1 = nullptr, expr* l2 = nullptr, expr* l3 = nullptr) override {
            search_tree* node = m_current;           
            if (!use_current_val) {
                node = m_current->parent();
            }
            m_literals.reset();
            while (node) {
                m_literals.push_back(mk_not(m, node->assignment()));
                node = node->parent();
            }    
            add_literal(l1);
            add_literal(l2);
            add_literal(l3);
            expr_ref fml(m);
            fml = m.mk_or(m_literals.size(), m_literals.c_ptr());
            TRACE("qe", tout << fml << "\n";);
            m_solver.assert_expr(fml);
        }            

        void blast_or(app* var, expr_ref& fml) override {
            m_qe.eliminate_exists(1, &var, fml, m_free_vars, false, nullptr);
        }

        lbool eliminate_exists(unsigned num_vars, app* const* vars, expr_ref& fml, bool get_first, guarded_defs* defs) {
            return m_qe.eliminate_exists(num_vars, vars, fml, m_free_vars, get_first, defs);
        }
    
    private:

        void add_literal(expr* l) {
            if (l != nullptr) {
                m_literals.push_back(l);
            }
        }

        void get_max_relevant(i_expr_pred& is_relevant, expr_ref& fml, expr_ref& subfml) {  
            if (m.is_and(fml) || m.is_or(fml)) {
                app* a = to_app(fml);
                unsigned num_args = a->get_num_args();
                ptr_buffer<expr> r_args;
                ptr_buffer<expr> i_args;
                for (unsigned i = 0; i < num_args; ++i) {
                    expr* arg = a->get_arg(i);
                    if (is_relevant(arg)) {
                        r_args.push_back(arg);
                    }
                    else {
                        i_args.push_back(arg);
                    }
                }
                if (r_args.empty() || i_args.empty()) {
                    subfml = fml;
                }
                else if (r_args.size() == 1) {
                    expr_ref tmp(r_args[0], m);
                    get_max_relevant(is_relevant, tmp, subfml);
                    i_args.push_back(tmp);
                    fml = m.mk_app(a->get_decl(), i_args.size(), i_args.c_ptr());                    
                }
                else {
                    subfml = m.mk_app(a->get_decl(), r_args.size(), r_args.c_ptr());                    
                    i_args.push_back(subfml);
                    fml = m.mk_app(a->get_decl(), i_args.size(), i_args.c_ptr());                    
                }
            }
            else {
                subfml = fml;
            }
        }

        app* get_branch_id(app* x) {
            return m_var2branch[x];
        }

        bool extract_partition(ptr_vector<app>& vars) {
            if (m_partition.empty()) {
                return false;
            }

            unsigned_vector& vec = m_partition.back();;
            for (unsigned i = 0; i < vec.size(); ++i) {
                vars.push_back(m_current->free_var(vec[i]));
            }
            m_partition.pop_back();
            return true;
        }

        enum update_status { CHOOSE_VAR, NEED_PROPAGATION };
        
        update_status update_current(model_evaluator& model_eval, bool apply) {
            SASSERT(m_fml);
            m_current = &m_root;
            rational branch, nb;
            while (true) {
                SASSERT(m_current->fml());
                if (m_current->is_unit()) {
                    m_current = m_current->child();                    
                    continue;
                }
                if (!m_current->has_var()) {
                    return CHOOSE_VAR;
                }

                app* x = m_current->var();
                app* b = get_branch_id(x);                
                nb = m_current->get_num_branches();
                expr_ref fml(m_current->fml(), m);
                if (!eval(model_eval, b, branch) || branch >= nb) {
                    TRACE("qe", tout << "evaluation failed: setting branch to 0\n";);
                    branch = rational::zero();
                }
                SASSERT(!branch.is_neg());
                if (!m_current->has_branch(branch)) {                    
                    if (apply) {                               
                        app_ref assignment(mk_eq_value(b, branch), m);
                        m_current = m_current->add_child(branch, assignment);
                        plugin(x).assign(contains(x), fml, branch);  
                        m_current->consume_vars(m_new_vars);
                    }
                    return NEED_PROPAGATION;
                }
                m_current = m_current->child(branch);
                if (m_current->fml() == nullptr) {
                    SASSERT(!m_current->has_var());
                    if (apply) {
                        expr_ref def(m);
                        plugin(x).subst(contains(x), branch, fml, m_defs?&def:nullptr);
                        SASSERT(!contains(x)(fml));
                        m_current->consume_vars(m_new_vars);
                        m_current->init(fml);
                        m_current->add_def(x, def);
                        normalize(*m_current);
                    }
                    return CHOOSE_VAR;
                }
            }
        }

        void pop(model_evaluator& model_eval) { 
            //
            // Eliminate trivial quantifiers by solving
            // variables that can be eliminated.
            // 
            solve_vars();
            expr* fml = m_current->fml();            
            // we are done splitting.
            if (m_current->num_free_vars() == 0) {
                block_assignment();
                return;
            }

            expr_ref fml_closed(m), fml_open(m), fml_mixed(m);
            unsigned num_vars = m_current->num_free_vars();
            ptr_vector<contains_app> cont;
            ptr_vector<app> vars;
            for (unsigned i = 0; i < num_vars; ++i) {
                cont.push_back(&contains(i));
                vars.push_back(m_current->free_var(i));
            }
            m_conjs.get_partition(fml, num_vars, vars.c_ptr(), fml_closed, fml_mixed, fml_open); 
            if (m.is_and(fml_open) && 
                m_conjs.partition_vars(
                    num_vars, cont.c_ptr(), 
                    to_app(fml_open)->get_num_args(), to_app(fml_open)->get_args(), 
                    m_partition)) {
                process_partition();
                return;
            }

            //
            // The closed portion of the formula
            // can be used as the quantifier-free portion, 
            // unless the current state is unsatisfiable.
            // 
            if (m.is_true(fml_mixed)) {
                SASSERT(l_false != m_solver.check());
                m_current = m_current->add_child(fml_closed);
                for (unsigned i = 0; m_defs && i < m_current->num_free_vars(); ++i) {
                    expr_ref val(m);
                    app* x = m_current->free_var(i);
                    model_eval(x, val);
                    // hack: assign may add new variables to the branch.
                    if (val == x) {
                        model_ref model;
                        lbool is_sat = m_solver.check();
                        if (is_sat == l_undef) return;
                        m_solver.get_model(model);
                        SASSERT(is_sat == l_true);
                        model_evaluator model_eval2(*model);
                        model_eval2.set_model_completion(true);
                        model_eval2(x, val);
                    }
                    TRACE("qe", tout << mk_pp(x,m) << " " << mk_pp(val, m) << "\n";);
                    m_current->add_def(x, val);
                }
                m_current->reset_free_vars();
                block_assignment();
                return;
            }
            //
            // one variable is to be processed.
            //             
            constrain_assignment();
        }

        void normalize(search_tree& st) {
            normalize(st.fml_ref(), st.pos_atoms(), st.neg_atoms());
        }

        void normalize(expr_ref& result, atom_set& pos, atom_set& neg) {
            m_rewriter(result);
            bool simplified = true;
            while (simplified) {
                simplified = false;
                for (unsigned i = 0; !simplified && i < m_plugins.size(); ++i) {
                    qe_solver_plugin* pl = m_plugins[i];
                    simplified = pl && pl->simplify(result);
                }
            }
            TRACE("qe_verbose", tout << "simp: " << mk_ismt2_pp(result.get(), m) << "\n";);
            m_nnf(result, pos, neg);
            TRACE("qe", tout << "nnf: " << mk_ismt2_pp(result.get(), m) << "\n";);
        }

        //
        // variable queuing.
        //


        // ------------------------------------------------
        // propagate the assignments to branch
        // literals to implied constraints on the 
        // variable.
        // 

        bool get_propagate_value(model_evaluator& model_eval, search_tree* node, app*& b, rational& b_val) {
            return node->has_var() && eval(model_eval, get_branch_id(node->var()), b_val);
        }

        bool can_propagate_assignment(model_evaluator& model_eval) {
            return m_fml && NEED_PROPAGATION == update_current(model_eval, false);
        }

        void propagate_assignment(model_evaluator& model_eval) {
            if (m_fml) {
                update_current(model_eval, true);
            }
        }

        //
        // evaluate the Boolean or bit-vector 'b' in
        // the current model
        //
        bool eval(model_evaluator& model_eval, app* b, rational& val) {
            unsigned bv_size;
            expr_ref res(m);
            model_eval(b, res);
            SASSERT(m.is_bool(b) || m_bv.is_bv(b));
            if (m.is_true(res)) {
                val = rational::one();
                return true;
            }
            else if (m.is_false(res)) {
                val = rational::zero();
                return true;
            }
            else if (m_bv.is_numeral(res, val, bv_size)) {
                return true;
            }
            else {
                return false;
            }
        }

        //
        // create literal 'b = r'
        //
        app* mk_eq_value(app* b, rational const& vl) {
            if (m.is_bool(b)) {
                if (vl.is_zero()) return to_app(mk_not(m, b));
                if (vl.is_one()) return b;
                UNREACHABLE();
            }        
            SASSERT(m_bv.is_bv(b));
            app_ref value(m_bv.mk_numeral(vl, m_bv.get_bv_size(b)), m);
            return m.mk_eq(b, value);
        }


        bool is_eq_value(app* e, app*& bv, rational& v) {
            unsigned sz = 0;
            if (!m.is_eq(e)) return false;
            expr* e0 = e->get_arg(0), *e1 = e->get_arg(1);
            if (!m_bv.is_bv(e0)) return false;
            if (m_bv.is_numeral(e0, v, sz) && is_app(e1)) {
                bv = to_app(e1);
                return true;
            }
            if (m_bv.is_numeral(e1, v, sz) && is_app(e0)) {
                bv = to_app(e0);
                return true;
            }
            return false;
        }

    
        // 
        // the current state is satisfiable.
        // all bound decisions have been made.
        // 
        void block_assignment() {                                
            TRACE("qe_verbose", m_solver.display(tout););             
            add_constraint(true);
        }

        //
        // The variable v is to be assigned a value in a range.
        // 
        void constrain_assignment() {
            SASSERT(m_current->fml());
            rational k;
            app* x;
            if (!find_min_weight(x, k)) {
                return;
            }

            m_current->set_var(x, k);
            TRACE("qe", tout << mk_pp(x, m) << " := " << k << "\n";);
            if (m_bv.is_bv(x)) {                
                return;
            }

            app* b = get_branch_id(x);
            //
            // Create implication:
            // 
            // assign_0 /\ ... /\ assign_{v-1} => b(v) <= k-1
            // where 
            // - assign_i is the current assignment: i = b(i)
            // - k is the number of cases for v
            //

            if (m.is_bool(b)) {
                SASSERT(k <= rational(2));    
                return;
            }
        
            SASSERT(m_bv.is_bv(b));
            SASSERT(k.is_pos());
            app_ref max_val(m_bv.mk_numeral(k-rational::one(), m_bv.get_bv_size(b)), m);
            expr_ref ub(m_bv.mk_ule(b, max_val), m);
            add_constraint(true, ub);
        }



        //
        // Process the partition stored in m_vars.
        //
        void process_partition() {
            expr_ref fml(m_current->fml(), m);
            ptr_vector<app> vars;
            bool closed = true;
            while (extract_partition(vars)) {
                lbool r = m_qe.eliminate_exists(vars.size(), vars.c_ptr(), fml, m_free_vars, m_get_first, m_defs);
                vars.reset();
                closed = closed && (r != l_undef);
            }        
            TRACE("qe", tout << fml << " free: " << m_current->free_vars() << "\n";);
            m_current->add_child(fml)->reset_free_vars();
            block_assignment(); 
        }


        // variable queueing.

        contains_app& contains(app* x) {
            return *m_var2contains[x];
        }

        bool find_min_weight(app*& x, rational& num_branches) {
            SASSERT(!m_current->has_var());
            while (m_current->num_free_vars() > 0) {
                unsigned weight = UINT_MAX;
                unsigned nv = m_current->num_free_vars();
                expr* fml = m_current->fml();
                unsigned index = 0;
                for (unsigned i = 0; i < nv; ++i) {
                    x = get_var(i);
                    if (!has_plugin(x)) {
                        break;
                    }
                    unsigned weight1 = plugin(get_var(i)).get_weight(contains(i), fml);
                    if (weight1 < weight) {
                        index = i;
                    }
                }
                x = get_var(index);
                if (has_plugin(x) && 
                    plugin(x).get_num_branches(contains(x), fml, num_branches)) {
                    return true;
                }
                TRACE("qe", tout << "setting variable " << mk_pp(x, m) << " free\n";);
                m_free_vars.push_back(x);
                m_current->del_var(x);
            }
            return false;
        }
 
        //
        // Solve for variables in fml.
        // Add a unit branch when variables are solved.
        // 
        void solve_vars() {
            bool solved = true;
            while (solved) {
                expr_ref fml(m_current->fml(), m);
                TRACE("qe", tout << fml << "\n";);
                conj_enum conjs(m, fml);
                solved = false;
                for (unsigned i = 0; !solved && i < m_plugins.size(); ++i) {
                    qe_solver_plugin* p = m_plugins[i];
                    solved = p && p->solve(conjs, fml);
                    SASSERT(m_new_vars.empty());
                }
            }
        }

    };

    // ------------------------------------------------
    // quant_elim 


    class quant_elim_new : public quant_elim {
        ast_manager&            m;
        smt_params&             m_fparams;  
        expr_ref                m_assumption;
        bool                    m_produce_models;
        ptr_vector<quant_elim_plugin> m_plugins;
        bool                     m_eliminate_variables_as_block;

    public:
        quant_elim_new(ast_manager& m, smt_params& p) :
            m(m),
            m_fparams(p),
            m_assumption(m),
            m_produce_models(m_fparams.m_model),
            m_eliminate_variables_as_block(true)
          {
          }

        ~quant_elim_new() override {
            reset();
        }
        
        void reset() {
            for (unsigned i = 0; i < m_plugins.size(); ++i) {
                dealloc(m_plugins[i]);
            }
        }
                
        void checkpoint() {
            if (m.canceled()) 
                throw tactic_exception(m.limit().get_cancel_msg());
        }


        void collect_statistics(statistics & st) const override {
            for (unsigned i = 0; i < m_plugins.size(); ++i) {
                m_plugins[i]->collect_statistics(st);
            }
        }

        void updt_params(params_ref const& p) override {
            m_eliminate_variables_as_block = p.get_bool("eliminate_variables_as_block", m_eliminate_variables_as_block);
        }
        
        void eliminate(bool is_forall, unsigned num_vars, app* const* vars, expr_ref& fml) override {
              if (is_forall) {
                  eliminate_forall_bind(num_vars, vars, fml);
              }
              else {
                  eliminate_exists_bind(num_vars, vars, fml);
              }
          }

        virtual void bind_variables(unsigned num_vars, app* const* vars, expr_ref& fml) {
            if (num_vars > 0) {
                ptr_vector<sort> sorts;
                vector<symbol> names;
                ptr_vector<app> free_vars;
                for (unsigned i = 0; i < num_vars; ++i) {
                    contains_app contains_x(m, vars[i]);
                    if (contains_x(fml)) {
                        sorts.push_back(m.get_sort(vars[i]));
                        names.push_back(vars[i]->get_decl()->get_name());
                        free_vars.push_back(vars[i]);
                    }
                }
                if (!free_vars.empty()) {
                    expr_ref tmp(m);
                    expr_abstract(m, 0, free_vars.size(), (expr*const*)free_vars.c_ptr(), fml, tmp);
                    fml = m.mk_exists(free_vars.size(), sorts.c_ptr(), names.c_ptr(), tmp, 1);
                  }
            }
        }

        void set_assumption(expr* fml) override {
            m_assumption = fml;
        }
        

        lbool eliminate_exists(
            unsigned num_vars, app* const* vars, expr_ref& fml, 
            app_ref_vector& free_vars, bool get_first, guarded_defs* defs) override {
            if (get_first) {
                return eliminate_block(num_vars, vars, fml, free_vars, get_first, defs);
            }
            if (m_eliminate_variables_as_block) {
                return eliminate_block(num_vars, vars, fml, free_vars, get_first, defs);
            }
            for (unsigned i = 0; i < num_vars; ++i) {
                lbool r = eliminate_block(1, vars+i, fml, free_vars, get_first, defs);
                switch(r) {
                case l_false: 
                    return l_false;
                case l_undef: 
                    free_vars.append(num_vars-i-1,vars+1+i);
                    return l_undef;
                default:
                    break;
                }
            }
            return l_true;
        }

    private:

        lbool eliminate_block(
            unsigned num_vars, app* const* vars, expr_ref& fml, 
            app_ref_vector& free_vars, bool get_first, guarded_defs* defs) {
              
            checkpoint();
            
            if (has_quantifiers(fml)) {
                free_vars.append(num_vars, vars);
                return l_undef;
            }
            
            flet<bool> fl1(m_fparams.m_model, true);
            flet<bool> fl2(m_fparams.m_simplify_bit2int, true);
            flet<bool> fl3(m_fparams.m_arith_enum_const_mod, true);
            flet<bool> fl4(m_fparams.m_bv_enable_int2bv2int, true);
            flet<bool> fl5(m_fparams.m_array_canonize_simplify, true);
            flet<unsigned> fl6(m_fparams.m_relevancy_lvl, 0);
            TRACE("qe", 
                  for (unsigned i = 0; i < num_vars; ++i) {
                      tout << mk_ismt2_pp(vars[i], m) << " ";
                  }
                  tout << "\n";
                  tout << mk_ismt2_pp(fml, m) << "\n";
                  );
            
            expr_ref fml0(fml, m);
            
            quant_elim_plugin* th;
            pop_context(th);                      
            
            th->check(num_vars, vars, m_assumption, fml, get_first, free_vars, defs);
            
            push_context(th);
            TRACE("qe", 
                  for (unsigned i = 0; i < num_vars; ++i) {
                      tout << mk_ismt2_pp(vars[i], m) << " ";
                  }
                  tout << "\n";
                  tout << "Input:\n" << mk_ismt2_pp(fml0, m) << "\n";
                  tout << "Result:\n" << mk_ismt2_pp(fml, m) << "\n";);
            
            if (m.is_false(fml)) {
                return l_false;
            }
            if (free_vars.empty()) {
                return l_true;
            }
            return l_undef;
        }

        void pop_context(quant_elim_plugin*& th) {
            if (m_plugins.empty()) {
                th = alloc(quant_elim_plugin, m, *this, m_fparams);
                th->add_plugin(mk_bool_plugin(*th));
                th->add_plugin(mk_bv_plugin(*th)); 
                th->add_plugin(mk_arith_plugin(*th, m_produce_models, m_fparams));
                th->add_plugin(mk_array_plugin(*th)); 
                th->add_plugin(mk_datatype_plugin(*th)); 
                th->add_plugin(mk_dl_plugin(*th)); 
            }
            else {
                th = m_plugins.back();
                m_plugins.pop_back();
            }        
        }

        void push_context(quant_elim_plugin* th) {
            m_plugins.push_back(th);
            th->reset();
        }

        void eliminate_exists_bind(unsigned num_vars, app* const* vars, expr_ref& fml) {
            checkpoint();
            app_ref_vector free_vars(m);
            eliminate_exists(num_vars, vars, fml, free_vars, false, nullptr);
            bind_variables(free_vars.size(), free_vars.c_ptr(), fml);
        }

        void eliminate_forall_bind(unsigned num_vars, app* const* vars, expr_ref& fml) {
            expr_ref tmp(m);
            bool_rewriter rw(m);
            rw.mk_not(fml, tmp);
            eliminate_exists_bind(num_vars, vars, tmp);
            rw.mk_not(tmp, fml);
        }

    };

    // ------------------------------------------------
    // expr_quant_elim

    expr_quant_elim::expr_quant_elim(ast_manager& m, smt_params const& fp, params_ref const& p):
        m(m),
        m_fparams(fp),
        m_params(p),
        m_trail(m),
        m_qe(nullptr),
        m_assumption(m.mk_true())
    {
    }

    expr_quant_elim::~expr_quant_elim() {
        dealloc(m_qe);
    }

    void expr_quant_elim::operator()(expr* assumption, expr* fml, expr_ref& result) {
        TRACE("qe", 
              if (assumption) tout << "elim assumption\n" << mk_ismt2_pp(assumption, m) << "\n";
              tout << "elim input\n"  << mk_ismt2_pp(fml, m) << "\n";);
        expr_ref_vector bound(m);
        result = fml;
        m_assumption = assumption;
        instantiate_expr(bound, result);
        elim(result);
        m_trail.reset();
        m_visited.reset();
        abstract_expr(bound.size(), bound.c_ptr(), result);
        TRACE("qe", tout << "elim result\n" << mk_ismt2_pp(result, m) << "\n";);
    }

    void expr_quant_elim::updt_params(params_ref const& p) {
        init_qe();
        m_qe->updt_params(p);
    }

    void expr_quant_elim::collect_param_descrs(param_descrs& r) {
        r.insert("eliminate_variables_as_block", CPK_BOOL, 
                 "(default: true) eliminate variables as a block (true) or one at a time (false)");
    }

    void expr_quant_elim::init_qe() {
        if (!m_qe) {
            m_qe = alloc(quant_elim_new, m, const_cast<smt_params&>(m_fparams));
        }
    }


    void expr_quant_elim::instantiate_expr(expr_ref_vector& bound, expr_ref& fml) {
        expr_free_vars fv;
        fv(fml);
        fv.set_default_sort(m.mk_bool_sort());
        if (!fv.empty()) {
            expr_ref tmp(m);
            for (unsigned i = fv.size(); i > 0;) {
                --i;
                bound.push_back(m.mk_fresh_const("bound", fv[i]));
            }
            var_subst subst(m);
            fml = subst(fml, bound.size(), bound.c_ptr());
        }
    }

    void expr_quant_elim::abstract_expr(unsigned sz, expr* const* bound, expr_ref& fml) {
        if (sz > 0) {
            expr_ref tmp(m);
            expr_abstract(m, 0, sz, bound, fml, tmp);
            fml = tmp;
        }    
    }

    void extract_vars(quantifier* q, expr_ref& new_body, app_ref_vector& vars) {
        ast_manager& m = new_body.get_manager();
        expr_ref tmp(m);
        unsigned nd = q->get_num_decls();
        for (unsigned i = 0; i < nd; ++i) {
            vars.push_back(m.mk_fresh_const("x",q->get_decl_sort(i)));
        }
        expr* const* exprs = (expr* const*)(vars.c_ptr());
        var_subst subst(m);
        tmp = subst(new_body, vars.size(), exprs);
        inv_var_shifter shift(m);
        shift(tmp, vars.size(), new_body);        
    }

    void expr_quant_elim::elim(expr_ref& result) {
        expr_ref tmp(m);
        ptr_vector<expr> todo;

        m_trail.push_back(result);
        todo.push_back(result);
        expr* e = nullptr, *r = nullptr;

        while (!todo.empty()) {
            e = todo.back();
            if (m_visited.contains(e)) {
                todo.pop_back();
                continue;            
            }

            switch(e->get_kind()) {
            case AST_APP: {
                app* a = to_app(e);
                expr_ref_vector args(m);
                bool all_visited = true;
                for (expr* arg : *a) {
                    if (m_visited.find(arg, r)) {
                        args.push_back(r);
                    }
                    else {
                        todo.push_back(arg);
                        all_visited = false;
                    }
                }
                if (all_visited) {
                    r = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
                    todo.pop_back();
                    m_trail.push_back(r);
                    m_visited.insert(e, r);
                }
                break;
            }
            case AST_QUANTIFIER: {
                app_ref_vector vars(m);
                quantifier* q = to_quantifier(e);
                if (is_lambda(q)) {
                    tmp = e;
                }
                else {
                    bool is_fa = is_forall(q);
                    tmp = q->get_expr();
                    extract_vars(q, tmp, vars);
                    elim(tmp);
                    init_qe();
                    m_qe->set_assumption(m_assumption);
                    m_qe->eliminate(is_fa, vars.size(), vars.c_ptr(), tmp);
                }
                m_trail.push_back(tmp);
                m_visited.insert(e, tmp);
                todo.pop_back();
                break;
            }
            default:
                UNREACHABLE();
                break;
            }        
        }

        VERIFY (m_visited.find(result, e));
        result = e;
    }

    void expr_quant_elim::collect_statistics(statistics & st) const {
        if (m_qe) {
            m_qe->collect_statistics(st);
        }
    }

    lbool expr_quant_elim::first_elim(unsigned num_vars, app* const* vars, expr_ref& fml, def_vector& defs) {
        app_ref_vector fvs(m);
        init_qe();
        guarded_defs gdefs(m);
        lbool res = m_qe->eliminate_exists(num_vars, vars, fml, fvs, true, &gdefs);
        if (gdefs.size() > 0) {
            defs.reset();
            defs.append(gdefs.defs(0));
            fml = gdefs.guard(0);
        }
        return res;
    }

    bool expr_quant_elim::solve_for_var(app* var, expr* fml, guarded_defs& defs) {
        return solve_for_vars(1,&var, fml, defs);
    }

    bool expr_quant_elim::solve_for_vars(unsigned num_vars, app* const* vars, expr* _fml, guarded_defs& defs) {
        app_ref_vector fvs(m);
        expr_ref fml(_fml, m);
        TRACE("qe", tout << mk_pp(fml, m) << "\n";);
        init_qe();  
        lbool is_sat = m_qe->eliminate_exists(num_vars, vars, fml, fvs, false, &defs);
        return is_sat != l_undef;
    }





#if 0
    // ------------------------------------------------
    // expr_quant_elim_star1

    bool expr_quant_elim_star1::visit_quantifier(quantifier * q) {
        if (!is_target(q)) {
            return true;
        }
        bool visited = true;
        visit(q->get_expr(), visited);
        return visited;
    }

    void expr_quant_elim_star1::reduce1_quantifier(quantifier * q) {
        if (!is_target(q)) {
            cache_result(q, q, 0); 
            return;
        }

        quantifier_ref new_q(m);
        expr * new_body = 0;
        proof * new_pr;
        get_cached(q->get_expr(), new_body, new_pr);
        new_q = m.update_quantifier(q, new_body);
        expr_ref r(m);
        m_quant_elim(m_assumption, new_q, r);
        if (q == r.get()) {
            cache_result(q, q, 0);
            return;
        }
        proof_ref pr(m);
        if (m.proofs_enabled()) {
            pr = m.mk_rewrite(q, r); // TODO: improve justification
        }
        cache_result(q, r, pr); 
    }

    expr_quant_elim_star1::expr_quant_elim_star1(ast_manager& m, smt_params const& p): 
        simplifier(m), m_quant_elim(m, p), m_assumption(m.mk_true())
    {
    }
#endif


    void hoist_exists(expr_ref& fml, app_ref_vector& vars) {
        quantifier_hoister hoister(fml.get_manager());
        hoister.pull_exists(fml, vars, fml);
    }

    void mk_exists(unsigned num_bound, app* const* vars, expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        expr_ref tmp(m);
        expr_abstract(m, 0, num_bound, (expr*const*)vars, fml, tmp);
        ptr_vector<sort> sorts;
        svector<symbol> names;
        for (unsigned i = 0; i < num_bound; ++i) {
            sorts.push_back(vars[i]->get_decl()->get_range());
            names.push_back(vars[i]->get_decl()->get_name());
        }
        if (num_bound > 0) {
            tmp = m.mk_exists(num_bound, sorts.c_ptr(), names.c_ptr(), tmp, 1);
        }
        fml = tmp;
    }

    
    class simplify_solver_context : public i_solver_context {
        ast_manager&             m;
        smt_params               m_fparams;
        app_ref_vector*          m_vars;
        expr_ref*                m_fml;
        ptr_vector<contains_app> m_contains;
        atom_set                 m_pos;
        atom_set                 m_neg;
    public:
        simplify_solver_context(ast_manager& m):
            m(m), 
            m_vars(nullptr),
            m_fml(nullptr)
        {
            add_plugin(mk_bool_plugin(*this));
            add_plugin(mk_arith_plugin(*this, false, m_fparams));
        }

        void updt_params(params_ref const& p) {
            m_fparams.updt_params(p);
        }

        ~simplify_solver_context() override { reset(); }
        

        void solve(expr_ref& fml, app_ref_vector& vars) {
            init(fml, vars);
            bool solved  = true;
            do {
                conj_enum conjs(m, fml);
                solved = false;
                for (unsigned i = 0; !solved && i < m_plugins.size(); ++i) {
                    qe_solver_plugin* p = m_plugins[i];
                    solved = p && p->solve(conjs, fml);
                }                
                TRACE("qe", tout << (solved?"solved":"not solved") << "\n";
                            if (solved) tout << mk_ismt2_pp(fml, m) << "\n";);
            }
            while (solved);
        }

        ast_manager& get_manager() override { return m; }

        atom_set const& pos_atoms() const override { return m_pos; }
        atom_set const& neg_atoms() const override { return m_neg; }

        // Access current set of variables to solve
        unsigned    get_num_vars() const override { return m_vars->size(); }
        app*        get_var(unsigned idx) const override { return (*m_vars)[idx].get(); }
        app_ref_vector const&  get_vars() const override { return *m_vars; }
        bool        is_var(expr* e, unsigned& idx) const override {
            for (unsigned i = 0; i < m_vars->size(); ++i) {
                if ((*m_vars)[i].get() == e) { 
                    idx = i; 
                    return true; 
                }
            }
            return false;
        }

        contains_app& contains(unsigned idx) override {
            return *m_contains[idx];
        }

        // callback to replace variable at index 'idx' with definition 'def' and updated formula 'fml'
        void elim_var(unsigned idx, expr* fml, expr* def) override {
            TRACE("qe", tout << mk_pp(m_vars->get(idx), m) << " " << mk_pp(fml, m) << "\n";);
            *m_fml = fml;
            m_vars->set(idx, m_vars->get(m_vars->size()-1));
            m_vars->pop_back();
            dealloc(m_contains[idx]);
            m_contains[idx] = m_contains[m_contains.size()-1];
            m_contains.pop_back();
        }

        // callback to add new variable to branch.
        void add_var(app* x) override {
            TRACE("qe", tout << "add var: " << mk_pp(x, m) << "\n";);
            m_vars->push_back(x);
        }

        // callback to add constraints in branch.
        void add_constraint(bool use_var, expr* l1 = nullptr, expr* l2 = nullptr, expr* l3 = nullptr) override {
            UNREACHABLE();
        }
        // eliminate finite domain variable 'var' from fml.
        void blast_or(app* var, expr_ref& fml) override {
            UNREACHABLE();
        }

    private:
        void reset() {
            for (unsigned i = 0; i < m_contains.size(); ++i) {
                dealloc (m_contains[i]);
            }  
            m_contains.reset();
        }

        void init(expr_ref& fml, app_ref_vector& vars) {
            reset();
            m_fml = &fml;
            m_vars = &vars;
            for (unsigned i = 0; i < vars.size(); ++i) {
                m_contains.push_back(alloc(contains_app, m, vars[i].get()));
            }
        }
    };

    class simplify_rewriter_cfg::impl {
        ast_manager& m;
        simplify_solver_context m_ctx;
    public:
        impl(ast_manager& m) : m(m), m_ctx(m) {}

        void updt_params(params_ref const& p) {
            m_ctx.updt_params(p);
        }

        void collect_statistics(statistics & st) const {
            m_ctx.collect_statistics(st);
        }

        bool reduce_quantifier(
            quantifier * old_q, 
            expr * new_body, 
            expr * const * new_patterns, 
            expr * const * new_no_patterns,
            expr_ref &  result,
            proof_ref & result_pr
            ) 
        {
            
            if (is_lambda(old_q)) {
                return false;
            }
            // bool is_forall = old_q->is_forall();
            app_ref_vector vars(m);
            TRACE("qe", tout << "simplifying" << mk_pp(new_body, m) << "\n";);
            result = new_body;
            extract_vars(old_q, result, vars);
            TRACE("qe", tout << "variables extracted" << mk_pp(result, m) << "\n";);

            if (is_forall(old_q)) {
                result = mk_not(m, result);
            }
            m_ctx.solve(result, vars);
            if (is_forall(old_q)) {
                expr* e = nullptr;
                result = m.is_not(result, e)?e:mk_not(m, result);
            }       
            var_shifter shift(m);
            shift(result, vars.size(), result);
            expr_abstract(m, 0, vars.size(), (expr*const*)vars.c_ptr(), result, result);
            TRACE("qe", tout << "abstracted" << mk_pp(result, m) << "\n";);
            ptr_vector<sort> sorts;
            svector<symbol> names;
            for (unsigned i = 0; i < vars.size(); ++i) {
                sorts.push_back(vars[i]->get_decl()->get_range());
                names.push_back(vars[i]->get_decl()->get_name());
            }
            if (!vars.empty()) {
                result = m.mk_quantifier(old_q->get_kind(), vars.size(), sorts.c_ptr(), names.c_ptr(), result, 1);
            }            
            result_pr = nullptr;
            return true;
        }

    };

    simplify_rewriter_cfg::simplify_rewriter_cfg(ast_manager& m) {
        imp = alloc(simplify_rewriter_cfg::impl, m);
    }

    simplify_rewriter_cfg::~simplify_rewriter_cfg() {
        dealloc(imp);
    }
    
    bool simplify_rewriter_cfg::reduce_quantifier(
        quantifier * old_q, 
        expr * new_body, 
        expr * const * new_patterns, 
        expr * const * new_no_patterns,
        expr_ref &  result,
        proof_ref & result_pr
        ) {
        return imp->reduce_quantifier(old_q, new_body, new_patterns, new_no_patterns, result, result_pr);
    }

    void simplify_rewriter_cfg::updt_params(params_ref const& p) {
        imp->updt_params(p);
    }

    void simplify_rewriter_cfg::collect_statistics(statistics & st) const {
        imp->collect_statistics(st);
    }

    bool simplify_rewriter_cfg::pre_visit(expr* e) {
        if (!is_quantifier(e)) return true;
        quantifier * q = to_quantifier(e);
        return (q->get_num_patterns() == 0 && q->get_num_no_patterns() == 0);
    }
    
    void simplify_exists(app_ref_vector& vars, expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        simplify_solver_context ctx(m);
        ctx.solve(fml, vars);       
    }
}


template class rewriter_tpl<qe::simplify_rewriter_cfg>;


