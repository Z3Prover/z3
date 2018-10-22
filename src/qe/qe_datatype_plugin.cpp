
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

// ---------------------
// datatypes
// Quantifier elimination routine for recursive data-types.
// 


//
// reduce implementation is modeled after Hodges:
// subst implementation is using QE "for dummies".

// for dummies:
// -----------
// 
// Step 1. ensure x is recognized.
// 
//    exists x . phi[x] -> \/_i exists x. R_C(x) & phi[x]    
// 
// Step 2. non-recursive data-types
// 
//    exists x . R_C(x) & phi[x] -> exists y . phi[C(y)]
// 
// Step 2. recursive data-types, eliminate selectors.
// 
//   exists x . R_C(x) & phi[x] -> exists y . phi[C(y)], x occurs with sel^C_i(x)
//
// Step 3. (recursive data-types)
//   
//   Solve equations 
//             . C[t] = C[s]   -> t = s
//             . C[x,t] = y    -> x = s1(y) /\ t = s2(y) /\ R_C(y) 
//             . C[x,t] != y   -> can remain 
// 
// The remaining formula is in NNF where occurrences of 'x' are of the form
//      x = t_i or t[x] != s_j
// 
// The last normalization step is:
// 
//   exists x . R_C(x) & phi[x = t_i, t[x] != s_j]
// 
//   -> \/_i R_C(t_i) & phi[t_i/x]  \/ phi[false, true]
// 
//  Justification: 
//  - We will assume that each of t_i, s_j are constructor terms.
//  - We can assume that x \notin t_i, x \notin s_j, or otherwise use simplification.
//  - We can assume that x occurs only in equalities or disequalities, or the recognizer, since 
//    otherwise, we could simplify equalities, or QE does not apply.
//  - either x = t_i for some positive t_i, or we create 
//      diag = C(t_1, ..., C(t_n, .. C(s_1, .. , C(s_m))))
//    and x is different from each t_i, s_j.
//    

//
// reduce:
// --------
// reduce set of literals containing x. The elimination procedure follows an adaptation of 
// the proof (with corrections) in Hodges (shorter model theory).
//
// . x = t - (x \notin t) x is eliminated immediately.
// 
// . x != t1, ..., x != t_n - (x \notin t_i) are collected into distrinct_terms.
// 
// . recognizer(x) - is stored as pos_recognizer.
// 
// . !recognizer(x) - is stored into neg_recognizers.
//
// . L[constructor(..,x,..)] - 
//                      We could assume pre-processing introduces auxiliary 
//                      variable y, Is_constructor(y), accessor_j(y) = arg_j.
//                      But we apply the following hack: re-introduce x' into vars, 
//                      but also the variable y and the reduced formula.
// 
// . L[accessor_i(x)] - if pos_recognizer(x) matches accessor, 
//                      or if complement of neg_recognizers match accessor, then 
//                      introduce x_1, .., x_n corresponding to accessor_i(x).
//                      
// The only way x is not in the scope of a data-type method is if it is in 
// an equality or dis-equality of the form:
// 
// . x (!)= acc_1(acc_2(..(acc_i(x)..) - would be false (true) if recognizer(..) 
//                     is declared for each sub-term.
// 
// 
// - otherwise, each x should be in the scope of an accessor.
// 
// Normalized literal elimination:
// 
// .    exists x . Lits[accessor_i(x)] & Is_constructor(x) 
//   -> 
//      exists x_1, .., x_n . Lits[x_1, .., x_n] for each accessor_i(x).
// 

//
// maintain set of equations and disequations with x.
//

#include "qe/qe.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "util/obj_pair_hashtable.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

namespace qe {

    class datatype_atoms {
        ast_manager&     m;
        app_ref_vector   m_recognizers;
        expr_ref_vector  m_eqs;
        expr_ref_vector  m_neqs;
        app_ref_vector   m_eq_atoms;
        app_ref_vector   m_neq_atoms;
        app_ref_vector   m_unsat_atoms;
        expr_ref_vector  m_eq_conds;
        ast_mark         m_mark;
        datatype_util    m_util;
    public:
        datatype_atoms(ast_manager& m) :
            m(m), 
            m_recognizers(m),
            m_eqs(m),
            m_neqs(m),
            m_eq_atoms(m), m_neq_atoms(m), m_unsat_atoms(m), m_eq_conds(m),
            m_util(m) {}
        
        bool add_atom(contains_app& contains_x, bool is_pos, app* a) {
            app* x = contains_x.x();
            SASSERT(contains_x(a));
            if (m_mark.is_marked(a)) {
                return true;
            }
            m_mark.mark(a, true);
            func_decl* f = a->get_decl();
            if (m_util.is_recognizer(f) && a->get_arg(0) == x) {
                m_recognizers.push_back(a);
                TRACE("qe", tout << "add recognizer:" << mk_pp(a, m) << "\n";);
                return true;
            }
            if (!m.is_eq(a)) {
                return false;
            }
            if (add_eq(contains_x, is_pos, a->get_arg(0), a->get_arg(1))) {
                add_atom(a, is_pos);
                return true;
            }
            if (add_eq(contains_x, is_pos, a->get_arg(1), a->get_arg(0))) {
                add_atom(a, is_pos);
                return true;
            }
            if (add_unsat_eq(contains_x, a, a->get_arg(0), a->get_arg(1))) {
                return true;
            }
            return false;
        }

        unsigned num_eqs() { return m_eqs.size(); }
        expr* eq(unsigned i) { return m_eqs[i].get(); }
        expr* eq_cond(unsigned i) { return m_eq_conds[i].get(); }
        app*  eq_atom(unsigned i) { return m_eq_atoms[i].get(); }

        unsigned num_neqs() { return m_neq_atoms.size(); }
        app*  neq_atom(unsigned i) { return m_neq_atoms[i].get(); }

        unsigned num_neq_terms() const { return m_neqs.size(); }
        expr* neq_term(unsigned i) const { return m_neqs[i]; }
        expr* const* neq_terms() const { return m_neqs.c_ptr(); }

        unsigned num_recognizers() { return m_recognizers.size(); }
        app*   recognizer(unsigned i) { return m_recognizers[i].get(); }

        unsigned num_unsat() { return m_unsat_atoms.size(); }
        app*     unsat_atom(unsigned i) { return m_unsat_atoms[i].get(); }
        
    private:

        //
        // perform occurs check on equality.
        // 
        bool add_unsat_eq(contains_app& contains_x, app* atom, expr* a, expr* b) {
            app* x = contains_x.x();
            if (x != a) {
                std::swap(a, b);
            }
            if (x != a) {
                return false;
            }
            if (!contains_x(b)) {
                return false;
            }
            ptr_vector<expr> todo;
            ast_mark mark;
            todo.push_back(b);
            while (!todo.empty()) {
                b = todo.back();
                todo.pop_back();
                if (mark.is_marked(b)) {
                    continue;
                }
                mark.mark(b, true);
                if (!is_app(b)) {
                    continue;
                }
                if (b == x) {
                    m_unsat_atoms.push_back(atom);
                    return true;
                }
                app* b_app = to_app(b);
                if (!m_util.is_constructor(b_app)) {
                    continue;
                }
                for (unsigned i = 0; i < b_app->get_num_args(); ++i) {
                    todo.push_back(b_app->get_arg(i));
                }                        
            }
            return false;
        }

        void add_atom(app* a, bool is_pos) {
            TRACE("qe", tout << "add atom:" << mk_pp(a, m) << " " << (is_pos?"pos":"neg") << "\n";);
            if (is_pos) {
                m_eq_atoms.push_back(a);
            }
            else {
                m_neq_atoms.push_back(a);
            }
        }

        bool add_eq(contains_app& contains_x, bool is_pos, expr* a, expr* b) {
            if (contains_x(b)) {
                return false;
            }
            if (is_pos) {
                return solve_eq(contains_x, a, b, m.mk_true());
            }
            else {
                return solve_diseq(contains_x, a, b);
            }
            return false;
        }

        bool solve_eq(contains_app& contains_x, expr* _a, expr* b, expr* cond0) {
            SASSERT(contains_x(_a));
            SASSERT(!contains_x(b));
            app* x = contains_x.x();
            if (!is_app(_a)) {
                return false;
            }
            app* a = to_app(_a);
            if (x == a) {
                m_eqs.push_back(b);
                m_eq_conds.push_back(cond0);
                return true;
            }
            if (!m_util.is_constructor(a)) {
                return false;
            }
            func_decl* c = a->get_decl();
            func_decl_ref r(m_util.get_constructor_is(c), m);
            ptr_vector<func_decl> const & acc = *m_util.get_constructor_accessors(c);
            SASSERT(acc.size() == a->get_num_args());
            //
            // It suffices to solve just the first available equality.
            // The others are determined by the first.
            //
            expr_ref cond(m.mk_and(m.mk_app(r, b), cond0), m);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* l = a->get_arg(i);
                if (contains_x(l)) {
                    expr_ref r(m.mk_app(acc[i], b), m);
                    if (solve_eq(contains_x, l, r, cond)) {
                        return true;
                    }
                }
            }
            return false;
        }

        //
        // check that some occurrence of 'x' is in a constructor sequence.
        //        
        bool solve_diseq(contains_app& contains_x, expr* a0, expr* b) {
            SASSERT(!contains_x(b));
            SASSERT(contains_x(a0));
            app* x = contains_x.x();
            ptr_vector<expr> todo;
            ast_mark mark;
            todo.push_back(a0);
            while (!todo.empty()) {
                a0 = todo.back();
                todo.pop_back();
                if (mark.is_marked(a0)) {
                    continue;
                }
                mark.mark(a0, true);
                if (!is_app(a0)) {
                    continue;
                }
                app* a = to_app(a0);
                if (a == x) {
                    m_neqs.push_back(b);
                    return true;
                }
                if (!m_util.is_constructor(a)) {
                    continue;
                }
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    todo.push_back(a->get_arg(i));
                }                        
            }
            return false;
        }
    };

    // 
    // eliminate foreign variable under datatype functions (constructors).            
    // (= C(x,y) t) -> (R_C(t) && x = s1(t) && x = s2(t))
    //

    class lift_foreign_vars : public map_proc {
        ast_manager&      m;
        bool              m_change;
        datatype_util&    m_util;
        i_solver_context& m_ctx;
    public:
        lift_foreign_vars(ast_manager& m, datatype_util& util, i_solver_context& ctx): 
            map_proc(m), m(m), m_change(false), m_util(util), m_ctx(ctx) {}

        bool lift(expr_ref& fml) {
            m_change = false;
            for_each_expr(*this, fml.get());
            if (m_change) {
                fml = get_expr(fml.get());  
                TRACE("qe", tout << "lift:\n" << mk_pp(fml.get(), m) << "\n";);
            }
            return m_change;
        }

        void operator()(var* v) {
            visit(v);
        }
        
        void operator()(quantifier* q) {
            visit(q);
        }
        
        void operator()(app* a) {
            expr* l, *r;
            if (m.is_eq(a, l, r)) {
                if (reduce_eq(a, l, r)) {
                    m_change = true;
                    return;
                }
                if (reduce_eq(a, r, l)) {
                    m_change = true;
                    return;
                }
            }
            reconstruct(a);
        }

    private:

        bool reduce_eq(app* a, expr* _l, expr* r) {
            if (!is_app(_l)) {
                return false;
            }
            app* l = to_app(_l);
            if (!m_util.is_constructor(l)) {
                return false;
            }
            
            if (!contains_foreign(l)) {
                return false;
            }
            func_decl* c = l->get_decl();
            ptr_vector<func_decl> const& acc = *m_util.get_constructor_accessors(c);
            func_decl* rec = m_util.get_constructor_is(c);
            expr_ref_vector conj(m);
            conj.push_back(m.mk_app(rec, r));
            for (unsigned i = 0; i < acc.size(); ++i) {
                expr* r_i = m.mk_app(acc[i], r);
                expr* l_i = l->get_arg(i);
                conj.push_back(m.mk_eq(l_i, r_i));                
            }
            expr* e = m.mk_and(conj.size(), conj.c_ptr());
            m_map.insert(a, e, nullptr);
            TRACE("qe", tout << "replace: " << mk_pp(a, m) << " ==> \n" << mk_pp(e, m) << "\n";);
            return true;
        }

        bool contains_foreign(app* a) {
            unsigned num_vars = m_ctx.get_num_vars();
            for (unsigned i = 0; i < num_vars; ++i) {
                contains_app& v = m_ctx.contains(i);
                sort* s = v.x()->get_decl()->get_range();

                //
                // data-type contains arithmetical term or bit-vector.
                //
                if (!m_util.is_datatype(s) &&
                    !m.is_bool(s) &&
                    v(a)) {
                    return true;
                }               
            }
            return false;
        }

    };


    class datatype_plugin : public qe_solver_plugin  {
        typedef std::pair<app*,ptr_vector<app> > subst_clos;
        typedef obj_pair_map<app,  expr, datatype_atoms*> eqs_cache;
        typedef obj_pair_map<app, func_decl, subst_clos*> subst_map;

        datatype_util              m_datatype_util;
        expr_safe_replace          m_replace;
        eqs_cache                  m_eqs_cache;
        subst_map                  m_subst_cache;
        ast_ref_vector             m_trail;

    public:
        datatype_plugin(i_solver_context& ctx, ast_manager& m) : 
            qe_solver_plugin(m, m.mk_family_id("datatype"), ctx),
            m_datatype_util(m),
            m_replace(m),
            m_trail(m)
        {
        }
                     
        ~datatype_plugin() override {
            {
                eqs_cache::iterator it = m_eqs_cache.begin(), end = m_eqs_cache.end();
                for (; it != end; ++it) {
                    dealloc(it->get_value());
                }
            }
            {
                subst_map::iterator it = m_subst_cache.begin(), end = m_subst_cache.end();
                for (; it != end; ++it) {
                    dealloc(it->get_value());
                }
            }
            
        }
        
        bool get_num_branches( contains_app& x, expr* fml, rational& num_branches) override {
            sort* s = x.x()->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            if (m_datatype_util.is_recursive(s)) {
                return get_num_branches_rec(x, fml, num_branches);
            }
            else {
                return get_num_branches_nonrec(x, fml, num_branches);
            }
        }

                
        void assign(contains_app& x, expr* fml, rational const& vl) override {
            sort* s = x.x()->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            TRACE("qe", tout << mk_pp(x.x(), m) << " " << vl << "\n";);
            if (m_datatype_util.is_recursive(s)) {
                assign_rec(x, fml, vl);
            }
            else {
                assign_nonrec(x, fml, vl);
            }
        }

        void subst(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) override {
            sort* s = x.x()->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            TRACE("qe", tout << mk_pp(x.x(), m) << " " << vl << "\n";);
            if (m_datatype_util.is_recursive(s)) {
                subst_rec(x, vl, fml, def);
            }
            else {
                subst_nonrec(x, vl, fml, def);
            }
        }
        
        unsigned get_weight( contains_app& x, expr* fml) override {
            return UINT_MAX;
        }

        bool solve( conj_enum& conj, expr* fml) override {
            return false;
        }

        bool simplify( expr_ref& fml) override {
            lift_foreign_vars lift(m, m_datatype_util, m_ctx);
            return lift.lift(fml);
        }

        bool mk_atom(expr* e, bool p, expr_ref& result) override {
            return false;
        }

        
        virtual rational get_cost(contains_app&, expr* fml) {
            return rational(0);
        }
        
    private:

        void add_def(expr* term, expr_ref* def) {
            if (def) {
                *def = term;
            }
        }

        //
        // replace x by C(y1,..,yn) where y1,..,yn are fresh variables.
        //
        void subst_constructor(contains_app& x, func_decl* c, expr_ref& fml, expr_ref* def) {
            subst_clos* sub = nullptr;
            
            if (m_subst_cache.find(x.x(), c, sub)) {
                m_replace.apply_substitution(x.x(), sub->first, fml);
                add_def(sub->first, def);
                for (unsigned i = 0; i < sub->second.size(); ++i) {
                    m_ctx.add_var(sub->second[i]);
                }
                return;
            }
            sub = alloc(subst_clos);
            unsigned arity = c->get_arity();
            expr_ref_vector vars(m);
            for (unsigned i = 0; i < arity; ++i) {
                sort* sort_x = c->get_domain()[i];
                app_ref fresh_x(m.mk_fresh_const("x", sort_x), m);
                m_ctx.add_var(fresh_x.get());
                vars.push_back(fresh_x.get());
                sub->second.push_back(fresh_x.get());
            }
            app_ref t(m.mk_app(c, vars.size(), vars.c_ptr()), m);
            m_trail.push_back(x.x());
            m_trail.push_back(c);
            m_trail.push_back(t);

            add_def(t, def);
            m_replace.apply_substitution(x.x(), t, fml);
            sub->first = t;
            m_subst_cache.insert(x.x(), c, sub);
        }

        void get_recognizers(expr* fml, ptr_vector<app>& recognizers) {
            conj_enum conjs(m, fml);
            conj_enum::iterator it = conjs.begin(), end = conjs.end();
            for (; it != end; ++it) {
                expr* e = *it;
                if (is_app(e)) {
                    app* a = to_app(e);
                    func_decl* f = a->get_decl();
                    if (m_datatype_util.is_recognizer(f)) {
                        recognizers.push_back(a);
                    }
                }
            }
        }

        bool has_recognizer(app* x, expr* fml, func_decl*& r, func_decl*& c) {
            ptr_vector<app> recognizers;
            get_recognizers(fml, recognizers);
            for (unsigned i = 0; i < recognizers.size(); ++i) {
                app* a = recognizers[i];
                if (a->get_arg(0) == x) {
                    r = a->get_decl();
                    c = m_datatype_util.get_recognizer_constructor(a->get_decl());
                    return true;
                }
            }
            return false;
        }

        bool get_num_branches_rec( contains_app& x, expr* fml, rational& num_branches) {
            sort* s = x.x()->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            SASSERT(m_datatype_util.is_recursive(s));

            unsigned sz = m_datatype_util.get_datatype_num_constructors(s);
            num_branches = rational(sz);
            func_decl* c = nullptr, *r = nullptr;
           
            //
            // If 'x' does not yet have a recognizer, then branch according to recognizers.
            // 
            if (!has_recognizer(x.x(), fml, r, c)) {
                return true;
            }
            //
            // eliminate 'x' by applying constructor to fresh variables.
            // 
            if (has_selector(x, fml, c)) {
                num_branches = rational(1);
                return true;
            }                
            
            //
            // 'x' has a recognizer. Count number of equalities and disequalities.
            //
            if (update_eqs(x, fml)) {
                datatype_atoms& eqs = get_eqs(x.x(), fml);
                num_branches = rational(eqs.num_eqs() + 1);
                return true;
            }
            TRACE("qe", tout << "could not get number of branches " << mk_pp(x.x(), m) << "\n";);
            return false;
        }


        void assign_rec(contains_app& contains_x, expr* fml, rational const& vl) {
            app* x = contains_x.x();
            sort* s = x->get_decl()->get_range();
            func_decl* c = nullptr, *r = nullptr;

            //
            // If 'x' does not yet have a recognizer, then branch according to recognizers.
            // 
            if (!has_recognizer(x, fml, r, c)) {
                c = m_datatype_util.get_datatype_constructors(s)->get(vl.get_unsigned());
                r = m_datatype_util.get_constructor_is(c);
                app* is_c = m.mk_app(r, x);                
                // assert v => r(x)            
                m_ctx.add_constraint(true, is_c);
                return;
            }

            //
            // eliminate 'x' by applying constructor to fresh variables.
            // 
            if (has_selector(contains_x, fml, c)) {
                return;
            }                
            
            //
            // 'x' has a recognizer. The branch ID id provided by the index of the equality.
            //
            datatype_atoms& eqs = get_eqs(x, fml);
            SASSERT(vl.is_unsigned());
            unsigned idx = vl.get_unsigned();
            SASSERT(idx <= eqs.num_eqs());
            
            if (idx < eqs.num_eqs()) {
                expr* t = eqs.eq(idx);
                m_ctx.add_constraint(true, m.mk_eq(x, t));
            }
            else {
                for (unsigned i = 0; i < eqs.num_eqs(); ++i) {
                    expr* t = eqs.eq(i);
                    m_ctx.add_constraint(true, m.mk_not(m.mk_eq(x, t)));
                }
            }
        }

        void subst_rec(contains_app& contains_x, rational const& vl, expr_ref& fml, expr_ref* def) {
            app* x = contains_x.x();
            sort* s = x->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            func_decl* c = nullptr, *r = nullptr;

            TRACE("qe", tout << mk_pp(x, m) << " " << vl << " " << mk_pp(fml, m) << " " << (def != 0) << "\n";);
            //
            // Add recognizer to formula.
            // Introduce auxiliary variable to eliminate.
            // 
            if (!has_recognizer(x, fml, r, c)) {
                c = m_datatype_util.get_datatype_constructors(s)->get(vl.get_unsigned());
                r = m_datatype_util.get_constructor_is(c);
                app* is_c = m.mk_app(r, x);                
                fml = m.mk_and(is_c, fml);
                app_ref fresh_x(m.mk_fresh_const("x", s), m);
                m_ctx.add_var(fresh_x);
                m_replace.apply_substitution(x, fresh_x, fml);
                add_def(fresh_x, def);
                TRACE("qe", tout << "Add recognizer " << mk_pp(is_c, m) << "\n";);
                return;
            }


            if (has_selector(contains_x, fml, c)) {
                TRACE("qe", tout << "Eliminate selector " << mk_ll_pp(c, m) << "\n";);
                subst_constructor(contains_x, c, fml, def); 
                return;
            }

            //
            // 'x' has a recognizer. The branch ID id provided by the index of the equality.
            //
            datatype_atoms& eqs = get_eqs(x, fml);
            SASSERT(vl.is_unsigned());
            unsigned idx = vl.get_unsigned();
            SASSERT(idx <= eqs.num_eqs());

            for (unsigned i = 0; i < eqs.num_recognizers(); ++i) {
                app* rec = eqs.recognizer(i);
                if (rec->get_decl() == r) {
                    m_replace.apply_substitution(rec, m.mk_true(), fml);
                }
                else {
                    m_replace.apply_substitution(rec, m.mk_false(), fml);
                }
            }

            for (unsigned i = 0; i < eqs.num_unsat(); ++i) {
                m_replace.apply_substitution(eqs.unsat_atom(i), m.mk_false(), fml);
            }

            if (idx < eqs.num_eqs()) {
                expr* t = eqs.eq(idx);
                expr* c = eqs.eq_cond(idx);
                add_def(t, def);
                m_replace.apply_substitution(x, t, fml);
                if (!m.is_true(c)) {
                    fml = m.mk_and(c, fml);
                }
            }
            else {                
                for (unsigned i = 0; i < eqs.num_eqs(); ++i) {
                    m_replace.apply_substitution(eqs.eq_atom(i), m.mk_false(), fml);
                }

                for (unsigned i = 0; i < eqs.num_neqs(); ++i) {
                    m_replace.apply_substitution(eqs.neq_atom(i), m.mk_false(), fml);
                }
                if (def) {
                    sort* s = m.get_sort(x);
                    ptr_vector<sort> sorts;
                    sorts.resize(eqs.num_neq_terms(), s);
                    func_decl* diag = m.mk_func_decl(symbol("diag"), sorts.size(), sorts.c_ptr(), s);
                    expr_ref t(m);
                    t = m.mk_app(diag, eqs.num_neq_terms(), eqs.neq_terms());
                    add_def(t, def);
                }
            }
            TRACE("qe", tout << "reduced " << mk_pp(fml.get(), m) << "\n";);
        }

        bool get_num_branches_nonrec( contains_app& x, expr* fml, rational& num_branches) {
            sort* s = x.x()->get_decl()->get_range();
            unsigned sz = m_datatype_util.get_datatype_num_constructors(s);
            num_branches = rational(sz);
            func_decl* c = nullptr, *r = nullptr;

            if (sz != 1 && has_recognizer(x.x(), fml, r, c)) {
                TRACE("qe", tout << mk_pp(x.x(), m) << " has a recognizer\n";);
                num_branches = rational(1);
            }        
            TRACE("qe", tout << mk_pp(x.x(), m) << " branches: " << sz << "\n";);
            return true; 
        }

        void assign_nonrec(contains_app& contains_x, expr* fml, rational const& vl) {
            app* x = contains_x.x();
            sort* s = x->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            unsigned sz = m_datatype_util.get_datatype_num_constructors(s);
            SASSERT(vl.is_unsigned());
            SASSERT(vl.get_unsigned() < sz);
            if (sz == 1) {
                return;
            }
            func_decl* c = nullptr, *r = nullptr;
            if (has_recognizer(x, fml, r, c)) {
                TRACE("qe", tout << mk_pp(x, m) << " has a recognizer\n";);
                return;
            }
            
            c = m_datatype_util.get_datatype_constructors(s)->get(vl.get_unsigned());
            r = m_datatype_util.get_constructor_is(c);
            app* is_c = m.mk_app(r, x);
            
            // assert v => r(x)
            
            m_ctx.add_constraint(true, is_c);
        }

        virtual void subst_nonrec(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) {
            sort* s = x.x()->get_decl()->get_range();
            SASSERT(m_datatype_util.is_datatype(s));
            SASSERT(!m_datatype_util.is_recursive(s));
            func_decl* c = nullptr, *r = nullptr;
            if (has_recognizer(x.x(), fml, r, c)) {
                TRACE("qe", tout << mk_pp(x.x(), m) << " has a recognizer\n";);
            }
            else {
                SASSERT(vl.is_unsigned());
                SASSERT(vl.get_unsigned() < m_datatype_util.get_datatype_num_constructors(s));
                c = m_datatype_util.get_datatype_constructors(s)->get(vl.get_unsigned());
            }
            subst_constructor(x, c, fml, def);                
        }


        class has_select : public i_expr_pred {
            app* m_x;
            func_decl* m_c;
            datatype_util& m_util;
        public:
            has_select(app* x, func_decl* c, datatype_util& u): m_x(x), m_c(c), m_util(u) {}

            bool operator()(expr* e) override {
                if (!is_app(e)) return false;
                app* a = to_app(e);
                if (!m_util.is_accessor(a)) return false;
                if (a->get_arg(0) != m_x) return false;
                func_decl* f = a->get_decl();
                return m_c == m_util.get_accessor_constructor(f);
            }
        };

        bool has_selector(contains_app& x, expr* fml, func_decl* c) {
            has_select hs(x.x(), c, m_datatype_util);
            check_pred ch(hs, m);
            return ch(fml);
        }

        datatype_atoms& get_eqs(app* x, expr* fml) {
            datatype_atoms* eqs = nullptr;
            VERIFY (m_eqs_cache.find(x, fml, eqs));
            return *eqs;
        }

        bool update_eqs(contains_app& contains_x, expr* fml) {
            datatype_atoms* eqs = nullptr;
            if (m_eqs_cache.find(contains_x.x(), fml, eqs)) {
                return true;
            }
            eqs = alloc(datatype_atoms, m);

            if (!update_eqs(*eqs, contains_x, fml, m_ctx.pos_atoms(), true)) {
                dealloc(eqs);
                return false;
            }
            if (!update_eqs(*eqs, contains_x, fml, m_ctx.neg_atoms(), false)) {
                dealloc(eqs);
                return false;
            }

            m_trail.push_back(contains_x.x());
            m_trail.push_back(fml);
            m_eqs_cache.insert(contains_x.x(), fml, eqs);
            return true;
        }

        bool update_eqs(datatype_atoms& eqs, contains_app& contains_x, expr* fml, atom_set const& tbl, bool is_pos) {
            atom_set::iterator it = tbl.begin(), end = tbl.end();
            for (; it != end; ++it) {
                app* e = *it; 
                if (!contains_x(e)) {
                    continue;
                }                
                if (!eqs.add_atom(contains_x, is_pos, e)) {
                    return false;
                }
            }    
            return true;
        }       
    };

    qe_solver_plugin* mk_datatype_plugin(i_solver_context& ctx) {
        return alloc(datatype_plugin, ctx, ctx.get_manager());
    }
}
