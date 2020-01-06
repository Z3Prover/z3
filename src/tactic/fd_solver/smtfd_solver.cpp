/**
   F1, F2, .., -> Fa1, Fa2, ...
   assert incrementally:
   t1 <-> Fa1
   t2 <-> Fa2 & t1
   ....
   
        
   abstraction replaces subterms that are not bv constants 
   by atomic formulas or a term of the form: 
       xor(random_bv, fresh_bv_variable) of enough (24) bits
   Then default assignment to the fresh bv variable (to 0)
   is hashed to a value that is likely different form other variables
   of the same type, so two variables of the same type are then most
   likely equal in a model if they have to be.

   atoms := list of atomic formulas (including equalities over bit-vectors)

   while True:
     r = check_sat([t_k])

     if r != sat:
        return r

     M = current model

     literals := evaluation of atoms under M
   
     r = check_sat([!t_k] + literals)

     if r != unsat:
        return unknown

     core = rep(some unsat_core excluding !t_k)

     if core is SAT modulo A + UF + other theories:
        return SAT

     optionally apply a step of superposition (reduce congruence and equality diamonds):
        let t1 = t2, core1 := core, where t1 in core1
        - t1 is uninterpreted constant
          core := replace t1 by t2 in core1
        - t1 = f(args):
          core := replace all occurrences of t1' by t2 in core1 where M(abs(t1)) = M(abs(t1')).
        - t1 = select(A,args)?
          when is it safe to reduce t1?
      
     for t in subterms(core) where t is f(args):
       v1 := M(abs(t))
       v_args = M(abs(args))
       v2, t2 := table[f][v_args]
       if v2 != null and v1 != v2:
          lemmas += (args = t2.args => t = t2)
       else:
          table[f][v_args] := v1, t

     for t in subterms((core) where t is select(A, args):
       vA := M(abs(A))
       v_args = M(abs(args))
       v2, args2, t2 := table[vA][v_args]
       if v2 != null and v1 != v2:
          lemmas += (args1 = args2 => t = t2)
       else:
          table[vA][v_args] := v1, args, t

     for t in subterms(core) where t is store(A, args, b):
        vT := M(abs(t))
        vA := M(abs(A))     
        vB := M(abs(b))     
        v2, args2, t2 := table[vT][v_args]
        if v2 != null and vB != v2:
           lemmas += (select(t, args) = b)
        if v2 = null:
           table[vT][v_args] := vB, args, t
        for v_args2 |-> v2, args2, t2 in table[vA]:
           check table[vT][v_args2] for compatibility with v2
           if not compatible:
              lemmas += (args2 != args => select(t, args2) = select(A, args2))
        for v_args2 |-> v2, args2, t2 in table[tA]:
           check table[vA][v_args2] for compatibility with v2
           if not compatible:
              lemmas += (args2 != args => select(t, args2) = select(A, args2))


     for t in subterms(core) where t is (lambda x . M), t is ground:
         vT := M(abs(t))
         for v_args2 |-> v2, args2, t2 in table[vT]:
             v1 := M(abs(M[args2/x]))
             if v1 != v2:
                lemmas += (select(t2, args2) = M[args2/x])                

     for t in subterms(core) where t is map(f, A, B, C), t is const:
         similar to lambda

     for A, B in array_terms(core):
         lemmas += (select(A, delta(A,B)) = select(B, delta(A,B)) => A = B)     

     if AUF solver returned unsat:
        add abs(!core) to solver 

     add abs(lemmas) to solver


Note:
- hint to SMT solver using FD model (add equalities from FD model)
- abstractions for multiplication and other BV operations:
  - add ackerman reductions for BV
  - commutativity?
  - fix most bits using model, blast specialization.
    Z = X * Y
    X[range] = k1, Y[range] = k2 => Z = (k1++X') * (k2 ++ Y')
- abstract also equality
  - add triangle lemmas whenever using equality chaining in lemmas.
- add equality resolution lemmas
  For core: v = t & phi(v) 
  and v = t occurs in several cores
  set core := phi(t/v)
- do something about arithmetic?
 
*/

#include "util/scoped_ptr_vector.h"
#include "util/obj_hashtable.h"
#include "util/obj_pair_hashtable.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/for_each_expr.h"
#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "tactic/tactic_exception.h"
#include "tactic/fd_solver/fd_solver.h"
#include "solver/solver.h"
#include "solver/solver_na2as.h"
#include "solver/solver2tactic.h"

namespace smtfd {

    struct stats {
        unsigned m_num_lemmas;
        unsigned m_num_rounds;
        unsigned m_num_mbqi;
        unsigned m_num_fresh_bool;
        stats() { memset(this, 0, sizeof(stats)); }
    };

    class smtfd_abs {
        ast_manager&    m;
        stats&          m_stats;
        expr_ref_vector m_abs, m_rep, m_atoms, m_atom_defs; // abstraction and representation maps
        array_util      m_autil;
        bv_util         m_butil;
        pb_util         m_pb;
        ptr_vector<expr> m_args, m_todo;
        unsigned        m_nv;
        unsigned_vector m_abs_trail, m_rep_trail, m_nv_trail;
        unsigned_vector m_abs_lim, m_rep_lim, m_atoms_lim;
        random_gen      m_rand;
        
        void pop(unsigned n, expr_ref_vector& v, unsigned_vector& trail, unsigned_vector& lim) {
            SASSERT(n > 0);
            unsigned sz = lim[lim.size() - n];
            for (unsigned i = trail.size(); i-- > sz;) {
                v[trail[i]] = nullptr;
            }
            trail.shrink(sz);
            lim.shrink(lim.size() - n);            
        }
        
        expr* try_abs(expr* e) { return m_abs.get(e->get_id(), nullptr); }
        expr* try_rep(expr* e) { return m_rep.get(e->get_id(), nullptr); }
        
        expr* fresh_var(expr* t) {
            symbol name = is_app(t) ? to_app(t)->get_name() : (is_quantifier(t) ? symbol("Q") : symbol("X"));
            if (m.is_bool(t)) {
                ++m_stats.m_num_fresh_bool;
                return m.mk_fresh_const(name, m.mk_bool_sort());
            }        
            else if (m_butil.is_bv(t)) {
                return m.mk_fresh_const(name, m.get_sort(t));
            }
            else {
                ++m_nv;
                unsigned bw = log2(m_nv) + 1;
                if (bw >= 24) {
                    throw default_exception("number of allowed bits for variables exceeded");
                }
                unsigned n = (m_rand() << 16) | m_rand();
                expr* num = m_butil.mk_numeral(n, bw);
                expr* es[2] = { num, m.mk_fresh_const(name, m_butil.mk_sort(bw)) };
                expr* e = m_butil.mk_bv_xor(2, es);
                return m_butil.mk_concat(e, m_butil.mk_numeral(0, 24 - bw));
            }
        }

        void push_trail(expr_ref_vector& map, unsigned_vector& trail, expr* t, expr* r) { 
            unsigned idx = t->get_id();
            map.reserve(idx + 1);
            map.set(idx, r);
            trail.push_back(idx);
        }

        bool is_atom(expr* r) {
            if (!m.is_bool(r)) {
                return false;
            }
            if (m.is_eq(r) && !m.is_bool(to_app(r)->get_arg(0))) {
                return true;
            }
            return !is_app(r) || to_app(r)->get_family_id() != m.get_basic_family_id();            
        }

        bool is_uninterp_atom(expr* a) {
            return is_app(a) && to_app(a)->get_num_args() == 0 && to_app(a)->get_family_id() == null_family_id;
        }
        
    public:
        smtfd_abs(ast_manager& m, stats& s):
            m(m),
            m_stats(s),
            m_abs(m),
            m_rep(m),
            m_atoms(m),
            m_atom_defs(m),
            m_autil(m),
            m_butil(m),
            m_pb(m),
            m_nv(0)
        {
            abs(m.mk_true());
            abs(m.mk_false());
        }
        
        expr_ref_vector const& atoms() { 
            return m_atoms; 
        }

        expr_ref_vector const& atom_defs() { 
            return m_atom_defs; 
        }

        void reset_atom_defs() {
            m_atom_defs.reset();
        }
        
        void push() {
            m_abs_lim.push_back(m_abs_trail.size());
            m_rep_lim.push_back(m_rep_trail.size());
            m_atoms_lim.push_back(m_atoms.size());
            m_nv_trail.push_back(m_nv);
        }

        void pop(unsigned n) {
            pop(n, m_abs, m_abs_trail, m_abs_lim);
            pop(n, m_rep, m_rep_trail, m_rep_lim);
            m_atoms.shrink(m_atoms_lim[m_atoms_lim.size() - n]);
            m_atoms_lim.shrink(m_atoms_lim.size() - n);
            m_nv = m_nv_trail[m_nv_trail.size() - n];
            m_nv_trail.shrink(m_nv_trail.size() - n);
        }
        
        std::ostream& display(std::ostream& out)  {
            out << "abs: " << m_atoms.size() << "\n";
            for (expr* a : m_atoms) {
                out << mk_pp(a, m) << ": ";
                out << mk_bounded_pp(rep(a), m, 2) << "\n";
            }
            return out;
        }

        expr* abs_assumption(expr* e) {
            expr* a = abs(e), *b = nullptr;
            if (is_uninterp_atom(a) || (m.is_not(a, b) && is_uninterp_atom(b))) {
                return a;
            }
            expr* f = fresh_var(e);
            push_trail(m_abs, m_abs_trail, e, f);
            push_trail(m_rep, m_rep_trail, f, e);
            m_atoms.push_back(f);
            m_atom_defs.push_back(m.mk_iff(f, a));
            return f;
        }

        
        expr* abs(expr* e) {
            expr* r = try_abs(e);
            if (r) return r;
            m_todo.push_back(e);
            family_id bvfid = m_butil.get_fid();
            family_id bfid  = m.get_basic_family_id();
            family_id pbfid = m_pb.get_family_id();
            while (!m_todo.empty()) {
                expr* t = m_todo.back();
                r = try_abs(t);
                if (r) {
                    m_todo.pop_back();
                    continue;
                }
                if (is_app(t)) {
                    app* a = to_app(t);
                    m_args.reset();
                    for (expr* arg : *a) {
                        r = try_abs(arg);
                        if (r) {
                            m_args.push_back(r);
                        }
                        else {
                            m_todo.push_back(arg);
                        }
                    }
                    if (m_args.size() != a->get_num_args()) {
                        continue;
                    }
                    family_id fid = a->get_family_id();
                    if (m.is_eq(a)) {
                        r = m.mk_eq(m_args.get(0), m_args.get(1));
                    }
                    else if (m.is_distinct(a)) {
                        r = m.mk_distinct(m_args.size(), m_args.c_ptr());
                    }
                    else if (m.is_ite(a)) {
                        r = m.mk_ite(m_args.get(0), m_args.get(1), m_args.get(2));
                    }
                    else if (bvfid == fid || bfid == fid || pbfid == fid) {
                        r = m.mk_app(a->get_decl(), m_args.size(), m_args.c_ptr());
                    }
                    else if (is_uninterp_const(t) && m.is_bool(t)) {
                        r = t;
                    }
                    else if (is_uninterp_const(t) && m_butil.is_bv(t)) {
                        r = t;
                    }
                    else if (m.is_model_value(t)) {
                        int idx = a->get_parameter(0).get_int();
                        r = m_butil.mk_numeral(rational(idx), 24); 
                    }
                    else {
                        r = fresh_var(t);                    
                    }
                }
                else {
                    r = fresh_var(t);
                }
                if (is_atom(r) && !is_uninterp_const(r)) {
                    expr* rr = fresh_var(r);
                    m_atom_defs.push_back(m.mk_iff(rr, r));
                    r = rr;
                }
                push_trail(m_abs, m_abs_trail, t, r);
                push_trail(m_rep, m_rep_trail, r, t);
                if (t != r) {
                    push_trail(m_abs, m_abs_trail, r, r);
                }
                if (is_atom(r)) {
                    m_atoms.push_back(r);
                }
            }
            return try_abs(e);
        }
        
        expr* rep(expr* e) { 
            expr* r = try_rep(e);
            if (r) return r;
            VERIFY(m.is_not(e, r));
            r = try_rep(r);
            r = m.mk_not(r);
            abs(r);
            return r;
        }
    };

    struct f_app {
        ast*       m_f;
        app*       m_t;
        sort*      m_s;
        unsigned   m_val_offset;
    };

    class theory_plugin;

    class plugin_context {
        ast_manager&    m;
        smtfd_abs&      m_abs;
        expr_ref_vector m_lemmas;
        unsigned        m_max_lemmas;
        th_rewriter     m_rewriter;
        ptr_vector<theory_plugin> m_plugins;
        model_ref       m_model;
    public:
        plugin_context(smtfd_abs& a, ast_manager& m):
            m(m),
            m_abs(a),
            m_lemmas(m), 
            m_rewriter(m)
        {
        }

        void set_max_lemmas(unsigned max) {            
            m_max_lemmas = max;
        }

        unsigned get_max_lemmas() const { return m_max_lemmas; }

        smtfd_abs& get_abs() { return m_abs; }

        void add(expr* f, char const* msg) { m_lemmas.push_back(f); TRACE("smtfd", tout << msg << " " << mk_bounded_pp(f, m, 2) << "\n";); }

        ast_manager& get_manager() { return m; }

        bool at_max() const { return m_lemmas.size() >= m_max_lemmas; }

        model& get_model() { return *m_model; }

        expr_ref_vector::iterator begin() { return m_lemmas.begin(); }
        expr_ref_vector::iterator end() { return m_lemmas.end(); }
        unsigned size() const { return m_lemmas.size(); }
        bool empty() const { return m_lemmas.empty(); }
        void reset_lemmas() { m_lemmas.reset(); }

        void add_plugin(theory_plugin* p) { m_plugins.push_back(p); }

        expr_ref model_value(expr* t);
        expr_ref model_value(sort* s);
        bool term_covered(expr* t);
        bool sort_covered(sort* s);
        void reset(model_ref& mdl);
        void rewrite(expr_ref& r) { m_rewriter(r); }

        /**
         * \brief use propositional model to create a model of uninterpreted functions
         */
        void populate_model(model_ref& mdl, expr_ref_vector const& terms);

        /**
         * \brief check consistency properties that can only be achived using a global analysis of terms
         */
        void global_check(expr_ref_vector const& core);

        /**
         * \brief add theory axioms that are violdated in the current model
         * the round indicator is used to prioritize "cheap" axioms before
         * expensive axiom instantiation. 
         */
        bool add_theory_axioms(expr_ref_vector const& core, unsigned round);

        std::ostream& display(std::ostream& out);

    };

    struct f_app_eq {
        theory_plugin& p;
        f_app_eq(theory_plugin& p):p(p) {}
        bool operator()(f_app const& a, f_app const& b) const;
    };

    struct f_app_hash {
        theory_plugin& p;
        f_app_hash(theory_plugin& p):p(p) {}
        unsigned operator()(f_app const& a) const;
        unsigned operator()(expr* const* args) const { return 14; }
        unsigned operator()(expr* const* args, unsigned idx) const { return args[idx]->hash(); }
    };

    class theory_plugin {
    protected:
        typedef hashtable<f_app, f_app_hash, f_app_eq> table;
        ast_manager&             m;
        smtfd_abs&               m_abs;    
        plugin_context&          m_context;
        expr_ref_vector          m_values;
        ast_ref_vector           m_pinned;
        expr_ref_vector          m_args, m_vargs;
        f_app_eq                 m_eq;
        f_app_hash               m_hash;
        scoped_ptr_vector<table> m_tables;
        obj_pair_map<ast, sort, unsigned>   m_ast2table;


        f_app mk_app(ast* f, app* t, sort* s) {
            f_app r;
            r.m_f = f;
            r.m_val_offset = m_values.size();
            r.m_t = t;
            r.m_s = s;
            for (expr* arg : *t) {
                m_values.push_back(eval_abs(arg));
            }
            m_values.push_back(eval_abs(t));
            return r;
        }

        f_app const& insert(f_app const& f) {
            return ast2table(f.m_f, f.m_s).insert_if_not_there(f);
        }

    public:
        theory_plugin(plugin_context& context) : 
            m(context.get_manager()), 
            m_abs(context.get_abs()),
            m_context(context),
            m_values(m),
            m_pinned(m),
            m_args(m), 
            m_vargs(m),
            m_eq(*this),
            m_hash(*this)
        {
            m_context.add_plugin(this);
        }

        table& ast2table(ast* f, sort* s) {
            unsigned idx = 0;
            if (!m_ast2table.find(f, s, idx)) {
                idx = m_tables.size();
                m_tables.push_back(alloc(table, DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_hash, m_eq));
                m_ast2table.insert(f, s, idx);
                m_pinned.push_back(f);
            }
            return *m_tables[idx];
        }

        expr_ref_vector const& values() const { return m_values; }

        ast_manager& get_manager() { return m; }

        expr_ref eval_abs(expr* t) { return m_context.get_model()(m_abs.abs(t)); }
        bool is_true_abs(expr* t) { return m_context.get_model().is_true(m_abs.abs(t)); }
        
        expr* value_of(f_app const& f) const { return m_values[f.m_val_offset + f.m_t->get_num_args()]; }

        bool check_congruence(ast* f, app* t, sort* s) {
            f_app f1 = mk_app(f, t, s);
            f_app const& f2 = insert(f1);
            if (f2.m_val_offset == f1.m_val_offset) {
                return true;
            }
            bool eq = value_of(f1) == value_of(f2);
            m_values.shrink(f1.m_val_offset);
            return eq;            
        }

        void enforce_congruence(ast* f, app* t, sort* s) {
            f_app f1 = mk_app(f, t, s);
            f_app const& f2 = insert(f1);
            if (f2.m_val_offset == f1.m_val_offset) {
                TRACE("smtfd_verbose", tout << "fresh: " << mk_pp(f, m, 2) << "\n";);
                return;
            }
            bool eq = value_of(f1) == value_of(f2);
            m_values.shrink(f1.m_val_offset);
            if (eq) {
                TRACE("smtfd_verbose", tout << "eq: " << " " << mk_bounded_pp(t, m, 2) << " " << mk_bounded_pp(f2.m_t, m, 2) << "\n";);
                return;
            }
            m_args.reset();
            SASSERT(t->get_num_args() == f1.m_t->get_num_args());
            SASSERT(t->get_num_args() == f2.m_t->get_num_args());
            for (unsigned i = 0; i < t->get_num_args(); ++i) {
                expr* e1 = f1.m_t->get_arg(i);
                expr* e2 = f2.m_t->get_arg(i);
                if (e1 != e2) m_args.push_back(m.mk_eq(e1, e2));
            }            
            TRACE("smtfd_verbose", tout << "diff: " << mk_bounded_pp(f1.m_t, m, 2) << " " << mk_bounded_pp(f2.m_t, m, 2) << "\n";);
            m_context.add(m.mk_implies(mk_and(m_args), m.mk_eq(f1.m_t, f2.m_t)), __FUNCTION__);
        }

        std::ostream& display(std::ostream& out) {
            for (table* tb : m_tables) {
                display(out, *tb);
            }
            return out;
        }

        std::ostream& display(std::ostream& out, table& t) {
            out << "table\n";
            for (auto const& k : t) {
                out << "key: " << mk_bounded_pp(k.m_f, m, 2) << "\nterm: " << mk_bounded_pp(k.m_t, m, 2) << "\n";
                out << "args:\n";
                for (unsigned i = 0; i <= k.m_t->get_num_args(); ++i) {
                    out << mk_bounded_pp(m_values.get(k.m_val_offset + i), m, 3) << "\n";
                }
                out << "\n";
            }
            return out;
        }

        expr_ref model_value(expr* t) { return m_context.model_value(t); }
        expr_ref model_value(sort* s) { return m_context.model_value(s); }

        virtual void global_check(expr_ref_vector const& core) {}
        virtual void check_term(expr* t, unsigned round) = 0;
        virtual expr_ref model_value_core(expr* t) = 0;
        virtual expr_ref model_value_core(sort* s) = 0;
        virtual bool term_covered(expr* t) = 0;
        virtual bool sort_covered(sort* s) = 0;
        virtual unsigned max_rounds() = 0;
        virtual void populate_model(model_ref& mdl, expr_ref_vector const& terms) {}
        virtual void reset() {
            m_pinned.reset();
            m_tables.reset();
            m_ast2table.reset();
            m_values.reset();
        }
    };

    void plugin_context::global_check(expr_ref_vector const& core) {
        for (theory_plugin* p : m_plugins) {
            p->global_check(core);
        }
    }

    bool plugin_context::add_theory_axioms(expr_ref_vector const& core, unsigned round) {
        unsigned max_rounds = 0;
        for (theory_plugin* p : m_plugins) {
            max_rounds = std::max(max_rounds, p->max_rounds());
        }
        if (max_rounds < round) {
            return false;
        }
        else if (round < max_rounds) {
            for (expr* t : subterms(core)) {
                for (theory_plugin* p : m_plugins) {
                    p->check_term(t, round);
                }
            }
        }
        else if (round == max_rounds) {
            global_check(core);
        }
        return true;
    }

    expr_ref plugin_context::model_value(expr* t) {
        expr_ref r(get_manager());
        for (theory_plugin* p : m_plugins) {
            r = p->model_value_core(t);
            if (r) break;
        }
        return r;
    }

    expr_ref plugin_context::model_value(sort* s) {
        expr_ref r(get_manager());
        for (theory_plugin* p : m_plugins) {
            r = p->model_value_core(s);
            if (r) break;
        }
        return r;
    }

    void plugin_context::reset(model_ref& mdl) {
        m_lemmas.reset();
        m_model = mdl;
        for (theory_plugin* p : m_plugins) {
            p->reset();
        }
    }

    bool plugin_context::sort_covered(sort* s) {
        for (theory_plugin* p : m_plugins) {
            if (p->sort_covered(s)) return true;
        }
        return false;
    }

    bool plugin_context::term_covered(expr* t) {
        for (theory_plugin* p : m_plugins) {
            if (p->term_covered(t)) return true;
        }
        return false;
    }

    std::ostream& plugin_context::display(std::ostream& out) {
        for (theory_plugin* p : m_plugins) {
            p->display(out);
        }
        return out;
    }

    void plugin_context::populate_model(model_ref& mdl, expr_ref_vector const& terms) {
        for (theory_plugin* p : m_plugins) {
            p->populate_model(mdl, terms);
        }
    }

    bool f_app_eq::operator()(f_app const& a, f_app const& b) const {
        if (a.m_f != b.m_f) 
            return false;
        for (unsigned i = 0; i < a.m_t->get_num_args(); ++i) {
            if (p.values().get(a.m_val_offset+i) != p.values().get(b.m_val_offset+i)) 
                return false;
            if (p.get_manager().get_sort(a.m_t->get_arg(i)) != p.get_manager().get_sort(b.m_t->get_arg(i)))
                return false;
        }
        return true;
    }

    unsigned f_app_hash::operator()(f_app const& a) const {
        return get_composite_hash(p.values().c_ptr() + a.m_val_offset, a.m_t->get_num_args(), *this, *this);
    }
    
    class basic_plugin : public theory_plugin {
    public:
        basic_plugin(plugin_context& context):
            theory_plugin(context) 
        {}
        void check_term(expr* t, unsigned round) override { }
        bool term_covered(expr* t) override { return is_app(t) && to_app(t)->get_family_id() == m.get_basic_family_id();  }
        bool sort_covered(sort* s) override { return m.is_bool(s); }
        unsigned max_rounds() override { return 0; }
        void populate_model(model_ref& mdl, expr_ref_vector const& terms) override { }
        expr_ref model_value_core(expr* t) override { return m.is_bool(t) ? m_context.get_model()(m_abs.abs(t)) : expr_ref(m); }
        expr_ref model_value_core(sort* s) override { return m.is_bool(s) ? expr_ref(m.mk_false(), m) : expr_ref(m); }
    };

    class pb_plugin : public theory_plugin {
        pb_util m_pb;
    public:
        pb_plugin(plugin_context& context):
            theory_plugin(context),
            m_pb(m)
        {}
        void check_term(expr* t, unsigned round) override { }
        bool term_covered(expr* t) override { return is_app(t) && to_app(t)->get_family_id() == m_pb.get_family_id(); }
        bool sort_covered(sort* s) override { return m.is_bool(s); }
        unsigned max_rounds() override { return 0; }
        void populate_model(model_ref& mdl, expr_ref_vector const& terms) override { }
        expr_ref model_value_core(expr* t) override { return expr_ref(m); }
        expr_ref model_value_core(sort* s) override { return expr_ref(m); }
    };

    class bv_plugin : public theory_plugin {
        bv_util m_butil;
    public:
        bv_plugin(plugin_context& context):
            theory_plugin(context),
            m_butil(m)
        {}
        void check_term(expr* t, unsigned round) override { }
        bool term_covered(expr* t) override { return is_app(t) && to_app(t)->get_family_id() == m_butil.get_family_id(); }
        bool sort_covered(sort* s) override { return m_butil.is_bv_sort(s); }
        unsigned max_rounds() override { return 0; }
        void populate_model(model_ref& mdl, expr_ref_vector const& terms) override { }
        expr_ref model_value_core(expr* t) override { return m_butil.is_bv(t) ? m_context.get_model()(m_abs.abs(t)) : expr_ref(m); }
        expr_ref model_value_core(sort* s) override { return m_butil.is_bv_sort(s) ? expr_ref(m_butil.mk_numeral(rational(0), s), m) : expr_ref(m); }
    };

    
    class uf_plugin : public theory_plugin {               

        obj_map<sort, unsigned> m_sort2idx;
        typedef obj_map<expr, expr*> val2elem_t;
        scoped_ptr_vector<val2elem_t> m_val2elem;

        val2elem_t& get_table(sort* s) {
            unsigned idx = 0;
            if (!m_sort2idx.find(s, idx)) {
                idx = m_val2elem.size();   
                m_sort2idx.insert(s, idx);
                m_val2elem.push_back(alloc(val2elem_t));
            }
            return *m_val2elem[idx];
        }

        bool is_uf(expr* t) {
            return is_app(t) && to_app(t)->get_family_id() == null_family_id && to_app(t)->get_num_args() > 0;
        }

        val2elem_t& ensure_table(sort* s) {
            val2elem_t& v2e = get_table(s);
            if (v2e.empty()) {
                v2e.insert(m.mk_true(), nullptr);
            }
            ptr_vector<expr> keys, values;
            for (auto const& kv : v2e) {
                if (kv.m_value) return v2e;
                keys.push_back(kv.m_key);
                values.push_back(m.mk_model_value(values.size(), s));
                m_pinned.push_back(values.back());                
            }
            m_context.get_model().register_usort(s, values.size(), values.c_ptr());
            for (unsigned i = 0; i < keys.size(); ++i) {
                v2e.insert(keys[i], values[i]);
            }
            return v2e;
        }

    public:

        uf_plugin(plugin_context& context):
            theory_plugin(context)
        {}
        
        void check_term(expr* t, unsigned round) override {
            sort* s = m.get_sort(t);
            if (round == 0 && is_uf(t)) {
                TRACE("smtfd_verbose", tout << "check-term: " << mk_bounded_pp(t, m, 2) << "\n";);
                enforce_congruence(to_app(t)->get_decl(), to_app(t), s);
            }
            else if (round == 1 && sort_covered(s) && m.is_value(t)) {
                expr_ref v = eval_abs(t);
                val2elem_t& v2e = get_table(s);
                expr* e;
                if (v2e.find(v, e) && e != t && m.is_value(e)) {
                    m_context.add(m.mk_not(m.mk_eq(e, t)), __FUNCTION__);
                }
                else {
                    m_pinned.push_back(v);
                    v2e.insert(v, t);
                }
            }
            if (m.is_model_value(t)) {
                //std::cout << "model value: " << mk_bounded_pp(t, m, 2) << " " << eval_abs(t) << " " << mk_pp(s, m) << "\n";
            }
        }

        bool term_covered(expr* t) override {
            sort* s = m.get_sort(t);
            if (sort_covered(s)) {
                val2elem_t& v2e = get_table(s);
                expr_ref v = eval_abs(t);
                if (!v2e.contains(v)) {
                    m_pinned.push_back(v);
                    v2e.insert(v, nullptr);
                }
            }
            check_term(t, 0);
            return is_uf(t) || is_uninterp_const(t) || sort_covered(s);
        }

        bool sort_covered(sort* s) override {
            return s->get_family_id() == m.get_user_sort_family_id();
        }

        void reset() override {
            theory_plugin::reset();
            for (auto& v2e : m_val2elem) {
                v2e->reset();
            }
        }

        unsigned max_rounds() override { return 1; }

        void populate_model(model_ref& mdl, expr_ref_vector const& terms) override {
            expr_ref_vector args(m);
            for (table* tb : m_tables) {
                func_interp* fi = nullptr;
                func_decl* fn = nullptr;
                for (f_app const& f : *tb) {
                    fn = to_func_decl(f.m_f);
                    unsigned arity = fn->get_arity();
                    if (!fi) {
                        fi = alloc(func_interp, m, arity);
                    }
                    args.reset();
                    for (expr* arg : *f.m_t) {
                        args.push_back(model_value(arg));
                    }
                    expr_ref val = model_value(f.m_t);
                    TRACE("smtfd_verbose", tout << mk_bounded_pp(f.m_t, m, 2) << " := " << val << "\n";);
                    fi->insert_new_entry(args.c_ptr(), val);
                }
                mdl->register_decl(fn, fi);
            }
            for (expr* t : subterms(terms)) {
                if (is_uninterp_const(t) && sort_covered(m.get_sort(t))) {
                    expr_ref val = model_value(t);
                    mdl->register_decl(to_app(t)->get_decl(), val);
                }
            }
        }

        expr_ref model_value_core(expr* t) override { 
            sort* s = m.get_sort(t);
            if (sort_covered(s)) {
                auto& v2e = ensure_table(s);
                return expr_ref(v2e[eval_abs(t)], m);
            }
            return expr_ref(m); 
        }
        expr_ref model_value_core(sort* s) override { 
            if (sort_covered(s)) {
                auto& v2e = ensure_table(s);
                return expr_ref(v2e.begin()->m_value, m);
            }
            return expr_ref(m); 
        }
        
    };

    class ar_plugin : public theory_plugin {
        array_util      m_autil;
        unsigned_vector m_num_stores;

        // count number of equivalent stores
        void update_lambda(expr* t) {
            if (m_autil.is_store(t)) {
                expr_ref tV = eval_abs(t);
                inc_lambda(tV);
            }
        }

        unsigned get_lambda(expr* tV) {
            unsigned id = tV->get_id();
            if (id >= m_num_stores.size()) {
                m_num_stores.resize(id + 1, 0);
            }
            return m_num_stores[id];
        }

        void inc_lambda(expr* tV) {
            unsigned id = tV->get_id();
            if (id >= m_num_stores.size()) {
                m_num_stores.resize(id + 1, 0);
            }
            if (0 == m_num_stores[id]++) {
                m_pinned.push_back(tV);
            }
        }

        void insert_select(app* t) {
            expr* a = t->get_arg(0);
            expr_ref vA = eval_abs(a);
            check_congruence(vA, t, m.get_sort(a));
        }

        void check_select(app* t) {
            expr* a = t->get_arg(0);
            expr_ref vA = eval_abs(a);
            TRACE("smtfd", tout << mk_bounded_pp(t, m, 2) << "\n";);
            enforce_congruence(vA, t, m.get_sort(a));                                 
        }

        // check that (select(t, t.args) = t.value)
        void check_store0(app * t) {
            SASSERT(m_autil.is_store(t));
            m_args.reset();
            m_args.push_back(t);
            for (unsigned i = 1; i + 1 < t->get_num_args(); ++i) {
                m_args.push_back(t->get_arg(i));
            }
            app_ref sel(m_autil.mk_select(m_args), m);
            expr* stored_value = t->get_arg(t->get_num_args()-1);
            expr_ref val1 = eval_abs(sel);
            expr_ref val2 = eval_abs(stored_value);
            // A[i] = v
            if (val1 != val2) {
                TRACE("smtfd", tout << "select/store: " << mk_bounded_pp(t, m, 2) << "\n";);
                m_context.add(m.mk_eq(sel, stored_value), __FUNCTION__);
                m_pinned.push_back(sel);
                insert_select(sel);
            }
        }

        // store(A, i, v)[j] = A[i] or i = j
        void check_select_store(app * t) {
            SASSERT(m_autil.is_select(t));
            if (!m_autil.is_store(t->get_arg(0))) {
                return;
            }
            app* store = to_app(t->get_arg(0));
            expr* val = store->get_arg(store->get_num_args()-1);
            expr* a = store->get_arg(0);
            expr_ref_vector eqs(m);
            m_args.reset();
            m_args.push_back(a);
            for (unsigned i = 1; i < t->get_num_args(); ++i) {
                expr* arg1 = t->get_arg(i);
                expr* arg2 = store->get_arg(i);
                m_args.push_back(arg1);
                if (arg1 == arg2) {
                    // skip
                }
                else if (m.are_distinct(arg1, arg2)) {
                    eqs.push_back(m.mk_false());
                }
                else {
                    eqs.push_back(m.mk_eq(arg1, arg2));
                }
            }
            //if (eqs.empty()) return;
            expr_ref eq = mk_and(eqs);
            expr_ref eqV = eval_abs(eq);
            expr_ref val1 = eval_abs(t);
            expr_ref val2 = eval_abs(val);
            if (val1 != val2 && !m.is_false(eqV)) {
                m_context.add(m.mk_implies(mk_and(eqs), m.mk_eq(t, val)), __FUNCTION__);
            }
            
            app_ref sel(m_autil.mk_select(m_args), m);
            val2 = eval_abs(sel);
            if (val1 != val2 && !m.is_true(eqV)) {
                TRACE("smtfd", tout << "select/store: " << mk_bounded_pp(t, m, 2) << "\n";);                
                m_context.add(m.mk_or(m.mk_eq(sel, t), mk_and(eqs)), __FUNCTION__);
                m_pinned.push_back(sel);
                insert_select(sel);
            }
        }

        /** 
            every t and a must agree with select values that
            are different from updates in t.

            let t := store(B, i, v)

            add axioms of the form: 

                 i = j or A != B or store(B,i,v)[j] = A[j]

            where j is in tableA and value equal to some index in tableT

        */
        void check_store2(app* t) {
            SASSERT(m_autil.is_store(t));

            expr* arg = t->get_arg(0);
            expr_ref vT = eval_abs(t);
            expr_ref vA = eval_abs(arg);

            table& tT = ast2table(vT, m.get_sort(t)); // select table of t
            table& tA = ast2table(vA, m.get_sort(arg)); // select table of arg

            if (vT == vA) {                
                return;
            }

            m_vargs.reset();
            for (unsigned i = 0; i + 1 < t->get_num_args(); ++i) {
                m_vargs.push_back(eval_abs(t->get_arg(i)));
            }            
            reconcile_stores(t, vT, tT, vA, tA);
        }
        
        //
        // T = store(A, i, v)
        // T[j] = w: i = j or A[j] = T[j]
        // A[j] = w: i = j or T[j] = A[j]
        // 
        void reconcile_stores(app* t, expr* vT, table& tT, expr* vA, table& tA) {
            unsigned r = 0;
            //if (get_lambda(vA) <= 1) {
            //    return;
            //}
            //std::cout << get_lambda(vA) << " " << get_lambda(vT) << "\n";
            inc_lambda(vT);
            for (auto& fA : tA) {
                f_app fT;
                if (m_context.at_max()) {
                    break;
                }
                if (m.get_sort(t) != m.get_sort(fA.m_t->get_arg(0))) {
                    continue;
                }
                if (!tT.find(fA, fT) || (value_of(fA) != value_of(fT) && !eq(m_vargs, fA))) {
                    add_select_store_axiom(t, fA);
                    ++r;
                }
            }            
#if 0
            // only up-propagation really needed.
            for (auto& fT : tT) {
                f_app fA;
                if (m_context.at_max()) {
                    break;
                }
                if (!tA.find(fT, fA) && m.get_sort(t) == m.get_sort(fT.m_t->get_arg(0))) {
                    TRACE("smtfd", tout << "not found\n";);
                    add_select_store_axiom(t, fT);
                    ++r;
                }
            }
#endif
        }

        void add_select_store_axiom(app* t, f_app& f) {
            SASSERT(m_autil.is_store(t));
            expr* a = t->get_arg(0);
            m_args.reset();
            for (expr* arg : *f.m_t) {
                m_args.push_back(arg);
            }
            SASSERT(m.get_sort(t) == m.get_sort(a));
            TRACE("smtfd", tout << mk_bounded_pp(t, m, 2) << " " << mk_bounded_pp(f.m_t, m, 2) << "\n";);
            expr_ref eq = mk_eq_idxs(t, f.m_t);
            m_args[0] = t;
            expr_ref sel1(m_autil.mk_select(m_args), m);
            m_args[0] = a;
            expr_ref sel2(m_autil.mk_select(m_args), m);
            expr_ref fml(m.mk_or(eq, m.mk_eq(sel1, sel2)), m);
            if (!is_true_abs(fml)) {
                m_context.add(fml, __FUNCTION__);
            }
        }

        bool same_array_sort(f_app const& fA, f_app const& fT) const {
            return m.get_sort(fA.m_t->get_arg(0)) == m.get_sort(fT.m_t->get_arg(0));
        }

        /**
           Enforce M[x] == rewrite(M[x]) for every A[x] such that M = A under current model.
         */
        void beta_reduce(expr* t) {
            if (m_autil.is_map(t) ||
                m_autil.is_const(t) ||
                is_lambda(t)) {
                expr_ref vT = eval_abs(t);
                table& tT = ast2table(vT, m.get_sort(t));
                for (f_app & f : tT) {
                    if (m.get_sort(t) != m.get_sort(f.m_t->get_arg(0))) 
                        continue;
                    if (m_context.at_max()) 
                        break;
                    m_args.reset();
                    m_args.append(f.m_t->get_num_args(), f.m_t->get_args());                    
                    m_args[0] = t;
                    expr_ref sel(m_autil.mk_select(m_args), m);
                    expr_ref selr = sel;
                    m_context.rewrite(selr);
                    expr_ref vS = eval_abs(sel);
                    expr_ref vR = eval_abs(selr);
                    if (vS != vR) {
                        m_context.add(m.mk_eq(sel, selr), __FUNCTION__);
                    }
                }
            }
        }

        // arguments, except for array variable are equal.
        bool eq(expr_ref_vector const& args, f_app const& f) {
            SASSERT(args.size() == f.m_t->get_num_args());
            for (unsigned i = args.size(); i-- > 1; ) {
                if (args.get(i) != m_values.get(f.m_val_offset + i))
                    return false;
            }
            return true;
        }

        expr_ref mk_eq_idxs(app* t, app* s) {
            SASSERT(m_autil.is_store(t));
            SASSERT(m_autil.is_select(s));
            expr_ref_vector r(m);
            for (unsigned i = 1; i < s->get_num_args(); ++i) {
                r.push_back(m.mk_eq(t->get_arg(i), s->get_arg(i)));
            }
            return mk_and(r);
        }


        bool same_table(table const& t1, table const& t2) {
            if (t1.size() != t2.size()) {
                return false;
            }
            for (f_app const& f1 : t1) {
                f_app f2;
                if (!t2.find(f1, f2) || value_of(f1) != value_of(f2)) {
                    return false;
                } 
            }
            return true;
        }

        bool same_table(expr* v1, sort* s1, expr* v2, sort* s2) {
            return same_table(ast2table(v1, s1), ast2table(v2, s2));
        }

        void enforce_extensionality(expr* a, expr* b) {
            sort* s = m.get_sort(a);
            unsigned arity = get_array_arity(s);
            expr_ref_vector args(m);
            args.push_back(a);
            for (unsigned i = 0; i < arity; ++i) {
                args.push_back(m.mk_app(m_autil.mk_array_ext(s, i), a, b));
            }
            expr_ref a1(m_autil.mk_select(args), m);
            args[0] = b;
            expr_ref b1(m_autil.mk_select(args), m);
            expr_ref ext(m.mk_iff(m.mk_eq(a1, b1), m.mk_eq(a, b)), m);
            if (!m.is_true(eval_abs(ext))) {
                TRACE("smtfd", tout << mk_bounded_pp(a, m, 2) << " " << mk_bounded_pp(b, m, 2) << "\n";);
                m_context.add(ext, __FUNCTION__);            
            }
        }

        expr_ref mk_array_value(table& t) {
            expr_ref value(m), default_value(m);
            SASSERT(!t.empty());
            expr_ref_vector args(m);
            for (f_app const& f : t) {
                SASSERT(m_autil.is_select(f.m_t));
                expr_ref v = model_value(f.m_t);
                if (!value) {
                    sort* s = m.get_sort(f.m_t->get_arg(0));
                    default_value = v;
                    value = m_autil.mk_const_array(s, default_value);
                }
                else if (v != default_value) {
                    args.reset();
                    args.push_back(value);
                    for (unsigned i = 1; i < f.m_t->get_num_args(); ++i) {
                        args.push_back(model_value(f.m_t->get_arg(i)));
                    }
                    args.push_back(v);
                    value = m_autil.mk_store(args);
                }
            }
            return value;
        }

    public:

        ar_plugin(plugin_context& context):
            theory_plugin(context),
            m_autil(m)
        {}

        void reset() override {
            theory_plugin::reset();
            m_num_stores.reset();
        }
        
        void check_term(expr* t, unsigned round) override {
            switch (round) {
            case 0:
                if (m_autil.is_select(t)) {
                    insert_select(to_app(t));
                }
                else if (m_autil.is_store(t)) {
                    update_lambda(t);
                    check_store0(to_app(t));
                }
                break;
            case 1:
                if (m_autil.is_select(t)) {
                    check_select(to_app(t));
                }
                else {
                    beta_reduce(t);
                }
                break;
            case 2:
                if (m_autil.is_store(t)) {
                    check_store2(to_app(t));
                }
                else if (m_autil.is_select(t)) {
                    check_select_store(to_app(t));
                }
                break;
            default:
                break;
            }
        }

        bool term_covered(expr* t) override {
            // populate congruence table for model building
            if (m_autil.is_select(t)) {
                expr* a = to_app(t)->get_arg(0);
                expr_ref vA = eval_abs(a);
                insert(mk_app(vA, to_app(t), m.get_sort(a)));                
                
            }
            return 
                m_autil.is_store(t) ||
                m_autil.is_select(t) ||
                m_autil.is_map(t) ||
                m_autil.is_ext(t) ||
                is_lambda(t) ||
                m_autil.is_const(t);
        }

        bool sort_covered(sort* s) override {
            if (!m_autil.is_array(s)) {
                return false;
            }
            if (!m_context.sort_covered(get_array_range(s))) {
                return false;
            }
            for (unsigned i = 0; i < get_array_arity(s); ++i) {
                if (!m_context.sort_covered(get_array_domain(s, i))) 
                    return false;
            }
            return true;
        }

        expr_ref model_value_core(expr* t) override { 
            if (m_autil.is_array(t)) {
                expr_ref vT = eval_abs(t);
                table& tb = ast2table(vT, m.get_sort(t));
                if (tb.empty()) {
                    return model_value_core(m.get_sort(t));
                }
                else {
                    return mk_array_value(tb);
                }
            }
            return expr_ref(m);
        }

        expr_ref model_value_core(sort* s) override { 
            if (m_autil.is_array(s)) {
                return expr_ref(m_autil.mk_const_array(s, model_value(get_array_range(s))), m);
            }
            return expr_ref(m);
        }


        void populate_model(model_ref& mdl, expr_ref_vector const& terms) override {
            for (expr* t : subterms(terms)) {
                if (is_uninterp_const(t) && m_autil.is_array(t)) {
                    mdl->register_decl(to_app(t)->get_decl(), model_value_core(t));
                }
            }
        }

        unsigned max_rounds() override { return 3; }

        void global_check(expr_ref_vector const& core) override {  
            expr_mark seen;
            expr_ref_vector shared(m), sharedvals(m);
            for (expr* t : subterms(core)) {
                if (!is_app(t)) continue;
                app* a = to_app(t);
                unsigned offset = 0;
                if (m_autil.is_select(t) || m_autil.is_store(t)) {
                    offset = 1;
                }
                else if (m_autil.is_map(t)) {
                    continue;
                }

                for (unsigned i = a->get_num_args(); i-- > offset; ) {
                    expr* arg = a->get_arg(i);
                    if (m_autil.is_array(arg) && !seen.is_marked(arg)) {
                        shared.push_back(arg);
                        seen.mark(arg, true);
                    }
                }
            }
            for (expr* s : shared) {
                sharedvals.push_back(eval_abs(s));
            }
            for (unsigned i = 0; !m_context.at_max() && i < shared.size(); ++i) {
                expr* s1 = shared.get(i);
                expr* v1 = sharedvals.get(i);
                for (unsigned j = i + 1; !m_context.at_max() && j < shared.size(); ++j) {
                    expr* s2 = shared.get(j);
                    expr* v2 = sharedvals.get(j);
                    if (v1 != v2 && m.get_sort(s1) == m.get_sort(s2) && same_table(v1, m.get_sort(s1), v2, m.get_sort(s2))) {
                        enforce_extensionality(s1, s2);
                    }
                }
            }
        }
    };


    class mbqi {
        ast_manager&                    m;
        plugin_context&                 m_context;
        obj_hashtable<quantifier>       m_enforced;
        model_ref                       m_model;
        ref<::solver>                   m_solver;
        obj_pair_map<expr, sort, expr*> m_val2term;
        expr_ref_vector                 m_val2term_trail;
        expr_ref_vector                 m_fresh_trail;
        obj_map<sort, obj_hashtable<expr>*> m_fresh;
        scoped_ptr_vector<obj_hashtable<expr>> m_values;

        expr* abs(expr* e) { return m_context.get_abs().abs(e);  }
        expr_ref eval_abs(expr* t) { return (*m_model)(abs(t)); }

        void restrict_to_universe(expr * sk, ptr_vector<expr> const & universe) {
            SASSERT(!universe.empty());
            expr_ref_vector eqs(m);
            for (expr * e : universe) {
                eqs.push_back(m.mk_eq(sk, e));
            }
            expr_ref fml = mk_or(eqs);
            m_solver->assert_expr(fml);
        }

        void register_value(expr* e) {
            sort* s = m.get_sort(e);
            obj_hashtable<expr>* values = nullptr;
            if (!m_fresh.find(s, values)) {
                values = alloc(obj_hashtable<expr>);
                m_fresh.insert(s, values);
                m_values.push_back(values);
            }
            if (!values->contains(e)) {
                for (expr* b : *values) {
                    m_context.add(m.mk_not(m.mk_eq(e, b)), __FUNCTION__);
                }
                values->insert(e);
                m_fresh_trail.push_back(e);
            }
        }

        // sort -> [ value -> expr ]
        // for fixed value return expr
        // new fixed value is distinct from other expr
        expr_ref replace_model_value(expr* e) {
            if (m.is_model_value(e)) { 
                register_value(e);
                expr_ref r(e, m);
                return r;
            }
            if (is_app(e) && to_app(e)->get_num_args() > 0) {
                expr_ref_vector args(m);
                for (expr* arg : *to_app(e)) {
                    args.push_back(replace_model_value(arg));
                }
                return expr_ref(m.mk_app(to_app(e)->get_decl(), args.size(), args.c_ptr()), m);
            }
            return expr_ref(e, m);
        }

        // !Ex P(x) => !P(t)
        // Ax P(x) => P(t)
        // l_true: new instance
        // l_false: no new instance
        // l_undef unresolved
        lbool check_forall(quantifier* q) {
            expr_ref tmp(m);
            unsigned sz = q->get_num_decls();
            if (!m_model->eval_expr(q->get_expr(), tmp, true)) {
                return l_undef;
            }
            if (is_forall(q) && m.is_true(tmp)) {
                return l_false;
            }
            if (is_exists(q) && m.is_false(tmp)) {
                return l_false;
            }
            TRACE("smtfd", 
                  tout << mk_pp(q, m) << "\n";
                  /*tout << *m_model << "\n"; */
                  tout << "eval: " << tmp << "\n";);


            m_solver->push();
            expr_ref_vector vars(m), vals(m);
            vars.resize(sz, nullptr);
            vals.resize(sz, nullptr);
            for (unsigned i = 0; i < sz; ++i) {
                sort* s = q->get_decl_sort(i);
                vars[i] = m.mk_fresh_const(q->get_decl_name(i), s, false);    
                if (m_model->has_uninterpreted_sort(s)) {
                    restrict_to_universe(vars.get(i), m_model->get_universe(s));
                }
            }
            var_subst subst(m);
            expr_ref body = subst(tmp, vars.size(), vars.c_ptr());
            
            if (is_forall(q)) {
                body = m.mk_not(body);
            }

            m_solver->assert_expr(body);
            lbool r = m_solver->check_sat(0, nullptr);
            model_ref mdl;
            TRACE("smtfd", tout << "check: " << r << "\n";);
            
            if (r == l_true) {
                expr_ref qq(q->get_expr(), m);
                for (expr* t : subterms(qq)) {
                    init_term(t);
                }
                m_solver->get_model(mdl);
                TRACE("smtfd", tout << *mdl << "\n";);

                for (unsigned i = 0; i < sz; ++i) {
                    app* v = to_app(vars.get(i));
                    func_decl* f = v->get_decl();
                    expr_ref val(mdl->get_some_const_interp(f), m);
                    if (!val) {
                        r = l_undef;
                        break;
                    }                    
                    expr* t = nullptr;
                    if (m_val2term.find(val, m.get_sort(v), t)) {
                        val = t;
                    }
                    else {
                        val = replace_model_value(val);
                    }
                    vals[i] = val;
                }
            }

            if (r == l_true) {                
                body = subst(q->get_expr(), vals.size(), vals.c_ptr());
                m_context.rewrite(body);
                TRACE("smtfd", tout << "vals: " << vals << "\n" << body << "\n";);
                if (is_forall(q)) {
                    body = m.mk_implies(q, body);
                }
                else {
                    body = m.mk_implies(body, q);
                }
                IF_VERBOSE(10, verbose_stream() << body << "\n");
                m_context.add(body, __FUNCTION__);
            }
            m_solver->pop(1);
            return r;
        }

        // 
        lbool check_exists(quantifier* q) {
            if (m_enforced.contains(q)) {
                return l_true;
            }
            expr_ref tmp(m);
            expr_ref_vector vars(m);
            unsigned sz = q->get_num_decls();
            vars.resize(sz, nullptr);
            for (unsigned i = 0; i < sz; ++i) {
                vars[i] = m.mk_fresh_const(q->get_decl_name(i), q->get_decl_sort(i));    
            }
            var_subst subst(m);
            expr_ref body = subst(q->get_expr(), vars.size(), vars.c_ptr());
            if (is_exists(q)) {
                body = m.mk_implies(q, body);
            }
            else {
                body = m.mk_implies(body, q);
            }
            m_enforced.insert(q);
            m_context.add(body, __FUNCTION__);
            return l_true;
        }

        void init_term(expr* t) {
            if (!m.is_bool(t) && is_ground(t)) {
                expr_ref v = eval_abs(t);
                if (!m_val2term.contains(v, m.get_sort(t))) {
                    m_val2term.insert(v, m.get_sort(t), t);
                    m_val2term_trail.push_back(v);
                }
            }
        }

    public:

        mbqi(plugin_context& c):
            m(c.get_manager()),
            m_context(c),
            m_model(nullptr),
            m_solver(nullptr),
            m_val2term_trail(m),
            m_fresh_trail(m)
        {}

        void set_model(model* mdl) { m_model = mdl; }

        ref<::solver> & get_solver() { return m_solver; }
            
        void init_val2term(expr_ref_vector const& fmls, expr_ref_vector const& core) {
            m_val2term_trail.reset();
            m_val2term.reset();
            for (expr* t : subterms(core)) {
                init_term(t);
            }
            for (expr* t : subterms(fmls)) {
                init_term(t);
            }
        }

        bool check_quantifiers(expr_ref_vector const& core) {
            bool result = true;
            IF_VERBOSE(9, 
                       for (expr* c : core) {
                           verbose_stream() << "core: " << mk_bounded_pp(c, m, 2) << "\n";
                       });
            for (expr* c : core) {
                lbool r = l_false;
                IF_VERBOSE(10, verbose_stream() << "core: " << mk_bounded_pp(c, m, 2) << "\n");
                if (is_forall(c)) {
                    r = check_forall(to_quantifier(c));
                }
                else if (is_exists(c)) {
                    r = check_exists(to_quantifier(c));
                }
                else if (m.is_not(c, c)) {
                    if (is_forall(c)) {
                        r = check_exists(to_quantifier(c));
                    }
                    else if (is_exists(c)) {
                        r = check_forall(to_quantifier(c));
                    }
                }
                if (r == l_undef) {
                    result = false;
                }
            }
            return result;
        }
    };

    class solver : public solver_na2as {
        stats           m_stats;
        ast_manager&    m;
        mutable smtfd_abs m_abs;
        unsigned        m_indent;
        plugin_context  m_context;
        uf_plugin       m_uf;
        ar_plugin       m_ar;
        bv_plugin       m_bv;
        basic_plugin    m_bs;
        pb_plugin       m_pb;
        ref<::solver>   m_fd_sat_solver;
        ref<::solver>   m_fd_core_solver;
        mbqi            m_mbqi;
        expr_ref_vector m_assertions;
        unsigned_vector m_assertions_lim;
        unsigned        m_assertions_qhead;
        expr_ref_vector m_axioms;
        unsigned_vector m_axioms_lim;
        expr_ref_vector m_toggles;
        unsigned_vector m_toggles_lim;
        model_ref       m_model;
        std::string     m_reason_unknown;

        void set_delay_simplify() {
            params_ref p;
            p.set_uint("simplify.delay", 10000);
            m_fd_sat_solver->updt_params(p);
            m_fd_core_solver->updt_params(p);
        }

        expr* add_toggle(expr* toggle) {
            m_toggles.push_back(abs(toggle));
            return toggle;
        }

        bool is_toggle(expr* e) {
            return m_toggles.contains(e);
        }

        void indent() {
            for (unsigned i = 0; i < m_indent; ++i) verbose_stream() << " ";
        }

        void flush_assertions() {
            SASSERT(m_assertions_qhead <= m_assertions.size());
            unsigned sz = m_assertions.size() - m_assertions_qhead;
            if (sz > 0) {
                m_assertions.push_back(m_toggles.back());                
                expr_ref fml(m.mk_and(sz + 1, m_assertions.c_ptr() + m_assertions_qhead), m);
                m_assertions.pop_back();                
                expr* toggle = add_toggle(m.mk_fresh_const("toggle", m.mk_bool_sort()));
                m_assertions_qhead = m_assertions.size();
                TRACE("smtfd", tout << "flush: " << m_assertions_qhead << " " << mk_bounded_pp(fml, m, 3) << "\n";);
                fml = abs(fml);
                m_fd_sat_solver->assert_expr(fml);                
                fml = m.mk_not(m.mk_and(toggle, fml));
                m_fd_core_solver->assert_expr(fml);
                flush_atom_defs();
            }
        }

        lbool check_abs(unsigned num_assumptions, expr * const * assumptions) {
            expr_ref_vector asms(m);
            init_assumptions(num_assumptions, assumptions, asms);
            TRACE("smtfd", 
                  for (unsigned i = 0; i < num_assumptions; ++i) {
                      tout << mk_bounded_pp(assumptions[i], m, 3) << "\n";
                  }
                  display(tout << asms << "\n"););
            TRACE("smtfd_verbose", m_fd_sat_solver->display(tout););

            lbool r = m_fd_sat_solver->check_sat(asms);
            update_reason_unknown(r, m_fd_sat_solver);
            set_delay_simplify();
            return r;
        }

        // not necessarily prime
        lbool get_prime_implicate(unsigned num_assumptions, expr * const * assumptions, expr_ref_vector& core) {
            expr_ref_vector asms(m);
            m_fd_sat_solver->get_model(m_model);
            m_model->set_model_completion(true);
            init_model_assumptions(num_assumptions, assumptions, asms);
            TRACE("smtfd", display(tout << asms << "\n" << *m_model << "\n"););
            lbool r = m_fd_core_solver->check_sat(asms);
            update_reason_unknown(r, m_fd_core_solver);
            if (r == l_false) {
                m_fd_core_solver->get_unsat_core(core);
                TRACE("smtfd", display(tout << core << "\n"););
                SASSERT(asms.contains(m_toggles.back()));
                SASSERT(core.contains(m_toggles.back()));
                core.erase(m_toggles.back());
                rep(core);
            }
            return r;
        }

        bool add_theory_axioms(expr_ref_vector const& core) {
            m_context.reset(m_model);           
            expr_ref_vector terms(core);
            terms.append(m_axioms);

            for (unsigned round = 0; !m_context.at_max() && m_context.add_theory_axioms(terms, round); ++round) {}
            
            TRACE("smtfd", m_context.display(tout););
            for (expr* f : m_context) {
                assert_fd(f);
            }
            m_stats.m_num_lemmas += m_context.size();
            if (m_context.at_max()) {
                m_context.set_max_lemmas(3*m_context.get_max_lemmas()/2);
            }
            return !m_context.empty();
        }

        lbool is_decided_sat(expr_ref_vector const& core) {
            bool has_q = false;
            lbool is_decided = l_true;
            m_context.reset(m_model);
            expr_ref_vector terms(core);
            terms.append(m_axioms);
            for (expr* t : subterms(core)) {
                if (is_forall(t) || is_exists(t)) {
                    has_q = true;
                }
            }
            for (expr* t : subterms(terms)) {
                if (!is_forall(t) && !is_exists(t) && (!m_context.term_covered(t) || !m_context.sort_covered(m.get_sort(t)))) {
                    is_decided = l_false;
                }
            }
            m_context.populate_model(m_model, terms);

            TRACE("smtfd", 
                  tout << "axioms: " << m_axioms << "\n";
                  for (expr* a : subterms(terms)) {
                      expr_ref val0 = (*m_model)(a);
                      expr_ref val1 = (*m_model)(abs(a));
                      if (is_ground(a) && val0 != val1 && m.get_sort(val0) == m.get_sort(val1)) {
                          tout << mk_bounded_pp(a, m, 2) << " := " << val0 << " " << val1 << "\n";
                      }
                      if (!is_forall(a) && !is_exists(a) && (!m_context.term_covered(a) || !m_context.sort_covered(m.get_sort(a)))) {
                          tout << "not covered: " << mk_pp(a, m) << " " << mk_pp(m.get_sort(a), m) << " "; 
                          tout << m_context.term_covered(a) << " " << m_context.sort_covered(m.get_sort(a)) << "\n";
                      }
                  }
                  tout << "has quantifier: " << has_q << "\n" << core << "\n";
                  tout << *m_model.get() << "\n";
                  );

            DEBUG_CODE(
                bool found_bad = false;
                for (expr* a : subterms(core)) {
                    expr_ref val0 = (*m_model)(a);
                    expr_ref val1 = (*m_model)(abs(a));
                    if (is_ground(a) && val0 != val1 && m.get_sort(val0) == m.get_sort(val1)) {
                        std::cout << mk_bounded_pp(a, m, 2) << " := " << val0 << " " << val1 << "\n";
                        found_bad = true;
                    }
                }
                if (found_bad) {
                    std::cout << "core: " << core << "\n";
                    std::cout << *m_model.get() << "\n";
                    exit(0);
                });

            if (!has_q) {
                return is_decided;
            }
            m_mbqi.set_model(m_model.get());
            if (!m_mbqi.get_solver()) {
                m_mbqi.get_solver() = alloc(solver, m_indent + 1, m, get_params());
            }
            m_mbqi.init_val2term(m_assertions, core);
            if (!m_mbqi.check_quantifiers(core) && m_context.empty()) {
                return l_false;
            }
            for (expr* f : m_context) {
                IF_VERBOSE(10, verbose_stream() << "lemma: " << f->get_id() << ": " << expr_ref(f, m) << "\n");
                assert_fd(f);
            }
            m_stats.m_num_mbqi += m_context.size();
            IF_VERBOSE(10, verbose_stream() << "context size: " << m_context.size() << "\n");
            return m_context.empty() ? is_decided : l_undef;
        }

        void init_assumptions(unsigned sz, expr* const* user_asms, expr_ref_vector& asms) {
            asms.reset();
            for (unsigned i = 0; i < sz; ++i) {
                asms.push_back(abs_assumption(user_asms[i]));
            }
            flush_atom_defs();
        }

        void init_model_assumptions(unsigned sz, expr* const* user_asms, expr_ref_vector& asms) {
            asms.reset();
            asms.push_back(m_toggles.back());
            for (unsigned i = 0; i < sz; ++i) {
                asms.push_back(abs(user_asms[i]));
            }
            for (expr* a : m_abs.atoms()) {
                if (is_toggle(a)) {
                    
                }
                else if (m_model->is_true(a)) {
                    //for (expr* t : subterms(expr_ref(a, m))) {
                    //    std::cout << expr_ref(t, m) << " " << (*m_model.get())(t) << "\n";
                    //}
                    asms.push_back(a);
                }
                else {
                    asms.push_back(m.mk_not(a));
                }
            }
        }

        void checkpoint() {
            if (m.canceled()) {
                throw tactic_exception(m.limit().get_cancel_msg());
            }
        }

        expr* rep(expr* e) { return m_abs.rep(e); }
        expr* abs(expr* e) { return m_abs.abs(e); }
        expr* abs_assumption(expr* e) { return m_abs.abs_assumption(e);  }
        expr_ref_vector& rep(expr_ref_vector& v) { for (unsigned i = v.size(); i-- > 0; ) v[i] = rep(v.get(i)); return v; }        
        expr_ref_vector& abs(expr_ref_vector& v) { for (unsigned i = v.size(); i-- > 0; ) v[i] = abs(v.get(i)); return v; }
        
        void init() {
            m_axioms.reset();
            if (!m_fd_sat_solver) {
                m_fd_sat_solver = mk_fd_solver(m, get_params());
                m_fd_core_solver = mk_fd_solver(m, get_params());
            }
        }

        std::ostream& display(std::ostream& out, unsigned n = 0, expr * const * assumptions = nullptr) const override {
            if (!m_fd_sat_solver) return out;
            // m_fd_sat_solver->display(out);
            // out << m_assumptions << "\n";
            m_abs.display(out);
            return out;
        }

        void update_reason_unknown(lbool r, ::solver_ref& s) {
            if (r == l_undef) m_reason_unknown = s->reason_unknown();
        }
        
    public:
        solver(unsigned indent, ast_manager& m, params_ref const& p):
            solver_na2as(m),
            m(m),
            m_abs(m, m_stats),
            m_indent(indent),
            m_context(m_abs, m),
            m_uf(m_context),
            m_ar(m_context),
            m_bv(m_context),
            m_bs(m_context),
            m_pb(m_context),
            m_mbqi(m_context),
            m_assertions(m),
            m_assertions_qhead(0),
            m_axioms(m),
            m_toggles(m)
        {            
            updt_params(p);
            add_toggle(m.mk_true());
        }
        
        ~solver() override {}
        
        ::solver* translate(ast_manager& dst_m, params_ref const& p) override {
            solver* result = alloc(solver, m_indent, dst_m, p);
            if (m_fd_sat_solver) result->m_fd_sat_solver = m_fd_sat_solver->translate(dst_m, p);
            if (m_fd_core_solver) result->m_fd_core_solver = m_fd_core_solver->translate(dst_m, p);
            return result;
        }
        
        void assert_expr_core(expr* t) override {
            m_assertions.push_back(t);
        }
        
        void push_core() override {
            init();
            flush_assertions();
            m_abs.push();
            m_fd_sat_solver->push();
            m_fd_core_solver->push();
            m_assertions_lim.push_back(m_assertions.size());
            m_axioms_lim.push_back(m_axioms.size());
            m_toggles_lim.push_back(m_toggles.size());
        }
        
        void pop_core(unsigned n) override {
            m_fd_sat_solver->pop(n);
            m_fd_core_solver->pop(n);
            m_abs.pop(n);
            unsigned sz = m_toggles_lim[m_toggles_lim.size() - n];
            m_toggles.shrink(sz);
            m_toggles_lim.shrink(m_toggles_lim.size() - n);
            m_assertions.shrink(m_assertions_lim[m_assertions_lim.size() - n]);
            m_assertions_lim.shrink(m_assertions_lim.size() - n);
            m_axioms.shrink(m_axioms_lim[m_axioms_lim.size() - n]);
            m_axioms_lim.shrink(m_axioms_lim.size() - n);
            m_assertions_qhead = m_assertions.size();
        }

        void flush_atom_defs() {
            CTRACE("smtfd", !m_abs.atom_defs().empty(), for (expr* f : m_abs.atom_defs()) tout << mk_bounded_pp(f, m, 4) << "\n";);
            for (expr* f : m_abs.atom_defs()) {
                m_fd_sat_solver->assert_expr(f);
                m_fd_core_solver->assert_expr(f);
                // TBD we want these too: m_axioms.push_back(f);
            }
            m_abs.reset_atom_defs();
        }

        void assert_fd(expr* fml) {
            expr_ref _fml(fml, m);
            TRACE("smtfd", tout << mk_bounded_pp(fml, m, 3) << "\n";);
            CTRACE("smtfd", m_axioms.contains(fml), 
                   tout << "formula:\n" << _fml << "\n";
                   tout << "axioms:\n" << m_axioms << "\n";
                   tout << "assertions:\n" << m_assertions << "\n";);

            // if (m_axioms.contains(fml)) return;
            SASSERT(!m_axioms.contains(fml));
            m_axioms.push_back(fml);
            _fml = abs(fml);
            TRACE("smtfd", tout << mk_bounded_pp(_fml, m, 3) << "\n";);
            m_fd_sat_solver->assert_expr(_fml);
            m_fd_core_solver->assert_expr(_fml);
            flush_atom_defs();
        }

        void block_core(expr_ref_vector const& core) {
            expr_ref fml(m.mk_not(mk_and(core)), m);
            TRACE("smtfd", tout << "block:\n" << mk_bounded_pp(fml, m, 3) << "\n" << mk_bounded_pp(abs(fml), m, 3) << "\n";);
            assert_fd(fml);
        }

        lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override {
            init();
            flush_assertions();
            lbool r = l_undef;
            expr_ref_vector core(m), axioms(m);
            while (true) {
                IF_VERBOSE(1, indent(); verbose_stream() << "(smtfd-check-sat :rounds " << m_stats.m_num_rounds 
                           << " :lemmas " << m_stats.m_num_lemmas << " :qi " << m_stats.m_num_mbqi << ")\n");
                m_stats.m_num_rounds++;
                checkpoint();
            
                // phase 1: check sat of abs
                r = check_abs(num_assumptions, assumptions);
                if (r != l_true) {
                    break;
                }
            
                // phase 2: find prime implicate over FD (abstraction)
                r = get_prime_implicate(num_assumptions, assumptions, core);
                if (r != l_false) {
                    break;
                }
             
                // phase 3: check if prime implicate is really valid, or add theory lemmas until there is a theory core
                r = refine_core(core);
                switch (r) {
                case l_true:
                    switch (is_decided_sat(core)) {
                    case l_true:
                        return l_true;
                    case l_undef:
                        break;
                    case l_false:
                        break;
                    }
                    break;
                case l_false:
                    block_core(core);
                    break;
                case l_undef:
                    return r;
                }
            }
            return r;
        }

        lbool refine_core(expr_ref_vector & core) {
            lbool r = l_true;
            unsigned round = 0;
            m_context.reset(m_model);
            while (true) {
                
                expr_ref_vector terms(core);
                terms.append(m_axioms);

                if (!m_context.add_theory_axioms(terms, round)) {
                    break;
                }
                if (m_context.empty()) {
                    ++round;
                    continue;
                }
                IF_VERBOSE(1, indent(); verbose_stream() << "(smtfd-round :round " << round << " :lemmas " << m_context.size() << ")\n");
                round = 0;
                TRACE("smtfd_verbose", 
                      for (expr* f : m_context) tout << "refine " << mk_bounded_pp(f, m, 3) << "\n";
                      m_context.display(tout););
                for (expr* f : m_context) {
                    assert_fd(f);
                }        
                m_stats.m_num_lemmas += m_context.size();
                m_context.reset(m_model);
                r = check_abs(core.size(), core.c_ptr());
                update_reason_unknown(r, m_fd_sat_solver);
                switch (r) {
                case l_false:
                    m_fd_sat_solver->get_unsat_core(core);
                    rep(core);
                    return r;
                case l_true:
                    m_fd_sat_solver->get_model(m_model);
                    m_model->set_model_completion(true);
                    m_context.reset(m_model);
                    break;
                default:
                    return r;
                }
            }
            // context is satisfiable
            SASSERT(r == l_true);
            return r;
        }

        void updt_params(params_ref const & p) override { 
            ::solver::updt_params(p); 
            if (m_fd_sat_solver) {
                m_fd_sat_solver->updt_params(p);  
                m_fd_core_solver->updt_params(p);  
            }
            m_context.set_max_lemmas(UINT_MAX); // p.get_uint("max-lemmas", 100));
        }        

        void collect_param_descrs(param_descrs & r) override { 
            init();
            m_fd_sat_solver->collect_param_descrs(r); 
            r.insert("max-lemmas", CPK_UINT, "maximal number of lemmas per round", "10");
        }    

        void set_produce_models(bool f) override { }
        void set_progress_callback(progress_callback * callback) override { }
        void collect_statistics(statistics & st) const override {
            if (m_fd_sat_solver) {
                m_fd_sat_solver->collect_statistics(st); 
                m_fd_core_solver->collect_statistics(st); 
            }         
            st.update("smtfd-num-lemmas", m_stats.m_num_lemmas);
            st.update("smtfd-num-rounds", m_stats.m_num_rounds);
            st.update("smtfd-num-mbqi",   m_stats.m_num_mbqi);
            st.update("smtfd-num-fresh-bool", m_stats.m_num_fresh_bool);
        }
        void get_unsat_core(expr_ref_vector & r) override { 
            m_fd_sat_solver->get_unsat_core(r);
            rep(r);
        }
        void get_model_core(model_ref & mdl) override { 
            mdl = m_model;
        } 

        model_converter_ref get_model_converter() const override {             
            return m_fd_sat_solver->get_model_converter();
        }
        
        proof * get_proof() override { return nullptr; }
        std::string reason_unknown() const override { return m_reason_unknown; }
        void set_reason_unknown(char const* msg) override { m_reason_unknown = msg; }
        void get_labels(svector<symbol> & r) override { }
        ast_manager& get_manager() const override { return m;  }
        lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override { 
            return l_undef;
        }
        expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) override { 
            return expr_ref_vector(m);
        }
        
        lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override {
            return l_undef;
        }
        
        void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
            init();
            m_fd_sat_solver->get_levels(vars, depth);
        }
        
        expr_ref_vector get_trail() override {
            init();
            return m_fd_sat_solver->get_trail();
        }
        
        unsigned get_num_assertions() const override {
            return m_assertions.size();
        }
        
        expr * get_assertion(unsigned idx) const override {
            return m_assertions.get(idx);
        }
    };

}

solver * mk_smtfd_solver(ast_manager & m, params_ref const & p) {
    return alloc(smtfd::solver, 0, m, p);
}

tactic * mk_smtfd_tactic(ast_manager & m, params_ref const & p) {
    return mk_solver2tactic(mk_smtfd_solver(m, p));
}
