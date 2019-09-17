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
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "tactic/tactic_exception.h"
#include "tactic/fd_solver/fd_solver.h"
#include "solver/solver.h"
#include "solver/solver_na2as.h"
#include "solver/solver2tactic.h"
#include "smt/smt_solver.h"

namespace smtfd {

    class smtfd_abs {
        ast_manager&    m;
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
            symbol name = is_app(t) ? to_app(t)->get_name() : symbol("X");
            if (m.is_bool(t)) {
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
        
    public:
        smtfd_abs(ast_manager& m):
            m(m),
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
        
        std::ostream& display(std::ostream& out) const {
            return out << "abs:\n" << m_atoms << "\n";
        }
        
        expr* abs(expr* e) {
            expr* r = try_abs(e);
            if (r) return r;
            m_todo.push_back(e);
            family_id bvfid = m_butil.get_fid();
            family_id bfid = m.get_basic_family_id();
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
        unsigned   m_val_offset;
    };

    class theory_plugin;

    class plugin_context {
        smtfd_abs&      m_abs;
        expr_ref_vector m_lemmas;
        unsigned        m_max_lemmas;
        ptr_vector<theory_plugin> m_plugins;
    public:
        plugin_context(smtfd_abs& a, ast_manager& m, unsigned max):
            m_abs(a),
            m_lemmas(m), 
            m_max_lemmas(max)
        {}
        
        smtfd_abs& get_abs() { return m_abs; }

        void add(expr* f) { m_lemmas.push_back(f); }

        ast_manager& get_manager() { return m_lemmas.get_manager(); }

        bool at_max() const { return m_lemmas.size() >= m_max_lemmas; }

        expr_ref_vector::iterator begin() { return m_lemmas.begin(); }
        expr_ref_vector::iterator end() { return m_lemmas.end(); }
        unsigned size() const { return m_lemmas.size(); }
        bool empty() const { return m_lemmas.empty(); }

        void add_plugin(theory_plugin* p) { m_plugins.push_back(p); }

        expr_ref model_value(expr* t);
        expr_ref model_value(sort* s);
        bool term_covered(expr* t);
        bool sort_covered(sort* s);
        void populate_model(model_ref& mdl, expr_ref_vector const& core);
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
        model_ref                m_model;
        expr_ref_vector          m_values;
        ast_ref_vector           m_pinned;
        expr_ref_vector          m_args, m_vargs;
        f_app_eq                 m_eq;
        f_app_hash               m_hash;
        scoped_ptr_vector<table> m_tables;
        obj_map<ast, unsigned>   m_ast2table;


        f_app mk_app(ast* f, app* t) {
            f_app r;
            r.m_f = f;
            r.m_val_offset = m_values.size();
            r.m_t = t;
            for (expr* arg : *t) {
                m_values.push_back(eval_abs(arg));
            }
            m_values.push_back(eval_abs(t));
            return r;
        }

        f_app const& insert(f_app const& f) {
            return ast2table(f.m_f).insert_if_not_there(f);
        }

    public:
        theory_plugin(plugin_context& context, model_ref& mdl) : 
            m(context.get_manager()), 
            m_abs(context.get_abs()),
            m_context(context),
            m_model(mdl),
            m_values(m),
            m_pinned(m),
            m_args(m), 
            m_vargs(m),
            m_eq(*this),
            m_hash(*this)
        {
            m_context.add_plugin(this);
        }

        table& ast2table(ast* f) {
            unsigned idx = 0;
            if (!m_ast2table.find(f, idx)) {
                idx = m_tables.size();
                m_tables.push_back(alloc(table, DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_hash, m_eq));
                m_ast2table.insert(f, idx);
                m_pinned.push_back(f);
            }
            return *m_tables[idx];
        }

        expr_ref_vector const& values() const { return m_values; }

        ast_manager& get_manager() { return m; }

        void add_lemma(expr* fml) {
            expr_ref _fml(fml, m);
            TRACE("smtfd", tout << _fml << "\n";);
            m_context.add(m_abs.abs(fml));
        }

        expr_ref eval_abs(expr* t) { return (*m_model)(m_abs.abs(t)); }
        
        expr* value_of(f_app const& f) const { return m_values[f.m_val_offset + f.m_t->get_num_args()]; }

        bool check_congruence(ast* f, app* t) {
            f_app f1 = mk_app(f, t);
            f_app const& f2 = insert(f1);
            if (f2.m_val_offset == f1.m_val_offset) {
                return true;
            }
            bool eq = value_of(f1) == value_of(f2);
            m_values.shrink(f1.m_val_offset);
            return eq;            
        }

        void enforce_congruence(ast* f, app* t) {
            f_app f1 = mk_app(f, t);
            f_app const& f2 = insert(f1);
            if (f2.m_val_offset == f1.m_val_offset) {
                return;
            }
            bool eq = value_of(f1) == value_of(f2);
            m_values.shrink(f1.m_val_offset);
            if (eq) {
                return;
            }
            m_args.reset();
            for (unsigned i = 0; i < t->get_num_args(); ++i) {
                m_args.push_back(m.mk_eq(f1.m_t->get_arg(i), f2.m_t->get_arg(i)));
            }
            add_lemma(m.mk_implies(mk_and(m_args), m.mk_eq(f1.m_t, f2.m_t)));
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
                out << "key: " << mk_pp(k.m_f, m) << "\nterm: " << mk_pp(k.m_t, m) << "\n";
                out << "args:\n";
                for (unsigned i = 0; i <= k.m_t->get_num_args(); ++i) {
                    out << mk_pp(m_values.get(k.m_val_offset + i), m) << "\n";
                }
                out << "\n";
            }
            return out;
        }

        expr_ref model_value(expr* t) { return m_context.model_value(t); }
        expr_ref model_value(sort* s) { return m_context.model_value(s); }

        virtual void check_term(expr* t, unsigned round) = 0;
        virtual expr_ref model_value_core(expr* t) = 0;
        virtual expr_ref model_value_core(sort* s) = 0;
        virtual bool term_covered(expr* t) = 0;
        virtual bool sort_covered(sort* s) = 0;
        virtual unsigned max_rounds() = 0;
        virtual void populate_model(model_ref& mdl, expr_ref_vector const& core) {}
    };

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

    void plugin_context::populate_model(model_ref& mdl, expr_ref_vector const& core) {
        for (theory_plugin* p : m_plugins) {
            p->populate_model(mdl, core);
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
        basic_plugin(plugin_context& context, model_ref& mdl):
            theory_plugin(context, mdl) 
        {}
        void check_term(expr* t, unsigned round) override { }
        bool term_covered(expr* t) override { return is_app(t) && to_app(t)->get_family_id() == m.get_basic_family_id();  }
        bool sort_covered(sort* s) override { return m.is_bool(s); }
        unsigned max_rounds() override { return 0; }
        void populate_model(model_ref& mdl, expr_ref_vector const& core) override { }
        expr_ref model_value_core(expr* t) override { return m.is_bool(t) ? (*m_model)(m_abs.abs(t)) : expr_ref(m); }
        expr_ref model_value_core(sort* s) override { return m.is_bool(s) ? expr_ref(m.mk_false(), m) : expr_ref(m); }
    };

    class pb_plugin : public theory_plugin {
        pb_util m_pb;
    public:
        pb_plugin(plugin_context& context, model_ref& mdl):
            theory_plugin(context, mdl),
            m_pb(m)
        {}
        void check_term(expr* t, unsigned round) override { }
        bool term_covered(expr* t) override { return is_app(t) && to_app(t)->get_family_id() == m_pb.get_family_id(); }
        bool sort_covered(sort* s) override { return m.is_bool(s); }
        unsigned max_rounds() override { return 0; }
        void populate_model(model_ref& mdl, expr_ref_vector const& core) override { }
        expr_ref model_value_core(expr* t) override { return expr_ref(m); }
        expr_ref model_value_core(sort* s) override { return expr_ref(m); }
    };

    class bv_plugin : public theory_plugin {
        bv_util m_butil;
    public:
        bv_plugin(plugin_context& context, model_ref& mdl):
            theory_plugin(context, mdl),
            m_butil(m)
        {}
        void check_term(expr* t, unsigned round) override { }
        bool term_covered(expr* t) override { return is_app(t) && to_app(t)->get_family_id() == m_butil.get_family_id(); }
        bool sort_covered(sort* s) override { return m_butil.is_bv_sort(s); }
        unsigned max_rounds() override { return 0; }
        void populate_model(model_ref& mdl, expr_ref_vector const& core) override { }
        expr_ref model_value_core(expr* t) override { return m_butil.is_bv(t) ? (*m_model)(m_abs.abs(t)) : expr_ref(m); }
        expr_ref model_value_core(sort* s) override { return m_butil.is_bv_sort(s) ? expr_ref(m_butil.mk_numeral(rational(0), s), m) : expr_ref(m); }
    };

    
    class uf_plugin : public theory_plugin {               

        expr_ref_vector m_pinned;
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
            m_model->register_usort(s, values.size(), values.c_ptr());
            for (unsigned i = 0; i < keys.size(); ++i) {
                v2e.insert(keys[i], values[i]);
            }
            return v2e;
        }

    public:

        uf_plugin(plugin_context& context, model_ref& mdl):
            theory_plugin(context, mdl),
            m_pinned(m)
        {}
        
        void check_term(expr* t, unsigned round) override {
            if (round == 0 && is_uf(t)) 
                enforce_congruence(to_app(t)->get_decl(), to_app(t));
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
            return is_uf(t) || is_uninterp_const(t);
        }

        bool sort_covered(sort* s) override {
            return s->get_family_id() == m.get_user_sort_family_id();
        }

        unsigned max_rounds() override { return 1; }

        void populate_model(model_ref& mdl, expr_ref_vector const& core) override {
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
                    fi->insert_new_entry(args.c_ptr(),val);
                }
                mdl->register_decl(fn, fi);
            }
            for (expr* t : subterms(core)) {
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

    class a_plugin : public theory_plugin {
        array_util m_autil;
        th_rewriter m_rewriter;

        void check_select(app* t) {
            expr* a = t->get_arg(0);
            expr_ref vA = eval_abs(a);
            enforce_congruence(vA, t);                     
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
                add_lemma(m.mk_eq(sel, stored_value));
            }
            m_pinned.push_back(sel);
            TRACE("smtfd", tout << sel << "\n";);
            check_select(sel);
        }

        /** 
            every t and a must agree with select values that
            are different from updates in t.

            let t := store(B, i, v)

            add axioms of the form: 

                 i = j or A != B or store(B,i,v)[j] = A[j]

            where j is in tableA and value equal to some index in tableT

        */
        void check_store1(app* t) {
            SASSERT(m_autil.is_store(t));

            expr* arg = t->get_arg(0);
            expr_ref vT = eval_abs(t);
            expr_ref vA = eval_abs(arg);

            table& tT = ast2table(vT); // select table of t
            table& tA = ast2table(vA); // select table of arg

            if (vT == vA) {                
                TRACE("smtfd", display(tout << "eq\n", tT););
                return;
            }

            TRACE("smtfd", tout << mk_pp(t, m) << "\n" << vT << "\n" << vA << "\n";);
            m_vargs.reset();
            for (unsigned i = 0; i + 1 < t->get_num_args(); ++i) {
                m_vargs.push_back(eval_abs(t->get_arg(i)));
            }            
            reconcile_stores(t, tT, tA);
        }
        
        //
        // T = store(A, i, v)
        // T[j] = w: i = j or A[j] = T[j]
        // A[j] = w: i = j or T[j] = A[j]
        // 
        void reconcile_stores(app* t, table& tT, table& tA) {
            for (auto& fA : tA) {
                f_app fT;
                if (m_context.at_max()) {
                    break;
                }
                if (!tT.find(fA, fT) || (value_of(fA) != value_of(fT) && !eq(m_vargs, fA))) {
                    add_select_store_axiom(t, fA);
                }
            }            
            for (auto& fT : tT) {
                f_app fA;
                if (m_context.at_max()) {
                    break;
                }
                if (!tA.find(fT, fA)) {
                    add_select_store_axiom(t, fT);
                }
            }
        }

        void add_select_store_axiom(app* t, f_app& f) {
            SASSERT(m_autil.is_store(t));
            expr* a = t->get_arg(0);
            m_args.reset();
            for (expr* arg : *f.m_t) {
                m_args.push_back(arg);
            }
            expr_ref eq = mk_eq_idxs(t, f.m_t);
            m_args[0] = t;
            expr_ref sel1(m_autil.mk_select(m_args), m);
            m_args[0] = a;
            expr_ref sel2(m_autil.mk_select(m_args), m);
            add_lemma(m.mk_or(eq, m.mk_eq(sel1, sel2)));
        }

        bool same_array_sort(f_app const& fA, f_app const& fT) const {
            return m.get_sort(fA.m_t->get_arg(0)) == m.get_sort(fT.m_t->get_arg(0));
        }

        /**
           Enforce M[x] == rewrite(M[x]) for every A[x] such that M = A under current model.
         */
        void beta_reduce(expr* t) {
            bool added = false;
            if (m_autil.is_map(t) ||
                m_autil.is_const(t) ||
                is_lambda(t)) {
                expr_ref vT = eval_abs(t);
                table& tT = ast2table(vT);
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
                    m_rewriter(selr);
                    expr_ref vS = eval_abs(sel);
                    expr_ref vR = eval_abs(selr);
                    if (vS != vR) {
                        add_lemma(m.mk_eq(sel, selr));
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

        bool same_table(expr* v1, expr* v2) {
            return same_table(ast2table(v1), ast2table(v2));
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
            add_lemma(m.mk_implies(m.mk_eq(a1, b1), m.mk_eq(a, b)));            
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

        a_plugin(plugin_context& context, model_ref& mdl):
            theory_plugin(context, mdl),
            m_autil(m),
            m_rewriter(m)
        {}
        
        void check_term(expr* t, unsigned round) override {
            switch (round) {
            case 0:
                if (m_autil.is_select(t)) {
                    check_select(to_app(t));
                }
                if (m_autil.is_store(t)) {
                    check_store0(to_app(t));
                }
                break;
            case 1:
                if (m_autil.is_store(t)) {
                    check_store1(to_app(t));
                }
                else {
                    beta_reduce(t);
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
                insert(mk_app(vA, to_app(t)));                
                
            }
            return 
                m_autil.is_store(t) ||
                m_autil.is_select(t) ||
                m_autil.is_map(t) ||
                m_autil.is_ext(t) ||
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
                table& tb = ast2table(vT);
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


        void populate_model(model_ref& mdl, expr_ref_vector const& core) override {
            for (expr* t : subterms(core)) {
                if (is_uninterp_const(t) && m_autil.is_array(t)) {
                    mdl->register_decl(to_app(t)->get_decl(), model_value_core(t));
                }
            }
        }

        unsigned max_rounds() override { return 2; }

        void global_check(expr_ref_vector const& core) {  
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
                    if (v1 != v2 && m.get_sort(s1) == m.get_sort(s2) && same_table(v1, v2)) {
                        enforce_extensionality(s1, s2);
                    }
                }
            }
        }

    };

    class mbqi {
        ast_manager&    m;
        plugin_context& m_context;
        obj_hashtable<quantifier>& m_enforced;
        model_ref       m_model;
        ref<::solver>   m_solver;
        expr_ref_vector m_pinned;
        obj_map<expr, expr*> m_val2term;

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

            m_solver->push();
            expr_ref_vector vars(m), vals(m);
            vars.resize(sz, nullptr);
            vals.resize(sz, nullptr);
            for (unsigned i = 0; i < sz; ++i) {
                sort* s = q->get_decl_sort(i);
                vars[i] = m.mk_fresh_const(q->get_decl_name(i), s);    
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
            
            if (r == l_true) {
                expr_ref qq(q->get_expr(), m);
                for (expr* t : subterms(qq)) {
                    if (is_ground(t)) {                       
                        expr_ref v = eval_abs(t);
                        m_pinned.push_back(v);
                        m_val2term.insert(v, t);
                    }
                }
                m_solver->get_model(mdl);
                for (unsigned i = 0; i < sz; ++i) {
                    app* v = to_app(vars.get(i));
                    func_decl* f = v->get_decl();
                    expr_ref val(mdl->get_some_const_interp(f), m);
                    if (!val) {
                        r = l_undef;
                        break;
                    }
                    expr* t = nullptr;
                    if (m_val2term.find(val, t)) {
                        val = t;
                    }
                    vals[i] = val;
                }
                if (r == l_true) {
                    body = subst(q->get_expr(), vals.size(), vals.c_ptr());
                    if (is_forall(q)) {
                        body = m.mk_implies(q, body);
                    }
                    else {
                        body = m.mk_implies(body, q);
                    }
                    body = abs(body);
                    m_context.add(body);
                }
            }
            m_solver->pop(1);
            return r;
        }

        lbool check_exists(quantifier* q) {
            if (m_enforced.contains(q)) {
                return l_true;
            }
            expr_ref tmp(m);
            expr_ref_vector vars(m);
            unsigned sz = q->get_num_decls();
            vars.resize(sz, nullptr);
            for (unsigned i = 0; i < sz; ++i) {
                vars[sz - i - 1] = m.mk_fresh_const(q->get_decl_name(i), q->get_decl_sort(i));    
            }
            var_subst subst(m);
            expr_ref body = subst(tmp, vars.size(), vars.c_ptr());
            if (is_exists(q)) {
                body = m.mk_implies(q, body);
            }
            else {
                body = m.mk_implies(body, q);
            }
            m_enforced.insert(q);
            m_context.add(abs(body));
            return l_true;
        }

        void init_val2term(expr_ref_vector const& core) {
            for (expr* t : subterms(core)) {
                if (!m.is_bool(t) && is_ground(t)) {
                    expr_ref v = eval_abs(t);
                    m_pinned.push_back(v);
                    m_val2term.insert(v, t);
                }
            }
        }

    public:

        mbqi(::solver* s, plugin_context& c, obj_hashtable<quantifier>& enforced, model_ref& mdl):
            m(s->get_manager()),
            m_context(c),
            m_enforced(enforced),
            m_model(mdl),
            m_solver(s),
            m_pinned(m)
        {}
            
        bool check_quantifiers(expr_ref_vector const& core) {
            bool result = true;
            init_val2term(core);
            for (expr* c : core) {
                lbool r = l_false;
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


    struct stats {
        unsigned m_num_lemmas;
        unsigned m_num_rounds;
        unsigned m_num_mbqi;
        stats() { memset(this, 0, sizeof(stats)); }
    };

    class solver : public solver_na2as {
        ast_manager&    m;
        smtfd_abs       m_abs;
        ref<::solver>   m_fd_sat_solver;
        ref<::solver>   m_fd_core_solver;
        ref<::solver>   m_smt_solver;
        ref<solver>     m_mbqi_solver;
        expr_ref_vector m_assertions;
        unsigned_vector m_assertions_lim;
        unsigned        m_assertions_qhead;
        expr_ref_vector m_toggles;
        expr_ref        m_toggle;
        expr_ref        m_not_toggle;
        model_ref       m_model;
        std::string     m_reason_unknown;
        unsigned        m_max_lemmas;
        stats           m_stats;
        unsigned        m_max_conflicts;
        obj_hashtable<quantifier> m_enforced_quantifier;

        void set_delay_simplify() {
            params_ref p;
            p.set_uint("simplify.delay", 10000);
            m_fd_sat_solver->updt_params(p);
            m_fd_core_solver->updt_params(p);
        }

        void flush_assertions() {
            SASSERT(m_assertions_qhead <= m_assertions.size());
            unsigned sz = m_assertions.size() - m_assertions_qhead;
            if (sz > 0) {
                m_assertions.push_back(m_toggle);
                expr_ref fml(m.mk_and(sz + 1, m_assertions.c_ptr() + m_assertions_qhead), m);
                m_assertions.pop_back();
                m_toggle = m.mk_fresh_const("toggle", m.mk_bool_sort());
                m_not_toggle = m.mk_not(m_toggle);
                m_not_toggle = abs(m_not_toggle);
                m_assertions_qhead = m_assertions.size();
                fml = m.mk_iff(m_toggle, fml);
                assert_fd(abs(fml));
            }
        }

        lbool check_abs(unsigned num_assumptions, expr * const * assumptions) {
            expr_ref_vector asms(m);
            init_assumptions(num_assumptions, assumptions, asms);
            TRACE("smtfd", display(tout << asms););
            SASSERT(asms.contains(m_toggle));
            m_fd_sat_solver->assert_expr(m_toggle);
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
            init_literals(num_assumptions, assumptions, asms);
            TRACE("smtfd", display(tout << asms););
            SASSERT(asms.contains(m_not_toggle));
            lbool r = m_fd_core_solver->check_sat(asms);
            update_reason_unknown(r, m_fd_core_solver);
            if (r == l_false) {
                m_fd_core_solver->get_unsat_core(core);
                TRACE("smtfd", display(tout << core););
                core.erase(m_not_toggle.get()); 
                SASSERT(asms.contains(m_not_toggle));
                SASSERT(!asms.contains(m_toggle));
            }
            return r;
        }

        lbool check_smt(expr_ref_vector& core) {
            rep(core);
            IF_VERBOSE(10, verbose_stream() << "core: " << core.size() << "\n");
            params_ref p;
            p.set_uint("max_conflicts", m_max_conflicts);
            m_smt_solver->updt_params(p);
            lbool r = m_smt_solver->check_sat(core);
            TRACE("smtfd", tout << "core: " << core << "\nresult: " << r << "\n";);
            update_reason_unknown(r, m_smt_solver);
            switch (r) {
            case l_false: {
                unsigned sz0 = core.size();
                m_smt_solver->get_unsat_core(core);
                TRACE("smtfd", display(tout << core););
                unsigned sz1 = core.size();
                if (sz1 < sz0) {
                    m_max_conflicts += 10;
                }
                else {
                    if (m_max_conflicts > 20) m_max_conflicts -= 5;
                }
                break;
            }
            case l_undef:
                if (m_max_conflicts > 20) m_max_conflicts -= 5;
                break;
            case l_true:
                m_smt_solver->get_model(m_model);
                break;
            }
            return r;
        }


        bool add_theory_lemmas(expr_ref_vector const& core) {
            plugin_context context(m_abs, m, m_max_lemmas);
            a_plugin  ap(context, m_model);
            uf_plugin uf(context, m_model);

            unsigned max_rounds = std::max(ap.max_rounds(), uf.max_rounds());
            for (unsigned round = 0; round < max_rounds; ++round) {
                for (expr* t : subterms(core)) {
                    if (context.at_max()) break;
                    ap.check_term(t, round);
                    uf.check_term(t, round);
                }
            }
            ap.global_check(core);
            TRACE("smtfd", context.display(tout););
            for (expr* f : context) {
                IF_VERBOSE(10, verbose_stream() << "lemma: " << expr_ref(rep(f), m) << "\n");
                assert_fd(f);
            }
            m_stats.m_num_lemmas += context.size();
            if (context.at_max()) {
                m_max_lemmas = (3*m_max_lemmas)/2;
            }
            return !context.empty();
        }

        lbool is_decided_sat(expr_ref_vector const& core) {
            plugin_context context(m_abs, m, m_max_lemmas);
            uf_plugin    uf(context, m_model);            
            a_plugin     ap(context, m_model);
            bv_plugin    bv(context, m_model);
            basic_plugin bs(context, m_model);
            pb_plugin    pb(context, m_model);
            
            bool has_q = false;
            bool has_non_covered = false;
            for (expr* t : subterms(core)) {
                if (is_forall(t) || is_exists(t)) {
                    has_q = true;
                }
                else if (!context.term_covered(t) || !context.sort_covered(m.get_sort(t))) {
                    has_non_covered = true;
                }
            }
            context.populate_model(m_model, core);
            
            TRACE("smtfd", tout << has_q << " " << has_non_covered << "\n";);
            if (!has_q) {
                return has_non_covered ? l_false : l_true;
            }
            if (!m_mbqi_solver) {
                m_mbqi_solver = alloc(solver, m, get_params());
            }
            mbqi mb(m_mbqi_solver.get(), context, m_enforced_quantifier, m_model);
            if (!mb.check_quantifiers(core) && context.empty()) {
                return l_false;
            }
            for (expr* f : context) {
                IF_VERBOSE(10, verbose_stream() << "lemma: " << expr_ref(rep(f), m) << "\n");
                assert_fd(f);
            }
            m_stats.m_num_mbqi += context.size();

            if (context.empty()) {                
                return has_non_covered ? l_false : l_true;
            }
            else {
                return l_undef;
            }
        }

        void init_assumptions(unsigned sz, expr* const* user_asms, expr_ref_vector& asms) {
            asms.reset();
            asms.push_back(m_toggle);
            for (unsigned i = 0; i < sz; ++i) {
                asms.push_back(abs(user_asms[i]));
            }
        }

        void init_literals(unsigned sz, expr* const* user_asms, expr_ref_vector& asms) {
            asms.reset();
            asms.push_back(m_not_toggle);
            for (unsigned i = 0; i < sz; ++i) {
                asms.push_back(abs(user_asms[i]));
            }
            for (expr* a : m_abs.atoms()) {
                if (m_model->is_true(a)) {
                    asms.push_back(a);
                }
                else {
                    asms.push_back(m.mk_not(a));
                }
            }
            asms.erase(m_toggle.get());
        }

        void checkpoint() {
            if (m.canceled()) {
                throw tactic_exception(m.limit().get_cancel_msg());
            }
        }

        expr* rep(expr* e) { return m_abs.rep(e);  }
        expr* abs(expr* e) { return m_abs.abs(e);  }
        expr_ref_vector& rep(expr_ref_vector& v) { for (unsigned i = v.size(); i-- > 0; ) v[i] = rep(v.get(i)); return v; }        
        expr_ref_vector& abs(expr_ref_vector& v) { for (unsigned i = v.size(); i-- > 0; ) v[i] = abs(v.get(i)); return v; }
        
        void init() {
            if (!m_fd_sat_solver) {
                m_fd_sat_solver = mk_fd_solver(m, get_params());
                m_fd_core_solver = mk_fd_solver(m, get_params());
                m_smt_solver = mk_smt_solver(m, get_params(), symbol::null);
                m_smt_solver->updt_params(get_params());
            }
        }

        std::ostream& display(std::ostream& out, unsigned n = 0, expr * const * assumptions = nullptr) const override {
            if (!m_fd_sat_solver) return out;
            m_fd_sat_solver->display(out);
            //m_fd_core_solver->display(out << "core solver\n");
            //m_smt_solver->display(out << "smt solver\n");
            out << m_assumptions << "\n";
            m_abs.display(out);
            return out;
        }

        void update_reason_unknown(lbool r, ::solver_ref& s) {
            if (r == l_undef) m_reason_unknown = s->reason_unknown();
        }
        
    public:
        solver(ast_manager& m, params_ref const& p):
            solver_na2as(m),
            m(m),
            m_abs(m),
            m_assertions(m),
            m_assertions_qhead(0),
            m_toggles(m), 
            m_toggle(m.mk_true(), m), 
            m_not_toggle(m.mk_false(), m),
            m_max_conflicts(50)
        {            
            updt_params(p);
        }
        
        ~solver() override {}
        
        ::solver* translate(ast_manager& dst_m, params_ref const& p) override {
            solver* result = alloc(solver, dst_m, p);
            if (m_smt_solver) result->m_smt_solver = m_smt_solver->translate(dst_m, p);
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
            m_toggles.push_back(m_toggle);
            m_abs.push();
            m_fd_sat_solver->push();
            m_fd_core_solver->push();
            m_smt_solver->push();
            m_assertions_lim.push_back(m_assertions.size());
        }
        
        void pop_core(unsigned n) override {
            m_fd_sat_solver->pop(n);
            m_fd_core_solver->pop(n);
            m_smt_solver->pop(n);
            m_abs.pop(n);
            m_toggle = m_toggles.get(m_toggles.size() - n);
            m_not_toggle = m.mk_not(m_toggle);
            m_toggles.shrink(m_toggles.size() - n);
            m_assertions.shrink(m_assertions_lim[m_assertions_lim.size() - n]);
            m_assertions_lim.shrink(m_assertions_lim.size() - n);
            m_assertions_qhead = m_assertions.size();
        }

        void assert_fd(expr* fml) {
            m_fd_sat_solver->assert_expr(fml);
            m_fd_core_solver->assert_expr(fml);
            for (expr* f : m_abs.atom_defs()) {
                m_fd_sat_solver->assert_expr(f);
                m_fd_core_solver->assert_expr(f);
            }
            m_abs.reset_atom_defs();
        }
        
        lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override {
            init();
            flush_assertions();
            lbool r;
            expr_ref_vector core(m);
            while (true) {
                IF_VERBOSE(1, verbose_stream() << "(smtfd-check-sat " << m_stats.m_num_rounds << " " << m_stats.m_num_lemmas << " " << m_stats.m_num_mbqi << ")\n");
                m_stats.m_num_rounds++;
                checkpoint();

                // phase 1: check sat of abs
                r = check_abs(num_assumptions, assumptions);
                if (r != l_true) {
                    return r;
                }

                // phase 2: find prime implicate over FD (abstraction)
                r = get_prime_implicate(num_assumptions, assumptions, core);
                if (r != l_false) {
                    return r;
                }

                // phase 3: prime implicate over SMT
                r = check_smt(core);
                if (r == l_true) {
                    return r;
                }

                // phase 4: add theory lemmas
                if (r == l_false) {
                    assert_fd(m.mk_not(mk_and(abs(core))));
                }
                if (add_theory_lemmas(core)) {
                    continue;
                }
                if (r != l_undef) {
                    continue;
                }
                switch (is_decided_sat(core)) {
                case l_true:
                    return l_true;
                case l_undef:
                    break;
                case l_false:
                    // m_max_conflicts = UINT_MAX;
                    break;
                }
            }
            return l_undef;
        }        

        void updt_params(params_ref const & p) override { 
            ::solver::updt_params(p); 
            if (m_fd_sat_solver) {
                m_fd_sat_solver->updt_params(p);  
                m_fd_core_solver->updt_params(p);  
                m_smt_solver->updt_params(p);  
            }
            m_max_lemmas = p.get_uint("max-lemmas", 100);
        }        

        void collect_param_descrs(param_descrs & r) override { 
            init();
            m_smt_solver->collect_param_descrs(r); 
            m_fd_sat_solver->collect_param_descrs(r); 
            r.insert("max-lemmas", CPK_UINT, "maximal number of lemmas per round", "10");
        }    

        void set_produce_models(bool f) override { }
        void set_progress_callback(progress_callback * callback) override { }
        void collect_statistics(statistics & st) const override {
            if (m_fd_sat_solver) {
                m_fd_sat_solver->collect_statistics(st); 
                m_fd_core_solver->collect_statistics(st); 
                m_smt_solver->collect_statistics(st);   
            }         
            st.update("smtfd-num-lemmas", m_stats.m_num_lemmas);
            st.update("smtfd-num-rounds", m_stats.m_num_rounds);
            st.update("smtfd-num-mbqi", m_stats.m_num_mbqi);
        }
        void get_unsat_core(expr_ref_vector & r) override { 
            m_fd_sat_solver->get_unsat_core(r);            
            r.erase(m_toggle.get());
            rep(r);
        }
        void get_model_core(model_ref & mdl) override { 
            mdl = m_model;
        } 
        
        model_converter_ref get_model_converter() const override {             
            SASSERT(m_smt_solver);
            return m_smt_solver->get_model_converter();
        }
        proof * get_proof() override { return nullptr; }
        std::string reason_unknown() const override { return m_reason_unknown; }
        void set_reason_unknown(char const* msg) override { m_reason_unknown = msg; }
        void get_labels(svector<symbol> & r) override { init(); m_smt_solver->get_labels(r); }
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
            m_smt_solver->get_levels(vars, depth);
        }
        
        expr_ref_vector get_trail() override {
            init();
            return m_smt_solver->get_trail();
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
    return alloc(smtfd::solver, m, p);
}

tactic * mk_smtfd_tactic(ast_manager & m, params_ref const & p) {
    return mk_solver2tactic(mk_smtfd_solver(m, p));
}
