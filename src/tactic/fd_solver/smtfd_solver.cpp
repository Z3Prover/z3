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

     for t in subterms(core) where t is select(A, args):
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

     for t in subterms(core) where t is const(k):
         vk := M(abs(k))
         vT := M(abs(t))
         for v_args2 |-> v2, args2, t2 in table[vT]:
             if vk != v2:
                lemmas += (t = t2 => select(t2, args2) = k)
                or lemmas += (select(t, args2) = k)

     for t in subterms(core) where t is (lambda x . M), t is ground:
         vT := M(abs(t))
         for v_args2 |-> v2, args2, t2 in table[vT]:
             v1 := M(abs(M[args2/x]))
             if v1 != v2:
                lemmas += (t = t2 => select(t2, args2) = M[args2/x])                

     for t in subterms(core) where t is map(f, A, B, C):
         similar to lambda

     for A in array_terms(core):
         // extensionality: 
         vA := M(abs(A))
         B := table[vA].array
         if B = nil:
            table[vA].array := A
         else:
            // add if not already true:
            lemmas += (select(A, delta(A,B)) = select(B, delta(A,B)) => A = B)     

     if AUF solver timed out and lemmas == []:
        really call AUF solver on core
        return sat or continue with adding !core

     add abs(!core) to solver

     add abs(lemmas) to solver
     
*/

#include "util/scoped_ptr_vector.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/th_rewriter.h"
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
        
        std::ostream& display(std::ostream& out) {
            return out << "abs:\n" << m_atoms << "\n";
        }
        
        expr* abs(expr* e) {
            expr* r = try_abs(e);
            if (r) return r;
            m_todo.push_back(e);
            family_id bvfid = m_butil.get_fid();
            family_id bfid = m.get_basic_family_id();
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
                    else if (bvfid == fid || bfid == fid) {
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
            r = m.mk_not(try_rep(r));
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
        expr_ref_vector&         m_lemmas;
        model_ref                m_model;
        expr_ref_vector          m_values;
        ast_ref_vector           m_pinned;
        expr_ref_vector          m_args, m_args2, m_vargs;
        f_app_eq                 m_eq;
        f_app_hash               m_hash;
        scoped_ptr_vector<table> m_tables;
        obj_map<ast, unsigned>   m_ast2table;

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
        theory_plugin(smtfd_abs& a, expr_ref_vector& lemmas, model* mdl) : 
            m(lemmas.get_manager()), 
            m_abs(a),
            m_lemmas(lemmas),
            m_model(mdl),
            m_values(m),
            m_pinned(m),
            m_args(m), m_args2(m), m_vargs(m),
            m_eq(*this),
            m_hash(*this)
        {}

        expr_ref_vector const& values() const { return m_values; }

        ast_manager& get_manager() { return m; }

        void add_lemma(expr* fml) {
            expr_ref _fml(fml, m);
            TRACE("smtfd", tout << _fml << "\n";);
            m_lemmas.push_back(m_abs.abs(fml));
        }

        expr_ref eval_abs(expr* t) { return (*m_model)(m_abs.abs(t)); }
        
        expr* value_of(f_app const& f) const { return m_values[f.m_val_offset + f.m_t->get_num_args()]; }

        void check_ackerman(ast* f, app* t) {
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
        virtual void check_term(expr* t, unsigned round) = 0;
        virtual unsigned max_rounds() = 0;
    };

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
    
    class uf_plugin : public theory_plugin {               

        bool is_uf(expr* t) {
            return is_app(t) && to_app(t)->get_family_id() == null_family_id && to_app(t)->get_num_args() > 0;
        }

    public:

        uf_plugin(smtfd_abs& a, expr_ref_vector& lemmas, model* mdl):
            theory_plugin(a, lemmas, mdl) 
        {}
        
        void check_term(expr* t, unsigned round) override {
            if (round == 0 && is_uf(t)) 
                check_ackerman(to_app(t)->get_decl(), to_app(t));
        }

        unsigned max_rounds() override { return 1; }
        
    };

    class a_plugin : public theory_plugin {
        array_util m_autil;
        th_rewriter m_rewriter;

        void check_select(app* t) {
            expr* a = t->get_arg(0);
            expr_ref vA = eval_abs(a);
            check_ackerman(vA, t);                     
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
            if (val1 != val2) {
                add_lemma(m.mk_eq(sel, stored_value));
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
        void check_store1(app* t) {
            SASSERT(m_autil.is_store(t));

            expr* arg = t->get_arg(0);
            expr_ref vT = eval_abs(t);
            expr_ref vA = eval_abs(arg);
            if (vT == vA) {
                return;
            }
            table& tT = ast2table(vT); // select table of t
            table& tA = ast2table(vA); // select table of arg
            m_vargs.reset();
            m_args.reset();
            m_args.push_back(t);
            for (unsigned i = 0; i + 1 < t->get_num_args(); ++i) {
                m_vargs.push_back(eval_abs(t->get_arg(i)));
                m_args.push_back(t->get_arg(i));
            }
            
            for (auto& fA : tA) {
                f_app fT;
                if (tT.find(fA, fT) && value_of(fA) != value_of(fT) && !eq(m_vargs, fA)) {
                    SASSERT(same_array_sort(fA, fT));
                    m_args2.reset();
                    for (unsigned i = 0; i < t->get_num_args(); ++i) {
                        m_args2.push_back(fA.m_t->get_arg(i));
                    }
                    expr_ref eq = mk_eq_idxs(m_args, m_args2);
                    m_args2[0] = t;
                    add_lemma(m.mk_implies(m.mk_eq(t->get_arg(0), fA.m_t->get_arg(0)), m.mk_or(eq, m.mk_eq(fA.m_t, m_autil.mk_select(m_args2)))));
                }
            }
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
                is_lambda(t)) {
                expr_ref vT = eval_abs(t);
                table& tT = ast2table(vT);
                for (f_app & f : tT) {
                    if (m.get_sort(t) != m.get_sort(f.m_t->get_arg(0))) 
                        continue;
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

        bool eq(expr_ref_vector const& args, f_app const& f) {
            SASSERT(args.size() == f.m_t->get_num_args());
            for (unsigned i = 0, sz = args.size(); i < sz; ++i) {
                if (args.get(i) != m_values.get(f.m_val_offset + 1))
                    return false;
            }
            return true;
        }

        expr_ref mk_eq_idxs(expr_ref_vector const& es1, expr_ref_vector const& es2) {
            SASSERT(es1.size() == es2.size());
            expr_ref_vector r(m);
            for (unsigned i = es1.size(); i-- > 1; ) {
                r.push_back(m.mk_eq(es1[i], es2[i]));
            }
            return mk_and(r);
        }

    public:

        a_plugin(smtfd_abs& a, expr_ref_vector& lemmas, model* mdl):
            theory_plugin(a, lemmas, mdl),
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

        // TBD: enforce extensionality

        unsigned max_rounds() override { return 2; }

    };

    struct stats {
        unsigned m_num_lemmas;
        unsigned m_num_rounds;
        stats() { memset(this, 0, sizeof(stats)); }
    };

    class solver : public solver_na2as {
        ast_manager&    m;
        smtfd_abs       m_abs;
        ref<::solver>   m_fd_solver;
        ref<::solver>   m_smt_solver;
        expr_ref_vector m_assertions;
        unsigned_vector m_assertions_lim;        
        unsigned        m_assertions_qhead;
        expr_ref_vector m_toggles;
        expr_ref        m_toggle, m_not_toggle;
        model_ref       m_model;
        std::string     m_reason_unknown;
        unsigned        m_max_lemmas;
        stats           m_stats;
        unsigned        m_useful_smt, m_non_useful_smt, m_max_conflicts;
        bool            m_smt_known;

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
            lbool r = m_fd_solver->check_sat(asms);
            update_reason_unknown(r, m_fd_solver);
            return r;
        }

        // not necessarily prime
        lbool get_prime_implicate(unsigned num_assumptions, expr * const * assumptions, expr_ref_vector& core) {
            expr_ref_vector asms(m);
            m_fd_solver->get_model(m_model);
            init_literals(num_assumptions, assumptions, asms);
            TRACE("smtfd", display(tout << asms););
            SASSERT(asms.contains(m_not_toggle));
            lbool r = m_fd_solver->check_sat(asms);
            update_reason_unknown(r, m_fd_solver);
            if (r == l_false) {
                m_fd_solver->get_unsat_core(core);
                TRACE("smtfd", display(tout << core););
                core.erase(m_not_toggle); 
                SASSERT(!asms.contains(m_not_toggle));
                SASSERT(!asms.contains(m_toggle));
            }
            return r;
        }

        lbool check_smt(expr_ref_vector& core) {
            rep(core);
            TRACE("smtfd", tout << "core: " << core << "\n";);
            IF_VERBOSE(10, verbose_stream() << "core: " << core << "\n");
            params_ref p;
            p.set_uint("max_conflicts", m_max_conflicts);
            m_smt_solver->updt_params(p);
            lbool r = m_smt_solver->check_sat(core);
            update_reason_unknown(r, m_smt_solver);
            m_smt_known = true;
            if (r == l_false) {
                unsigned sz0 = core.size();
                m_smt_solver->get_unsat_core(core);
                TRACE("smtfd", display(tout << core););
                unsigned sz1 = core.size();
                if (sz1 < sz0) {
                    ++m_useful_smt;
                    m_max_conflicts += 10;
                }
                else {
                    ++m_non_useful_smt;
                    if (m_max_conflicts > 200) m_max_conflicts -= 5;
                }
            }            
            if (r == l_undef) {
                ++m_non_useful_smt;
                m_max_conflicts -= 5;
                if (m_max_conflicts > 200) m_max_conflicts -= 5;
                r = l_false;
                m_smt_known = false;
            }
            return r;
        }

        bool add_theory_lemmas(expr_ref_vector const& core) {
            expr_ref_vector lemmas(m);
            a_plugin ap(m_abs, lemmas, m_model.get());
            uf_plugin uf(m_abs, lemmas, m_model.get());
            unsigned max_rounds = std::max(ap.max_rounds(), uf.max_rounds());
            for (unsigned round = 0; round < max_rounds; ++round) {
                for (expr* t : subterms(core)) {
                    if (lemmas.size() >= m_max_lemmas) 
                        break;
                    ap.check_term(t, round);
                    uf.check_term(t, round);
                }
            }
            for (expr* f : lemmas) {
                IF_VERBOSE(10, verbose_stream() << "lemma: " << expr_ref(rep(f), m) << "\n");
                assert_fd(f);
            }
            m_stats.m_num_lemmas += lemmas.size();
            return !lemmas.empty();
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
            asms.erase(m_toggle);
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
            if (!m_fd_solver) {
                m_fd_solver = mk_fd_solver(m, get_params());
                m_smt_solver = mk_smt_solver(m, get_params(), symbol::null);
                m_smt_solver->updt_params(get_params());
            }
        }

        std::ostream& display(std::ostream& out) {
            init();
            m_fd_solver->display(out);
            m_smt_solver->display(out);
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
            m_assertions(m),
            m_assertions_qhead(0),
            m_abs(m),
            m_toggles(m), 
            m_toggle(m.mk_true(), m), 
            m_not_toggle(m.mk_false(), m),
            m_useful_smt(0),
            m_non_useful_smt(0),
            m_max_conflicts(500)
        {            
            m_max_lemmas = 10;
            updt_params(p);
        }
        
        ~solver() override {}
        
        ::solver* translate(ast_manager& dst_m, params_ref const& p) override {
            solver* result = alloc(solver, dst_m, p);
            if (m_smt_solver) result->m_smt_solver = m_smt_solver->translate(dst_m, p);
            if (m_fd_solver) result->m_fd_solver = m_fd_solver->translate(dst_m, p);
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
            m_fd_solver->push();
            m_smt_solver->push();
            m_assertions_lim.push_back(m_assertions.size());
        }
        
        void pop_core(unsigned n) override {
            m_fd_solver->pop(n);
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
            m_fd_solver->assert_expr(fml);
            for (expr* f : m_abs.atom_defs()) {
                m_fd_solver->assert_expr(f);
            }
            m_abs.reset_atom_defs();
        }
        
        lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override {
            init();
            flush_assertions();
            lbool r;
            expr_ref_vector core(m);
            while (true) {
                IF_VERBOSE(1, verbose_stream() << "(smtfd-check-sat " << m_stats.m_num_rounds << ")\n");
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
                if (r != l_false) {
                    return r;
                }

                // phase 4: add theory lemmas
                if (add_theory_lemmas(core) || m_smt_known) {
                    assert_fd(m.mk_not(mk_and(abs(core))));                
                }
                else {
                    m_max_conflicts *= 2;
                }
            }
            return l_undef;
        }        

        void updt_params(params_ref const & p) override { 
            ::solver::updt_params(p); 
            if (m_fd_solver) {
                m_fd_solver->updt_params(p);  
                m_smt_solver->updt_params(p);  
            }
            m_max_lemmas = p.get_uint("max-lemmas", 10);
        }        

        void collect_param_descrs(param_descrs & r) override { 
            init();
            m_smt_solver->collect_param_descrs(r); 
            m_fd_solver->collect_param_descrs(r); 
            r.insert("max-lemmas", CPK_UINT, "maximal number of lemmas per round", "10");
        }    

        void set_produce_models(bool f) override { }
        void set_progress_callback(progress_callback * callback) override { }
        void collect_statistics(statistics & st) const override {
            m_fd_solver->collect_statistics(st); 
            m_smt_solver->collect_statistics(st);
            st.update("smtfd-num-lemmas", m_stats.m_num_lemmas);
            st.update("smtfd-num-rounds", m_stats.m_num_rounds);
        }
        void get_unsat_core(expr_ref_vector & r) override { 
            m_fd_solver->get_unsat_core(r);            
            r.erase(m_toggle);
            rep(r);
        }
        void get_model_core(model_ref & mdl) override { 
            SASSERT(m_smt_solver);
            m_smt_solver->get_model(mdl);
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
