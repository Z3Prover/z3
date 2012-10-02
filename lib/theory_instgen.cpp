/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_instgen.cpp

Abstract:

    iProver style theory solver.
    It provides an instantiation based engine
    based on InstGen methods together with
    unit propagation.

Author:

    Krystof Hoder (t-khoder) 
    Nikolaj Bjorner (nbjorner) 2011-10-6

Revision History:

Main data-structures:

- Instantiation = Var -> Expr
- MatchingSet = Instantiation-set
  operations:
   - has_instance : Instantiation -> Bool
     has_instance(i) = exists j in MatchingSet . j <= i
- UnificationIndex 
  operations:
   - insert : Expr
   - remove : Expr
   - unify : Expr -> Expr-set   
      - set of inserted expressions that unify
- RootClauseMap : Expr -> Quantifier
  where RootClauseMap(clause) = The quantifier that originated clause
- Occurs : Expr -> Quantifier-set
  the set of quantifiers where non-ground literal occurs.
- LiteralMeanings : Literal -> Expr-set 
  - set of non-ground literals that were grounded to Literal
- InternalizedFoLits : Expr-set
  - forall e in InternalizedFoLits . e \in LiteralMeanings(ground(e))
- MatchingSets : Quantifier -> MatchingSet


Main operation:

 - insert all assigned literals into UnificationIndex
 - for l' in LiteralMeanings(l) do:       
       for m',theta in UnificationIndex.unify(not l') do:
           for q in Occurs(l') do:
               for q' in Occurs(m') do:
                   instantiate q  with theta
                   instantiate q' with theta

    instantiate q with theta:
        
Discussion of plans:

- Efficient unit propagation using the tables from dl_
  See addittional notes under unit propagation.
  The idea is to perfrm unit propagation using the tables 
  provided in the dl_ module. This is similar to unit 
  propagation from the EPR solver and retains succinctness
  features, but does not carry over the splitting component.
  The efficient propagator is aimed at solving ground problems more efficiently,
  for example

- Reduce set of selected literals when clause already has on selected literal.

- Subsumption module:
  - simplify clause using already asserted clauses.
  - check for variants.

- Completeness for EPR with equality:
  The relevant equality clause for EPR are C \/ x = y and C \/ a = x
  Destructive E-resolution (DER) removes disequalities.
  Two approaches:
  1. Rely on super-position/hyper-resolution of ordinary literals 
     in the clause.
  2. Instantiate based on congruence closure.
     The instantiation based approach takes a clause of the form C \/ x = y, 
     where all other non-equality literals in C are assigned false by the 
     current assignment, and (the grounded version U = U' of) x = y is 
     assigned true. Take the equivalence classes of the type of x and 
     instantiate x, y using representatives for different equivalence
     classes. The number of instantiations is potentially quadratic 
     in the number of terms. One reduction considers symmetries: 
     instantiate x by a smaller representative than y.
- Unit propagation:
     - Why should unit-propagation matter: hunch: similar role as 
       theory propagation where conflicts are created close to root 
       of search tree.
     - Add theory identifiers to literals so that assign_eh is invoked.
     - Produce explanation objects for unit propagation.
     - Unit propagation index.
        - Idea only propagate known literals
- Exchange unit literals with super position engine for equalities.
  iProver approach: perform unit super-position proof, get instances 
    by labeling equalities by clauses + substitution (set-labeling)
  portfolio approach: exchange unit literals to super-position 
    (or hypotheses as suggested in more general setting).
      
--*/

#include "theory_instgen.h"
#include "value_factory.h"
#include "smt_model_generator.h"
#include "smt_context.h"
#include "ast_smt2_pp.h"
#include "substitution.h"
#include "substitution_tree.h"
#include "uint_set.h"
#include "unifier.h"
#include "matcher.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "var_subst.h"

#define PP mk_pp

namespace smt {


    //
    // expression grounding for passing to the SMT solver
    //
    class grounder {
        ast_manager& m;
        vector<obj_map<sort,expr*> > m_defaults;
        expr_ref_vector              m_ref_holder;

        class grounding_rewriter_cfg;

        void reserve(unsigned idx) {
            if (m_defaults.size() <= idx) {
                m_defaults.resize(idx+1);
            }
        }

        expr* mk_default(sort* s) {
            return mk_default(0, s);
        }

        expr* mk_default(unsigned i, sort* s) {
            expr* d;
            reserve(i);
            if (!m_defaults[i].find(s, d)) {
                d = m.mk_fresh_const("U",s);
                m_defaults[i].insert(s, d);
                m_ref_holder.push_back(d);
            }
            return d;    
        }
        
        class grounding_rewriter_cfg : public default_rewriter_cfg {
            grounder& m_parent;
            bool      m_collapse;
        public:
            grounding_rewriter_cfg(grounder& parent, bool collapse)
                : m_parent(parent), m_collapse(collapse) {}
            
            bool get_subst(expr * s, expr * & t, proof * & t_pr) {
                SASSERT(is_app(s) || is_var(s));
                if (is_var(s)) {
                    var* v = to_var(s);
                    if (m_collapse) {
                        t = m_parent.mk_default(v->get_sort());
                    }
                    else {
                        t = m_parent.mk_default(v->get_idx(), v->get_sort());
                    }
                }
                return is_var(s);
            }
        };

        void mk(expr * e, app_ref& res, bool collapse) {
            if(is_ground(e)) {
                res = to_app(e);
            }
            else {
                while (is_quantifier(e)) {
                    e = to_quantifier(e)->get_expr();
                }
                SASSERT(is_app(e));
                grounding_rewriter_cfg r_cfg(*this, collapse);
                rewriter_tpl<grounding_rewriter_cfg> rwr(m, false, r_cfg);
                expr_ref res_e(m);
                rwr(e, res_e);
                res = to_app(res_e);
            }
            SASSERT(is_ground(res.get()));
        } 

    public:
        grounder(ast_manager& m): m(m), m_ref_holder(m) {
            reserve(0);
        }

        /** 
            create a grounding that recycles the same constant for
            different variables of the same sort.

            This function can be called either with whole clauses (incl. quantifier), 
            or with literals one by one (without a quantifier) 
        */
        void operator()(expr * e, app_ref& res) {
            mk(e, res, true);
        }

        //
        // create a grounding where different variables have different names
        //
        void mk_diff(expr * e, app_ref& res) {
            mk(e, res, false);
        }        
    };

    //
    // Class for first-order subsumption checking.
    // if clause[renaming] is a superset of existing clause in context, then clause is subsumed.
    // if context => clause         then clause is subsumed.
    // if context & clause => ~ lit then lit is subsumed from clause
    //
    // TBD: 
    // - check unit propagation
    // - use internalizer functions directly. The assertions have already been pre-processed.
    // 
    class clause_subsumption {
        ast_manager& m;
        grounder     m_grounder;
        front_end_params m_params;
        context      m_ctx;
        quantifier_ref_vector m_assumptions;
        unsigned_vector m_limit;
    public:
        clause_subsumption(ast_manager& m, front_end_params& p): 
            m(m), m_grounder(m), m_params(p), m_ctx(m,m_params), m_assumptions(m) {
                m_params.m_instgen = false;
        }
        
        void simplify(quantifier* new_clause, expr_ref& result, ptr_vector<quantifier>& assumptions) {
#if 1
            result = new_clause;
            return;
#endif 

            SASSERT(new_clause->is_forall());
            expr* body = new_clause->get_expr();
            app_ref ground_clause(m);
            m_grounder.mk_diff(new_clause, ground_clause);
            if (is_subsumed(ground_clause)) {
                TRACE("theory_instgen", tout << "subsumed: " << PP(new_clause,m) << "\n";);
                result = m.mk_true();
                return;
            }
            if (is_homomorphic_image(body)) {
                result = m.mk_true();
                return;
            }
            // Assert the current clause.
            m_ctx.internalize(ground_clause, true);
            m_ctx.assign(m_ctx.get_literal(ground_clause), b_justification());
            TRACE("theory_instgen", tout << "Asserting: " << PP(ground_clause,m) << "\n";);
            m_assumptions.push_back(new_clause);
            SASSERT(m.is_or(body) == m.is_or(ground_clause));
            if (!m.is_or(body)) {
                result = new_clause;
                return;
            }
            SASSERT(to_app(body)->get_num_args() == ground_clause->get_num_args());
            ptr_vector<expr> lits;
            for (unsigned i = 0; i < to_app(body)->get_num_args(); ++i) {
                m_ctx.push();
                m_ctx.assign(m_ctx.get_literal(ground_clause->get_arg(i)), b_justification());
                lbool is_sat = m_ctx.check();
                m_ctx.pop(1);
                if (is_sat != l_false) {
                    lits.push_back(to_app(body)->get_arg(i));
                }
                else {
                    TRACE("theory_instgen", tout << "subsumed literal: " << PP(to_app(body)->get_arg(i),m) << "\n";);
                }
            }
            if (lits.size() == ground_clause->get_num_args()) {
                result = new_clause;
            }
            else {
                SASSERT(!lits.empty());
                result = lits.size()==1?lits[0]:m.mk_or(lits.size(), lits.c_ptr());
                result = m.update_quantifier(new_clause, result);
                TRACE("theory_instgen", tout << "simplified: " << PP(new_clause,m) << "\n";
                                        tout << PP(result.get(), m) << "\n";
                     );
                //overapproximation of required assumptions
                //( m_assumptions.size()-1 ... the -1 is not to make ourselves as an assumption)
                assumptions.append(m_assumptions.size()-1, m_assumptions.c_ptr());
            }
        }

        void push() {
            m_ctx.push();
            m_limit.push_back(m_assumptions.size());
        }

        void pop(unsigned num_scopes) { 
            m_ctx.pop(num_scopes);

            unsigned last_idx = m_limit.size()-num_scopes;
            unsigned restored_assumptions_size = m_limit[last_idx];
            m_limit.resize(last_idx);
            m_assumptions.resize(restored_assumptions_size);
        }

    private:

        bool is_subsumed(expr* ground_clause) {
            m_ctx.push();
            m_ctx.internalize(ground_clause, true);
            m_ctx.assign(~m_ctx.get_literal(ground_clause), b_justification());
            lbool is_sat = m_ctx.check();
            m_ctx.pop(1);
            TRACE("theory_instgen", 
                  tout << PP(ground_clause, m) << " " <<
                  ((is_sat==l_false)?"unsat":"sat") << "\n";);
            return (is_sat == l_false);
        }

        bool is_homomorphic_image(expr* body) {
            // TBD
            return false;
        }

    };

    class fo_clause_internalizer;
    class instantiator;
    class theory_instgen_impl;
    typedef expr_ref_vector inst;

    class instantiation_result {
        quantifier_ref m_clause;
        inst           m_subst;
    public:
        instantiation_result(ast_manager& m) : m_clause(m), m_subst(m) {}

        void init(quantifier * q, const inst& subst) {
            SASSERT(!m_clause); //we init each object at most once
            SASSERT(m_subst.empty());
            SASSERT(q);
            m_clause = q;
            m_subst.append(subst);
        }
        quantifier * clause() const { return m_clause; }
        const inst& subst() const { return m_subst; }
    };

    typedef vector<instantiation_result> instantiation_result_vector;

    // TBD: replace this by the substitution tree index. 
    // It should do the trick of identifying instances and generalizers.
    // see matching_set2..
    //
    class matching_set {
        ast_manager& m;
        vector<inst> m_inst;

        //used in the has_instance function
        mutable substitution m_subst;

    public:
        matching_set(ast_manager& m) : m(m), m_subst(m) {}
        unsigned size() const { return m_inst.size(); }
        inst const& operator[](unsigned i) const { return m_inst[i]; }

        void insert(inst const& inst) {
            SASSERT(m_inst.empty() || m_inst.back().size() == inst.size());
            TRACE("theory_instgen_verbose",
            for (unsigned i = 0; i < inst.size(); ++i) {
                tout << PP(inst[i], m) << " ";
            }
            tout << "\n";
            );
            m_inst.push_back(inst);
        }
        void insert(unsigned sz, expr* const* exprs) {
            insert(inst(m, sz, exprs));
        }
        void pop_insert() { m_inst.pop_back(); }

        bool has_instance(inst const& inst) {
            unsigned dont_care;
            return has_instance(inst, dont_care);
        }

        bool has_instance(inst const& new_inst, unsigned& index) {
            for (unsigned i = 0; i < size(); ++i) {
                if (has_instance(new_inst, m_inst[i])) {
                    index = i;
                    return true;
                }
            }
            return false;
        }

        class insert_inst : public trail<smt::context> {
            matching_set& m_ms;
        public:
            insert_inst(matching_set& m): m_ms(m) {}
            virtual void undo(smt::context& ctx) { m_ms.pop_insert(); }
        };

        static bool is_identity(const inst& subst) {
            uint_set vars;
            vars.reset();
            unsigned sz = subst.size();
            for(unsigned i=0; i<sz; i++) {
                expr * val = subst[i];
                if(!is_var(val)) { return false; }
                unsigned var_idx = to_var(val)->get_idx();
                if(vars.contains(var_idx)) {
                    return false;
                }
                vars.insert(var_idx);
            }
            return true;
        }

    private:
        // check if old_instance is an instance of new_instance.
        bool has_instance(inst const& new_instance, inst const& old_instance) const {
            SASSERT(new_instance.size() == old_instance.size());
            unsigned sz = new_instance.size();
            m_subst.reset();
            m_subst.reserve_vars(sz);
            m_subst.reserve_offsets(2);
            matcher mtchr(m);
            for(unsigned i = 0; i < sz; i++) {
                TRACE("theory_instgen_verbose", tout << PP(new_instance[i], m) << " " << PP(old_instance[i], m) << "\n";);
                if(!mtchr(new_instance[i], old_instance[i], m_subst)) {
                    return false;
                }
            }
            return true;
        }
    };


    class matching_set2 {
        class inst_visitor : public st_visitor {
            bool m_found;
        public:
            inst_visitor(substitution& s): st_visitor(s), m_found(false) {}
            virtual bool operator()(expr * e) {
                m_found = true;
                return false;
            }
            void reset() { m_found = false; }
            bool found() const { return m_found; }
        };

        ast_manager&      m;
        substitution_tree m_st;
        func_decl_ref     m_f;
        app_ref_vector    m_trail;
        substitution      m_dummy;
        inst_visitor      m_visitor;

    public:
        matching_set2(ast_manager& m) : m(m), m_st(m), m_f(m), m_trail(m), m_dummy(m), m_visitor(m_dummy) {}

        void insert(inst const& inst) {
            if (!m_f.get()) {
                ptr_buffer<sort> domain;
                for (unsigned i = 0; i < inst.size(); ++i) {
                    domain.push_back(m.get_sort(inst[i]));
                }
                m_f = m.mk_func_decl(symbol("tuple"),inst.size(), domain.c_ptr(), m.mk_bool_sort());
                m_trail.push_back(m.mk_app(m_f, inst.size(), inst.c_ptr()));
                m_st.insert(m_trail.back());
            }
        }
        void insert(unsigned sz, expr* const* exprs) {
            insert(inst(m, sz, exprs));
        }
        void pop_insert() { 
             m_st.erase(m_trail.back()); 
             m_trail.pop_back(); 
        }

        bool has_instance(inst const& inst) {
            app_ref f(m);
            f = m.mk_app(m_f, inst.size(), inst.c_ptr());
            m_visitor.reset();
            m_st.inst(f, m_visitor);
            return m_visitor.found();
        }

        class insert_inst : public trail<smt::context> {
            matching_set& m_ms;
        public:
            insert_inst(matching_set& m): m_ms(m) {}
            virtual void undo(smt::context& ctx) { m_ms.pop_insert(); }
        };

        static bool is_identity(const inst& subst) {
            uint_set vars;
            vars.reset();
            unsigned sz = subst.size();
            for(unsigned i=0; i<sz; i++) {
                expr * val = subst[i];
                if(!is_var(val)) { return false; }
                unsigned var_idx = to_var(val)->get_idx();
                if(vars.contains(var_idx)) {
                    return false;
                }
                vars.insert(var_idx);
            }
            return true;
        }
    };


    /////////////////////////
    // inst_gen_unif_index
    //

    class inst_gen_unif_index {
        ast_manager &     m;
        substitution_tree m_st;
        unsigned          m_num_vars;
        app_ref_vector    m_ref_holder;
        unsigned_vector   m_lim;

        class collecting_visitor : public st_visitor {
            app_ref_vector& m_acc;
        public:
            collecting_visitor(app_ref_vector& acc, substitution& subst)
                : st_visitor(subst), m_acc(acc) {}
            virtual bool operator()(expr * e) {
                SASSERT(is_app(e));
                m_acc.push_back(to_app(e));
                return true;
            }
        };


        class st_contains_visitor : public st_visitor {
            expr* m_e;
            bool m_found;
        public:
            st_contains_visitor(substitution& s, expr* e): st_visitor(s), m_e(e), m_found(false) {}
            virtual bool operator()(expr* e) {
                if (e == m_e) {
                    m_found = true;
                    return false;
                }
                return true;
            }
            bool found() const { return m_found; }
        };

        void debug_st(char const* cmd, app* l) {  
            expr_ref e(m);
            ptr_vector<sort> sorts;
            svector<symbol> names;
            get_free_vars(l, sorts);
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (!sorts[i]) {
                    sorts[i] = m.mk_bool_sort();
                }
                names.push_back(symbol(i));
            }
            sorts.reverse();
            if (!sorts.empty()) {
                e = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), l);
            }
            else {
                e = l;
            }
            std::cout << ":" << cmd << " " << PP(e.get(),m) << "\n";
        }

    public:
        inst_gen_unif_index(ast_manager & m) : 
            m(m), m_st(m), m_num_vars(0), m_ref_holder(m) {}

        void insert_literal(app * lit) {
            // debug_st("st_insert", lit);
            m_ref_holder.push_back(lit);
            m_st.insert(lit);
        }

        void get_unifications(app * lit, app_ref_vector& res) {
            substitution subst(m);
            subst.reserve_vars(m_num_vars);
            subst.reserve_offsets(m_st.get_approx_num_regs());
            collecting_visitor visitor(res, subst);
            // TRACE("theory_instgen", m_st.display(tout); );
            m_st.unify(lit, visitor);
        }
        void reserve_num_vars(unsigned num_vars) {
            if (num_vars > m_num_vars) m_num_vars = num_vars;
        }

        void push() {
            m_lim.push_back(m_ref_holder.size());
        }

        void pop() {
            unsigned sz = m_lim.back();
            m_ref_holder.resize(sz);
            m_lim.pop_back();
            m_st.reset();
        }

        void pop_orig() {
            unsigned sz = m_lim.back();
            while (m_ref_holder.size() > sz) {
                debug_st("st_erase", m_ref_holder.back());
                m_st.erase(m_ref_holder.back());

                substitution subst(m);
                subst.reserve_vars(m_num_vars);
                subst.reserve_offsets(m_st.get_approx_num_regs());
                st_contains_visitor cv(subst, m_ref_holder.back());
                m_st.unify(m_ref_holder.back(), cv);
                if (cv.found()) {
                    m_st.display(std::cout);
                    m_st.erase(m_ref_holder.back());
                }
                SASSERT(!cv.found());
                m_ref_holder.pop_back();
            }
            m_lim.pop_back();
        }

        void display(std::ostream& out) {
            m_st.display(out);
        }

        bool empty() const{
            return m_st.empty();
        }
    };


    ///////////////////////////
    // fo_clause_internalizer
    //

    class fo_clause_internalizer {
    private:
        typedef map<literal, app_ref_vector*, obj_hash<literal>, default_eq<literal> > literal_meaning_map;
        typedef obj_map<expr,quantifier_ref_vector*> occurs;
        typedef obj_map<expr,quantifier*> root_clause_map; //for any clause instance it gives us the clause from the original problem

        theory_instgen_impl& m_parent;
        expr_ref_vector      m_vars;
        var_subst            m_subst;
        occurs               m_occurs;
        grounder             m_grounder;
        /**
           For each clause which is a result of instantiation contains the 
           original problem clause from which it derives.
        */
        root_clause_map      m_root_clause_map;

        
        /**
           For each SMT literal contains a vector of first-order literals
           that are represented by this literal.
        */
        literal_meaning_map  m_literal_meanings;

        /**
           fo literals that have been internalized by this object.
           Invariant: any app* fol in this set has a literal l such that 
           m_literal_meanings[l].contains(fol).
           Particularly, l==get_context().get_literal(gnd_fol) where gnd_fol 
           is a grounded version of this literal
        */
        obj_hashtable<expr>  m_internalized_fo_lits;


        ast_manager& m() const;
        smt::context& get_context() const;

        class insert_occurs_trail : public trail<smt::context> {
            occurs&  m_occ;
            quantifier_ref_vector* m_qs;
            expr_ref m_lit;
        public:
            insert_occurs_trail(occurs& o, expr_ref& lit, quantifier* q): m_occ(o), m_qs(0), m_lit(lit) {
                occurs::obj_map_entry* e = m_occ.insert_if_not_there2(lit,0);
                m_qs = e->get_data().m_value;
                if (!m_qs) {
                    m_qs = alloc(quantifier_ref_vector, lit.get_manager());
                    e->get_data().m_value = m_qs;
                }
                m_qs->push_back(q);            
            }

            virtual void undo(smt::context& ctx) {
                SASSERT(m_qs && !m_qs->empty());
                SASSERT(m_qs == m_occ.find_core(m_lit)->get_data().m_value);
                m_qs->pop_back();
                if (m_qs->empty()) {
                    m_occ.remove(m_lit);
                    dealloc(m_qs);
                }
            }
        };

        class lit_meaning_trail : public trail<smt::context> {
            literal_meaning_map& m_map;
            app_ref_vector* m_apps;
            smt::literal m_smtlit;
        public:

            lit_meaning_trail(literal_meaning_map& map, ast_manager& m, smt::literal l, app* lit): 
                m_map(map), m_smtlit(l) {             
                literal_meaning_map::entry* e = map.insert_if_not_there2(l, 0);
                m_apps = e->get_data().m_value;
                if (!m_apps) {
                    m_apps = alloc(app_ref_vector, m);
                    e->get_data().m_value = m_apps;
                }
                m_apps->push_back(lit);
            }

            virtual void undo(smt::context& ctx) { 
                SASSERT(m_apps && !m_apps->empty());
                SASSERT(m_apps == m_map.find_core(m_smtlit)->get_data().m_value);
                m_apps->pop_back();
                if (m_apps->empty()) {
                    m_map.remove(m_smtlit);
                    dealloc(m_apps);
                }
            }
        };

        quantifier * get_root_clause(expr* clause) const {
            quantifier * root;
            if(!m_root_clause_map.find(clause, root)) {
                SASSERT(is_forall(clause));
                root = to_quantifier(clause);
            }
            return root;
        }

        void replace_by_root_clauses(ptr_vector<quantifier>& vect) const {
            unsigned sz = vect.size();
            for(unsigned i=0; i<sz; ++i) {
                vect[i] = get_root_clause(vect[i]);
            }
        }

        literal get_root_clause_control_literal(quantifier* root_clause) {
            get_context().internalize(root_clause, true);
            return get_context().get_literal(root_clause);
        }

        //
        // Grounding
        //

        void insert_occurs(app * lit, quantifier* clause) {
            SASSERT(clause);
            TRACE("theory_instgen", tout << PP(lit, m()) << " occurs in " << PP(clause, m()) << "\n";);
            expr_ref t(lit,m());
            get_context().push_trail(insert_occurs_trail(m_occurs, t, clause));
        }

        literal ground_fo_literal(app * lit, quantifier* q) {

            literal smt_lit;

            if (is_ground(lit)) {
                get_context().internalize(lit, true);
                smt_lit = get_context().get_literal(lit);
                get_context().mark_as_relevant(smt_lit); 
                return smt_lit;
            }
            insert_occurs(lit, q);

            app_ref grounded_lit(m());
            m_grounder(lit, grounded_lit);

            if(m_internalized_fo_lits.contains(lit)) {                
                smt_lit = get_context().get_literal(grounded_lit);
            }
            else {                
                get_context().internalize(grounded_lit, true);
                smt_lit = get_context().get_literal(grounded_lit);
                m_internalized_fo_lits.insert(lit);

                expr_ref t(lit, m());
                get_context().push_trail(obj_ref_trail<smt::context,ast_manager,expr>(t));
                get_context().push_trail(insert_obj_trail<smt::context,expr>(m_internalized_fo_lits, lit));
                get_context().push_trail(lit_meaning_trail(m_literal_meanings, m(), smt_lit, lit));
                TRACE("theory_instgen", tout << smt_lit << " "<<  PP(grounded_lit, m())  << " |-> " << PP(lit, m()) << "\n";);
            }
            get_context().mark_as_relevant(smt_lit); 
            return smt_lit;
        }

        void add_clause_to_smt(expr * clause, quantifier* root_clause, ptr_vector<quantifier> const& assumptions=ptr_vector<quantifier>());

        void get_instance_clause(instantiation_result const& ir, expr_ref& res);

        /**
        return false if nothing was done

        assumptions are instantiated clauses (to get a correct assumption for the SMT solver, we need
        to convert the vector to root clauses).
        */
        bool simplify_clause(quantifier * clause, expr_ref& result, ptr_vector<quantifier>& assumptions);

    public:

        fo_clause_internalizer(theory_instgen_impl& parent): 
            m_parent(parent),
            m_vars(m()),
            m_subst(m()),
            m_grounder(m()) {
        }

        ~fo_clause_internalizer() {
            reset_dealloc_values(m_occurs);
        }

        void get_literal_meanings(literal l, ptr_vector<app>& fo_lits) {
            app_ref_vector* lits = 0;
            m_literal_meanings.find(l, lits);
            if (lits) {
                fo_lits.append(lits->size(), lits->c_ptr());
            }
        }

        void add_initial_clause(quantifier* q) {
            add_clause_to_smt(q, 0);
        }

        quantifier_ref_vector* find_occurs(app * l) {
            quantifier_ref_vector* result = 0;
            m_occurs.find(l, result);
            return result;
        }                

        void add_new_instance(instantiation_result const& ir) {
            quantifier * root_clause = get_root_clause(ir.clause());
            expr_ref inst_clause(m());
            get_instance_clause(ir, inst_clause);

            ptr_vector<quantifier> assumptions;
            if(is_quantifier(inst_clause.get())) {
                quantifier * q_clause = to_quantifier(inst_clause.get());
                bool simplified = simplify_clause(q_clause, inst_clause, assumptions);
                SASSERT(simplified || assumptions.empty());
            }
            replace_by_root_clauses(assumptions);

            if(!m_root_clause_map.contains(inst_clause)) {
                m_root_clause_map.insert(inst_clause, root_clause);
                get_context().push_trail(insert_obj_map<smt::context,expr,quantifier*>(m_root_clause_map, inst_clause));
            }
            add_clause_to_smt(inst_clause, root_clause, assumptions);
        }
    };


    /////////////////
    // instantiator
    //

    class instantiator {
    private:
        typedef quantifier clause_type;
        typedef ptr_vector<clause_type> clause_vector;
        typedef obj_map<quantifier,matching_set*> matching_sets;

        ast_manager&            m;
        theory_instgen_impl&    m_parent;
        fo_clause_internalizer& m_internalizer;
        inst_gen_unif_index     m_unif_index;
        matching_sets           m_matching;
        unifier                 m_unifier; //used in the unify method, but we don't want to recreate over and over

        class var_rename_rewriter_cfg : public default_rewriter_cfg {
            ast_manager& m;
            u_map<unsigned> m_index_rename;
        public:
            var_rename_rewriter_cfg(ast_manager& m) : m(m) {}

            bool get_subst(expr * s, expr * & t, proof * & t_pr) {
                if (is_var(s)) {
                    unsigned idx = to_var(s)->get_idx();
                    unsigned new_idx = 0;
                    if (!m_index_rename.find(idx, new_idx)) {
                        new_idx = m_index_rename.size();
                        m_index_rename.insert(idx, new_idx);
                    }
                    t = m.mk_var(new_idx, to_var(s)->get_sort());
                    return true;
                }
                else {
                    return false;
                }
            }
        };

        static void extract_substitution(substitution& s, quantifier * q, unsigned subst_var_cnt, bool is_first_bank, expr_ref_vector& tgt) {
            // unsigned var_increment = is_first_bank ? 0 : subst_var_cnt;
            unsigned var_offset = is_first_bank ? 0 : 1;

            unsigned deltas[2] = {0, subst_var_cnt};
            ast_manager& m = s.get_manager();
            unsigned var_cnt = q->get_num_decls();
            var_rename_rewriter_cfg r_cfg(m);
            rewriter_tpl<var_rename_rewriter_cfg> rwr(m, false, r_cfg);
            for(unsigned i=0; i<var_cnt; i++) {
                sort * var_sort = q->get_decl_sort(i);
                unsigned var_idx = var_cnt-1-i;
                var_ref v(m.mk_var(var_idx, var_sort), m);
                expr_ref tmp(m), subst_result(m);
                s.apply(2, deltas, expr_offset(v.get(), var_offset), tmp); 
                rwr(tmp, subst_result);
                tgt.push_back(subst_result);
            }
        }

        
        // just to be sure there's not misunderstanding with the caller, we require the res to be empty:)
        void get_literal_occurrences(app * lit, clause_vector& res) {
            SASSERT(res.empty());
            quantifier_ref_vector * occurrences = m_internalizer.find_occurs(lit);
            if(occurrences) {
                res.append(occurrences->size(), occurrences->c_ptr());
            }
        }        

        /**
           check substitution wrt dismatching constraints of clause
           (variable offset is to deal with how variable banks are shifted on each 
           other in the substitution)
        */
        bool is_allowed_instantiation(clause_type * clause, const inst& subst) {
            matching_set * ms;
            return !m_matching.find(clause, ms) || !ms->has_instance(subst);
        }

        class new_ms : public trail<smt::context> {
            matching_sets& m_ms;
            matching_set*  m_s;
            quantifier*    m_q;
        public:
            new_ms(matching_sets& m, matching_set* s, quantifier* q): m_ms(m), m_s(s), m_q(q) {}
            virtual void undo(smt::context& ctx) { dealloc(m_s); m_ms.remove(m_q); }
        };

        // add instantiating substitution among the dismatching constraints
        void record_instantiation(instantiation_result const& inst) {
            quantifier * cl = inst.clause();
            matching_set * ms;
            if(!m_matching.find(cl, ms)) {
                ms = alloc(matching_set, m);
                m_matching.insert(cl, ms);
                get_context().push_trail(new_ms(m_matching, ms, cl));
            }
            ms->insert(inst.subst());
            get_context().push_trail(matching_set::insert_inst(*ms));
        }

        void get_result_from_subst(clause_type * clause, const inst& subst, instantiation_result& res) {
            res.init(clause, subst);
            record_instantiation(res);
        }

        void display_vector(expr_ref_vector const& v, std::ostream& out) {
            for (unsigned i = 0; i < v.size(); ++i) {
                out << PP(v[i], m) << " ";
            }
            out << "\n";
        }


        void add_lit(literal lit) {
            ptr_vector<app> fo_lits;
            m_internalizer.get_literal_meanings(lit, fo_lits);
            expr_ref e(m);
            get_context().literal2expr(lit, e);
            if (is_ground(e.get())) {
                fo_lits.push_back(to_app(e));
            }
            for (unsigned i = 0; i < fo_lits.size(); ++i) {
                app * fol = fo_lits[i];
                m_unif_index.insert_literal(fol);
            }
        }

        void mk_folit_neg(app * lit, app_ref& res) {
            expr * arg;
            if(m.is_not(lit, arg)) {
                SASSERT(is_app(arg));
                res = to_app(arg);
            }
            else {
                res = m.mk_not(lit);
            }
        }

        ast_manager& get_manager() const;
        context& get_context() const;

    public:
        instantiator(fo_clause_internalizer& internalizer, theory_instgen_impl& parent, ast_manager& m) : 
            m(m), 
            m_parent(parent),
            m_internalizer(internalizer),
            m_unif_index(m),
            m_unifier(m) {}
        
        ~instantiator() {
            reset_dealloc_values(m_matching);
        }

        bool unif_is_empty() const {
            return m_unif_index.empty();
        }

        void display(std::ostream& out) {
            m_unif_index.display(out);
        }

        void add_true_lit(literal lit) { 
            add_lit(lit); 
        }

        void push() { 
            m_unif_index.push(); 
        }

        void pop() { 
            m_unif_index.pop(); 
        }

        void reserve_num_vars(unsigned num_vars) {
            m_unif_index.reserve_num_vars(num_vars);
        }

        bool instantiate_clauses(
            app * lit1, clause_type * clause1, 
            app * lit2, clause_type * clause2, 
            instantiation_result_vector& result);

        bool instantiate_clause(
            app * lit1, clause_type * clause1, app * lit2, 
            instantiation_result_vector& result);

        void do_instantiating(literal lit, instantiation_result_vector& res) {
            ptr_vector<app> folits;
            clause_vector   folit_clauses; // clauses in which the first-order literal appears
            app_ref_vector  unifs(m);      // unifying complementary literals
            clause_vector   comp_clauses;  // clauses in which the unifying complementary literal appears

            m_internalizer.get_literal_meanings(lit, folits);

            while(!folits.empty()) {
                app * folit = folits.back();
                
                folits.pop_back();
                folit_clauses.reset();
                get_literal_occurrences(folit, folit_clauses);
                SASSERT(!folit_clauses.empty()); //if we have a literal it should be in some clause (or not?)

                SASSERT(folit->get_ref_count() > 0);
                app_ref complementary(m);
                mk_folit_neg(folit, complementary);
                m_unif_index.get_unifications(complementary, unifs);

                while(!unifs.empty()) {
                    app * comp_lit = unifs.back();
                    unifs.pop_back();
                    SASSERT(comp_lit->get_ref_count() > 0);
                    comp_clauses.reset();
                    get_literal_occurrences(comp_lit, comp_clauses);
                    TRACE("theory_instgen", tout << "Literal " << lit << " meaning: " << PP(folit, m) << "\n";
                                            tout << "Unifies with: " << PP(comp_lit, m) << "\n";);
                    //
                    //if a literal is in the unification index (i.e. was assigned true sometime before),
                    //it should be in some clause or it is a ground literal.

                    //iterate through all clauses that contain the query literal
                    //
                    clause_vector::const_iterator fc_end = folit_clauses.end();
                    for(clause_vector::const_iterator fc_it = folit_clauses.begin(); fc_it!=fc_end; ++fc_it) {

                        //iterate through all clauses that contain the complementary unifying literal
                        clause_vector::const_iterator end = comp_clauses.end();
                        for(clause_vector::const_iterator it = comp_clauses.begin(); it!=end; ++it) {

                            instantiate_clauses(folit, *fc_it, comp_lit, *it, res);
                        }
                        if (comp_clauses.empty()) {
                            instantiate_clause(folit, *fc_it, comp_lit, res);
                        }
                    }
                }
                complementary.reset();
            }
        }
    };


    ///////////////////////////
    // theory_instgen_impl
    //

    class theory_instgen_impl : public theory_instgen {

        friend class instantiator;
        friend class fo_clause_internalizer;

        struct stats {
            unsigned m_num_axioms;
            unsigned m_num_subsumptions;
            unsigned m_num_pruned;
            stats() { memset(this, 0, sizeof(*this)); }            
        };

        ast_manager&           m_manager;
        front_end_params&      m_params;
        fo_clause_internalizer m_internalizer;
        instantiator           m_instantiator;
        clause_subsumption     m_subsumer;
        stats                 m_stats;

        final_check_status instantiate_all_possible() {
            // traverse instantiation queue and create initial instances.

            ast_manager& m = get_manager();
            context& ctx   = get_context();
            instantiation_result_vector generated_clauses;
            unsigned bv_cnt = ctx.get_num_bool_vars();

            m_instantiator.push();

            TRACE("theory_instgen",
                tout << "Literals:\n";
                for (unsigned v = 0; v < bv_cnt; ++v) {
                    if (l_undef == ctx.get_assignment(v)) continue;
                    literal lit(v, ctx.get_assignment(v) == l_false);
                    expr_ref e(m); 
                    ctx.literal2expr(lit, e); 
                    tout << PP(e.get(),m) << "\n";
                }
            );

            SASSERT(m_instantiator.unif_is_empty());

            for(unsigned bvi=0; bvi < bv_cnt; ++bvi) {
                lbool asgn_val = ctx.get_assignment(bvi);
                if(asgn_val==l_undef) {
                    continue;
                }
                literal lit(bvi, asgn_val==l_false);
                m_instantiator.add_true_lit(lit);
                m_instantiator.do_instantiating(lit, generated_clauses);                                
            }

            bool change = !generated_clauses.empty();

            while(!generated_clauses.empty()) {
                m_internalizer.add_new_instance(generated_clauses.back());
                generated_clauses.pop_back();
            }

            m_instantiator.pop();

            return change?FC_CONTINUE:FC_DONE;
        }


    public:
        theory_instgen_impl(ast_manager& m, front_end_params& p):            
            theory_instgen(m.get_family_id("inst_gen")),
            m_manager(m),
            m_params(p),
            m_internalizer(*this),
            m_instantiator(m_internalizer, *this, m),
            m_subsumer(m, p)
        {}

        ast_manager& m() { return m_manager; }

        virtual void internalize_quantifier(quantifier* q) {
            TRACE("theory_instgen", tout << PP(q, m()) << "\n";);
            context& ctx = get_context();
            if (!ctx.b_internalized(q)) {
                bool_var v = ctx.mk_bool_var(q);
                ctx.set_var_theory(v, get_id());      
                m_instantiator.reserve_num_vars(q->get_num_decls());
            }
        }

        virtual bool internalize_atom(app * atom, bool gate_ctx) {      
            UNREACHABLE();
            return false;
        }

        virtual bool internalize_term(app * term) {
            UNREACHABLE();
            return false;
        }

        virtual void new_eq_eh(theory_var v1, theory_var v2) {}

        virtual void new_diseq_eh(theory_var v1, theory_var v2) {}

        virtual theory * mk_fresh(context * new_ctx) {
            return alloc(theory_instgen_impl, get_manager(), m_params);
        }

        virtual void assign_eh(bool_var v, bool is_true) {
            context& ctx = get_context();
            expr* e = ctx.bool_var2expr(v);
            if (is_quantifier(e)) {
                if (is_true) {
                    m_internalizer.add_initial_clause(to_quantifier(e));
                }
                else {
                    // TBD: handle existential force later.
                }
            }
        }

        virtual final_check_status final_check_eh() {
            TRACE("theory_instgen", tout << "Final check\n";);
            return instantiate_all_possible();
        }

        virtual void init_model(smt::model_generator & m) { }
        
        virtual smt::model_value_proc * mk_value(smt::enode * n, smt::model_generator & m) {
            UNREACHABLE();
            return 0;
        }
        
        virtual void relevant_eh(app * n) { }

        virtual void push_scope_eh() {
            m_subsumer.push();
        }

        virtual void pop_scope_eh(unsigned num_scopes) {
            m_subsumer.pop(num_scopes);
        }

        virtual void collect_statistics(::statistics & st) const {
            st.update("inst axiom", m_stats.m_num_axioms);
            st.update("inst subsump", m_stats.m_num_subsumptions);
        }

        void inc_subsumptions() {
            ++m_stats.m_num_subsumptions;
        }

        void inc_axioms() {
            ++m_stats.m_num_axioms;
        }

        void inc_pruned() {
            ++m_stats.m_num_pruned;
        }

    };

    theory_instgen* mk_theory_instgen(ast_manager& m, front_end_params& p) { 
        return alloc(theory_instgen_impl, m, p); 
    }

    ast_manager& instantiator::get_manager() const {
        return m_parent.m();
    }

    smt::context& instantiator::get_context() const {
        return m_parent.get_context();
    }

    bool instantiator::instantiate_clauses(
        app * lit1, clause_type * clause1, 
        app * lit2, clause_type * clause2, 
        instantiation_result_vector& result) {
        TRACE("theory_instgen", tout << PP(lit1, m) << " " << PP(clause1, m) << "\n";
              tout << PP(lit2, m) << " " << PP(clause2, m) << "\n";);
        substitution subst(m);
        unsigned var_cnt = std::max(clause1->get_num_decls(), clause2->get_num_decls());
        subst.reserve(2, var_cnt);
        //don't trust there offset values too much, it's just what i expect the substitution does:)
        app_ref complementary(m);
        mk_folit_neg(lit1, complementary);
        TRUSTME(m_unifier(complementary, lit2, subst));
        
        inst subst1(m);
        extract_substitution(subst, clause1, var_cnt, true, subst1);
        inst subst2(m);
        extract_substitution(subst, clause2, var_cnt, false, subst2);
        
        bool s1_identity = matching_set::is_identity(subst1);
        bool s2_identity = matching_set::is_identity(subst2);
        
        if((!s1_identity && !is_allowed_instantiation(clause1, subst1)) || 
           (!s2_identity && !is_allowed_instantiation(clause2, subst2))) {
            TRACE("theory_instgen", 
                  tout << "Pruned instantiation\n";
                  tout << PP(clause1, m) << "\n";
                  display_vector(subst1, tout);
                  tout << PP(clause2, m) << "\n";
                  display_vector(subst2, tout);
                  );
            m_parent.inc_pruned();
            return false;
        }            
        
        //
        // both substitutions cannot be identity as then the two complementary
        // literals would correspond to the same SAT solver variable
        //
        SASSERT(!s1_identity || !s2_identity);
        
        if(!s1_identity) {
            instantiation_result res1(m);
            get_result_from_subst(clause1, subst1, res1);
            result.push_back(res1);
        }
        
        if(!s2_identity) {
            instantiation_result res2(m);
            get_result_from_subst(clause2, subst2, res2);
            result.push_back(res2);
        }
        return true;
    }

    // literal lit2 is ground. It is not associated with a clause.
    // literal lit1 is associatd with a non-ground clause.
    bool instantiator::instantiate_clause(
        app * lit1, clause_type * clause1, app * lit2, 
        instantiation_result_vector& result) {
        TRACE("theory_instgen", tout << PP(lit1, m) << " " << PP(clause1, m) << "\n";
              tout << PP(lit2, m) << "\n";);
        if (!is_ground(lit2)) {
            // TBD: remove. Debug code.
            std::cout << PP(lit1, m) << " " << PP(clause1, m) << "\n";
            std::cout << PP(lit2, m) << "\n";
            m_unif_index.display(std::cout);
        }
        SASSERT(is_ground(lit2));
        substitution subst(m);
        unsigned var_cnt = clause1->get_num_decls();
        subst.reserve(2, var_cnt);            
        app_ref complementary(m);
        mk_folit_neg(lit1, complementary);
        
        TRUSTME(m_unifier(complementary, lit2, subst));
        
        inst subst1(m);            
        extract_substitution(subst, clause1, var_cnt, true, subst1);
        
        if(matching_set::is_identity(subst1) ||
           !is_allowed_instantiation(clause1, subst1)) { 
            TRACE("theory_instgen", 
                  tout << "Pruned instantiation\n";
                  tout << PP(clause1, m) << "\n";
                  display_vector(subst1, tout);
                  );
            m_parent.inc_pruned();
            return false;
        }            
        
        instantiation_result res1(m);
        get_result_from_subst(clause1, subst1, res1);
        result.push_back(res1);
        return true;
    }


    //--------------------------
    //
    // fo_clause_internalizer
    //
    //--------------------------

    smt::context& fo_clause_internalizer::get_context() const {
        return m_parent.get_context();
    }

    ast_manager& fo_clause_internalizer::m() const {
        return m_parent.m();
    }

    bool fo_clause_internalizer::simplify_clause(quantifier * clause, expr_ref& result, ptr_vector<quantifier>& assumptions) {
        m_parent.m_subsumer.simplify(clause, result, assumptions);
        bool change = clause!=result.get();
        if (change) {
            m_parent.inc_subsumptions(); 
        }
        return change;
    }

    void fo_clause_internalizer::get_instance_clause(instantiation_result const& ir, expr_ref& res) {
        expr * orig_cl = ir.clause()->get_expr();
        SASSERT(is_app(orig_cl));

        expr_ref res_inner(m()); //the clause after substitution, we might still need to quantify it
        m_subst(orig_cl, ir.subst().size(), ir.subst().c_ptr(), res_inner);
        SASSERT(is_app(res_inner.get()));

        if(is_ground(res_inner.get())) {
            res = res_inner;
            return; //we made it ground!
        }

        ptr_vector<sort> free_var_sorts;
        svector<symbol> quant_names;
        get_free_vars(res_inner.get(), free_var_sorts);
        unsigned free_var_cnt = free_var_sorts.size();
        for(unsigned i=0; i<free_var_cnt; i++) {
            if(!free_var_sorts[i]) {
                free_var_sorts[i] = m().mk_bool_sort(); //get a dummy variable
            }
            quant_names.push_back(symbol(free_var_cnt-i-1));
        }
        free_var_sorts.reverse();

        quantifier_ref q_with_unused(m().mk_quantifier(true, free_var_cnt, free_var_sorts.c_ptr(), quant_names.c_ptr(), res_inner.get()), m());
        elim_unused_vars(m(), q_with_unused, res);
    }

    /**
       Clause can be either ground (app) or non-ground (quantifier). Root clause 
       should be the original input clause from which the current clause was 
       instantiated, or zero if this clause is initial
    */
    void fo_clause_internalizer::add_clause_to_smt(expr * clause, quantifier* root_clause, ptr_vector<quantifier> const& assumptions) {
        SASSERT(!root_clause || root_clause->is_forall());
        SASSERT(is_quantifier(clause) || root_clause);
        context& ctx = get_context();
        buffer<literal> lits;
        ptr_buffer<expr> todo;

        bool is_q_clause = is_quantifier(clause);
        quantifier * q_clause = is_q_clause ? to_quantifier(clause) : 0;
        if (!root_clause) root_clause = q_clause;

        lits.push_back(~get_root_clause_control_literal(root_clause));

        for(unsigned i=0; i<assumptions.size(); ++i) {
            lits.push_back(~get_root_clause_control_literal(assumptions[i]));
        }

        todo.push_back(is_q_clause?(q_clause->get_expr()):clause);

        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (m().is_or(e)) {
                todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else if (is_app(e)) {
                lits.push_back(ground_fo_literal(to_app(e), q_clause));
            }
            else {
                SASSERT(is_var(e) || is_quantifier(e));
                UNREACHABLE(); 
                //by skipping part of the disjunction we may get unsound
            }
        }
        TRACE("theory_instgen",
              tout << "Axiom: \n";
              for (unsigned i = 0; i < lits.size(); ++i) {
                  expr_ref e(m());
                  get_context().literal2expr(lits[i], e);
                  tout << PP(e.get(), m()) << "\n";
              }
              );
        m_parent.inc_axioms();
        ctx.mk_th_axiom(m_parent.get_id(), lits.size(), lits.c_ptr());
    }


};
