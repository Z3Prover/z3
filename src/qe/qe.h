/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe.h

Abstract:

    Quantifier-elimination procedures 

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:


--*/

#ifndef QE_H_
#define QE_H_

#include "ast/ast.h"
#include "smt/params/smt_params.h"
#include "util/statistics.h"
#include "util/lbool.h"
#include "ast/expr_functors.h"
#include "ast/rewriter/rewriter.h"
#include "model/model.h"
#include "util/params.h"

namespace qe {


    class i_nnf_atom {
    public:
        virtual void operator()(expr* e, bool pol, expr_ref& result) = 0;
    };

    typedef obj_hashtable<app> atom_set;

    class qe_solver_plugin;


    class i_solver_context {
    protected:
        class is_relevant : public i_expr_pred {
            i_solver_context& m_s;
        public:
            is_relevant(i_solver_context& s):m_s(s) {}
            bool operator()(expr* e) override;
        };
        class mk_atom_fn : public i_nnf_atom {
            i_solver_context& m_s;
        public:
            mk_atom_fn(i_solver_context& s) : m_s(s) {}
            void operator()(expr* e, bool p, expr_ref& result) override;
        };

        is_relevant                  m_is_relevant;
        mk_atom_fn                   m_mk_atom;
        ptr_vector<qe_solver_plugin> m_plugins;      // fid -> plugin

    public:
        i_solver_context():m_is_relevant(*this), m_mk_atom(*this) {}

        virtual ~i_solver_context();

        void add_plugin(qe_solver_plugin* p);

        bool has_plugin(app* x);

        qe_solver_plugin& plugin(app* x);

        qe_solver_plugin& plugin(unsigned fid) { return *m_plugins[fid]; }

        void mk_atom(expr* e, bool p, expr_ref& result);

        virtual ast_manager& get_manager() = 0;

        // set of atoms in current formula.
        virtual atom_set const& pos_atoms() const = 0;
        virtual atom_set const& neg_atoms() const = 0;        

        // Access current set of variables to solve
        virtual unsigned      get_num_vars() const = 0;
        virtual app*          get_var(unsigned idx) const = 0;
        virtual app_ref_vector const&  get_vars() const = 0;
        virtual bool          is_var(expr* e, unsigned& idx) const;
        virtual contains_app& contains(unsigned idx) = 0;

        // callback to replace variable at index 'idx' with definition 'def' and updated formula 'fml'
        virtual void          elim_var(unsigned idx, expr* fml, expr* def) = 0;        

        // callback to add new variable to branch.
        virtual void          add_var(app* x) = 0;

        // callback to add constraints in branch.
        virtual void          add_constraint(bool use_var, expr* l1 = nullptr, expr* l2 = nullptr, expr* l3 = nullptr) = 0;

        // eliminate finite domain variable 'var' from fml.
        virtual void blast_or(app* var, expr_ref& fml) = 0;

        i_expr_pred& get_is_relevant() { return m_is_relevant; }
        
        i_nnf_atom& get_mk_atom() { return m_mk_atom; }

        void collect_statistics(statistics & st) const;

    };

    class conj_enum {
        ast_manager& m;
        expr_ref_vector m_conjs;
    public:
        conj_enum(ast_manager& m, expr* e);

        class iterator {
            conj_enum* m_super;
            unsigned m_index;
        public:
            iterator(conj_enum& c, bool first) : m_super(&c), m_index(first?0:c.m_conjs.size()) {}
            expr* operator*() { return m_super->m_conjs[m_index].get(); }
            iterator& operator++() { m_index++; return *this; }
            bool operator==(iterator const& it) const { return m_index == it.m_index; }
            bool operator!=(iterator const& it) const { return m_index != it.m_index; }
        };

        void extract_equalities(expr_ref_vector& eqs);

        iterator begin() { return iterator(*this, true); }
        iterator end() { return iterator(*this, false); }
    };


    //
    // interface for plugins to eliminate quantified variables.
    // 
    class qe_solver_plugin {
    protected:
        ast_manager&      m;
        family_id         m_fid;
        i_solver_context& m_ctx;
    public:
        qe_solver_plugin(ast_manager& m, family_id fid, i_solver_context& ctx) : 
            m(m), 
            m_fid(fid),
            m_ctx(ctx)
        {}
        
        virtual ~qe_solver_plugin() {}
        
        family_id get_family_id() { return m_fid; }

        /**
           \brief Return number of case splits for variable x in fml.
        */
        virtual bool get_num_branches(contains_app& x, expr* fml, rational& num_branches) = 0;

        /**
           \brief Given a case split index 'vl' assert the constraints associated with it.
        */
        virtual void assign(contains_app& x, expr* fml, rational const& vl) = 0;


        /**
           \brief The case splits associated with 'vl' are satisfiable. 
           Apply the elimination for fml corresponding to case split.
           If def is non-null, then retrieve the realizer corresponding to the case split.
        */                     
        virtual void subst(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) = 0;


        /**
           \brief solve quantified variable.
        */
        virtual bool solve(conj_enum& conjs, expr* fml) = 0;

        /**
           \brief project variable x for fml given model.

           Assumption: model |= fml[x]

           Projection updates fml to fml', such that:

           - fml' -> fml
           - model |= fml'
           - fml' does not contain x           

           return false if the method is not implemented.
        */
        virtual bool project(contains_app& x, model_ref& model, expr_ref& fml) { return false; }

        /**
           \brief assign branching penalty to variable x for 'fml'.
        */
        virtual unsigned get_weight(contains_app& x, expr* fml) { return UINT_MAX; }

        /**
           \brief simplify formula.
        */
        virtual bool simplify(expr_ref& fml) { return false; }

        /**
           \brief Normalize literal during NNF conversion.
        */
        virtual bool mk_atom(expr* e, bool p, expr_ref& result) { return false; }

        /**
           \brief Determine whether sub-term is uninterpreted with respect to quantifier elimination.
        */
        virtual bool is_uninterpreted(app* f) { return true; }
    };

    qe_solver_plugin* mk_datatype_plugin(i_solver_context& ctx);

    qe_solver_plugin* mk_bool_plugin(i_solver_context& ctx);

    qe_solver_plugin* mk_bv_plugin(i_solver_context& ctx);

    qe_solver_plugin* mk_dl_plugin(i_solver_context& ctx);

    qe_solver_plugin* mk_array_plugin(i_solver_context& ctx);

    qe_solver_plugin* mk_arith_plugin(i_solver_context& ctx, bool produce_models, smt_params& p);

    void extract_vars(quantifier* q, expr_ref& new_body, app_ref_vector& vars);

    class def_vector {
        func_decl_ref_vector m_vars;
        expr_ref_vector      m_defs;
        def_vector& operator=(def_vector const& other);
    public:
        def_vector(ast_manager& m): m_vars(m), m_defs(m) {}
        def_vector(def_vector const& other): m_vars(other.m_vars), m_defs(other.m_defs) {}
        void push_back(func_decl* v, expr* e) {
            m_vars.push_back(v);
            m_defs.push_back(e);
        }
        void reset() { m_vars.reset(); m_defs.reset(); }
        void append(def_vector const& o) { m_vars.append(o.m_vars); m_defs.append(o.m_defs); }
        unsigned size() const { return m_defs.size(); }
        void shrink(unsigned sz) { m_vars.shrink(sz); m_defs.shrink(sz); }
        bool empty() const { return m_defs.empty(); }
        func_decl* var(unsigned i) const { return m_vars[i]; }
        expr*  def(unsigned i) const { return m_defs[i]; }
        expr_ref_vector::element_ref  def_ref(unsigned i) { return m_defs[i]; }
        void normalize();
        void project(unsigned num_vars, app* const* vars);
    };

    /**
       \brief Guarded definitions.

       A realizer to a an existential quantified formula is a disjunction
       together with a substitution from the existentially quantified variables
       to terms such that:
       1. The original formula (exists (vars) fml) is equivalent to the disjunction of guards.
       2. Each guard is equivalent to fml where 'vars' are replaced by the substitution associated
          with the guard.       
    */

    class guarded_defs {
        expr_ref_vector    m_guards;
        vector<def_vector> m_defs;
        bool inv();
    public:
        guarded_defs(ast_manager& m): m_guards(m) { SASSERT(inv()); }
        void add(expr* guard, def_vector const& defs);
        unsigned size() const { return m_guards.size(); }
        def_vector const& defs(unsigned i) const { return m_defs[i]; }
        expr* guard(unsigned i) const { return m_guards[i]; }
        std::ostream& display(std::ostream& out) const;
        void project(unsigned num_vars, app* const* vars);
    };

    class quant_elim; 

    class expr_quant_elim {
        ast_manager&            m;
        smt_params const&       m_fparams;
        params_ref              m_params;
        expr_ref_vector         m_trail;
        obj_map<expr,expr*>     m_visited;
        quant_elim*             m_qe;
        expr*                   m_assumption;
    public:
        expr_quant_elim(ast_manager& m, smt_params const& fp, params_ref const& p = params_ref());
        ~expr_quant_elim(); 

        void operator()(expr* assumption, expr* fml, expr_ref& result);

        void collect_statistics(statistics & st) const;

        void updt_params(params_ref const& p);

        void collect_param_descrs(param_descrs& r);

        /**
           \brief try to eliminate 'vars' and find first satisfying assignment.

           return l_true if satisfiable, l_false if unsatisfiable, l_undef if 
           the formula could not be satisfied modulo eliminating the quantified variables.
        */
        lbool first_elim(unsigned num_vars, app* const* vars, expr_ref& fml, def_vector& defs);

        /**
           \brief solve for (exists (var) fml).
           Return false if operation failed.
           Return true  and list of pairs (t_i, fml_i) in <terms, fmls>
                          such that fml_1 \/ ... \/ fml_n == (exists (var) fml)
                          and       fml_i => fml[t_i]
         */
        bool solve_for_var(app* var, expr* fml, guarded_defs& defs);

        bool solve_for_vars(unsigned num_vars, app* const* vars, expr* fml, guarded_defs& defs);


    private:
        void instantiate_expr(expr_ref_vector& bound, expr_ref& fml);
        void abstract_expr(unsigned sz, expr* const* bound, expr_ref& fml);
        void elim(expr_ref& result);
        void init_qe();
    };

    void hoist_exists(expr_ref& fml, app_ref_vector& vars);

    void mk_exists(unsigned num_vars, app* const* vars, expr_ref& fml);

    void get_nnf(expr_ref& fml, i_expr_pred& pred, i_nnf_atom& mk_atom, atom_set& pos, atom_set& neg); 

    class simplify_rewriter_cfg : public default_rewriter_cfg {
        class impl;
        impl* imp;
    public:
        simplify_rewriter_cfg(ast_manager& m);

        ~simplify_rewriter_cfg();
        
        bool reduce_quantifier(
            quantifier * old_q, 
            expr * new_body, 
            expr * const * new_patterns, 
            expr * const * new_no_patterns,
            expr_ref & result,
            proof_ref & result_pr);
        
        bool pre_visit(expr* e);

        void updt_params(params_ref const& p);

        void collect_statistics(statistics & st) const;
    };
    
    class simplify_rewriter_star : public rewriter_tpl<simplify_rewriter_cfg> {
        simplify_rewriter_cfg m_cfg;
    public:
        simplify_rewriter_star(ast_manager& m):
            rewriter_tpl<simplify_rewriter_cfg>(m, false, m_cfg),
            m_cfg(m) {}
         
        void updt_params(params_ref const& p) { m_cfg.updt_params(p); }

        void collect_statistics(statistics & st) const {
            m_cfg.collect_statistics(st);
        }

    };

};

#endif

