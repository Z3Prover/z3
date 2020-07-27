/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nlarith_util.h

Abstract:

    Utilities for nln-linear arithmetic quantifier elimination and
    solving.

Author:

    Nikolaj (nbjorner) 2011-05-13

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"

namespace nlarith {

    /**
        \brief A summary for branch side conditions and substitutions.

        Each branch in a split comprises of:
        - preds    - a sequence of predicates used for the branching.
        - branches - a sequence of branch side conditions
        - subst    - a sequence of substitutions that replace 'preds' by formulas 
                     not containing the eliminated variable
        - constraints - a sequence of side constraints to add to the main formula.
    */
    class branch_conditions {
        expr_ref_vector         m_branches;
        expr_ref_vector         m_preds;
        vector<expr_ref_vector> m_subst;
        expr_ref_vector         m_constraints;
        expr_ref_vector         m_defs;
        expr_ref_vector         m_a;
        expr_ref_vector         m_b;
        expr_ref_vector         m_c;

    public:
        branch_conditions(ast_manager& m) : m_branches(m), m_preds(m), m_constraints(m), m_defs(m), m_a(m), m_b(m), m_c(m) {}
        void add_pred(expr* p) { m_preds.push_back(p); }
        void add_branch(expr* branch, expr* cond, expr_ref_vector const& subst, expr* def, expr* a, expr* b, expr* c) {
            m_branches.push_back(branch);
            m_constraints.push_back(cond);
            m_subst.push_back(subst);
            m_defs.push_back(def);
            m_a.push_back(a);
            m_b.push_back(b);
            m_c.push_back(c);
        }
        expr*                          preds(unsigned i) const { return m_preds[i]; }
        expr*                          branches(unsigned i) const { return m_branches[i]; }
        expr*                          constraints(unsigned i) const { return m_constraints[i]; }
        expr*                          def(unsigned i) const { return m_defs[i]; }
        expr*                          a(unsigned i) const { return m_a[i]; }
        expr*                          b(unsigned i) const { return m_b[i]; }
        expr*                          c(unsigned i) const { return m_c[i]; }
        expr_ref_vector const&         subst(unsigned i) const { return m_subst[i]; }
        expr_ref_vector const&         branches() const { return m_branches; }
        expr_ref_vector const&         preds() const  { return m_preds; }
        vector<expr_ref_vector> const& subst() const  { return m_subst; }
        expr_ref_vector const&         constraints() const { return m_constraints; }
        void reset() { 
            m_branches.reset(); m_preds.reset(); m_subst.reset(); 
            m_constraints.reset(); m_defs.reset(); 
            m_a.reset(); m_b.reset(); m_c.reset();
        }

        unsigned size() const { return branches().size(); }
        unsigned num_preds() const { return preds().size(); }
    };

    class util {
        class imp;
        imp* m_imp;
    public:
        util(ast_manager& m);
        ~util();

        /**
           \brief Enable handling of linear variables.
        */
        void set_enable_linear(bool enable_linear);

        /**
           \brief Create branches for non-linear variable x.
        */
        bool create_branches(app* x, unsigned nl, expr* const* lits, branch_conditions& bc);
        /**
           \brief Extract non-linear variables from ground formula.
           
           \requires a ground formula.
        */
        void extract_non_linear(expr* e, ptr_vector<app>& nl_vars);

        /**
           \brief literal sets. Opaque state.
        */                       

        class literal_set;

        static void deallocate(literal_set* lits);



        /**
           \brief Sign-based branching. v2.
        */                       
        typedef obj_hashtable<app> atoms;

        class eval {
        public:
            virtual ~eval() {}
            virtual lbool operator()(app* a) = 0;
        };

        enum atom_update { INSERT, REMOVE };
        
        class branch {
        public:
            virtual ~branch() {}
            virtual app* get_constraint() = 0;
            virtual void get_updates(ptr_vector<app>& atoms, svector<atom_update>& updates) = 0;
        };

        /**
            \brief select literals that contain non-linear variables.
        */
        bool get_sign_literals(atoms const& atoms, eval& eval, literal_set*& lits);

        /**
            \brief given selected literals, generate branch conditions.
        */
        void get_sign_branches(literal_set& lits, eval& eval, ptr_vector<branch>& branches);
        
        

    };

};

