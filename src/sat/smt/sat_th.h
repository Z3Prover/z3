/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_th.h

Abstract:

    Theory plugins

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once

#include "util/top_sort.h"
#include "sat/smt/sat_smt.h"
#include "ast/euf/euf_egraph.h"
#include "model/model.h"
#include "smt/params/smt_params.h"

namespace euf {

    class solver;
    
    class th_internalizer {
    protected:
        euf::enode_vector     m_args;
        svector<sat::eframe>  m_stack;
        bool                  m_is_redundant { false };

        bool visit_rec(ast_manager& m, expr* e, bool sign, bool root, bool redundant);

        virtual bool visit(expr* e) { return false; }
        virtual bool visited(expr* e) { return false; }
        virtual bool post_visit(expr* e, bool sign, bool root) { return false; }

    public:
        virtual ~th_internalizer() {}

        virtual sat::literal internalize(expr* e, bool sign, bool root, bool redundant) = 0;

        virtual void internalize(expr* e, bool redundant) = 0;

        sat::literal b_internalize(expr* e) { return internalize(e, false, false, m_is_redundant); }

        /**
           \brief Apply (interpreted) sort constraints on the given enode.
        */
        virtual void apply_sort_cnstr(enode * n, sort * s) {}

        /**
           \record that an equality has been internalized.
         */
        virtual void eq_internalized(enode* n) {}

    };

    class th_decompile {
    public:
        virtual ~th_decompile() {}

        virtual bool to_formulas(std::function<expr_ref(sat::literal)>& lit2expr, expr_ref_vector& fmls) { return false; }
    };

    class th_model_builder {
    public:

        virtual ~th_model_builder() {}

        /**
           \brief compute the value for enode \c n and store the value in \c values 
           for the root of the class of \c n.
         */
        virtual void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {}

        /**
           \brief compute dependencies for node n
         */
        virtual void add_dep(euf::enode* n, top_sort<euf::enode>& dep) { dep.insert(n, nullptr);  }

        /**
           \brief should function be included in model.
        */
        virtual bool include_func_interp(func_decl* f) const { return false; }
    };

    class th_solver : public sat::extension, public th_model_builder, public th_decompile, public th_internalizer {
    protected:
        ast_manager &       m;
    public:
        th_solver(ast_manager& m, euf::theory_id id): extension(id), m(m) {}

        virtual th_solver* fresh(sat::solver* s, euf::solver& ctx) = 0;  

        virtual void new_eq_eh(euf::th_eq const& eq) {}

        virtual bool use_diseqs() const { return false; }

        virtual void new_diseq_eh(euf::th_eq const& eq) {}

        /**
           \brief Parametric theories (e.g. Arrays) should implement this method.
        */
        virtual bool is_shared(theory_var v) const { return false; }

    };

    class th_euf_solver : public th_solver {
    protected:
        solver &            ctx;
        euf::enode_vector   m_var2enode;
        unsigned_vector     m_var2enode_lim;
        unsigned            m_num_scopes{ 0 };

        smt_params const& get_config() const;
        sat::literal expr2literal(expr* e) const;
        region& get_region();
        

        bool add_unit(sat::literal lit);
        bool add_clause(sat::literal lit) { return add_unit(lit); }
        bool add_clause(sat::literal a, sat::literal b);
        bool add_clause(sat::literal a, sat::literal b, sat::literal c);
        bool add_clause(sat::literal a, sat::literal b, sat::literal c, sat::literal d);

        bool is_true(sat::literal lit);
        bool is_true(sat::literal a, sat::literal b) { return is_true(a) || is_true(b); }
        bool is_true(sat::literal a, sat::literal b, sat::literal c) { return is_true(a) || is_true(b, c); }
        bool is_true(sat::literal a, sat::literal b, sat::literal c, sat::literal d) { return is_true(a) || is_true(b, c, c); }

        euf::enode* e_internalize(expr* e) { internalize(e, m_is_redundant); return expr2enode(e); }
        euf::enode* mk_enode(expr* e, bool suppress_args);
        expr_ref mk_eq(expr* e1, expr* e2);
        expr_ref mk_var_eq(theory_var v1, theory_var v2) { return mk_eq(var2expr(v1), var2expr(v2)); }

        void rewrite(expr_ref& a);

        virtual void push_core();
        virtual void pop_core(unsigned n);
        void force_push() { 
            CTRACE("euf", m_num_scopes > 0, tout << "push-core " << m_num_scopes << "\n";);
            for (; m_num_scopes > 0; --m_num_scopes) push_core(); 
        }

    public:
        th_euf_solver(euf::solver& ctx, euf::theory_id id);
        virtual ~th_euf_solver() {}
        virtual theory_var mk_var(enode * n);
        unsigned get_num_vars() const { return m_var2enode.size();}
        enode* expr2enode(expr* e) const; 
        enode* var2enode(theory_var v) const { return m_var2enode[v]; }
        expr* var2expr(theory_var v) const { return var2enode(v)->get_expr(); }
        expr* bool_var2expr(sat::bool_var v) const;
        enode* bool_var2enode(sat::bool_var v) const { expr* e = bool_var2expr(v); return e ? expr2enode(e) : nullptr; }
        expr_ref literal2expr(sat::literal lit) const { expr* e = bool_var2expr(lit.var()); return lit.sign() ? expr_ref(m.mk_not(e), m) : expr_ref(e, m); }
        theory_var get_th_var(enode* n) const { return n->get_th_var(get_id()); }
        theory_var get_th_var(expr* e) const;
        trail_stack<euf::solver> & get_trail_stack();
        bool is_attached_to_var(enode* n) const;
        bool is_root(theory_var v) const { return var2enode(v)->is_root(); }
        void push() override { m_num_scopes++; }
        void pop(unsigned n) override;       

    };


}
