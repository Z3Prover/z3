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

        /**
           \brief Apply (interpreted) sort constraints on the given enode.
        */
        virtual void apply_sort_cnstr(enode * n, sort * s) {}

    };

    class th_decompile {
    public:
        virtual ~th_decompile() {}

        virtual bool to_formulas(std::function<expr_ref(sat::literal)>& lit2expr, expr_ref_vector& fmls) = 0;
    };

    class th_model_builder {
    public:

        virtual ~th_model_builder() {}

        /**
           \brief compute the value for enode \c n and store the value in \c values 
           for the root of the class of \c n.
         */
        virtual void add_value(euf::enode* n, expr_ref_vector& values) {}

        /**
           \brief compute dependencies for node n
         */
        virtual void add_dep(euf::enode* n, top_sort<euf::enode>& dep) {}

        /**
           \brief should function be included in model.
        */
        virtual bool include_func_interp(func_decl* f) const { return false; }
    };

    class th_solver : public sat::extension, public th_model_builder, public th_decompile, public th_internalizer {
    protected:
        ast_manager &       m;
        theory_id           m_id;
    public:
        th_solver(ast_manager& m, euf::theory_id id): m(m), m_id(id) {}

        unsigned get_id() const override { return m_id; }

        virtual th_solver* fresh(sat::solver* s, euf::solver& ctx) = 0;  

        virtual void new_eq_eh(euf::th_eq const& eq) {}

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

        smt_params const& get_config() const;
        sat::literal get_literal(expr* e) const;
        region& get_region();
    public:
        th_euf_solver(euf::solver& ctx, euf::theory_id id);
        virtual ~th_euf_solver() {}
        virtual theory_var mk_var(enode * n);
        unsigned get_num_vars() const { return m_var2enode.size();}
        enode* get_enode(expr* e) const; 
        enode* get_enode(theory_var v) const { return m_var2enode[v]; }
        expr* get_expr(theory_var v) const { return get_enode(v)->get_owner(); }
        expr_ref get_expr(sat::literal lit) const { expr* e = get_expr(lit.var()); return lit.sign() ? expr_ref(m.mk_not(e), m) : expr_ref(e, m); }
        theory_var get_th_var(enode* n) const { return n->get_th_var(get_id()); }
        theory_var get_th_var(expr* e) const;
        bool is_attached_to_var(enode* n) const;
        void push() override;
        void pop(unsigned n) override;
    };


}
