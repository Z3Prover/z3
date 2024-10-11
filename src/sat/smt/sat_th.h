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

        bool visit_rec(ast_manager& m, expr* e, bool sign, bool root);

        virtual bool visit(expr* e) { return false; }
        virtual bool visited(expr* e) { return false; }
        virtual bool post_visit(expr* e, bool sign, bool root) { return false; }

    public:
        virtual ~th_internalizer() = default;

        virtual sat::literal internalize(expr* e, bool sign, bool root) = 0;

        virtual void internalize(expr* e) = 0;


        /**
           \brief Apply (interpreted) sort constraints on the given enode.
        */
        virtual void apply_sort_cnstr(enode* n, sort* s) {}

        /**
           \brief Record that an equality has been internalized.
         */
        virtual void eq_internalized(enode* n) {}

    };


    class th_decompile {
    public:
        virtual ~th_decompile() = default;

        virtual bool to_formulas(std::function<expr_ref(sat::literal)>& lit2expr, expr_ref_vector& fmls) { return false; }
    };

    class th_model_builder {
    public:

        virtual ~th_model_builder() = default;

        /**
           \brief compute the value for enode \c n and store the value in \c values
           for the root of the class of \c n.
         */
        virtual void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {}

        /**
           \brief compute dependencies for node n
         */
        virtual bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) { dep.insert(n, nullptr); return true; }

        /**
           \brief should function be included in model.
        */
        virtual bool include_func_interp(func_decl* f) const { return false; }

        /**
          \brief initialize model building
        */
        virtual void init_model() {}

        /**
          \brief conclude model building
        */
        virtual void finalize_model(model& mdl) {}

        /**
        * \brief does solver have an unhandled function.
        */
        virtual bool has_unhandled() const { return false; }
    };

    class th_solver : public sat::extension, public th_model_builder, public th_decompile, public th_internalizer {
    protected:
        ast_manager& m;
    public:
        th_solver(ast_manager& m, symbol const& name, euf::theory_id id) : extension(name, id), m(m) {}

        virtual th_solver* clone(euf::solver& ctx) = 0;

        virtual void new_eq_eh(euf::th_eq const& eq) {}

        virtual bool use_diseqs() const { return false; }

        virtual void new_diseq_eh(euf::th_eq const& eq) {}

        virtual bool enable_ackerman_axioms(euf::enode* n) const { return true; }

        virtual bool is_fixed(euf::theory_var v, expr_ref& val, sat::literal_vector& lits) { return false; }

        virtual void relevant_eh(euf::enode* n) {}

        /**
           \brief Parametric theories (e.g. Arrays) should implement this method.
        */
        virtual bool is_shared(theory_var v) const { return false; }


        /**
           \brief Determine if argument n of parent p is a beta redex position
         */

        virtual bool is_beta_redex(euf::enode* p, euf::enode* n) const { return false; }

        sat::status status() const { return sat::status::th(false, get_id()); }

        virtual euf::enode_pair get_justification_eq(size_t j);


        virtual void set_bounds_begin() {}

        virtual void set_bounds_end(unsigned num_literals) {}

        virtual void set_bounds(enode* n) {}

        virtual void finalize() {}

        virtual void initialize_value(expr* v, expr* value) { IF_VERBOSE(5, verbose_stream() << "value initialzation is not supported for theory\n"); }

    };

    class th_proof_hint : public sat::proof_hint {
    public:
        virtual expr* get_hint(euf::solver& s) const = 0;
    };

    class th_euf_solver : public th_solver {
    protected:
        solver& ctx;
        euf::enode_vector   m_var2enode;
        unsigned_vector     m_var2enode_lim;
        unsigned            m_num_scopes{ 0 };

        smt_params const& get_config() const;
        sat::literal expr2literal(expr* e) const;
        region& get_region();

        bool add_unit(sat::literal lit, th_proof_hint const* ps = nullptr);
        bool add_units(sat::literal_vector const& lits);
        bool add_clause(sat::literal lit, th_proof_hint const* ps = nullptr) { return add_unit(lit, ps); }
        bool add_clause(sat::literal a, sat::literal b, th_proof_hint const* ps = nullptr);
        bool add_clause(sat::literal a, sat::literal b, sat::literal c, th_proof_hint const* ps = nullptr);
        bool add_clause(sat::literal a, sat::literal b, sat::literal c, sat::literal d, th_proof_hint const* ps = nullptr);
        bool add_clause(sat::literal_vector const& lits, th_proof_hint const* ps = nullptr) { return add_clause(lits.size(), lits.data(), ps); }
        bool add_clause(unsigned n, sat::literal* lits, th_proof_hint const* ps, bool is_redundant = false);
        void add_equiv(sat::literal a, sat::literal b);
        void add_equiv_and(sat::literal a, sat::literal_vector const& bs);
        bool add_redundant(sat::literal_vector const& lits, th_proof_hint const* ps) { return add_clause(lits.size(), lits.data(), ps, true); }
        bool add_redundant(unsigned n, sat::literal* lits, th_proof_hint const* ps);


        bool is_true(sat::literal lit);
        bool is_true(sat::literal a, sat::literal b) { return is_true(a) || is_true(b); }
        bool is_true(sat::literal a, sat::literal b, sat::literal c) { return is_true(a) || is_true(b, c); }
        bool is_true(sat::literal a, sat::literal b, sat::literal c, sat::literal d) { return is_true(a) || is_true(b, c, c); }

        sat::literal eq_internalize(expr* a, expr* b);
        sat::literal eq_internalize(enode* a, enode* b) { return eq_internalize(a->get_expr(), b->get_expr()); }

        euf::enode* mk_enode(expr* e, bool suppress_args = false);
        expr_ref mk_eq(expr* e1, expr* e2);
        expr_ref mk_var_eq(theory_var v1, theory_var v2) { return mk_eq(var2expr(v1), var2expr(v2)); }

        void rewrite(expr_ref& a);

        virtual void push_core();
        virtual void pop_core(unsigned n);
        void force_push() {
            CTRACE("euf_verbose", m_num_scopes > 0, tout << "push-core " << m_num_scopes << "\n";);
            for (; m_num_scopes > 0; --m_num_scopes) push_core();
        }

        friend class th_explain;

    public:
        th_euf_solver(euf::solver& ctx, symbol const& name, euf::theory_id id);
        virtual theory_var mk_var(enode* n);
        unsigned get_num_vars() const { return m_var2enode.size(); }
        euf::enode* e_internalize(expr* e); 
        enode* expr2enode(expr* e) const;
        enode* var2enode(theory_var v) const { return m_var2enode[v]; }
        expr* var2expr(theory_var v) const { return var2enode(v)->get_expr(); }
        bool is_representative(theory_var v) const { return v == get_representative(v); }
        expr* bool_var2expr(sat::bool_var v) const;
        expr_ref literal2expr(sat::literal lit) const;
        enode* bool_var2enode(sat::bool_var v) const { expr* e = bool_var2expr(v); return e ? expr2enode(e) : nullptr; }
        sat::literal mk_literal(expr* e) const;
        theory_var get_th_var(enode* n) const { return n->get_th_var(get_id()); }
        theory_var get_th_var(expr* e) const;
        theory_var get_representative(theory_var v) const;
        trail_stack& get_trail_stack();
        bool is_attached_to_var(enode* n) const;
        bool is_root(theory_var v) const { return var2enode(v)->is_root(); }
        void push() override { m_num_scopes++; }
        void pop(unsigned n) override;


        unsigned random();
    };

    /**
    * General purpose, eager explanation object. Explanations are conjunctions of literals and equalities.
    * Used literals and equalities are stored in the object and retrieved on demand for conflict resolution
    * It is "eager" in the sense that relevant literals are accumulated when the explanation is created.
    * This is not a real problem for conflicts, but a theory has an option to implement custom lazy explanations
    * that retrieve literals on demand.
    */
    class th_explain {
        sat::literal     m_consequent = sat::null_literal; // literal consequent for propagations
        enode_pair       m_eq = enode_pair();              // equality consequent for propagations
        th_proof_hint const* m_proof_hint;
        unsigned       m_num_literals;
        unsigned       m_num_eqs;        
        sat::literal*  m_literals;
        enode_pair*    m_eqs;
        static size_t get_obj_size(unsigned num_lits, unsigned num_eqs);
        th_explain(unsigned n_lits, sat::literal const* lits, unsigned n_eqs, enode_pair const* eqs, sat::literal c, enode_pair const& eq, th_proof_hint const* ph = nullptr);
        static th_explain* mk(th_euf_solver& th, unsigned n_lits, sat::literal const* lits, unsigned n_eqs, enode_pair const* eqs, sat::literal c, enode* x, enode* y, th_proof_hint const* ph = nullptr);

    public:
        static th_explain* conflict(th_euf_solver& th, sat::literal_vector const& lits, enode_pair_vector const& eqs, th_proof_hint const* ph = nullptr);
        static th_explain* conflict(th_euf_solver& th, sat::literal_vector const& lits, th_proof_hint const* ph = nullptr) { return conflict(th, lits.size(), lits.data(), 0, nullptr, ph); }
        static th_explain* conflict(th_euf_solver& th, unsigned n_lits, sat::literal const* lits, unsigned n_eqs, enode_pair const* eqs, th_proof_hint const* ph = nullptr);
        static th_explain* conflict(th_euf_solver& th, enode_pair_vector const& eqs, th_proof_hint const* ph = nullptr);
        static th_explain* conflict(th_euf_solver& th, sat::literal lit, th_proof_hint const* ph = nullptr);
        static th_explain* conflict(th_euf_solver& th, sat::literal lit, euf::enode* x, euf::enode* y, th_proof_hint const* ph = nullptr);
        static th_explain* conflict(th_euf_solver& th, euf::enode* x, euf::enode* y, th_proof_hint const* ph = nullptr);
        static th_explain* propagate(th_euf_solver& th, sat::literal lit, euf::enode* x, euf::enode* y, th_proof_hint const* ph = nullptr);
        static th_explain* propagate(th_euf_solver& th, enode_pair_vector const& eqs, euf::enode* x, euf::enode* y, th_proof_hint const* ph = nullptr);
        static th_explain* propagate(th_euf_solver& th, sat::literal_vector const& lits, enode_pair_vector const& eqs, sat::literal consequent, th_proof_hint const* ph = nullptr);
        static th_explain* propagate(th_euf_solver& th, sat::literal_vector const& lits, enode_pair_vector const& eqs, euf::enode* x, euf::enode* y, th_proof_hint const* ph = nullptr);

        sat::ext_constraint_idx to_index() const {
            return sat::constraint_base::mem2base(this);
        }
        static th_explain& from_index(size_t idx) {
            return *reinterpret_cast<th_explain*>(sat::constraint_base::from_index(idx)->mem());
        }

        sat::extension& ext() const {
            return *sat::constraint_base::to_extension(to_index());
        }

        std::ostream& display(std::ostream& out) const;

        class lits {
            th_explain const& th;
        public:
            lits(th_explain const& th) : th(th) {}
            sat::literal const* begin() const { return th.m_literals; }
            sat::literal const* end() const { return th.m_literals + th.m_num_literals; }
        };

        class eqs {
            th_explain const& th;
        public:
            eqs(th_explain const& th) : th(th) {}
            enode_pair const* begin() const { return th.m_eqs; }
            enode_pair const* end() const { return th.m_eqs + th.m_num_eqs; }
        };

        sat::literal lit_consequent() const { return m_consequent; }

        enode_pair eq_consequent() const { return m_eq; }

        th_proof_hint const* get_pragma() const { return m_proof_hint; } 

    };


}
