/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_special_relations.h

Abstract:

    Special Relations theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-16

Notes:

--*/

#ifndef THEORY_SPECIAL_RELATIONS_H_
#define THEORY_SPECIAL_RELATIONS_H_

#include "ast/special_relations_decl_plugin.h"
#include "smt/smt_theory.h"
#include "smt/theory_diff_logic.h"
#include "util/union_find.h"
#include "util/rational.h"

namespace smt {
    class theory_special_relations : public theory {


        struct relation;

        class atom {
            bool_var    m_bvar;
            relation&   m_relation;
            bool        m_phase;
            theory_var  m_v1;
            theory_var  m_v2;
            edge_id     m_pos;
            edge_id     m_neg;
        public:
            atom(bool_var b, relation& r, theory_var v1, theory_var v2):
                m_bvar(b),
                m_relation(r),
                m_phase(true),
                m_v1(v1),
                m_v2(v2)
            {
                r.ensure_var(v1);
                r.ensure_var(v2);
                literal_vector ls;
                ls.push_back(literal(b, false));
                m_pos = r.m_graph.add_edge(v1, v2, s_integer(0), ls);  // v1 <= v2
                ls[0] = literal(b, true);
                m_neg = r.m_graph.add_edge(v2, v1, s_integer(-1), ls); // v2 + 1 <= v1 
            }
            bool_var var() const { return m_bvar;}
            relation& get_relation() const { return m_relation; }
            bool phase() const { return m_phase; }
            void set_phase(bool b) { m_phase = b; }
            theory_var v1() const { return m_v1; }
            theory_var v2() const { return m_v2; }
            literal explanation() const { return literal(m_bvar, !m_phase); }
            bool enable() {
                edge_id edge = m_phase?m_pos:m_neg;
                return m_relation.m_graph.enable_edge(edge);
            }
        };
        typedef ptr_vector<atom> atoms;

        struct scope {
            unsigned m_asserted_atoms_lim;
            unsigned m_asserted_qhead_old;
        };

        struct int_ext : public sidl_ext {
            typedef literal_vector explanation;
        };
        struct graph : public dl_graph<int_ext> {
            bool add_strict_edge(theory_var v1, theory_var v2, literal_vector const& j) {
                // v1 + 1 <= v2
                return enable_edge(add_edge(v1, v2, s_integer(-1), j));
            }
            bool add_non_strict_edge(theory_var v1, theory_var v2, literal_vector const& j) {
                // v1 <= v2
                return enable_edge(add_edge(v1, v2, s_integer(0), j));
            }
        };

        typedef union_find<union_find_default_ctx> union_find_t;

        struct relation {
            ast_manager&           m;
            func_decl_ref          m_next;
            sr_property            m_property;
            func_decl*             m_decl;
            atoms                  m_asserted_atoms;   // set of asserted atoms
            unsigned               m_asserted_qhead;
            svector<scope>         m_scopes;
            graph                  m_graph;
            union_find_default_ctx m_ufctx;
            union_find_t           m_uf;
            literal_vector         m_explanation;

            relation(sr_property p, func_decl* d, ast_manager& m): m(m), m_next(m), m_property(p), m_decl(d), m_asserted_qhead(0), m_uf(m_ufctx) {}

            func_decl* decl() { return m_decl; }

            app_ref   next(expr* a, expr* b) { return app_ref(m.mk_app(next(), a, b), m); }
            bool       is_next(expr* n) { return is_app(n) && next() == to_app(n)->get_decl(); }
            func_decl* next();

            void push();
            void pop(unsigned num_scopes);
            void ensure_var(theory_var v);
            bool new_eq_eh(literal l, theory_var v1, theory_var v2);
            void operator()(literal_vector const & ex) {
                m_explanation.append(ex);
            }
            void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {}

            bool add_strict_edge(theory_var v1, theory_var v2, literal_vector const& j);
            bool add_non_strict_edge(theory_var v1, theory_var v2, literal_vector const& j);
            
            std::ostream& display(theory_special_relations const& sr, std::ostream& out) const;
        };

        typedef u_map<atom*>     bool_var2atom;

        special_relations_util         m_util;
        atoms                          m_atoms;
        unsigned_vector                m_atoms_lim;
        obj_map<func_decl, relation*>  m_relations;
        bool_var2atom                  m_bool_var2atom;
        bool                           m_can_propagate;
        

        void del_atoms(unsigned old_size);
        lbool final_check(relation& r);
        lbool final_check_po(relation& r);
        lbool final_check_lo(relation& r);
        lbool final_check_plo(relation& r);
        lbool final_check_to(relation& r);
        lbool final_check_tc(relation& r);
        lbool propagate(relation& r);
        lbool enable(atom& a);
        bool  extract_equalities(relation& r);
        void set_neg_cycle_conflict(relation& r);
        void set_conflict(relation& r);
        lbool  propagate_plo(atom& a);
        lbool  propagate_po(atom& a); 
        lbool  propagate_tc(atom& a); 
        theory_var mk_var(expr* e);
        void count_children(graph const& g, unsigned_vector& num_children);
        void ensure_strict(graph& g);
        void ensure_tree(graph& g);
        void assign_interval(graph const& g, unsigned_vector const& num_children, unsigned_vector& lo, unsigned_vector& hi);
        expr_ref mk_inj(relation& r, model_generator& m);
        expr_ref mk_class(relation& r, model_generator& m);
        expr_ref mk_interval(relation& r, model_generator& mg, unsigned_vector & lo, unsigned_vector& hi);
        void init_model_lo(relation& r, model_generator& m);
        void init_model_to(relation& r, model_generator& m);
        void init_model_po(relation& r, model_generator& m, bool is_reflexive);
        void init_model_plo(relation& r, model_generator& m);
        bool is_neighbour_edge(graph const& g, edge_id id) const;
        bool is_strict_neighbour_edge(graph const& g, edge_id id) const;
        bool disconnected(graph const& g, dl_var u, dl_var v) const;

        literal mk_literal(expr* _e);
        enode* ensure_enode(expr* e);
        theory_var mk_var(enode* n) override;

        void collect_asserted_po_atoms(vector< std::pair<bool_var,bool> >& atoms) const;
        void display_atom(std::ostream & out, atom& a) const;
        void internalize_next(func_decl* f, app * term);

    public:
        theory_special_relations(ast_manager& m);
        ~theory_special_relations() override;

        theory * mk_fresh(context * new_ctx) override;
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        bool use_diseqs() const override { return false; }
        bool build_models() const override { return true; }
        final_check_status final_check_eh() override;
        void reset_eh() override;
        void assign_eh(bool_var v, bool is_true) override;
        void init_search_eh() override {}
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override {}
        void collect_statistics(::statistics & st) const override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
        void init_model(model_generator & m) override;
        bool can_propagate() override { return m_can_propagate; }
        void propagate() override;
        void display(std::ostream & out) const override;
   
    };
}

#endif
