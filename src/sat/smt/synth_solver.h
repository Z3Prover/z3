/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    synth_solver.h

Author:

    Petra Hozzova 2023-08-08
    Nikolaj Bjorner (nbjorner) 2020-08-17

Notes:

- for each function, determine a set of input variables, a set of uncomputable, and a spec.
- functions may share specs
- functions may share input variables. 
- functions may differ in input variables and uncomputable.
- uncomputable play the role of input variables that the function cannot access.
- functions may be in one of the forms:
  - f is a skolem functions: there is a unique occurrence of f, it takes all input variables as argument
  - f is a nested skolem functions: function occurrences are unique and can be ordered by subsets. f(x) g(x,y) h(x,z)
  - f comes from a Henkin quantifier: there is a unique occurrence of each f, but variables are uncorrelated.
  - f occurrences use arbitrary arguments, there is more than one occurrence of f.

Functions that occur uniquely are handled the same way, regardless of whether they are Skolem or Henkin.
Input variables that are not in scope of these functions are uncomputable.


Example setting: 
- Synthesize f(x,y), g(x, z)
- Inputs     [x,y,z]
- Uncomputable u 
- Spec       Phi[x, y, z, f(x,y), g(x, z), u]
- Auxilary   Psi[u]

- Using model-based projection.
- Given model M for Phi
- f(x,y):
  - Set x, y, f(x,y) to shared, 
    - u, z g(x,z) are not shared
  - Phi1[x,y,f(x,y)] := Project u, z, g(x, z) form Phi
  - Set x, y to shared
  - realizer t[x,y] := Project f(x,y) from Phi1 
- g(x,z):
  - set x, z, g(x,z) to shared
  - Phi1 := Project u, y, f(x, y) from Phi
  - Set x, z to shared
  - realizer s[x,z] := Project g(x, z) from Phi3 
- Guard: Phi1[x,y,t[x,y]] -> f(x,y) = t[x,y]
  Guard: Phi2[x,z,s[x,z]] -> g(x,z) = s[x,z]
- Block not (Phi1[t] & Phi2[s])

Properties: 
- Phi1 => Exists u, z, g(x, z) . Phi
- Phi1[x,y,t[x,y]] is true in M 
- Similar with Phi2

--*/

#pragma once

#include "sat/smt/sat_th.h"
#include "solver/solver.h"


namespace synth {

    class solver : public euf::th_euf_solver {
    public:
        solver(euf::solver& ctx);
        ~solver() override;        
        void asserted(sat::literal lit) override;
        sat::check_result check() override;
        void push_core() override {}
        void pop_core(unsigned n) override {}
        bool unit_propagate() override;
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override {}
        void collect_statistics(statistics& st) const override {}
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out << "synth"; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out << "synth"; }
        euf::th_solver* clone(euf::solver& ctx) override;

    private:
        class synth_objective {
            app* obj;
            expr_ref m_solution;
            bool m_is_solved = false;
        public:
            synth_objective(ast_manager& m, app* obj): obj(obj), m_solution(m) { VERIFY(obj->get_num_args() > 0); }
            expr* output() const { return obj->get_arg(0); }
            expr* const* begin() const { return obj->get_args() + 1; }
            expr* const* end() const { return obj->get_args() + obj->get_num_args(); }
            bool operator==(synth_objective const& o) const { return o.obj == obj; }
            expr* solution() const { return m_solution; }
            void set_solution(expr* s) { m_solution = s; m_is_solved = true; }
            void clear_solution() { m_solution = nullptr; m_is_solved = false;}
            bool is_solved() const { return m_is_solved; }

            struct unset_solution : public trail {
                synth_objective& e;
                unset_solution(synth_objective& e): e(e) {}
                void undo() override { e.clear_solution(); }
            };
        };

        
        bool is_output(expr* e) const;
        void add_uncomputable(app* e);
        void add_synth_objective(synth_objective const & e);
        void add_specification(app* e, expr* arg);
        bool contains_uncomputable(expr* e);
        void on_merge_eh(euf::enode* root, euf::enode* other);
        expr_ref compute_solution(synth_objective const& synth_objective);
        expr_ref compute_condition();
        bool compute_solutions();
        void compute_rep();

        bool synthesize_uninterpreted_sort(synth_objective& obj);
        bool synthesize_arithmetic(synth_objective& obj);

        expr* get_rep(euf::enode* n) { return m_rep.get(n->get_root_id(), nullptr); };
        bool has_rep(euf::enode* n) { return !!get_rep(n); };
        void set_rep(euf::enode* n, expr* e) { m_rep.setx(n->get_root_id(), e); };

        expr_ref simplify_condition(expr* e);
        
        bool_vector     m_is_computable;
        bool            m_is_solved = false;
        expr_ref_vector m_rep;
        
    	vector<synth_objective>  m_synth;
        obj_hashtable<func_decl> m_uncomputable;
        ptr_vector<expr>         m_spec;

    };

};
