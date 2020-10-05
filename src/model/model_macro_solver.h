/*++
Copyright (c) 2006 Microsoft Corporation

Abstract:

    Macro solving utilities

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

--*/

#pragma once
#include "util/obj_pair_hashtable.h"
#include "util/backtrackable_set.h"
#include "ast/macros/quantifier_macro_info.h"
#include "model/model_core.h"


class quantifier2macro_infos {
public:
    virtual ~quantifier2macro_infos() {}
    virtual quantifier_macro_info* operator()(quantifier* q) = 0;
};

/**
   \brief Base class for macro solvers.
*/
class base_macro_solver {
protected:
    ast_manager& m;
    quantifier2macro_infos& m_q2info;
    model_core* m_model;

    quantifier_macro_info* get_qinfo(quantifier* q) const {
        return m_q2info(q);
    }

    void set_else_interp(func_decl* f, expr* f_else);

    virtual bool process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) = 0;

public:
    base_macro_solver(ast_manager& m, quantifier2macro_infos& q2i) :
        m(m),
        m_q2info(q2i),
        m_model(nullptr) {
    }

    virtual ~base_macro_solver() {}

    /**
       \brief Try to satisfy quantifiers in qs by using macro definitions.
       Store in new_qs the quantifiers that were not satisfied.
       Store in residue a subset of the quantifiers that were satisfied but contain information useful for the auf_solver.
    */
    void operator()(model_core& m, ptr_vector<quantifier>& qs, ptr_vector<quantifier>& residue);
};

/**
   \brief The simple macro solver satisfies quantifiers that contain
   (conditional) macros for a function f that does not occur in any other quantifier.

   Since f does not occur in any other quantifier, I don't need to track the dependencies
   of f. That is, recursive definition cannot be created.
*/
class simple_macro_solver : public base_macro_solver {
protected:
    /**
       \brief Return true if \c f is in (qs\{q})
    */
    bool contains(func_decl* f, ptr_vector<quantifier> const& qs, quantifier* q);

    bool process(quantifier* q, ptr_vector<quantifier> const& qs);

    bool process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) override;

public:
    simple_macro_solver(ast_manager& m, quantifier2macro_infos& q2i) :
        base_macro_solver(m, q2i) {}
};


class hint_macro_solver : public base_macro_solver {
    /*
      This solver tries to satisfy quantifiers by using macros, cond_macros and hints.
      The idea is to satisfy a set of quantifiers Q = Q_{f_1} union ... union Q_{f_n}
      where Q_{f_i} is the set of quantifiers that contain the function f_i.
      Let f_i = def_i be macros (in this solver conditions are ignored).
      Let Q_{f_i = def_i} be the set of quantifiers where f_i = def_i is a macro.
      Then, the set Q can be satisfied using f_1 = def_1 ... f_n = def_n
      when

      Q_{f_1} union ... union Q_{f_n} = Q_{f_1 = def_1} ... Q_{f_n = def_n} (*)

      So, given a set of macros f_1 = def_1, ..., f_n = d_n, it is very easy to check
      whether they can be used to satisfy all quantifiers that use f_1, ..., f_n in
      non ground terms.

      We can find the sets of f_1 = def_1, ..., f_n = def_n that satisfy Q using
      the following search procedure
            find(Q)
              for each f_i = def_i in Q
                  R = greedy(Q_{f_i = def_1}, Q_f_i \ Q_{f_i = def_i}, {f_i}, {f_i = def_i})
                  if (R != empty-set)
                    return R
            greedy(Satisfied, Residue, F, F_DEF)
              if Residue = empty-set return F_DEF
              for each f_j = def_j in Residue such that f_j not in F
                  New-Satisfied = Satisfied union Q_{f_j = def_j}
                  New-Residue = (Residue union Q_{f_j}) \ New-Satisfied
                  R = greedy(New-Satisfied, New-Residue, F \union {f_j}, F_DEF union {f_j = def_j})
                  if (R != empty-set)
                     return R

      This search may be too expensive, and is exponential on the number of different function
      symbols.
      Some observations to prune the search space.
      1) If f_i occurs in a quantifier without macros, then f_i and any macro using it can be ignored during the search.
      2) If f_i = def_i is not a macro in a quantifier q, and there is no other f_j = def_j (i != j) in q,
         then f_i = def_i can be ignored during the search.
    */

    typedef obj_hashtable<quantifier> quantifier_set;
    typedef obj_map<func_decl, quantifier_set*> q_f;
    typedef obj_pair_map<func_decl, expr, quantifier_set*> q_f_def;
    typedef obj_pair_hashtable<func_decl, expr> f_def_set;
    typedef obj_hashtable<expr> expr_set;
    typedef obj_map<func_decl, expr_set*> f2defs;

    q_f                        m_q_f;
    q_f_def                    m_q_f_def;
    ptr_vector<quantifier_set> m_qsets;
    f2defs                     m_f2defs;
    ptr_vector<expr_set>       m_esets;

    void insert_q_f(quantifier* q, func_decl* f);

    void insert_f2def(func_decl* f, expr* def);
    void insert_q_f_def(quantifier* q, func_decl* f, expr* def);

    quantifier_set* get_q_f_def(func_decl* f, expr* def);

    expr_set* get_f_defs(func_decl* f) { return m_f2defs[f]; }
    quantifier_set* get_q_f(func_decl* f) { return m_q_f[f]; }

    void reset_q_fs();

    func_decl_set              m_forbidden;
    func_decl_set              m_candidates;

    bool is_candidate(quantifier* q) const;
    void register_decls_as_forbidden(quantifier* q);

    void preprocess(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& qcandidates, ptr_vector<quantifier>& non_qcandidates);

    void mk_q_f_defs(ptr_vector<quantifier> const& qs);

    static void display_quantifier_set(std::ostream& out, quantifier_set const* s);

    void display_qcandidates(std::ostream& out, ptr_vector<quantifier> const& qcandidates) const;

    //
    // Search: main procedures
    //

    struct ev_handler {
        hint_macro_solver* m_owner;

        void operator()(quantifier* q, bool ins) {
            quantifier_macro_info* qi = m_owner->get_qinfo(q);
            qi->set_the_one(nullptr);
        }

        ev_handler(hint_macro_solver* o) :
            m_owner(o) {
        }
    };


    typedef backtrackable_set<quantifier_set, quantifier*> qset;
    typedef backtrackable_set<quantifier_set, quantifier*, ev_handler> qsset;
    typedef obj_map<func_decl, expr*> f2def;

    qset         m_residue;
    qsset        m_satisfied;
    f2def        m_fs; // set of function symbols (and associated interpretation) that were used to satisfy the quantifiers in m_satisfied.

    struct found_satisfied_subset {};

    void display_search_state(std::ostream& out) const;
    bool check_satisfied_residue_invariant();


    bool update_satisfied_residue(func_decl* f, expr* def);

    /**
       \brief Extract from m_residue, func_decls that can be used as macros to satisfy it.
       The candidates must not be elements of m_fs.
    */
    void get_candidates_from_residue(func_decl_set& candidates);

    /**
      \brief Try to reduce m_residue using the macros of f.
    */
    void greedy(func_decl* f, unsigned depth);

    /**
       \brief check if satisfied subset introduces a cyclic dependency.

       f_1 = def_1(f_2), ..., f_n = def_n(f_1)
     */

    expr_mark               m_visited;
    obj_hashtable<func_decl> m_acyclic;
    bool is_cyclic();
    struct occurs {};
    struct occurs_check {
        hint_macro_solver& m_cls;
        occurs_check(hint_macro_solver& hs) : m_cls(hs) {}
        void operator()(app* n) { if (m_cls.m_fs.contains(n->get_decl()) && !m_cls.m_acyclic.contains(n->get_decl())) throw occurs(); }
        void operator()(var* n) {}
        void operator()(quantifier* n) {}
    };
    bool is_acyclic(expr* def);

    /**
       \brief Try to reduce m_residue (if not empty) by selecting a function f
       that is a macro in the residue.
    */
    void greedy(unsigned depth);

    /**
       \brief Try to find a set of quantifiers by starting to use the macros of f.
       This is the "find" procedure in the comments above.
       The set of satisfied quantifiers is in m_satisfied, and the remaining to be
       satisfied in m_residue. When the residue becomes empty we throw the exception found_satisfied_subset.
    */
    void process(func_decl* f);

    /**
       \brief Copy the quantifiers from qcandidates to new_qs that are not in m_satisfied.
    */
    void copy_non_satisfied(ptr_vector<quantifier> const& qcandidates, ptr_vector<quantifier>& new_qs);
    /**
       \brief Use m_fs to set the interpretation of the function symbols that were used to satisfy the
       quantifiers in m_satisfied.
    */
    void set_interp();

    void reset();

    bool process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) override;

public:
    hint_macro_solver(ast_manager& m, quantifier2macro_infos& q2i) :
        base_macro_solver(m, q2i),
        m_satisfied(ev_handler(this)) {
    }

    ~hint_macro_solver() override {
        reset();
    }

};

/**
\brief Satisfy clauses that are not in the AUF fragment but define conditional macros.
These clauses are eliminated even if the symbol being defined occurs in other quantifiers.
The auf_solver is ineffective in these clauses.

\remark Full macros are used even if they are in the AUF fragment.
*/

class non_auf_macro_solver : public base_macro_solver {
    func_decl_dependencies& m_dependencies;
    unsigned m_mbqi_force_template{ 0 };

    bool add_macro(func_decl* f, expr* f_else);

    // Return true if r1 is a better macro than r2.
    bool is_better_macro(cond_macro* r1, cond_macro* r2);

    cond_macro* get_macro_for(func_decl* f, quantifier* q);

    typedef std::pair<cond_macro*, quantifier*> mq_pair;

    void collect_candidates(ptr_vector<quantifier> const& qs, obj_map<func_decl, mq_pair>& full_macros, func_decl_set& cond_macros);

    void process_full_macros(obj_map<func_decl, mq_pair> const& full_macros, obj_hashtable<quantifier>& removed);

    void process(func_decl* f, ptr_vector<quantifier> const& qs, obj_hashtable<quantifier>& removed);

    void process_cond_macros(func_decl_set const& cond_macros, ptr_vector<quantifier> const& qs, obj_hashtable<quantifier>& removed);

    bool process(ptr_vector<quantifier> const& qs, ptr_vector<quantifier>& new_qs, ptr_vector<quantifier>& residue) override;

public:
    non_auf_macro_solver(ast_manager& m, quantifier2macro_infos& q2i, func_decl_dependencies& d) :
        base_macro_solver(m, q2i),
        m_dependencies(d) {
    }

    void set_mbqi_force_template(unsigned n) { m_mbqi_force_template = n; }
};


