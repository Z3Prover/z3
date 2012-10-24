/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    demodulator.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-12.

Revision History:

    Christoph M. Wintersteiger (cwinter) 2012-10-24: Moved from demodulator.h to ufbv_rewriter.h

--*/
#ifndef _UFBV_REWRITER_H_
#define _UFBV_REWRITER_H_

#include"ast.h"
#include"substitution.h"
#include"obj_hashtable.h"
#include"obj_pair_hashtable.h"
#include"array_map.h"
#include"basic_simplifier_plugin.h"

/**
   \brief Apply demodulators as a preprocessing technique.

In first-order theorem proving (FOTP), a demodulator is a universally quantified formula of the form:

Forall X1, ..., Xn.  L[X1, ..., Xn] = R[X1, ..., Xn]
Where L[X1, ..., Xn] contains all variables in R[X1, ..., Xn], and 
L[X1, ..., Xn] is "bigger" than R[X1, ...,Xn].

The idea is to replace something big L[X1, ..., Xn] with something smaller R[X1, ..., Xn].
In FOTP, they use term orderings to decide what does it mean to be smaller.
We are using demodulators in a different context (pre-processing). 
So, I suggest we have a virtual method is_smaller for comparing expressions.
The default implementation just compares the size of the expressions. 

Similarly, in our context, formulas using iff are also demodulators.
Forall X1, ..., Xn.  L[X1, ..., Xn] iff R[X1, ..., Xn]

After selecting the demodulators, we traverse the rest of the formula looking for instances of L[X1, ..., Xn].
Whenever we find an instance, we replace it with the associated instance of R[X1, ..., Xn].

For example, suppose we have

Forall x, y.  f(x+y, y) = y
and
f(g(b) + h(c), h(c)) <= 0

The term f(g(b) + h(c), h(c)) is an instance of f(x+y, y) if we replace x <- g(b) and y <- h(c).
So, we can replace it with "y" which is bound to h(c) in this example. So, the result of the transformation is:

Forall x, y.  f(x+y, y) = y
and
h(c) <= 0

In the first implementation, let us ignore theory matching. That is,
for us the term f(a+1) is not an instance of f(1+x), because the
matcher doesn't know + is commutative.  Observe the demodulator is
*not* copied to the macro manager in this case.

Another complication is when we are looking for instances inside other universally quantified formulas.
The problem is that both formulas (demodular) and target are reusing variables names (ids).
To avoid renaming, we use offsets. The idea is to represent renames implicitly. In this case,
each offset is a different "variable bank". A pair (expr, offset) is essentially an expression
where every variable in expr is assumed to be from the "bank" offset.

The class substitution (in substitution.h) manages offsets for us.
The class matcher (in matcher.h) can be use to test whether an expression is an instance of another one.

Finally, there is the problem when we have N demodulators (where N is big), and a big formula, and we want
to traverse the formula only once looking for opportunities for applying these N demodulators.
We want to efficiently find the applicable demodulars. 
We can start with a simple optimization that given a func_decl it returns the set of demodulators that start with this declaration.
For example, suppose we have the demodulators.
   forall x, f(x, g(0)) = 10
   forall x, f(g(h(x)), g(1)) = 20
Then, in our "index" f would map to these two demodulators.

As a final optimization, we should adapt the code to use substitution-trees.
The current implementation in Z3 is not efficient, and I think it is buggy.
So, it would be great to replace it with a new one.
The code in spc_rewriter.* does something like that. We cannot reuse this code directly since it is meant
for the superposion engine in Z3, but we can adapt it for our needs in the preprocessor.
   
*/
class ufbv_rewriter {
    class rewrite_proc;
    class add_back_idx_proc;
    class remove_back_idx_proc;
    class can_rewrite_proc;

    typedef std::pair<expr *, bool> expr_bool_pair;

    class plugin {
        ast_manager& m_manager;
    public:
        plugin(ast_manager& m): m_manager(m) { }        
        void ins_eh(expr* k, expr_bool_pair v) { m_manager.inc_ref(k); m_manager.inc_ref(v.first); }
        void del_eh(expr* k, expr_bool_pair v) { m_manager.dec_ref(k); m_manager.dec_ref(v.first); }
        static unsigned to_int(expr const * k) { return k->get_id(); }
    };
    typedef array_map<expr*, expr_bool_pair, plugin> expr_map;
    
    typedef std::pair<expr *, expr *> expr_pair;
    typedef obj_hashtable<expr> expr_set;    
    typedef obj_map<func_decl, expr_set *> back_idx_map;
    typedef obj_hashtable<quantifier> quantifier_set;
    typedef obj_map<func_decl, quantifier_set *> fwd_idx_map;
    typedef obj_map<quantifier, expr_pair> demodulator2lhs_rhs;
    typedef expr_map rewrite_cache_map;

    /**
       \brief Custom matcher & substitution application
    */
    class match_subst {
        typedef std::pair<expr *, expr *>      expr_pair;
        typedef obj_pair_hashtable<expr, expr> cache;

        void reset();

        ast_manager &         m_manager;
        substitution          m_subst;
        cache                 m_cache;
        svector<expr_pair>    m_todo;
        bool                  m_all_args_eq;
     
        bool match_args(app * t, expr * const * args);
   
    public:
        match_subst(ast_manager & m);
        void reserve(unsigned max_vid) { m_subst.reserve(2, max_vid+1); }
        /**
           \brief Let f be the top symbol of lhs. If (f args) is an
           instance of lhs, that is, there is a substitution s
           s.t. s[lhs] = (f args), then return true and store s[rhs]
           into new_rhs.  Where s[t] represents the application of the
           substitution s into t.

           Assumptions, the variables in lhs and (f args) are assumed to be distinct.
           So, (f x y) matches (f y x). 
           Moreover, the result should be in terms of the variables in (f args).
        */
        bool operator()(app * lhs, expr * rhs, expr * const * args, expr_ref & new_rhs);
        
        /**
           \brief Return true if \c i is an instance of \c t.
        */
        bool operator()(expr * t, expr * i);
    };

    ast_manager &       m_manager;
    match_subst         m_match_subst;
    basic_simplifier_plugin & m_bsimp;
    fwd_idx_map         m_fwd_idx;
    back_idx_map        m_back_idx;
    demodulator2lhs_rhs m_demodulator2lhs_rhs;
    expr_ref_buffer     m_todo;
    obj_hashtable<expr> m_processed;
    ptr_vector<expr>    m_new_args;

    expr_ref_buffer     m_rewrite_todo;
    rewrite_cache_map   m_rewrite_cache;
    expr_ref_buffer     m_new_exprs;
    
    void insert_fwd_idx(expr * large, expr * small, quantifier * demodulator);
    void remove_fwd_idx(func_decl * f, quantifier * demodulator);
    bool check_fwd_idx_consistency(void);
    void show_fwd_idx(std::ostream & out);
    bool is_demodulator(expr * e, expr_ref & large, expr_ref & small) const;
    bool can_rewrite(expr * n, expr * lhs);
    
    expr * rewrite(expr * n);
    bool rewrite1(func_decl * f, ptr_vector<expr> & m_new_args, expr_ref & np);
    bool rewrite_visit_children(app * a);
    void rewrite_cache(expr * e, expr * new_e, bool done);
    void reschedule_processed(func_decl * f);
    void reschedule_demodulators(func_decl * f, expr * np);
    unsigned max_var_id(expr * e);
    
protected:    
    // is_smaller returns -1 for e1<e2, 0 for e1==e2 and +1 for e1>e2.
    virtual int is_smaller(expr * e1, expr * e2) const; 

    // is_subset returns -1 for e1 subset e2, +1 for e2 subset e1, 0 else.
    virtual int is_subset(expr * e1, expr * e2) const; 

public:
    ufbv_rewriter(ast_manager & m, basic_simplifier_plugin & p);
    virtual ~ufbv_rewriter();
    
    void operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);

    /**
      Given a demodulator (aka rewrite rule) of the form
      Forall X. L[X] = R[X]
      We say the top symbol is the first symbol in L.
      For example: f is the top symbol in
      Forall x, f(h(x)) = x + 1

      The rewrite engine main loop is based on the DISCOUNT loop used in first-order theorem provers.
      
      Main structures:
      - m_todo:          The todo-stack of formulas to be processed.
      - m_fwd_idx:       "Forward index" for finding efficiently which demodulators can be used to rewrite an expression.
                         We organize this set as a mapping from func_decl to a set of demodulators which start with the same top symbol.
      - m_processed:     The set of already processed formulas. We can represent it using a hashtable.
      - m_back_idx:      "Backward index" we use it to find efficiently which already processed expressions and demodulators may be rewritten
                         by a new demodulator. Again, we use a very simple index, for each uninterpreted function symbol (ignore constants)
                         f, store the expressions in m_processed and the demodulators that contain f.
                         If you prefer, you may use two m_back_idxs (one for formulas in m_processed and another for demodulators in m_fwd_idx).

      Initially, m_todo contains all formulas. That is, it contains the argument exprs. m_fwd_idx, m_processed, m_back_idx are empty.

      while (m_todo is not empty) {
        let n be the next formula in m_todo.
        rewrite n using m_fwd_idx, and let n' be the result.
        // at this point, it should be the case that there is no demodulator in m_fwd_idx that can rewrite n'.
        if (n' is not a demodulator) {
          insert n' into m_processed
          update m_back_idx (traverse n' and for each uninterpreted function declaration f in n' add the entry f->n' to m_back_idx)
        }
        else {
            let f be the top symbol of n'
            use m_back_idx to find all formulas p in m_processed that contains f {
               remove p from m_processed
               remove p from m_back_idx
               insert p into m_todo
            }
            use m_back_idx to find all demodulators d in m_fwd_idx that contains f {
               if n' can rewrite d { 
                  // this is a quick check, we just traverse d and check if there is an expression in d that is an instance of lhs of n'.
                  // we cannot use the trick used for m_processed, since the main loop would not terminate.
                  remove d from m_fwd_idx
                  remode d from m_back_idx
                  insert p into m_todo
               }
            }
            insert n' into m_fwd_idx
            update m_back_idx
        }
     }
     the result is the contents of m_processed + all demodulators in m_fwd_idx.

     Note: to remove p from m_back_idx, we need to traverse p, and for every function declartion f in p, we should remove the entry f->p from m_back_idx.
     
     Note: we can implement m_back_idx for formulas as:
         typedef obj_hashtable<expr> expr_set;
         obj_map<func_decl, expr_set *> m_back_idx;
         we should represent the sets as hashtables because we want to be able to efficiently remove elements from these sets.
         ptr_vector<expr_set>           m_expr_set_to_delete; // same trick we used in macro_manager.
         we can use a similar structure for m_back_idx and m_fwd_idx for demodulators.
         
     Note: m_processed should be obj_hashtable<expr> since we want to remove elements from there efficiently.
    */    
};

#endif /* _UFBV_REWRITER_H_ */

