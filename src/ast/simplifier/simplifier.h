/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    simplifier.h

Abstract:

    Generic expression simplifier with support for theory specific "plugins".

Author:

    Leonardo (leonardo) 2008-01-03

Notes:

--*/
#ifndef SIMPLIFIER_H_
#define SIMPLIFIER_H_

#include"base_simplifier.h"
#include"simplifier_plugin.h"
#include"plugin_manager.h"
#include"ast_util.h"
#include"obj_hashtable.h"

/**
   \brief Local simplifier.
   Proof production can be enabled/disabled.
   
   The simplifier can also apply substitutions during the
   simplification. A substitution is a mapping from expression
   to expression+proof, where for each entry e_1->(e_2,p) p is 
   a proof for (= e_1 e_2).
   
   The simplifier can also generate coarse grain proofs. In a coarse
   proof, local rewrite steps are omitted, and only the substitutions
   used are tracked.

   Example: 

   Consider the expression (+ a b), and the substitution b->(0, p)
   When fine grain proofs are enabled, the simplifier will produce the
   following proof

   Assume the id of the proof object p is $0. Note that p is a proof for (= b 0).

   $1: [reflexivity] |- (= a a)
   $2: [congruence] $1 $0 |- (= (+ a b) (+ a 0))
   $3: [plus-0] |- (= (+ a 0) a)
   $4: [transitivity] $2 $3 |- (= (+ a b) a)

   When coarse grain proofs are enabled, the simplifier produces the following
   proof:

   $1: [simplifier] $0 |- (= (+ a b) a)
*/
class simplifier : public base_simplifier {
protected:
    typedef simplifier_plugin plugin;
    plugin_manager<plugin>         m_plugins;
    ptr_vector<expr>               m_args;
    vector<rational>               m_mults;
    ptr_vector<expr>               m_args2;

    proof_ref_vector               m_proofs; // auxiliary vector for implementing exhaustive simplification.
    proof_ref_vector               m_subst_proofs; // in coarse grain proof generation mode, this vector tracks the justification for substitutions (see method get_subst).

    bool                           m_need_reset;
    bool                           m_use_oeq;

    bool                           m_visited_quantifier; //!< true, if the simplifier found a quantifier

    bool                           m_ac_support;

    expr_mark                      m_ac_mark;
    ptr_vector<expr>               m_ac_marked;
    obj_map<app, app *>            m_ac_cache;    // temporary cache for ac
    obj_map<app, proof *>          m_ac_pr_cache; // temporary cache for ac
    obj_map<expr, int>             m_colors;      // temporary cache for topological sort.
    obj_map<expr, rational>        m_ac_mults;

    /*
      Simplifier uses an idiom for rewriting ASTs without using recursive calls.

      - It uses a cache (field m_cache in base_simplifier) and a todo-stack (field m_todo in base_simplifier).
      
      - The cache is a mapping from AST to (AST + Proof). An entry [n -> (n',pr)] is used to store the fact
      that n and n' are equivalent and pr is a proof for that. If proofs are disabled, then pr is 0.
      We say n' is the result of the simplification of n.
      Note: Some simplifications do not preserve equivalence, but equisatisfiability.
      For saving space, we use pr = 0 also to represent the reflexivity proof [n -> (n, 0)].

     
      - The simplifier can be extended using plugin (subclasses of the class simplifier_plugin).
      Each theory has a family ID. All operators (func_decls) and sorts from a given theory have
      the same family_id. Given an application (object of the class app), we use the method
      get_family_id() to obtain the family id of the operator in this application. 
      The simplifier uses plugin to apply theory specific simplifications. The basic idea is:
      whenever an AST with family_id X is found, invoke the plugin for this family_id.
      A simplifier_plugin implements the following API:
         1) bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result)
         This method is invoked when the simplifier is trying to reduce/simplify an application
         of the form (f args[0] ... args[num_args - 1]), and f has a family_id associated with
         the plugin. The plugin may return false to indicate it could not simplify this application.
         If it returns true (success), the result should be stored in the argument result.

         2) bool reduce(func_decl * f, unsigned num_args, rational const * mults, expr * const * args, expr_ref & result);
         This method is a similar to the previous one, and it is used to handle associative operators.
         A plugin does not need to implement this method, the default implementation will use the previous one.
         The arguments mults indicates the multiplicity of every argument in args. 
         For example, suppose this reduce is invoked with the arguments (f, 2, [3, 2], [a, b], result).
         This represents the application (f a a a b b). 
         Some theory simplifiers may have efficient ways to encode this multiplicity. For example,
         the arithmetic solver, if f is "+", the multiplicity can be encoded using "*". 
         This optimization is used because some benchmarks can create term that are very huge when
         flattened. One "real" example (that motivated this optimization) is:
             let a1 = x1 + x1
             let a2 = a1 + a1
             ...
             let an = a{n-1} + a{n-1}
             an
         In this example, n was 32, so after AC flattening, we had an application
         (+ x1 ... x1) with 2^32 arguments. Using the simple reduce would produce a stack overflow.

         This class uses a topological sort for computing the multiplicities efficiently.
         So, the field m_colors is used to implement the topological sort.


         3) bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result)
         This method is invoked when the sort of lhs and rhs has a family_id associated with the plugin.
         This method allows theory specific simplifications such as:
         (= (+ a b) b)  --> (= a 0)
         Assuming n1 is a reference to (+ a b) and n2 to b, the simplifier would invoke
         reduce_eq(n1, n2, result)
         Like reduce, false can be returned if a simplification could not be applied.
         And if true is returned, then the result is stored in the argument result.

         4) bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result)
         It is similar to reduce_eq, but it used for theory specific simplifications for
         (distinct args[0] ... args[num_args-1])
         Example:
         (distinct 0 1 ... n) --> true

      - The idiom used in this class is implemented in the methdo reduce_core.
      See reduce_core for more details. The basic idea is:

         1) Get the next ast to be simplified from the todo-stack.
         2) If it is already cached, then do nothing. That is, this expression was already simplified.
         3) Otherwise, check whether all arguments already have been simplified (method visit_children).
             3a) The arguments that have not been simplified are added to the todo-stack by visit_children.
             In this case visit_children will return false.
             3b) If all arguments have already been simplified, then invoke reduce1 to perform a reduction/simplification
             step. The cache is updated with the result.

      - After invoking reduce_core(n), the cache contains an entry [n -> (n', pr)].

     */

    void flush_cache();

    /**
       \brief This method can be redefined in subclasses of simplifier to implement substitutions.
       It returns true if n should be substituted by r, where the substitution is justified by the
       proof p. The field m_subst_proofs is used to store these justifications when coarse proofs are used (PGM_COARSE).
       This method is redefined in the class subst_simplifier. It is used in asserted_formulas
       for implementing constant elimination. For example, if asserted_formulas contains the atoms
       (= a (+ b 1)) (p a c), then the constant "a" can be eliminated. This is achieved by set (+ b 1) as
       a substitution for "a".
    */
    virtual bool get_subst(expr * n, expr_ref & r, proof_ref & p);

    void reduce_core(expr * n);
    bool visit_children(expr * n);
    bool visit_ac(app * n);
    virtual bool visit_quantifier(quantifier * q);
    void reduce1(expr * n);
    void reduce1_app(app * n);
    void reduce1_app_core(app * n);
    void reduce1_ac_app_core(app * n);
    void mk_congruent_term(app * n, app_ref & r, proof_ref & p);
    void mk_ac_congruent_term(app * n, app_ref & r, proof_ref & p);
    bool get_args(app * n, ptr_vector<expr> & result, proof_ref & p);
    void get_ac_args(app * n, ptr_vector<expr> & args, vector<rational> & mults);
    virtual void reduce1_quantifier(quantifier * q);
    void dump_rewrite_lemma(func_decl * decl, unsigned num_args, expr * const * args, expr* result);
    void ac_top_sort(app * n, ptr_buffer<expr> & result);
    
public:
    simplifier(ast_manager & manager);
    virtual ~simplifier();

    void enable_ac_support(bool flag);

    /**
       \brief Simplify the expression \c s. Store the result in \c r, and a proof that <tt>(= s r)</tt> in \c p.
    */
    void operator()(expr * s, expr_ref & r, proof_ref & p);
    void reset() { if (m_need_reset) { flush_cache(); m_need_reset = false; } }

    bool visited_quantifier() const { return m_visited_quantifier; }

    void mk_app(func_decl * decl, unsigned num_args, expr * const * args, expr_ref & r);
    void cache_result(expr * n, expr * r, proof * p) { m_need_reset = true;  base_simplifier::cache_result(n, r, p); }

    void register_plugin(plugin * p);
    ptr_vector<plugin>::const_iterator begin_plugins() const { return m_plugins.begin(); }
    ptr_vector<plugin>::const_iterator end_plugins() const { return m_plugins.end(); }

    plugin * get_plugin(family_id fid) const { return m_plugins.get_plugin(fid); }

    ast_manager & get_manager() { return m; }

    void borrow_plugins(simplifier const & s);
    void release_plugins();

    void enable_presimp();
};

class subst_simplifier : public simplifier {
protected:
    expr_map *                     m_subst_map;
    virtual bool get_subst(expr * n, expr_ref & r, proof_ref & p);
public:
    subst_simplifier(ast_manager & manager):simplifier(manager), m_subst_map(0) {}
    void set_subst_map(expr_map * s);
};

void push_assertion(ast_manager & m, expr * e, proof * pr, expr_ref_vector & result, proof_ref_vector & result_prs);

#endif 
