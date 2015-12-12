/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    der.h

Abstract:

    Destructive equality resolution.

Author:

    Leonardo de Moura (leonardo) 2008-01-27.    

Revision History:

    Christoph Wintersteiger, 2010-03-30: Added Destr. Multi-Equality Resolution

--*/
#ifndef DER_H_
#define DER_H_

#include"ast.h"
#include"var_subst.h"

/*
  New DER: the class DER (above) eliminates variables one by one.
  This is inefficient, and we should implement a new version that
  can handle efficiently examples with hundreds of variables.
  
  Suppose the target of the simplification is the quantifier
  (FORALL (x1 T1) (x2 T2) ... (xn Tn) (or ....))
  So, the variables x1 ... xn are the candidates for elimination.
  First, we build a mapping of candidate substitutions
  Since variables x1 ... xn have ids 0 ... n-1, we can
  use an array m_map to implement this mapping.

  The idea is to traverse the children of the (or ...) looking
  for diseqs. The method is_var_diseq can be used for doing that.
  Given a child c, if is_var_diseq(c, num_decls, v, t) returns true,
  and m_map[v] is null, then we store t at m_map[v].
  For performance reasons, we also store a mapping from child position (in the OR) to variable ID.
  Thus, m_pos2var[pos] contains the variable that is defined by the diseq at position pos.
  m_pos2var[pos] = -1, if this position does not contain a diseq.

  After doing that, m_map contains the variables that can 
  be potentially eliminated using DER.
  We say m_map[v] is the definition of variable v.
  
  The next step is to perform a topological sort on these
  variables. The result is an array (m_order) of integers (variable ids)
  such that i < j implies that m_map[m_order[i]] does not depend on variable m_order[j].
  For example, consider the case where m_map contains the following values

  m_map[0]  =    (+ (VAR 2) 0)
  m_map[1]  =    null
  m_map[2]  =    (+ (VAR 3) 0)
  m_map[3]  =    (+ (VAR 1) 1)
  m_map[4]  =    (* (VAR 5) 2)
  m_map[5]  =    null

  In this example, variable 0 depends on the definition of variable 2, which 
  depends on the definition of variable 3, which depends on the definition of variable 0 (cycle).
  On the other hand, no cycle is found when starting at variable 4.
  Cycles can be broken by erasing entries from m_map. For example, the cycle above
  can be removed by setting m_map[0] = null. 

  m_map[0]  =    null
  m_map[1]  =    null
  m_map[2]  =    (+ (VAR 3) 0)
  m_map[3]  =    (+ (VAR 1) 1)
  m_map[4]  =    (* (VAR 5) 2)
  m_map[5]  =    null

  The file asserted_formulas.cpp has a class top_sort for performing topological sort.
  This class cannot be used here, since it is meant for eliminating constants (instead of variables).
  We need to implement a new top_sort here, we do not need a separate class for doing that.
  Moreover, it is much simpler, since m_map is just an array.
  
  In the example above (after setting m_map[0] to null), top_sort will produce the following order
  m_order = [3, 2, 4]

  The next step is to use var_subst to update the definitions in var_subst.
  The idea is to process the variables in the order specified by m_order.
  When processing m_map[m_order[i]] we use the definitions of all variables in m_order[0 ... i-1].
  For example:
  The first variable is 3, since it is at m_order[0], nothing needs to be done.
  Next we have variable 2, we use m_map[3] since 3 is before 2 in m_order. So, the new
  definition for 2 is (+ (+ (VAR 1) 1) 0). That is, we update m_map[2] with (+ (+ (VAR 1) 1) 0)
  Next we have variable 4, we use m_map[3] and m_map[2] since 3 and 2 are before 4 in m_order.
  In this case, var_subst will not do anything since m_map[4] does not contain variables 3 or 2.
  So, the new m_map is:

  m_map[0]  =    null
  m_map[1]  =    null
  m_map[2]  =    (+ (+ (VAR 1) 1) 0)
  m_map[3]  =    (+ (VAR 1) 1)
  m_map[4]  =    (* (VAR 5) 2)
  m_map[5]  =    null
  
  Now, we update the body of the quantifier using var_subst and the mapping above.
  The idea is to create a new set of children for the OR.
  For each child at position i, we do
     if m_map[m_pos2var[i]] != -1
       skip this child, it is a diseq used during DER
     else
       apply var_subst using m_map to this child, and store the result in a new children array
  Create a new OR (new body of the quantifier) using the new children
  Then, we create a new quantifier using this new body, and use the function elim_unused_vars to 
  eliminate the ununsed variables.

  Remark: let us implement the new version inside the class der.
  Use #if 0 ... #endif to comment the old version.
  
  Remark: after you are done, we can eliminate the call to occurs in is_var_diseq, since
  top_sort is already performing cycle detection.
*/

/**
   \brief Functor for applying Destructive Multi-Equality Resolution.
   
   (forall (X Y) (or X /= s C[X])) --> (forall (Y) C[Y])
*/
class der {
    ast_manager &   m_manager;
    var_subst       m_subst;
    expr_ref_buffer m_new_exprs;
    
    ptr_vector<expr> m_map;
    int_vector       m_pos2var;
    ptr_vector<var>  m_inx2var;
    unsigned_vector  m_order;
    expr_ref_vector  m_subst_map;
    expr_ref_buffer  m_new_args;

    /**
       \brief Return true if e can be viewed as a variable disequality. 
       Store the variable id in v and the definition in t.
       For example:

          if e is (not (= (VAR 1) T)), then v assigned to 1, and t to T.
          if e is (iff (VAR 2) T), then v is assigned to 2, and t to (not T).
              (not T) is used because this formula is equivalent to (not (iff (VAR 2) (not T))),
              and can be viewed as a disequality.
    */
    bool is_var_diseq(expr * e, unsigned num_decls, var *& v, expr_ref & t);

    void get_elimination_order();
    void create_substitution(unsigned sz);
    void apply_substitution(quantifier * q, expr_ref & r);

    void reduce1(quantifier * q, expr_ref & r, proof_ref & pr);

public:
    der(ast_manager & m):m_manager(m),m_subst(m),m_new_exprs(m),m_subst_map(m),m_new_args(m) {}
    ast_manager & m() const { return m_manager; }
    void operator()(quantifier * q, expr_ref & r, proof_ref & pr);
};

/**
   \brief Functor for applying Destructive Multi-Equality Resolution in all
   universal quantifiers in an expression.
*/
class der_rewriter {
protected:
    struct     imp;
    imp *      m_imp;
public:
    der_rewriter(ast_manager & m); 
    ~der_rewriter();

    ast_manager & m () const;

    void operator()(expr * t, expr_ref & result, proof_ref & result_pr);

    void cleanup();
    void reset();
};

typedef der_rewriter der_star; 

#endif /* DER_H_ */

