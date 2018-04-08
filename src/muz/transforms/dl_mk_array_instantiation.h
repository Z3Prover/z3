/*++

Module Name:

    dl_mk_array_instantiation.h

Abstract:
    Transforms predicates so that array invariants can be discovered.

    Motivation   :  Given a predicate P(a), no quantifier-free solution can express that P(a) <=> forall i, P(a[i]) = 0

    Solution     :  Introduce a fresh variable i, and transform P(a) into P!inst(i, a).
                    Now, (P!inst(i,a) := a[i] = 0) <=> P(a) := forall i, a[i] = 0.

                    Transformation on Horn rules:
                    P(a, args) /\ phi(a, args, args') => P'(args') (for simplicity, assume there are no arrays in args').
                    Is transformed into:
                    (/\_r in read_indices(phi) P!inst(r, a, args)) /\ phi(a, args, args') => P'(args')

    Limitations  :  This technique can only discover invariants on arrays that depend on one quantifier.
    Related work :  Techniques relying on adding quantifiers and eliminating them. See dl_mk_quantifier_abstraction and dl_mk_quantifier_instantiation

Implementation:
    The implementation follows the solution suggested above, with more options. The addition of options implies that in the simple
    case described above, we in fact have P(a) transformed into P(i, a[i], a).

    1) Dealing with multiple quantifiers -> The options fixedpoint.xform.instantiate_arrays.nb_quantifier gives the number of quantifiers per array.

    2) Enforcing the instantiation -> We suggest an option (enforce_instantiation) to enforce this abstraction. This transforms
       P(a) into P(i, a[i]). This enforces the solver to limit the space search at the cost of imprecise results. This option
       corresponds to fixedpoint.xform.instantiate_arrays.enforce

    3) Adding slices in the mix -> We wish to have the possibility to further restrict the search space: we want to smash cells, given a smashing rule.
       For example, in for loops j=0; j<n; j++, it might be relevant to restrict the search space and look for invariants that only depend on whether
       0<=i<j or j<=i, where i is the quantified variable.

       Formally, a smashing rule is a function from the Index set (usually integer) to integers (the id set).
       GetId(i) should return the id of the set i belongs in.

       In our example, we can give 0 as the id of the set {n, 0<=n<j} and 1 for the set {n, j<=n}, and -1 for the set {n, n<0}. We then have
       GetId(i) = ite(i<0, -1, ite(i<j, 0, 1))

       Given that GetId function, P(a) /\ phi(a, ...) => P'(...) is transformed into
       (/\_r in read_indices(phi) P!inst(id_r, a[r], a) /\ GetId(r) = id_r) /\ phi(a, ...) => P'(...).
       Note : when no slicing is done, GetId(i) = i.
       This option corresponds to fixedpoint.xform.instantiate_arrays.slice_technique

       Although we described GetId as returning integers, there is no reason to restrict the type of ids to integers. A more direct method,
       for the 0<=i<j or j<=i case could be :
       GetId(i) = (i<0, i<j)

       GetId is even more powerful as we deal with the multiple quantifiers on multiple arrays.
       For example, we can use GetId to look for the same quantifiers in each array.
       Assume we have arrays a and b, instantiated with one quantifier each i and j.
       We can have GetId(i,j) = ite(i=j, (i, true), (fresh, false))

    4) Reducing the set of r in read_indices(phi): in fact, we do not need to "instantiate" on all read indices of phi,
       we can restrict ourselves to those "linked" to a, through equalities and stores.


Author:

    Julien Braine

Revision History:

--*/

#ifndef DL_MK_ARRAY_INSTANTIATION_H_
#define DL_MK_ARRAY_INSTANTIATION_H_


#include "ast/factor_equivs.h"
#include "muz/base/dl_rule_transformer.h"

namespace datalog {

    class context;
    class mk_array_instantiation : public rule_transformer::plugin {
       //Context objects
       ast_manager&      m;
       context&          m_ctx;
       array_util   m_a;

       //Rule set context
       const rule_set*src_set;
       rule_set*dst;
       rule_manager* src_manager;

       //Rule context
       obj_map<expr, ptr_vector<expr> > selects;
       expr_equiv_class eq_classes;
       unsigned cnt;//Index for new variables
       obj_map<expr, var*> done_selects;
       expr_ref_vector ownership;

       //Helper functions
       void instantiate_rule(const rule& r, rule_set & dest);//Instantiates the rule
       void retrieve_selects(expr* e);//Retrieves all selects (fills the selects and eq_classes members)
       expr_ref rewrite_select(expr*array, expr*select);//Rewrites select(a, args) to select(array, args)
       expr_ref_vector retrieve_all_selects(expr*array);//Retrieves all selects linked to a given array (using eq classes and selects)
       expr_ref_vector instantiate_pred(app*old_pred);//Returns all the instantiation of a given predicate
       expr_ref create_pred(app*old_pred, expr_ref_vector& new_args);//Creates a predicate
       expr_ref create_head(app* old_head);//Creates the new head
       var * mk_select_var(expr* select);

       /*Given the old predicate, and the new arguments for the new predicate, returns the new setId arguments.
         By default getId(P(x, y, a, b), (x, y, a[i], a[j], a, b[k], b[l], b)) (nb_quantifier=2, enforce=false)
         returns (i,j,k,l)
         So that the final created predicate is P!inst(x, y, a[i], a[j], a, b[k], b[l], b, i, j, k, l)
       */
       expr_ref_vector getId(app*old_pred, const expr_ref_vector& new_args);
     public:
        mk_array_instantiation(context & ctx, unsigned priority);
        rule_set * operator()(rule_set const & source) override;
        ~mk_array_instantiation() override{}
    };



};

#endif /* DL_MK_ARRAY_INSTANTIATION_H_ */
