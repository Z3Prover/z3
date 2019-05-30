/*++
    Copyright (c) 2015 Microsoft Corporation
--*/

#ifndef Z3_API_H_
#define Z3_API_H_

DEFINE_TYPE(Z3_symbol);
DEFINE_TYPE(Z3_literals);
DEFINE_TYPE(Z3_config);
DEFINE_TYPE(Z3_context);
DEFINE_TYPE(Z3_sort);
#define Z3_sort_opt Z3_sort
DEFINE_TYPE(Z3_func_decl);
DEFINE_TYPE(Z3_ast);
#define Z3_ast_opt Z3_ast
DEFINE_TYPE(Z3_app);
DEFINE_TYPE(Z3_pattern);
DEFINE_TYPE(Z3_model);
DEFINE_TYPE(Z3_constructor);
DEFINE_TYPE(Z3_constructor_list);
DEFINE_TYPE(Z3_params);
DEFINE_TYPE(Z3_param_descrs);
DEFINE_TYPE(Z3_goal);
DEFINE_TYPE(Z3_tactic);
DEFINE_TYPE(Z3_probe);
DEFINE_TYPE(Z3_stats);
DEFINE_TYPE(Z3_solver);
DEFINE_TYPE(Z3_ast_vector);
DEFINE_TYPE(Z3_ast_map);
DEFINE_TYPE(Z3_apply_result);
DEFINE_TYPE(Z3_func_interp);
#define Z3_func_interp_opt Z3_func_interp
DEFINE_TYPE(Z3_func_entry);
DEFINE_TYPE(Z3_fixedpoint);
DEFINE_TYPE(Z3_optimize);
DEFINE_TYPE(Z3_rcf_num);

/** \defgroup capi C API */
/*@{*/

/** @name Types
    @{

   Most of the types in the C API are opaque pointers.

   - \c Z3_config: configuration object used to initialize logical contexts.
   - \c Z3_context: manager of all other Z3 objects, global configuration options, etc.
   - \c Z3_symbol: Lisp-like symbol used to name types, constants, and functions.  A symbol can be created using string or integers.
   - \c Z3_ast: abstract syntax tree node. That is, the data-structure used in Z3 to represent terms, formulas and types.
   - \c Z3_sort: kind of AST used to represent types.
   - \c Z3_func_decl: kind of AST used to represent function symbols.
   - \c Z3_app: kind of AST used to represent function applications.
   - \c Z3_pattern: kind of AST used to represent pattern and multi-patterns used to guide quantifier instantiation.
   - \c Z3_constructor: type constructor for a (recursive) datatype.
   - \c Z3_constructor_list: list of constructors for a (recursive) datatype.
   - \c Z3_params: parameter set used to configure many components such as: simplifiers, tactics, solvers, etc.
   - \c Z3_param_descrs: provides a collection of parameter names, their types, default values and documentation strings. Solvers, tactics, and other objects accept different collection of parameters.
   - \c Z3_model: model for the constraints asserted into the logical context.
   - \c Z3_func_interp: interpretation of a function in a model.
   - \c Z3_func_entry: representation of the value of a \c Z3_func_interp at a particular point.
   - \c Z3_fixedpoint: context for the recursive predicate solver.
   - \c Z3_optimize: context for solving optimization queries.
   - \c Z3_ast_vector: vector of \c Z3_ast objects.
   - \c Z3_ast_map: mapping from \c Z3_ast to \c Z3_ast objects.
   - \c Z3_goal: set of formulas that can be solved and/or transformed using tactics and solvers.
   - \c Z3_tactic: basic building block for creating custom solvers for specific problem domains.
   - \c Z3_probe: function/predicate used to inspect a goal and collect information that may be used to decide which solver and/or preprocessing step will be used.
   - \c Z3_apply_result: collection of subgoals resulting from applying of a tactic to a goal.
   - \c Z3_solver: (incremental) solver, possibly specialized by a particular tactic or logic.
   - \c Z3_stats: statistical data for a solver.
*/

/**
   \brief Z3 Boolean type. It is just an alias for \c bool.
*/
typedef bool Z3_bool;

/**
   \brief Z3 string type. It is just an alias for \ccode{const char *}.
*/
typedef const char * Z3_string;
typedef Z3_string * Z3_string_ptr;

/**
   \brief True value. It is just an alias for \c true.
*/
#define Z3_TRUE  true

/**
   \brief False value. It is just an alias for \c false.
*/
#define Z3_FALSE false

/**
   \brief Lifted Boolean type: \c false, \c undefined, \c true.
*/
typedef enum
{
    Z3_L_FALSE = -1,
    Z3_L_UNDEF,
    Z3_L_TRUE
} Z3_lbool;

/**
   \brief The different kinds of symbol.
   In Z3, a symbol can be represented using integers and strings (See #Z3_get_symbol_kind).

   \sa Z3_mk_int_symbol
   \sa Z3_mk_string_symbol
*/
typedef enum
{
    Z3_INT_SYMBOL,
    Z3_STRING_SYMBOL
} Z3_symbol_kind;


/**
   \brief The different kinds of parameters that can be associated with function symbols.
   \sa Z3_get_decl_num_parameters
   \sa Z3_get_decl_parameter_kind

   - Z3_PARAMETER_INT is used for integer parameters.
   - Z3_PARAMETER_DOUBLE is used for double parameters.
   - Z3_PARAMETER_RATIONAL is used for parameters that are rational numbers.
   - Z3_PARAMETER_SYMBOL is used for parameters that are symbols.
   - Z3_PARAMETER_SORT is used for sort parameters.
   - Z3_PARAMETER_AST is used for expression parameters.
   - Z3_PARAMETER_FUNC_DECL is used for function declaration parameters.
*/
typedef enum
{
    Z3_PARAMETER_INT,
    Z3_PARAMETER_DOUBLE,
    Z3_PARAMETER_RATIONAL,
    Z3_PARAMETER_SYMBOL,
    Z3_PARAMETER_SORT,
    Z3_PARAMETER_AST,
    Z3_PARAMETER_FUNC_DECL
} Z3_parameter_kind;

/**
   \brief The different kinds of Z3 types (See #Z3_get_sort_kind).
*/
typedef enum
{
    Z3_UNINTERPRETED_SORT,
    Z3_BOOL_SORT,
    Z3_INT_SORT,
    Z3_REAL_SORT,
    Z3_BV_SORT,
    Z3_ARRAY_SORT,
    Z3_DATATYPE_SORT,
    Z3_RELATION_SORT,
    Z3_FINITE_DOMAIN_SORT,
    Z3_FLOATING_POINT_SORT,
    Z3_ROUNDING_MODE_SORT,
    Z3_SEQ_SORT,
    Z3_RE_SORT,
    Z3_UNKNOWN_SORT = 1000
} Z3_sort_kind;

/**
   \brief
   The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types.

   - Z3_APP_AST:            constant and applications
   - Z3_NUMERAL_AST:        numeral constants
   - Z3_VAR_AST:            bound variables
   - Z3_QUANTIFIER_AST:     quantifiers
   - Z3_SORT_AST:           sort
   - Z3_FUNC_DECL_AST:      function declaration
   - Z3_UNKNOWN_AST:        internal
*/
typedef enum
{
    Z3_NUMERAL_AST,
    Z3_APP_AST,
    Z3_VAR_AST,
    Z3_QUANTIFIER_AST,
    Z3_SORT_AST,
    Z3_FUNC_DECL_AST,
    Z3_UNKNOWN_AST = 1000
} Z3_ast_kind;

/**
   \brief The different kinds of interpreted function kinds.

   - Z3_OP_TRUE The constant true.

   - Z3_OP_FALSE The constant false.

   - Z3_OP_EQ The equality predicate.

   - Z3_OP_DISTINCT The n-ary distinct predicate (every argument is mutually distinct).

   - Z3_OP_ITE The ternary if-then-else term.

   - Z3_OP_AND n-ary conjunction.

   - Z3_OP_OR n-ary disjunction.

   - Z3_OP_IFF equivalence (binary).

   - Z3_OP_XOR Exclusive or.

   - Z3_OP_NOT Negation.

   - Z3_OP_IMPLIES Implication.

   - Z3_OP_OEQ Binary equivalence modulo namings. This binary predicate is used in proof terms.
        It captures equisatisfiability and equivalence modulo renamings.

   - Z3_OP_ANUM Arithmetic numeral.

   - Z3_OP_AGNUM Arithmetic algebraic numeral. Algebraic numbers are used to represent irrational numbers in Z3.

   - Z3_OP_LE <=.

   - Z3_OP_GE >=.

   - Z3_OP_LT <.

   - Z3_OP_GT >.

   - Z3_OP_ADD Addition - Binary.

   - Z3_OP_SUB Binary subtraction.

   - Z3_OP_UMINUS Unary minus.

   - Z3_OP_MUL Multiplication - Binary.

   - Z3_OP_DIV Division - Binary.

   - Z3_OP_IDIV Integer division - Binary.

   - Z3_OP_REM Remainder - Binary.

   - Z3_OP_MOD Modulus - Binary.

   - Z3_OP_TO_REAL Coercion of integer to real - Unary.

   - Z3_OP_TO_INT Coercion of real to integer - Unary.

   - Z3_OP_IS_INT Check if real is also an integer - Unary.

   - Z3_OP_POWER Power operator x^y.

   - Z3_OP_STORE Array store. It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j).
        Array store takes at least 3 arguments.

   - Z3_OP_SELECT Array select.

   - Z3_OP_CONST_ARRAY The constant array. For example, select(const(v),i) = v holds for every v and i. The function is unary.

   - Z3_OP_ARRAY_DEFAULT Default value of arrays. For example default(const(v)) = v. The function is unary.

   - Z3_OP_ARRAY_MAP Array map operator.
         It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.

   - Z3_OP_SET_UNION Set union between two Boolean arrays (two arrays whose range type is Boolean). The function is binary.

   - Z3_OP_SET_INTERSECT Set intersection between two Boolean arrays. The function is binary.

   - Z3_OP_SET_DIFFERENCE Set difference between two Boolean arrays. The function is binary.

   - Z3_OP_SET_COMPLEMENT Set complement of a Boolean array. The function is unary.

   - Z3_OP_SET_SUBSET Subset predicate between two Boolean arrays. The relation is binary.

   - Z3_OP_AS_ARRAY An array value that behaves as the function graph of the
                    function passed as parameter.

   - Z3_OP_ARRAY_EXT Array extensionality function. It takes two arrays as arguments and produces an index, such that the arrays
                    are different if they are different on the index.

   - Z3_OP_BNUM Bit-vector numeral.

   - Z3_OP_BIT1 One bit bit-vector.

   - Z3_OP_BIT0 Zero bit bit-vector.

   - Z3_OP_BNEG Unary minus.

   - Z3_OP_BADD Binary addition.

   - Z3_OP_BSUB Binary subtraction.

   - Z3_OP_BMUL Binary multiplication.

   - Z3_OP_BSDIV Binary signed division.

   - Z3_OP_BUDIV Binary unsigned division.

   - Z3_OP_BSREM Binary signed remainder.

   - Z3_OP_BUREM Binary unsigned remainder.

   - Z3_OP_BSMOD Binary signed modulus.

   - Z3_OP_BSDIV0 Unary function. bsdiv(x,0) is congruent to bsdiv0(x).

   - Z3_OP_BUDIV0 Unary function. budiv(x,0) is congruent to budiv0(x).

   - Z3_OP_BSREM0 Unary function. bsrem(x,0) is congruent to bsrem0(x).

   - Z3_OP_BUREM0 Unary function. burem(x,0) is congruent to burem0(x).

   - Z3_OP_BSMOD0 Unary function. bsmod(x,0) is congruent to bsmod0(x).

   - Z3_OP_ULEQ Unsigned bit-vector <= - Binary relation.

   - Z3_OP_SLEQ Signed bit-vector  <= - Binary relation.

   - Z3_OP_UGEQ Unsigned bit-vector  >= - Binary relation.

   - Z3_OP_SGEQ Signed bit-vector  >= - Binary relation.

   - Z3_OP_ULT Unsigned bit-vector  < - Binary relation.

   - Z3_OP_SLT Signed bit-vector < - Binary relation.

   - Z3_OP_UGT Unsigned bit-vector > - Binary relation.

   - Z3_OP_SGT Signed bit-vector > - Binary relation.

   - Z3_OP_BAND Bit-wise and - Binary.

   - Z3_OP_BOR Bit-wise or - Binary.

   - Z3_OP_BNOT Bit-wise not - Unary.

   - Z3_OP_BXOR Bit-wise xor - Binary.

   - Z3_OP_BNAND Bit-wise nand - Binary.

   - Z3_OP_BNOR Bit-wise nor - Binary.

   - Z3_OP_BXNOR Bit-wise xnor - Binary.

   - Z3_OP_CONCAT Bit-vector concatenation - Binary.

   - Z3_OP_SIGN_EXT Bit-vector sign extension.

   - Z3_OP_ZERO_EXT Bit-vector zero extension.

   - Z3_OP_EXTRACT Bit-vector extraction.

   - Z3_OP_REPEAT Repeat bit-vector n times.

   - Z3_OP_BREDOR Bit-vector reduce or - Unary.

   - Z3_OP_BREDAND Bit-vector reduce and - Unary.

   - Z3_OP_BCOMP .

   - Z3_OP_BSHL Shift left.

   - Z3_OP_BLSHR Logical shift right.

   - Z3_OP_BASHR Arithmetical shift right.

   - Z3_OP_ROTATE_LEFT Left rotation.

   - Z3_OP_ROTATE_RIGHT Right rotation.

   - Z3_OP_EXT_ROTATE_LEFT (extended) Left rotation. Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.

   - Z3_OP_EXT_ROTATE_RIGHT (extended) Right rotation. Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.

   - Z3_OP_INT2BV Coerce integer to bit-vector. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - Z3_OP_BV2INT Coerce bit-vector to integer. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - Z3_OP_CARRY Compute the carry bit in a full-adder.
       The meaning is given by the equivalence
       (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3)))

   - Z3_OP_XOR3 Compute ternary XOR.
       The meaning is given by the equivalence
       (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3)

   - Z3_OP_BSMUL_NO_OVFL: a predicate to check that bit-wise signed multiplication does not overflow.
     Signed multiplication overflows if the operands have the same sign and the result of multiplication
     does not fit within the available bits. \sa Z3_mk_bvmul_no_overflow.

   - Z3_OP_BUMUL_NO_OVFL: check that bit-wise unsigned multiplication does not overflow.
     Unsigned multiplication overflows if the result does not fit within the available bits.
     \sa Z3_mk_bvmul_no_overflow.

   - Z3_OP_BSMUL_NO_UDFL: check that bit-wise signed multiplication does not underflow.
     Signed multiplication underflows if the operands have opposite signs and the result of multiplication
     does not fit within the available bits. Z3_mk_bvmul_no_underflow.

   - Z3_OP_BSDIV_I: Binary signed division.
     It has the same semantics as Z3_OP_BSDIV, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BUDIV_I: Binary unsigned division.
     It has the same semantics as Z3_OP_BUDIV, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BSREM_I: Binary signed remainder.
     It has the same semantics as Z3_OP_BSREM, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BUREM_I: Binary unsigned remainder.
     It has the same semantics as Z3_OP_BUREM, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BSMOD_I: Binary signed modulus.
     It has the same semantics as Z3_OP_BSMOD, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_PR_UNDEF: Undef/Null proof object.

   - Z3_OP_PR_TRUE: Proof for the expression 'true'.

   - Z3_OP_PR_ASSERTED: Proof for a fact asserted by the user.

   - Z3_OP_PR_GOAL: Proof for a fact (tagged as goal) asserted by the user.

   - Z3_OP_PR_MODUS_PONENS: Given a proof for p and a proof for (implies p q), produces a proof for q.
       \nicebox{
          T1: p
          T2: (implies p q)
          [mp T1 T2]: q
          }
          The second antecedents may also be a proof for (iff p q).

   - Z3_OP_PR_REFLEXIVITY: A proof for (R t t), where R is a reflexive relation. This proof object has no antecedents.
        The only reflexive relations that are used are
        equivalence modulo namings, equality and equivalence.
        That is, R is either '~', '=' or 'iff'.

   - Z3_OP_PR_SYMMETRY: Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
          \nicebox{
          T1: (R t s)
          [symmetry T1]: (R s t)
          }
          T1 is the antecedent of this proof object.

   - Z3_OP_PR_TRANSITIVITY: Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof
       for (R t u).
       \nicebox{
       T1: (R t s)
       T2: (R s u)
       [trans T1 T2]: (R t u)
       }

   - Z3_OP_PR_TRANSITIVITY_STAR: Condensed transitivity proof. 
     It combines several symmetry and transitivity proofs.

          Example:
          \nicebox{
          T1: (R a b)
          T2: (R c b)
          T3: (R c d)
          [trans* T1 T2 T3]: (R a d)
          }
          R must be a symmetric and transitive relation.

          Assuming that this proof object is a proof for (R s t), then
          a proof checker must check if it is possible to prove (R s t)
          using the antecedents, symmetry and transitivity.  That is,
          if there is a path from s to t, if we view every
          antecedent (R a b) as an edge between a and b.

   - Z3_OP_PR_MONOTONICITY: Monotonicity proof object.
          \nicebox{
          T1: (R t_1 s_1)
          ...
          Tn: (R t_n s_n)
          [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
          }
          Remark: if t_i == s_i, then the antecedent Ti is suppressed.
          That is, reflexivity proofs are suppressed to save space.

   - Z3_OP_PR_QUANT_INTRO: Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).

       T1: (~ p q)
       [quant-intro T1]: (~ (forall (x) p) (forall (x) q))

   - Z3_OP_PR_BIND: Given a proof p, produces a proof of lambda x . p, where x are free variables in p.
       T1: f
       [proof-bind T1] forall (x) f

   - Z3_OP_PR_DISTRIBUTIVITY: Distributivity proof object.
          Given that f (= or) distributes over g (= and), produces a proof for

          (= (f a (g c d))
             (g (f a c) (f a d)))

          If f and g are associative, this proof also justifies the following equality:

          (= (f (g a b) (g c d))
             (g (f a c) (f a d) (f b c) (f b d)))

          where each f and g can have arbitrary number of arguments.

          This proof object has no antecedents.
          Remark. This rule is used by the CNF conversion pass and
          instantiated by f = or, and g = and.

   - Z3_OP_PR_AND_ELIM: Given a proof for (and l_1 ... l_n), produces a proof for l_i

       \nicebox{
       T1: (and l_1 ... l_n)
       [and-elim T1]: l_i
       }
   - Z3_OP_PR_NOT_OR_ELIM: Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).

       \nicebox{
       T1: (not (or l_1 ... l_n))
       [not-or-elim T1]: (not l_i)
       }

   - Z3_OP_PR_REWRITE: A proof for a local rewriting step (= t s).
          The head function symbol of t is interpreted.

          This proof object has no antecedents.
          The conclusion of a rewrite rule is either an equality (= t s),
          an equivalence (iff t s), or equi-satisfiability (~ t s).
          Remark: if f is bool, then = is iff.


          Examples:
          \nicebox{
          (= (+ x 0) x)
          (= (+ x 1 2) (+ 3 x))
          (iff (or x false) x)
          }

   - Z3_OP_PR_REWRITE_STAR: A proof for rewriting an expression t into an expression s.
       This proof object can have n antecedents.
       The antecedents are proofs for equalities used as substitution rules.
       The proof rule is used in a few cases. The cases are:
         - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
         - When converting bit-vectors to Booleans (BIT2BOOL=true)

   - Z3_OP_PR_PULL_QUANT: A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.

   - Z3_OP_PR_PUSH_QUANT: A proof for:

       \nicebox{
          (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
               (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
                 ...
               (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
               }
         This proof object has no antecedents.

   - Z3_OP_PR_ELIM_UNUSED_VARS:
          A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
                           (forall (x_1 ... x_n) p[x_1 ... x_n]))

          It is used to justify the elimination of unused variables.
          This proof object has no antecedents.

   - Z3_OP_PR_DER: A proof for destructive equality resolution:
          (iff (forall (x) (or (not (= x t)) P[x])) P[t])
          if x does not occur in t.

          This proof object has no antecedents.

          Several variables can be eliminated simultaneously.

   - Z3_OP_PR_QUANT_INST: A proof of (or (not (forall (x) (P x))) (P a))

   - Z3_OP_PR_HYPOTHESIS: Mark a hypothesis in a natural deduction style proof.

   - Z3_OP_PR_LEMMA:

       \nicebox{
          T1: false
          [lemma T1]: (or (not l_1) ... (not l_n))
          }
          This proof object has one antecedent: a hypothetical proof for false.
          It converts the proof in a proof for (or (not l_1) ... (not l_n)),
          when T1 contains the open hypotheses: l_1, ..., l_n.
          The hypotheses are closed after an application of a lemma.
          Furthermore, there are no other open hypotheses in the subtree covered by
          the lemma.

   - Z3_OP_PR_UNIT_RESOLUTION:
       \nicebox{
          T1:      (or l_1 ... l_n l_1' ... l_m')
          T2:      (not l_1)
          ...
          T(n+1):  (not l_n)
          [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
          }

   - Z3_OP_PR_IFF_TRUE:
      \nicebox{
       T1: p
       [iff-true T1]: (iff p true)
       }

   - Z3_OP_PR_IFF_FALSE:
      \nicebox{
       T1: (not p)
       [iff-false T1]: (iff p false)
       }

   - Z3_OP_PR_COMMUTATIVITY:

          [comm]: (= (f a b) (f b a))

          f is a commutative operator.

          This proof object has no antecedents.
          Remark: if f is bool, then = is iff.

   - Z3_OP_PR_DEF_AXIOM: Proof object used to justify Tseitin's like axioms:

          \nicebox{
          (or (not (and p q)) p)
          (or (not (and p q)) q)
          (or (not (and p q r)) p)
          (or (not (and p q r)) q)
          (or (not (and p q r)) r)
          ...
          (or (and p q) (not p) (not q))
          (or (not (or p q)) p q)
          (or (or p q) (not p))
          (or (or p q) (not q))
          (or (not (iff p q)) (not p) q)
          (or (not (iff p q)) p (not q))
          (or (iff p q) (not p) (not q))
          (or (iff p q) p q)
          (or (not (ite a b c)) (not a) b)
          (or (not (ite a b c)) a c)
          (or (ite a b c) (not a) (not b))
          (or (ite a b c) a (not c))
          (or (not (not a)) (not a))
          (or (not a) a)
          }
          This proof object has no antecedents.
          Note: all axioms are propositional tautologies.
          Note also that 'and' and 'or' can take multiple arguments.
          You can recover the propositional tautologies by
          unfolding the Boolean connectives in the axioms a small
          bounded number of steps (=3).

   - Z3_OP_PR_ASSUMPTION_ADD
     Clausal proof adding axiom

   - Z3_OP_PR_LEMMA_ADD
     Clausal proof lemma addition

   - Z3_OP_PR_REDUNDANT_DEL
     Clausal proof lemma deletion

   - Z3_OP_PR_CLAUSE_TRAIL,
     Clausal proof trail of additions and deletions

   - Z3_OP_PR_DEF_INTRO: Introduces a name for a formula/term.
       Suppose e is an expression with free variables x, and def-intro
       introduces the name n(x). The possible cases are:

       When e is of Boolean type:
       [def-intro]: (and (or n (not e)) (or (not n) e))

       or:
       [def-intro]: (or (not n) e)
       when e only occurs positively.

       When e is of the form (ite cond th el):
       [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))

       Otherwise:
       [def-intro]: (= n e)

   - Z3_OP_PR_APPLY_DEF:
       [apply-def T1]: F ~ n
       F is 'equivalent' to n, given that T1 is a proof that
       n is a name for F.

   - Z3_OP_PR_IFF_OEQ:
       T1: (iff p q)
       [iff~ T1]: (~ p q)

   - Z3_OP_PR_NNF_POS: Proof for a (positive) NNF step. Example:
       \nicebox{
          T1: (not s_1) ~ r_1
          T2: (not s_2) ~ r_2
          T3: s_1 ~ r_1'
          T4: s_2 ~ r_2'
          [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2)
                                    (and (or r_1 r_2') (or r_1' r_2)))
          }
       The negation normal form steps NNF_POS and NNF_NEG are used in the following cases:
       (a) When creating the NNF of a positive force quantifier.
        The quantifier is retained (unless the bound variables are eliminated).
        Example
        \nicebox{
           T1: q ~ q_new
           [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
        }
       (b) When recursively creating NNF over Boolean formulas, where the top-level
       connective is changed during NNF conversion. The relevant Boolean connectives
       for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
       NNF_NEG furthermore handles the case where negation is pushed
       over Boolean connectives 'and' and 'or'.


   - Z3_OP_PR_NNF_NEG: Proof for a (negative) NNF step. Examples:
          \nicebox{
          T1: (not s_1) ~ r_1
          ...
          Tn: (not s_n) ~ r_n
         [nnf-neg T1 ... Tn]: (not (and s_1 ... s_n)) ~ (or r_1 ... r_n)
      and
          T1: (not s_1) ~ r_1
          ...
          Tn: (not s_n) ~ r_n
         [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1 ... r_n)
      and
          T1: (not s_1) ~ r_1
          T2: (not s_2) ~ r_2
          T3: s_1 ~ r_1'
          T4: s_2 ~ r_2'
         [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2))
                                   (and (or r_1 r_2) (or r_1' r_2')))
       }

   - Z3_OP_PR_SKOLEMIZE: Proof for:

          \nicebox{
          [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y)))
          [sk]: (~ (exists x (p x y)) (p (sk y) y))
          }

          This proof object has no antecedents.

   - Z3_OP_PR_MODUS_PONENS_OEQ: Modus ponens style rule for equi-satisfiability.
       \nicebox{
          T1: p
          T2: (~ p q)
          [mp~ T1 T2]: q
          }

    - Z3_OP_PR_TH_LEMMA: Generic proof for theory lemmas.

         The theory lemma function comes with one or more parameters.
         The first parameter indicates the name of the theory.
         For the theory of arithmetic, additional parameters provide hints for
         checking the theory lemma.
         The hints for arithmetic are:

         - farkas - followed by rational coefficients. Multiply the coefficients to the
           inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.

         - triangle-eq - Indicates a lemma related to the equivalence:
         \nicebox{
            (iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
         }

         - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.


    - Z3_OP_PR_HYPER_RESOLVE: Hyper-resolution rule.

        The premises of the rules is a sequence of clauses.
        The first clause argument is the main clause of the rule.
        with a literal from the first (main) clause.

        Premises of the rules are of the form
        \nicebox{
                (or l0 l1 l2 .. ln)
        }
        or
        \nicebox{
             (=> (and l1 l2 .. ln) l0)
        }
        or in the most general (ground) form:
        \nicebox{
             (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln))
        }
        In other words we use the following (Prolog style) convention for Horn
        implications:
        The head of a Horn implication is position 0,
        the first conjunct in the body of an implication is position 1
        the second conjunct in the body of an implication is position 2

        For general implications where the head is a disjunction, the
        first n positions correspond to the n disjuncts in the head.
        The next m positions correspond to the m conjuncts in the body.

        The premises can be universally quantified so that the most
        general non-ground form is:

        \nicebox{
             (forall (vars) (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln)))
        }

        The hyper-resolution rule takes a sequence of parameters.
        The parameters are substitutions of bound variables separated by pairs
        of literal positions from the main clause and side clause.


      - Z3_OP_RA_STORE: Insert a record into a relation.
        The function takes \c n+1 arguments, where the first argument is the relation and the remaining \c n elements
        correspond to the \c n columns of the relation.

      - Z3_OP_RA_EMPTY: Creates the empty relation.

      - Z3_OP_RA_IS_EMPTY: Tests if the relation is empty.

      - Z3_OP_RA_JOIN: Create the relational join.

      - Z3_OP_RA_UNION: Create the union or convex hull of two relations.
        The function takes two arguments.

      - Z3_OP_RA_WIDEN: Widen two relations.
        The function takes two arguments.

      - Z3_OP_RA_PROJECT: Project the columns (provided as numbers in the parameters).
        The function takes one argument.

      - Z3_OP_RA_FILTER: Filter (restrict) a relation with respect to a predicate.
        The first argument is a relation.
        The second argument is a predicate with free de-Bruijn indices
        corresponding to the columns of the relation.
        So the first column in the relation has index 0.

      - Z3_OP_RA_NEGATION_FILTER: Intersect the first relation with respect to negation
        of the second relation (the function takes two arguments).
        Logically, the specification can be described by a function

           target = filter_by_negation(pos, neg, columns)

        where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
        target are elements in x in pos, such that there is no y in neg that agrees with
        x on the columns c1, d1, .., cN, dN.


      - Z3_OP_RA_RENAME: rename columns in the relation.
        The function takes one argument.
        The parameters contain the renaming as a cycle.

      - Z3_OP_RA_COMPLEMENT: Complement the relation.

      - Z3_OP_RA_SELECT: Check if a record is an element of the relation.
        The function takes \c n+1 arguments, where the first argument is a relation,
        and the remaining \c n arguments correspond to a record.

      - Z3_OP_RA_CLONE: Create a fresh copy (clone) of a relation.
        The function is logically the identity, but
        in the context of a register machine allows
        for #Z3_OP_RA_UNION to perform destructive updates to the first argument.


      - Z3_OP_FD_LT: A less than predicate over the finite domain Z3_FINITE_DOMAIN_SORT.

      - Z3_OP_LABEL: A label (used by the Boogie Verification condition generator).
                     The label has two parameters, a string and a Boolean polarity.
                     It takes one argument, a formula.

      - Z3_OP_LABEL_LIT: A label literal (used by the Boogie Verification condition generator).
                     A label literal has a set of string parameters. It takes no arguments.

      - Z3_OP_DT_CONSTRUCTOR: datatype constructor.

      - Z3_OP_DT_RECOGNISER: datatype recognizer.

      - Z3_OP_DT_IS: datatype recognizer.

      - Z3_OP_DT_ACCESSOR: datatype accessor.

      - Z3_OP_DT_UPDATE_FIELD: datatype field update.

      - Z3_OP_PB_AT_MOST: Cardinality constraint.
              E.g., x + y + z <= 2

      - Z3_OP_PB_AT_LEAST: Cardinality constraint.
              E.g., x + y + z >= 2

      - Z3_OP_PB_LE: Generalized Pseudo-Boolean cardinality constraint.
              Example  2*x + 3*y <= 4

      - Z3_OP_PB_GE: Generalized Pseudo-Boolean cardinality constraint.
              Example  2*x + 3*y + 2*z >= 4

      - Z3_OP_PB_EQ: Generalized Pseudo-Boolean equality constraint.
              Example  2*x + 1*y + 2*z + 1*u = 4

       - Z3_OP_SPECIAL_RELATION_LO: A relation that is a total linear order

       - Z3_OP_SPECIAL_RELATION_PO: A relation that is a partial order

       - Z3_OP_SPECIAL_RELATION_PLO: A relation that is a piecewise linear order

       - Z3_OP_SPECIAL_RELATION_TO: A relation that is a tree order

       - Z3_OP_SPECIAL_RELATION_TC: Transitive closure of a relation

       - Z3_OP_SPECIAL_RELATION_TRC: Transitive reflexive closure of a relation

      - Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN: Floating-point rounding mode RNE

      - Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY: Floating-point rounding mode RNA

      - Z3_OP_FPA_RM_TOWARD_POSITIVE: Floating-point rounding mode RTP

      - Z3_OP_FPA_RM_TOWARD_NEGATIVE: Floating-point rounding mode RTN

      - Z3_OP_FPA_RM_TOWARD_ZERO: Floating-point rounding mode RTZ

      - Z3_OP_FPA_NUM: Floating-point value

      - Z3_OP_FPA_PLUS_INF: Floating-point +oo

      - Z3_OP_FPA_MINUS_INF: Floating-point -oo

      - Z3_OP_FPA_NAN: Floating-point NaN

      - Z3_OP_FPA_PLUS_ZERO: Floating-point +zero

      - Z3_OP_FPA_MINUS_ZERO: Floating-point -zero

      - Z3_OP_FPA_ADD: Floating-point addition

      - Z3_OP_FPA_SUB: Floating-point subtraction

      - Z3_OP_FPA_NEG: Floating-point negation

      - Z3_OP_FPA_MUL: Floating-point multiplication

      - Z3_OP_FPA_DIV: Floating-point division

      - Z3_OP_FPA_REM: Floating-point remainder

      - Z3_OP_FPA_ABS: Floating-point absolute value

      - Z3_OP_FPA_MIN: Floating-point minimum

      - Z3_OP_FPA_MAX: Floating-point maximum

      - Z3_OP_FPA_FMA: Floating-point fused multiply-add

      - Z3_OP_FPA_SQRT: Floating-point square root

      - Z3_OP_FPA_ROUND_TO_INTEGRAL: Floating-point round to integral

      - Z3_OP_FPA_EQ: Floating-point equality

      - Z3_OP_FPA_LT: Floating-point less than

      - Z3_OP_FPA_GT: Floating-point greater than

      - Z3_OP_FPA_LE: Floating-point less than or equal

      - Z3_OP_FPA_GE: Floating-point greater than or equal

      - Z3_OP_FPA_IS_NAN: Floating-point isNaN

      - Z3_OP_FPA_IS_INF: Floating-point isInfinite

      - Z3_OP_FPA_IS_ZERO: Floating-point isZero

      - Z3_OP_FPA_IS_NORMAL: Floating-point isNormal

      - Z3_OP_FPA_IS_SUBNORMAL: Floating-point isSubnormal

      - Z3_OP_FPA_IS_NEGATIVE: Floating-point isNegative

      - Z3_OP_FPA_IS_POSITIVE: Floating-point isPositive

      - Z3_OP_FPA_FP: Floating-point constructor from 3 bit-vectors

      - Z3_OP_FPA_TO_FP: Floating-point conversion (various)

      - Z3_OP_FPA_TO_FP_UNSIGNED: Floating-point conversion from unsigned bit-vector

      - Z3_OP_FPA_TO_UBV: Floating-point conversion to unsigned bit-vector

      - Z3_OP_FPA_TO_SBV: Floating-point conversion to signed bit-vector

      - Z3_OP_FPA_TO_REAL: Floating-point conversion to real number

      - Z3_OP_FPA_TO_IEEE_BV: Floating-point conversion to IEEE-754 bit-vector

      - Z3_OP_FPA_BVWRAP: (Implicitly) represents the internal bitvector-
        representation of a floating-point term (used for the lazy encoding
        of non-relevant terms in theory_fpa)

      - Z3_OP_FPA_BV2RM: Conversion of a 3-bit bit-vector term to a
        floating-point rounding-mode term

        The conversion uses the following values:
            0 = 000 = Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN,
            1 = 001 = Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
            2 = 010 = Z3_OP_FPA_RM_TOWARD_POSITIVE,
            3 = 011 = Z3_OP_FPA_RM_TOWARD_NEGATIVE,
            4 = 100 = Z3_OP_FPA_RM_TOWARD_ZERO.

      - Z3_OP_INTERNAL: internal (often interpreted) symbol, but no additional
        information is exposed. Tools may use the string representation of the
        function declaration to obtain more information.

      - Z3_OP_UNINTERPRETED: kind used for uninterpreted symbols.
*/
typedef enum {
    // Basic
    Z3_OP_TRUE = 0x100,
    Z3_OP_FALSE,
    Z3_OP_EQ,
    Z3_OP_DISTINCT,
    Z3_OP_ITE,
    Z3_OP_AND,
    Z3_OP_OR,
    Z3_OP_IFF,
    Z3_OP_XOR,
    Z3_OP_NOT,
    Z3_OP_IMPLIES,
    Z3_OP_OEQ,

    // Arithmetic
    Z3_OP_ANUM = 0x200,
    Z3_OP_AGNUM,
    Z3_OP_LE,
    Z3_OP_GE,
    Z3_OP_LT,
    Z3_OP_GT,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_UMINUS,
    Z3_OP_MUL,
    Z3_OP_DIV,
    Z3_OP_IDIV,
    Z3_OP_REM,
    Z3_OP_MOD,
    Z3_OP_TO_REAL,
    Z3_OP_TO_INT,
    Z3_OP_IS_INT,
    Z3_OP_POWER,

    // Arrays & Sets
    Z3_OP_STORE = 0x300,
    Z3_OP_SELECT,
    Z3_OP_CONST_ARRAY,
    Z3_OP_ARRAY_MAP,
    Z3_OP_ARRAY_DEFAULT,
    Z3_OP_SET_UNION,
    Z3_OP_SET_INTERSECT,
    Z3_OP_SET_DIFFERENCE,
    Z3_OP_SET_COMPLEMENT,
    Z3_OP_SET_SUBSET,
    Z3_OP_AS_ARRAY,
    Z3_OP_ARRAY_EXT,

    // Bit-vectors
    Z3_OP_BNUM = 0x400,
    Z3_OP_BIT1,
    Z3_OP_BIT0,
    Z3_OP_BNEG,
    Z3_OP_BADD,
    Z3_OP_BSUB,
    Z3_OP_BMUL,

    Z3_OP_BSDIV,
    Z3_OP_BUDIV,
    Z3_OP_BSREM,
    Z3_OP_BUREM,
    Z3_OP_BSMOD,

    // special functions to record the division by 0 cases
    // these are internal functions
    Z3_OP_BSDIV0,
    Z3_OP_BUDIV0,
    Z3_OP_BSREM0,
    Z3_OP_BUREM0,
    Z3_OP_BSMOD0,

    Z3_OP_ULEQ,
    Z3_OP_SLEQ,
    Z3_OP_UGEQ,
    Z3_OP_SGEQ,
    Z3_OP_ULT,
    Z3_OP_SLT,
    Z3_OP_UGT,
    Z3_OP_SGT,

    Z3_OP_BAND,
    Z3_OP_BOR,
    Z3_OP_BNOT,
    Z3_OP_BXOR,
    Z3_OP_BNAND,
    Z3_OP_BNOR,
    Z3_OP_BXNOR,

    Z3_OP_CONCAT,
    Z3_OP_SIGN_EXT,
    Z3_OP_ZERO_EXT,
    Z3_OP_EXTRACT,
    Z3_OP_REPEAT,

    Z3_OP_BREDOR,
    Z3_OP_BREDAND,
    Z3_OP_BCOMP,

    Z3_OP_BSHL,
    Z3_OP_BLSHR,
    Z3_OP_BASHR,
    Z3_OP_ROTATE_LEFT,
    Z3_OP_ROTATE_RIGHT,
    Z3_OP_EXT_ROTATE_LEFT,
    Z3_OP_EXT_ROTATE_RIGHT,

    Z3_OP_BIT2BOOL,
    Z3_OP_INT2BV,
    Z3_OP_BV2INT,
    Z3_OP_CARRY,
    Z3_OP_XOR3,

    Z3_OP_BSMUL_NO_OVFL,
    Z3_OP_BUMUL_NO_OVFL,
    Z3_OP_BSMUL_NO_UDFL,
    Z3_OP_BSDIV_I,
    Z3_OP_BUDIV_I,
    Z3_OP_BSREM_I,
    Z3_OP_BUREM_I,
    Z3_OP_BSMOD_I,

    // Proofs
    Z3_OP_PR_UNDEF = 0x500,
    Z3_OP_PR_TRUE,
    Z3_OP_PR_ASSERTED,
    Z3_OP_PR_GOAL,
    Z3_OP_PR_MODUS_PONENS,
    Z3_OP_PR_REFLEXIVITY,
    Z3_OP_PR_SYMMETRY,
    Z3_OP_PR_TRANSITIVITY,
    Z3_OP_PR_TRANSITIVITY_STAR,
    Z3_OP_PR_MONOTONICITY,
    Z3_OP_PR_QUANT_INTRO,
    Z3_OP_PR_BIND,
    Z3_OP_PR_DISTRIBUTIVITY,
    Z3_OP_PR_AND_ELIM,
    Z3_OP_PR_NOT_OR_ELIM,
    Z3_OP_PR_REWRITE,
    Z3_OP_PR_REWRITE_STAR,
    Z3_OP_PR_PULL_QUANT,
    Z3_OP_PR_PUSH_QUANT,
    Z3_OP_PR_ELIM_UNUSED_VARS,
    Z3_OP_PR_DER,
    Z3_OP_PR_QUANT_INST,
    Z3_OP_PR_HYPOTHESIS,
    Z3_OP_PR_LEMMA,
    Z3_OP_PR_UNIT_RESOLUTION,
    Z3_OP_PR_IFF_TRUE,
    Z3_OP_PR_IFF_FALSE,
    Z3_OP_PR_COMMUTATIVITY,
    Z3_OP_PR_DEF_AXIOM,
    Z3_OP_PR_ASSUMPTION_ADD, 
    Z3_OP_PR_LEMMA_ADD, 
    Z3_OP_PR_REDUNDANT_DEL, 
    Z3_OP_PR_CLAUSE_TRAIL,
    Z3_OP_PR_DEF_INTRO,
    Z3_OP_PR_APPLY_DEF,
    Z3_OP_PR_IFF_OEQ,
    Z3_OP_PR_NNF_POS,
    Z3_OP_PR_NNF_NEG,
    Z3_OP_PR_SKOLEMIZE,
    Z3_OP_PR_MODUS_PONENS_OEQ,
    Z3_OP_PR_TH_LEMMA,
    Z3_OP_PR_HYPER_RESOLVE,

    // Relational algebra
    Z3_OP_RA_STORE = 0x600,
    Z3_OP_RA_EMPTY,
    Z3_OP_RA_IS_EMPTY,
    Z3_OP_RA_JOIN,
    Z3_OP_RA_UNION,
    Z3_OP_RA_WIDEN,
    Z3_OP_RA_PROJECT,
    Z3_OP_RA_FILTER,
    Z3_OP_RA_NEGATION_FILTER,
    Z3_OP_RA_RENAME,
    Z3_OP_RA_COMPLEMENT,
    Z3_OP_RA_SELECT,
    Z3_OP_RA_CLONE,
    Z3_OP_FD_CONSTANT,
    Z3_OP_FD_LT,

    // Sequences
    Z3_OP_SEQ_UNIT,
    Z3_OP_SEQ_EMPTY,
    Z3_OP_SEQ_CONCAT,
    Z3_OP_SEQ_PREFIX,
    Z3_OP_SEQ_SUFFIX,
    Z3_OP_SEQ_CONTAINS,
    Z3_OP_SEQ_EXTRACT,
    Z3_OP_SEQ_REPLACE,
    Z3_OP_SEQ_AT,
    Z3_OP_SEQ_NTH,
    Z3_OP_SEQ_LENGTH,
    Z3_OP_SEQ_INDEX,
    Z3_OP_SEQ_LAST_INDEX,
    Z3_OP_SEQ_TO_RE,
    Z3_OP_SEQ_IN_RE,

    // strings
    Z3_OP_STR_TO_INT,
    Z3_OP_INT_TO_STR,

    // regular expressions
    Z3_OP_RE_PLUS,
    Z3_OP_RE_STAR,
    Z3_OP_RE_OPTION,
    Z3_OP_RE_CONCAT,
    Z3_OP_RE_UNION,
    Z3_OP_RE_RANGE,
    Z3_OP_RE_LOOP,
    Z3_OP_RE_INTERSECT,
    Z3_OP_RE_EMPTY_SET,
    Z3_OP_RE_FULL_SET,
    Z3_OP_RE_COMPLEMENT,

    // Auxiliary
    Z3_OP_LABEL = 0x700,
    Z3_OP_LABEL_LIT,

    // Datatypes
    Z3_OP_DT_CONSTRUCTOR=0x800,
    Z3_OP_DT_RECOGNISER,
    Z3_OP_DT_IS,
    Z3_OP_DT_ACCESSOR,
    Z3_OP_DT_UPDATE_FIELD,

    // Pseudo Booleans
    Z3_OP_PB_AT_MOST=0x900,
    Z3_OP_PB_AT_LEAST,
    Z3_OP_PB_LE,
    Z3_OP_PB_GE,
    Z3_OP_PB_EQ,

    // Special relations
    Z3_OP_SPECIAL_RELATION_LO = 0xa000,
    Z3_OP_SPECIAL_RELATION_PO,
    Z3_OP_SPECIAL_RELATION_PLO,
    Z3_OP_SPECIAL_RELATION_TO,
    Z3_OP_SPECIAL_RELATION_TC,
    Z3_OP_SPECIAL_RELATION_TRC,


    // Floating-Point Arithmetic
    Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN = 0xb000,
    Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
    Z3_OP_FPA_RM_TOWARD_POSITIVE,
    Z3_OP_FPA_RM_TOWARD_NEGATIVE,
    Z3_OP_FPA_RM_TOWARD_ZERO,

    Z3_OP_FPA_NUM,
    Z3_OP_FPA_PLUS_INF,
    Z3_OP_FPA_MINUS_INF,
    Z3_OP_FPA_NAN,
    Z3_OP_FPA_PLUS_ZERO,
    Z3_OP_FPA_MINUS_ZERO,

    Z3_OP_FPA_ADD,
    Z3_OP_FPA_SUB,
    Z3_OP_FPA_NEG,
    Z3_OP_FPA_MUL,
    Z3_OP_FPA_DIV,
    Z3_OP_FPA_REM,
    Z3_OP_FPA_ABS,
    Z3_OP_FPA_MIN,
    Z3_OP_FPA_MAX,
    Z3_OP_FPA_FMA,
    Z3_OP_FPA_SQRT,
    Z3_OP_FPA_ROUND_TO_INTEGRAL,

    Z3_OP_FPA_EQ,
    Z3_OP_FPA_LT,
    Z3_OP_FPA_GT,
    Z3_OP_FPA_LE,
    Z3_OP_FPA_GE,
    Z3_OP_FPA_IS_NAN,
    Z3_OP_FPA_IS_INF,
    Z3_OP_FPA_IS_ZERO,
    Z3_OP_FPA_IS_NORMAL,
    Z3_OP_FPA_IS_SUBNORMAL,
    Z3_OP_FPA_IS_NEGATIVE,
    Z3_OP_FPA_IS_POSITIVE,

    Z3_OP_FPA_FP,
    Z3_OP_FPA_TO_FP,
    Z3_OP_FPA_TO_FP_UNSIGNED,
    Z3_OP_FPA_TO_UBV,
    Z3_OP_FPA_TO_SBV,
    Z3_OP_FPA_TO_REAL,

    Z3_OP_FPA_TO_IEEE_BV,

    Z3_OP_FPA_BVWRAP,
    Z3_OP_FPA_BV2RM,

    Z3_OP_INTERNAL,

    Z3_OP_UNINTERPRETED
} Z3_decl_kind;

/**
   \brief The different kinds of parameters that can be associated with parameter sets.
   (see #Z3_mk_params).

    - Z3_PK_UINT integer parameters.
    - Z3_PK_BOOL boolean parameters.
    - Z3_PK_DOUBLE double parameters.
    - Z3_PK_SYMBOL symbol parameters.
    - Z3_PK_STRING string parameters.
    - Z3_PK_OTHER all internal parameter kinds which are not exposed in the API.
    - Z3_PK_INVALID invalid parameter.
*/
typedef enum {
    Z3_PK_UINT,
    Z3_PK_BOOL,
    Z3_PK_DOUBLE,
    Z3_PK_SYMBOL,
    Z3_PK_STRING,
    Z3_PK_OTHER,
    Z3_PK_INVALID
} Z3_param_kind;

/**
    \brief Z3 pretty printing modes (See #Z3_set_ast_print_mode).

   - Z3_PRINT_SMTLIB_FULL:   Print AST nodes in SMTLIB verbose format.
   - Z3_PRINT_LOW_LEVEL:     Print AST nodes using a low-level format.
   - Z3_PRINT_SMTLIB2_COMPLIANT: Print AST nodes in SMTLIB 2.x compliant format.
*/
typedef enum {
    Z3_PRINT_SMTLIB_FULL,
    Z3_PRINT_LOW_LEVEL,
    Z3_PRINT_SMTLIB2_COMPLIANT
} Z3_ast_print_mode;


/**
   \brief Z3 error codes (See #Z3_get_error_code).

   - Z3_OK:            No error.
   - Z3_SORT_ERROR:    User tried to build an invalid (type incorrect) AST.
   - Z3_IOB:           Index out of bounds.
   - Z3_INVALID_ARG:   Invalid argument was provided.
   - Z3_PARSER_ERROR:  An error occurred when parsing a string or file.
   - Z3_NO_PARSER:     Parser output is not available, that is, user didn't invoke #Z3_parse_smtlib2_string or #Z3_parse_smtlib2_file.
   - Z3_INVALID_PATTERN: Invalid pattern was used to build a quantifier.
   - Z3_MEMOUT_FAIL:   A memory allocation failure was encountered.
   - Z3_FILE_ACCESS_ERRROR: A file could not be accessed.
   - Z3_INVALID_USAGE:   API call is invalid in the current state.
   - Z3_INTERNAL_FATAL: An error internal to Z3 occurred.
   - Z3_DEC_REF_ERROR: Trying to decrement the reference counter of an AST that was deleted or the reference counter was not initialized with #Z3_inc_ref.
   - Z3_EXCEPTION:     Internal Z3 exception. Additional details can be retrieved using #Z3_get_error_msg.
*/
typedef enum
{
    Z3_OK,
    Z3_SORT_ERROR,
    Z3_IOB,
    Z3_INVALID_ARG,
    Z3_PARSER_ERROR,
    Z3_NO_PARSER,
    Z3_INVALID_PATTERN,
    Z3_MEMOUT_FAIL,
    Z3_FILE_ACCESS_ERROR,
    Z3_INTERNAL_FATAL,
    Z3_INVALID_USAGE,
    Z3_DEC_REF_ERROR,
    Z3_EXCEPTION
} Z3_error_code;

/**
  Definitions for update_api.py

  def_Type('CONFIG',           'Z3_config',           'Config')
  def_Type('CONTEXT',          'Z3_context',          'ContextObj')
  def_Type('AST',              'Z3_ast',              'Ast')
  def_Type('APP',              'Z3_app',              'Ast')
  def_Type('SORT',             'Z3_sort',             'Sort')
  def_Type('FUNC_DECL',        'Z3_func_decl',        'FuncDecl')
  def_Type('PATTERN',          'Z3_pattern',          'Pattern')
  def_Type('MODEL',            'Z3_model',            'Model')
  def_Type('LITERALS',         'Z3_literals',         'Literals')
  def_Type('CONSTRUCTOR',      'Z3_constructor',      'Constructor')
  def_Type('CONSTRUCTOR_LIST', 'Z3_constructor_list', 'ConstructorList')
  def_Type('SOLVER',           'Z3_solver',           'SolverObj')
  def_Type('GOAL',             'Z3_goal',             'GoalObj')
  def_Type('TACTIC',           'Z3_tactic',           'TacticObj')
  def_Type('PARAMS',           'Z3_params',           'Params')
  def_Type('PROBE',            'Z3_probe',            'ProbeObj')
  def_Type('STATS',            'Z3_stats',            'StatsObj')
  def_Type('AST_VECTOR',       'Z3_ast_vector',       'AstVectorObj')
  def_Type('AST_MAP',          'Z3_ast_map',          'AstMapObj')
  def_Type('APPLY_RESULT',     'Z3_apply_result',     'ApplyResultObj')
  def_Type('FUNC_INTERP',      'Z3_func_interp',      'FuncInterpObj')
  def_Type('FUNC_ENTRY',       'Z3_func_entry',       'FuncEntryObj')
  def_Type('FIXEDPOINT',       'Z3_fixedpoint',       'FixedpointObj')
  def_Type('OPTIMIZE',         'Z3_optimize',         'OptimizeObj')
  def_Type('PARAM_DESCRS',     'Z3_param_descrs',     'ParamDescrs')
  def_Type('RCF_NUM',          'Z3_rcf_num',          'RCFNumObj')
*/

/**
   \brief Z3 custom error handler (See #Z3_set_error_handler).
*/
typedef void Z3_error_handler(Z3_context c, Z3_error_code e);

/**
   \brief A Goal is essentially a set of formulas.
   Z3 provide APIs for building strategies/tactics for solving and transforming Goals.
   Some of these transformations apply under/over approximations.

   - Z3_GOAL_PRECISE:    Approximations/Relaxations were not applied on the goal (sat and unsat answers were preserved).
   - Z3_GOAL_UNDER:      Goal is the product of a under-approximation (sat answers are preserved).
   - Z3_GOAL_OVER:       Goal is the product of an over-approximation (unsat answers are preserved).
   - Z3_GOAL_UNDER_OVER: Goal is garbage (it is the product of over- and under-approximations, sat and unsat answers are not preserved).
*/
typedef enum
{
    Z3_GOAL_PRECISE,
    Z3_GOAL_UNDER,
    Z3_GOAL_OVER,
    Z3_GOAL_UNDER_OVER
} Z3_goal_prec;

/*@}*/

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** @name Global Parameters */

    /*@{*/
    /**
       \brief Set a global (or module) parameter.
       This setting is shared by all Z3 contexts.

       When a Z3 module is initialized it will use the value of these parameters
       when Z3_params objects are not provided.

       The name of parameter can be composed of characters [a-z][A-Z], digits [0-9], '-' and '_'.
       The character '.' is a delimiter (more later).

       The parameter names are case-insensitive. The character '-' should be viewed as an "alias" for '_'.
       Thus, the following parameter names are considered equivalent: "pp.decimal-precision"  and "PP.DECIMAL_PRECISION".

       This function can be used to set parameters for a specific Z3 module.
       This can be done by using <module-name>.<parameter-name>.
       For example:
       Z3_global_param_set('pp.decimal', 'true')
       will set the parameter "decimal" in the module "pp" to true.

       def_API('Z3_global_param_set', VOID, (_in(STRING), _in(STRING)))
    */
    void Z3_API Z3_global_param_set(Z3_string param_id, Z3_string param_value);


    /**
       \brief Restore the value of all global (and module) parameters.
       This command will not affect already created objects (such as tactics and solvers).

       \sa Z3_global_param_set

       def_API('Z3_global_param_reset_all', VOID, ())
    */
    void Z3_API Z3_global_param_reset_all(void);

    /**
       \brief Get a global (or module) parameter.

       Returns \c false if the parameter value does not exist.

       \sa Z3_global_param_set

       \remark This function cannot be invoked simultaneously from different threads without synchronization.
       The result string stored in param_value is stored in shared location.

       def_API('Z3_global_param_get', BOOL, (_in(STRING), _out(STRING)))
    */
    Z3_bool_opt Z3_API Z3_global_param_get(Z3_string param_id, Z3_string_ptr param_value);

    /*@}*/

    /** @name Create configuration */
    /*@{*/

    /**
        \brief Create a configuration object for the Z3 context object.

        Configurations are created in order to assign parameters prior to creating
        contexts for Z3 interaction. For example, if the users wishes to use proof
        generation, then call:

        \ccode{Z3_set_param_value(cfg\, "proof"\, "true")}

        \remark In previous versions of Z3, the \c Z3_config was used to store
        global and module configurations. Now, we should use \c Z3_global_param_set.

        The following parameters can be set:

            - proof  (Boolean)           Enable proof generation
            - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting
            - trace  (Boolean)           Tracing support for VCC
            - trace_file_name (String)   Trace out file for VCC traces
            - timeout (unsigned)         default timeout (in milliseconds) used for solvers
            - well_sorted_check          type checker
            - auto_config                use heuristics to automatically select solver and configure it
            - model                      model generation for solvers, this parameter can be overwritten when creating a solver
            - model_validate             validate models produced by solvers
            - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver

        \sa Z3_set_param_value
        \sa Z3_del_config

        def_API('Z3_mk_config', CONFIG, ())
    */
    Z3_config Z3_API Z3_mk_config(void);

    /**
        \brief Delete the given configuration object.

        \sa Z3_mk_config

        def_API('Z3_del_config', VOID, (_in(CONFIG),))
    */
    void Z3_API Z3_del_config(Z3_config c);

    /**
        \brief Set a configuration parameter.

        The following parameters can be set for

        \sa Z3_mk_config

        def_API('Z3_set_param_value', VOID, (_in(CONFIG), _in(STRING), _in(STRING)))
    */
    void Z3_API Z3_set_param_value(Z3_config c, Z3_string param_id, Z3_string param_value);

    /*@}*/

    /** @name Context and AST Reference Counting */
    /*@{*/

    /**
       \brief Create a context using the given configuration.

       After a context is created, the configuration cannot be changed,
       although some parameters can be changed using #Z3_update_param_value.
       All main interaction with Z3 happens in the context of a \c Z3_context.

       In contrast to #Z3_mk_context_rc, the life time of \c Z3_ast objects
       are determined by the scope level of #Z3_solver_push and #Z3_solver_pop.
       In other words, a \c Z3_ast object remains valid until there is a
       call to #Z3_solver_pop that takes the current scope below the level where
       the object was created.

       Note that all other reference counted objects, including \c Z3_model,
       \c Z3_solver, \c Z3_func_interp have to be managed by the caller.
       Their reference counts are not handled by the context.

       Further remarks:
       - \c Z3_sort, \c Z3_func_decl, \c Z3_app, \c Z3_pattern are \c Z3_ast's.
       - Z3 uses hash-consing, i.e., when the same \c Z3_ast is created twice,
         Z3 will return the same pointer twice.

       \sa Z3_del_context

       def_API('Z3_mk_context', CONTEXT, (_in(CONFIG),))
    */
    Z3_context Z3_API Z3_mk_context(Z3_config c);

    /**
       \brief Create a context using the given configuration.
       This function is similar to #Z3_mk_context. However,
       in the context returned by this function, the user
       is responsible for managing \c Z3_ast reference counters.
       Managing reference counters is a burden and error-prone,
       but allows the user to use the memory more efficiently.
       The user must invoke #Z3_inc_ref for any \c Z3_ast returned
       by Z3, and #Z3_dec_ref whenever the \c Z3_ast is not needed
       anymore. This idiom is similar to the one used in
       BDD (binary decision diagrams) packages such as CUDD.

       Remarks:

       - \c Z3_sort, \c Z3_func_decl, \c Z3_app, \c Z3_pattern are \c Z3_ast's.
       - After a context is created, the configuration cannot be changed.
       - All main interaction with Z3 happens in the context of a \c Z3_context.
       - Z3 uses hash-consing, i.e., when the same \c Z3_ast is created twice,
         Z3 will return the same pointer twice.

       def_API('Z3_mk_context_rc', CONTEXT, (_in(CONFIG),))
    */
    Z3_context Z3_API Z3_mk_context_rc(Z3_config c);

    /**
       \brief Delete the given logical context.

       \sa Z3_mk_context

       def_API('Z3_del_context', VOID, (_in(CONTEXT),))
    */
    void Z3_API Z3_del_context(Z3_context c);

    /**
       \brief Increment the reference counter of the given AST.
       The context \c c should have been created using #Z3_mk_context_rc.
       This function is a NOOP if \c c was created using #Z3_mk_context.

       def_API('Z3_inc_ref', VOID, (_in(CONTEXT), _in(AST)))
    */
    void Z3_API Z3_inc_ref(Z3_context c, Z3_ast a);

    /**
       \brief Decrement the reference counter of the given AST.
       The context \c c should have been created using #Z3_mk_context_rc.
       This function is a NOOP if \c c was created using #Z3_mk_context.

       def_API('Z3_dec_ref', VOID, (_in(CONTEXT), _in(AST)))
    */
    void Z3_API Z3_dec_ref(Z3_context c, Z3_ast a);

    /**
       \brief Set a value of a context parameter.

       \sa Z3_global_param_set

       def_API('Z3_update_param_value', VOID, (_in(CONTEXT), _in(STRING), _in(STRING)))
    */
    void Z3_API Z3_update_param_value(Z3_context c, Z3_string param_id, Z3_string param_value);

    /**
       \brief Interrupt the execution of a Z3 procedure.
       This procedure can be used to interrupt: solvers, simplifiers and tactics.

       def_API('Z3_interrupt', VOID, (_in(CONTEXT),))
    */
    void Z3_API Z3_interrupt(Z3_context c);


    /*@}*/

    /** @name Parameters */
    /*@{*/

    /**
       \brief Create a Z3 (empty) parameter set.
       Starting at Z3 4.0, parameter sets are used to configure many components such as:
       simplifiers, tactics, solvers, etc.

       \remark Reference counting must be used to manage parameter sets, even when the \c Z3_context was
       created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_params', PARAMS, (_in(CONTEXT),))
    */
    Z3_params Z3_API Z3_mk_params(Z3_context c);

    /**
       \brief Increment the reference counter of the given parameter set.

       def_API('Z3_params_inc_ref', VOID, (_in(CONTEXT), _in(PARAMS)))
    */
    void Z3_API Z3_params_inc_ref(Z3_context c, Z3_params p);

    /**
       \brief Decrement the reference counter of the given parameter set.

       def_API('Z3_params_dec_ref', VOID, (_in(CONTEXT), _in(PARAMS)))
    */
    void Z3_API Z3_params_dec_ref(Z3_context c, Z3_params p);

    /**
       \brief Add a Boolean parameter \c k with value \c v to the parameter set \c p.

       def_API('Z3_params_set_bool', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(BOOL)))
    */
    void Z3_API Z3_params_set_bool(Z3_context c, Z3_params p, Z3_symbol k, bool v);

    /**
       \brief Add a unsigned parameter \c k with value \c v to the parameter set \c p.

       def_API('Z3_params_set_uint', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(UINT)))
    */
    void Z3_API Z3_params_set_uint(Z3_context c, Z3_params p, Z3_symbol k, unsigned v);

    /**
       \brief Add a double parameter \c k with value \c v to the parameter set \c p.

       def_API('Z3_params_set_double', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(DOUBLE)))
    */
    void Z3_API Z3_params_set_double(Z3_context c, Z3_params p, Z3_symbol k, double v);

    /**
       \brief Add a symbol parameter \c k with value \c v to the parameter set \c p.

       def_API('Z3_params_set_symbol', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(SYMBOL)))
    */
    void Z3_API Z3_params_set_symbol(Z3_context c, Z3_params p, Z3_symbol k, Z3_symbol v);

    /**
       \brief Convert a parameter set into a string. This function is mainly used for printing the
       contents of a parameter set.

       def_API('Z3_params_to_string', STRING, (_in(CONTEXT), _in(PARAMS)))
    */
    Z3_string Z3_API Z3_params_to_string(Z3_context c, Z3_params p);

    /**
       \brief Validate the parameter set \c p against the parameter description set \c d.

       The procedure invokes the error handler if \c p is invalid.

       def_API('Z3_params_validate', VOID, (_in(CONTEXT), _in(PARAMS), _in(PARAM_DESCRS)))
    */
    void Z3_API Z3_params_validate(Z3_context c, Z3_params p, Z3_param_descrs d);

    /*@}*/

    /** @name Parameter Descriptions */
    /*@{*/

    /**
       \brief Increment the reference counter of the given parameter description set.

       def_API('Z3_param_descrs_inc_ref', VOID, (_in(CONTEXT), _in(PARAM_DESCRS)))
    */
    void Z3_API Z3_param_descrs_inc_ref(Z3_context c, Z3_param_descrs p);

    /**
       \brief Decrement the reference counter of the given parameter description set.

       def_API('Z3_param_descrs_dec_ref', VOID, (_in(CONTEXT), _in(PARAM_DESCRS)))
    */
    void Z3_API Z3_param_descrs_dec_ref(Z3_context c, Z3_param_descrs p);

    /**
       \brief Return the kind associated with the given parameter name \c n.

       def_API('Z3_param_descrs_get_kind', UINT, (_in(CONTEXT), _in(PARAM_DESCRS), _in(SYMBOL)))
    */
    Z3_param_kind Z3_API Z3_param_descrs_get_kind(Z3_context c, Z3_param_descrs p, Z3_symbol n);

    /**
       \brief Return the number of parameters in the given parameter description set.

       def_API('Z3_param_descrs_size', UINT, (_in(CONTEXT), _in(PARAM_DESCRS)))
    */
    unsigned Z3_API Z3_param_descrs_size(Z3_context c, Z3_param_descrs p);

    /**
       \brief Return the name of the parameter at given index \c i.

       \pre i < Z3_param_descrs_size(c, p)

       def_API('Z3_param_descrs_get_name', SYMBOL, (_in(CONTEXT), _in(PARAM_DESCRS), _in(UINT)))
    */
    Z3_symbol Z3_API Z3_param_descrs_get_name(Z3_context c, Z3_param_descrs p, unsigned i);

    /**
       \brief Retrieve documentation string corresponding to parameter name \c s.

       def_API('Z3_param_descrs_get_documentation', STRING, (_in(CONTEXT), _in(PARAM_DESCRS), _in(SYMBOL)))
     */
    Z3_string Z3_API Z3_param_descrs_get_documentation(Z3_context c, Z3_param_descrs p, Z3_symbol s);

    /**
       \brief Convert a parameter description set into a string. This function is mainly used for printing the
       contents of a parameter description set.

       def_API('Z3_param_descrs_to_string', STRING, (_in(CONTEXT), _in(PARAM_DESCRS)))
    */
    Z3_string Z3_API Z3_param_descrs_to_string(Z3_context c, Z3_param_descrs p);

    /*@}*/

    /** @name Symbols */
    /*@{*/

    /**
       \brief Create a Z3 symbol using an integer.

       Symbols are used to name several term and type constructors.

       NB. Not all integers can be passed to this function.
       The legal range of unsigned integers is 0 to 2^30-1.

       \sa Z3_get_symbol_int
       \sa Z3_mk_string_symbol

       def_API('Z3_mk_int_symbol', SYMBOL, (_in(CONTEXT), _in(INT)))
    */
    Z3_symbol Z3_API Z3_mk_int_symbol(Z3_context c, int i);

    /**
       \brief Create a Z3 symbol using a C string.

       Symbols are used to name several term and type constructors.

       \sa Z3_get_symbol_string
       \sa Z3_mk_int_symbol

       def_API('Z3_mk_string_symbol', SYMBOL, (_in(CONTEXT), _in(STRING)))
    */
    Z3_symbol Z3_API Z3_mk_string_symbol(Z3_context c, Z3_string s);

    /*@}*/

    /** @name Sorts */
    /*@{*/

    /**
       \brief Create a free (uninterpreted) type using the given name (symbol).

       Two free types are considered the same iff the have the same name.

       def_API('Z3_mk_uninterpreted_sort', SORT, (_in(CONTEXT), _in(SYMBOL)))
    */
    Z3_sort Z3_API Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol s);

    /**
       \brief Create the Boolean type.

       This type is used to create propositional variables and predicates.

       def_API('Z3_mk_bool_sort', SORT, (_in(CONTEXT), ))
    */
    Z3_sort Z3_API Z3_mk_bool_sort(Z3_context c);

    /**
       \brief Create the integer type.

       This type is not the int type found in programming languages.
       A machine integer can be represented using bit-vectors. The function
       #Z3_mk_bv_sort creates a bit-vector type.

       \sa Z3_mk_bv_sort

       def_API('Z3_mk_int_sort', SORT, (_in(CONTEXT), ))
    */
    Z3_sort Z3_API Z3_mk_int_sort(Z3_context c);

    /**
       \brief Create the real type.

       Note that this type is not a floating point number.

       def_API('Z3_mk_real_sort', SORT, (_in(CONTEXT), ))
    */
    Z3_sort Z3_API Z3_mk_real_sort(Z3_context c);

    /**
       \brief Create a bit-vector type of the given size.

       This type can also be seen as a machine integer.

       \remark The size of the bit-vector type must be greater than zero.

       def_API('Z3_mk_bv_sort', SORT, (_in(CONTEXT), _in(UINT)))
    */
    Z3_sort Z3_API Z3_mk_bv_sort(Z3_context c, unsigned sz);

    /**
       \brief Create a named finite domain sort.

       To create constants that belong to the finite domain,
       use the APIs for creating numerals and pass a numeric
       constant together with the sort returned by this call.
       The numeric constant should be between 0 and the less
       than the size of the domain.

       \sa Z3_get_finite_domain_sort_size

       def_API('Z3_mk_finite_domain_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT64)))
    */
    Z3_sort Z3_API Z3_mk_finite_domain_sort(Z3_context c, Z3_symbol name, uint64_t size);

    /**
       \brief Create an array type.

       We usually represent the array type as: \ccode{[domain -> range]}.
       Arrays are usually used to model the heap/memory in software verification.

       \sa Z3_mk_select
       \sa Z3_mk_store

       def_API('Z3_mk_array_sort', SORT, (_in(CONTEXT), _in(SORT), _in(SORT)))
    */
    Z3_sort Z3_API Z3_mk_array_sort(Z3_context c, Z3_sort domain, Z3_sort range);

    /**
       \brief Create an array type with N arguments

       \sa Z3_mk_select_n
       \sa Z3_mk_store_n

       def_API('Z3_mk_array_sort_n', SORT, (_in(CONTEXT), _in(UINT), _in_array(1, SORT), _in(SORT)))
    */
    Z3_sort Z3_API Z3_mk_array_sort_n(Z3_context c, unsigned n, Z3_sort const * domain, Z3_sort range);

    /**
       \brief Create a tuple type.

       A tuple with \c n fields has a constructor and \c n projections.
       This function will also declare the constructor and projection functions.

       \param c logical context
       \param mk_tuple_name name of the constructor function associated with the tuple type.
       \param num_fields number of fields in the tuple type.
       \param field_names name of the projection functions.
       \param field_sorts type of the tuple fields.
       \param mk_tuple_decl output parameter that will contain the constructor declaration.
       \param proj_decl output parameter that will contain the projection function declarations. This field must be a buffer of size \c num_fields allocated by the user.

       def_API('Z3_mk_tuple_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT), _out(FUNC_DECL), _out_array(2, FUNC_DECL)))
    */
    Z3_sort Z3_API Z3_mk_tuple_sort(Z3_context c,
                                        Z3_symbol mk_tuple_name,
                                        unsigned num_fields,
                                        Z3_symbol const field_names[],
                                        Z3_sort const field_sorts[],
                                        Z3_func_decl * mk_tuple_decl,
                                        Z3_func_decl proj_decl[]);

    /**
       \brief Create a enumeration sort.

       An enumeration sort with \c n elements.
       This function will also declare the functions corresponding to the enumerations.

       \param c logical context
       \param name name of the enumeration sort.
       \param n number of elements in enumeration sort.
       \param enum_names names of the enumerated elements.
       \param enum_consts constants corresponding to the enumerated elements.
       \param enum_testers predicates testing if terms of the enumeration sort correspond to an enumeration.

       For example, if this function is called with three symbols A, B, C and the name S, then
       \c s is a sort whose name is S, and the function returns three terms corresponding to A, B, C in
       \c enum_consts. The array \c enum_testers has three predicates of type \ccode{(s -> Bool)}.
       The first predicate (corresponding to A) is true when applied to A, and false otherwise.
       Similarly for the other predicates.

       def_API('Z3_mk_enumeration_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _in_array(2, SYMBOL), _out_array(2, FUNC_DECL), _out_array(2, FUNC_DECL)))
    */
    Z3_sort Z3_API Z3_mk_enumeration_sort(Z3_context c,
                                          Z3_symbol name,
                                          unsigned n,
                                          Z3_symbol  const enum_names[],
                                          Z3_func_decl enum_consts[],
                                          Z3_func_decl enum_testers[]);

    /**
       \brief Create a list sort

       A list sort over \c elem_sort
       This function declares the corresponding constructors and testers for lists.

       \param c logical context
       \param name name of the list sort.
       \param elem_sort sort of list elements.
       \param nil_decl declaration for the empty list.
       \param is_nil_decl test for the empty list.
       \param cons_decl declaration for a cons cell.
       \param is_cons_decl cons cell test.
       \param head_decl list head.
       \param tail_decl list tail.

       def_API('Z3_mk_list_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(SORT), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL)))
    */
    Z3_sort Z3_API Z3_mk_list_sort(Z3_context c,
                                   Z3_symbol name,
                                   Z3_sort   elem_sort,
                                   Z3_func_decl* nil_decl,
                                   Z3_func_decl* is_nil_decl,
                                   Z3_func_decl* cons_decl,
                                   Z3_func_decl* is_cons_decl,
                                   Z3_func_decl* head_decl,
                                   Z3_func_decl* tail_decl
                                   );

    /**
       \brief Create a constructor.

       \param c logical context.
       \param name constructor name.
       \param recognizer name of recognizer function.
       \param num_fields number of fields in constructor.
       \param field_names names of the constructor fields.
       \param sorts field sorts, 0 if the field sort refers to a recursive sort.
       \param sort_refs reference to datatype sort that is an argument to the constructor; if the corresponding
                        sort reference is 0, then the value in sort_refs should be an index referring to
                        one of the recursive datatypes that is declared.

       def_API('Z3_mk_constructor', CONSTRUCTOR, (_in(CONTEXT), _in(SYMBOL), _in(SYMBOL), _in(UINT), _in_array(3, SYMBOL), _in_array(3, SORT), _in_array(3, UINT)))
    */
    Z3_constructor Z3_API Z3_mk_constructor(Z3_context c,
                                            Z3_symbol name,
                                            Z3_symbol recognizer,
                                            unsigned num_fields,
                                            Z3_symbol const field_names[],
                                            Z3_sort_opt const sorts[],
                                            unsigned sort_refs[]
                                            );

    /**
       \brief Reclaim memory allocated to constructor.

       \param c logical context.
       \param constr constructor.

       def_API('Z3_del_constructor', VOID, (_in(CONTEXT), _in(CONSTRUCTOR)))
    */
    void Z3_API Z3_del_constructor(Z3_context c, Z3_constructor constr);

    /**
       \brief Create datatype, such as lists, trees, records, enumerations or unions of records.
       The datatype may be recursive. Return the datatype sort.

       \param c logical context.
       \param name name of datatype.
       \param num_constructors number of constructors passed in.
       \param constructors array of constructor containers.

       def_API('Z3_mk_datatype', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _inout_array(2, CONSTRUCTOR)))
    */
    Z3_sort Z3_API Z3_mk_datatype(Z3_context c,
                                  Z3_symbol name,
                                  unsigned num_constructors,
                                  Z3_constructor constructors[]);

    /**
       \brief Create list of constructors.

       \param c logical context.
       \param num_constructors number of constructors in list.
       \param constructors list of constructors.

       def_API('Z3_mk_constructor_list', CONSTRUCTOR_LIST, (_in(CONTEXT), _in(UINT), _in_array(1, CONSTRUCTOR)))
    */
    Z3_constructor_list Z3_API Z3_mk_constructor_list(Z3_context c,
                                                      unsigned num_constructors,
                                                      Z3_constructor const constructors[]);

    /**
       \brief Reclaim memory allocated for constructor list.

       Each constructor inside the constructor list must be independently reclaimed using #Z3_del_constructor.

       \param c logical context.
       \param clist constructor list container.

       def_API('Z3_del_constructor_list', VOID, (_in(CONTEXT), _in(CONSTRUCTOR_LIST)))
    */
    void Z3_API Z3_del_constructor_list(Z3_context c, Z3_constructor_list clist);

    /**
       \brief Create mutually recursive datatypes.

       \param c logical context.
       \param num_sorts number of datatype sorts.
       \param sort_names names of datatype sorts.
       \param sorts array of datatype sorts.
       \param constructor_lists list of constructors, one list per sort.

       def_API('Z3_mk_datatypes', VOID, (_in(CONTEXT), _in(UINT), _in_array(1, SYMBOL), _out_array(1, SORT), _inout_array(1, CONSTRUCTOR_LIST)))
    */
    void Z3_API Z3_mk_datatypes(Z3_context c,
                                unsigned num_sorts,
                                Z3_symbol const sort_names[],
                                Z3_sort sorts[],
                                Z3_constructor_list constructor_lists[]);

    /**
       \brief Query constructor for declared functions.

       \param c logical context.
       \param constr constructor container. The container must have been passed in to a #Z3_mk_datatype call.
       \param num_fields number of accessor fields in the constructor.
       \param constructor constructor function declaration, allocated by user.
       \param tester constructor test function declaration, allocated by user.
       \param accessors array of accessor function declarations allocated by user. The array must contain num_fields elements.

       def_API('Z3_query_constructor', VOID, (_in(CONTEXT), _in(CONSTRUCTOR), _in(UINT), _out(FUNC_DECL), _out(FUNC_DECL), _out_array(2, FUNC_DECL)))
    */
    void Z3_API Z3_query_constructor(Z3_context c,
                                     Z3_constructor constr,
                                     unsigned num_fields,
                                     Z3_func_decl* constructor,
                                     Z3_func_decl* tester,
                                     Z3_func_decl accessors[]);

    /*@}*/

    /** @name Constants and Applications */
    /*@{*/

    /**
       \brief Declare a constant or function.

       \param c logical context.
       \param s name of the constant or function.
       \param domain_size number of arguments. It is 0 when declaring a constant.
       \param domain array containing the sort of each argument. The array must contain domain_size elements. It is 0 when declaring a constant.
       \param range sort of the constant or the return sort of the function.

       After declaring a constant or function, the function
       #Z3_mk_app can be used to create a constant or function
       application.

       \sa Z3_mk_app

       def_API('Z3_mk_func_decl', FUNC_DECL, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _in_array(2, SORT), _in(SORT)))
    */
    Z3_func_decl Z3_API Z3_mk_func_decl(Z3_context c, Z3_symbol s,
                                        unsigned domain_size, Z3_sort const domain[],
                                        Z3_sort range);



    /**
       \brief Create a constant or function application.

       \sa Z3_mk_func_decl

       def_API('Z3_mk_app', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT), _in_array(2, AST)))
    */
    Z3_ast Z3_API Z3_mk_app(
        Z3_context c,
        Z3_func_decl d,
        unsigned num_args,
        Z3_ast const args[]);

    /**
       \brief Declare and create a constant.

       This function is a shorthand for:
       \code
       Z3_func_decl d = Z3_mk_func_decl(c, s, 0, 0, ty);
       Z3_ast n            = Z3_mk_app(c, d, 0, 0);
       \endcode

       \sa Z3_mk_func_decl
       \sa Z3_mk_app

       def_API('Z3_mk_const', AST, (_in(CONTEXT), _in(SYMBOL), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_const(Z3_context c, Z3_symbol s, Z3_sort ty);

    /**
       \brief Declare a fresh constant or function.

       Z3 will generate an unique name for this function declaration.
       If prefix is different from \c NULL, then the name generate by Z3 will start with \c prefix.

       \remark If \c prefix is \c NULL, then it is assumed to be the empty string.

       \sa Z3_mk_func_decl

       def_API('Z3_mk_fresh_func_decl', FUNC_DECL, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SORT), _in(SORT)))
    */
    Z3_func_decl Z3_API Z3_mk_fresh_func_decl(Z3_context c, Z3_string prefix,
                                                   unsigned domain_size, Z3_sort const domain[],
                                                   Z3_sort range);

    /**
       \brief Declare and create a fresh constant.

       This function is a shorthand for:
       \code Z3_func_decl d = Z3_mk_fresh_func_decl(c, prefix, 0, 0, ty); Z3_ast n = Z3_mk_app(c, d, 0, 0); \endcode

       \remark If \c prefix is \c NULL, then it is assumed to be the empty string.

       \sa Z3_mk_func_decl
       \sa Z3_mk_app

       def_API('Z3_mk_fresh_const', AST, (_in(CONTEXT), _in(STRING), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fresh_const(Z3_context c, Z3_string prefix, Z3_sort ty);


    /**
       \brief Declare a recursive function

       \param c logical context.
       \param s name of the function.
       \param domain_size number of arguments. It should be greater than 0.
       \param domain array containing the sort of each argument. The array must contain domain_size elements. 
       \param range sort of the constant or the return sort of the function.

       After declaring recursive function, it should be associated with a recursive definition #Z3_add_rec_def.
       The function #Z3_mk_app can be used to create a constant or function
       application.

       \sa Z3_mk_app
       \sa Z3_add_rec_def

       def_API('Z3_mk_rec_func_decl', FUNC_DECL, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _in_array(2, SORT), _in(SORT)))
    */
    Z3_func_decl Z3_API Z3_mk_rec_func_decl(Z3_context c, Z3_symbol s,
                                        unsigned domain_size, Z3_sort const domain[],
                                        Z3_sort range);

    /**
       \brief Define the body of a recursive function.
       
       \param c logical context.
       \param f function declaration.
       \param n number of arguments to the function
       \param args constants that are used as arguments to the recursive function in the definition.
       \param body body of the recursive function

       After declaring a recursive function or a collection of  mutually recursive functions, use 
       this function to provide the definition for the recursive function.

       \sa Z3_mk_rec_func_decl

       def_API('Z3_add_rec_def', VOID, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT), _in_array(2, AST), _in(AST)))
     */
    void Z3_API Z3_add_rec_def(Z3_context c, Z3_func_decl f, unsigned n, Z3_ast args[], Z3_ast body);

    /*@}*/

    /** @name Propositional Logic and Equality */
    /*@{*/
    /**
        \brief Create an AST node representing \c true.

        def_API('Z3_mk_true', AST, (_in(CONTEXT), ))
    */
    Z3_ast Z3_API Z3_mk_true(Z3_context c);

    /**
        \brief Create an AST node representing \c false.

        def_API('Z3_mk_false', AST, (_in(CONTEXT), ))
    */
    Z3_ast Z3_API Z3_mk_false(Z3_context c);

    /**
        \brief Create an AST node representing \ccode{l = r}.

        The nodes \c l and \c r must have the same type.

        def_API('Z3_mk_eq', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);

    /**
       \brief Create an AST node representing \ccode{distinct(args[0], ..., args[num_args-1])}.

       The \c distinct construct is used for declaring the arguments pairwise distinct.
       That is, \ccode{Forall 0 <= i < j < num_args. not args[i] = args[j]}.

       All arguments must have the same sort.

       \remark The number of arguments of a distinct construct must be greater than one.

       def_API('Z3_mk_distinct', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_distinct(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
        \brief Create an AST node representing \ccode{not(a)}.

        The node \c a must have Boolean sort.

        def_API('Z3_mk_not', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_not(Z3_context c, Z3_ast a);

    /**
       \brief Create an AST node representing an if-then-else: \ccode{ite(t1, t2, t3)}.

       The node \c t1 must have Boolean sort, \c t2 and \c t3 must have the same sort.
       The sort of the new node is equal to the sort of \c t2 and \c t3.

       def_API('Z3_mk_ite', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_ite(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3);

    /**
       \brief Create an AST node representing \ccode{t1 iff t2}.

       The nodes \c t1 and \c t2 must have Boolean sort.

       def_API('Z3_mk_iff', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_iff(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Create an AST node representing \ccode{t1 implies t2}.

       The nodes \c t1 and \c t2 must have Boolean sort.

       def_API('Z3_mk_implies', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_implies(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Create an AST node representing \ccode{t1 xor t2}.

       The nodes \c t1 and \c t2 must have Boolean sort.

       def_API('Z3_mk_xor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_xor(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Create an AST node representing \ccode{args[0] and ... and args[num_args-1]}.

       The array \c args must have \c num_args elements.
       All arguments must have Boolean sort.

       \remark The number of arguments must be greater than zero.

       def_API('Z3_mk_and', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_and(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Create an AST node representing \ccode{args[0] or ... or args[num_args-1]}.

       The array \c args must have \c num_args elements.
       All arguments must have Boolean sort.

       \remark The number of arguments must be greater than zero.

       def_API('Z3_mk_or', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_or(Z3_context c, unsigned num_args, Z3_ast const args[]);
    /*@}*/

    /** @name Integers and Reals */
    /*@{*/
    /**
       \brief Create an AST node representing \ccode{args[0] + ... + args[num_args-1]}.

       The array \c args must have \c num_args elements.
       All arguments must have int or real sort.

       \remark The number of arguments must be greater than zero.

       def_API('Z3_mk_add', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_add(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Create an AST node representing \ccode{args[0] * ... * args[num_args-1]}.

       The array \c args must have \c num_args elements.
       All arguments must have int or real sort.

       \remark Z3 has limited support for non-linear arithmetic.
       \remark The number of arguments must be greater than zero.

       def_API('Z3_mk_mul', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_mul(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Create an AST node representing \ccode{args[0] - ... - args[num_args - 1]}.

       The array \c args must have \c num_args elements.
       All arguments must have int or real sort.

       \remark The number of arguments must be greater than zero.

       def_API('Z3_mk_sub', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_sub(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Create an AST node representing \ccode{- arg}.

       The arguments must have int or real type.

       def_API('Z3_mk_unary_minus', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_unary_minus(Z3_context c, Z3_ast arg);

    /**
       \brief Create an AST node representing \ccode{arg1 div arg2}.

       The arguments must either both have int type or both have real type.
       If the arguments have int type, then the result type is an int type, otherwise the
       the result type is real.

       def_API('Z3_mk_div', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_div(Z3_context c, Z3_ast arg1, Z3_ast arg2);

    /**
       \brief Create an AST node representing \ccode{arg1 mod arg2}.

       The arguments must have int type.

       def_API('Z3_mk_mod', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_mod(Z3_context c, Z3_ast arg1, Z3_ast arg2);

    /**
       \brief Create an AST node representing \ccode{arg1 rem arg2}.

       The arguments must have int type.

       def_API('Z3_mk_rem', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_rem(Z3_context c, Z3_ast arg1, Z3_ast arg2);

    /**
       \brief Create an AST node representing \ccode{arg1 ^ arg2}.

       The arguments must have int or real type.

       def_API('Z3_mk_power', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_power(Z3_context c, Z3_ast arg1, Z3_ast arg2);

    /**
        \brief Create less than.

        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.

        def_API('Z3_mk_lt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_lt(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Create less than or equal to.

        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.

        def_API('Z3_mk_le', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_le(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Create greater than.

        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.

        def_API('Z3_mk_gt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_gt(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Create greater than or equal to.

        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.

        def_API('Z3_mk_ge', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_ge(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Coerce an integer to a real.

        There is also a converse operation exposed.
        It follows the semantics prescribed by the SMT-LIB standard.

        You can take the floor of a real by
        creating an auxiliary integer constant \c k and
        and asserting \ccode{mk_int2real(k) <= t1 < mk_int2real(k)+1}.

        The node \c t1 must have sort integer.

        \sa Z3_mk_real2int
        \sa Z3_mk_is_int

        def_API('Z3_mk_int2real', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_int2real(Z3_context c, Z3_ast t1);

    /**
        \brief Coerce a real to an integer.

        The semantics of this function follows the SMT-LIB standard
        for the function to_int

        \sa Z3_mk_int2real
        \sa Z3_mk_is_int

        def_API('Z3_mk_real2int', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_real2int(Z3_context c, Z3_ast t1);

    /**
        \brief Check if a real number is an integer.

        \sa Z3_mk_int2real
        \sa Z3_mk_real2int

        def_API('Z3_mk_is_int', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_is_int(Z3_context c, Z3_ast t1);
    /*@}*/

    /** @name Bit-vectors */
    /*@{*/
    /**
       \brief Bitwise negation.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_bvnot', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvnot(Z3_context c, Z3_ast t1);

    /**
       \brief Take conjunction of bits in vector, return vector of length 1.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_bvredand', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvredand(Z3_context c, Z3_ast t1);

    /**
       \brief Take disjunction of bits in vector, return vector of length 1.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_bvredor', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvredor(Z3_context c, Z3_ast t1);

    /**
       \brief Bitwise and.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvand', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvand(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Bitwise or.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvor(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Bitwise exclusive-or.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvxor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvxor(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Bitwise nand.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvnand', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvnand(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Bitwise nor.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvnor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvnor(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Bitwise xnor.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvxnor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvxnor(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Standard two's complement unary minus.

       The node \c t1 must have bit-vector sort.

       def_API('Z3_mk_bvneg', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvneg(Z3_context c, Z3_ast t1);

    /**
        \brief Standard two's complement addition.

        The nodes \c t1 and \c t2 must have the same bit-vector sort.

        def_API('Z3_mk_bvadd', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvadd(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Standard two's complement subtraction.

        The nodes \c t1 and \c t2 must have the same bit-vector sort.

        def_API('Z3_mk_bvsub', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsub(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Standard two's complement multiplication.

        The nodes \c t1 and \c t2 must have the same bit-vector sort.

        def_API('Z3_mk_bvmul', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvmul(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Unsigned division.

        It is defined as the \c floor of \ccode{t1/t2} if \c t2 is
        different from zero. If \ccode{t2} is zero, then the result
        is undefined.

        The nodes \c t1 and \c t2 must have the same bit-vector sort.

        def_API('Z3_mk_bvudiv', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvudiv(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Two's complement signed division.

        It is defined in the following way:

        - The \c floor of \ccode{t1/t2} if \c t2 is different from zero, and \ccode{t1*t2 >= 0}.

        - The \c ceiling of \ccode{t1/t2} if \c t2 is different from zero, and \ccode{t1*t2 < 0}.

        If \ccode{t2} is zero, then the result is undefined.

        The nodes \c t1 and \c t2 must have the same bit-vector sort.

        def_API('Z3_mk_bvsdiv', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsdiv(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Unsigned remainder.

       It is defined as \ccode{t1 - (t1 /u t2) * t2}, where \ccode{/u} represents unsigned division.

       If \ccode{t2} is zero, then the result is undefined.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvurem', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvurem(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Two's complement signed remainder (sign follows dividend).

       It is defined as \ccode{t1 - (t1 /s t2) * t2}, where \ccode{/s} represents signed division.
       The most significant bit (sign) of the result is equal to the most significant bit of \c t1.

       If \ccode{t2} is zero, then the result is undefined.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       \sa Z3_mk_bvsmod

       def_API('Z3_mk_bvsrem', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsrem(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Two's complement signed remainder (sign follows divisor).

       If \ccode{t2} is zero, then the result is undefined.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       \sa Z3_mk_bvsrem

       def_API('Z3_mk_bvsmod', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsmod(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Unsigned less than.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvult', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvult(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Two's complement signed less than.

       It abbreviates:
       \code
        (or (and (= (extract[|m-1|:|m-1|] t1) bit1)
                (= (extract[|m-1|:|m-1|] t2) bit0))
            (and (= (extract[|m-1|:|m-1|] t1) (extract[|m-1|:|m-1|] t2))
                (bvult t1 t2)))
       \endcode

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvslt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvslt(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Unsigned less than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvule', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvule(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Two's complement signed less than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvsle', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsle(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Unsigned greater than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvuge', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvuge(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Two's complement signed greater than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvsge', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsge(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Unsigned greater than.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvugt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvugt(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Two's complement signed greater than.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvsgt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsgt(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Concatenate the given bit-vectors.

       The nodes \c t1 and \c t2 must have (possibly different) bit-vector sorts

       The result is a bit-vector of size \ccode{n1+n2}, where \c n1 (\c n2) is the size
       of \c t1 (\c t2).

       def_API('Z3_mk_concat', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_concat(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Extract the bits \c high down to \c low from a bit-vector of
       size \c m to yield a new bit-vector of size \c n, where \ccode{n = high - low + 1}.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_extract', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_extract(Z3_context c, unsigned high, unsigned low, Z3_ast t1);

    /**
       \brief Sign-extend of the given bit-vector to the (signed) equivalent bit-vector of
       size \ccode{m+i}, where \c m is the size of the given
       bit-vector.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_sign_ext', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_sign_ext(Z3_context c, unsigned i, Z3_ast t1);

    /**
       \brief Extend the given bit-vector with zeros to the (unsigned) equivalent
       bit-vector of size \ccode{m+i}, where \c m is the size of the
       given bit-vector.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_zero_ext', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_zero_ext(Z3_context c, unsigned i, Z3_ast t1);

    /**
       \brief Repeat the given bit-vector up length \ccode{i}.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_repeat', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_repeat(Z3_context c, unsigned i, Z3_ast t1);

    /**
       \brief Shift left.

       It is equivalent to multiplication by \ccode{2^x} where \c x is the value of the
       third argument.

       NB. The semantics of shift operations varies between environments. This
       definition does not necessarily capture directly the semantics of the
       programming language or assembly architecture you are modeling.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvshl', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvshl(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Logical shift right.

       It is equivalent to unsigned division by \ccode{2^x} where \c x is the
       value of the third argument.

       NB. The semantics of shift operations varies between environments. This
       definition does not necessarily capture directly the semantics of the
       programming language or assembly architecture you are modeling.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvlshr', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvlshr(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Arithmetic shift right.

       It is like logical shift right except that the most significant
       bits of the result always copy the most significant bit of the
       second argument.

       The semantics of shift operations varies between environments. This
       definition does not necessarily capture directly the semantics of the
       programming language or assembly architecture you are modeling.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvashr', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvashr(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Rotate bits of \c t1 to the left \c i times.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_rotate_left', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_rotate_left(Z3_context c, unsigned i, Z3_ast t1);

    /**
       \brief Rotate bits of \c t1 to the right \c i times.

       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_rotate_right', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_rotate_right(Z3_context c, unsigned i, Z3_ast t1);

    /**
       \brief Rotate bits of \c t1 to the left \c t2 times.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_ext_rotate_left', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_ext_rotate_left(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Rotate bits of \c t1 to the right \c t2 times.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_ext_rotate_right', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_ext_rotate_right(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Create an \c n bit bit-vector from the integer argument \c t1.

       The resulting bit-vector has \c n bits, where the i'th bit (counting
       from 0 to \c n-1) is 1 if \c (t1 div 2^i) mod 2 is 1.       

       The node \c t1 must have integer sort.

       def_API('Z3_mk_int2bv', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_int2bv(Z3_context c, unsigned n, Z3_ast t1);

    /**
       \brief Create an integer from the bit-vector argument \c t1.
       If \c is_signed is false, then the bit-vector \c t1 is treated as unsigned.
       So the result is non-negative
       and in the range \ccode{[0..2^N-1]}, where N are the number of bits in \c t1.
       If \c is_signed is true, \c t1 is treated as a signed bit-vector.


       The node \c t1 must have a bit-vector sort.

       def_API('Z3_mk_bv2int', AST, (_in(CONTEXT), _in(AST), _in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_bv2int(Z3_context c,Z3_ast t1, bool is_signed);

    /**
       \brief Create a predicate that checks that the bit-wise addition
       of \c t1 and \c t2 does not overflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvadd_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_bvadd_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);

    /**
       \brief Create a predicate that checks that the bit-wise signed addition
       of \c t1 and \c t2 does not underflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvadd_no_underflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvadd_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Create a predicate that checks that the bit-wise signed subtraction
       of \c t1 and \c t2 does not overflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvsub_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsub_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Create a predicate that checks that the bit-wise subtraction
       of \c t1 and \c t2 does not underflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvsub_no_underflow', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_bvsub_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);

    /**
       \brief Create a predicate that checks that the bit-wise signed division
       of \c t1 and \c t2 does not overflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvsdiv_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvsdiv_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
       \brief Check that bit-wise negation does not overflow when
       \c t1 is interpreted as a signed bit-vector.

       The node \c t1 must have bit-vector sort.

       def_API('Z3_mk_bvneg_no_overflow', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvneg_no_overflow(Z3_context c, Z3_ast t1);

    /**
       \brief Create a predicate that checks that the bit-wise multiplication
       of \c t1 and \c t2 does not overflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvmul_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_bvmul_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);

    /**
       \brief Create a predicate that checks that the bit-wise signed multiplication
       of \c t1 and \c t2 does not underflow.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       def_API('Z3_mk_bvmul_no_underflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_bvmul_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
    /*@}*/

    /** @name Arrays */
    /*@{*/
    /**
       \brief Array read.
       The argument \c a is the array and \c i is the index of the array that gets read.

       The node \c a must have an array sort \ccode{[domain -> range]},
       and \c i must have the sort \c domain.
       The sort of the result is \c range.

       \sa Z3_mk_array_sort
       \sa Z3_mk_store

       def_API('Z3_mk_select', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_select(Z3_context c, Z3_ast a, Z3_ast i);

    

    /**
       \brief n-ary Array read.
       The argument \c a is the array and \c idxs are the indices of the array that gets read.

       def_API('Z3_mk_select_n', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))

    */
    Z3_ast Z3_API Z3_mk_select_n(Z3_context c, Z3_ast a, unsigned n, Z3_ast const* idxs);


    /**
       \brief Array update.

       The node \c a must have an array sort \ccode{[domain -> range]}, \c i must have sort \c domain,
       \c v must have sort range. The sort of the result is \ccode{[domain -> range]}.
       The semantics of this function is given by the theory of arrays described in the SMT-LIB
       standard. See http://smtlib.org for more details.
       The result of this function is an array that is equal to \c a (with respect to \c select)
       on all indices except for \c i, where it maps to \c v (and the \c select of \c a with
       respect to \c i may be a different value).

       \sa Z3_mk_array_sort
       \sa Z3_mk_select

       def_API('Z3_mk_store', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_store(Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v);


    /**
       \brief n-ary Array update.

       def_API('Z3_mk_store_n', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST), _in(AST)))

    */
    Z3_ast Z3_API Z3_mk_store_n(Z3_context c, Z3_ast a, unsigned n, Z3_ast const* idxs, Z3_ast v);

    /**
        \brief Create the constant array.

        The resulting term is an array, such that a \c select on an arbitrary index
        produces the value \c v.

        \param c logical context.
        \param domain domain sort for the array.
        \param v value that the array maps to.

        def_API('Z3_mk_const_array', AST, (_in(CONTEXT), _in(SORT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_const_array(Z3_context c, Z3_sort domain, Z3_ast v);

    /**
       \brief Map f on the argument arrays.

       The \c n nodes \c args must be of array sorts \ccode{[domain_i -> range_i]}.
       The function declaration \c f must have type \ccode{ range_1 .. range_n -> range}.
       \c v must have sort range. The sort of the result is \ccode{[domain_i -> range]}.

       \sa Z3_mk_array_sort
       \sa Z3_mk_store
       \sa Z3_mk_select

       def_API('Z3_mk_map', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT), _in_array(2, AST)))
    */
    Z3_ast Z3_API Z3_mk_map(Z3_context c, Z3_func_decl f, unsigned n, Z3_ast const* args);

    /**
        \brief Access the array default value.
        Produces the default range value, for arrays that can be represented as
        finite maps with a default range value.

        \param c logical context.
        \param array array value whose default range value is accessed.

        def_API('Z3_mk_array_default', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_array_default(Z3_context c, Z3_ast array);

    /**
       \brief Create array with the same interpretation as a function.
       The array satisfies the property (f x) = (select (_ as-array f) x) 
       for every argument x.

       def_API('Z3_mk_as_array', AST, (_in(CONTEXT), _in(FUNC_DECL)))
     */
    Z3_ast Z3_API Z3_mk_as_array(Z3_context c, Z3_func_decl f);

    /**
       \brief Create predicate that holds if Boolean array \c set has \c k elements set to true.       

       def_API('Z3_mk_set_has_size', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_has_size(Z3_context c, Z3_ast set, Z3_ast k);

    /*@}*/

    /** @name Sets */
    /*@{*/
    /**
       \brief Create Set type.

       def_API('Z3_mk_set_sort', SORT, (_in(CONTEXT), _in(SORT)))
    */
    Z3_sort Z3_API Z3_mk_set_sort(Z3_context c, Z3_sort ty);

    /**
        \brief Create the empty set.

        def_API('Z3_mk_empty_set', AST, (_in(CONTEXT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_empty_set(Z3_context c, Z3_sort domain);

    /**
        \brief Create the full set.

        def_API('Z3_mk_full_set', AST, (_in(CONTEXT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_full_set(Z3_context c, Z3_sort domain);

    /**
       \brief Add an element to a set.

       The first argument must be a set, the second an element.

       def_API('Z3_mk_set_add', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_add(Z3_context c, Z3_ast set, Z3_ast elem);

    /**
       \brief Remove an element to a set.

       The first argument must be a set, the second an element.

       def_API('Z3_mk_set_del', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_del(Z3_context c, Z3_ast set, Z3_ast elem);

    /**
       \brief Take the union of a list of sets.

       def_API('Z3_mk_set_union', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_set_union(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Take the intersection of a list of sets.

       def_API('Z3_mk_set_intersect', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_ast Z3_API Z3_mk_set_intersect(Z3_context c, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Take the set difference between two sets.

       def_API('Z3_mk_set_difference', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_difference(Z3_context c, Z3_ast arg1, Z3_ast arg2);

    /**
       \brief Take the complement of a set.

       def_API('Z3_mk_set_complement', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_complement(Z3_context c, Z3_ast arg);

    /**
       \brief Check for set membership.

       The first argument should be an element type of the set.

       def_API('Z3_mk_set_member', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_member(Z3_context c, Z3_ast elem, Z3_ast set);

    /**
       \brief Check for subsetness of sets.

       def_API('Z3_mk_set_subset', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_set_subset(Z3_context c, Z3_ast arg1, Z3_ast arg2);

    /**
       \brief Create array extensionality index given two arrays with the same sort.
              The meaning is given by the axiom:
              (=> (= (select A (array-ext A B)) (select B (array-ext A B))) (= A B))

       def_API('Z3_mk_array_ext', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */

    Z3_ast Z3_API Z3_mk_array_ext(Z3_context c, Z3_ast arg1, Z3_ast arg2);
    /*@}*/

    /** @name Numerals */
    /*@{*/
    /**
       \brief Create a numeral of a given sort.

       \param c logical context.
       \param numeral A string representing the numeral value in decimal notation. The string may be of the form `[num]*[.[num]*][E[+|-][num]+]`.
                      If the given sort is a real, then the numeral can be a rational, that is, a string of the form `[num]* / [num]*` .
       \param ty The sort of the numeral. In the current implementation, the given sort can be an int, real, finite-domain, or bit-vectors of arbitrary size.

       \sa Z3_mk_int
       \sa Z3_mk_unsigned_int

       def_API('Z3_mk_numeral', AST, (_in(CONTEXT), _in(STRING), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_numeral(Z3_context c, Z3_string numeral, Z3_sort ty);

    /**
       \brief Create a real from a fraction.

       \param c logical context.
       \param num numerator of rational.
       \param den denominator of rational.

       \pre den != 0

       \sa Z3_mk_numeral
       \sa Z3_mk_int
       \sa Z3_mk_unsigned_int

       def_API('Z3_mk_real', AST, (_in(CONTEXT), _in(INT), _in(INT)))
    */
    Z3_ast Z3_API Z3_mk_real(Z3_context c, int num, int den);

    /**
       \brief Create a numeral of an int, bit-vector, or finite-domain sort.

       This function can be used to create numerals that fit in a machine integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral

       def_API('Z3_mk_int', AST, (_in(CONTEXT), _in(INT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_int(Z3_context c, int v, Z3_sort ty);

    /**
       \brief Create a numeral of a int, bit-vector, or finite-domain sort.

       This function can be used to create numerals that fit in a machine unsigned integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral

       def_API('Z3_mk_unsigned_int', AST, (_in(CONTEXT), _in(UINT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_unsigned_int(Z3_context c, unsigned v, Z3_sort ty);

    /**
       \brief Create a numeral of a int, bit-vector, or finite-domain sort.

       This function can be used to create numerals that fit in a machine \c int64_t integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral

       def_API('Z3_mk_int64', AST, (_in(CONTEXT), _in(INT64), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_int64(Z3_context c, int64_t v, Z3_sort ty);

    /**
       \brief Create a numeral of a int, bit-vector, or finite-domain sort.

       This function can be used to create numerals that fit in a machine \c uint64_t integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral

       def_API('Z3_mk_unsigned_int64', AST, (_in(CONTEXT), _in(UINT64), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_unsigned_int64(Z3_context c, uint64_t v, Z3_sort ty);

    /**
       \brief create a bit-vector numeral from a vector of Booleans.
       
       \sa Z3_mk_numeral
       def_API('Z3_mk_bv_numeral', AST, (_in(CONTEXT), _in(UINT), _in_array(1, BOOL)))
    */
    Z3_ast Z3_API Z3_mk_bv_numeral(Z3_context c, unsigned sz, bool const* bits);

    /*@}*/

    /** @name Sequences and regular expressions */
    /*@{*/

    /**
       \brief Create a sequence sort out of the sort for the elements.

       def_API('Z3_mk_seq_sort', SORT, (_in(CONTEXT), _in(SORT)))
     */
    Z3_sort Z3_API Z3_mk_seq_sort(Z3_context c, Z3_sort s);

    /**
       \brief Check if \c s is a sequence sort.

       def_API('Z3_is_seq_sort', BOOL, (_in(CONTEXT), _in(SORT)))
     */
    bool Z3_API Z3_is_seq_sort(Z3_context c, Z3_sort s);

    /**
       \brief Retrieve basis sort for sequence sort.

       def_API('Z3_get_seq_sort_basis', SORT, (_in(CONTEXT), _in(SORT)))
     */
    Z3_sort Z3_API Z3_get_seq_sort_basis(Z3_context c, Z3_sort s);

    /**
       \brief Create a regular expression sort out of a sequence sort.

       def_API('Z3_mk_re_sort', SORT, (_in(CONTEXT), _in(SORT)))
     */
    Z3_sort Z3_API Z3_mk_re_sort(Z3_context c, Z3_sort seq);

    /**
       \brief Check if \c s is a regular expression sort.

       def_API('Z3_is_re_sort', BOOL, (_in(CONTEXT), _in(SORT)))
     */
    bool Z3_API Z3_is_re_sort(Z3_context c, Z3_sort s);

    /**
       \brief Retrieve basis sort for regex sort.

       def_API('Z3_get_re_sort_basis', SORT, (_in(CONTEXT), _in(SORT)))
     */
    Z3_sort Z3_API Z3_get_re_sort_basis(Z3_context c, Z3_sort s);

    /**
       \brief Create a sort for 8 bit strings.

       This function creates a sort for ASCII strings.
       Each character is 8 bits.

       def_API('Z3_mk_string_sort', SORT ,(_in(CONTEXT), ))
     */
    Z3_sort Z3_API Z3_mk_string_sort(Z3_context c);

    /**
       \brief Check if \c s is a string sort.

       def_API('Z3_is_string_sort', BOOL, (_in(CONTEXT), _in(SORT)))
     */
    bool Z3_API Z3_is_string_sort(Z3_context c, Z3_sort s);

    /**
       \brief Create a string constant out of the string that is passed in
       def_API('Z3_mk_string' ,AST ,(_in(CONTEXT), _in(STRING)))
     */
    Z3_ast Z3_API Z3_mk_string(Z3_context c, Z3_string s);

    /**
       \brief Create a string constant out of the string that is passed in
       It takes the length of the string as well to take into account
       0 characters. The string is unescaped.

       def_API('Z3_mk_lstring' ,AST ,(_in(CONTEXT), _in(UINT), _in(STRING)))
     */
    Z3_ast Z3_API Z3_mk_lstring(Z3_context c, unsigned len, Z3_string s);

    /**
       \brief Determine if \c s is a string constant.

       def_API('Z3_is_string', BOOL, (_in(CONTEXT), _in(AST)))
     */
    bool Z3_API Z3_is_string(Z3_context c, Z3_ast s);

    /**
       \brief Retrieve the string constant stored in \c s.

       \pre  Z3_is_string(c, s)

       def_API('Z3_get_string' ,STRING ,(_in(CONTEXT), _in(AST)))
     */
    Z3_string Z3_API Z3_get_string(Z3_context c, Z3_ast s);

    /**
       \brief Retrieve the unescaped string constant stored in \c s.

       \pre  Z3_is_string(c, s)

       def_API('Z3_get_lstring' ,STRING ,(_in(CONTEXT), _in(AST), _out(UINT)))
     */
    Z3_string Z3_API Z3_get_lstring(Z3_context c, Z3_ast s, unsigned* length);

    /**
       \brief Create an empty sequence of the sequence sort \c seq.

       \pre s is a sequence sort.

       def_API('Z3_mk_seq_empty' ,AST ,(_in(CONTEXT), _in(SORT)))
     */
    Z3_ast Z3_API Z3_mk_seq_empty(Z3_context c, Z3_sort seq);

    /**
       \brief Create a unit sequence of \c a.

       def_API('Z3_mk_seq_unit' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_unit(Z3_context c, Z3_ast a);

    /**
       \brief Concatenate sequences.

       \pre n > 0

       def_API('Z3_mk_seq_concat' ,AST ,(_in(CONTEXT), _in(UINT), _in_array(1, AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_concat(Z3_context c, unsigned n, Z3_ast const args[]);

    /**
       \brief Check if \c prefix is a prefix of \c s.

       \pre prefix and s are the same sequence sorts.

       def_API('Z3_mk_seq_prefix' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_prefix(Z3_context c, Z3_ast prefix, Z3_ast s);

    /**
       \brief Check if \c suffix is a suffix of \c s.

       \pre \c suffix and \c s are the same sequence sorts.

       def_API('Z3_mk_seq_suffix' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_suffix(Z3_context c, Z3_ast suffix, Z3_ast s);

    /**
       \brief Check if \c container contains \c containee.

       \pre \c container and \c containee are the same sequence sorts.

       def_API('Z3_mk_seq_contains' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_contains(Z3_context c, Z3_ast container, Z3_ast containee);

    /**
       \brief Extract subsequence starting at \c offset of \c length.

       def_API('Z3_mk_seq_extract' ,AST ,(_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_extract(Z3_context c, Z3_ast s, Z3_ast offset, Z3_ast length);

    /**
       \brief Replace the first occurrence of \c src with \c dst in \c s.

       def_API('Z3_mk_seq_replace' ,AST ,(_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_replace(Z3_context c, Z3_ast s, Z3_ast src, Z3_ast dst);

    /**
       \brief Retrieve from \c s the unit sequence positioned at position \c index.
       The sequence is empty if the index is out of bounds.

       def_API('Z3_mk_seq_at' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_at(Z3_context c, Z3_ast s, Z3_ast index);

    /**
       \brief Retrieve from \c s the element positioned at position \c index.
       The function is under-specified if the index is out of bounds.

       def_API('Z3_mk_seq_nth' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_nth(Z3_context c, Z3_ast s, Z3_ast index);

    /**
       \brief Return the length of the sequence \c s.

       def_API('Z3_mk_seq_length' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_length(Z3_context c, Z3_ast s);


    /**
       \brief Return index of first occurrence of \c substr in \c s starting from offset \c offset.
       If \c s does not contain \c substr, then the value is -1, if \c offset is the length of \c s, then the value is -1 as well.
       The value is -1 if \c offset is negative or larger than the length of \c s.

       def_API('Z3_mk_seq_index' ,AST ,(_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_index(Z3_context c, Z3_ast s, Z3_ast substr, Z3_ast offset);

    /**
       \brief Return the last occurrence of \c substr in \c s.
       If \c s does not contain \c substr, then the value is -1, 
       def_API('Z3_mk_seq_last_index', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_seq_last_index(Z3_context c, Z3_ast, Z3_ast substr);

    /**
       \brief Convert string to integer.

       def_API('Z3_mk_str_to_int' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_str_to_int(Z3_context c, Z3_ast s);


    /**
       \brief Integer to string conversion.

       def_API('Z3_mk_int_to_str' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_int_to_str(Z3_context c, Z3_ast s);

    /**
       \brief Create a regular expression that accepts the sequence \c seq.

       def_API('Z3_mk_seq_to_re' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_to_re(Z3_context c, Z3_ast seq);

    /**
       \brief Check if \c seq is in the language generated by the regular expression \c re.

       def_API('Z3_mk_seq_in_re' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_seq_in_re(Z3_context c, Z3_ast seq, Z3_ast re);

    /**
       \brief Create the regular language \c re+.

       def_API('Z3_mk_re_plus' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_re_plus(Z3_context c, Z3_ast re);

    /**
       \brief Create the regular language \c re*.

       def_API('Z3_mk_re_star' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_re_star(Z3_context c, Z3_ast re);

    /**
       \brief Create the regular language \c [re].

       def_API('Z3_mk_re_option' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_re_option(Z3_context c, Z3_ast re);

    /**
       \brief Create the union of the regular languages.

       \pre n > 0

       def_API('Z3_mk_re_union' ,AST ,(_in(CONTEXT), _in(UINT), _in_array(1, AST)))
     */
    Z3_ast Z3_API Z3_mk_re_union(Z3_context c, unsigned n, Z3_ast const args[]);

    /**
       \brief Create the concatenation of the regular languages.

       \pre n > 0

       def_API('Z3_mk_re_concat' ,AST ,(_in(CONTEXT), _in(UINT), _in_array(1, AST)))
     */
    Z3_ast Z3_API Z3_mk_re_concat(Z3_context c, unsigned n, Z3_ast const args[]);


    /**
       \brief Create the range regular expression over two sequences of length 1.

       def_API('Z3_mk_re_range' ,AST ,(_in(CONTEXT), _in(AST), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_re_range(Z3_context c, Z3_ast lo, Z3_ast hi);

    /**
       \brief Create a regular expression loop. The supplied regular expression \c r is repeated
       between \c lo and \c hi times. The \c lo should be below \c hi with one exception: when
       supplying the value \c hi as 0, the meaning is to repeat the argument \c r at least
       \c lo number of times, and with an unbounded upper bound.

       def_API('Z3_mk_re_loop', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in(UINT)))
     */
    Z3_ast Z3_API Z3_mk_re_loop(Z3_context c, Z3_ast r, unsigned lo, unsigned hi);

    /**
       \brief Create the intersection of the regular languages.

       \pre n > 0

       def_API('Z3_mk_re_intersect' ,AST ,(_in(CONTEXT), _in(UINT), _in_array(1, AST)))
     */
    Z3_ast Z3_API Z3_mk_re_intersect(Z3_context c, unsigned n, Z3_ast const args[]);

    /**
       \brief Create the complement of the regular language \c re.

       def_API('Z3_mk_re_complement' ,AST ,(_in(CONTEXT), _in(AST)))
     */
    Z3_ast Z3_API Z3_mk_re_complement(Z3_context c, Z3_ast re);

    /**
       \brief Create an empty regular expression of sort \c re.

       \pre re is a regular expression sort.

       def_API('Z3_mk_re_empty' ,AST ,(_in(CONTEXT), _in(SORT)))
     */
    Z3_ast Z3_API Z3_mk_re_empty(Z3_context c, Z3_sort re);


    /**
       \brief Create an universal regular expression of sort \c re.

       \pre re is a regular expression sort.

       def_API('Z3_mk_re_full' ,AST ,(_in(CONTEXT), _in(SORT)))
     */
    Z3_ast Z3_API Z3_mk_re_full(Z3_context c, Z3_sort re);

    /*@}*/


    /** @name Special relations */
    /*@{*/
    /**
       \brief declare \c a and \c b are in linear order over a relation indexed by \c id.

       \pre a and b are of same type.
       

       def_API('Z3_mk_linear_order', FUNC_DECL ,(_in(CONTEXT), _in(SORT), _in(UINT)))
     */
    Z3_func_decl Z3_API Z3_mk_linear_order(Z3_context c, Z3_sort a, unsigned id);

    /**
       \brief create a partial ordering relation over signature \c a and index \c id.

       def_API('Z3_mk_partial_order', FUNC_DECL ,(_in(CONTEXT), _in(SORT), _in(UINT)))
     */
    Z3_func_decl Z3_API Z3_mk_partial_order(Z3_context c, Z3_sort a, unsigned id);

    /**
       \brief create a piecewise linear ordering relation over signature \c a and index \c id.

       def_API('Z3_mk_piecewise_linear_order', FUNC_DECL ,(_in(CONTEXT), _in(SORT), _in(UINT)))
     */
    Z3_func_decl Z3_API Z3_mk_piecewise_linear_order(Z3_context c, Z3_sort a, unsigned id);

    /**
       \brief create a tree ordering lreation over signature \c a identified using index \c id.

       def_API('Z3_mk_tree_order', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
     */
    Z3_func_decl Z3_API Z3_mk_tree_order(Z3_context c, Z3_sort a, unsigned id);

    /**
       \brief create transitive closure of binary relation.

       \pre f is a binary relation, such that the two arguments have the same sorts.

       The resulting relation f+ represents the transitive closure of f.

       def_API('Z3_mk_transitive_closure', FUNC_DECL ,(_in(CONTEXT), _in(FUNC_DECL)))
     */
    Z3_func_decl Z3_API Z3_mk_transitive_closure(Z3_context c, Z3_func_decl f);

    /*@}*/

    /** @name Quantifiers */
    /*@{*/
    /**
       \brief Create a pattern for quantifier instantiation.

       Z3 uses pattern matching to instantiate quantifiers. If a
       pattern is not provided for a quantifier, then Z3 will
       automatically compute a set of patterns for it. However, for
       optimal performance, the user should provide the patterns.

       Patterns comprise a list of terms. The list should be
       non-empty.  If the list comprises of more than one term, it is
       a called a multi-pattern.

       In general, one can pass in a list of (multi-)patterns in the
       quantifier constructor.

       \sa Z3_mk_forall
       \sa Z3_mk_exists

       def_API('Z3_mk_pattern', PATTERN, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
    */
    Z3_pattern Z3_API Z3_mk_pattern(Z3_context c, unsigned num_patterns, Z3_ast const terms[]);

    /**
       \brief Create a bound variable.

       Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
       the meaning of de-Bruijn indices by indicating the compilation process from
       non-de-Bruijn formulas to de-Bruijn format.

       \verbatim
       abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
       abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
       abs1(x, x, n) = b_n
       abs1(y, x, n) = y
       abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
       abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
       \endverbatim

       The last line is significant: the index of a bound variable is different depending
       on the scope in which it appears. The deeper x appears, the higher is its
       index.

       \param c logical context
       \param index de-Bruijn index
       \param ty sort of the bound variable

       \sa Z3_mk_forall
       \sa Z3_mk_exists

       def_API('Z3_mk_bound', AST, (_in(CONTEXT), _in(UINT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_bound(Z3_context c, unsigned index, Z3_sort ty);

    /**
       \brief Create a forall formula. It takes an expression \c body that contains bound variables
       of the same sorts as the sorts listed in the array \c sorts. The bound variables are de-Bruijn indices created
       using #Z3_mk_bound. The array \c decl_names contains the names that the quantified formula uses for the
       bound variables. Z3 applies the convention that the last element in the \c decl_names and \c sorts array
       refers to the variable with index 0, the second to last element of \c decl_names and \c sorts refers
       to the variable with index 1, etc.

       \param c logical context.
       \param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_decls number of variables to be bound.
       \param sorts the sorts of the bound variables.
       \param decl_names names of the bound variables
       \param body the body of the quantifier.

       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_exists

       def_API('Z3_mk_forall', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in_array(2, PATTERN), _in(UINT), _in_array(4, SORT), _in_array(4, SYMBOL), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_forall(Z3_context c, unsigned weight,
                               unsigned num_patterns, Z3_pattern const patterns[],
                               unsigned num_decls, Z3_sort const sorts[],
                               Z3_symbol const decl_names[],
                               Z3_ast body);

    /**
       \brief Create an exists formula. Similar to #Z3_mk_forall.

       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_quantifier

       def_API('Z3_mk_exists', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in_array(2, PATTERN), _in(UINT), _in_array(4, SORT), _in_array(4, SYMBOL), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_exists(Z3_context c, unsigned weight,
                               unsigned num_patterns, Z3_pattern const patterns[],
                               unsigned num_decls, Z3_sort const sorts[],
                               Z3_symbol const decl_names[],
                               Z3_ast body);

    /**
       \brief Create a quantifier - universal or existential, with pattern hints.
       See the documentation for #Z3_mk_forall for an explanation of the parameters.

       \param c logical context.
       \param is_forall flag to indicate if this is a universal or existential quantifier.
       \param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_decls number of variables to be bound.
       \param sorts array of sorts of the bound variables.
       \param decl_names names of the bound variables.
       \param body the body of the quantifier.

       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_exists

       def_API('Z3_mk_quantifier', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(UINT), _in_array(3, PATTERN), _in(UINT), _in_array(5, SORT), _in_array(5, SYMBOL), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_quantifier(
        Z3_context c,
        bool is_forall,
        unsigned weight,
        unsigned num_patterns, Z3_pattern const patterns[],
        unsigned num_decls, Z3_sort const sorts[],
        Z3_symbol const decl_names[],
        Z3_ast body);


    /**
       \brief Create a quantifier - universal or existential, with pattern hints, no patterns, and attributes

       \param c logical context.
       \param is_forall flag to indicate if this is a universal or existential quantifier.
       \param quantifier_id identifier to identify quantifier
       \param skolem_id identifier to identify skolem constants introduced by quantifier.
       \param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_no_patterns number of no_patterns.
       \param no_patterns array containing subexpressions to be excluded from inferred patterns.
       \param num_decls number of variables to be bound.
       \param sorts array of sorts of the bound variables.
       \param decl_names names of the bound variables.
       \param body the body of the quantifier.

       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_exists

       def_API('Z3_mk_quantifier_ex', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(SYMBOL), _in(SYMBOL), _in(UINT), _in_array(5, PATTERN), _in(UINT), _in_array(7, AST), _in(UINT), _in_array(9, SORT), _in_array(9, SYMBOL), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_quantifier_ex(
        Z3_context c,
        bool is_forall,
        unsigned weight,
        Z3_symbol quantifier_id,
        Z3_symbol skolem_id,
        unsigned num_patterns, Z3_pattern const patterns[],
        unsigned num_no_patterns, Z3_ast const no_patterns[],
        unsigned num_decls, Z3_sort const sorts[],
        Z3_symbol const decl_names[],
        Z3_ast body);

    /**
       \brief Create a universal quantifier using a list of constants that
       will form the set of bound variables.

       \param c logical context.
       \param weight quantifiers are associated with weights indicating the importance of using
              the quantifier during instantiation. By default, pass the weight 0.
       \param num_bound number of constants to be abstracted into bound variables.
       \param bound array of constants to be abstracted into bound variables.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param body the body of the quantifier.

       \sa Z3_mk_pattern
       \sa Z3_mk_exists_const

       def_API('Z3_mk_forall_const', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in_array(2, APP), _in(UINT), _in_array(4, PATTERN), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_forall_const(
        Z3_context c,
        unsigned weight,
        unsigned num_bound,
        Z3_app const bound[],
        unsigned num_patterns,
        Z3_pattern const patterns[],
        Z3_ast body
        );

    /**
       \brief Similar to #Z3_mk_forall_const.

       \brief Create an existential quantifier using a list of constants that
       will form the set of bound variables.

       \param c logical context.
       \param weight quantifiers are associated with weights indicating the importance of using
              the quantifier during instantiation. By default, pass the weight 0.
       \param num_bound number of constants to be abstracted into bound variables.
       \param bound array of constants to be abstracted into bound variables.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param body the body of the quantifier.

       \sa Z3_mk_pattern
       \sa Z3_mk_forall_const

       def_API('Z3_mk_exists_const', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in_array(2, APP), _in(UINT), _in_array(4, PATTERN), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_exists_const(
        Z3_context c,
        unsigned weight,
        unsigned num_bound,
        Z3_app const bound[],
        unsigned num_patterns,
        Z3_pattern const patterns[],
        Z3_ast body
        );

    /**
       \brief Create a universal or existential quantifier using a list of
       constants that will form the set of bound variables.

       def_API('Z3_mk_quantifier_const', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(UINT), _in_array(3, APP), _in(UINT), _in_array(5, PATTERN), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_quantifier_const(
        Z3_context c,
        bool is_forall,
        unsigned weight,
        unsigned num_bound,  Z3_app const bound[],
        unsigned num_patterns, Z3_pattern const patterns[],
        Z3_ast body
        );

    /**
       \brief Create a universal or existential quantifier using a list of
       constants that will form the set of bound variables.

       def_API('Z3_mk_quantifier_const_ex', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(SYMBOL), _in(SYMBOL), _in(UINT), _in_array(5, APP), _in(UINT), _in_array(7, PATTERN), _in(UINT), _in_array(9, AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_quantifier_const_ex(
        Z3_context c,
        bool is_forall,
        unsigned weight,
        Z3_symbol quantifier_id,
        Z3_symbol skolem_id,
        unsigned num_bound,  Z3_app const bound[],
        unsigned num_patterns, Z3_pattern const patterns[],
        unsigned num_no_patterns, Z3_ast const no_patterns[],
        Z3_ast body
        );

    /**
       \brief Create a lambda expression. It takes an expression \c body that contains bound variables
       of the same sorts as the sorts listed in the array \c sorts. The bound variables are de-Bruijn indices created
       using #Z3_mk_bound. The array \c decl_names contains the names that the quantified formula uses for the
       bound variables. Z3 applies the convention that the last element in the \c decl_names and \c sorts array
       refers to the variable with index 0, the second to last element of \c decl_names and \c sorts refers
       to the variable with index 1, etc.
       The sort of the resulting expression is \c (Array sorts range) where \c range is the sort of \c body.
       For example, if the lambda binds two variables of sort \c Int and \c Bool, and the \c body has sort \c Real, 
       the sort of the expression is \c (Array Int Bool Real).

       \param c logical context
       \param num_decls number of variables to be bound.
       \param sorts the sorts of the bound variables.
       \param decl_names names of the bound variables
       \param body the body of the lambda expression.       

       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_lambda_const

       def_API('Z3_mk_lambda', AST, (_in(CONTEXT), _in(UINT), _in_array(1, SORT), _in_array(1, SYMBOL), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_lambda(Z3_context c, 
                               unsigned num_decls, Z3_sort const sorts[],
                               Z3_symbol const decl_names[],
                               Z3_ast body);

    /**
       \brief Create a lambda expression using a list of constants that form the set
       of bound variables

       \param c logical context.
       \param num_bound number of constants to be abstracted into bound variables.
       \param bound array of constants to be abstracted into bound variables.
       \param body the body of the lambda expression.

       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_lambda

       def_API('Z3_mk_lambda_const', AST, (_in(CONTEXT), _in(UINT), _in_array(1, APP), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_lambda_const(Z3_context c, 
                                     unsigned num_bound, Z3_app const bound[],
                                     Z3_ast body);


    /*@}*/

    /** @name Accessors */
    /*@{*/
    /**
       \brief Return \c Z3_INT_SYMBOL if the symbol was constructed
       using #Z3_mk_int_symbol, and \c Z3_STRING_SYMBOL if the symbol
       was constructed using #Z3_mk_string_symbol.

       def_API('Z3_get_symbol_kind', UINT, (_in(CONTEXT), _in(SYMBOL)))
    */
    Z3_symbol_kind Z3_API Z3_get_symbol_kind(Z3_context c, Z3_symbol s);

    /**
       \brief Return the symbol int value.

       \pre Z3_get_symbol_kind(s) == Z3_INT_SYMBOL

       \sa Z3_mk_int_symbol

       def_API('Z3_get_symbol_int', INT, (_in(CONTEXT), _in(SYMBOL)))
    */
    int Z3_API Z3_get_symbol_int(Z3_context c, Z3_symbol s);

    /**
       \brief Return the symbol name.

       \pre Z3_get_symbol_kind(s) == Z3_STRING_SYMBOL

       \warning The returned buffer is statically allocated by Z3. It will
       be automatically deallocated when #Z3_del_context is invoked.
       So, the buffer is invalidated in the next call to \c Z3_get_symbol_string.

       \sa Z3_mk_string_symbol

       def_API('Z3_get_symbol_string', STRING, (_in(CONTEXT), _in(SYMBOL)))
    */
    Z3_string Z3_API Z3_get_symbol_string(Z3_context c, Z3_symbol s);

    /**
       \brief Return the sort name as a symbol.

       def_API('Z3_get_sort_name', SYMBOL, (_in(CONTEXT), _in(SORT)))
    */
    Z3_symbol Z3_API Z3_get_sort_name(Z3_context c, Z3_sort d);

    /**
        \brief Return a unique identifier for \c s.

        def_API('Z3_get_sort_id', UINT, (_in(CONTEXT), _in(SORT)))
    */
    unsigned Z3_API Z3_get_sort_id(Z3_context c, Z3_sort s);

    /**
       \brief Convert a \c Z3_sort into \c Z3_ast. This is just type casting.

       def_API('Z3_sort_to_ast', AST, (_in(CONTEXT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_sort_to_ast(Z3_context c, Z3_sort s);

    /**
       \brief compare sorts.

       def_API('Z3_is_eq_sort', BOOL, (_in(CONTEXT), _in(SORT), _in(SORT)))
    */
    bool Z3_API Z3_is_eq_sort(Z3_context c, Z3_sort s1, Z3_sort s2);

    /**
       \brief Return the sort kind (e.g., array, tuple, int, bool, etc).

       \sa Z3_sort_kind

       def_API('Z3_get_sort_kind', UINT, (_in(CONTEXT), _in(SORT)))
    */
    Z3_sort_kind Z3_API Z3_get_sort_kind(Z3_context c, Z3_sort t);

    /**
       \brief Return the size of the given bit-vector sort.

       \pre Z3_get_sort_kind(c, t) == Z3_BV_SORT

       \sa Z3_mk_bv_sort
       \sa Z3_get_sort_kind

       def_API('Z3_get_bv_sort_size', UINT, (_in(CONTEXT), _in(SORT)))
    */
    unsigned Z3_API Z3_get_bv_sort_size(Z3_context c, Z3_sort t);

    /**
        \brief Store the size of the sort in \c r. Return \c false if the call failed.
        That is, Z3_get_sort_kind(s) == Z3_FINITE_DOMAIN_SORT

        def_API('Z3_get_finite_domain_sort_size', BOOL, (_in(CONTEXT), _in(SORT), _out(UINT64)))
    */
    Z3_bool_opt Z3_API Z3_get_finite_domain_sort_size(Z3_context c, Z3_sort s, uint64_t* r);

    /**
       \brief Return the domain of the given array sort.
       In the case of a multi-dimensional array, this function returns the sort of the first dimension.

       \pre Z3_get_sort_kind(c, t) == Z3_ARRAY_SORT

       \sa Z3_mk_array_sort
       \sa Z3_get_sort_kind

       def_API('Z3_get_array_sort_domain', SORT, (_in(CONTEXT), _in(SORT)))
    */
    Z3_sort Z3_API Z3_get_array_sort_domain(Z3_context c, Z3_sort t);

    /**
       \brief Return the range of the given array sort.

       \pre Z3_get_sort_kind(c, t) == Z3_ARRAY_SORT

       \sa Z3_mk_array_sort
       \sa Z3_get_sort_kind

       def_API('Z3_get_array_sort_range', SORT, (_in(CONTEXT), _in(SORT)))
    */
    Z3_sort Z3_API Z3_get_array_sort_range(Z3_context c, Z3_sort t);

    /**
       \brief Return the constructor declaration of the given tuple
       sort.

       \pre Z3_get_sort_kind(c, t) == Z3_DATATYPE_SORT

       \sa Z3_mk_tuple_sort
       \sa Z3_get_sort_kind

       def_API('Z3_get_tuple_sort_mk_decl', FUNC_DECL, (_in(CONTEXT), _in(SORT)))
    */
    Z3_func_decl Z3_API Z3_get_tuple_sort_mk_decl(Z3_context c, Z3_sort t);

    /**
       \brief Return the number of fields of the given tuple sort.

       \pre Z3_get_sort_kind(c, t) == Z3_DATATYPE_SORT

       \sa Z3_mk_tuple_sort
       \sa Z3_get_sort_kind

       def_API('Z3_get_tuple_sort_num_fields', UINT, (_in(CONTEXT), _in(SORT)))
    */
    unsigned Z3_API Z3_get_tuple_sort_num_fields(Z3_context c, Z3_sort t);

    /**
       \brief Return the i-th field declaration (i.e., projection function declaration)
       of the given tuple sort.

       \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
       \pre i < Z3_get_tuple_sort_num_fields(c, t)

       \sa Z3_mk_tuple_sort
       \sa Z3_get_sort_kind

       def_API('Z3_get_tuple_sort_field_decl', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_get_tuple_sort_field_decl(Z3_context c, Z3_sort t, unsigned i);

    /**
        \brief Return number of constructors for datatype.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT

        \sa Z3_get_datatype_sort_constructor
        \sa Z3_get_datatype_sort_recognizer
        \sa Z3_get_datatype_sort_constructor_accessor

        def_API('Z3_get_datatype_sort_num_constructors', UINT, (_in(CONTEXT), _in(SORT)))
    */
    unsigned Z3_API Z3_get_datatype_sort_num_constructors(
        Z3_context c, Z3_sort t);

    /**
        \brief Return idx'th constructor.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
        \pre idx < Z3_get_datatype_sort_num_constructors(c, t)

        \sa Z3_get_datatype_sort_num_constructors
        \sa Z3_get_datatype_sort_recognizer
        \sa Z3_get_datatype_sort_constructor_accessor

        def_API('Z3_get_datatype_sort_constructor', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_get_datatype_sort_constructor(
        Z3_context c, Z3_sort t, unsigned idx);

    /**
        \brief Return idx'th recognizer.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
        \pre idx < Z3_get_datatype_sort_num_constructors(c, t)

        \sa Z3_get_datatype_sort_num_constructors
        \sa Z3_get_datatype_sort_constructor
        \sa Z3_get_datatype_sort_constructor_accessor

        def_API('Z3_get_datatype_sort_recognizer', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_get_datatype_sort_recognizer(
        Z3_context c, Z3_sort t, unsigned idx);

    /**
        \brief Return idx_a'th accessor for the idx_c'th constructor.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
        \pre idx_c < Z3_get_datatype_sort_num_constructors(c, t)
        \pre idx_a < Z3_get_domain_size(c, Z3_get_datatype_sort_constructor(c, idx_c))

        \sa Z3_get_datatype_sort_num_constructors
        \sa Z3_get_datatype_sort_constructor
        \sa Z3_get_datatype_sort_recognizer

        def_API('Z3_get_datatype_sort_constructor_accessor', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_get_datatype_sort_constructor_accessor(Z3_context c,
                                                                  Z3_sort t,
                                                                  unsigned idx_c,
                                                                  unsigned idx_a);

    /**
       \brief Update record field with a value.

       This corresponds to the 'with' construct in OCaml.
       It has the effect of updating a record field with a given value.
       The remaining fields are left unchanged. It is the record
       equivalent of an array store (see \sa Z3_mk_store).
       If the datatype has more than one constructor, then the update function
       behaves as identity if there is a mismatch between the accessor and
       constructor. For example ((_ update-field car) nil 1) is nil,
       while ((_ update-field car) (cons 2 nil) 1) is (cons 1 nil).


       \pre Z3_get_sort_kind(Z3_get_sort(c, t)) == Z3_get_domain(c, field_access, 1) == Z3_DATATYPE_SORT
       \pre Z3_get_sort(c, value) == Z3_get_range(c, field_access)


       def_API('Z3_datatype_update_field', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_datatype_update_field(Z3_context c, Z3_func_decl field_access,
                                           Z3_ast t, Z3_ast value);

    /**
        \brief Return arity of relation.

        \pre Z3_get_sort_kind(s) == Z3_RELATION_SORT

        \sa Z3_get_relation_column

        def_API('Z3_get_relation_arity', UINT, (_in(CONTEXT), _in(SORT)))
    */
    unsigned Z3_API Z3_get_relation_arity(Z3_context c, Z3_sort s);

    /**
        \brief Return sort at i'th column of relation sort.

        \pre Z3_get_sort_kind(c, s) == Z3_RELATION_SORT
        \pre col < Z3_get_relation_arity(c, s)

        \sa Z3_get_relation_arity

        def_API('Z3_get_relation_column', SORT, (_in(CONTEXT), _in(SORT), _in(UINT)))
    */
    Z3_sort Z3_API Z3_get_relation_column(Z3_context c, Z3_sort s, unsigned col);

    /**
       \brief Pseudo-Boolean relations.

       Encode p1 + p2 + ... + pn <= k

       def_API('Z3_mk_atmost', AST, (_in(CONTEXT), _in(UINT), _in_array(1,AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_mk_atmost(Z3_context c, unsigned num_args,
                               Z3_ast const args[], unsigned k);

    /**
       \brief Pseudo-Boolean relations.

       Encode p1 + p2 + ... + pn >= k

       def_API('Z3_mk_atleast', AST, (_in(CONTEXT), _in(UINT), _in_array(1,AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_mk_atleast(Z3_context c, unsigned num_args,
                                Z3_ast const args[], unsigned k);

    /**
       \brief Pseudo-Boolean relations.

       Encode k1*p1 + k2*p2 + ... + kn*pn <= k

       def_API('Z3_mk_pble', AST, (_in(CONTEXT), _in(UINT), _in_array(1,AST), _in_array(1,INT), _in(INT)))
    */
    Z3_ast Z3_API Z3_mk_pble(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const coeffs[],
                             int k);

    /**
       \brief Pseudo-Boolean relations.

       Encode k1*p1 + k2*p2 + ... + kn*pn >= k

       def_API('Z3_mk_pbge', AST, (_in(CONTEXT), _in(UINT), _in_array(1,AST), _in_array(1,INT), _in(INT)))
    */
    Z3_ast Z3_API Z3_mk_pbge(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const coeffs[],
                             int k);

    /**
       \brief Pseudo-Boolean relations.

       Encode k1*p1 + k2*p2 + ... + kn*pn = k

       def_API('Z3_mk_pbeq', AST, (_in(CONTEXT), _in(UINT), _in_array(1,AST), _in_array(1,INT), _in(INT)))
    */
    Z3_ast Z3_API Z3_mk_pbeq(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const coeffs[],
                             int k);

    /**
       \brief Convert a \c Z3_func_decl into \c Z3_ast. This is just type casting.

       def_API('Z3_func_decl_to_ast', AST, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    Z3_ast Z3_API Z3_func_decl_to_ast(Z3_context c, Z3_func_decl f);

    /**
       \brief Compare terms.

       def_API('Z3_is_eq_func_decl', BOOL, (_in(CONTEXT), _in(FUNC_DECL), _in(FUNC_DECL)))
    */
    bool Z3_API Z3_is_eq_func_decl(Z3_context c, Z3_func_decl f1, Z3_func_decl f2);

    /**
        \brief Return a unique identifier for \c f.

        def_API('Z3_get_func_decl_id', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    unsigned Z3_API Z3_get_func_decl_id(Z3_context c, Z3_func_decl f);

    /**
       \brief Return the constant declaration name as a symbol.

       def_API('Z3_get_decl_name', SYMBOL, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    Z3_symbol Z3_API Z3_get_decl_name(Z3_context c, Z3_func_decl d);

    /**
       \brief Return declaration kind corresponding to declaration.

       def_API('Z3_get_decl_kind', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    Z3_decl_kind Z3_API Z3_get_decl_kind(Z3_context c, Z3_func_decl d);

    /**
       \brief Return the number of parameters of the given declaration.

       \sa Z3_get_arity

       def_API('Z3_get_domain_size', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    unsigned Z3_API Z3_get_domain_size(Z3_context c, Z3_func_decl d);

    /**
       \brief Alias for \c Z3_get_domain_size.

       \sa Z3_get_domain_size

       def_API('Z3_get_arity', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    unsigned Z3_API Z3_get_arity(Z3_context c, Z3_func_decl d);

    /**
       \brief Return the sort of the i-th parameter of the given function declaration.

       \pre i < Z3_get_domain_size(d)

       \sa Z3_get_domain_size

       def_API('Z3_get_domain', SORT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_sort Z3_API Z3_get_domain(Z3_context c, Z3_func_decl d, unsigned i);

    /**
       \brief Return the range of the given declaration.

       If \c d is a constant (i.e., has zero arguments), then this
       function returns the sort of the constant.

       def_API('Z3_get_range', SORT, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    Z3_sort Z3_API Z3_get_range(Z3_context c, Z3_func_decl d);

    /**
       \brief Return the number of parameters associated with a declaration.

       def_API('Z3_get_decl_num_parameters', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    unsigned Z3_API Z3_get_decl_num_parameters(Z3_context c, Z3_func_decl d);

    /**
       \brief Return the parameter type associated with a declaration.

       \param c the context
       \param d the function declaration
       \param idx is the index of the named parameter it should be between 0 and the number of parameters.

       def_API('Z3_get_decl_parameter_kind', UINT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_parameter_kind Z3_API Z3_get_decl_parameter_kind(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the integer value associated with an integer parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_INT

       def_API('Z3_get_decl_int_parameter', INT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    int Z3_API Z3_get_decl_int_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the double value associated with an double parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_DOUBLE

       def_API('Z3_get_decl_double_parameter', DOUBLE, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    double Z3_API Z3_get_decl_double_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the double value associated with an double parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_SYMBOL

       def_API('Z3_get_decl_symbol_parameter', SYMBOL, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_symbol Z3_API Z3_get_decl_symbol_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the sort value associated with a sort parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_SORT

       def_API('Z3_get_decl_sort_parameter', SORT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_sort Z3_API Z3_get_decl_sort_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the expression value associated with an expression parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_AST

       def_API('Z3_get_decl_ast_parameter', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_ast Z3_API Z3_get_decl_ast_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the expression value associated with an expression parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_FUNC_DECL

       def_API('Z3_get_decl_func_decl_parameter', FUNC_DECL, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_get_decl_func_decl_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Return the rational value, as a string, associated with a rational parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_RATIONAL

       def_API('Z3_get_decl_rational_parameter', STRING, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
    */
    Z3_string Z3_API Z3_get_decl_rational_parameter(Z3_context c, Z3_func_decl d, unsigned idx);

    /**
       \brief Convert a \c Z3_app into \c Z3_ast. This is just type casting.

       def_API('Z3_app_to_ast', AST, (_in(CONTEXT), _in(APP)))
    */
    Z3_ast Z3_API Z3_app_to_ast(Z3_context c, Z3_app a);

    /**
       \brief Return the declaration of a constant or function application.

       def_API('Z3_get_app_decl', FUNC_DECL, (_in(CONTEXT), _in(APP)))
    */
    Z3_func_decl Z3_API Z3_get_app_decl(Z3_context c, Z3_app a);

    /**
       \brief Return the number of argument of an application. If \c t
       is an constant, then the number of arguments is 0.

       def_API('Z3_get_app_num_args', UINT, (_in(CONTEXT), _in(APP)))
    */
    unsigned Z3_API Z3_get_app_num_args(Z3_context c, Z3_app a);

    /**
       \brief Return the i-th argument of the given application.

       \pre i < Z3_get_app_num_args(c, a)

       def_API('Z3_get_app_arg', AST, (_in(CONTEXT), _in(APP), _in(UINT)))
    */
    Z3_ast Z3_API Z3_get_app_arg(Z3_context c, Z3_app a, unsigned i);

    /**
       \brief Compare terms.

       def_API('Z3_is_eq_ast', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    bool Z3_API Z3_is_eq_ast(Z3_context c, Z3_ast t1, Z3_ast t2);

    /**
        \brief Return a unique identifier for \c t.
        The identifier is unique up to structural equality. Thus, two ast nodes
        created by the same context and having the same children and same function symbols
        have the same identifiers. Ast nodes created in the same context, but having
        different children or different functions have different identifiers.
        Variables and quantifiers are also assigned different identifiers according to
        their structure.

        def_API('Z3_get_ast_id', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_ast_id(Z3_context c, Z3_ast t);

    /**
       \brief Return a hash code for the given AST.
       The hash code is structural. You can use Z3_get_ast_id interchangeably with
       this function.

       def_API('Z3_get_ast_hash', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_ast_hash(Z3_context c, Z3_ast a);

    /**
       \brief Return the sort of an AST node.

       The AST node must be a constant, application, numeral, bound variable, or quantifier.

       def_API('Z3_get_sort', SORT, (_in(CONTEXT), _in(AST)))
    */
    Z3_sort Z3_API Z3_get_sort(Z3_context c, Z3_ast a);

    /**
       \brief Return true if the given expression \c t is well sorted.

       def_API('Z3_is_well_sorted', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_well_sorted(Z3_context c, Z3_ast t);

    /**
       \brief Return \c Z3_L_TRUE if \c a is true, \c Z3_L_FALSE if it is false, and \c Z3_L_UNDEF otherwise.

       def_API('Z3_get_bool_value', INT, (_in(CONTEXT), _in(AST)))
    */
    Z3_lbool Z3_API Z3_get_bool_value(Z3_context c, Z3_ast a);

    /**
       \brief Return the kind of the given AST.

       def_API('Z3_get_ast_kind', UINT, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast_kind Z3_API Z3_get_ast_kind(Z3_context c, Z3_ast a);

    /**
      def_API('Z3_is_app', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_app(Z3_context c, Z3_ast a);

    /**
      def_API('Z3_is_numeral_ast', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_numeral_ast(Z3_context c, Z3_ast a);

    /**
       \brief Return true if the given AST is a real algebraic number.

       def_API('Z3_is_algebraic_number', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_algebraic_number(Z3_context c, Z3_ast a);

    /**
       \brief Convert an \c ast into an \c APP_AST. This is just type casting.

       \pre \code Z3_get_ast_kind(c, a) == \c Z3_APP_AST \endcode

       def_API('Z3_to_app', APP, (_in(CONTEXT), _in(AST)))
    */
    Z3_app Z3_API Z3_to_app(Z3_context c, Z3_ast a);

    /**
       \brief Convert an AST into a FUNC_DECL_AST. This is just type casting.

       \pre \code Z3_get_ast_kind(c, a) == Z3_FUNC_DECL_AST \endcode

       def_API('Z3_to_func_decl', FUNC_DECL, (_in(CONTEXT), _in(AST)))
    */
    Z3_func_decl Z3_API Z3_to_func_decl(Z3_context c, Z3_ast a);

    /**
       \brief Return numeral value, as a string of a numeric constant term

       \pre Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST

       def_API('Z3_get_numeral_string', STRING, (_in(CONTEXT), _in(AST)))
    */
    Z3_string Z3_API Z3_get_numeral_string(Z3_context c, Z3_ast a);

    /**
       \brief Return numeral as a string in decimal notation.
       The result has at most \c precision decimal places.

       \pre Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST || Z3_is_algebraic_number(c, a)

       def_API('Z3_get_numeral_decimal_string', STRING, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_string Z3_API Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned precision);

    /**
       \brief Return numeral as a double.

       \pre Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST || Z3_is_algebraic_number(c, a)

       def_API('Z3_get_numeral_double', DOUBLE, (_in(CONTEXT), _in(AST)))
    */
    double Z3_API Z3_get_numeral_double(Z3_context c, Z3_ast a);

    /**
       \brief Return the numerator (as a numeral AST) of a numeral AST of sort Real.

       \pre Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST

       def_API('Z3_get_numerator', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_get_numerator(Z3_context c, Z3_ast a);

    /**
       \brief Return the denominator (as a numeral AST) of a numeral AST of sort Real.

       \pre Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST

       def_API('Z3_get_denominator', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_get_denominator(Z3_context c, Z3_ast a);

    /**
       \brief Return numeral value, as a pair of 64 bit numbers if the representation fits.

       \param c logical context.
       \param a term.
       \param num numerator.
       \param den denominator.

       Return \c true if the numeral value fits in 64 bit numerals, \c false otherwise.

       \pre Z3_get_ast_kind(a) == Z3_NUMERAL_AST

       def_API('Z3_get_numeral_small', BOOL, (_in(CONTEXT), _in(AST), _out(INT64), _out(INT64)))
    */
    bool Z3_API Z3_get_numeral_small(Z3_context c, Z3_ast a, int64_t* num, int64_t* den);

    /**
       \brief Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine int. Return \c true if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string

       def_API('Z3_get_numeral_int', BOOL, (_in(CONTEXT), _in(AST), _out(INT)))
    */
    bool Z3_API Z3_get_numeral_int(Z3_context c, Z3_ast v, int* i);

    /**
       \brief Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine unsigned int. Return \c true if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string

       def_API('Z3_get_numeral_uint', BOOL, (_in(CONTEXT), _in(AST), _out(UINT)))
    */
    bool Z3_API Z3_get_numeral_uint(Z3_context c, Z3_ast v, unsigned* u);

    /**
       \brief Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine \c uint64_t int. Return \c true if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string

       def_API('Z3_get_numeral_uint64', BOOL, (_in(CONTEXT), _in(AST), _out(UINT64)))
    */
    bool Z3_API Z3_get_numeral_uint64(Z3_context c, Z3_ast v, uint64_t* u);

    /**
       \brief Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine \c int64_t int. Return \c true if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string

       def_API('Z3_get_numeral_int64', BOOL, (_in(CONTEXT), _in(AST), _out(INT64)))
    */
    bool Z3_API Z3_get_numeral_int64(Z3_context c, Z3_ast v, int64_t* i);

    /**
       \brief Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit as a rational number as machine \c int64_t int. Return \c true if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string

       def_API('Z3_get_numeral_rational_int64', BOOL, (_in(CONTEXT), _in(AST), _out(INT64), _out(INT64)))
    */
    bool Z3_API Z3_get_numeral_rational_int64(Z3_context c, Z3_ast v, int64_t* num, int64_t* den);

    /**
       \brief Return a lower bound for the given real algebraic number.
       The interval isolating the number is smaller than 1/10^precision.
       The result is a numeral AST of sort Real.

       \pre Z3_is_algebraic_number(c, a)

       def_API('Z3_get_algebraic_number_lower', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_get_algebraic_number_lower(Z3_context c, Z3_ast a, unsigned precision);

    /**
       \brief Return a upper bound for the given real algebraic number.
       The interval isolating the number is smaller than 1/10^precision.
       The result is a numeral AST of sort Real.

       \pre Z3_is_algebraic_number(c, a)

       def_API('Z3_get_algebraic_number_upper', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_get_algebraic_number_upper(Z3_context c, Z3_ast a, unsigned precision);

    /**
       \brief Convert a Z3_pattern into Z3_ast. This is just type casting.

       def_API('Z3_pattern_to_ast', AST, (_in(CONTEXT), _in(PATTERN)))
    */
    Z3_ast Z3_API Z3_pattern_to_ast(Z3_context c, Z3_pattern p);

    /**
        \brief Return number of terms in pattern.

        def_API('Z3_get_pattern_num_terms', UINT, (_in(CONTEXT), _in(PATTERN)))
    */
    unsigned Z3_API Z3_get_pattern_num_terms(Z3_context c, Z3_pattern p);

    /**
       \brief Return i'th ast in pattern.

       def_API('Z3_get_pattern', AST, (_in(CONTEXT), _in(PATTERN), _in(UINT)))
    */
    Z3_ast Z3_API Z3_get_pattern(Z3_context c, Z3_pattern p, unsigned idx);

    /**
       \brief Return index of de-Bruijn bound variable.

       \pre Z3_get_ast_kind(a) == Z3_VAR_AST

       def_API('Z3_get_index_value', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_index_value(Z3_context c, Z3_ast a);

    /**
       \brief Determine if an ast is a universal quantifier.

       def_API('Z3_is_quantifier_forall', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_quantifier_forall(Z3_context c, Z3_ast a);

    /**
       \brief Determine if ast is an existential quantifier.


       def_API('Z3_is_quantifier_exists', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_quantifier_exists(Z3_context c, Z3_ast a);

    /**
       \brief Determine if ast is a lambda expression.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_is_lambda', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_lambda(Z3_context c, Z3_ast a);

    /**
       \brief Obtain weight of quantifier.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_weight', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_quantifier_weight(Z3_context c, Z3_ast a);

    /**
       \brief Return number of patterns used in quantifier.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_num_patterns', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a);

    /**
       \brief Return i'th pattern.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_pattern_ast', PATTERN, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_pattern Z3_API Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned i);

    /**
       \brief Return number of no_patterns used in quantifier.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_num_no_patterns', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_quantifier_num_no_patterns(Z3_context c, Z3_ast a);

    /**
       \brief Return i'th no_pattern.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_no_pattern_ast', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_get_quantifier_no_pattern_ast(Z3_context c, Z3_ast a, unsigned i);

    /**
       \brief Return number of bound variables of quantifier.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_num_bound', UINT, (_in(CONTEXT), _in(AST)))
    */
    unsigned Z3_API Z3_get_quantifier_num_bound(Z3_context c, Z3_ast a);

    /**
       \brief Return symbol of the i'th bound variable.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_bound_name', SYMBOL, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_symbol Z3_API Z3_get_quantifier_bound_name(Z3_context c, Z3_ast a, unsigned i);

    /**
       \brief Return sort of the i'th bound variable.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_bound_sort', SORT, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_sort Z3_API Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned i);

    /**
       \brief Return body of quantifier.

       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST

       def_API('Z3_get_quantifier_body', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_get_quantifier_body(Z3_context c, Z3_ast a);

    /**
        \brief Interface to simplifier.

        Provides an interface to the AST simplifier used by Z3.
        It returns an AST object which is equal to the argument.
        The returned AST is simplified using algebraic simplification rules,
        such as constant propagation (propagating true/false over logical connectives).

        \sa Z3_simplify_ex

        def_API('Z3_simplify', AST, (_in(CONTEXT), _in(AST)))
    */
    Z3_ast Z3_API Z3_simplify(Z3_context c, Z3_ast a);

    /**
        \brief Interface to simplifier.

        Provides an interface to the AST simplifier used by Z3.
        This procedure is similar to #Z3_simplify, but the behavior of the simplifier
        can be configured using the given parameter set.

        \sa Z3_simplify
        \sa Z3_simplify_get_help
        \sa Z3_simplify_get_param_descrs

        def_API('Z3_simplify_ex', AST, (_in(CONTEXT), _in(AST), _in(PARAMS)))
    */
    Z3_ast Z3_API Z3_simplify_ex(Z3_context c, Z3_ast a, Z3_params p);

    /**
       \brief Return a string describing all available parameters.

        \sa Z3_simplify_ex
        \sa Z3_simplify_get_param_descrs

       def_API('Z3_simplify_get_help', STRING, (_in(CONTEXT),))
    */
    Z3_string Z3_API Z3_simplify_get_help(Z3_context c);

    /**
       \brief Return the parameter description set for the simplify procedure.

        \sa Z3_simplify_ex
        \sa Z3_simplify_get_help

       def_API('Z3_simplify_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT),))
    */
    Z3_param_descrs Z3_API Z3_simplify_get_param_descrs(Z3_context c);
    /*@}*/

    /** @name Modifiers */
    /*@{*/
    /**
       \brief Update the arguments of term \c a using the arguments \c args.
       The number of arguments \c num_args should coincide
       with the number of arguments to \c a.
       If \c a is a quantifier, then num_args has to be 1.

       def_API('Z3_update_term', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))
    */
    Z3_ast Z3_API Z3_update_term(Z3_context c, Z3_ast a, unsigned num_args, Z3_ast const args[]);

    /**
       \brief Substitute every occurrence of \ccode{from[i]} in \c a with \ccode{to[i]}, for \c i smaller than \c num_exprs.
       The result is the new AST. The arrays \c from and \c to must have size \c num_exprs.
       For every \c i smaller than \c num_exprs, we must have that sort of \ccode{from[i]} must be equal to sort of \ccode{to[i]}.

       def_API('Z3_substitute', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST), _in_array(2, AST)))
    */
    Z3_ast Z3_API Z3_substitute(Z3_context c,
                                Z3_ast a,
                                unsigned num_exprs,
                                Z3_ast const from[],
                                Z3_ast const to[]);

    /**
       \brief Substitute the free variables in \c a with the expressions in \c to.
       For every \c i smaller than \c num_exprs, the variable with de-Bruijn index \c i is replaced with term \ccode{to[i]}.

       def_API('Z3_substitute_vars', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))
    */
    Z3_ast Z3_API Z3_substitute_vars(Z3_context c,
                                     Z3_ast a,
                                     unsigned num_exprs,
                                     Z3_ast const to[]);

    /**
       \brief Translate/Copy the AST \c a from context \c source to context \c target.
       AST \c a must have been created using context \c source.
       \pre source != target

       def_API('Z3_translate', AST, (_in(CONTEXT), _in(AST), _in(CONTEXT)))
    */
    Z3_ast Z3_API Z3_translate(Z3_context source, Z3_ast a, Z3_context target);
    /*@}*/

    /** @name Models */
    /*@{*/

    /**
       \brief Create a fresh model object. It has reference count 0.

       def_API('Z3_mk_model', MODEL, (_in(CONTEXT),))
    */
    Z3_model Z3_API Z3_mk_model(Z3_context c);

    /**
       \brief Increment the reference counter of the given model.

       def_API('Z3_model_inc_ref', VOID, (_in(CONTEXT), _in(MODEL)))
    */
    void Z3_API Z3_model_inc_ref(Z3_context c, Z3_model m);

    /**
       \brief Decrement the reference counter of the given model.

       def_API('Z3_model_dec_ref', VOID, (_in(CONTEXT), _in(MODEL)))
    */
    void Z3_API Z3_model_dec_ref(Z3_context c, Z3_model m);

    /**
       \brief Evaluate the AST node \c t in the given model.
       Return \c true if succeeded, and store the result in \c v.

       If \c model_completion is \c true, then Z3 will assign an interpretation for any constant or function that does
       not have an interpretation in \c m. These constants and functions were essentially don't cares.

       If \c model_completion is \c false, then Z3 will not assign interpretations to constants for functions that do
       not have interpretations in \c m. Evaluation behaves as the identify function in this case.

       The evaluation may fail for the following reasons:

       - \c t contains a quantifier.

       - the model \c m is partial, that is, it doesn't have a complete interpretation for uninterpreted functions.
       That is, the option \ccode{MODEL_PARTIAL=true} was used.

       - \c t is type incorrect.

       - \c Z3_interrupt was invoked during evaluation.

       def_API('Z3_model_eval', BOOL, (_in(CONTEXT), _in(MODEL), _in(AST), _in(BOOL), _out(AST)))
    */
    Z3_bool_opt Z3_API Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion, Z3_ast * v);

    /**
       \brief Return the interpretation (i.e., assignment) of constant \c a in the model \c m.
       Return \c NULL, if the model does not assign an interpretation for \c a.
       That should be interpreted as: the value of \c a does not matter.

       \pre Z3_get_arity(c, a) == 0

       def_API('Z3_model_get_const_interp', AST, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL)))
    */
    Z3_ast_opt Z3_API Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);

    /**
       \brief Test if there exists an interpretation (i.e., assignment) for \c a in the model \c m.

       def_API('Z3_model_has_interp', BOOL, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL)))
    */
    bool Z3_API Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl a);

    /**
       \brief Return the interpretation of the function \c f in the model \c m.
       Return \c NULL, if the model does not assign an interpretation for \c f.
       That should be interpreted as: the \c f does not matter.

       \pre Z3_get_arity(c, f) > 0

       \remark Reference counting must be used to manage Z3_func_interp objects, even when the Z3_context was
       created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_model_get_func_interp', FUNC_INTERP, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL)))
    */
    Z3_func_interp_opt Z3_API Z3_model_get_func_interp(Z3_context c, Z3_model m, Z3_func_decl f);

    /**
       \brief Return the number of constants assigned by the given model.

       \sa Z3_model_get_const_decl

       def_API('Z3_model_get_num_consts', UINT, (_in(CONTEXT), _in(MODEL)))
    */
    unsigned Z3_API Z3_model_get_num_consts(Z3_context c, Z3_model m);

    /**
       \brief Return the i-th constant in the given model.

       \pre i < Z3_model_get_num_consts(c, m)

       \sa Z3_model_eval

       def_API('Z3_model_get_const_decl', FUNC_DECL, (_in(CONTEXT), _in(MODEL), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned i);

    /**
       \brief Return the number of function interpretations in the given model.

       A function interpretation is represented as a finite map and an 'else' value.
       Each entry in the finite map represents the value of a function given a set of arguments.

       def_API('Z3_model_get_num_funcs', UINT, (_in(CONTEXT), _in(MODEL)))
    */
    unsigned Z3_API Z3_model_get_num_funcs(Z3_context c, Z3_model m);

    /**
       \brief Return the declaration of the i-th function in the given model.

       \pre i < Z3_model_get_num_funcs(c, m)

       \sa Z3_model_get_num_funcs

       def_API('Z3_model_get_func_decl', FUNC_DECL, (_in(CONTEXT), _in(MODEL), _in(UINT)))
    */
    Z3_func_decl Z3_API Z3_model_get_func_decl(Z3_context c, Z3_model m, unsigned i);

    /**
       \brief Return the number of uninterpreted sorts that \c m assigns an interpretation to.

       Z3 also provides an interpretation for uninterpreted sorts used in a formula.
       The interpretation for a sort \c s is a finite set of distinct values. We say this finite set is
       the "universe" of \c s.

       \sa Z3_model_get_sort
       \sa Z3_model_get_sort_universe

       def_API('Z3_model_get_num_sorts', UINT, (_in(CONTEXT), _in(MODEL)))
    */
    unsigned Z3_API Z3_model_get_num_sorts(Z3_context c, Z3_model m);

    /**
       \brief Return a uninterpreted sort that \c m assigns an interpretation.

       \pre i < Z3_model_get_num_sorts(c, m)

       \sa Z3_model_get_num_sorts
       \sa Z3_model_get_sort_universe

       def_API('Z3_model_get_sort', SORT, (_in(CONTEXT), _in(MODEL), _in(UINT)))
    */
    Z3_sort Z3_API Z3_model_get_sort(Z3_context c, Z3_model m, unsigned i);

    /**
       \brief Return the finite set of distinct values that represent the interpretation for sort \c s.

       \sa Z3_model_get_num_sorts
       \sa Z3_model_get_sort

       def_API('Z3_model_get_sort_universe', AST_VECTOR, (_in(CONTEXT), _in(MODEL), _in(SORT)))
    */
    Z3_ast_vector Z3_API Z3_model_get_sort_universe(Z3_context c, Z3_model m, Z3_sort s);

    /**
       \brief translate model from context \c c to context \c dst.

       def_API('Z3_model_translate', MODEL, (_in(CONTEXT), _in(MODEL), _in(CONTEXT)))
    */
    Z3_model Z3_API Z3_model_translate(Z3_context c, Z3_model m, Z3_context dst);

    /**
       \brief The \ccode{(_ as-array f)} AST node is a construct for assigning interpretations for arrays in Z3.
       It is the array such that forall indices \c i we have that \ccode{(select (_ as-array f) i)} is equal to \ccode{(f i)}.
       This procedure returns \c true if the \c a is an \c as-array AST node.

       Z3 current solvers have minimal support for \c as_array nodes.

       \sa Z3_get_as_array_func_decl

       def_API('Z3_is_as_array', BOOL, (_in(CONTEXT), _in(AST)))
    */
    bool Z3_API Z3_is_as_array(Z3_context c, Z3_ast a);

    /**
       \brief Return the function declaration \c f associated with a \ccode{(_ as_array f)} node.

       \sa Z3_is_as_array

       def_API('Z3_get_as_array_func_decl', FUNC_DECL, (_in(CONTEXT), _in(AST)))
    */
    Z3_func_decl Z3_API Z3_get_as_array_func_decl(Z3_context c, Z3_ast a);

    /**
       \brief Create a fresh func_interp object, add it to a model for a specified function.
       It has reference count 0.

       \param c context
       \param m model
       \param f function declaration
       \param default_value default value for function interpretation

       def_API('Z3_add_func_interp', FUNC_INTERP, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL), _in(AST)))
    */
    Z3_func_interp Z3_API Z3_add_func_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast default_value);

    /**
       \brief Add a constant interpretation.

       def_API('Z3_add_const_interp', VOID, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL), _in(AST)))
     */
    void Z3_API Z3_add_const_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast a);

    /**
       \brief Increment the reference counter of the given Z3_func_interp object.

       def_API('Z3_func_interp_inc_ref', VOID, (_in(CONTEXT), _in(FUNC_INTERP)))
    */
    void Z3_API Z3_func_interp_inc_ref(Z3_context c, Z3_func_interp f);

    /**
       \brief Decrement the reference counter of the given Z3_func_interp object.

       def_API('Z3_func_interp_dec_ref', VOID, (_in(CONTEXT), _in(FUNC_INTERP)))
    */
    void Z3_API Z3_func_interp_dec_ref(Z3_context c, Z3_func_interp f);

    /**
       \brief Return the number of entries in the given function interpretation.

       A function interpretation is represented as a finite map and an 'else' value.
       Each entry in the finite map represents the value of a function given a set of arguments.
       This procedure return the number of element in the finite map of \c f.

       def_API('Z3_func_interp_get_num_entries', UINT, (_in(CONTEXT), _in(FUNC_INTERP)))
    */
    unsigned Z3_API Z3_func_interp_get_num_entries(Z3_context c, Z3_func_interp f);

    /**
       \brief Return a "point" of the given function interpretation. It represents the
       value of \c f in a particular point.

       \pre i < Z3_func_interp_get_num_entries(c, f)

       \sa Z3_func_interp_get_num_entries

       def_API('Z3_func_interp_get_entry', FUNC_ENTRY, (_in(CONTEXT), _in(FUNC_INTERP), _in(UINT)))
    */
    Z3_func_entry Z3_API Z3_func_interp_get_entry(Z3_context c, Z3_func_interp f, unsigned i);

    /**
       \brief Return the 'else' value of the given function interpretation.

       A function interpretation is represented as a finite map and an 'else' value.
       This procedure returns the 'else' value.

       def_API('Z3_func_interp_get_else', AST, (_in(CONTEXT), _in(FUNC_INTERP)))
    */
    Z3_ast Z3_API Z3_func_interp_get_else(Z3_context c, Z3_func_interp f);

    /**
       \brief Return the 'else' value of the given function interpretation.

       A function interpretation is represented as a finite map and an 'else' value.
       This procedure can be used to update the 'else' value.

       def_API('Z3_func_interp_set_else', VOID, (_in(CONTEXT), _in(FUNC_INTERP), _in(AST)))
    */
    void Z3_API Z3_func_interp_set_else(Z3_context c, Z3_func_interp f, Z3_ast else_value);

    /**
       \brief Return the arity (number of arguments) of the given function interpretation.

       def_API('Z3_func_interp_get_arity', UINT, (_in(CONTEXT), _in(FUNC_INTERP)))
    */
    unsigned Z3_API Z3_func_interp_get_arity(Z3_context c, Z3_func_interp f);

    /**
       \brief add a function entry to a function interpretation.

       \param c logical context
       \param fi a function interpretation to be updated.
       \param args list of arguments. They should be constant values (such as integers) and be of the same types as the domain of the function.
       \param value value of the function when the parameters match args.

       It is assumed that entries added to a function cover disjoint arguments.
       If an two entries are added with the same arguments, only the second insertion survives and the
       first inserted entry is removed.

       def_API('Z3_func_interp_add_entry', VOID, (_in(CONTEXT), _in(FUNC_INTERP), _in(AST_VECTOR), _in(AST)))
     */
    void Z3_API Z3_func_interp_add_entry(Z3_context c, Z3_func_interp fi, Z3_ast_vector args, Z3_ast value);

    /**
       \brief Increment the reference counter of the given Z3_func_entry object.

       def_API('Z3_func_entry_inc_ref', VOID, (_in(CONTEXT), _in(FUNC_ENTRY)))
    */
    void Z3_API Z3_func_entry_inc_ref(Z3_context c, Z3_func_entry e);

    /**
       \brief Decrement the reference counter of the given Z3_func_entry object.

       def_API('Z3_func_entry_dec_ref', VOID, (_in(CONTEXT), _in(FUNC_ENTRY)))
    */
    void Z3_API Z3_func_entry_dec_ref(Z3_context c, Z3_func_entry e);

    /**
       \brief Return the value of this point.

       A Z3_func_entry object represents an element in the finite map used to encode
       a function interpretation.

       \sa Z3_func_interp_get_entry

       def_API('Z3_func_entry_get_value', AST, (_in(CONTEXT), _in(FUNC_ENTRY)))
    */
    Z3_ast Z3_API Z3_func_entry_get_value(Z3_context c, Z3_func_entry e);

    /**
       \brief Return the number of arguments in a Z3_func_entry object.

       \sa Z3_func_interp_get_entry

       def_API('Z3_func_entry_get_num_args', UINT, (_in(CONTEXT), _in(FUNC_ENTRY)))
    */
    unsigned Z3_API Z3_func_entry_get_num_args(Z3_context c, Z3_func_entry e);

    /**
       \brief Return an argument of a Z3_func_entry object.

       \pre i < Z3_func_entry_get_num_args(c, e)

       \sa Z3_func_interp_get_entry

       def_API('Z3_func_entry_get_arg', AST, (_in(CONTEXT), _in(FUNC_ENTRY), _in(UINT)))
    */
    Z3_ast Z3_API Z3_func_entry_get_arg(Z3_context c, Z3_func_entry e, unsigned i);
    /*@}*/

    /** @name Interaction logging */
    /*@{*/
    /**
       \brief Log interaction to a file.

       extra_API('Z3_open_log', INT, (_in(STRING),))
    */
    bool Z3_API Z3_open_log(Z3_string filename);

    /**
       \brief Append user-defined string to interaction log.

       The interaction log is opened using Z3_open_log.
       It contains the formulas that are checked using Z3.
       You can use this command to append comments, for instance.

       extra_API('Z3_append_log', VOID, (_in(STRING),))
    */
    void Z3_API Z3_append_log(Z3_string string);

    /**
       \brief Close interaction log.

       extra_API('Z3_close_log', VOID, ())
    */
    void Z3_API Z3_close_log(void);

    /**
       \brief Enable/disable printing warning messages to the console.

       Warnings are printed after passing \c true, warning messages are
       suppressed after calling this method with \c false.

       def_API('Z3_toggle_warning_messages', VOID, (_in(BOOL),))
    */
    void Z3_API Z3_toggle_warning_messages(bool enabled);
    /*@}*/

    /** @name String conversion */
    /*@{*/
    /**
       \brief Select mode for the format used for pretty-printing AST nodes.

       The default mode for pretty printing AST nodes is to produce
       SMT-LIB style output where common subexpressions are printed
       at each occurrence. The mode is called Z3_PRINT_SMTLIB_FULL.
       To print shared common subexpressions only once,
       use the Z3_PRINT_LOW_LEVEL mode.
       To print in way that conforms to SMT-LIB standards and uses let
       expressions to share common sub-expressions use Z3_PRINT_SMTLIB2_COMPLIANT.

       \sa Z3_ast_to_string
       \sa Z3_pattern_to_string
       \sa Z3_func_decl_to_string

       def_API('Z3_set_ast_print_mode', VOID, (_in(CONTEXT), _in(PRINT_MODE)))
    */
    void Z3_API Z3_set_ast_print_mode(Z3_context c, Z3_ast_print_mode mode);

    /**
       \brief Convert the given AST node into a string.

       \warning The result buffer is statically allocated by Z3. It will
       be automatically deallocated when #Z3_del_context is invoked.
       So, the buffer is invalidated in the next call to \c Z3_ast_to_string.

       \sa Z3_pattern_to_string
       \sa Z3_sort_to_string

       def_API('Z3_ast_to_string', STRING, (_in(CONTEXT), _in(AST)))
    */
    Z3_string Z3_API Z3_ast_to_string(Z3_context c, Z3_ast a);

    /**
      def_API('Z3_pattern_to_string', STRING, (_in(CONTEXT), _in(PATTERN)))
    */
    Z3_string Z3_API Z3_pattern_to_string(Z3_context c, Z3_pattern p);

    /**
      def_API('Z3_sort_to_string', STRING, (_in(CONTEXT), _in(SORT)))
    */
    Z3_string Z3_API Z3_sort_to_string(Z3_context c, Z3_sort s);

    /**
      def_API('Z3_func_decl_to_string', STRING, (_in(CONTEXT), _in(FUNC_DECL)))
    */
    Z3_string Z3_API Z3_func_decl_to_string(Z3_context c, Z3_func_decl d);

    /**
       \brief Convert the given model into a string.

       \warning The result buffer is statically allocated by Z3. It will
       be automatically deallocated when #Z3_del_context is invoked.
       So, the buffer is invalidated in the next call to \c Z3_model_to_string.

       def_API('Z3_model_to_string', STRING, (_in(CONTEXT), _in(MODEL)))
    */
    Z3_string Z3_API Z3_model_to_string(Z3_context c, Z3_model m);

    /**
       \brief Convert the given benchmark into SMT-LIB formatted string.

       \warning The result buffer is statically allocated by Z3. It will
       be automatically deallocated when #Z3_del_context is invoked.
       So, the buffer is invalidated in the next call to \c Z3_benchmark_to_smtlib_string.

       \param c - context.
       \param name - name of benchmark. The argument is optional.
       \param logic - the benchmark logic.
       \param status - the status string (sat, unsat, or unknown)
       \param attributes - other attributes, such as source, difficulty or category.
       \param num_assumptions - number of assumptions.
       \param assumptions - auxiliary assumptions.
       \param formula - formula to be checked for consistency in conjunction with assumptions.

       def_API('Z3_benchmark_to_smtlib_string', STRING, (_in(CONTEXT), _in(STRING), _in(STRING), _in(STRING), _in(STRING), _in(UINT), _in_array(5, AST), _in(AST)))
    */
    Z3_string Z3_API Z3_benchmark_to_smtlib_string(Z3_context c,
                                                   Z3_string name,
                                                   Z3_string logic,
                                                   Z3_string status,
                                                   Z3_string attributes,
                                                   unsigned num_assumptions,
                                                   Z3_ast const assumptions[],
                                                   Z3_ast formula);

    /*@}*/

    /** @name Parser interface */
    /*@{*/
    /**
       \brief Parse the given string using the SMT-LIB2 parser.

       It returns a formula comprising of the conjunction of assertions in the scope
       (up to push/pop) at the end of the string.

       def_API('Z3_parse_smtlib2_string', AST_VECTOR, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT), _in(UINT), _in_array(5, SYMBOL), _in_array(5, FUNC_DECL)))
    */
    Z3_ast_vector Z3_API Z3_parse_smtlib2_string(Z3_context c,
                                          Z3_string str,
                                          unsigned num_sorts,
                                          Z3_symbol const sort_names[],
                                          Z3_sort const sorts[],
                                          unsigned num_decls,
                                          Z3_symbol const decl_names[],
                                          Z3_func_decl const decls[]);

    /**
       \brief Similar to #Z3_parse_smtlib2_string, but reads the benchmark from a file.

       def_API('Z3_parse_smtlib2_file', AST_VECTOR, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT), _in(UINT), _in_array(5, SYMBOL), _in_array(5, FUNC_DECL)))
    */
    Z3_ast_vector Z3_API Z3_parse_smtlib2_file(Z3_context c,
                                        Z3_string file_name,
                                        unsigned num_sorts,
                                        Z3_symbol const sort_names[],
                                        Z3_sort const sorts[],
                                        unsigned num_decls,
                                        Z3_symbol const decl_names[],
                                        Z3_func_decl const decls[]);


    /**
       \brief Parse and evaluate and SMT-LIB2 command sequence. The state from a previous call is saved so the next
              evaluation builds on top of the previous call.

       \returns output generated from processing commands.

       def_API('Z3_eval_smtlib2_string', STRING, (_in(CONTEXT), _in(STRING),))
    */

    Z3_string Z3_API Z3_eval_smtlib2_string(Z3_context, Z3_string str);
    
    /*@}*/

    /** @name Error Handling */
    /*@{*/
#ifndef SAFE_ERRORS
    /**
       \brief Return the error code for the last API call.

       A call to a Z3 function may return a non Z3_OK error code,
       when it is not used correctly.

       \sa Z3_set_error_handler

       def_API('Z3_get_error_code', UINT, (_in(CONTEXT), ))
    */
    Z3_error_code Z3_API Z3_get_error_code(Z3_context c);

    /**
       \brief Register a Z3 error handler.

       A call to a Z3 function may return a non Z3_OK error code, when
       it is not used correctly.  An error handler can be registered
       and will be called in this case.  To disable the use of the
       error handler, simply register with \c h=NULL.

       \warning Log files, created using #Z3_open_log, may be potentially incomplete/incorrect if error handlers are used.

       \sa Z3_get_error_code
    */
    void Z3_API Z3_set_error_handler(Z3_context c, Z3_error_handler h);
#endif

    /**
       \brief Set an error.

       def_API('Z3_set_error', VOID, (_in(CONTEXT), _in(ERROR_CODE)))
    */
    void Z3_API Z3_set_error(Z3_context c, Z3_error_code e);

    /**
       \brief Return a string describing the given error code.

       def_API('Z3_get_error_msg', STRING, (_in(CONTEXT), _in(ERROR_CODE)))
    */
    Z3_string Z3_API Z3_get_error_msg(Z3_context c, Z3_error_code err);

    /*@}*/

    /** @name Miscellaneous */
    /*@{*/

    /**
       \brief Return Z3 version number information.

       def_API('Z3_get_version', VOID, (_out(UINT), _out(UINT), _out(UINT), _out(UINT)))
    */
    void Z3_API Z3_get_version(unsigned * major, unsigned * minor, unsigned * build_number, unsigned * revision_number);

    /**
        \brief Return a string that fully describes the version of Z3 in use.

        def_API('Z3_get_full_version', STRING, ())
    */
    Z3_string Z3_API Z3_get_full_version(void);

    /**
       \brief Enable tracing messages tagged as \c tag when Z3 is compiled in debug mode.
       It is a NOOP otherwise

       def_API('Z3_enable_trace', VOID, (_in(STRING),))
    */
    void Z3_API Z3_enable_trace(Z3_string tag);

    /**
       \brief Disable tracing messages tagged as \c tag when Z3 is compiled in debug mode.
       It is a NOOP otherwise

       def_API('Z3_disable_trace', VOID, (_in(STRING),))
    */
    void Z3_API Z3_disable_trace(Z3_string tag);

    /**
       \brief Reset all allocated resources.

       Use this facility on out-of memory errors.
       It allows discharging the previous state and resuming afresh.
       Any pointers previously returned by the API
       become invalid.

       def_API('Z3_reset_memory', VOID, ())
    */
    void Z3_API Z3_reset_memory(void);

    /**
       \brief Destroy all allocated resources.

       Any pointers previously returned by the API become invalid.
       Can be used for memory leak detection.

       def_API('Z3_finalize_memory', VOID, ())
    */
    void Z3_API Z3_finalize_memory(void);
    /*@}*/

    /** @name Goals */
    /*@{*/
    /**
       \brief Create a goal (aka problem). A goal is essentially a set
       of formulas, that can be solved and/or transformed using
       tactics and solvers.

       If models == true, then model generation is enabled for the new goal.

       If unsat_cores == true, then unsat core generation is enabled for the new goal.

       If proofs == true, then proof generation is enabled for the new goal. Remark, the
       Z3 context c must have been created with proof generation support.

       \remark Reference counting must be used to manage goals, even when the Z3_context was
       created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_goal', GOAL, (_in(CONTEXT), _in(BOOL), _in(BOOL), _in(BOOL)))
    */
    Z3_goal Z3_API Z3_mk_goal(Z3_context c, bool models, bool unsat_cores, bool proofs);

    /**
       \brief Increment the reference counter of the given goal.

       def_API('Z3_goal_inc_ref', VOID, (_in(CONTEXT), _in(GOAL)))
    */
    void Z3_API Z3_goal_inc_ref(Z3_context c, Z3_goal g);

    /**
       \brief Decrement the reference counter of the given goal.

       def_API('Z3_goal_dec_ref', VOID, (_in(CONTEXT), _in(GOAL)))
    */
    void Z3_API Z3_goal_dec_ref(Z3_context c, Z3_goal g);

    /**
       \brief Return the "precision" of the given goal. Goals can be transformed using over and under approximations.
       A under approximation is applied when the objective is to find a model for a given goal.
       An over approximation is applied when the objective is to find a proof for a given goal.

       def_API('Z3_goal_precision', UINT, (_in(CONTEXT), _in(GOAL)))
    */
    Z3_goal_prec Z3_API Z3_goal_precision(Z3_context c, Z3_goal g);

    /**
       \brief Add a new formula \c a to the given goal.
        The formula is split according to the following procedure that is applied
        until a fixed-point:
           Conjunctions are split into separate formulas.
           Negations are distributed over disjunctions, resulting in separate formulas.
        If the goal is \c false, adding new formulas is a no-op.
        If the formula \c a is \c true, then nothing is added.
        If the formula \c a is \c false, then the entire goal is replaced by the formula \c false.

       def_API('Z3_goal_assert', VOID, (_in(CONTEXT), _in(GOAL), _in(AST)))
    */
    void Z3_API Z3_goal_assert(Z3_context c, Z3_goal g, Z3_ast a);

    /**
       \brief Return true if the given goal contains the formula \c false.

       def_API('Z3_goal_inconsistent', BOOL, (_in(CONTEXT), _in(GOAL)))
    */
    bool Z3_API Z3_goal_inconsistent(Z3_context c, Z3_goal g);

    /**
       \brief Return the depth of the given goal. It tracks how many transformations were applied to it.

       def_API('Z3_goal_depth', UINT, (_in(CONTEXT), _in(GOAL)))
    */
    unsigned Z3_API Z3_goal_depth(Z3_context c, Z3_goal g);

    /**
       \brief Erase all formulas from the given goal.

       def_API('Z3_goal_reset', VOID, (_in(CONTEXT), _in(GOAL)))
    */
    void Z3_API Z3_goal_reset(Z3_context c, Z3_goal g);

    /**
       \brief Return the number of formulas in the given goal.

       def_API('Z3_goal_size', UINT, (_in(CONTEXT), _in(GOAL)))
    */
    unsigned Z3_API Z3_goal_size(Z3_context c, Z3_goal g);

    /**
       \brief Return a formula from the given goal.

       \pre idx < Z3_goal_size(c, g)

       def_API('Z3_goal_formula', AST, (_in(CONTEXT), _in(GOAL), _in(UINT)))
    */
    Z3_ast Z3_API Z3_goal_formula(Z3_context c, Z3_goal g, unsigned idx);

    /**
       \brief Return the number of formulas, subformulas and terms in the given goal.

       def_API('Z3_goal_num_exprs', UINT, (_in(CONTEXT), _in(GOAL)))
    */
    unsigned Z3_API Z3_goal_num_exprs(Z3_context c, Z3_goal g);

    /**
       \brief Return true if the goal is empty, and it is precise or the product of a under approximation.

       def_API('Z3_goal_is_decided_sat', BOOL, (_in(CONTEXT), _in(GOAL)))
    */
    bool Z3_API Z3_goal_is_decided_sat(Z3_context c, Z3_goal g);

    /**
       \brief Return true if the goal contains false, and it is precise or the product of an over approximation.

       def_API('Z3_goal_is_decided_unsat', BOOL, (_in(CONTEXT), _in(GOAL)))
    */
    bool Z3_API Z3_goal_is_decided_unsat(Z3_context c, Z3_goal g);

    /**
       \brief Copy a goal \c g from the context \c source to the context \c target.

       def_API('Z3_goal_translate', GOAL, (_in(CONTEXT), _in(GOAL), _in(CONTEXT)))
    */
    Z3_goal Z3_API Z3_goal_translate(Z3_context source, Z3_goal g, Z3_context target);

    /**
       \brief Convert a model of the formulas of a goal to a model of an original goal.
       The model may be null, in which case the returned model is valid if the goal was
       established satisfiable.

       def_API('Z3_goal_convert_model', MODEL, (_in(CONTEXT), _in(GOAL), _in(MODEL)))
    */
    Z3_model Z3_API Z3_goal_convert_model(Z3_context c, Z3_goal g, Z3_model m);

    /**
       \brief Convert a goal into a string.

       def_API('Z3_goal_to_string', STRING, (_in(CONTEXT), _in(GOAL)))
    */
    Z3_string Z3_API Z3_goal_to_string(Z3_context c, Z3_goal g);

    /**
       \brief Convert a goal into a DIMACS formatted string.
       The goal must be in CNF. You can convert a goal to CNF
       by applying the tseitin-cnf tactic. Bit-vectors are not automatically
       converted to Booleans either, so if the caller intends to
       preserve satisfiability, it should apply bit-blasting tactics.
       Quantifiers and theory atoms will not be encoded.

       def_API('Z3_goal_to_dimacs_string', STRING, (_in(CONTEXT), _in(GOAL)))
    */
    Z3_string Z3_API Z3_goal_to_dimacs_string(Z3_context c, Z3_goal g);

    /*@}*/

    /** @name Tactics and Probes */
    /*@{*/
    /**
       \brief Return a tactic associated with the given name.
       The complete list of tactics may be obtained using the procedures #Z3_get_num_tactics and #Z3_get_tactic_name.
       It may also be obtained using the command \ccode{(help-tactic)} in the SMT 2.0 front-end.

       Tactics are the basic building block for creating custom solvers for specific problem domains.

       def_API('Z3_mk_tactic', TACTIC, (_in(CONTEXT), _in(STRING)))
    */
    Z3_tactic Z3_API Z3_mk_tactic(Z3_context c, Z3_string name);

    /**
       \brief Increment the reference counter of the given tactic.

       def_API('Z3_tactic_inc_ref', VOID, (_in(CONTEXT), _in(TACTIC)))
    */
    void Z3_API Z3_tactic_inc_ref(Z3_context c, Z3_tactic t);

    /**
       \brief Decrement the reference counter of the given tactic.

       def_API('Z3_tactic_dec_ref', VOID, (_in(CONTEXT), _in(TACTIC)))
    */
    void Z3_API Z3_tactic_dec_ref(Z3_context c, Z3_tactic g);

    /**
       \brief Return a probe associated with the given name.
       The complete list of probes may be obtained using the procedures #Z3_get_num_probes and #Z3_get_probe_name.
       It may also be obtained using the command \ccode{(help-tactic)} in the SMT 2.0 front-end.

       Probes are used to inspect a goal (aka problem) and collect information that may be used to decide
       which solver and/or preprocessing step will be used.

       def_API('Z3_mk_probe', PROBE, (_in(CONTEXT), _in(STRING)))
    */
    Z3_probe Z3_API Z3_mk_probe(Z3_context c, Z3_string name);

    /**
       \brief Increment the reference counter of the given probe.

       def_API('Z3_probe_inc_ref', VOID, (_in(CONTEXT), _in(PROBE)))
    */
    void Z3_API Z3_probe_inc_ref(Z3_context c, Z3_probe p);

    /**
       \brief Decrement the reference counter of the given probe.

       def_API('Z3_probe_dec_ref', VOID, (_in(CONTEXT), _in(PROBE)))
    */
    void Z3_API Z3_probe_dec_ref(Z3_context c, Z3_probe p);

    /**
       \brief Return a tactic that applies \c t1 to a given goal and \c t2
       to every subgoal produced by t1.

       def_API('Z3_tactic_and_then', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(TACTIC)))
    */
    Z3_tactic Z3_API Z3_tactic_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);

    /**
       \brief Return a tactic that first applies \c t1 to a given goal,
       if it fails then returns the result of \c t2 applied to the given goal.

       def_API('Z3_tactic_or_else', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(TACTIC)))
    */
    Z3_tactic Z3_API Z3_tactic_or_else(Z3_context c, Z3_tactic t1, Z3_tactic t2);

    /**
       \brief Return a tactic that applies the given tactics in parallel.

       def_API('Z3_tactic_par_or', TACTIC, (_in(CONTEXT), _in(UINT), _in_array(1, TACTIC)))
    */
    Z3_tactic Z3_API Z3_tactic_par_or(Z3_context c, unsigned num, Z3_tactic const ts[]);

    /**
       \brief Return a tactic that applies \c t1 to a given goal and then \c t2
       to every subgoal produced by t1. The subgoals are processed in parallel.

       def_API('Z3_tactic_par_and_then', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(TACTIC)))
    */
    Z3_tactic Z3_API Z3_tactic_par_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);

    /**
       \brief Return a tactic that applies \c t to a given goal for \c ms milliseconds.
       If \c t does not terminate in \c ms milliseconds, then it fails.

       def_API('Z3_tactic_try_for', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(UINT)))
     */
    Z3_tactic Z3_API Z3_tactic_try_for(Z3_context c, Z3_tactic t, unsigned ms);

    /**
       \brief Return a tactic that applies \c t to a given goal is the probe \c p evaluates to true.
       If \c p evaluates to false, then the new tactic behaves like the skip tactic.

       def_API('Z3_tactic_when', TACTIC, (_in(CONTEXT), _in(PROBE), _in(TACTIC)))
    */
    Z3_tactic Z3_API Z3_tactic_when(Z3_context c, Z3_probe p, Z3_tactic t);

    /**
       \brief Return a tactic that applies \c t1 to a given goal if the probe \c p evaluates to true,
       and \c t2 if \c p evaluates to false.

       def_API('Z3_tactic_cond', TACTIC, (_in(CONTEXT), _in(PROBE), _in(TACTIC), _in(TACTIC)))
     */
    Z3_tactic Z3_API Z3_tactic_cond(Z3_context c, Z3_probe p, Z3_tactic t1, Z3_tactic t2);

    /**
       \brief Return a tactic that keeps applying \c t until the goal is not modified anymore or the maximum
       number of iterations \c max is reached.

       def_API('Z3_tactic_repeat', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(UINT)))
    */
    Z3_tactic Z3_API Z3_tactic_repeat(Z3_context c, Z3_tactic t, unsigned max);

    /**
       \brief Return a tactic that just return the given goal.

       def_API('Z3_tactic_skip', TACTIC, (_in(CONTEXT),))
    */
    Z3_tactic Z3_API Z3_tactic_skip(Z3_context c);

    /**
       \brief Return a tactic that always fails.

       def_API('Z3_tactic_fail', TACTIC, (_in(CONTEXT),))
    */
    Z3_tactic Z3_API Z3_tactic_fail(Z3_context c);

    /**
       \brief Return a tactic that fails if the probe \c p evaluates to false.

       def_API('Z3_tactic_fail_if', TACTIC, (_in(CONTEXT), _in(PROBE)))
    */
    Z3_tactic Z3_API Z3_tactic_fail_if(Z3_context c, Z3_probe p);

    /**
       \brief Return a tactic that fails if the goal is not trivially satisfiable (i.e., empty) or
       trivially unsatisfiable (i.e., contains false).

       def_API('Z3_tactic_fail_if_not_decided', TACTIC, (_in(CONTEXT),))
    */
    Z3_tactic Z3_API Z3_tactic_fail_if_not_decided(Z3_context c);

    /**
       \brief Return a tactic that applies \c t using the given set of parameters.

       def_API('Z3_tactic_using_params', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(PARAMS)))
    */
    Z3_tactic Z3_API Z3_tactic_using_params(Z3_context c, Z3_tactic t, Z3_params p);

    /**
       \brief Return a probe that always evaluates to val.

       def_API('Z3_probe_const', PROBE, (_in(CONTEXT), _in(DOUBLE)))
    */
    Z3_probe Z3_API Z3_probe_const(Z3_context x, double val);

    /**
       \brief Return a probe that evaluates to "true" when the value returned by \c p1 is less than the value returned by \c p2.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_lt', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_lt(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when the value returned by \c p1 is greater than the value returned by \c p2.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_gt', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_gt(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when the value returned by \c p1 is less than or equal to the value returned by \c p2.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_le', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_le(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when the value returned by \c p1 is greater than or equal to the value returned by \c p2.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_ge', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_ge(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when the value returned by \c p1 is equal to the value returned by \c p2.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_eq', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_eq(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when \c p1 and \c p2 evaluates to true.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_and', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_and(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when \c p1 or \c p2 evaluates to true.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_or', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_or(Z3_context x, Z3_probe p1, Z3_probe p2);

    /**
       \brief Return a probe that evaluates to "true" when \c p does not evaluate to true.

       \remark For probes, "true" is any value different from 0.0.

       def_API('Z3_probe_not', PROBE, (_in(CONTEXT), _in(PROBE)))
    */
    Z3_probe Z3_API Z3_probe_not(Z3_context x, Z3_probe p);

    /**
       \brief Return the number of builtin tactics available in Z3.

       def_API('Z3_get_num_tactics', UINT, (_in(CONTEXT),))
    */
    unsigned Z3_API Z3_get_num_tactics(Z3_context c);

    /**
       \brief Return the name of the idx tactic.

       \pre i < Z3_get_num_tactics(c)

       def_API('Z3_get_tactic_name', STRING, (_in(CONTEXT), _in(UINT)))
    */
    Z3_string Z3_API Z3_get_tactic_name(Z3_context c, unsigned i);

    /**
       \brief Return the number of builtin probes available in Z3.

       def_API('Z3_get_num_probes', UINT, (_in(CONTEXT),))
    */
    unsigned Z3_API Z3_get_num_probes(Z3_context c);

    /**
       \brief Return the name of the i probe.

       \pre i < Z3_get_num_probes(c)

       def_API('Z3_get_probe_name', STRING, (_in(CONTEXT), _in(UINT)))
    */
    Z3_string Z3_API Z3_get_probe_name(Z3_context c, unsigned i);

    /**
       \brief Return a string containing a description of parameters accepted by the given tactic.

       def_API('Z3_tactic_get_help', STRING, (_in(CONTEXT), _in(TACTIC)))
    */
    Z3_string Z3_API Z3_tactic_get_help(Z3_context c, Z3_tactic t);

    /**
       \brief Return the parameter description set for the given tactic object.

       def_API('Z3_tactic_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(TACTIC)))
    */
    Z3_param_descrs Z3_API Z3_tactic_get_param_descrs(Z3_context c, Z3_tactic t);

    /**
       \brief Return a string containing a description of the tactic with the given name.

       def_API('Z3_tactic_get_descr', STRING, (_in(CONTEXT), _in(STRING)))
    */
    Z3_string Z3_API Z3_tactic_get_descr(Z3_context c, Z3_string name);

    /**
       \brief Return a string containing a description of the probe with the given name.

       def_API('Z3_probe_get_descr', STRING, (_in(CONTEXT), _in(STRING)))
    */
    Z3_string Z3_API Z3_probe_get_descr(Z3_context c, Z3_string name);

    /**
       \brief Execute the probe over the goal. The probe always produce a double value.
       "Boolean" probes return 0.0 for false, and a value different from 0.0 for true.

       def_API('Z3_probe_apply', DOUBLE, (_in(CONTEXT), _in(PROBE), _in(GOAL)))
    */
    double Z3_API Z3_probe_apply(Z3_context c, Z3_probe p, Z3_goal g);

    /**
       \brief Apply tactic \c t to the goal \c g.

       def_API('Z3_tactic_apply', APPLY_RESULT, (_in(CONTEXT), _in(TACTIC), _in(GOAL)))
    */
    Z3_apply_result Z3_API Z3_tactic_apply(Z3_context c, Z3_tactic t, Z3_goal g);

    /**
       \brief Apply tactic \c t to the goal \c g using the parameter set \c p.

       def_API('Z3_tactic_apply_ex', APPLY_RESULT, (_in(CONTEXT), _in(TACTIC), _in(GOAL), _in(PARAMS)))
    */
    Z3_apply_result Z3_API Z3_tactic_apply_ex(Z3_context c, Z3_tactic t, Z3_goal g, Z3_params p);

    /**
       \brief Increment the reference counter of the given \c Z3_apply_result object.

       def_API('Z3_apply_result_inc_ref', VOID, (_in(CONTEXT), _in(APPLY_RESULT)))
    */
    void Z3_API Z3_apply_result_inc_ref(Z3_context c, Z3_apply_result r);

    /**
       \brief Decrement the reference counter of the given \c Z3_apply_result object.

       def_API('Z3_apply_result_dec_ref', VOID, (_in(CONTEXT), _in(APPLY_RESULT)))
    */
    void Z3_API Z3_apply_result_dec_ref(Z3_context c, Z3_apply_result r);

    /**
       \brief Convert the \c Z3_apply_result object returned by #Z3_tactic_apply into a string.

       def_API('Z3_apply_result_to_string', STRING, (_in(CONTEXT), _in(APPLY_RESULT)))
    */
    Z3_string Z3_API Z3_apply_result_to_string(Z3_context c, Z3_apply_result r);

    /**
       \brief Return the number of subgoals in the \c Z3_apply_result object returned by #Z3_tactic_apply.

       def_API('Z3_apply_result_get_num_subgoals', UINT, (_in(CONTEXT), _in(APPLY_RESULT)))
    */
    unsigned Z3_API Z3_apply_result_get_num_subgoals(Z3_context c, Z3_apply_result r);

    /**
       \brief Return one of the subgoals in the \c Z3_apply_result object returned by #Z3_tactic_apply.

       \pre i < Z3_apply_result_get_num_subgoals(c, r)

       def_API('Z3_apply_result_get_subgoal', GOAL, (_in(CONTEXT), _in(APPLY_RESULT), _in(UINT)))
    */
    Z3_goal Z3_API Z3_apply_result_get_subgoal(Z3_context c, Z3_apply_result r, unsigned i);

    /*@}*/

    /** @name Solvers*/
    /*@{*/
    /**
       \brief Create a new solver. This solver is a "combined solver" (see
       combined_solver module) that internally uses a non-incremental (solver1) and an
       incremental solver (solver2). This combined solver changes its behaviour based
       on how it is used and how its parameters are set.

       If the solver is used in a non incremental way (i.e. no calls to
       #Z3_solver_push() or #Z3_solver_pop(), and no calls to
       #Z3_solver_assert() or #Z3_solver_assert_and_track() after checking
       satisfiability without an intervening #Z3_solver_reset()) then solver1
       will be used. This solver will apply Z3's "default" tactic.

       The "default" tactic will attempt to probe the logic used by the
       assertions and will apply a specialized tactic if one is supported.
       Otherwise the general `(and-then simplify smt)` tactic will be used.

       If the solver is used in an incremental way then the combined solver
       will switch to using solver2 (which behaves similarly to the general
       "smt" tactic).

       Note however it is possible to set the `solver2_timeout`,
       `solver2_unknown`, and `ignore_solver1` parameters of the combined
       solver to change its behaviour.

       The function #Z3_solver_get_model retrieves a model if the
       assertions is satisfiable (i.e., the result is \c
       Z3_L_TRUE) and model construction is enabled.
       The function #Z3_solver_get_model can also be used even
       if the result is \c Z3_L_UNDEF, but the returned model
       is not guaranteed to satisfy quantified assertions.

       \remark User must use #Z3_solver_inc_ref and #Z3_solver_dec_ref to manage solver objects.
       Even if the context was created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_solver', SOLVER, (_in(CONTEXT),))
    */
    Z3_solver Z3_API Z3_mk_solver(Z3_context c);

    /**
       \brief Create a new incremental solver.

       This is equivalent to applying the "smt" tactic.

       Unlike #Z3_mk_solver() this solver
         - Does not attempt to apply any logic specific tactics.
         - Does not change its behaviour based on whether it used
           incrementally/non-incrementally.

       Note that these differences can result in very different performance
       compared to #Z3_mk_solver().

       The function #Z3_solver_get_model retrieves a model if the
       assertions is satisfiable (i.e., the result is \c
       Z3_L_TRUE) and model construction is enabled.
       The function #Z3_solver_get_model can also be used even
       if the result is \c Z3_L_UNDEF, but the returned model
       is not guaranteed to satisfy quantified assertions.

       \remark User must use #Z3_solver_inc_ref and #Z3_solver_dec_ref to manage solver objects.
       Even if the context was created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_simple_solver', SOLVER, (_in(CONTEXT),))
    */
    Z3_solver Z3_API Z3_mk_simple_solver(Z3_context c);

    /**
       \brief Create a new solver customized for the given logic.
       It behaves like #Z3_mk_solver if the logic is unknown or unsupported.

       \remark User must use #Z3_solver_inc_ref and #Z3_solver_dec_ref to manage solver objects.
       Even if the context was created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_solver_for_logic', SOLVER, (_in(CONTEXT), _in(SYMBOL)))
    */
    Z3_solver Z3_API Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic);

    /**
       \brief Create a new solver that is implemented using the given tactic.
       The solver supports the commands #Z3_solver_push and #Z3_solver_pop, but it
       will always solve each #Z3_solver_check from scratch.

       \remark User must use #Z3_solver_inc_ref and #Z3_solver_dec_ref to manage solver objects.
       Even if the context was created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_solver_from_tactic', SOLVER, (_in(CONTEXT), _in(TACTIC)))
    */
    Z3_solver Z3_API Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t);

    /**
       \brief Copy a solver \c s from the context \c source to the context \c target.

       def_API('Z3_solver_translate', SOLVER, (_in(CONTEXT), _in(SOLVER), _in(CONTEXT)))
    */
    Z3_solver Z3_API Z3_solver_translate(Z3_context source, Z3_solver s, Z3_context target);

    /**
       \brief Ad-hoc method for importing model conversion from solver.
       
       def_API('Z3_solver_import_model_converter', VOID, (_in(CONTEXT), _in(SOLVER), _in(SOLVER)))
     */
    void Z3_API Z3_solver_import_model_converter(Z3_context ctx, Z3_solver src, Z3_solver dst);

    /**
       \brief Return a string describing all solver available parameters.

       \sa Z3_solver_get_param_descrs
       \sa Z3_solver_set_params

       def_API('Z3_solver_get_help', STRING, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_string Z3_API Z3_solver_get_help(Z3_context c, Z3_solver s);

    /**
       \brief Return the parameter description set for the given solver object.

       \sa Z3_solver_get_help
       \sa Z3_solver_set_params

       def_API('Z3_solver_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_param_descrs Z3_API Z3_solver_get_param_descrs(Z3_context c, Z3_solver s);

    /**
       \brief Set the given solver using the given parameters.

       \sa Z3_solver_get_help
       \sa Z3_solver_get_param_descrs

       def_API('Z3_solver_set_params', VOID, (_in(CONTEXT), _in(SOLVER), _in(PARAMS)))
    */
    void Z3_API Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p);

    /**
       \brief Increment the reference counter of the given solver.

       def_API('Z3_solver_inc_ref', VOID, (_in(CONTEXT), _in(SOLVER)))
    */
    void Z3_API Z3_solver_inc_ref(Z3_context c, Z3_solver s);

    /**
       \brief Decrement the reference counter of the given solver.

       def_API('Z3_solver_dec_ref', VOID, (_in(CONTEXT), _in(SOLVER)))
    */
    void Z3_API Z3_solver_dec_ref(Z3_context c, Z3_solver s);

    /**
       \brief Create a backtracking point.

       The solver contains a stack of assertions.

       \sa Z3_solver_get_num_scopes
       \sa Z3_solver_pop

       def_API('Z3_solver_push', VOID, (_in(CONTEXT), _in(SOLVER)))
    */
    void Z3_API Z3_solver_push(Z3_context c, Z3_solver s);

    /**
       \brief Backtrack \c n backtracking points.

       \sa Z3_solver_get_num_scopes
       \sa Z3_solver_push

       \pre n <= Z3_solver_get_num_scopes(c, s)

       def_API('Z3_solver_pop', VOID, (_in(CONTEXT), _in(SOLVER), _in(UINT)))
    */
    void Z3_API Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n);

    /**
       \brief Remove all assertions from the solver.

       \sa Z3_solver_assert
       \sa Z3_solver_assert_and_track

       def_API('Z3_solver_reset', VOID, (_in(CONTEXT), _in(SOLVER)))
    */
    void Z3_API Z3_solver_reset(Z3_context c, Z3_solver s);

    /**
       \brief Return the number of backtracking points.

       \sa Z3_solver_push
       \sa Z3_solver_pop

       def_API('Z3_solver_get_num_scopes', UINT, (_in(CONTEXT), _in(SOLVER)))
    */
    unsigned Z3_API Z3_solver_get_num_scopes(Z3_context c, Z3_solver s);

    /**
       \brief Assert a constraint into the solver.

       The functions #Z3_solver_check and #Z3_solver_check_assumptions should be
       used to check whether the logical context is consistent or not.

       \sa Z3_solver_assert_and_track
       \sa Z3_solver_reset

       def_API('Z3_solver_assert', VOID, (_in(CONTEXT), _in(SOLVER), _in(AST)))
    */
    void Z3_API Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);

    /**
       \brief Assert a constraint \c a into the solver, and track it (in the unsat) core using
       the Boolean constant \c p.

       This API is an alternative to #Z3_solver_check_assumptions for extracting unsat cores.
       Both APIs can be used in the same solver. The unsat core will contain a combination
       of the Boolean variables provided using Z3_solver_assert_and_track and the Boolean literals
       provided using #Z3_solver_check_assumptions.

       \pre \c a must be a Boolean expression
       \pre \c p must be a Boolean constant (aka variable).

       \sa Z3_solver_assert
       \sa Z3_solver_reset

       def_API('Z3_solver_assert_and_track', VOID, (_in(CONTEXT), _in(SOLVER), _in(AST), _in(AST)))
    */
    void Z3_API Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p);

    /**
       \brief load solver assertions from a file.

       \sa Z3_solver_from_string
       \sa Z3_solver_to_string

       def_API('Z3_solver_from_file', VOID, (_in(CONTEXT), _in(SOLVER), _in(STRING)))
    */
    void Z3_API Z3_solver_from_file(Z3_context c, Z3_solver s, Z3_string file_name);

    /**
       \brief load solver assertions from a string.

       \sa Z3_solver_from_file
       \sa Z3_solver_to_string

       def_API('Z3_solver_from_string', VOID, (_in(CONTEXT), _in(SOLVER), _in(STRING)))
    */
    void Z3_API Z3_solver_from_string(Z3_context c, Z3_solver s, Z3_string file_name);

    /**
       \brief Return the set of asserted formulas on the solver.

       def_API('Z3_solver_get_assertions', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_ast_vector Z3_API Z3_solver_get_assertions(Z3_context c, Z3_solver s);

    /**
       \brief Return the set of units modulo model conversion.

       def_API('Z3_solver_get_units', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_ast_vector Z3_API Z3_solver_get_units(Z3_context c, Z3_solver s);

    /**
       \brief Return the trail modulo model conversion, in order of decision level
       The decision level can be retrieved using \c Z3_solver_get_level based on the trail.

       def_API('Z3_solver_get_trail', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_ast_vector Z3_API Z3_solver_get_trail(Z3_context c, Z3_solver s);

    /**
       \brief Return the set of non units in the solver state.

       def_API('Z3_solver_get_non_units', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_ast_vector Z3_API Z3_solver_get_non_units(Z3_context c, Z3_solver s);

    /**
       \brief retrieve the decision depth of Boolean literals (variables or their negations).
       Assumes a check-sat call and no other calls (to extract models) have been invoked.
       
       def_API('Z3_solver_get_levels', VOID, (_in(CONTEXT), _in(SOLVER), _in(AST_VECTOR), _in(UINT), _in_array(3, UINT)))
    */
    void Z3_API Z3_solver_get_levels(Z3_context c, Z3_solver s, Z3_ast_vector literals, unsigned sz,  unsigned levels[]);

    /**
       \brief Check whether the assertions in a given solver are consistent or not.

       The function #Z3_solver_get_model retrieves a model if the
       assertions is satisfiable (i.e., the result is \c
       Z3_L_TRUE) and model construction is enabled.
       Note that if the call returns \c Z3_L_UNDEF, Z3 does not
       ensure that calls to #Z3_solver_get_model succeed and any models
       produced in this case are not guaranteed to satisfy the assertions.

       The function #Z3_solver_get_proof retrieves a proof if proof
       generation was enabled when the context was created, and the
       assertions are unsatisfiable (i.e., the result is \c Z3_L_FALSE).

       \sa Z3_solver_check_assumptions

       def_API('Z3_solver_check', INT, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_lbool Z3_API Z3_solver_check(Z3_context c, Z3_solver s);

    /**
       \brief Check whether the assertions in the given solver and
       optional assumptions are consistent or not.

       The function #Z3_solver_get_unsat_core retrieves the subset of the
       assumptions used in the unsatisfiability proof produced by Z3.

       \sa Z3_solver_check

       def_API('Z3_solver_check_assumptions', INT, (_in(CONTEXT), _in(SOLVER), _in(UINT), _in_array(2, AST)))
    */
    Z3_lbool Z3_API Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                                unsigned num_assumptions, Z3_ast const assumptions[]);

    /**
       \brief Retrieve congruence class representatives for terms.

       The function can be used for relying on Z3 to identify equal terms under the current
       set of assumptions. The array of terms and array of class identifiers should have
       the same length. The class identifiers are numerals that are assigned to the same
       value for their corresponding terms if the current context forces the terms to be
       equal. You cannot deduce that terms corresponding to different numerals must be all different,
       (especially when using non-convex theories).
       All implied equalities are returned by this call.
       This means that two terms map to the same class identifier if and only if
       the current context implies that they are equal.

       A side-effect of the function is a satisfiability check on the assertions on the solver that is passed in.
       The function return \c Z3_L_FALSE if the current assertions are not satisfiable.

       def_API('Z3_get_implied_equalities', INT, (_in(CONTEXT), _in(SOLVER), _in(UINT), _in_array(2, AST), _out_array(2, UINT)))
    */
    Z3_lbool Z3_API Z3_get_implied_equalities(Z3_context c,
                                              Z3_solver  s,
                                              unsigned num_terms,
                                              Z3_ast const terms[],
                                              unsigned class_ids[]);

    /**
       \brief retrieve consequences from solver that determine values of the supplied function symbols.

       def_API('Z3_solver_get_consequences', INT, (_in(CONTEXT), _in(SOLVER), _in(AST_VECTOR), _in(AST_VECTOR), _in(AST_VECTOR)))
     */

    Z3_lbool Z3_API Z3_solver_get_consequences(Z3_context c,
                                               Z3_solver s,
                                               Z3_ast_vector assumptions,
                                               Z3_ast_vector variables,
                                               Z3_ast_vector consequences);


    /**
       \brief extract a next cube for a solver. The last cube is the constant \c true or \c false.
       The number of (non-constant) cubes is by default 1. For the sat solver cubing is controlled
       using parameters sat.lookahead.cube.cutoff and sat.lookahead.cube.fraction.
       
       The third argument is a vector of variables that may be used for cubing.
       The contents of the vector is only used in the first call. The initial list of variables
       is used in subsequent calls until it returns the unsatisfiable cube. 
       The vector is modified to contain a set of Autarky variables that occur in clauses that
       are affected by the (last literal in the) cube. These variables could be used by a different
       cuber (on a different solver object) for further recursive cubing. 

       The last argument is a backtracking level. It instructs the cube process to backtrack below
       the indicated level for the next cube.
       
       def_API('Z3_solver_cube', AST_VECTOR, (_in(CONTEXT), _in(SOLVER), _in(AST_VECTOR), _in(UINT)))
    */

    Z3_ast_vector Z3_API Z3_solver_cube(Z3_context c, Z3_solver s, Z3_ast_vector vars, unsigned backtrack_level);

    /**
       \brief Retrieve the model for the last #Z3_solver_check or #Z3_solver_check_assumptions

       The error handler is invoked if a model is not available because
       the commands above were not invoked for the given solver, or if the result was \c Z3_L_FALSE.

       def_API('Z3_solver_get_model', MODEL, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_model Z3_API Z3_solver_get_model(Z3_context c, Z3_solver s);

    /**
       \brief Retrieve the proof for the last #Z3_solver_check or #Z3_solver_check_assumptions

       The error handler is invoked if proof generation is not enabled,
       or if the commands above were not invoked for the given solver,
       or if the result was different from \c Z3_L_FALSE.

       def_API('Z3_solver_get_proof', AST, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_ast Z3_API Z3_solver_get_proof(Z3_context c, Z3_solver s);

    /**
       \brief Retrieve the unsat core for the last #Z3_solver_check_assumptions
       The unsat core is a subset of the assumptions \c a.

       def_API('Z3_solver_get_unsat_core', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_ast_vector Z3_API Z3_solver_get_unsat_core(Z3_context c, Z3_solver s);

    /**
       \brief Return a brief justification for an "unknown" result (i.e., \c Z3_L_UNDEF) for
       the commands #Z3_solver_check and #Z3_solver_check_assumptions

       def_API('Z3_solver_get_reason_unknown', STRING, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_string Z3_API Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s);

    /**
       \brief Return statistics for the given solver.

       \remark User must use #Z3_stats_inc_ref and #Z3_stats_dec_ref to manage Z3_stats objects.

       def_API('Z3_solver_get_statistics', STATS, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_stats Z3_API Z3_solver_get_statistics(Z3_context c, Z3_solver s);

    /**
       \brief Convert a solver into a string.

       \sa Z3_solver_from_file
       \sa Z3_solver_from_string

       def_API('Z3_solver_to_string', STRING, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_string Z3_API Z3_solver_to_string(Z3_context c, Z3_solver s);

    /**
       \brief Convert a solver into a DIMACS formatted string.
       \sa Z3_goal_to_diamcs_string for requirements.

       def_API('Z3_solver_to_dimacs_string', STRING, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_string Z3_API Z3_solver_to_dimacs_string(Z3_context c, Z3_solver s);

    /*@}*/

    /** @name Statistics */
    /*@{*/

    /**
       \brief Convert a statistics into a string.

       def_API('Z3_stats_to_string', STRING, (_in(CONTEXT), _in(STATS)))
    */
    Z3_string Z3_API Z3_stats_to_string(Z3_context c, Z3_stats s);

    /**
       \brief Increment the reference counter of the given statistics object.

       def_API('Z3_stats_inc_ref', VOID, (_in(CONTEXT), _in(STATS)))
    */
    void Z3_API Z3_stats_inc_ref(Z3_context c, Z3_stats s);

    /**
       \brief Decrement the reference counter of the given statistics object.

       def_API('Z3_stats_dec_ref', VOID, (_in(CONTEXT), _in(STATS)))
    */
    void Z3_API Z3_stats_dec_ref(Z3_context c, Z3_stats s);

    /**
       \brief Return the number of statistical data in \c s.

       def_API('Z3_stats_size', UINT, (_in(CONTEXT), _in(STATS)))
    */
    unsigned Z3_API Z3_stats_size(Z3_context c, Z3_stats s);

    /**
       \brief Return the key (a string) for a particular statistical data.

       \pre idx < Z3_stats_size(c, s)

       def_API('Z3_stats_get_key', STRING, (_in(CONTEXT), _in(STATS), _in(UINT)))
    */
    Z3_string Z3_API Z3_stats_get_key(Z3_context c, Z3_stats s, unsigned idx);

    /**
       \brief Return \c true if the given statistical data is a unsigned integer.

       \pre idx < Z3_stats_size(c, s)

       def_API('Z3_stats_is_uint', BOOL, (_in(CONTEXT), _in(STATS), _in(UINT)))
    */
    bool Z3_API Z3_stats_is_uint(Z3_context c, Z3_stats s, unsigned idx);

    /**
       \brief Return \c true if the given statistical data is a double.

       \pre idx < Z3_stats_size(c, s)

       def_API('Z3_stats_is_double', BOOL, (_in(CONTEXT), _in(STATS), _in(UINT)))
    */
    bool Z3_API Z3_stats_is_double(Z3_context c, Z3_stats s, unsigned idx);

    /**
       \brief Return the unsigned value of the given statistical data.

       \pre idx < Z3_stats_size(c, s) && Z3_stats_is_uint(c, s)

       def_API('Z3_stats_get_uint_value', UINT, (_in(CONTEXT), _in(STATS), _in(UINT)))
    */
    unsigned Z3_API Z3_stats_get_uint_value(Z3_context c, Z3_stats s, unsigned idx);

    /**
       \brief Return the double value of the given statistical data.

       \pre idx < Z3_stats_size(c, s) && Z3_stats_is_double(c, s)

       def_API('Z3_stats_get_double_value', DOUBLE, (_in(CONTEXT), _in(STATS), _in(UINT)))
    */
    double Z3_API Z3_stats_get_double_value(Z3_context c, Z3_stats s, unsigned idx);

    /**
    \brief Return the estimated allocated memory in bytes.

    def_API('Z3_get_estimated_alloc_size', UINT64, ())
    */
    uint64_t Z3_API Z3_get_estimated_alloc_size(void);

    /*@}*/

#ifdef __cplusplus
}
#endif // __cplusplus

/*@}*/

#endif
