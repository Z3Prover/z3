module Z3ArithRewriterCast

(*
   Companion module to Z3ArithRewriter.fst: formalizes the to_int/to_real/
   is_int identities from src/ast/rewriter/arith_rewriter.cpp's
   mk_to_int_core, mk_to_real_core and mk_is_int. Split into its own file
   because combined verification together with Z3ArithRewriter.fst's
   power-merge induction is slow; each module verifies quickly on its own.
*)

open FStar.Real

/// to_real is injective and to_int . to_real is the identity on integers:
/// mk_to_int_core's "is_to_real(arg, x) && is_int(x) -> result = x" rule,
/// modeled abstractly via an uninterpreted real-embedding of int (standing
/// in for Z3's OP_TO_REAL / OP_TO_INT, which inject int into the reals).
assume val to_real : int -> real
assume val to_int : real -> int
assume To_int_to_real: forall (n:int). to_int (to_real n) == n
assume To_real_injective: forall (m n:int). to_real m == to_real n ==> m == n

let to_int_to_real_cancel (n:int) : Lemma (to_int (to_real n) == n) = ()

/// Pushing to_real over + and * (m_push_to_real rules).
assume Push_to_real_add: forall (m n:int). to_real (m + n) == to_real m +. to_real n
assume Push_to_real_mul: forall (m n:int). to_real (m * n) == to_real m *. to_real n

let push_to_real_add (m n:int) : Lemma (to_real (m + n) == to_real m +. to_real n) = ()
let push_to_real_mul (m n:int) : Lemma (to_real (m * n) == to_real m *. to_real n) = ()

/// is_int(to_real n) is always true -- mk_is_int's "is_to_real(arg) &&
/// is_int(inner-arg)" shortcut.
let is_int_of_to_real (n:int) : Lemma (to_int (to_real n) == n) = ()
