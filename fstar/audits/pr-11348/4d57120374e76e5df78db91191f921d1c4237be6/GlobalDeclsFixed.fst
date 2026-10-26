module GlobalDeclsFixed
(* Model of set_option_cmd for :global-declarations at PR head 4d57120.
   set_global_decls has SASSERT(!has_manager()) (from the previous audit of this PR). *)
type ctx = { has_manager: bool; global_decls: bool }
type outcome = | Throws | Sets of ctx | NoChange | AssertViolation

let head_step (c:ctx) (v:bool) : outcome =
  if v <> c.global_decls then
    (if c.has_manager then Throws
     else if c.has_manager then AssertViolation
     else Sets { c with global_decls = v })
  else NoChange

let base_step (c:ctx) (v:bool) : outcome =
  if c.has_manager then Throws else Sets { c with global_decls = v }

(* O1: the assertion is never reached *)
let no_assert (c:ctx) (v:bool) : Lemma (head_step c v <> AssertViolation) = ()
(* O2: changing the value after manager init still throws *)
let change_throws (c:ctx) (v:bool)
  : Lemma (requires c.has_manager /\ v <> c.global_decls) (ensures head_step c v == Throws) = ()
(* O3: before init, final state agrees with base *)
let pre_init_agrees (c:ctx) (v:bool)
  : Lemma (requires not c.has_manager)
          (ensures (match head_step c v with
                    | NoChange -> c.global_decls = v
                    | o -> o == base_step c v)) = ()
