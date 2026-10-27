module GlobalDeclsGuard
(* Model of set_option_cmd for :global-declarations at PR head 19d5ac8.
   ctx = (has_manager, m_global_decls). set_global_decls has SASSERT(!has_manager()). *)
type ctx = { has_manager: bool; global_decls: bool }

type outcome = | Throws | Sets of ctx | AssertViolation

let set_global_decls_pre (c:ctx) : bool = not c.has_manager

(* Head code: if (value != ctx.global_decls()) check_not_initialized; set_global_decls(value) *)
let head_step (c:ctx) (v:bool) : outcome =
  if v <> c.global_decls && c.has_manager then Throws
  else if not (set_global_decls_pre c) then AssertViolation
  else Sets { c with global_decls = v }

(* Base code: check_not_initialized unconditionally *)
let base_step (c:ctx) (v:bool) : outcome =
  if c.has_manager then Throws
  else Sets { c with global_decls = v }

(* Reachable witness: manager initialized, default false, option set to false again *)
let witness : ctx = { has_manager = true; global_decls = false }
let cex () : Lemma (head_step witness false == AssertViolation /\ base_step witness false == Throws) = ()

(* Characterisation: exactly the no-change-after-init inputs violate the assertion *)
let exact (c:ctx) (v:bool)
  : Lemma (head_step c v == AssertViolation <==> (c.has_manager /\ v = c.global_decls)) = ()
