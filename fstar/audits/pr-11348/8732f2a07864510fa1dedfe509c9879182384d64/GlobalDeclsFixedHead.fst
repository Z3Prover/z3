module GlobalDeclsFixedHead
(* Model of set_option_cmd :global-declarations branch at head 8732f2a. *)
type ctx = { has_manager: bool; global_decls: bool }
type result = | Ok : ctx -> result | Throw : result | AssertFail : result

(* cmd_context::set_global_decls has SASSERT(!has_manager()) *)
let set_global_decls (c:ctx) (f:bool) : result =
  if c.has_manager then AssertFail else Ok ({ c with global_decls = f })

(* check_not_initialized: throws iff has_manager *)
let check_not_initialized (c:ctx) : option result =
  if c.has_manager then Some Throw else None

(* head: if (g != ctx.global_decls()) { check_not_initialized; set_global_decls(g) } *)
let head (c:ctx) (g:bool) : result =
  if g <> c.global_decls then
    (match check_not_initialized c with
     | Some r -> r
     | None -> set_global_decls c g)
  else Ok c

(* base: check_not_initialized; set_global_decls(g) *)
let base (c:ctx) (g:bool) : result =
  match check_not_initialized c with
  | Some r -> r
  | None -> set_global_decls c g

(* O1: the SASSERT is never violated (refutes the earlier counterexample against 19d5ac8) *)
let o1 (c:ctx) (g:bool) : Lemma (head c g <> AssertFail) = ()

(* O2: changing the value after initialization still throws, as in base *)
let o2 (c:ctx) (g:bool) : Lemma
  (requires c.has_manager /\ g <> c.global_decls) (ensures head c g = Throw) = ()

(* O3: on success the option equals the requested value; head differs from base only
   by accepting a same-value set after initialization (state unchanged) *)
let o3 (c:ctx) (g:bool) : Lemma
  (ensures (match head c g with Ok c' -> c'.global_decls = g /\ c'.has_manager = c.has_manager | _ -> True)
        /\ (head c g <> base c g ==> (c.has_manager /\ g = c.global_decls /\ head c g = Ok c))) = ()
