module Z3DtRollback
(* Abstract model of PR 11657: cmd_context::insert(symbol, psort_decl ptr) followed by
   cmd_context::rollback_psort_decl, driven by the parser's new_sorts list.
   decls = m_psort_decls keys, stack = m_psort_decls_stack, global = m_global_decls. *)
open FStar.List.Tot

type st = { decls: list nat; stack: list nat; global: bool }

(* insert: throws (None) on an existing name; pushes on the stack only when scoped *)
let insert (s:st) (n:nat) : option st =
  if mem n s.decls then None
  else Some ({ s with decls = n :: s.decls;
                      stack = (if s.global then s.stack else n :: s.stack) })

(* rollback_psort_decl: erase name; when scoped, pop the stack top (SASSERT top == n) *)
let rollback (s:st) (n:nat) : st =
  { s with decls = filter (fun x -> x <> n) s.decls;
           stack = (if s.global then s.stack
                    else (match s.stack with | _ :: t -> t | [] -> [])) }

(* Parser: insert names in order; the first failing insert throws.
   The returned list is new_sorts, newest first. *)
let rec run (s:st) (ns:list nat) : Tot (st & list nat) (decreases ns) =
  match ns with
  | [] -> (s, [])
  | n :: r ->
    (match insert s n with
     | None -> (s, [])
     | Some s1 -> let (s2, a) = run s1 r in (s2, a @ [n]))

(* The rollback lambda iterates new_sorts from the back: newest first *)
let rec rollback_all (s:st) (a:list nat) : Tot st (decreases a) =
  match a with [] -> s | n :: r -> rollback_all (rollback s n) r

(* O1: new_sorts are exactly the newly added names; stack grew by them (scoped). *)
let rec run_shape (s:st) (ns:list nat)
  : Lemma (ensures (let (s', a) = run s ns in
                    s'.global == s.global /\
                    s'.stack == (if s.global then s.stack else a @ s.stack) /\
                    (forall x. mem x s'.decls <==> (mem x s.decls \/ mem x a)) /\
                    (forall x. mem x a ==> not (mem x s.decls))))
          (decreases ns)
  = match ns with
    | [] -> ()
    | n :: r ->
      (match insert s n with
       | None -> ()
       | Some s1 ->
         run_shape s1 r;
         let (_, a) = run s1 r in
         append_assoc a [n] s.stack;
         FStar.Classical.forall_intro (append_mem a [n]))

(* O2: newest-first rollback restores stack and removes exactly the new names. *)
let rec rollback_restores (s:st) (a:list nat) (base:list nat)
  : Lemma (requires (not s.global ==> s.stack == a @ base))
          (ensures (let s' = rollback_all s a in
                    s'.global == s.global /\
                    s'.stack == (if s.global then s.stack else base) /\
                    (forall x. mem x s'.decls <==> (mem x s.decls /\ not (mem x a)))))
          (decreases a)
  = match a with
    | [] -> ()
    | n :: r -> rollback_restores (rollback s n) r base

(* O3: end to end, including duplicate names that make a later insert throw. *)
let end_to_end (s:st) (ns:list nat)
  : Lemma (ensures (let (s1, a) = run s ns in
                    let s2 = rollback_all s1 a in
                    s2.stack == s.stack /\ s2.global == s.global /\
                    (forall x. mem x s2.decls <==> mem x s.decls)))
  = run_shape s ns;
    let (s1, a) = run s ns in
    rollback_restores s1 a s.stack

let dup_noop (s:st) (n:nat) : Lemma (requires mem n s.decls) (ensures insert s n == None) = ()
