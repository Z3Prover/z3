module Z3NestedArgs
open FStar.List.Tot

type srt = | DT : srt | Arr : srt -> srt | Seq : srt -> srt | Set : srt -> srt | Other : srt

let rec has_nested (s:srt) : Tot bool (decreases s) =
  match s with
  | DT -> true
  | Arr r -> has_nested r
  | Seq e -> has_nested e
  | Set e -> has_nested e
  | Other -> false

let rec dt_under (s:srt) : Tot bool (decreases s) =
  match s with
  | DT -> true
  | Arr r | Seq r | Set r -> dt_under r
  | Other -> false
let rec o1 (s:srt) : Lemma (ensures has_nested s == dt_under s) (decreases s) =
  match s with
  | Arr r | Seq r | Set r -> o1 r
  | _ -> ()

noeq type node = | Leaf : nat -> node | Node : s:srt -> kids:list node -> node

let rec leaves (n:node) : Tot (list nat) (decreases n) =
  match n with
  | Leaf k -> [k]
  | Node _ ks -> leaves_l ks
and leaves_l (ks:list node) : Tot (list nat) (decreases ks) =
  match ks with
  | [] -> []
  | k::r -> leaves k @ leaves_l r

let rec pruned (n:node) : Tot (list nat) (decreases n) =
  match n with
  | Leaf k -> [k]
  | Node s ks -> if has_nested s then pruned_l ks else []
and pruned_l (ks:list node) : Tot (list nat) (decreases ks) =
  match ks with
  | [] -> []
  | k::r -> pruned k @ pruned_l r

let rec wf (n:node) : Tot bool (decreases n) =
  match n with
  | Leaf _ -> true
  | Node s ks -> (has_nested s || leaves_l ks = []) && wf_l ks
and wf_l (ks:list node) : Tot bool (decreases ks) =
  match ks with | [] -> true | k::r -> wf k && wf_l r

let rec o2 (n:node) : Lemma (requires wf n) (ensures pruned n == leaves n) (decreases n) =
  match n with
  | Leaf _ -> ()
  | Node s ks -> o2l ks
and o2l (ks:list node) : Lemma (requires wf_l ks) (ensures pruned_l ks == leaves_l ks) (decreases ks) =
  match ks with
  | [] -> ()
  | k::r -> o2 k; o2l r

let add_todo (visited todo:list nat) (c:nat) : (list nat & list nat) =
  if mem c visited then (visited, todo) else (c::visited, todo @ [c])
let rec nodup (l:list nat) : Tot bool = match l with | [] -> true | x::r -> not (mem x r) && nodup r
let rec mem_app (l1 l2:list nat) (x:nat) : Lemma (mem x (l1@l2) == (mem x l1 || mem x l2)) =
  match l1 with | [] -> () | _::r -> mem_app r l2 x
let rec nodup_snoc (l:list nat) (c:nat) : Lemma (requires nodup l /\ not (mem c l)) (ensures nodup (l @ [c])) =
  match l with | [] -> () | y::r -> mem_app r [c] y; nodup_snoc r c
let o3 (visited todo:list nat) (c:nat)
  : Lemma (requires nodup todo /\ (forall x. mem x todo ==> mem x visited))
          (ensures (let (v',t') = add_todo visited todo c in
                    nodup t' /\ mem c v' /\ (forall x. mem x t' ==> mem x v')))
  = if mem c visited then () else (mem_app todo [c] c; nodup_snoc todo c;
      FStar.Classical.forall_intro (mem_app todo [c]))

let w : node = Node (Arr (Seq DT)) [Node (Seq DT) [Leaf 7]]
let witness () : Lemma (wf w /\ pruned w == [7] /\ has_nested (Arr (Seq DT)))
  = assert_norm (wf w); assert_norm (pruned w == [7])
