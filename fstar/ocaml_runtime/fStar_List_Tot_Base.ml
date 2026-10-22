(* Stand-in for FStar_List_Tot_Base (OCaml extraction target of
   FStar.List.Tot.Base). All functions here operate on plain OCaml
   lists, matching how the extracted Z3*.ml code uses `Prims.list`
   (see prims.ml: `type 'a list = 'a Stdlib.list`). *)

let length (l : 'a list) : Prims.int = Z.of_int (Stdlib.List.length l)
let rev (l : 'a list) : 'a list = Stdlib.List.rev l
let map (f : 'a -> 'b) (l : 'a list) : 'b list = Stdlib.List.map f l
let append (l1 : 'a list) (l2 : 'a list) : 'a list = l1 @ l2
let op_At (l1 : 'a list) (l2 : 'a list) : 'a list = l1 @ l2
let hd (l : 'a list) : 'a = Stdlib.List.hd l
let tl (l : 'a list) : 'a list = Stdlib.List.tl l
let rec splitAt (n : Prims.int) (l : 'a list) : 'a list * 'a list =
  if Z.equal n Z.zero then [], l
  else match l with
    | [] -> [], []
    | x :: rest ->
        let prefix, suffix = splitAt (Z.pred n) rest in
        x :: prefix, suffix
let mem (x : 'a) (l : 'a list) : Prims.bool = Stdlib.List.mem x l
let for_all (f : 'a -> Prims.bool) (l : 'a list) : Prims.bool = Stdlib.List.for_all f l
let index (l : 'a list) (i : Prims.int) : 'a = Stdlib.List.nth l (Z.to_int i)
