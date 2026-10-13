(* Stand-in for FStar_List_Tot_Base (OCaml extraction target of
   FStar.List.Tot.Base). All functions here operate on plain OCaml
   lists, matching how the extracted Z3*.ml code uses `Prims.list`
   (see prims.ml: `type 'a list = 'a Stdlib.list`). *)

let length (l : 'a list) : Prims.int = Stdlib.List.length l
let rev (l : 'a list) : 'a list = Stdlib.List.rev l
let append (l1 : 'a list) (l2 : 'a list) : 'a list = l1 @ l2
let op_At (l1 : 'a list) (l2 : 'a list) : 'a list = l1 @ l2
let hd (l : 'a list) : 'a = Stdlib.List.hd l
let mem (x : 'a) (l : 'a list) : Prims.bool = Stdlib.List.mem x l
let index (l : 'a list) (i : Prims.int) : 'a = Stdlib.List.nth l i
