(* Stand-in for FStar_String (OCaml extraction target of FStar.String),
   with only what the extracted checker uses and no Batteries dependency.
   `strlen` counts UTF-8 characters, as `FStar.String.strlen` specifies
   (`List.length (list_of_string s)`): every byte that does not continue
   a multi-byte sequence starts one. *)

let strlen (s : string) : Prims.int =
  let n = ref 0 in
  Stdlib.String.iter (fun c -> if Stdlib.Char.code c land 0xC0 <> 0x80 then incr n) s;
  Z.of_int !n
