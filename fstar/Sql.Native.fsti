module Sql.Native

(* Foreign operations only inspect or construct native syntax. All rewrite
   decisions are made by Sql.Optimize.rewrite, not by this interface. *)
new val term : Type0
val opcode : term -> Tot FStar.UInt32.t
val child : term -> FStar.UInt32.t -> Tot term
val identifier : term -> Tot FStar.UInt64.t
val lookup : FStar.UInt64.t -> Tot term
val make0 : FStar.UInt32.t -> Tot term
val make1 : FStar.UInt32.t -> term -> Tot term
val make2 : FStar.UInt32.t -> term -> term -> Tot term
val make3 : FStar.UInt32.t -> term -> term -> term -> Tot term
