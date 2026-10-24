(* Stand-in for FStar_FunctionalExtensionality: at the value level this
   module is a no-op for us -- `restricted_t` is only ever used as a
   *type* alias (Z3ArrayTheory.ml's `('idx,'v) arr`), never as a
   function actually called at runtime by the extracted checker. *)

type ('a, 'b) restricted_t = 'a -> 'b
