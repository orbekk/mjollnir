(* Our very simple language *)

Require Import List.

Inductive stmt : Type :=
  | nop : stmt.

Definition path : Type := list stmt.





