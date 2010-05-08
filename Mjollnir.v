Require Import List.

Inductive stmt : Type :=
  | nop : stmt.

Definition path : Type := list stmt.

Definition state : Type := unit.

Inductive correlation : Type :=
  | states_eq : correlation
  | true_c    : correlation.

Inductive correlation_holds : correlation -> state -> state -> Prop :=
  | states_eq_holds : forall st, correlation_holds states_eq st st
  | true_c_holds    : forall st1 st2, correlation_holds true_c st1 st2.

Definition step (s0:state) (stmt:stmt) : state :=
  s0.

Definition step_path s0 p := fold_left step p s0.

Definition pec_check (c c':correlation) (p1 p2:path) : bool :=
  false.

Theorem pec_check_correct :
  forall c c' p1 p2 sL sR,
    correlation_holds c sL sR ->
    pec_check c c' p1 p2 = true ->
    correlation_holds c' (step_path sL p1) (step_path sR p2).
Proof.
  intros.
  inversion H0.
Qed.