Require Import List.

Add LoadPath "contrib".
Require Import Registers.
Require Import Values.
Require Import Coqlib.
Require Import Integers.

(* ToDo: Add Mach to contrib (many dependencies) *)
Definition regset := Regmap.t val.


(*** Our language: ***)

Inductive expr : Type :=
  | intlit : val -> expr
  | add : positive -> positive -> expr.

Inductive stmt : Type :=
  | skip : stmt
  | assign : positive -> expr -> stmt.

Definition path : Type := list stmt.

Definition state : Type := regset.

Definition empty_state : state := Regmap.init Vundef.

Inductive correlation : Type :=
  | states_eq : correlation
  | true_c    : correlation.

Inductive correlation_holds : correlation -> state -> state -> Prop :=
  | states_eq_holds : forall st, correlation_holds states_eq st st
  | true_c_holds    : forall st1 st2, correlation_holds true_c st1 st2.

Definition add_int_vals v1 v2 : val :=
  match (v1, v2) with
    | (Vint x, Vint y) => Vint (Int.add x y)
    | _                => Vint (Int.zero)
  end.

Definition eval (s:state) (e:expr) : val :=
  match e with
    | intlit x => x
    | add v1 v2 => add_int_vals (s#v1) (s#v2)
  end.

Definition step (s:state) (stmt:stmt) : state :=
  match stmt with
    | skip => s
    | assign var e => 
      let val := eval s e 
        in s # var <- val
  end.

Definition step_path s0 p := fold_left step p s0.


(*** Test code ***)

(* Lookup *)
Definition v := ((Regmap.init (Vint (Int.repr 5))) # 1).
Eval compute in v.


(* ToDo: Look at Zach's stuff and fix better notation *)

(* A very simple program and its optimization *)
Definition my_program :=
  assign 1 (intlit (Vint (Int.repr 5))) ::
  assign 2 (intlit (Vint (Int.repr 3))) ::
  assign 3 (add 1 2)                    ::
  nil.

Definition my_program_opt :=
  assign 1 (intlit (Vint (Int.repr 5))) ::
  assign 2 (intlit (Vint (Int.repr 3))) ::
  assign 3 (intlit (Vint (Int.repr 8))) ::
  nil.

Lemma my_program_opt_correct_0 : 
  correlation_holds states_eq
  (step_path empty_state my_program)
  (step_path empty_state my_program_opt).
Proof.
  apply states_eq_holds.
Qed.

(* A "parameterized" version of the above program *)
Definition P_my_program x y :=
  assign 1 (intlit (Vint (Int.repr x))) ::
  assign 2 (intlit (Vint (Int.repr y))) ::
  assign 3 (add 1 2)                    ::
  nil.

Definition P_my_program_opt x y :=
  assign 1 (intlit (Vint (Int.repr x))) ::
  assign 2 (intlit (Vint (Int.repr y))) ::
  assign 3 (intlit (Vint (Int.add (Int.repr x) (Int.repr y)))) ::
  nil.

Lemma P_my_program_opt_correct_0 : forall x y,
  correlation_holds states_eq
  (step_path empty_state (P_my_program x y))
  (step_path empty_state (P_my_program_opt x y)).
Proof.
  intros.
  apply states_eq_holds. (* Wow! *)
Qed.

(* The real thing: start from arbitrary states *)
Lemma P_my_program_opt_correct : forall s0 s1 x y,
  correlation_holds states_eq s0 s1 ->
  correlation_holds states_eq
    (step_path s0 (P_my_program x y))
    (step_path s1 (P_my_program x y)).
Proof.
  intros.
  inversion H; subst.
  apply states_eq_holds.
Qed.


(* Old stuff *)
Definition pec_check (c c':correlation) (p1 p2:path) : bool :=
  true.

Theorem pec_check_correct :
  forall c c' p1 p2 sL sR,
    correlation_holds c sL sR ->
    pec_check c c' p1 p2 = true ->
    correlation_holds c' (step_path sL p1) (step_path sR p2).
Proof.
  intros.
  induction c'.
    destruct step_path. destruct step_path.
    apply states_eq_holds.

    apply true_c_holds.
Qed.


