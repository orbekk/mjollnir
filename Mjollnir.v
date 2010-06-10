Require Import List.

Add LoadPath "contrib".
Require Import Registers.
Require Import Values.
Require Import Coqlib.
Require Import Integers.

(* ToDo: Add Mach to contrib (many dependencies) *)
Definition regset := Regmap.t val.


(*** The language: ***)

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

Definition eval_def (s:state) (e:expr) : val :=
  match e with
    | intlit x => x
    | add v1 v2 => add_int_vals (s#v1) (s#v2)
  end.

Definition step_def (s:state) (stmt:stmt) : state :=
  match stmt with
    | skip => s
    | assign var e => 
      let val := eval_def s e 
        in s # var <- val
  end.


Inductive eval : state -> expr -> val -> Prop :=
  | eval_intlit : forall s x,
    eval s (intlit x) x
  | eval_add : forall s var1 var2,
    eval s (add var1 var2) (add_int_vals (s#var1) (s#var2)).

Inductive step : state -> stmt -> state -> Prop :=
  | step_skip : forall s,
    step s skip s
  | step_assign : forall s var ex val,
    eval s ex val ->
    step s (assign var ex) (s # var <- val).
    
Definition step_path_def s0 p := fold_left step_def p s0.

Inductive step_path : state -> path -> state -> Prop :=
  | step_path_nil : forall s,
    step_path s nil s
  | step_path_cons : forall s stmt0 stmts s0 s',
    step s stmt0 s0 ->
    step_path s0 stmts s' ->
    step_path s (stmt0::stmts) s'.

Theorem eval_result_unique : forall s0 s1 e v0 v1,
  correlation_holds states_eq s0 s1 ->
  eval s0 e v0 ->
  eval s1 e v1 ->
  v0 = v1.
Proof.
intros.
destruct e.
inversion H0. subst.
inversion H1. subst.
reflexivity.

inversion H0. subst.
inversion H1. subst.
inversion H. subst.
reflexivity.
Qed.

Theorem step_program_state_equal : forall s0 s1 stmt s'0 s'1,
  correlation_holds states_eq s0 s1 ->
  step s0 stmt s'0 ->
  step s1 stmt s'1 ->
  correlation_holds states_eq s'0 s'1.
Proof.
  intros.
  destruct H.
  destruct stmt0; inversion H0; inversion H1; subst.
  rewrite -> H5.
  constructor.

  assert (val = val0).
  apply eval_result_unique with (s0 := st) (s1 := st) (e := e).
  constructor. auto. auto.

  rewrite -> H.
  constructor.

  constructor.
Qed.
 

Theorem same_program_state_equal : forall p s0 s1 s'0 s'1,
  correlation_holds states_eq s0 s1 ->
  step_path s0 p s'0 ->
  step_path s1 p s'1 ->
  correlation_holds states_eq s'0 s'1.
Proof.
  induction p. 

    intros.
    destruct H.
    inversion H0. inversion H1. subst.
    rewrite -> H5.
    apply states_eq_holds.

    apply true_c_holds.

    intros.
    
    inversion H0; inversion H1; subst.
    apply IHp with (s0 := s2) (s1 := s4).
    Check step_program_state_equal.
    apply step_program_state_equal with (s0 := s0) (s1 := s1) (stmt := a).
    auto. assumption. assumption. assumption. assumption.
Qed.

(*** Test code ***)

(* Lookup *)
Definition v := ((Regmap.init (Vint (Int.repr 5))) # 1).
Eval compute in v.


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
  (step_path_def empty_state my_program)
  (step_path_def empty_state my_program_opt).
Proof.
  apply states_eq_holds.
Qed.

Lemma my_program_opt_connect_0_I : forall s0 s1,
  (step_path empty_state my_program s0) ->
  (step_path empty_state my_program_opt s1) ->
  correlation_holds states_eq s0 s1.
Proof.
  intros s0 s1 Hstep0 Hstep1.
  inversion Hstep0. subst.
  inversion Hstep1. subst.

  assert (correlation_holds states_eq s2 s3).
  apply step_program_state_equal with
    (s0 := empty_state) (s1:= empty_state) 
    (stmt := (assign 1 (intlit (Vint (Int.repr 5))))).
    constructor. assumption. assumption.

  clear H2 H3.

  inversion H4. inversion H6. subst.

  assert (correlation_holds states_eq s4 s6).
  apply step_program_state_equal with
    (s0 := s2) (s1 := s3)
    (stmt := (assign 2 (intlit (Vint (Int.repr 3))))).
  assumption. assumption. assumption.

  clear H3 H11.

  inversion H7. inversion H13. subst.

  assert (correlation_holds states_eq s5 s8).
  inversion H5.
  inversion H14. subst.

  inversion H10. inversion H18. subst.

  assert (add_int_vals s4 # 1 s4 # 2 = Vint (Int.repr 8)).
  
  (* We would like to show this. But at this point we need more
  information about the state variables, which is hidden in the
  state_equal theorem *)
Admitted.

  

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


