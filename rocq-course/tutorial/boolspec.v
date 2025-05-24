(* Tutorial 9: Executable specifications *)

(************************************************************************************)
(* Executable specifications *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Open Scope bool_scope.

Check (true && false).

Require Import Nat.
Check (2 =? 3).
Locate "=?".
Check (2 <=? 3).
Check (2 <= 3).

Fixpoint sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: ((y :: _) as t) => (x <=? y) && sorted t
  end.

Compute sorted [1; 2; 4; 11].
Compute sorted [1; 2; 11; 12; 10].

Lemma lem_sorted_eq : forall x y l, sorted (x :: y :: l) = (x <=? y) && sorted (y :: l).
Proof.
  reflexivity.
Qed.

Coercion is_true (b : bool) := b = true.

Lemma andE: forall b1 b2 : bool, (b1 /\ b2) <-> (b1 && b2).
Proof.
  cbv.
  destruct b1, b2; tauto.
Qed.

Lemma lem_sorted_1 :
  forall l x y, x <=? y ->
                sorted (y :: l) ->
                sorted (x :: y :: l).
Proof.
  destruct l; intros; apply andE; auto.
Qed.

Ltac bsolve := intros; try apply andE; auto.

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

Lemma lem_insert_eq :
  forall x l y, insert (x :: l) y = if y <=? x then y :: x :: l else x :: insert l y.
Proof.
  reflexivity.
Qed.

Require Import Psatz.

Lemma lem_insert_sorted_hlp :
  forall l x y, x <=? y -> sorted (x :: l) -> sorted (x :: insert l y).
Proof.
  induction l as [| a l IHl].
  - bsolve.
  - intros x y H1 H2.
    inversion H2.
    rewrite lem_insert_eq.
    destruct (y <=? a) eqn:Heq.
    + rewrite lem_sorted_eq in *.
      apply andE.
      apply andE in H2.
      firstorder using lem_sorted_1.
    + rewrite lem_sorted_eq in *.
      apply andE.
      apply andE in H2.
      split; [ tauto | apply IHl; [ idtac | tauto ] ].
      apply PeanoNat.Nat.leb_gt in Heq.
      apply PeanoNat.Nat.leb_le.
      lia.
Qed.

Search (_ < _ -> _ <= _).

Ltac bdestruct Heq :=
  match goal with
    [ |- context[?a <=? ?b] ] =>
    destruct (a <=? b) eqn:Heq;
    [ idtac | apply PeanoNat.Nat.leb_gt in Heq;
              apply PeanoNat.Nat.lt_le_incl in Heq;
              apply PeanoNat.Nat.leb_le in Heq ]
  end.

Lemma lem_insert_sorted_hlp' :
  forall l x y, x <=? y -> sorted (x :: l) -> sorted (x :: insert l y).
Proof.
  induction l as [| a l IHl].
  - bsolve.
  - intros x y H1 H2.
    rewrite lem_insert_eq.
    bdestruct Heq; rewrite lem_sorted_eq in *; apply andE; apply andE in H2.
    + firstorder using lem_sorted_1.
    + firstorder.
Qed.

Lemma lem_insert_sorted (l : list nat) (x : nat) :
  sorted l -> sorted (insert l x).
Proof.
  revert x.
  induction l as [| a l Hl].
  - bsolve.
  - intros x H.
    rewrite lem_insert_eq.
    bdestruct Heq.
    + rewrite lem_sorted_eq.
      bsolve.
    + auto using lem_insert_sorted_hlp.
Qed.
