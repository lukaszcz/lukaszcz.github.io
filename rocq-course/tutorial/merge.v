(* Tutorial 18: Dependent merge *)

From Hammer Require Import Tactics.
From Hammer Require Import Reflect. (* declares "is_true" as a coercion *)
(* Coercion is_true : bool >-> Sortclass. *)

Require List.
Open Scope list_scope.
Import List.ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Sorting.Permutation.
Require Import Program.

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total_dec : forall x y, {leb x y}+{leb y x};
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Arguments leb {A _}.
Arguments leb_total_dec {A _}.
Arguments leb_antisym {A _}.
Arguments leb_trans {A _}.

Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.

Inductive Sorted {A} {dto : DecTotalOrder A} : list A -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y, leb x y ->
                         forall l, Sorted (y :: l) ->
                                   Sorted (x :: y :: l).

Lemma lem_sorted_tail {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) -> Sorted l.
Proof.
  inversion 1; sauto.
Qed.

(* LeLst x l means that for all y in l we have leb x y *)
Inductive LeLst {A} {dto : DecTotalOrder A} : A -> list A -> Prop :=
| LeLst_0 : forall x, LeLst x []
| LeLst_1 : forall x y l, leb x y -> LeLst x l -> LeLst x (y :: l).

Lemma lem_lelst_trans {A} {dto : DecTotalOrder A} :
  forall l y, LeLst y l -> forall x, leb x y -> LeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  (* induction l; sintuition. *)
  (* simplification tactics: sintuition, qsimpl, ssimpl *)
  (* induction l; qsimpl. (* we have LeLst a l, so also LeLst a (a :: l) *) *)
  (* time (induction l; sauto use: lem_lelst_trans). *) (* 0.6s *)
  (* induction l; sauto use: lem_lelst_trans inv: Sorted, LeLst. *)
  (* induction l; sauto use: lem_lelst_trans inv: Sorted. *)
  (* induction l; sauto use: lem_lelst_trans inv: LeLst. *)
  time (induction l;
          hauto use: lem_lelst_trans inv: Sorted, LeLst ctrs: Sorted). (* 0.4s *)
Qed.

Lemma lem_lelst_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l1 -> LeLst x l2.
Proof.
  (* induction 1; sauto. *) (* hauto is essentially sauto inv: - ctrs: - *)
  (* induction 1; hauto ctrs: LeLst. *)
  induction 1; hauto inv: LeLst ctrs: LeLst.
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l2 -> LeLst x l1.
Proof.
  induction 1; hauto inv: LeLst ctrs: LeLst.
Qed.

Lemma lem_lelst_concat {A} {dto : DecTotalOrder A} :
  forall l1 x, LeLst x l1 -> forall l2, LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto.
Qed.

Hint Resolve lem_lelst_trans lem_lelst_perm lem_lelst_perm_rev lem_lelst_concat : lelst.

Lemma lem_sorted_concat_1 {A} {dto : DecTotalOrder A} :
  forall (l1 : list A) x, Sorted (x :: l1) -> forall l2 y,
      leb x y -> Sorted (y :: l2) -> forall l,
        Permutation l (l1 ++ y :: l2) -> Sorted l ->
        Sorted (x :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Lemma lem_sorted_concat_2 {A} {dto : DecTotalOrder A} :
  forall (l1 : list A) x, Sorted (x :: l1) -> forall l2 y,
      leb y x -> Sorted (y :: l2) -> forall l,
        Permutation l (x :: l1 ++ l2) -> Sorted l ->
        Sorted (y :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Program Fixpoint merge {A} {dto : DecTotalOrder A}
  (l1 l2 : {l : list A | Sorted l})
  {measure (List.length l1 + List.length l2)} :
  {l : list A | Sorted l /\ Permutation l (l1 ++ l2)} :=
  match l1 with
  | [] => l2
  | h1 :: t1 =>
    match l2 with
    | [] => l1
    | h2 :: t2 =>
      (* match leb_total_dec h1 h2 with
         | left H => h1 :: merge t1 l2
         | right H => h2 :: merge l1 t2
         end *)
      if leb_total_dec h1 h2 then
        h1 :: merge t1 l2
      else
        h2 :: merge l1 t2
    end
  end.
Next Obligation.
  sauto db: list.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  Locate "`".
  Print proj1_sig.
  match goal with
  | [ |- context[merge A dto ?X ?Y ?Z] ] =>
    destruct (merge A dto X Y Z)
  end.
  simpl in *.
  sauto use: lem_sorted_concat_1.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  simpl; lia.
Qed.
Next Obligation.
  match goal with
  | [ |- context[merge A dto ?X ?Y ?Z] ] =>
    destruct (merge A dto X Y Z)
  end.
  simpl in *.
  split.
  - sauto use: lem_sorted_concat_2.
  - Search (Permutation _ (_ ++ _ :: _)).
    Fail apply Permutation_cons_app.
    Search (_ :: _ ++ _).
    rewrite List.app_comm_cons.
    apply Permutation_cons_app.
    strivial.
Qed.

Print sig.

Definition l1 : {l : list nat | Sorted l}.
  refine (exist _ [1; 3; 7; 8] _).
  repeat constructor.
Defined.

Definition l2 : {l : list nat | Sorted l}.
  refine (exist _ [2; 3; 4; 6; 9] _).
  repeat constructor.
Defined.

Print l1.

Check merge l1 l2.
Locate "`".
Check proj1_sig.

Compute ` (merge l1 l2).

Fixpoint sortedb {A} {dto : DecTotalOrder A} (l : list A) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: ((y :: l) as l') =>
    if leb x y then
      sortedb l'
    else
      false
  end.

Lemma lem_sortedb {A} {dto : DecTotalOrder A} : forall l, sortedb l -> Sorted l.
Proof.
  induction l; simpl; hauto red: off rew: off ctrs: Sorted.
  (* For goals involving boolean coercions `sauto' sometimes works
     better with (eager) reduction and/or rewriting turned off. *)
  (* red: off - turn reduction (simpl) off *)
  (* ered: off - turn eager reduction (simpl) off
                 (still performed with backtracing) *)
  (* rew: off - turn rewriting off *)
  (* erew: off - turn eager rewriting off *)
Qed.

Definition cast_sorted {A} {dto : DecTotalOrder A} (l : list A) :
  sortedb l -> {l | Sorted l}.
Proof.
  intro H.
  refine (exist _ l _).
  apply lem_sortedb; assumption.
Defined.

(* sortedb l = true *)

Notation "% l" := (cast_sorted l eq_refl) (at level 5) : list_scope.

Compute %[1; 2; 3].
Fail Compute %[2; 3; 1].

Compute ` (merge %[1; 2; 7; 8; 9] %[0; 3; 4; 5; 6; 10; 11; 12; 13; 14]).

Require Import FunInd.

Functional Scheme sortedb_ind := Induction for sortedb Sort Prop.

Print R_sortedb.
