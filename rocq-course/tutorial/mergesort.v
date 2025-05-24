(* Tutorial 13: Mergesort and the Function command *)

From Hammer Require Import Tactics.
From Hammer Require Import Reflect. (* declares "is_true" as a coercion *)

Require List.
Open Scope list_scope.
Import List.ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Sorting.Permutation.
Require Import Recdef. (* for the Function command *)

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total : forall x y, leb x y \/ leb y x;
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Print DecTotalOrder.
(* "Record" is a special notation for an inductive type with exactly
   one constructor. *)
(* A typeclass is just an inductive type with one constructor. The
   difference is in the search algorithm for implicit arguments in a
   typeclass. *)

Arguments leb {A _}.
Arguments leb_total {A _}.
Arguments leb_antisym {A _}.
Arguments leb_trans {A _}.

Inductive DecTotalOrderI (A : Type) :=
  Build_DecTotalOrderI : forall leb : A -> A -> bool,
    (forall x y, leb x y \/ leb y x) ->
    (forall x y, leb x y -> leb y x -> x = y) ->
    (forall x y z, leb x y -> leb y z -> leb x z) ->
    DecTotalOrderI A.

Definition lebI (A : Type) (d : DecTotalOrderI A) :=
  match d with Build_DecTotalOrderI _ leb _ _ _ => leb end.

Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.

Definition leb_total_dec {A} {dto : DecTotalOrder A}
  : forall x y, {leb x y}+{leb y x}.
  intros x y.
  sdestruct (leb x y).
  - left; constructor.
  - right; destruct (leb_total x y); auto.
Defined.

Inductive Sorted {A} {dto : DecTotalOrder A} : list A -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, leb x y ->
                           Sorted (y :: l) ->
                           Sorted (x :: y :: l).

Lemma lem_sorted_tail {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) -> Sorted l.
Proof.
  inversion 1; sauto.
Qed.

Definition LeLst {A} {dto : DecTotalOrder A} (x : A) (l : list A) :=
  List.Forall (leb x) l.

Lemma lem_lelst_nil {A} {dto : DecTotalOrder A} : forall x, LeLst x [].
Proof.
  sauto.
Qed.

Lemma lem_lelst_cons {A} {dto : DecTotalOrder A} :
  forall x y l, LeLst x l -> leb x y -> LeLst x (y :: l).
Proof.
  sauto.
Qed.

Local Hint Resolve lem_lelst_nil lem_lelst_cons : lelst.

Lemma lem_lelst_trans {A} {dto : DecTotalOrder A} :
  forall l y, LeLst y l -> forall x, leb x y -> LeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  (* induction l; best *)
  induction l; sauto lq: on rew: off use: lem_lelst_trans.
Qed.

Lemma lem_lelst_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l1 -> LeLst x l2.
Proof.
  induction 1; sauto lq: on rew: off.
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l2 -> LeLst x l1.
Proof.
  induction 1; sauto lq: on.
Qed.

Lemma lem_lelst_concat {A} {dto : DecTotalOrder A} :
  forall l1 x, LeLst x l1 -> forall l2, LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto lq: on.
Qed.

Local Hint Resolve lem_lelst_trans lem_lelst_perm lem_lelst_perm_rev lem_lelst_concat : lelst.

Definition length_sum {A} (p : list A * list A) :=
  match p with
  | (l1, l2) => List.length l1 + List.length l2
  end.

Function merge {A} {dto : DecTotalOrder A}
  (p : list A * list A) {measure length_sum p} : list A :=
  match fst p with
  | [] => snd p
  | h1 :: t1 =>
    match snd p with
    | [] => h1 :: t1
    | h2 :: t2 =>
      if leb h1 h2 then
        h1 :: merge (t1, snd p)
      else
        h2 :: merge (fst p, t2)
    end
  end.
Proof.
  all: sauto.
Defined.

Arguments merge {_ _}.

Function split {A} (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
    match split t with
    | (l1, l2) => (x :: l1, y :: l2)
    end
  end.

Lemma lem_split_sum {A} : forall l : list A,
    forall l1 l2, split l = (l1, l2) ->
                  length l = length l1 + length l2.
Proof.
  intro l.
  functional induction (split l); sauto.
Qed.

Lemma lem_split {A} : forall l : list A,
    2 <= List.length l ->
    forall l1 l2, split l = (l1, l2) ->
    List.length l1 < List.length l /\
    List.length l2 < List.length l.
Proof.
  intros [|x [|y l]]; hauto use: lem_split_sum.
Qed.

Function msort {A} {dto : DecTotalOrder A} (l : list A)
  {measure List.length l} : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
    match split l with
    | (l1, l2) => merge (msort l1, msort l2)
    end
  end.
Proof.
  all:
    intros; assert (Hlen: 2 <= length l) by sauto;
    hauto use: (lem_split l Hlen).
Defined.

Arguments msort {_ _}.

Compute (msort [2; 7; 3; 1; 4; 6; 5; 8; 0; 8]).

Require Extraction.

Recursive Extraction msort.

Lemma lem_merge_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation (merge (l1, l2)) (l1 ++ l2).
Proof.
  enough (forall p, Permutation (merge p) (fst p ++ snd p)) by sauto.
  intro p.
  functional induction (merge p) as [ | | | ? ? ? ? ? ? E].
  - sauto.
  - sauto db: list.
  - sauto db: list.
  - rewrite E; hauto use: Permutation_middle.
Qed.

Lemma lem_sorted_concat_1 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (l1 ++ y :: l2) -> Sorted (x :: l1) -> leb x y ->
    Sorted (y :: l2) -> Sorted l -> Sorted (x :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Lemma lem_sorted_concat_2 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (x :: l1 ++ l2) -> Sorted (x :: l1) -> leb y x ->
    Sorted (y :: l2) -> Sorted l -> Sorted (y :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Lemma lem_merge_sorted {A} {dto : DecTotalOrder A} :
  forall l1 l2, Sorted l1 -> Sorted l2 -> Sorted (merge (l1, l2)).
Proof.
  enough (forall p, Sorted (fst p) -> Sorted (snd p) -> Sorted (merge p)) by sauto.
  intro p.
  functional induction (merge p) as [ | | ? h1 t1 E1 h2 t2 E2 |
                                      ? h1 t1 E1 h2 t2 E2 ].
  - sauto.
  - sauto.
  - simpl in *.
    intros.
    rewrite E1 in *.
    rewrite E2 in *.
    assert (Sorted (merge (t1, h2 :: t2))).
    { qauto use: lem_sorted_tail. }
    hauto use: lem_sorted_concat_1, lem_merge_perm.
  - simpl in *.
    intros.
    rewrite E1 in *.
    rewrite E2 in *.
    assert (Sorted (merge (h1 :: t1, t2))).
    { qauto use: lem_sorted_tail. }
    eapply lem_sorted_concat_2; hauto use: leb_total, lem_merge_perm.
Qed.

Lemma lem_split_perm {A} :
  forall l l1 l2 : list A, split l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  intro l.
  functional induction (split l).
  - hauto.
  - hauto.
  - hauto use: perm_skip, Permutation_cons_app.
Qed.

Lemma lem_msort_perm {A} {dto : DecTotalOrder A} :
  forall l, Permutation (msort l) l.
Proof.
  intro l.
  functional induction (msort l) as [ | | ? ? ? ? l1 l2 ].
  - sauto.
  - sauto.
  - assert (HH1: Permutation (l1 ++ l2) l).
    { hauto use: (lem_split_perm l l1 l2), Permutation_sym. }
    assert (Permutation (merge (msort l1, msort l2)) (msort l1 ++ msort l2)).
    { hauto use: (lem_merge_perm (msort l1) (msort l2)). }
    assert (Permutation (msort l1 ++ msort l2) (l1 ++ l2)).
    { hauto use: Permutation_app. }
    assert (HH2: Permutation (merge (msort l1, msort l2)) (l1 ++ l2)).
    { eapply perm_trans; eassumption. }
    eapply perm_trans; eassumption.
Qed.

Lemma lem_msort_sorted {A} {dto : DecTotalOrder A} :
  forall l, Sorted (msort l).
Proof.
  intro l.
  functional induction (msort l).
  - hauto.
  - hauto.
  - hauto use: lem_merge_sorted.
Qed.
