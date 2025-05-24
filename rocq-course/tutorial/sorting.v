(* Tutorial 8: Sorting *)

(****************************************************************)
(* Permutations *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Sorting.Permutation.

Print Permutation.

Print List.rev.

Lemma lem_rev_perm {A} :
  forall l : list A, Permutation l (List.rev l).
Proof.
  induction l as [|x l IHl].
  - constructor.
  - simpl.
    Print Permutation.
Abort.

Lemma lem_app_perm {A} :
  forall (x : A) (l : list A), Permutation (x :: l) (l ++ [x]).
Proof.
  intros x l.
  induction l as [|a l IHl].
  - trivial.
  - simpl.
    Print Permutation.
    (* eapply perm_trans.
    + apply perm_swap.
    + apply perm_skip. *)
    Fail solve [ auto using Permutation ].
    Print Permutation.
    eauto using Permutation.
Qed.

SearchPattern (Permutation (_ :: _) (_ ++ _)).

Lemma lem_rev_perm {A} :
  forall l : list A, Permutation l (List.rev l).
Proof.
  induction l as [|x l IHl].
  - trivial.
  - simpl.
    eauto using Permutation, lem_app_perm.
Qed.

(*************************************************************)
(* Insertion sort *)

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

(* "Sorted" is the smallest relation which satisfies:
  Sorted_0: Sorted []
  Sorted_1: forall x, Sorted [x]
  Sorted_2: forall x y l, x <= y -> Sorted (y :: l) ->
                          Sorted (x :: y :: l).

  "Sorted l" holds iff it is inhabited, i.e., there exists
  an element of "Sorted l"
*)

Inductive Sorted : list nat -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, x <= y -> Sorted (y :: l) ->
                           Sorted (x :: y :: l).

Example ex1: Sorted [1; 2; 4; 11].
Proof.
  constructor.
  Locate "<=".
  Print le.
  constructor.
  Restart.
  repeat constructor.
Qed.

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

Require Import Lia. (* Needed for "lia" *)
Require Import PeanoNat. (* Needed for "Nat.leb_spec" *)

Lemma lem_insert_sorted :
  forall l x, Sorted l -> Sorted (insert l x).
Proof.
  intros l x H.
  (* Heuristic: generalise the statement before invoking induction. *)
  revert x.
  induction H as [|x|x y l H1 H2 IH].
  - constructor.
  - simpl.
    intro y.
    destruct (y <=? x).
    Undo.
    (* When destructing a non-variable term we need the "eqn:" option
       to introduce an appropriate equality to the context in each
       case. *)
    destruct (y <=? x) eqn:H.
    + repeat constructor.
      Search (_ <=? _).
      apply Compare_dec.leb_complete.
      assumption.
    + repeat constructor.
      Search (_ <=? _).
      assert (x < y) by auto using Compare_dec.leb_complete_conv.
      auto with arith.
      (* The auto database "arith" contains lemmas concerning arithmetic. *)
      (* We could have used "lia" here as well. *)
  - intro z.
    simpl.
    (* Destructing boolean comparisons directly is annoying.
       Let's try something better. *)
    Search (_ <=? _).
    Print BoolSpec.
    (* "BoolSpec P Q b" means:
       1. P holds iff b = true, and
       2. Q holds iff b = false *)
    (* BoolSpecT : P -> BoolSpec P Q true
       BoolSpecF : Q -> BoolSpec P Q false *)
    Check Nat.leb_spec.
    Check Nat.leb_spec z x.
    (* Destructing (Nat.leb_spec z x) will create two subgoals: one in
       which we have a proof of (z <= x) and (z <=? x) is true; and one in
       which we have a proof of (x < z) and (z <=? x) is false. *)
    destruct (Nat.leb_spec z x).
    + auto using Sorted.
    + destruct (Nat.leb_spec z y); auto using Sorted with arith.
      assert (HH: Sorted (insert (y :: l) z)) by auto.
      simpl in HH.
      destruct (Nat.leb_spec z y).
      * lia.
      * auto using Sorted.
Qed.

Lemma lem_insert_sorted' : forall l x, Sorted l -> Sorted (insert l x).
Proof.
  intros l x H.
  revert x.
  induction H as [|x|x y l H1 H2 IH].
  - constructor.
  - simpl.
    intro y.
    destruct (Nat.leb_spec y x); auto using Sorted with arith.
  - intro z.
    simpl.
    destruct (Nat.leb_spec z x); auto using Sorted with arith.
    assert (HH: Sorted (insert (y :: l) z)) by auto.
    simpl in HH.
    destruct (Nat.leb_spec z y); auto using Sorted with arith.
Qed.

Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_isort_sorted : forall l, Sorted (isort l).
Proof.
  induction l as [|x l IH].
  - constructor.
  - simpl.
    auto using lem_insert_sorted.
Qed.

(* But is this specification enough? *)

Definition ridiculous_sort (l : list nat) : list nat := [].

Lemma lem_ridiculous_sort_sorted : forall l, Sorted (ridiculous_sort l).
Proof.
  auto using Sorted.
Qed.

(* We proved an important property of "isort": that its result is a
   sorted list. But a full specification of "isort" must also say that
   the elements of "isort l" are exactly the elements of "l" in a
   different order, i.e., "isort l" is a permutation of "l" *)

Require Import Sorting.Permutation.

Print Permutation.

(* Exercise: forall l, Permutation (isort l) l *)

(* Making sure your specification is correct *)

Print List.nth.

Lemma lem_sorted_correct_1 :
  forall l, Sorted l ->
            forall i j, i < j < List.length l ->
                        List.nth i l 0 <= List.nth j l 0.
Proof.
  intros l H.
  induction H as [|x|x y l H1 H2 IH].
  - simpl.
    destruct i, j; lia.
  - simpl.
    destruct i, j; lia.
  - intros i j H.
    destruct i as [|i]; destruct j as [|j]; try lia.
    + destruct j; auto.
      assert (y <= List.nth (S j) (y :: l) 0).
      { Fail apply IH.
        apply IH with (i := 0).
        simpl in *.
        lia. }
      change (x <= List.nth (S j) (y :: l) 0).
      lia.
    + change (List.nth i (y :: l) 0 <= List.nth j (y :: l) 0).
      apply IH.
      simpl in *; lia.
Qed.

(* Exercise (tedious): prove the other direction:

  forall l,
    (forall i j, i < j < List.length l -> List.nth i l 0 <= List.nth j l 0) ->
    Sorted l.
*)
