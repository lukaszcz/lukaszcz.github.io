(* Tutorial 10: Strong automation with CoqHammer *)

(* For the following import to work you need to install the CoqHammer
   tactics v1.3 or later. Download the v1.3 or v1.3.1 release for your
   version of Coq from:

   https://github.com/lukaszcz/coqhammer/releases

   Unpack the package and run:

   > make tactics
   > make install-tactics

   in your command line. You need an OCaml compiler >= 4.08, the
   "make" system and Coq development files. You should already have
   all of those if you installed Coq with opam. The plugin has *not*
   been tested on Windows, only on macOS and Linux. If you use Windows
   and want to install external Coq packages, it might turn out that
   it's easier to just run Coq in a virtual Linux machine.

 *)
(* It may also be possible (and probably easier) to install CoqHammer
   via opam:

   > opam repo add coq-released https://coq.inria.fr/opam/released
   > opam install coq-hammer-tactics
 *)
(*
   For a detailed manual see the CoqHammer webpage:

   https://coqhammer.github.io
 *)

From Hammer Require Import Tactics.

(* Solvers (in the order of increasing strength and decreasing speed):

   strivial, qauto, hauto, sauto
*)

(* Simplifiers (in the order of increasing strength and decreasing speed):

   simp_hyps, sintuition, qsimpl, ssimpl
*)

(* Most useful options:

use: lemma_1, ..., lemma_n

Add the given lemmas at the top of the context before invoking the
tactic. Analogous to the "using" clause in "auto".

db: db_1, ..., db_n

Use the given hint databases. Analogous to the "with"
clause in "auto".

inv: ind_1, ..., ind_n

Do inversion (case reasoning) only on elements of the given inductive
types.

ctrs: ind_1, ..., ind_n

Use constructors of only the given inductive types.

unfold: c_1, ..., c_n

Try heuristically unfolding the given constants.

unfold!: c_1, ..., c_n

Always unfold the given constants.

One can provide "-" to denote an empty list, e.g. "sauto inv: -".

By default "sauto" tries to use constructors of and do inversion on
elements of all available inductive types, while "hauto" and "qauto"
only of the explicitly specified ones.

*)

(* Automatic option choice for "sauto": best.

  The "best" tactic only chooses the best options among those
  that influence the search algorithm. It does not select
  lemmas (use:), databases (db:), inversions (inv:),
  constructors (ctrs:), or unfoldings (unfold:).
*)

(*******************************************************************)
(* Insertion sort *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Arith.
Require Import Lia.

Inductive Sorted : list nat -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, x <= y ->
                           Sorted (y :: l) ->
                           Sorted (x :: y :: l).

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_insert_sorted : forall l x, Sorted l -> Sorted (insert l x).
Proof.
  intros l x H.
  revert x.
  induction H.
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

Lemma lem_insert_sorted' : forall l x, Sorted l -> Sorted (insert l x).
Proof.
  intros l x H.
  revert x.
  induction H as [|?|x y l ? ? IH].
  - sauto.
  - sauto.
  - intro z.
    assert (Sorted (insert (y :: l) z)) by auto.
    (* sauto. *)
    qsimpl; sauto.
Qed.

Lemma lem_isort_sorted : forall l, Sorted (isort l).
Proof.
  induction l as [|x l IH].
  - auto using Sorted.
  - simpl.
    auto using lem_insert_sorted.
Qed.

Lemma lem_isort_sorted' : forall l, Sorted (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

(* "LeLst m l" holds if "m" is less or equal to each element of
   "l". *)
Inductive LeLst : nat -> list nat -> Prop :=
| LeLst_0 : forall n, LeLst n []
| LeLst_1 : forall n m l, n <= m -> LeLst n l -> LeLst n (m :: l).

Lemma lem_lelst_insert :
  forall l n m, n <= m -> LeLst n l -> LeLst n (insert l m).
Proof.
  induction l as [|x l IH].
  - simpl; auto using LeLst.
  - intros n m Hle H.
    simpl.
    destruct (Nat.leb_spec m x) as [H1|H1].
    + auto using LeLst.
    + inversion_clear H; auto using LeLst.
Qed.

Lemma lem_lelst_insert' :
  forall l n m, n <= m -> LeLst n l -> LeLst n (insert l m).
Proof.
  induction l; sauto.
Qed.

Lemma lem_lelst_sorted :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  induction l as [|x l IH].
  - split; auto using Sorted, LeLst.
  - intro y.
    split.
    + intro H.
      inversion_clear H as [| |? ? ? ? H1].
      split; [|assumption].
      constructor.
      * assumption.
      * apply IH.
        inversion_clear H1;
          eauto using Sorted with arith.
    + intros [H1 H2].
      inversion_clear H1;
        auto using Sorted.
Qed.

Lemma lem_lelst_sorted' :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  (* time (induction l; sauto db: arith). *)
  (* You need CoqHammer v1.3.1 or later for the "best" tactic. *)
  (* induction l; best db: arith. *)
  time (induction l; sauto lq: on db: arith).
Qed.

Lemma lem_insert_sorted_2 :
  forall l x, Sorted l -> Sorted (insert l x).
Proof.
  induction l as [|y l IH].
  - simpl; auto using Sorted.
  - intros x H.
    simpl.
    destruct (Nat.leb_spec x y) as [H1|H1].
    + constructor; assumption.
    + rewrite lem_lelst_sorted.
      rewrite lem_lelst_sorted in H.
      destruct H;
        auto using lem_lelst_insert with arith.
Qed.

Lemma lem_insert_sorted_2' :
  forall l x, Sorted l -> Sorted (insert l x).
Proof.
  (* Check Nat.lt_le_incl. *)
  (* induction l; best time: 2 use: lem_lelst_sorted, lem_lelst_insert, Nat.lt_le_incl. *)
  time (induction l; hfcrush use: lem_lelst_sorted, lem_lelst_insert, Nat.lt_le_incl).
Qed.

(* Tail-recursive reverse *)

Fixpoint itrev {A} (lst acc : list A) :=
  match lst with
  | [] => acc
  | h :: t => itrev t (h :: acc)
  end.

Definition rev {A} (lst : list A) := itrev lst [].

Lemma lem_itrev {A} :
  forall lst acc : list A, itrev lst acc = itrev lst [] ++ acc.
Proof.
  induction lst as [| h t IH].
  - auto.
  - intro acc.
    simpl.
    assert (H: itrev t [h] = itrev t [] ++ [h]).
    { rewrite IH; reflexivity. }
    rewrite H.
    rewrite IH.
    rewrite <- List.app_assoc.
    reflexivity.
Qed.

From Hammer Require Import Hints.
(* Provides rewriting databases: shints, sbool, slist, sarith. *)

Lemma lem_itrev' {A} :
  forall lst acc : list A, itrev lst acc = itrev lst [] ++ acc.
Proof.
  induction lst as [| h t IH].
  - auto.
  - assert (H: itrev t [h] = itrev t [] ++ [h]).
    { rewrite IH; reflexivity. }
    sauto db: slist.
Qed.

Lemma lem_rev_app {A} :
  forall l1 l2 : list A, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  unfold rev.
  induction l1 as [| x l1 IH]; intro l2.
  - simpl.
    rewrite List.app_nil_r.
    reflexivity.
  - simpl.
    rewrite lem_itrev.
    rewrite IH.
    rewrite <- List.app_assoc.
    assert (H: itrev l1 [x] = itrev l1 [] ++ [x]).
    { rewrite lem_itrev; reflexivity. }
    rewrite H.
    reflexivity.
Qed.

Lemma lem_rev_app' {A} :
  forall l1 l2 : list A, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  unfold rev.
  induction l1; sauto use: lem_itrev db: slist.
Qed.

Lemma lem_rev_rev {A} : forall l : list A, rev (rev l) = l.
Proof.
  unfold rev.
  induction l as [| x l IH].
  - reflexivity.
  - simpl.
    assert (H: itrev l [x] = itrev l [] ++ [x]).
    { rewrite lem_itrev; reflexivity. }
    rewrite H.
    clear H.
    generalize (lem_rev_app (itrev l []) [x]).
    unfold rev.
    intro H.
    rewrite H.
    clear H.
    rewrite IH.
    reflexivity.
Qed.

Lemma lem_rev_rev' {A} : forall l : list A, rev (rev l) = l.
Proof.
  unfold rev.
  induction l as [| x l IH].
  - reflexivity.
  - sauto use: (lem_itrev l [x]), (lem_rev_app (itrev l []) [x]).
Qed.

Lemma lem_rev_lst {A} : forall l : list A, rev l = List.rev l.
Proof.
  unfold rev.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite lem_itrev.
    rewrite IH.
    reflexivity.
Qed.

Lemma lem_rev_lst' {A} : forall l : list A, rev l = List.rev l.
Proof.
  unfold rev.
  induction l; sauto use: lem_itrev.
Qed.

(* Permutations *)

Require Import Sorting.Permutation.

Lemma lem_perm_length {A} :
  forall l1 l2 : list A, Permutation l1 l2 ->
    List.length l1 = List.length l2.
Proof.
  intros l1 l2 H.
  induction H as [ | | | ? ? ? ? IH1 ? IH2]; simpl; auto.
  rewrite IH1.
  rewrite IH2.
  reflexivity.
Qed.

Lemma lem_perm_length' {A} :
  forall l1 l2 : list A, Permutation l1 l2 ->
    List.length l1 = List.length l2.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_perm_sym {A} :
  forall l1 l2 : list A, Permutation l1 l2 -> Permutation l2 l1.
Proof.
  induction 1; simpl; eauto using Permutation.
Qed.

Lemma lem_perm_sym' {A} :
  forall l1 l2 : list A, Permutation l1 l2 -> Permutation l2 l1.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_perm_forall {A} (P : A -> Prop) :
  forall l1 l2, Permutation l1 l2 ->
    List.Forall P l1 -> List.Forall P l2.
Proof.
  intros l1 l2 H1 H2.
  induction H1 as [| | | ]; auto.
  - inversion H2; constructor; auto.
  - inversion H2 as [| ? ? ? [|]]; subst; constructor; auto.
Qed.

Lemma lem_perm_forall' {A} (P : A -> Prop) :
  forall l1 l2, Permutation l1 l2 ->
    List.Forall P l1 -> List.Forall P l2.
Proof.
  induction 1; sauto.
Qed.
