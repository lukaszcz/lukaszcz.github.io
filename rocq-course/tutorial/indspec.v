(* Tutorial 6: Inductive specifications *)

(* "Even" is the smallest relation on "nat" such that:
   1. Even 0
   2. forall n, Even n -> Even (S (S n))

   "Even n" holds iff an element of the inductive type (a proof of)
   "Even n" may be constructed using the constructors "Even_0" and
   "Even_S".
*)
Inductive Even : nat -> Prop :=
| Even_0 : Even 0
| Even_S : forall n, Even n -> Even (S (S n)).

Fail Inductive Even' (n : nat) : Prop :=
| Even_0' : Even' 0
| Even_S' : Even' n -> Even' (S (S n)).

Require Import Lia.

Lemma lem_even_1 : forall n, Even (2 * n).
Proof.
  induction n as [|n IHn].
  - apply Even_0.
  - assert (Heq: 2 * S n = S (S (2 * n))) by lia.
    rewrite Heq.
    apply Even_S.
    assumption.
Qed.

Lemma lem_even_3 : forall n, Even n -> Even (3 * n).
Proof.
  intros n H.
  (* We can do induction on the proof "H" of "Even n". This often
     results in a simpler proof than doing induction on "n". *)
  induction H as [|n H IH].
  - apply Even_0.
  - assert (Heq: 3 * S (S n) = S (S (S (S (S (S (3 * n))))))) by lia.
    rewrite Heq.
    auto using Even.
Qed.

Lemma lem_even_destruct :
  forall n, Even n -> n = 0 \/ exists m, Even m /\ n = m + 2.
Proof.
  intros n H.
  Print Even.
  destruct H as [|m H1].
  - auto.
  - right.
    exists m.
    split; [ assumption | lia ].
Qed.

Lemma lem_even_twice :
  forall n, Even n -> exists m, n = 2 * m.
Proof.
  intros n H.
  induction H as [|n H IH].
  - exists 0; auto.
  - destruct IH as [m Hm].
    Fail lia.
    exists (S m).
    lia.
Qed.

Lemma lem_even_SS : forall n, Even (S (S n)) -> Even n.
Proof.
  intros n H.
  destruct H as [|m H].
  Show 2.
  Undo.
  remember (S (S n)) as x eqn:Heq.
  destruct H as [|m H].
  - discriminate Heq.
  - injection Heq.
    intro H1.
    rewrite <- H1.
    assumption.
Qed.

Lemma lem_even_SS' : forall n, Even (S (S n)) -> Even n.
Proof.
  intros n H.
  (* The "inversion" tactic automatically adds to the context the
     equations on the arguments of the inductive predicate. If these
     equations become contradictory in a given subgoal, it
     automatically solves the subgoal. *)
  inversion H as [|m H' Heq].
  assumption.
Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S m) => evenb m
  end.

Lemma lem_even_evenb : forall n, evenb n = true <-> Even n.
Proof.
  split.
  - induction n as [|n IH].
    + auto using Even.
    + intro H.
      simpl in H.
      destruct n as [|n].
      * discriminate H.
      *
Abort.

Lemma lem_evenb_to_even : forall n, evenb n = true -> Even n.
Proof.
  enough (forall n m, m < n -> evenb m = true -> Even m).
  { eauto with arith. }
  induction n as [|n IH].
  - intros; lia.
  - intros m H1 H2.
    destruct m as [|m].
    + apply Even_0.
    + simpl in H2.
      destruct m as [|m].
      * discriminate H2.
      * assert (m < n) by lia.
        auto using Even.
Qed.

Lemma lem_evenb_to_even' : forall n, evenb n = true -> Even n.
Proof.
  enough (forall n, (forall m, m < n -> evenb m = true -> Even m)).
  { eauto with arith. }
  induction n as [|n IH].
  - lia.
  - intros m H1 H2.
    destruct m as [|[|m]].
    + apply Even_0.
    + simpl in H2. discriminate H2.
    + simpl in H2.
      assert (m < n) by lia.
      auto using Even.
Qed.

Lemma lem_even_to_evenb : forall n, Even n -> evenb n = true.
Proof.
  induction n as [|n IH].
  - trivial.
  - intro H.
    simpl.
    destruct n as [|n].
    Show 2.
Abort.

Lemma lem_even_to_evenb : forall n, Even n -> evenb n = true.
Proof.
  intros n H.
  induction H as [|n H IH].
  - trivial.
  - simpl.
    assumption.
Qed.

Lemma lem_even_to_evenb' : forall n, Even n -> evenb n = true.
Proof.
  intros n H; induction H; trivial.
Qed.
