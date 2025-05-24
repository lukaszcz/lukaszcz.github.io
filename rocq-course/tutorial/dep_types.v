(* Tutorial 12: Dependent types *)

From Hammer Require Import Tactics.
Require Extraction.

(* Subset types *)

Definition pred (n : nat) : option nat :=
  match n with
  | 0 => None
  | S m => Some m
  end.

Lemma lem_pred :
  forall n, n > 0 ->
    exists m, pred n = Some m /\ S m = n.
Proof.
  sauto.
Qed.

Extraction pred.

Print eq_refl.

Definition pred1 (n : nat) : n <> 0 -> nat :=
  (* We match on "n" before fixing "p", so the type of "p" is "0 <> 0"
     in the first branch and "S m <> 0" in the second branch *)
  match n with
  | 0 => fun p : 0 = 0 -> False => match p (@eq_refl nat 0) with end
  | S m => fun _ => m
  end.

Print pred1.

Extraction pred1.

Fail Definition pred1 (n : nat) (p : n <> 0) : nat :=
  (* We match on "n" after fixing "p", so the type of
     "p" is "n <> 0" inside both branches *)
  match n with
  | 0 => match p eq_refl with end
  | S m => m
  end.

Print sig.
(* An element of a subset type { x : A | P x } is a dependent pair
   "exist P x p" where the first component is an element "x" of type
   "A" and the second component is a proof "p" of "P x". *)
(* Compare with existentials "ex". *)
Print ex.

Definition pred2 (s : {n : nat | n <> 0}) : nat :=
  match s with
  | exist _ 0 p => match p eq_refl with end
  | exist _ (S m) _ => m
  end.

Extraction pred2.

(* "proj1_sig" is the first projection for subset types *)
Print proj1_sig.

(* forall s : {n : nat | n <> 0}, {m : nat | S m = proj1_sig s} *)

Definition pred3 (s : {n : nat | n <> 0}) : {m : nat | S m = proj1_sig s}.
refine(
  match s with
  | exist _ 0 p => match p eq_refl with end
  | exist _ (S m) _ => exist _ m _
  (* The last hole in "exist _ m _" corresponds to
     the generated subgoal *)
  end).
Proof.
  simpl.
  reflexivity.
Defined.
(* Ending a tactic proof with "Defined" instead of "Qed" makes the
   definition transparent - it can be unfolded by Coq's computation
   mechanism. If ended with "Qed" the definition is opaque - it is not
   unfolded for computation. *)

Lemma one_not_zero : 1 <> 0.
Proof.
  discriminate.
Qed.

Compute proj1_sig (pred3 (exist _ 1 one_not_zero)).

Extraction pred3.

Require Import Program.

(* The "Program" command automatically inserts the right conversion
   between elements of subset types and their first components. The
   proofs that need to be provided for second components are turned
   into subgoals which the "Program" command tries to solve with the
   "program_simpl" tactic. *)
Program Definition pred4 (s : {n : nat | n <> 0}) :
    {m : nat | S m = proj1_sig s} :=
  match s with
  | 0 => _
  | S m => m
  end.

Extraction pred4.

(* Dependent products *)

Print sigT.
(* Dependent products are analogous to subset types except that the
   second component is not a proof but an element of a type in
   universe Type. *)

(* Coproducts *)

Print sumbool.

Print Nat.eqb.
(* In comparison to booleans, elements of "sumbool" contain additional
   information - a proof that a given case actually holds. *)

(* The function eq_nat_dec takes two numbers and checks whether they
   are equal. The result of the function contains a proof that the
   numbers are equal or a proof that they are not. *)
Definition eq_nat_dec (n m : nat) : {n = m} + {n <> m}.
  (* The "decide equality" tactic can automatically decide equality
     for certain inductive types. *)
  decide equality.
Defined.

Print sumbool.
Print in_right.

Compute eq_nat_dec 0 1.

Inductive tree A := leaf (x : A) | node (x : A) (l r : tree A).

Definition EqDec (A : Type) := forall x y : A, {x = y} + {x <> y}.

Definition eq_tree_dec {A} : EqDec A -> EqDec (tree A).
  unfold EqDec.
  intros.
  decide equality.
Defined.

Print sumor.

Print sum.
