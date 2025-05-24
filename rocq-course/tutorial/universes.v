(* Tutorial 7: Universes and axioms *)

(************************************************************************************)
(* Proof of falsity with non-total function definitions *)

Fail Fixpoint loop (n : nat) : False := loop n.

Fail Fixpoint loop (n : nat) : False :=
  match n with
  | S m => loop m
  end.

(************************************************************************************)
(* Universes and impredicativity of Prop *)

Set Printing Universes.

Check Set.
Check Type.
Check nat.
Check nat -> nat.
Check (forall A : Set, A).
Check (forall A : Type, A).
Check (forall A : Prop, A).

Definition id {T : Set} (x : T) : T := x.

Check id 0.
Fail Check id Set.
Fail Check id (@id).

Definition identity {T : Type} (x : T) : T := x.

Check @identity.
Check identity 0.
Check identity Set.
Check identity Type.
Fail Check identity (@identity).

Check @identity.
Check (forall T : Type, T -> T).
Check (forall T : Prop, T -> T).

Definition pidentity {T : Prop} (x : T) : T := x.

Check @pidentity.

Check pidentity (@pidentity).
Fail Check pidentity Set.

Fixpoint arrows n (A : Set) : Set :=
  match n with
  | 0 => A
  | S m => A -> arrows m A
  end.

Check arrows.
Compute (arrows 3 nat).
Compute (arrows 3 (arrows 3 nat)).

Fixpoint arrows' n (A : Set) : Type :=
  match n with
  | 0 => A
  | S m => A -> arrows' m A
  end.

Compute (arrows' 3 nat).
Fail Compute (arrows' 3 (arrows' 3 nat)).

Unset Printing Universes.

(************************************************************************************)
(* Axioms and computation *)

(* "Fin n" represents the type of natural numbers smaller than n *)
Inductive Fin : nat -> Set :=
| Zero : forall {n}, Fin (S n)
| Succ : forall {n}, Fin n -> Fin (S n).

Check Zero.
Check (Succ Zero).

Fixpoint fin_to_nat {k} (n : Fin k) : nat :=
  match n with
  | Zero => 0
  | Succ m => S (fin_to_nat m)
  end.

Compute (fin_to_nat (Succ (Succ Zero))).

Fixpoint nat_to_fin (n : nat) : Fin (S n) :=
  match n with
  | 0 => Zero
  | S m => Succ (nat_to_fin m)
  end.

Compute (nat_to_fin 10).
Compute (fin_to_nat (nat_to_fin 10)).

Locate "=".
Print eq.

Definition cast {A B : Set} (p : A = B) (x : A) : B :=
  match p with
  | eq_refl => x
  end.

Print cast.

Check (eq_refl (nat->nat)).

Compute cast (eq_refl (nat -> nat)) (fun x => x + 10) 0.

Lemma lem_fin_eq : forall n, Fin (S n) = Fin (n + 1).
Proof.
  intro n.
  assert (H : S n = n + 1).
  { induction n; simpl; auto. }
  auto.
Qed.

Check nat_to_fin.

Require Import FunctionalExtensionality.

Lemma lem_cast_1 : (forall n, Fin (S n)) = (forall n, Fin (n + 1)).
Proof.
  change ((forall n, (fun n => Fin (S n)) n) =
          (forall n, (fun n => Fin (n + 1)) n)).
  Check functional_extensionality.
  rewrite (functional_extensionality
              (fun n => Fin (S n))
              (fun n => Fin (n + 1))
              lem_fin_eq).
  reflexivity.
Qed.

Check cast.
Check nat_to_fin.

Fail Compute (cast lem_cast_1 nat_to_fin 10).
Set Printing All.
Fail Compute (cast lem_cast_1 nat_to_fin 10).
Unset Printing All.

Lemma lem_cast_2 : (forall n, Fin (S n)) = (forall n, Fin (n + 1)) :> Set.
Proof.
  change ((forall n, (fun n => Fin (S n)) n) =
          (forall n, (fun n => Fin (n + 1)) n) :> Set).
  rewrite (functional_extensionality
            (fun n => Fin (S n))
            (fun n => Fin (n + 1))
            lem_fin_eq).
  reflexivity.
Qed.

Compute (cast lem_cast_2 nat_to_fin 10).

(* Proofs finished with "Qed" are not "transparent" -- they are not
   unfolded by the computation mechanism. We need to use "Defined" to
   make a definition transparent. *)

Definition def_fin_eq : forall n, Fin (S n) = Fin (n + 1).
  intro n.
  assert (H : S n = n + 1).
  { induction n; simpl; auto. }
  auto.
Defined.

Definition def_cast : (forall n, Fin (S n)) = (forall n, Fin (n + 1)) :> Set.
  change ((forall n, (fun n => Fin (S n)) n) = (forall n, (fun n => Fin (n + 1)) n) :> Set).
  rewrite (functional_extensionality (fun n => Fin (S n)) (fun n => Fin (n + 1)) def_fin_eq).
  reflexivity.
Defined.

(* nat_to_fin : forall n : nat, Fin (S n) *)
(* cast : forall {A B : Set}, A = B -> A -> B *)

Compute (cast def_cast nat_to_fin 10).
Compute (cast (def_fin_eq 10) (nat_to_fin 10)).

(* Fortunately, because in Coq matches on proofs that create programs
   are restricted, it rarely happens that adding axioms in Prop
   results in blocked computations of programs. *)

(* Moreover, the restrictions on proof matching are such that
   extraction works well with axioms in Prop. *)

Definition nat_to_fin' := cast def_cast nat_to_fin.

Require Extraction.
Extraction Language Haskell.

Recursive Extraction nat_to_fin'.

(* However, axioms not in Prop *may* compromise computation of
   programs more severely, making extraction produce useless code. *)

Require Import IndefiniteDescription.

Check constructive_indefinite_description.
Print sig.
(* { x : A | P x } represents a "subset type" of A determined by the
   predicate P *)
(* We'll talk more about subset types later. Now we use them only to
   illustrate what can go wrong with axioms. *)

Lemma lem_ex : forall n, exists m, m > n.
Proof.
  intro n.
  exists (S n).
  auto.
Defined.

Definition increase (n : nat) : { m | m > n }.
  generalize (lem_ex n).
  intro H.
  Fail destruct H as [m H].
  (* Coq doesn't allow to produce programs from proofs, except in very
     restricted circumstances (more about this later). *)
  Print constructive_indefinite_description.
  generalize (constructive_indefinite_description (fun m => m > n) H).
  (* The axiom gets around this restriction. *)
  auto.
Defined.

Compute (increase 2).

(* The extracted function always raises an error. *)
Recursive Extraction increase.
