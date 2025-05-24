(* Tutorial 19: Equality reasoning with dependent types *)

(************************************************************************************)
(* Uniqueness of identity proofs *)

Require Import Eqdep. (* for UIP_refl *)

About UIP_refl.
Print Assumptions UIP_refl.

Require Import Arith.
Require Import Lia.

Inductive vector (A : Type) : nat -> Type :=
  vnil : vector A 0 | vcons : forall (n : nat), A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A n}.

Notation "[: :]" := vnil.
Notation "[: x :]" := (vcons x vnil).
Notation "[: x ; y ; .. ; z :]" := (vcons x (vcons y .. (vcons z vnil) ..)).

Fixpoint vapp {A n m} (v1 : vector A n) (v2 : vector A m) : vector A (n + m) :=
  match v1 with
  | vnil => v2
  | vcons x v1' => vcons x (vapp v1' v2)
  end.

Definition vcast {A} n m (p : n = m) (v : vector A n) : vector A m :=
  eq_rect n (fun k => vector A k) v m p.

Compute vcast.

Import EqNotations. (* for the "rew" notations *)

Print vcast.

Definition vcast' {A} n m (p : n = m) (v : vector A n) : vector A m :=
  rew p in v.

Compute vcast'.

Fail Lemma lem_vapp_assoc {A} :
  forall a b c (va : vector A a) (vb : vector A b) (vc : vector A c),
    vapp (vapp va vb) vc = vapp va (vapp vb vc).

Check Nat.add_assoc.

Lemma lem_vapp_assoc {A} :
  forall a b c (va : vector A a) (vb : vector A b) (vc : vector A c),
    vapp (vapp va vb) vc =
    rew (Nat.add_assoc a b c) in (vapp va (vapp vb vc)).
Proof.
  intros a b c va vb vc.
  induction va as [|d x va IH].
  - simpl.
    unfold eq_rect.
    About Nat.add_assoc.
    Fail unfold Nat.add_assoc.
    Fail destruct (Nat.add_assoc 0 b c).
    Check Eqdep_dec.UIP_refl_nat.
    rewrite (Eqdep_dec.UIP_refl_nat (b + c) (Nat.add_assoc 0 b c)).
    reflexivity.
  - simpl.
    rewrite IH.
    Fail destruct (Nat.add_assoc d b c).
    (* "destruct" is not smart enough to guess the right annotations
       for a match expression *)
    generalize (Nat.add_assoc d b c).
    generalize (Nat.add_assoc (S d) b c).
    simpl.
    generalize (d + b + c).
    intros.
    subst.
    Show Proof.
    Compute internal_eq_rew_dep.
    rewrite (Eqdep_dec.UIP_refl_nat (S (d + (b + c))) ltac:(assumption)).
    reflexivity.
Qed.

Print Assumptions lem_vapp_assoc.

(*************************************************************************************)
(* Transparent lemmas *)

Lemma lem_add_assoc : forall x y z, x + (y + z) = x + y + z.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - intros.
    simpl.
    rewrite IH.
    reflexivity.
Defined.

Program Definition stmt_vapp_assoc {A} :=
  forall a b c (va : vector A a) (vb : vector A b) (vc : vector A c),
    vapp (vapp va vb) vc = vapp va (vapp vb vc).
Next Obligation.
  apply lem_add_assoc.
Defined.

Lemma lem_vapp_assoc' {A} : @stmt_vapp_assoc A.
Proof.
  unfold stmt_vapp_assoc.
  intros a b c va vb vc.
  induction va as [|d x va IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IH.
    simpl.
    unfold eq_rect.
    unfold stmt_vapp_assoc_obligation_1.
    destruct (lem_add_assoc d b c).
    simpl.
    reflexivity.
Qed.

(*************************************************************************************)
(* John Major equality *)

Require Import Program.Equality. (* for "~=" *)

Print JMeq.

Lemma lem_eq_to_JMeq {A} : forall x y : A, x = y -> x ~= y.
Proof.
  intros x y H.
  rewrite H.
  reflexivity.
Qed.

Lemma jmeq_vcons {A n m} : n = m ->
  forall (v1 : vector A n) (v2 : vector A m),
    v1 ~= v2 -> forall x, vcons x v1 ~= vcons x v2.
Proof.
  intros e v1 v2 H x.
  Fail rewrite H.
  (* JMeq may be rewritten only when the types of both sides are the
     same *)
  Fail destruct H.
  Set Printing All.
  Fail rewrite e in H.
  Restart.
  (* we need to rewrite all occurrences at once so that everything
     still type-checks *)
  intro e.
  rewrite e.
  intros v1 v2 H x.
  rewrite H.
  reflexivity.
Qed.

Print Assumptions jmeq_vcons.

Lemma lem_vapp_nil_jmeq {A} :
  forall n (v : vector A n), vapp v vnil ~= v.
Proof.
  induction v as [|n x v IH].
  - simpl.
    reflexivity.
    Show Proof.
  - simpl.
    Fail rewrite IH.
    (* JMeq may be rewritten only when the types of both sides are the
       same *)
    apply jmeq_vcons; auto.
Qed.

Lemma lem_vapp_assoc_jmeq {A} :
  forall a b c (va : vector A a) (vb : vector A b) (vc : vector A c),
    vapp (vapp va vb) vc ~= vapp va (vapp vb vc).
Proof.
  intros a b c va vb vc.
  induction va as [|d x va IH].
  - simpl.
    reflexivity.
  - simpl.
    apply jmeq_vcons; trivial.
    lia.
Qed.

Print Assumptions lem_vapp_assoc_jmeq.

(*************************************************************************************)
(* Dependent equality *)

Require Import Eqdep. (* for eq_dep *)

Print eq_dep.

Arguments eq_dep {U} _ {p} _ {q}.

Lemma lem_vapp_nil_dep {A} :
  forall n (v : vector A n), eq_dep (vector A) (vapp v vnil) v.
Proof.
  induction v as [|n x v IH].
  - simpl.
    reflexivity.
    Show Proof.
  - simpl.
    rewrite IH.
    Show Proof.
    Compute internal_eq_dep_rew_r.
    reflexivity.
Qed.

Print Assumptions lem_vapp_nil_dep.

Lemma lem_vapp_assoc_dep {A} :
  forall a b c (va : vector A a) (vb : vector A b) (vc : vector A c),
    eq_dep (vector A) (vapp (vapp va vb) vc) (vapp va (vapp vb vc)).
Proof.
  intros a b c va vb vc.
  induction va as [|d x va IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Print Assumptions lem_vapp_assoc_dep.
