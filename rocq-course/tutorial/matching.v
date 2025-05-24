(* Tutorial 16: Dependent pattern matching, the Program command and well-founded recursion *)

(************************************************************************************)
(* Balanced binary trees *)

Inductive htree A : nat -> Type :=
| hleaf : A -> htree A 0
| hnode : forall n, A -> htree A n -> htree A n -> htree A (S n).

Arguments hleaf {A}.
Arguments hnode {A n}.

Inductive Dummy : Type := dummy.

Definition hleft {A} {n} (t : htree A (S n)) : htree A n :=
  match t in htree _ m
        return match m with
               | 0 => Dummy
               | S k => htree A k
               end
  with
  | hleaf _ => dummy (* : Dummy *)
  | @hnode _ k _ l _ => l (* : htree A k *)
  end. (* match .. end : htree A n *)

Compute (hleft (hnode 3 (hleaf 1) (hleaf 2))).
Fail Compute (hleft (hleaf 3)).

Definition hleft' {A} {n} (t : htree A (S n)) : htree A n :=
  match t with
  | hnode _ l _ => l
  end.

Print hleft'.

Check idProp.

(************************************************************************************)
(* Vectors reloaded *)

Inductive vector (A : Type) : nat -> Type :=
  vnil : vector A 0 | vcons : forall (n : nat), A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A n}.

Notation "[: :]" := vnil.
Notation "[: x :]" := (vcons x vnil).
Notation "[: x ; y ; .. ; z :]" := (vcons x (vcons y .. (vcons z vnil) ..)).

Compute [: 1; 2; 3 :].
Compute [::].

Fixpoint vapp {A n m} (v1 : vector A n) (v2 : vector A m) : vector A (n + m) :=
  match v1 with
  | vnil => v2
  | vcons x v1' => vcons x (vapp v1' v2)
  end.

Print vapp.

(*
vapp =
fix vapp (A : Type) (n m : nat) (v1 : vector A n) (v2 : vector A m) {struct v1} :
vector A (n + m) :=
  match v1 in (vector _ n') return (vector A (n' + m)) with
  | vnil => v2 (* : vector A (0 + m) which is definitionally equal to "vector A m" *)
  | @vcons _ k x v1' => vcons x (vapp A k m v1' v2) (* : vector A (S k + m) *)
       (* vcons x (vapp A k m v1' v2) : vector A (S (k + m)) *)
       (* But (S (k + m)) and (S k + m) are definitionally equal,
          so everything works out *)
  end (* match .. end : vector A (n + m) *)
     : forall (A : Type) (n m : nat), vector A n -> vector A m -> vector A (n + m)
*)

Compute (vapp [: 1; 2 :] [: 1 :]).

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v in vector _ k return vector A (k + m) with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.

Print eq_rect.

Definition vcast {A} n m (p : n = m) (v : vector A n) : vector A m :=
  eq_rect n (fun k => vector A k) v m p.

Require Import Psatz. (* for "lia" and some lemmas about natural numbers *)

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v in vector _ k return vector A (k + m) with
    | vnil => acc
    | @vcons _ k' x v' =>
      vcast (k' + S m) (S k' + m) ltac:(lia) (vrev v' (vcons x acc))
    end
  in
  vrev v vnil.

Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v in vector _ k return vector A (k + m) with
    | vnil => acc
    | @vcons _ k' x v' => vcast (k' + S m) (S k' + m) ltac:(lia) (vrev v' (vcons x acc))
    end
  in
  vcast (n + 0) n ltac:(auto) (vrev v vnil).

Compute (vrev [: 1; 2 :]). (* oops! *)

(* The reason for a blocked computation are opaque constants
   (lemma definitions) which are never unfolded by the computation
   mechanism. "Qed" defines a constant as opaque, "Defined" as
   transparent. Most lemmas in the standard library are opaque, even
   if proven constructively. *)

(* However, this is not a "logical" but an (intended) "implementation"
   limitation. Extraction still works. *)

Require Import Extraction.
Extraction Language Haskell.

Recursive Extraction vrev.

Extraction Inline vcast.
Extraction Inline eq_rect.

Recursive Extraction vrev.

Require Import Program.

Program Definition vrev' {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.

Print vrev'.
Print vrev'_obligation_1.
Print vrev'_obligation_2.

(* The "Program" command does not help with the opaqueness of
   definitions. *)
Compute (vrev' [: 1; 2 :]). (* oops! *)

Recursive Extraction vrev'.

(* To make the proofs compute we need to re-prove the opaque lemmas we
   used, redefining them as transparent. *)

Lemma lem_plus_n_0 : forall n, n + 0 = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Defined. (* transparent *)

Lemma lem_plus_n_Sm : forall n m, n + S m = S n + m.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - intro m.
    simpl.
    rewrite IH.
    reflexivity.
Defined. (* transparent *)

Obligation Tactic := idtac.

Program Definition vrev'' {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.
Next Obligation.
  auto using lem_plus_n_Sm.
Defined.
Next Obligation.
  auto using lem_plus_n_0.
Defined.

Obligation Tactic := program_simpl.

Compute (vrev'' [: 1; 2 :]).

(* This is annoying for larger developments! *)

(* We can:
1) give up on computation of the function inside Coq (extraction still
   works)
2) use an alternative proof-relevant library of lemmas
*)

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v with
  | vnil => (vnil, vnil)
  | vcons x (vcons y v') =>
    let (v1, v2) := vsplit v' in
    (vcons x v1, vcons y v2)
  end.

Require Import Nat. (* for div2 *)

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return vector A (div2 m) * vector A (div2 m) with
  | vnil => (vnil, vnil)
  | vcons x (vcons y v') =>
    let (v1, v2) := vsplit v' in
    (vcons x v1, vcons y v2)
  end.

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return vector A (div2 m) * vector A (div2 m) with
  | vnil => (vnil, vnil)
  | @vcons _ k _ vnil => (vnil, vnil)
  | vcons x (vcons y v') =>
    let (v1, v2) := vsplit v' in
    (vcons x v1, vcons y v2)
  end.

Print eq_refl.

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return m = 2 * n -> vector A (div2 m) * vector A (div2 m) with
  | vnil => fun _ => (vnil, vnil)
  | @vcons _ k x v' =>
    fun p1 : S k = 2 * n =>
      match v' in vector _ m' return vector A (div2 (S m')) * vector A (div2 (S m')) with
      | vnil => (vnil, vnil)
      | @vcons _ k' y v'' =>
        let (v1, v2) := vsplit v'' in
        (vcons x v1, vcons y v2)
      end
  end eq_refl.

(*
2 * n = 2 * n -> vector A (div2 (2 * n)) * vector A (div2 (2 * n))
*)

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return m = 2 * n -> vector A (div2 m) * vector A (div2 m) with
  | vnil => fun _ => (vnil, vnil)
  | @vcons _ k x v' =>
    fun p1 : S k = 2 * n =>
      match v' in vector _ m'
            return m' = k -> vector A (div2 (S m')) * vector A (div2 (S m'))
      with
      | vnil => fun _ => (vnil, vnil)
      | @vcons _ k' y v'' =>
        fun p2 : S k' = k =>
          let (v1, v2) := vsplit v'' in
          (vcons x v1, vcons y v2)
      end eq_refl
  end eq_refl.

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return m = 2 * n -> vector A (div2 m) * vector A (div2 m) with
  | vnil => fun _ => (vnil, vnil)
  | @vcons _ k x v' =>
    fun p1 : S k = 2 * n =>
      match v' in vector _ m'
            return m' = k -> vector A (div2 (S m')) * vector A (div2 (S m'))
      with
      | vnil => fun _ => (vnil, vnil)
      | @vcons _ k' y v'' =>
        fun p2 : S k' = k =>
          let (v1, v2) := vsplit (vcast k' (2 * (n - 1)) ltac:(lia) v'') in
          (vcons x v1, vcons y v2)
      end eq_refl
  end eq_refl.

Lemma lem_div2 : forall k n, S (S k) = 2 * n -> S (n - 1) = div2 (S (S k)).
Proof.
  intros k n H.
  assert (k = 2 * (n - 1)) by lia.
  simpl.
  subst.
  SearchRewrite (div2 (2 * _)).
  rewrite PeanoNat.Nat.div2_double.
  reflexivity.
Qed.

Fail Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return m = 2 * n -> vector A (div2 m) * vector A (div2 m) with
  | vnil => fun _ => (vnil, vnil)
  | @vcons _ k x v' =>
    fun p1 : S k = 2 * n =>
      match v' in vector _ m'
            return m' = k -> vector A (div2 (S m')) * vector A (div2 (S m'))
      with
      | vnil => fun _ => (vnil, vnil)
      | @vcons _ k' y v'' =>
        fun p2 : S k' = k =>
          let (v1, v2) := vsplit (vcast k' (2 * (n - 1)) ltac:(lia) v'') in
          (vcast (S (n - 1)) (div2 (S (S k')))
                 ltac:(subst; auto using lem_div2) (vcons x v1),
           vcast (S (n - 1)) (div2 (S (S k')))
                 ltac:(subst; auto using lem_div2) (vcons y v2))
      end eq_refl
  end eq_refl.

Fixpoint vsplit {A} {n} (v : vector A (2 * n)) : vector A n * vector A n.
refine (
  let (v1, v2) :=
      match v in vector _ m return m = 2 * n -> vector A (div2 m) * vector A (div2 m) with
      | vnil => fun _ => (vnil, vnil)
      | @vcons _ k x v' =>
        fun p1 : S k = 2 * n =>
          match v' in vector _ m'
                return m' = k -> vector A (div2 (S m')) * vector A (div2 (S m'))
          with
          | vnil => fun _ => (vnil, vnil)
          | @vcons _ k' y v'' =>
            fun p2 : S k' = k =>
              let (v1, v2) := vsplit _ _ (vcast k' (2 * (n - 1)) _ v'') in
              (vcast (S (n - 1)) (div2 (S (S k'))) _ (vcons x v1),
               vcast (S (n - 1)) (div2 (S (S k'))) _ (vcons y v2))
          end eq_refl
      end eq_refl
  in
  (vcast (div2 (2 * n)) n _ v1,
   vcast (div2 (2 * n)) n _ v2)  ).
Proof.
  - lia.
  - subst; auto using lem_div2.
  - subst; auto using lem_div2.
  - rewrite PeanoNat.Nat.div2_double; reflexivity.
  - rewrite PeanoNat.Nat.div2_double; reflexivity.
Defined.

Fail Compute vsplit [: 1; 2; 3; 4 :].
Compute vsplit (vcast 4 (2 * 2) eq_refl [: 1; 2; 3; 4 :]). (* oops! *)

Fail Program Fixpoint vsplit' {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v with
  | vnil => (vnil, vnil)
  | vcons _ vnil => (vnil, vnil)
  | vcons x (vcons y v') =>
    let (v1, v2) := vsplit v' in
    (vcons x v1, vcons y v2)
  end.

(*
Program Fixpoint vsplit' {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return vector A (div2 m) * vector A (div2 m) with
  | vnil => (vnil, vnil)
  | @vcons _ k x v' =>
      match v' with
      | vnil => (vnil, vnil)
      | vcons y v'' =>
        let (v1, v2) := vsplit v'' in
        (vcons x v1, vcons y v2)
      end
  end.
Obligations.
*)

(*
Program Fixpoint vsplit' {A} {n} (v : vector A (2 * n)) : vector A n * vector A n :=
  match v in vector _ m return m = 2 * n -> vector A (div2 m) * vector A (div2 m) with
  | vnil => fun _ => (vnil, vnil)
  | @vcons _ k x v' =>
    fun p =>
      match v' with
      | vnil => (vnil, vnil)
      | vcons y v'' =>
        let (v1, v2) := vsplit' v'' in
        (vcons x v1, vcons y v2)
      end
  end eq_refl.
Obligations.
(*
Next Obligation.
*)
Show Obligation Tactic.
Obligation Tactic := idtac.
Next Obligation.
  intros A n _ k _ v' H1 k' y v'' H2 _.
  fold div2.
  assert (k' = 2 * (n - 1)) by lia.
  subst.
  rewrite Div2.div2_double.
  reflexivity.
Defined.
Obligations.
Solve Obligations with (intros; rewrite Div2.div2_double; reflexivity).

Extraction vsplit'. *)

Obligation Tactic := program_simpl.

Fail Definition vsplitS {A} {n} (v : vector A (S (2 * n))) : (vector A (S n) * vector A n) :=
  match v with
  | vcons x v' =>
    let (v1, v2) := vsplit v'
    in
    (vcons x v1, v2)
  end.

Program Definition vsplitS {A} {n} (v : vector A (S (2 * n))) :
  (vector A (S n) * vector A n) :=
  match v with
  | vnil => _
  | vcons x v' =>
    let (v1, v2) := vsplit v' in
    (vcons x v1, v2)
  end.
(*
Obligation Tactic := idtac.

Program Definition vsplitS {A} {n} (v : vector A (S (2 * n))) :
  (vector A (S n) * vector A n) :=
  match v with
  | vnil => _
  | vcons x v' =>
    let (v1, v2) := vsplit v' in
    (vcons x v1, v2)
  end.
*)

(*******************************************************************************)
(* Well-founded recursion *)

Print well_founded.
Print Acc.
(* "Acc R x0" means that there is no infinite sequence x0 x1 x2 ... with
    R xi+1 xi for each i *)

(*
Fixpoint div_wf n m (p : m <> 0) (wf : Acc lt n) {struct wf} : nat.
  refine (if n <? m then
            0
          else
            S (div_wf (n - m) m p _)).
  inversion wf as [H].
  apply H.
  lia.
Defined.
*)

Require Import Arith. (* for lt_dec *)

Check lt_dec.
Locate "+".
Print sumbool.

Fixpoint div_wf n m (p : m <> 0) (wf : Acc lt n) {struct wf} : nat.
  refine (match lt_dec n m with
          | left _ => 0
          | right Hneq =>
            S (div_wf (n - m) m p _)
          end).
  inversion wf as [H].
  apply H.
  lia.
Defined.
(* Actually, the "if then else" syntactic sugar works for any
   inductive type with two constructors, not only for bool. So we
   could write:

   if lt_dec n m then 0 else S (div_wf (n - m) m p _)
 *)

Print Acc.

Fixpoint div_wf' n m (p : m <> 0) (wf : Acc lt n) {struct wf} : nat :=
  match lt_dec n m with
  | left _ => 0
  | right Hneq =>
    S (div_wf (n - m) m p
        (match wf with Acc_intro _ H => H (n - m) ltac:(lia) end))
  end.

Fixpoint div_wf'' n m (p : m <> 0) (wf : Acc lt n) {struct wf} : nat :=
  match lt_dec n m with
  | left _ => 0
  | right Hneq =>
    match wf with
    | Acc_intro _ H =>
      S (div_wf (n - m) m p (H (n - m) ltac:(lia)))
    end
  end.

Lemma lem_wf_lt : forall x, Acc lt x.
Proof.
  induction x as [|x IH].
  - constructor.
    lia.
  - constructor.
    inversion IH.
    auto with arith.
Defined.

Definition div n m (p : m <> 0) : nat := div_wf n m p (lem_wf_lt n).

Compute (div 10 2 ltac:(discriminate)).
Compute (div 1 2 ltac:(discriminate)).
Compute (div 11 2 ltac:(discriminate)).
Compute (div 11 5 ltac:(discriminate)).

Obligation Tactic := program_simpl.

Program Fixpoint div' n m (p : m <> 0) {measure n} :=
  if lt_dec n m then
    0
  else
    S (div' (n - m) m p).
Solve Obligations with lia.

Compute (div' 10 2 ltac:(discriminate)).
Compute (div' 1 2 ltac:(discriminate)).
Compute (div' 11 2 ltac:(discriminate)).
Compute (div' 11 5 ltac:(discriminate)).
