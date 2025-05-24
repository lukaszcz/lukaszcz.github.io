(* Tutorial 20: Equations package *)

Inductive vector (A : Type) : nat -> Type :=
  vnil : vector A 0 | vcons : forall (n : nat), A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A n}.

Notation "[: :]" := vnil.
Notation "[: x :]" := (vcons x vnil).
Notation "[: x ; y ; .. ; z :]" := (vcons x (vcons y .. (vcons z vnil) ..)).

From Equations Require Import Equations.

Derive Signature for vector.

Equations vapp {A n m} (v1 : vector A n) (v2 : vector A m) : vector A (n + m) :=
  vapp vnil v := v;
  vapp (vcons x v1) v2 := vcons x (vapp v1 v2).

Equations vzip {A B C n} (f : A -> B -> C) : vector A n -> vector B n -> vector C n :=
  vzip f vnil vnil := vnil;
  vzip f (vcons x v1) (vcons y v2) := vcons (f x y) (vzip f v1 v2).

Compute (vzip (fun x y => x + y) [: 1; 2; 3 :] [: 4; 3; 2 :]).

Require Import Program.

Program Fixpoint vzip' {A B C n} (f : A -> B -> C)
         (v1 : vector A n) (v2 : vector B n) : vector C n :=
  match v1 with
  | vnil => vnil
  | vcons x v1' =>
    match v2 with
    | vnil => _
    | vcons y v2' => vcons (f x y) (vzip' f v1' v2')
    end
  end.

Compute (vzip' (fun x y => x + y) [: 1; 2; 3 :] [: 4; 3; 2 :]).
