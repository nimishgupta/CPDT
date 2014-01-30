(* *)
Require Import Arith.
Require Import Omega.
Set Implicit Arguments.

(*
Section BinTree.

Variable A : Set.

Inductive bintree (A : Set) : Set :=
  | Leaf : bintree A
  | Node : bintree A -> nat -> A -> bintree A -> bintree A.
*)



(* Dependent types, a type holds a theorem -> Curry Howard Isomorphism *)
Inductive order (x y : nat) : Set :=
  | LT : x < y -> order x y
  | EQ : x = y -> order x y
  | GT : x > y -> order x y.

Lemma order_correct :
  forall m n,
    order m n -> order (S m) (S n).

  intros.
  destruct H.
  apply LT. omega.
  apply EQ. omega.
  apply GT. omega.
Qed.


Fixpoint  compare (m n : nat) : order m n :=
  match m, n with
    | 0, 0 => EQ eq_refl
    | S m', S n' => order_correct (compare m' n')
    | S _, 0 => GT (gt_Sn_O _)
    | 0, S _ => LT (lt_0_Sn _)
  end.


