Module Playground1.


Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
End Playground1.

Definition minustwo (n : nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).


Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.

Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.


Module Playground2.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S O => m
    | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => mult n n'
  end. 
End Playground2.

Eval simpl in (Playground2.plus (S (S O)) (S (S (S O)))).

Eval simpl in (Playground2.mult (S (S O)) (S (S (S O)))).

Eval simpl in (Playground2.factorial (S (S (S (S O))))).
