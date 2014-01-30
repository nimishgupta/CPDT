Require Import Arith Bool List.
Set Implicit Arguments.

(* Our language of types *)
Inductive type: Set := Nat | Bool.


(* Set of binary operators *)
(* Here tbinop is an indexed family type 
 *)
Inductive tbinop: type -> type -> type -> Set :=
  | TPlus: tbinop Nat Nat Nat
  | TTimes: tbinop Nat Nat Nat
  (* Polymorphism, we want to allow equality comparison of two values
   * that have the same type
   *)
  | TEq: forall t, tbinop t t Bool
  | TLt: tbinop Nat Nat Bool.


(* typed expression *)
Inductive texp: type -> Set :=
  | TNConst: nat -> texp Nat
  | TBConst: bool -> texp Bool
  | TBinop: forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

(* Semantics for types *)
Definition typeDenote (t: type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

Print lt.
Print gt.
Print eqb.
Print leb.
Print plus.



Fixpoint my_lt (m n: nat) : bool :=
  match m, n with
    | O, O => true
    | O, _ => false
    | _, O => false
    | S m', S n' => my_lt m' n'
  end.


(* XXX: Why it has been written like this??
 *
 * Since tbinop is an indexed type, its indices become
 * additional arguments to tbinopDenote.
 *
 * We need to do a genuine dependent pattern match,
 * where the necessary type of each case body depends
 * on the the value that has been matched.
 *)
Definition tbinopDenote arg1 arg2 res (b: tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b in tbinop arg1 arg2 res 
    return typeDenote arg1 -> typeDenote arg2 -> typeDenote res with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => my_lt
  end.


(* Semantics for exp evaluation *)
Fixpoint texpDenote t (e: texp t): typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TNConst 42).
Eval simpl in texpDenote (TBConst true).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).



Definition tstack := list type.


(* Define instruction classified by tstack must have exactly as many elements, and each stack
 * element must have the type found in the same position of the stack type
 *)
(* Instructions in terms of stack types, where every instruction's type tells us what initial
 * stack type it expects and what final stack type it will produce.
 *)
Inductive tinstr: tstack -> tstack -> Set :=
  | TiNConst : forall s, nat -> tinstr s (Nat :: s)
  | TiBConst : forall s, bool  -> tinstr s (Bool :: s)
  | TiBinop : forall arg1 arg2 res s,
      tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog: tstack -> tstack -> Set :=
  | TNil : forall s, tprog s s
  | TCons : forall s1 s2 s3,
      tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.

Fixpoint vstack (ts: tstack): Set := 
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.



Definition tinstrDenote ts ts' (i: tinstr ts ts'): vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ _ _ _ b => 
       fun s => 
         let '(arg1, (arg2, s')) := s in ((tbinopDenote b) arg1 arg2, s')
  end.


Fixpoint tprogDenote ts ts' (p: tprog ts ts'): vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s 
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

Fixpoint tconcat ts ts' ts'' (p: tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e: texp t) (ts: tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
         (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.
Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.



