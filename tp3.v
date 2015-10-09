Goal forall n : nat, n * 1 = n.
intros.
elim n.
simpl.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.

Fixpoint f (n : nat) : nat :=
match n with
| 0 => 1
| S p => (2 * (f p)) 
end.

Goal f(10) = 1024.
simpl.
reflexivity.

Open Scope list.
Require Import List.
Import ListNotations.

Lemma P1 : forall E : Type, forall l : (list E) , forall e : E, rev(l ++ [e]) = e :: rev l. 
intros.
elim l.
simpl.
reflexivity.
intros.
simpl.
rewrite H.
simpl.
reflexivity.

Save.


Lemma P2 : forall E : Type, forall l : (list E), rev( rev( l) ) = l.
intros.
elim l.
simpl.
reflexivity.
intros.
simpl.
rewrite (P1 E (rev l0) a).
rewrite H.
reflexivity.

Save.

Lemma my_eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
double induction n m.
left.
reflexivity.
intros.
right.
discriminate.
intros.
right.
discriminate.
intros.
elim (H0 n0).
left.
elim a.
reflexivity.
right.
congruence.

Save.

Lemma my_eq_nat_dec2  : forall n m : nat, {n = m} + {n <> m}.
intros.
decide equality.

Save.

Fixpoint function_equality (a b : nat) : bool := 
match a with 
| 0 => match b with
       | 0 =>  true
       | S p => false
       end
| S p1 => match b with 
          | 0 => false
          | S p2 => (function_equality p1 p2)
          end
end.


Eval compute in (function_equality 0 0).
Eval compute in (function_equality (S 0) 0).
Eval compute in (function_equality (S 0) (S 0)).

Inductive BinTree : Set :=
| Leaf : nat -> BinTree
| Node : nat -> BinTree -> BinTree -> BinTree.
.









