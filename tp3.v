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

Save.


Eval compute in (function_equality 0 0).
Eval compute in (function_equality (S 0) 0).
Eval compute in (function_equality (S 0) (S 0)).

Inductive BinTree : Set :=
| Leaf : nat -> BinTree
| Node : nat -> BinTree -> BinTree -> BinTree.


Save.

Lemma my_eq_nat_Tree : forall n m : BinTree, {n = m} + {n <> m}.
induction n.
induction m.
elim (my_eq_nat_dec n n0).
left.
rewrite a.
reflexivity.
right.
congruence.
right.
discriminate.
induction m.
right.
discriminate.
elim (my_eq_nat_dec n1 n).
intros.
rewrite a.
elim (IHn1 m1).
intros.
rewrite a0.
elim (IHn2 m2).
intros.
rewrite a1.
left.
reflexivity.
intros.
right.
congruence.
right.
congruence.
right.
congruence.

Save.

Lemma my_eq_nat_Tree2 : forall n m : BinTree, {n = m} + {n <> m}.
intros.
decide equality.
elim (my_eq_nat_dec2 n0 n1).
left.
rewrite a.
reflexivity.
right.
congruence.
elim (my_eq_nat_dec2 n0 n1).
left.
rewrite a.
reflexivity.
right.
congruence.

Inductive is_even : nat -> Prop :=
| is_even_0 : is_even 0
| is_even_S : forall n : nat, is_even n -> is_even (S (S n)).

Fixpoint is_even_tac (n : nat) : bool := 
match n with 
| 0 => true
| 1 => false
| S (S p) => (is_even_tac p)
end. 

Ltac is_event_tac :=
repeat apply is_even_S;
apply is_even_0.


Eval compute in (is_even_tac (S (S 0))).
Eval compute in (is_even_tac (S (S (S 0)))).

Open Scope nat_scope.
Check (S (S 0)).

Save.

Lemma test_even : (is_even (S(S(S(S 0))))).
is_event_tac.

Save.

Goal ~(is_even 7).
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
inversion_clear H0.

Ltac is_event_tac_tild := 
intro;
repeat (match goal with 
| H : is_even ?e |- _ => inversion_clear H
end).



Goal ~(is_even 9).
is_event_tac_tild.

 






