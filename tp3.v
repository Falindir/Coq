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


