Goal forall n : nat, n * 1 = n.
intros.
elim n.
simpl.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.

