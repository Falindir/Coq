Open Scope type_scope.
Section Iso_axioms.
Variables A B C : Set.
Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.
End Iso_axioms.

Lemma isos_ex1 : forall A B:Set,
A * unit * B = B * (unit * A).
intros.
rewrite P_unit.
rewrite (Com unit A).
rewrite P_unit.
rewrite Com.
reflexivity.

Lemma isos_ex2 : forall A B C:Set,
(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).
intros.
rewrite (P_unit).
rewrite (P_unit).
rewrite AR_unit.
rewrite <-(Cur unit A B).
rewrite (Com unit A).
rewrite (P_unit).
rewrite (Com unit C).
rewrite (P_unit).
rewrite (Dis).
rewrite Com.
reflexivity.

 