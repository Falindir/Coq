Parameters A B C : Prop.
Goal A -> B -> A.
intros.
assumption.
Save th1.

Goal (A -> B -> C ) -> (A -> B) -> A -> C.
intros.
apply H.
assumption.
apply H0.
assumption.
Save th2.

Goal A/\B -> B.
intro.
elim H.
intros.
assumption.

Goal B->A\/B.
intro.
right.
assumption.

Goal (A \/ B) -> (A -> C ) -> (B -> C ) -> C.
intros.
elim H.
assumption.
assumption.

Goal A -> False -> ~A.
intros.
intro.
assumption.

Goal False -> A.
intro.
elim H.

Goal (A <-> B) -> A -> B.
intros.
elim H.
intros.
apply (H1 H0).

Goal (A <-> B) -> B -> A.
intros.
elim H.
intros.
apply (H2 H0).

Goal (A -> B) -> (B -> A) -> (A <-> B).
intros.
split.
assumption.
assumption.


Parameters E : Set.
Parameters P : E -> Prop.
Goal (forall x : E, ~(P x)) -> ~(exists x : E, (P x)).
intros.
intro.
elim H0.
assumption.

Require Import Classical.

Goal ~(forall x : E, (P x)) -> (exists x : E, ~(P x)).
intros.
apply NNPP.
intro.
apply H.
intro.
apply NNPP.
intro.
apply H0.
exists x.
assumption.

Ltac hyp_false :=
 intros;
 match goal with
 | [ H : False |- ?e ] => elim H
 end.

Goal (C <-> (C \/ B)) -> A -> False -> B -> (A <-> (A \/ B)).
hyp_false.


Ltac my_intros := 
 match goal with
 | [ |- ?e1 -> ?e2] => intro; try my_intros
end.

Goal A -> B -> C -> B -> A.
my_intros.

Ltac my_assumption :=
 match goal with 
 | [ H : ?e |- ?e] => assumption
 end.

Goal A -> B -> C -> B -> A.
my_intros.
my_assumption.

Goal A -> B -> A.
tauto. (* un com *)

Ltac res_form_prop := 
 match goal with
 

 end.






