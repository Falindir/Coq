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

Abort All.

Ltac axiom E := 
 repeat match E with
 | unit * ?e => rewrite (Com unit e)
 | ?e * unit => rewrite (P_unit e)
 | ?e -> unit => rewrite (AR_unit e)
 | unit -> ?e => rewrite (AL_unit e)
 | ?e * (?f * ?g) => rewrite (Ass e)
 | ?e * ?f -> ?g => rewrite (Cur e)
 | ?e -> ?f * ?g => rewrite (Dis e)

end.

Ltac AB := 
 match goal with
 | |- ?e = ?e => reflexivity
 | |- ?e = ?f => try (axiom e); try (axiom f)
end.

Section Peano.
Parameter N : Set.
Parameter o : N.
Parameter s : N -> N.
Parameters plus mult : N -> N -> N.
Variables x y : N.
Axiom ax1 : ~((s x) = o).
Axiom ax2 : exists z, ~(x = o) -> (s z) = x.
Axiom ax3 : (s x) = (s y) -> x = y.
Axiom ax4 : (plus x o) = x.
Axiom ax5 : (plus x (s y)) = s (plus x y).
Axiom ax6 : (mult x o) = o.
Axiom ax7 : (mult x (s y)) = (plus (mult x y) x).
End Peano.

Lemma PP : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
intros.
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.


Lemma PX : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
intros.
rewrite ax7.
rewrite ax7.
rewrite ax6.
rewrite ax5.
rewrite ax5.
rewrite ax5.
rewrite ax5.
rewrite ax4.
rewrite ax4.
reflexivity.

Abort All.

Ltac tPeano := (rewrite ax4) || (rewrite ax5) || (rewrite ax6) || (rewrite ax7)
.

Hint Rewrite ax4 ax5 ax6 ax7 : base0.

Lemma PX : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
intros.
autorewrite with base0; try reflexivity.

Abort All.

Section Anneau.
Parameter W : Type.
Parameter ZE : W.
Parameter UN : W.
Parameters PL MO MU : W -> W -> W.
Parameter INV : W -> W.
Variables x y z : W.
Axiom axB1 : (PL x (PL y z)) = (PL (PL x y) z).
Axiom axB2 : (PL x y) = (PL y x).
Axiom axB3 : (MO x (MO y z)) = (MO (MO x y) z).
Axiom axB4 : (MO x (PL y z)) = (PL (MO x y ) (MO x z)).
Axiom axB5 : (MO (PL x y) z) = (PL (MO x z) (MO y z)).
Axiom axB6 : (PL x ZE) = x.
Axiom axB7 : (PL ZE x) = x.
Axiom axB8 : (PL x (INV x)) = ZE.
Axiom axB9 : (PL (INV x) x) = ZE.
Axiom axB10 : (MO x UN) = x.
Axiom axB11 : (MO UN x) = x.
Axiom axB12 : (MO x y) = (MO y x).
Axiom axB13 : (MU x y) = (PL x (INV y)). 

End Anneau.



Require Import Ring_base.

Print ring_theory.

Check mk_rt.

Definition my_ring := 
mk_rt ZE UN PL MO MU INV eq axB7 axB2 axB1 axB11 axB12 axB3 axB5 axB13 axB8.

Add Ring toto : my_ring.
Lemma ID4 : forall A B C:W, (MO (PL A B) (PL A B) ) = (PL (PL (MO A A) (PL (MO A B) (MO A B) ) ) (MO B B )).
intros.


ring.
