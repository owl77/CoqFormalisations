Axiom individuals : Set.
Axiom no_empty : forall ( P : individuals -> Prop), exists (i : individuals), P i.

Theorem syll : forall (S P Q : individuals -> Prop), 
(forall (x: individuals), S x -> P x) /\ (forall ( x: individuals),
S x -> Q x ) -> exists (y : individuals),  P y /\ Q y.

Proof.
intros.
destruct H.
pose proof (no_empty S).
elim H1.
intros.
pose proof H x.
pose proof H0 x.
pose proof H3 H2.
pose proof H4 H2.
exists x.
split.
assumption.
assumption.
Qed.














