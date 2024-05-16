Axiom individual : Set.
Axiom world : Set.
Definition modal : world -> Prop.



Inductive OSig :=
| i : OSig
| p : OSig
| arg : OSig -> OSig -> OSig.

Fixpoint O_unf ( X : OSig) := match X with
| i => i
| p => p
| arg A B => arg (O_unf A) (arg (O_unf B) p)
end.

Fixpoint OTyp ( X : OSig):Type := match X with
| i => individual
| p => world -> Prop
| arg A B => (OTyp A) -> (OTyp B)
end.

Definition o_t ( X : OSig ) :=  OTyp (O_unf X).

Compute o_t (arg (arg p i) i).



