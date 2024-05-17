Axiom individual : Set.
Axiom world : Set.
Axiom this : world.
Definition modal := world -> Prop.


Inductive OSig :=
| i : OSig
| p : OSig
| prop : OSig -> OSig
| arg : OSig -> OSig -> OSig.



Fixpoint OTyp ( X : OSig):Type := match X with
| i => individual
| p => world -> Prop
| prop A => (OTyp A) -> world -> Prop
| arg A B => (OTyp A) -> ((OTyp B) -> (world -> Prop))
end.


Fixpoint oTyp ( X : OSig):Type := match X with
| i => individual
| p =>  Prop
| prop A => (OTyp A) ->Prop
| arg A B => (OTyp A) -> ((OTyp B) -> Prop)
end.



(* example *)

Compute OTyp (arg (arg p i) i).

Axiom Concrete : forall ( X: OSig), OTyp  (prop X).

Compute Concrete i.

Definition Sq ( f : OTyp p) : (OTyp p):= fun ( x: world) => forall (y: world), f y.

Definition Poss ( f : OTyp p) : (OTyp p):= fun ( x: world) => exists (y: world), f y.




Definition necc (X : OSig) := match X with
|i => fun (T : OTyp i) => T
|p => fun ( T: OTyp p) => Sq T
|prop a => fun (T : OTyp _) => fun (x : OTyp a) =>  Sq (T x)
|arg a b => fun ( T: OTyp (arg a b)) => fun ( x : OTyp a) =>  fun ( y : OTyp b) =>
Sq ((T x) y)
end.


Definition poss (X : OSig) := match X with
|i => fun (T : OTyp i) => T
|p => fun ( T: OTyp p) => Poss T
|prop a => fun (T : OTyp _) => fun (x : OTyp a) => Poss (T x)
|arg a b => fun ( T: OTyp (arg a b)) => fun ( x : OTyp a) =>  fun ( y : OTyp b) =>
Poss ((T x) y)
end.

Definition inj ( x : OTyp i) : (oTyp i) := x.


Definition actual (X : OSig) : (OTyp X) -> (oTyp X):= match X with
|i => fun (T : OTyp i) =>  inj T
|p =>  fun (T :OTyp p) => T this
|prop a =>  fun ( T : OTyp (prop a)) =>  fun (x : OTyp a) => (T x) this
|arg a b => fun ( T : OTyp (arg a b)) => fun (x : OTyp a) => fun (y : OTyp b) => (T x y) this
end.

Check actual.


