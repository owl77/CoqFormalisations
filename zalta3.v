(* Modal Object Logic for possible worlds and monads *)


Axiom object: Set.

Axiom world : Set.

Axiom this : world.

Fixpoint nrelation ( n : nat) := match n with
| 0 => Prop
| S n => object -> (nrelation n)
end.

Axiom coer : Prop -> nrelation 0.
Axiom coer_ax : forall (p : Prop), p = (coer p).


Fixpoint nrelation_mod ( n : nat) := match n with
| 0 => world -> Prop
| S n => object -> (nrelation_mod n)
end.


Axiom modalize : forall (n : nat) ( F : nrelation n), nrelation_mod n.


Require Import Nat.

Definition property := nrelation 1.

Definition property_mod := nrelation_mod 1.


Fixpoint necc ( n : nat) : (nrelation_mod n) -> nrelation_mod n := match n with
| 0 => fun ( F : nrelation_mod 0) => fun (x : world) => forall (w : world), F w
|S n => fun ( F : nrelation_mod (S n)) => fun (x : object) => (necc n) (F x)
end.


Fixpoint apply_mod ( n : nat) : ( nrelation_mod 0 -> nrelation_mod 0) -> (nrelation_mod n) -> nrelation_mod n := match n with
| 0 => fun (f : nrelation_mod 0 -> nrelation_mod 0) => fun ( F : nrelation_mod 0) => f F
|S n => fun ( f : nrelation_mod 0 -> nrelation_mod 0) => fun (F : nrelation_mod (S n)) =>
 fun ( x : object ) => apply_mod n f (F x)  
end.


Fixpoint demodalize (n : nat) : (nrelation_mod n) -> nrelation n := match n with
| 0 => fun ( F : nrelation_mod 0) =>  coer(F this)
| S n => fun ( F : nrelation_mod (S n)) =>  fun ( x : object) => demodalize n (F x)
end.

Definition poss_0 : nrelation_mod 0 -> nrelation_mod 0 :=
fun (F : nrelation_mod 0) => fun (w : world) => exists (v : world), F v.

Definition poss (n : nat) := apply_mod n poss_0.

Definition not_mod := apply_mod 0
 (fun (F : nrelation_mod 0) => fun (w : world) =>  not (F w) ).


Axiom encodes : forall (o : object) (p : property), Prop.

Axiom encodes_mod : forall (o :object) (F : property_mod), Prop.

Definition D3_Eq ( F G : property_mod) := forall (x : object), encodes_mod x F <-> encodes_mod x G.


Definition Const ( F: property_mod) ( P : nrelation_mod 0) := D3_Eq F (fun (x : object) => P).

Definition Vac (F : property_mod) := exists (P : nrelation_mod 0), Const F P.

Definition encodes_mod_0 ( x : object) ( P : nrelation_mod 0):= encodes_mod x (fun (x : object) => P).

Definition Maximal (z : object) := forall ( P : nrelation_mod 0), 
encodes_mod_0 z P \/ encodes_mod_0 z(not_mod P).

Definition





