(* Modal Object Logic for possible worlds and Leibnizian monads. Abstract Objects Chs.III and IV*)


Axiom object: Set.

Axiom world : Set.

Axiom this : world.

Fixpoint nrelation ( n : nat) : Type := match n with
| 0 => Prop
| S n => object -> (nrelation n)
end.

Axiom coer : Prop -> nrelation 0.
Axiom coer_ax : forall (p : Prop), p = (coer p).


Fixpoint nrelation_mod ( n : nat)  := match n with
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

Fixpoint apply2_mod ( n : nat) : ( nrelation_mod 0 -> nrelation_mod 0 -> nrelation_mod 0) 
-> (nrelation_mod n) ->  (nrelation_mod n) -> nrelation_mod n  := match n with
| 0 => fun (f : nrelation_mod 0 -> nrelation_mod 0 -> nrelation_mod 0) => 
fun ( F : nrelation_mod 0) (G : nrelation_mod 0) => f F G
|S n => fun ( f : nrelation_mod 0 -> nrelation_mod 0 -> nrelation_mod 0) => 
fun (F : nrelation_mod (S n)) (G : nrelation_mod (S n)) =>
 fun ( x : object ) => apply2_mod n f (F x) (G x)  
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

Definition imp_mod (n : nat) ( F G : nrelation_mod n) :=
apply2_mod n (fun ( p q : nrelation_mod 0) => fun (w : world) => p w -> q w) F G.

Definition and_mod (n : nat) ( F G : nrelation_mod n) :=
apply2_mod n (fun ( p q : nrelation_mod 0) => fun (w : world) => p w /\ q w) F G.

Definition or_mod (n : nat) ( F G : nrelation_mod n) :=
apply2_mod n (fun ( p q : nrelation_mod 0) => fun (w : world) => p w \/ q w) F G.


Definition equiv_mod (n : nat) ( F G : nrelation_mod n)  :=
apply2_mod n (fun ( p q : nrelation_mod 0) => fun (w : world) => p w <-> q w) F G.

Definition forall_obj_mod ( f : object -> nrelation_mod 0) :=
fun (w : world) =>  forall ( x: object),  f x w.
Definition forall_pro_mod ( f : property_mod -> nrelation_mod 0) :=
fun (w : world) =>  forall ( x: property_mod),  f x w.
Definition forall_prop_mod ( f : nrelation_mod 0 -> nrelation_mod 0) :=
fun (w : world) =>  forall ( x: nrelation_mod 0),  f x w.






Axiom encodes : forall (o : object) (p : property), nrelation_mod 0.

Axiom encodes_mod : forall (o :object) (F : property_mod), nrelation_mod 0.



Definition D3_Eq ( F G : property_mod) := fun (w : world) => forall (x : object) (w : world), (equiv_mod 0 (encodes_mod x F) (encodes_mod x G)) w.


Definition Const ( F: property_mod) ( P : nrelation_mod 0) := D3_Eq F (fun (x : object) => P).

Definition Vac (F : property_mod) :=  fun (w : world) => exists (P : nrelation_mod 0), (Const F P) w.

Definition encodes_mod_0 ( x : object) ( P : nrelation_mod 0):= encodes_mod x (fun (x : object) => P).

Definition Maximal (z : object) := fun (w : world) => forall ( P : nrelation_mod 0), (or_mod 0
(encodes_mod_0 z P)  (encodes_mod_0 z(not_mod P))) w.

Require Import Coq.Logic.Classical.

Definition World1 (z : object) := forall_pro_mod (fun ( F: property_mod) => 
imp_mod 0 (encodes_mod z F) (Vac F)).

Definition World2 ( z : object) := poss 0 (forall_prop_mod 
( fun ( F: nrelation_mod 0) => equiv_mod 0 (encodes_mod_0 z F) F 

) ).

Definition World (z : object) := and_mod 0 (World1 z) (World2 z).

Axiom LA10 : forall ( z : object) (F : nrelation_mod 0) (w : world),
encodes_mod_0 z F w -> forall (v : world), encodes_mod_0 z F v.


Theorem leib1 : (forall_obj_mod ( fun ( z: object) => imp_mod 0 (World z) (Maximal z))) this.

Proof.
intro. unfold imp_mod. unfold apply2_mod. unfold World. unfold and_mod. unfold apply2_mod.
unfold World1. unfold World2. unfold forall_pro_mod. unfold forall_prop_mod. unfold poss.
unfold apply_mod. unfold poss_0. unfold imp_mod. unfold apply2_mod. unfold equiv_mod.
unfold apply2_mod. intros. destruct H.
unfold Maximal. unfold or_mod. unfold apply2_mod.
elim H0. intros. 
pose proof H1 P.
unfold not_mod.
unfold apply_mod. simpl.
pose proof (classic (P x0)).
destruct H2.
destruct H3.
pose proof H4 H3. left. pose proof (LA10 x P x0). pose proof H6 H5. pose proof (H7 this).
assumption.
right. 
pose proof H1 (not_mod P).
unfold not_mod in H5.
unfold apply_mod in H5. simpl in H5.
destruct H5. pose proof H6 H3.
pose proof (LA10 x (fun w : world => ~ P w) x0). pose proof H8 H7. pose proof H9 this. assumption.
Qed.

(* Cf. p.79 - The proof of Theorem 1 could be simplified a great deal if we think model-theoretically, 
using the notion of a possible world as a primitive. *)




