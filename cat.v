
(* The two rules: 1) No curly brackets (explicitness)
                  2) Import nothing (minimality, stability and self-containedness)*)

Record Cat   := mkCat 
{ Obj :  Type
; hom: Obj * Obj ->  Type
; id : forall A: Obj, hom (A,A)
; comp :  forall (A B C : Obj) ( f: hom (A, B)) ( g : hom (B,C)), hom (A,C)
; id_ax : forall (A B : Obj) (f : hom (A,B)), (comp A A B (id A) f = f) /\ (comp A B B f (id B) = f)
; ass : forall (A B C D:Obj)(f:hom (A,B))(g : hom (B,C))(h: hom (C,D)), comp A C D (comp A B C f g) h =   comp A B D f (comp B C D g h) 
}.

(* small categories should be a subtype of Cat *)

Definition Arrows ( C :Cat) := sigT (hom C).

Definition Src ( C :Cat) ( a : Arrows C) := fst (projT1 a).

Definition Targ ( C :Cat) ( a : Arrows C) := snd (projT1 a).

Definition Terminal (C : Cat) ( A : Obj C) := forall ( B : Obj C), exists ( f :(hom C) (B,A)), forall ( g: (hom C) (B,A)), g = f.

(* Or rather Record Terminal (C : Cat) := mkTerminal { TermObj : Obj C ; 
termuni :  forall ( B : Obj C), exists ( f :(hom C) (B,A)), forall ( g: (hom C) (B,A)), g = f. *)

Definition Iso (C : Cat) (A B : Obj C) := exists ( f : (hom C) (A,B)), exists ( g : (hom C) (B,A)), ((comp C) A B A f g = (id C) A /\ (comp C) B A B g f = (id C) 
B).

Theorem isoterm : forall (C :Cat) ( A : Obj C) ( B : Obj C), Terminal C A /\ Terminal C B -> Iso C A B.
Proof.
(intros **).
(unfold Iso).
(unfold Terminal).
(destruct H).
(unfold Terminal).
(unfold Terminal in H).
(unfold Terminal in H0).
(pose proof (H B)).
(pose proof (H0 A)).
(destruct H1).
(destruct H2).
(pose proof (H A)).
(destruct H3).
(pose proof (H3 ((id C) A))).
(pose proof (H3 (comp C A B A x0 x))).
(pose proof (H0 B)).
(destruct H6).
(pose proof (H6 (id C B))).
(pose proof (H6 (comp C B A B x x0))).
(pose proof (Logic.conj H5 H8)).
(rewrite <- H4 in H9).
(rewrite <- H7 in H9).
(pose proof
  (ex_intro
     (fun x : hom C (B, A) =>
      comp C A B A x0 x = id C A /\ comp C B A B x x0 = id C B) x H9)).
(pose proof
  (ex_intro
     (fun x0 : hom C (A, B) =>
      exists x : hom C (B, A),
        comp C A B A x0 x = id C A /\ comp C B A B x x0 = id C B) x0 H10)).
assumption.
Qed.

Record Functor ( X: Cat * Cat) :=  mkFunctor { 
obj : (Obj (fst X)) -> (Obj (snd X));
arr :  forall ( a : Obj (fst X) ) ( b : Obj (fst X) ), hom (fst X) (a,b) -> hom (snd X) ( obj a, obj b);
f_id : forall (a : Obj (fst X)), arr a a (id (fst X) a) = id (snd X) (obj a);
f_comp :  forall (a : Obj (fst X)) (b : Obj (fst X)) (c : Obj (fst X))( f: hom (fst X) (a,b)) ( g: hom (fst X) (b,c)), 
arr a c ((comp (fst X)) a b c f g) = (comp (snd X)) (obj a) (obj b) (obj c) (arr a b f) (arr b c g)  }.


Definition Func := sigT Functor.


Record NatTrans ( X: Cat * Cat) ( F  G : Functor X) := mkNatTrans{
eta : forall ( A : Obj (fst X) ), (hom (snd X)) ((obj X F) A,  (obj X G) A );
nat_com : forall (A  B : Obj (fst X)) ( f : (hom (fst X)) (A,B) ),  
(comp (snd X))  ((obj X F) A) ((obj X F) B) ((obj X G) B )   ((arr X F) A B f) (eta B) 
= (comp (snd X))  ((obj X F) A) ((obj X G) A) ((obj X G) B) (eta A) ((arr X G) A B f)  }.


(* Definition NatId ( F : Func) ( A : Obj( fst (projT1 F))) :=  (id (snd (projT1 F) )) ((  (obj (projT1 F) (projT2 F) )     A)). *)

Definition NatId  (X: Cat * Cat) ( F : Functor X) := fun ( A : Obj (fst X) ) =>  (id (snd X )) ( obj X F  A ).



(*Definition getCat (F : Func) := fst (projT1 F).

Definition getCat2 (F: Func) := snd (projT1 F). *)

(*Theorem Natidcom : forall (F : Func) (A  B : Obj ( getCat F)) (f : hom (getCat F) (A,B)),
(comp (getCat2 F))  (obj (projT1 F) (projT2 F) A)  (obj (projT1 F) (projT2 F)  B)  (obj (projT1 F) (projT2 F) B )   ((arr (projT1 F) (projT2 F)) A B f) ((NatId F) B) = 
(comp (snd (projT1 F) ))  ((obj (projT1 F) (projT2 F)) A) ((obj (projT1 F) (projT2 F)) A) ((obj (projT1 F) (projT2 F)) B) ((NatId F) A) ((arr (projT1 F) (projT2 F)) A B f).

Proof.
intros.
unfold NatId.
pose proof id_ax (getCat2 F).
unfold getCat.
unfold getCat2.
unfold getCat in H.
unfold getCat2 in H.
pose proof H (obj (projT1 F) (projT2 F) A).
pose proof H0  (obj (projT1 F) (projT2 F) B).
pose proof H1 (arr (projT1 F) (projT2 F) A B f).
destruct H2.
rewrite -> H2.
rewrite -> H3.
reflexivity.
Qed. *)


Theorem Natidcom : forall ( X: Cat * Cat) ( F : Functor X) ( A B : Obj (fst X)) (f : hom (fst X)(A ,B)),
(comp (snd X))  (obj  X  F A)  (obj X F  B)  (obj X F B )   (arr X F A B f) ((NatId X F) B) = 
(comp (snd X ))  (obj X F A) (obj X F A) (obj X F B) ((NatId X F) A) (arr X F A B f).

Proof.
intros.
unfold NatId.
pose proof id_ax (snd X).
pose proof H (obj X F A) (obj X F B) (arr X F A B f).
destruct H0.
rewrite -> H0.
rewrite -> H1.
reflexivity.

Qed.

Definition IdNat (X : Cat* Cat) ( F : Functor X) := mkNatTrans X F F (NatId X F) (Natidcom X F).

 

(* Definition IdNat  (F: Func) := mkNatTrans (projT1 F) (projT2 F) (projT2 F) (NatId F) (Natidcom F). *)




Definition NatCompEta (X: Cat * Cat) (F G H : Functor X) (eta1 : NatTrans X F G)
(eta2 : NatTrans X G H)  := fun (A : Obj (fst X))  => (comp (snd X)) (obj X F A) (obj X G A) (obj X H A) (((eta X F G) eta1) A) 
( ((eta X G H) eta2) A).

Theorem natcompeta : forall (X: Cat * Cat) (F G H : Functor X) (eta1 : NatTrans X F G)
(eta2 : NatTrans X G H), let eta :=  NatCompEta (X: Cat * Cat) (F : Functor X) ( G : Functor X) ( H : Functor X) (eta1 : NatTrans X F G)
(eta2 : NatTrans X G H)  in   forall (A : Obj (fst X)) ( B : Obj (fst X)) ( f : (hom (fst X)) (A,B) ),  
(comp (snd X))  ((obj X F) A) ((obj X F) B) ((obj X H) B )   ((arr X F) A B f) (eta B) 
= (comp (snd X))  ((obj X F) A) ((obj X H) A) ((obj X H) B) (eta A) ((arr X H) A B f).


Proof.
intros.
pose proof (nat_com X F G eta1).
pose proof (nat_com X G H eta2).
unfold NatCompEta in eta0.
unfold eta0.
pose proof ( (ass (snd X)) (obj X F A) (obj X F B) (obj X G B) (obj X H B) (arr X F A B f) (eta X F G eta1 B)(eta X G H eta2 B)).
rewrite <- H2.
rewrite -> H0.
pose proof ( (ass (snd X)) (obj X F A) (obj X G A) (obj X G B) (obj X H B) (eta X F G eta1 A)
 (arr X G A B f)(eta X G H eta2 B)).
rewrite -> H3.
rewrite -> H1.
pose proof ( (ass (snd X)) (obj X F A) (obj X G A) (obj X H A) (obj X H B)  (eta X F G eta1 A)
(eta X G H eta2 A) (arr X H A B f) ).
rewrite <- H4.
reflexivity.

Qed.

(* Now we can define composition of natural transformations. *)


Definition NatComp  (X: Cat * Cat) (F G  H : Functor X) (eta1 : NatTrans X F G) (eta2 : NatTrans X G H)
:= mkNatTrans X F H (NatCompEta X F G H eta1 eta2) (natcompeta X F G H eta1 eta2).


(* To do: define the category of functors and natural transformations between two categories. We need to show identity
and associativity laws for NatComp and IdNat *)

Axiom nateq : forall (X: Cat*Cat) (F G : Functor X) (eta1 eta2 : NatTrans X F G),
(eta X F G eta1) = (eta X F G eta2) -> eta1 = eta2.

(* two natural transformations are equal if their fields eta are equal *)

Axiom ext: forall (A : Type) ( T : A -> Type ) (f g : forall ( x : A), T x) , (forall (x :A), f x = g x ) -> f = g.

(* we need extensionality to prove equality of eta's *)



Theorem natidl1 : forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G) (A : Obj (fst X)),
(eta X F G (NatComp X F F G (IdNat X F)  eta1))  A = (eta X F G eta1) A. 

Proof.
intros.
unfold NatComp.
unfold IdNat.
unfold NatCompEta.
unfold NatId.
pose proof id_ax (snd X) .
unfold eta.
pose proof H (obj X F A) (obj X G A) ((eta X F G  eta1) A).
destruct H0.
assumption.

Qed.


Theorem natidr1: forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G) (A : Obj (fst X)),
(eta X F G (NatComp X F G G eta1 (IdNat X G) ))  A = (eta X F G eta1) A. 

Proof.
intros.
unfold NatComp.
unfold IdNat.
unfold NatCompEta.
unfold NatId.
pose proof id_ax (snd X) .
unfold eta.
pose proof H (obj X F A) (obj X G A) ((eta X F G  eta1) A).
destruct H0.
assumption.
Qed.




Theorem natidl2 : forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G),
(eta X F G (NatComp X F F G (IdNat X F)  eta1))   = (eta X F G eta1). 

Proof.
intros.
pose proof natidl1 X F G eta1.
pose proof ext (Obj (fst X)) (fun (x : Obj (fst X)) =>  (hom (snd X)) ((obj X F) x,  (obj X G) x ))
(eta X F G (NatComp X F F G (IdNat X F)  eta1)) (eta X F G eta1).
pose proof H0 H.
assumption.

Qed.



Theorem natidr2 : forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G),
(eta X F G (NatComp X F G G eta1 (IdNat X G) ))  = (eta X F G eta1). 

Proof.
intros.
pose proof natidr1 X F G eta1.
pose proof ext (Obj (fst X)) (fun (x : Obj (fst X)) =>  (hom (snd X)) ((obj X F) x,  (obj X G) x ))
(eta X F G (NatComp X F G G eta1 (IdNat X G) ))(eta X F G eta1). 
pose proof H0 H.
assumption.

Qed.



Theorem natidl3 : forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G),
NatComp X F F G (IdNat X F)  eta1   =  eta1.


Proof.
intros.
pose proof natidl2  X F G eta1.
pose proof nateq X F G (NatComp X F F G (IdNat X F)  eta1  ) (eta1 ).
pose proof H0 H.
assumption.
Qed.


Theorem natidr3 : forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G),
(NatComp X F G G eta1 (IdNat X G) )  =  eta1. 


Proof.
intros.
pose proof natidr2  X F G eta1.
pose proof nateq X F G (NatComp X F G G eta1 (IdNat X G) )  (eta1 ).
pose proof H0 H.
assumption.
Qed.

Theorem natid : forall (X : Cat * Cat) ( F G : Functor X) (eta1 : NatTrans X F G),
NatComp X F F G (IdNat X F)  eta1   =  eta1 /\ (NatComp X F G G eta1 (IdNat X G) )  =  eta1.

Proof.
intros.
pose proof natidl3 X F G eta1.
pose proof natidr3 X F G eta1.
pose proof (conj H H0).
assumption.
Qed.



(* associativity to define functor category *)


Theorem natass1 : forall ( X : Cat * Cat ) ( F G H I : Functor X) (eta1 : NatTrans X F G)( eta2 : NatTrans X G H)
(eta3: NatTrans X H I) ( A: Obj (fst X)),
  (eta X F I (NatComp X F H I ( NatComp X F G H eta1 eta2) eta3)) A =
  (eta X F I (NatComp X F G I eta1 ( NatComp X G H I eta2 eta3))) A.
 
Proof.
intros.
unfold NatComp.
simpl.
unfold NatCompEta.
simpl.
pose proof (ass (snd X)) (obj X F A) (obj X G A) (obj X H A) (obj X I A) (eta X F G eta1 A) (eta X G H eta2 A)(eta X H I eta3 A).
assumption.
Qed.


Theorem natass2 : forall ( X : Cat * Cat ) ( F G H I : Functor X) (eta1 : NatTrans X F G)( eta2 : NatTrans X G H)
(eta3: NatTrans X H I),
  (eta X F I (NatComp X F H I ( NatComp X F G H eta1 eta2) eta3))  =
  (eta X F I (NatComp X F G I eta1 ( NatComp X G H I eta2 eta3))).

Proof.
intros.
pose proof natass1 X F G H I eta1 eta2 eta3.
pose proof ext (Obj (fst X)) (fun (x : Obj (fst X)) =>  (hom (snd X)) ((obj X F) x,  (obj X I) x )) 
 (eta X F I (NatComp X F H I ( NatComp X F G H eta1 eta2) eta3))
  (eta X F I (NatComp X F G I eta1 ( NatComp X G H I eta2 eta3))).
pose proof H1 H0.
assumption.
Qed.

Theorem natass3 : forall ( X : Cat * Cat ) ( F G H I : Functor X) (eta1 : NatTrans X F G)( eta2 : NatTrans X G H)
(eta3: NatTrans X H I),   NatComp X F H I ( NatComp X F G H eta1 eta2) eta3 =  NatComp X F G I eta1 ( NatComp X G H I eta2 eta3).

Proof.
intros.
pose proof natass2 X F G H I eta1 eta2 eta3.
pose proof nateq X F I (NatComp X F H I ( NatComp X F G H eta1 eta2) eta3) (NatComp X F G I eta1 ( NatComp X G H I eta2 eta3)).
pose proof H1 H0.
assumption.
Qed.


Definition FunctorCat (X : Cat* Cat) := mkCat (Functor X) (fun ( Funs : Functor X * Functor X) => NatTrans X (fst Funs)(snd Funs))
(IdNat X) (NatComp X) (natid X) (natass3 X).

(* We now have, for two categories A and B the categories of functors A -> B and natural transformations. *)



Definition Shom (x : Set * Set) := let (a,b):= x in a ->b.

Definition Sid (x : Set) :=  fun (a : x) => a.

Definition Scomp (a  b  c :Set) (f : Shom(a,b)) (g : Shom(b,c)) := fun (x: a) => g (f x).

Theorem Sid_ax : forall ( a  b : Set) ( f : Shom (a,b) ), (Scomp a a b (Sid a) f = f) /\     (Scomp a b b f (Sid b) = f).
Proof.
(intros **).
(unfold Scomp).
split.
 (unfold Sid).
 (simpl).
 auto.
 (unfold Sid).
 auto.
Qed.

Theorem  Sass : forall (A B C D:Set)(f:Shom (A,B))(g : Shom (B,C))(h: Shom (C,D)), Scomp A C D (Scomp A B C f g) h =   Scomp A B D f 
(Scomp B C D g h).
Proof.
intros.
(unfold Scomp).
(pose proof (eq_refl (fun x : A => h (g (f x))))).
assumption.
Qed.

Definition SET := mkCat Set Shom Sid Scomp Sid_ax Sass.
 
(* Presheaves *)

Lemma conj_comm : forall {A B : Prop} , (A /\ B) -> (B /\ A).

Proof.
intros.
split.
apply H.
apply H.
Qed.


Lemma eq_comm : forall {U: Type} {A B : U}, (A = B) -> (B = A).

Proof.
intros.
symmetry.
assumption.
Qed.

(* Ok, so I got lazy and used  curly brackets... *)


Definition Op ( U : Cat) := let hom2 := ( fun ( X : (Obj U) * (Obj U) ) => (hom U)(snd X, fst X)) in
 mkCat (Obj U) hom2
(id U) 
(fun (A B C : Obj U) ( f : hom2(A,B)) (g : hom2(B,C)) => (comp U) C B A g f )
(fun (A B : Obj U)(f : hom2(A,B)) => conj_comm   (id_ax U B A f)) 
(fun (A B C D :Obj U)( f : hom2(A,B))(g : hom2(B,C))(h: hom2(C,D)) 
=>  eq_comm ((ass U) D C B A h g f )).



Definition PShv ( A :Cat) := FunctorCat (Op A, SET).

(* We now have presheaves ! *)

(*  To do: constant functor, category of cones, (co)limits, adjunctions via triangular identities, simplicial sets,
representable functor *)





















