
(* The two rules: 1) Avoid curly brackets and _ as much as possible (explicitness)
                  2) Import nothing extra  beyond standard library
                    (minimality, stability, clarity, logic-centric and self-containedness)*)

(* 17-08-23 : Defined functor categories, comma categories, diagonal functor, cone categories, (co)limits, 
the category SET, presheaves, Yoneda embedding, the terminal category, category with two objects. 
Adjunctions now are easy to define via unit-counit adjunctions*)

(* 18-08-23 : Defined category with two objects and minimal arrows. Subtle interplay between
Empty_set and singletons, induction, and natural deduction negation law *)

(* 20-08-23 : Functor composition, Godement product, identity functor, lists with given length,
preparation for simplicial sets *)

(*To do: triangle identities,
adjunctions, product categories, finite categories, simplicial sets, 2-categories, 
enriched categories *)

Record Cat :=mkCat
{ Obj :  Type
; hom: Obj * Obj ->  Type
; id : forall A: Obj, hom (A,A)
; comp :  forall (A B C : Obj) ( f: hom (A, B)) ( g : hom (B,C)), hom (A,C)
; id_ax : forall (A B : Obj) (f : hom (A,B)), (comp A A B (id A) f = f) /\ (comp A B B f (id B) = f)
; ass : forall (A B C D:Obj)(f:hom (A,B))(g : hom (B,C))(h: hom (C,D)), 
comp A C D (comp A B C f g) h =   comp A B D f (comp B C D g h) 
}.

(*  some hom(A,B) may be Empty_set *)

(* Cat is a 'big' category. Must solve the problem of
defining small and locally small categories as subtypes of Cat (needed for Yoneda embedding). 
How is this done ? It is nice that Coq considers Set a subtype of Type so that we can define our
category SET. We solve this problem by coercion (on records). 
https://www.dc.fi.udc.es/staff/freire/coqdoc/pauillac.inria.fr/coq/doc/no21.htm   *)


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
f_comp :  forall (a b c  : Obj (fst X))( f: hom (fst X) (a,b)) ( g: hom (fst X) (b,c)), 
arr a c ((comp (fst X)) a b c f g) = (comp (snd X)) (obj a) (obj b) (obj c) (arr a b f) (arr b c g)  }.


Definition Func := sigT Functor.


Record NatTrans ( X: Cat * Cat) ( F  G : Functor X) := mkNatTrans{
eta : forall ( A : Obj (fst X) ), (hom (snd X)) ((obj X F) A,  (obj X G) A );
nat_com : forall (A  B : Obj (fst X)) ( f : (hom (fst X)) (A,B) ),  
(comp (snd X))  ((obj X F) A) ((obj X F) B) ((obj X G) B )   ((arr X F) A B f) (eta B) 
= (comp (snd X))  ((obj X F) A) ((obj X G) A) ((obj X G) B) (eta A) ((arr X G) A B f)  }.


(* Definition NatId ( F : Func) ( A : Obj( fst (projT1 F))) :=  (id (snd (projT1 F) )) ((  (obj (projT1 F) (projT2 F) )     A)). *)

Definition NatId  (X: Cat * Cat) ( F : Functor X) := fun ( A : Obj (fst X) ) =>  (id (snd X )) ( obj X F  A ).


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


Definition yonobj (U: Cat) (C : Obj U) (X : Obj U):=
(hom U)(X,C).


Definition yonarr (U : Cat) (C : Obj U)(A B : Obj U) (f : (hom U)(A,B))
:= fun ( x : (hom U)(B, C)) => comp U A B C f x.

(* this doesn't work because of size problems. Rather we do the following: *)


Record SmallCat := mkSmallCat
{SmObj : Set;
 Smhom: SmObj * SmObj ->  Set;
 Smid : forall A: SmObj, Smhom (A,A);
 Smcomp :  forall (A B C : SmObj) ( f: Smhom (A, B)) ( g : Smhom (B,C)), Smhom (A,C);
 Smid_ax : forall (A B : SmObj) (f : Smhom (A,B)), (Smcomp A A B (Smid A) f = f) /\ (Smcomp A B B f (Smid B) = f);
 Smass : forall (A B C D:SmObj)(f:Smhom (A,B))(g : Smhom (B,C))(h: Smhom (C,D)), 
Smcomp A C D (Smcomp A B C f g) h =   Smcomp A B D f (Smcomp B C D g h) 
}.

Definition SmOp ( U : SmallCat) := let hom2 := ( fun ( X : (SmObj U) * (SmObj U) )
 => (Smhom U)(snd X, fst X)) in
 mkSmallCat (SmObj U) hom2
(Smid U) 
(fun (A B C : SmObj U) ( f : hom2(A,B)) (g : hom2(B,C)) => (Smcomp U) C B A g f )
(fun (A B : SmObj U)(f : hom2(A,B)) => conj_comm   (Smid_ax U B A f)) 
(fun (A B C D :SmObj U)( f : hom2(A,B))(g : hom2(B,C))(h: hom2(C,D)) 
=>  eq_comm ((Smass U) D C B A h g f )).


Definition smI (U : SmallCat) := 
mkCat (SmObj U) (Smhom U) (Smid U) (Smcomp U) (Smid_ax U) (Smass U).


Coercion smI : SmallCat >-> Cat.


Definition yonobj1 (U: SmallCat) (C : SmObj U) (X : SmObj U):=
(Smhom U)(X,C).


Definition yonarr1 (U : SmallCat) (C : SmObj U)(A B : SmObj U) (f : (Smhom U)(A,B))
:= fun ( x : (hom U)(B, C)) => comp U A B C f x.

Lemma yonid_f1 : forall (U : SmallCat) (C : SmObj U)
(A : SmObj U), ((yonarr1 U C) A A ((Smid U) A) )= ((id SET) ((yonobj1 U C) A)).

Proof.
intros.
unfold yonarr1.
unfold yonobj1.
simpl.
unfold Sid.
pose proof (ext (Smhom U (A,C)) (fun (x : Smhom U (A,C)) => Smhom U (A,C)) (fun x : Smhom U (A, C) => Smcomp U A A C (Smid U A) x)
(fun a : Smhom U (A, C) => a) ).
cut ( (forall x : Smhom U (A, C),
     (fun x0 : Smhom U (A, C) => Smcomp U A A C (Smid U A) x0)
       x = (fun a : Smhom U (A, C) => a) x ) ).
assumption.
simpl.
intros.
pose proof (Smid_ax U A C x).
destruct H0.
assumption.
Qed.

Lemma yonid_comp1: forall (U : SmallCat) (W: SmObj U) (A B C : SmObj U) ( f : Smhom U (A,B)) (g : Smhom U (B,C)),
yonarr1 U W A C (Smcomp U A B C f g) = (comp SET) (yonobj1 U W C) (yonobj1 U W B) (yonobj1 U W A) (yonarr1 U W B C g)
(yonarr1 U W A B f).


Proof.
intros.
unfold yonarr1, yonobj1.
simpl.
unfold Scomp.
pose proof (Smass U A B C W f g).
pose proof (ext (Smhom U (C,W)) (fun (y: Smhom U (C,W)) => Smhom U (A,W) )
(fun x : Smhom U (C, W) =>
 Smcomp U A C W (Smcomp U A B C f g) x) (fun x : Smhom U (C, W) => Smcomp U A B W f (Smcomp U B C W g x)) ).


cut ( (forall x : Smhom U (C, W),
      (fun x0 : Smhom U (C, W) =>
       Smcomp U A C W (Smcomp U A B C f g) x0) x =
      (fun x0 : Smhom U (C, W) =>
       Smcomp U A B W f (Smcomp U B C W g x0)) x)).

assumption.
intros.
simpl.
pose proof (Smass U A B C W f g x).
assumption.
Qed.



Definition Yoneda (C: SmallCat) (W : Obj C) := mkFunctor (smI C, Op SET)
(yonobj1  C W) (yonarr1  C W) (yonid_f1 C W) (yonid_comp1 C W).

(*   Yoneda : forall C : SmallCat, Obj C -> Functor (C, Op SET)*  Not quite, but almost what we want...     *)



(* constant functor, category of cones, (co)limits, adjunctions via triangular identities, simplicial sets,
representable functor *)


Definition dobj ( X: Cat* Cat) (C: Obj (snd X)) (A :  Obj (fst X)) :=  C.
Definition darr (X : Cat * Cat) (C : Obj (snd X)) ( a : Obj (fst X) ) ( b : Obj (fst X) ) (f:  hom (fst X) (a,b))
   := (id (snd X)) C.

Theorem did_f : forall (X : Cat* Cat) (C : Obj(snd X)) 
(a : Obj (fst X)), (darr X C) a a (id (fst X) a) = id (snd X) ((dobj X C) a).

Proof.
intros.
unfold darr.
unfold dobj.
reflexivity.
Qed.

Theorem dcomp_f :forall (X: Cat * Cat) (C : Obj (snd X))
 (a : Obj (fst X)) (b : Obj (fst X)) (c : Obj (fst X))( f: hom (fst X) (a,b)) 
( g: hom (fst X) (b,c)), 
(darr X C) a c ((comp (fst X)) a b c f g) = (comp (snd X)) ((dobj X C) a)
 ((dobj X C) b) ((dobj X C) c) ((darr X C) a b f) ((darr X C) b c g).

Proof.
intros.
unfold darr.
unfold dobj.
pose proof id_ax (snd X) C C (id (snd X) C).
destruct H.
symmetry in H0.
apply H0.
Qed.

Definition Delta (X : Cat * Cat )( C: Obj (snd X)) :=
 mkFunctor X (dobj X C) (darr X C) (did_f X C)(dcomp_f X C).


Definition ConeObj (X: Cat * Cat) (C: Obj (snd X)) (D: Functor X)  :=  NatTrans X D (Delta X C).


(* Terminal Category *)

Definition TObj := unit.

Definition Thom := fun (  X : unit * unit ) => unit.

Definition Tid := fun ( A: TObj) => tt.

Definition Tcomp := fun (x y z : TObj) ( f :Thom (x ,y)) (g : Thom (y,z)) => tt.

Lemma Tid_ax: forall (A B : TObj) (f : Thom (A,B)), (Tcomp A A B (Tid A) f = f) /\ 
(Tcomp A B B f (Tid B) = f).

Proof.
intros.
unfold Tcomp.
unfold Thom in f.
unfold Tid.
split.
induction f.
reflexivity.
induction f.
reflexivity.
Qed.

Lemma Tass : forall (A B C D:TObj)(f:Thom (A,B))(g : Thom (B,C))(h: Thom (C,D)),
 Tcomp A C D (Tcomp A B C f g) h =   Tcomp A B D f (Tcomp B C D g h).

Proof. 
intros. 
unfold Tcomp. 
unfold Thom in f,g,h.   
reflexivity. 
Qed.

Definition One := mkCat TObj Thom Tid Tcomp Tid_ax Tass.


(* Functor from One to any Category sending tt to a given object C *)

Definition Tiobj (U : Cat) (C : Obj U) ( x: Obj One) := C.

Definition Tiarr (U : Cat) (C : Obj U) ( a b: Obj One) ( f: (hom One)(a,b)) 
:= (id U) C.

Lemma Tif_id: forall (U: Cat) (C : Obj U) 
(a : Obj One), (Tiarr U C) a a ((id One) a) = id U ((Tiobj U C ) a).

Proof.
intros.
unfold Tiarr.
unfold Tiobj.
reflexivity.
Qed.

Lemma Tf_comp:  forall (U : Cat) (C: Obj U) (a  b  c : Obj One)
( f: hom One (a,b)) ( g: hom One (b,c)), 
(Tiarr U C)  a c ((comp One) a b c f g) = (comp U) 
(Tiobj U C a) (Tiobj U C b) (Tiobj U C c) (Tiarr U C a b f) (Tiarr U C b c g).

Proof.
intros.
unfold Tiarr.
unfold Tiobj.
pose proof id_ax U C C (id U C).
destruct H.
symmetry.
apply H.
Qed.

Definition OneToCat (U: Cat) (C : Obj U) := mkFunctor (One, U) 
(Tiobj U C) (Tiarr U C) (Tif_id U C) (Tf_comp U C).



(* Comma Categories *)
 
Definition CommaObj (A B C : Cat)(S : Functor (A,C))(T : Functor (B,C)):=
sigT (fun (c: (Obj A)*(Obj B)) => (hom C)(obj  (A,C) S  (fst c), (obj (B,C) T (snd c)))).

Definition CommaProj1 {A B C :Cat} (S : Functor (A,C))(T : Functor (B,C))  (X : CommaObj A B C S T) := fst (projT1 X).

Definition CommaProj2 {A B C :Cat} (S : Functor (A,C))(T : Functor (B,C))   (X : CommaObj A B C S T) := snd (projT1 X).

Definition CommMor {A B C :Cat} (S : Functor (A,C))(T : Functor (B,C))  (X : CommaObj A B C S T) := projT2 X.


(* without curly brackets the proofs become unwieldy *)

Definition preCommaMor {A B C : Cat}(S : Functor (A,C))(T : Functor (B,C)) (X Y : CommaObj A B C S T):=
 (fun ( pair : ((hom A)(CommaProj1  S T X , (CommaProj1 
 S T  Y) )) *( (hom B)(CommaProj2  S T X, CommaProj2  S T Y) ))
=> let U := CommaProj1  S T    X in let V := 
CommaProj2  S T  X in let U' := CommaProj1  S T Y in let V' := CommaProj2  S T Y in
let h := CommMor  S T  X in let h' :=
 CommMor  S T  Y in let f:= fst pair in let g:= snd pair in
let SU := (obj (A,C) S U) in let SU' := (obj (A,C) S U') in let TV := (obj (B,C) T V) in let TV':= (obj (B,C) T V') in
let Sf := (arr (A,C) S U U' f) in let Tg := (arr  (B,C) T V V' g) in
(comp C) SU SU' TV' Sf h' = (comp C) SU TV TV' h Tg).

Definition CommaMor {A B C : Cat}(S : Functor (A,C))(T : Functor (B,C))
 (X : (CommaObj A B C S T) * (CommaObj A B C S T) ):=
 sigT (preCommaMor S T (fst X) (snd X)).



Definition preCommaComp {A B C : Cat} (S : Functor (A,C))(T : Functor (B,C))
( X Y Z : CommaObj A B C S T) ( f : CommaMor  S T (X,Y)) ( g : CommaMor  S T (Y,Z)) :=
let i1 := fst (projT1 f) in let i2 := snd (projT1 f) in let j1 := fst (projT1 g) in let j2 := snd (projT1 g) in
let a1:= CommaProj1  S T X in let a2 := CommaProj2  S T X in let b1:= CommaProj1  S T Y in
let b2:= CommaProj2  S T Y in let c1:= CommaProj1  S T Z in let c2:= CommaProj2  S T Z in 
( (comp A) a1 b1 c1 i1 j1,  (comp B) a2 b2  c2  i2 j2).


Theorem commacomm : forall (A B C : Cat) (S : Functor (A,C))(T : Functor (B,C))
( X Y Z : CommaObj A B C S T) ( f : CommaMor S T (X,Y)) ( g : CommaMor  S T (Y,Z)),
let a1:= CommaProj1  S T X in let a2 := CommaProj2  S T X in 
let c1:= CommaProj1  S T Z in let c2:= CommaProj2  S T Z in 
let i:= CommMor  S T X in let j:= CommMor  S T Z in
let Sa1 := (obj (A,C) S a1) in let Sc1 := (obj (A,C) S c1) in
let Ta2 := (obj (B,C) T a2) in let Tc2 := (obj (B,C) T c2) in
let (u,w) := preCommaComp  S T X Y Z f g in
let Su := (arr (A,C) S a1 c1 u) in let Tw := (arr (B,C) T a2 c2 w) in
(comp C) Sa1 Sc1 Tc2 Su j = (comp C) Sa1 Ta2 Tc2 i Tw.


Proof.
intros.
pose proof projT2 f.
pose proof projT2 g.
simpl in i.
simpl in j.
simpl in H.
simpl in H0.
simpl.
unfold Sa1.
unfold a1.
unfold Sc1.
unfold Tc2.
unfold Ta2.
unfold c2.
unfold i.
unfold j.
unfold a2.
unfold c1.
simpl in Sa1.
simpl in Sc1.
simpl in Ta2.
simpl in Tc2.
pose proof f_comp (A,C) S (CommaProj1 S T X)  (CommaProj1 S T Y)  (CommaProj1 S T Z)
(fst (projT1 f)) (fst (projT1 g)).
simpl in H1.
rewrite -> H1.
pose proof ass C (obj (A, C) S (CommaProj1 S T X)) (obj (A, C) S (CommaProj1 S T Y))
 (obj (A, C) S (CommaProj1 S T Z)) (obj (B, C) T (CommaProj2 S T Z))
(arr (A, C) S (CommaProj1 S T X) (CommaProj1 S T Y) (fst (projT1 f))) (arr (A, C) S (CommaProj1 S T Y) (CommaProj1 S T Z) (fst (projT1 g)))
(CommMor S T Z).
simpl in H2.
rewrite -> H2.
rewrite -> H0.
pose proof ass C 
(obj (A, C) S (CommaProj1 S T X)) 
(obj (A, C) S (CommaProj1 S T Y))
(obj (B, C) T (CommaProj2 S T Y))
(obj (B, C) T (CommaProj2 S T Z)) 
(arr (A, C) S (CommaProj1 S T X) (CommaProj1 S T Y) (fst (projT1 f)))
(CommMor S T Y)
(arr (B, C) T (CommaProj2 S T Y) (CommaProj2 S T Z) (snd (projT1 g))).
simpl in H3.
rewrite <- H3.
rewrite -> H.
pose proof ass C
(obj (A, C) S (CommaProj1 S T X)) 
(obj (B, C) T (CommaProj2 S T X)) 
(obj (B, C) T (CommaProj2 S T Y))
(obj (B, C) T (CommaProj2 S T Z))
(CommMor S T X)
(arr (B, C) T (CommaProj2 S T X) (CommaProj2 S T Y) (snd (projT1 f)))
(arr (B, C) T (CommaProj2 S T Y) (CommaProj2 S T Z) (snd (projT1 g))).
simpl in H4.
rewrite -> H4.
pose proof f_comp (B,C) T (CommaProj2 S T X) (CommaProj2 S T Y) (CommaProj2 S T Z)
(snd (projT1 f)) (snd (projT1 g)).
simpl in H5.
rewrite -> H5.
reflexivity.
Qed.

Definition CommaComp (A B C : Cat) (S : Functor(A,C))( T : Functor (B,C))
(X Y Z : CommaObj A B C S T)(f : CommaMor S T ( X ,Y) ) (g : CommaMor S T (Y,Z)) :=
existT (preCommaMor S T X Z) (preCommaComp S T X Y Z f g) ( commacomm A B C S T X Y Z f g).

Definition preIdComma (A B C : Cat) (S : Functor(A,C))( T : Functor (B,C)) (X : CommaObj A B C S T)
:= (  id A (CommaProj1 S T X), id B (CommaProj2 S T X) ).

Theorem commaidcomm : forall (A B C : Cat) (S : Functor(A,C))( T : Functor (B,C)) (X : CommaObj A B C S T),
let i:= preIdComma A B C S T X in
let U := CommaProj1  S T X in let V := 
CommaProj2  S T  X in let f := CommMor S T X in 
let SU := (obj (A,C) S U) in let TV := (obj (B,C) T V) in
let g1:= fst (preIdComma A B C S T X) in
let g2:= snd (preIdComma A B C S T X) in
let Sg1 := (arr (A,C) S U U g1) in let Tg2 := (arr  (B,C) T V V g2) in
(comp C) SU SU TV Sg1 f = (comp C) SU TV TV f Tg2.

Proof.
intros.
unfold SU.
unfold TV.
simpl in g1.
simpl in g2.
pose proof f_id (A,C) S U.
simpl in H.
unfold U in H.
unfold U in Sg1.
unfold g1 in Sg1.
unfold Sg1.
unfold Tg2.
unfold g1.
unfold g2.
rewrite -> H.
pose proof f_id (B,C ) T V.
simpl in H0.
unfold V.
unfold V in H0.
rewrite -> H0.
pose proof id_ax C (obj (A, C) S U) (obj (B, C) T (CommaProj2 S T X)) f.
destruct H1.
rewrite -> H2.
unfold U.
unfold U in H1.
rewrite -> H1.
reflexivity.
Qed.

Definition IdComma (A B C : Cat) (S : Functor(A,C))( T : Functor (B,C)) (X : CommaObj A B C S T)
:= existT (preCommaMor S T X X    ) (preIdComma A B C S T X) (commaidcomm A B C S T X).

(* equality between Comma morphisms *)

Axiom comma_eq: forall (A B C : Cat) (S : Functor (A,C))( T: Functor(B,C))
(X Y : CommaObj A B C S T) ( f g : CommaMor S T (X,Y)),
( (projT1 f) = (projT1 g)) -> f = g.

(* better, use inhabited for the second component *)

(* need this *)

Lemma star : forall (A B :Type) (X : A * B),
(fst X, snd X) = X.

Proof.
intros.
pose proof surjective_pairing X.
(* https://coq.inria.fr/library/Coq.Init.Datatypes.html *)
symmetry.
assumption.
Qed.


Theorem commaid_ax : forall (A B C : Cat) (S : Functor (A,C))( T: Functor(B,C))
(X Y : CommaObj A B C S T) ( f : CommaMor S T (X,Y)),
(CommaComp A B C S T X X Y (IdComma A B C S T X) f =
f) /\ (CommaComp A B C S T X Y Y f (IdComma A B C S T Y) =
f).

Proof.
intros.
split.
cut ( projT1 (CommaComp A B C S T X X Y  (IdComma A B C S T X) f)  = projT1 f ).
pose proof comma_eq A B C S T X Y 
(CommaComp A B C S T X X Y (IdComma A B C S T X) f ) f .
assumption.
unfold CommaComp; unfold IdComma.
unfold preCommaComp.
simpl.
pose proof id_ax A (CommaProj1 S T X) 
   (CommaProj1 S T Y) (fst (projT1 f)).
destruct H.
simpl in H.
rewrite -> H.
pose proof id_ax B (CommaProj2 S T X) (CommaProj2 S T Y) (snd (projT1 f)).
destruct H1.
simpl in H1.
rewrite -> H1.
pose proof star (hom A (CommaProj1 S T X, CommaProj1 S T Y)) 
     (hom B (CommaProj2 S T X, CommaProj2 S T Y)) (projT1 f).
assumption.
cut ( projT1 (CommaComp A B C S T X Y Y f (IdComma A B C S T Y)) = projT1 f).
pose proof comma_eq A B C S T X Y 
(CommaComp A B C S T X Y Y f (IdComma A B C S T Y)) f.
assumption.
unfold CommaComp; unfold IdComma.
unfold preCommaComp.
simpl.
pose proof id_ax A (CommaProj1 S T X) 
   (CommaProj1 S T Y) (fst (projT1 f)).
destruct H.
simpl in H0.
rewrite -> H0.
pose proof id_ax B (CommaProj2 S T X) (CommaProj2 S T Y) (snd (projT1 f)).
destruct H1.
simpl in H2.
rewrite -> H2.
pose proof star (hom A (CommaProj1 S T X, CommaProj1 S T Y)) 
     (hom B (CommaProj2 S T X, CommaProj2 S T Y)) (projT1 f).
assumption.
Qed.


Theorem commaass : forall (A B C : Cat) (S : Functor (A,C))( T: Functor(B,C))
(X Y Z W : CommaObj A B C S T) ( f : CommaMor S T (X,Y)) ( g : CommaMor S T (Y,Z))
( h : CommaMor S T (Z,W)),
CommaComp A B C S T X Z W (CommaComp A B C S T X Y Z f g) h = 
CommaComp A B C S T X Y W f (CommaComp A B C S T Y Z W g h).

Proof.
intros.
cut (projT1 (CommaComp A B C S T X Z W (CommaComp A B C S T X Y Z f g) h) = 
projT1 (CommaComp A B C S T X Y W f (CommaComp A B C S T Y Z W g h))).
pose proof comma_eq A B C S T X W (CommaComp A B C S T X Z W (CommaComp A B C S T X Y Z f g) h) 
(CommaComp A B C S T X Y W f (CommaComp A B C S T Y Z W g h)).
assumption.
unfold CommaComp.
unfold preCommaComp.
simpl.
pose proof (ass A (CommaProj1 S T X) (CommaProj1 S T Y) (CommaProj1 S T Z) (CommaProj1 S T W)
 (fst (projT1 f)) (fst (projT1 g)) (fst (projT1 h))).
simpl in H.
rewrite -> H.
pose proof (ass B (CommaProj2 S T X) (CommaProj2 S T Y) (CommaProj2 S T Z) (CommaProj2 S T W)
 (snd (projT1 f)) (snd (projT1 g)) (snd (projT1 h))).
simpl in H0.
rewrite -> H0.
reflexivity.
Qed.

Definition CommaCat A B C S T := mkCat (CommaObj A B C S T)
 (CommaMor S T) (IdComma A B C S T) (CommaComp A B C S T) (commaid_ax A B C S T)
( commaass A B C S T).


(* finally we can define cones and limits *)


(*We need first to turn Delta  : forall X : Cat * Cat, Obj (snd X) -> Functor X  into a functor itself *)


Definition Delta_arrow_eta ( D C : Cat) (A B : Obj C) (f : hom C (A,B))  (O : Obj D)
:= f.

Lemma Delta_arrow_comm : forall ( D C : Cat) (A B : Obj C) (f : hom C (A,B))  (O P : Obj D)
(h : hom D (O,P)),
let etO:= Delta_arrow_eta D C A B f O in let etP := Delta_arrow_eta D C A B f P in
let deltAf := arr (D,C) (Delta (D,C) A) O P h in
let deltBf := arr (D,C) (Delta (D,C) B) O P h in 
comp C A A B deltAf etO = comp C A B B etP deltBf.

Proof.
intros.
unfold deltAf, deltBf.
unfold Delta.
simpl.
unfold darr, etP, etO.
unfold Delta_arrow_eta.
simpl.
pose proof id_ax C A B f.
destruct H.
rewrite -> H.
rewrite -> H0.
reflexivity.
Qed.

Definition Delta_arrow (D C : Cat) (A B : Obj C) (f : hom C (A,B)) := mkNatTrans
(D,C) (Delta (D,C) A) (Delta (D,C) B)  (Delta_arrow_eta D C A B f)
(Delta_arrow_comm D C A B f).


Lemma Delta_id : forall (D C :Cat) ( A : Obj C),
Delta_arrow D C A A (id C A) = id (FunctorCat (D,C)) ( Delta (D,C) A).

Proof.
intros.
cut ((eta (D,C)  ( Delta (D,C) A) ( Delta (D,C) A)  (Delta_arrow D C A A (id C A))) = (eta (D,C)
( Delta (D,C) A) ( Delta (D,C) A)  (id (FunctorCat (D,C)) ( Delta (D,C) A)))). 
pose proof (nateq (D,C) ( Delta (D,C) A) ( Delta (D,C) A) 
 (Delta_arrow D C A A (id C A))  (id (FunctorCat (D,C)) ( Delta (D,C) A))  ).
assumption.
unfold Delta, FunctorCat.
simpl.
unfold NatId, Delta_arrow_eta.
simpl.
cut (forall (x: Obj D), ((fun _ : Obj D => id C A) x) = ((fun A0 : Obj D => id C (dobj (D, C) A A0)) x)).
pose proof (ext (Obj D) (fun (d : Obj D) => hom C (A,A)) (fun _ : Obj D => id C A) 
 (fun A0 : Obj D => id C (dobj (D, C) A A0)) ).
assumption.
intros.
simpl.
unfold dobj.
reflexivity.
Qed.

Lemma Delta_comp : forall ( D C: Cat) (a b c: Obj C) (f : hom C (a,b))(g : hom C (b,c)),
(Delta_arrow D C a c (comp C a b c f g)) = (comp (FunctorCat(D,C)) (Delta (D,C) a)(Delta (D,C) b) (Delta (D,C) c)
(Delta_arrow D C a b f) (Delta_arrow D C b c g)).

Proof.
intros.
cut ( eta (D,C) (Delta (D,C) a) (Delta (D,C) c)  (Delta_arrow D C a c (comp C a b c f g)) = eta 
(D,C) (Delta (D,C) a) (Delta (D,C) c)  (comp (FunctorCat(D,C)) (Delta (D,C) a)(Delta (D,C) b) (Delta (D,C) c)
(Delta_arrow D C a b f) (Delta_arrow D C b c g) ) ).

pose proof (nateq  (D,C)  (Delta (D,C) a) (Delta (D,C) c) (Delta_arrow D C a c (comp C a b c f g))
 (comp (FunctorCat(D,C)) (Delta (D,C) a)(Delta (D,C) b) (Delta (D,C) c)
(Delta_arrow D C a b f) (Delta_arrow D C b c g))).

assumption.
unfold Delta, Delta_arrow, NatCompEta, Delta_arrow_eta.
simpl.
unfold NatCompEta.
simpl.

pose proof (ext (Obj D) (fun (x: Obj D) => hom C (a,c) ) (fun _ : Obj D => comp C a b c f g) 
(fun A : Obj D => comp C (dobj (D, C) a A) (dobj (D, C) b A) (dobj (D, C) c A) f g) ).

cut ( (forall x : Obj D,
     (fun _ : Obj D => comp C a b c f g) x =
     (fun A : Obj D =>
      comp C (dobj (D, C) a A) (dobj (D, C) b A) (dobj (D, C) c A) f g) x)).
assumption.
intros.
simpl.
unfold dobj.
reflexivity.
Qed.

Definition DeltaFunctor (D C: Cat) := mkFunctor
 (C, (FunctorCat (D,C))) (Delta (D,C)) (Delta_arrow D C)  
(Delta_id D C) (Delta_comp D C).


(* finally, we can define a cone over a functor ! *)

Definition ConeCat (D C : Cat) (F : Functor (D,C)) :=
CommaCat C One (FunctorCat(D,C)) (DeltaFunctor D C) (OneToCat (FunctorCat(D,C)) F).

Definition CoConeCat ( D C : Cat) (F : Functor (D,C)) := Op (ConeCat D C F).

Definition Limit {D C : Cat} (F: Functor(D,C))  (L : Obj (ConeCat D C F)) := 
Terminal (ConeCat D C F) L.

Definition Complete (C :Cat):= forall (D: Cat) (F : Functor(D,C)), exists (L: Obj (ConeCat D C F)),
Limit F L.


Definition Complete2 (C :Cat):= forall (D: SmallCat) (F : Functor(smI D,C)), exists (L: Obj (ConeCat D C F)),
Limit F L.


(* initial object needed for colimits, define as terminal of opposite category *)

(*To do: Adjunctions via unit-counit adjunctions.  *)


Inductive IdA :Set :=
  ida : IdA.

Inductive IdB :Set :=
  idb : IdB.

Inductive Two : Set :=
 one : Two
| two : Two.

Definition Two_hom : Two * Two -> Set := fun (x : Two * Two ) => 
let (a,b) := x in match a,b with | one, one  => IdA | two, two => IdB | _,_ => Empty_set end.


Definition Two_id : forall (x : Two), Two_hom (x,x) := fun (x: Two) => match x with | one => ida 
| two => idb end.

Lemma Two_equals : forall ( x y : Two), Two_hom (x,y) -> (x = y).

Proof.
intros.
induction x,y.
induction H.
reflexivity.
simpl in H.
contradiction H.
simpl in H.
contradiction H.
reflexivity.
Qed.

Lemma Two_trans : forall (x y z : Two), Two_hom (x,y) -> Two_hom (y,z) -> Two_hom(x,z).

Proof.
intros.
pose proof Two_equals x y H.
rewrite <- H1 in H0.
assumption.
Qed.


Lemma Two_sing :  forall ( x y : IdA ), x = y.
Proof.
intros.
induction x ,y.
reflexivity.
Qed.



Lemma Two_sing' :  forall ( x y : IdB ), x = y.
Proof.
intros.
induction x ,y.
reflexivity.
Qed.


Definition Two_comp : forall (x y z : Two)(f : Two_hom (x,y))(g : Two_hom (y,z)), Two_hom(x,z)
:= fun (x y z : Two)(f : Two_hom (x,y))(g : Two_hom (y,z)) => Two_trans x y z f g.

Lemma Two_id_ax : forall (x y : Two) ( f : Two_hom (x,y)),
(Two_comp x x y (Two_id x) f = f) /\ (Two_comp x y y f (Two_id y) = f).

Proof.
intros.
induction x,y,f.
simpl.
unfold Two_comp.
split.
pose proof Two_sing (Two_trans one one one ida ida)  ida.
assumption.
pose proof Two_sing  (Two_trans one one one ida ida)  ida.
assumption.
split.
pose proof Two_sing' (Two_comp two two two (Two_id two) idb)  idb.
assumption.
pose proof Two_sing' (Two_comp two two two idb (Two_id two)) idb.
assumption.
Qed.



Lemma Two_sing2 :  forall (a b : Two) ( x y : Two_hom(a,b) ), x = y.

Proof.
intros.
induction a,b.
simpl in x,y.
pose proof Two_sing x y.
assumption.
simpl in x,y.
contradiction x.
simpl in x,y.
contradiction x.
simpl in x,y.
pose proof Two_sing' x y.
assumption.
Qed.



Definition Two_ass : forall (x y z w : Two) (f :Two_hom (x,y))(g : Two_hom(y,z))(h: Two_hom(z,w)),
Two_comp x z w (Two_comp x y z f g) h = Two_comp x y w f (Two_comp y z w g h).


Proof.
intros.
unfold Two_comp.
induction x,w.
pose proof Two_sing2 one one  (Two_trans one z one (Two_trans one y z f g) h)
 (Two_trans one y one f (Two_trans y z one g h)).
assumption.
pose proof Two_sing2 one two  (Two_trans one z two (Two_trans one y z f g) h)
 (Two_trans one y two f (Two_trans y z two g h)).
assumption.

pose proof Two_sing2 two one  (Two_trans two z one (Two_trans two y z f g) h)
 (Two_trans two y one f (Two_trans y z one g h)).
assumption.
pose proof Two_sing2 two two  (Two_trans two z two (Two_trans two y z f g) h)
 (Two_trans two y two f (Two_trans y z two g h)).
assumption.
Qed.




Definition TwoCat := mkCat Two Two_hom Two_id Two_comp Two_id_ax Two_ass.

(* the following will be useful for simplicial sets *)


Inductive fList {A: Type }: forall (n : nat), Type  :=
| nil : fList 0
| cons : forall ( n : nat), A -> fList n -> fList (S n).



Fixpoint delta (n : nat) : (fList n) := match n with
| 0 => nil
| S n => cons n (S n) (delta n) end.



(* now composition of functors and Godement product *)


Definition FuncComp_obj {A B C :Cat} (F : Functor (A,B)) (G : Functor (B,C))  :=
fun ( a : Obj A) =>  obj (B,C) G (obj (A,B) F a).



Definition FuncComp_arr {A B C :Cat} (F : Functor (A,B)) (G : Functor (B,C)) :=
fun ( a b : Obj A) (f : hom A (a,b))  =>  arr (B,C) G ( obj (A,B) F a  )
 (obj (A,B) F b ) (arr (A,B) F a b f). 


Lemma FuncComp_f_id : forall (A B C : Cat)(F : Functor (A,B)) (G : Functor (B,C))
(a : Obj A),    FuncComp_arr F G a a (id A a) =  id C (FuncComp_obj F G a).

Proof.
intros.
unfold FuncComp_arr.
unfold FuncComp_obj.
pose proof f_id (A,B) F a.
simpl in H.
rewrite -> H.
pose proof f_id (B,C) G  (obj (A, B) F a).
simpl in H0.
rewrite -> H0.
reflexivity.
Qed.

Lemma FuncComp_f_comp : forall (A B C : Cat)(F : Functor (A,B)) (G : Functor (B,C))
(a b c : Obj A) (f : hom A (a,b)) ( g : hom A (b,c)),
FuncComp_arr F G a c ( comp A a b c f g) = comp C (FuncComp_obj F G a)
(FuncComp_obj F G b) (FuncComp_obj F G c) (FuncComp_arr F G a b f) (FuncComp_arr F G b c g).

Proof.
intros.
unfold FuncComp_arr.
unfold FuncComp_obj.
pose proof f_comp (A, B) F a b c f g.
simpl in H.
rewrite -> H.
pose proof f_comp (B,C) G (obj (A, B) F a) (obj (A, B) F b) (obj (A, B) F c) (arr (A, B) F a b f)
     (arr (A, B) F b c g).
simpl in H0.
rewrite -> H0.
reflexivity.
Qed.

Definition FuncComp {A B C : Cat} (F : Functor (A,B))( G : Functor (B,C)) : Functor(A,C) :=
mkFunctor (A,C) (FuncComp_obj F G) (FuncComp_arr F G)  (FuncComp_f_id A B C F G) (FuncComp_f_comp A B C F G).


Definition Godement_eta {A B C : Cat} { F G : Functor (A,B)}{H I : Functor (B,C)}
( e : NatTrans (A,B) F G ) ( f : NatTrans (B,C) H I ):=

fun (a : Obj A) =>  let G1 :=   arr (B,C) H  (obj (A,B) F a) (obj (A,B) G a)
 ( eta (A,B) F G e a)
in  let G2 := eta (B,C) H I f  (obj (A,B) G a) in 
comp C (obj (A,C) (FuncComp F H) a) (obj (A,C) (FuncComp G H) a) 
(obj (A,C) (FuncComp  G I) a) G1 G2.

(* explanation:

                   a               F a  --e-->   G a


  F == e ==> G     H ==f==> I      H F a -----> H G a


                                   H G a --f---> I G a
   

                     composing     H F a  ------> I G a 



*)

Theorem Godement_com : forall {A B C : Cat} ( F G : Functor (A,B)) (H I : Functor (B,C))
( e : NatTrans (A,B) F G ) ( f : NatTrans (B,C) H I ),
forall (a  b : Obj A) ( m : hom A (a,b) ),  
(comp C)  (obj (A,C) (FuncComp F H)  a) (obj (A,C) (FuncComp F H) b) (obj (A,C) (FuncComp  G I) b )
   (arr (A,C) (FuncComp F H) a b m) (Godement_eta e f b ) 
= (comp C   (obj (A,C) (FuncComp F H) a) (obj (A,C) (FuncComp G I) a)
 (obj (A,C) (FuncComp G I) b) (Godement_eta e f a) (arr (A,C) (FuncComp G I) a b m)) .

Proof.
intros.
unfold FuncComp.
unfold Godement_eta.
unfold FuncComp_obj.
unfold FuncComp_arr.
unfold FuncComp_obj.
simpl.
unfold FuncComp_obj.
pose proof nat_com (A,B) F G e a b m.
simpl in H0.
pose proof  f_comp (B,C) H  (obj (A, B) F a) (obj (A, B) F b) (obj (A, B) G b) (arr (A, B) F a b m)
       (eta (A, B) F G e b).
simpl in H1.
pose proof f_comp (B,C) H (obj (A, B) F a) (obj (A, B) G a) (obj (A, B) G b) (eta (A, B) F G e a)
       (arr (A, B) G a b m).
simpl in H2.

rewrite <- H0 in H2.
rewrite -> H1 in H2.

pose proof nat_com (B, C) H I f  (obj (A, B) G a)
       (obj (A, B) G b) (arr (A, B) G a b m).

simpl in H3.

pose proof ass C (obj (B, C) H (obj (A, B) F a)) (obj (B, C) H (obj (A, B) G a)) 
(obj (B, C) I (obj (A, B) G a)) (obj (B, C) I (obj (A, B) G b)) 
 (arr (B, C) H (obj (A, B) F a) (obj (A, B) G a) (eta (A, B) F G e a))
 (eta (B, C) H I f (obj (A, B) G a))
 (arr (B, C) I (obj (A, B) G a) (obj (A, B) G b) (arr (A, B) G a b m)).

rewrite -> H4.

rewrite <- H3.

pose proof ass C (obj (B, C) H (obj (A, B) F a)) (obj (B, C) H (obj (A, B) G a)) 
 (obj (B, C) H (obj (A, B) G b))  (obj (B, C) I (obj (A, B) G b)) 
 (arr (B, C) H (obj (A, B) F a) (obj (A, B) G a) (eta (A, B) F G e a))
 (arr (B, C) H (obj (A, B) G a) (obj (A, B) G b) (arr (A, B) G a b m))
     (eta (B, C) H I f (obj (A, B) G b)).

rewrite <- H5.

rewrite <- H2.

pose proof ass C (obj (B, C) H (obj (A, B) F a)) (obj (B, C) H (obj (A, B) F b))
 (obj (B, C) H (obj (A, B) G b))
  (obj (B, C) I (obj (A, B) G b))
  (arr (B, C) H (obj (A, B) F a) (obj (A, B) F b) (arr (A, B) F a b m))
     (arr (B, C) H (obj (A, B) F b) (obj (A, B) G b) (eta (A, B) F G e b))
  (eta (B, C) H I f (obj (A, B) G b)).

rewrite -> H6.

reflexivity.
Qed.

Definition Godement {A B C : Cat} (F G : Functor (A,B)) (H I : Functor (B,C))
(e : NatTrans (A,B) F G)(f : NatTrans (B,C) H I)
:= mkNatTrans (A,C) (FuncComp F H) (FuncComp G I) (Godement_eta  e f) (Godement_com F G H I e f).



(* Identity functor *)

Definition IdFunctor_obj (A : Cat) := fun (x : Obj A) => x.
Definition IdFunctor_arr (A: Cat) := fun (a b : Obj A)(f : hom A (a,b)) => f.

Lemma  IdFunctor_id : forall (A : Cat) (a : Obj A), IdFunctor_arr A a a (id A a) = 
(id A (IdFunctor_obj A a)).
Proof.
intros.
unfold IdFunctor_arr.
unfold IdFunctor_obj.
reflexivity.
Qed.

Lemma IdFunctor_comp :  forall (A : Cat) (a b c  : Obj A )( f: hom A (a,b)) ( g: hom A (b,c)), 
IdFunctor_arr A a c ((comp A) a b c f g) = (comp A) (IdFunctor_obj A a)
 (IdFunctor_obj A  b) (IdFunctor_obj A c) (IdFunctor_arr A a b f) (IdFunctor_arr A b c g).

Proof.
intros.
unfold IdFunctor_arr.
unfold IdFunctor_obj.
reflexivity.
Qed.


Definition IdFunctor (A : Cat) : Functor (A,A) := mkFunctor (A,A) (IdFunctor_obj A) (IdFunctor_arr A)
(IdFunctor_id A) (IdFunctor_comp A).


(* a certain coherence associativity natural tranformation required *)

Definition coh_eta1 : forall (A  B :Cat) (F : Functor (A,B))(G : Functor (B,A)) (a : Obj A),

obj _ (FuncComp (FuncComp F G) F) a = obj _  (FuncComp F (FuncComp G F)) a.

Proof.
intros.
unfold FuncComp.
simpl.
unfold FuncComp_arr.
unfold FuncComp_obj.
simpl.
reflexivity.
Qed.

Definition coh_eta2 : forall (A  B :Cat) (F : Functor (A,B))(G : Functor (B,A)) (a : Obj A),
hom B (obj _ (FuncComp (FuncComp F G) F) a,  obj _  (FuncComp F (FuncComp G F)) a).

Proof.
intros.
pose proof  coh_eta1 A B F G a.
rewrite -> H.
pose proof id B (obj (A, B) (FuncComp F (FuncComp G F)) a).
assumption.
Qed.

(*
Lemma coh_eta3 :  forall (A  B :Cat) (F : Functor (A,B))(G : Functor (B,A)) (a : Obj A),
coh_eta2 A B F G a = id B (obj (A, B) (FuncComp F (FuncComp G F)) a).

Proof.
intros.
simpl.








Lemma coh_com :  forall (A  B :Cat) (F : Functor (A,B))(G : Functor (B,A)),
let F1 := (FuncComp (FuncComp F G) F) in let F2 := (FuncComp F (FuncComp G F)) in
forall (a b : Obj A ) ( f : (hom A (a,b) )),  
(comp B)  ((obj (A,B) F1  ) a) ((obj (A,B) F1) b) ((obj (A,B) F2) b )   
((arr (A,B) F1) a b f) (coh_eta2 A B F G b) 
= (comp B  ((obj (A,B) F1) a) ((obj (A,B) F2) a) ((obj (A,B) F2) b) (coh_eta2 A B F G a)
 ((arr (A,B) F2) a b f)).


Proof.

intros.
pose proof id_ax B .
pose proof coh_eta2 A B F G a.
pose proof coh_eta2 A B F G b.

*)






Record Adjunction {A B : Cat} (F : Functor (A,B))(G : Functor (B,A)):= mkAdjunction {
 Epsilon :  NatTrans (A,A) (FuncComp F G) (IdFunctor A);
 Eta  :     NatTrans (B,B)  (IdFunctor B) (FuncComp G F); }. 


(*
 triangle : (NatComp (A,B)  (FuncComp F (IdFunctor B))  (FuncComp F (FuncComp G F))
 (FuncComp (IdFunctor A) F)
 (Godement F F (IdFunctor B) (FuncComp G F) (IdNat (A,B) F) Eta) 
 (Godement (FuncComp F G) (IdFunctor A) F F Epsilon (IdNat(A,B) F)) )  = (IdNat (A,B) F)
 } .

  (NatComp (A,B)  (FuncComp F (IdFunctor B))  (FuncComp F (FuncComp G F))
 (FuncComp (IdFunctor A) F)
 (Godement F F (IdFunctor B) (FuncComp G F) (IdNat (A,B) F) Eta) 
 (Godement (FuncComp F G) (IdFunctor A) F F Epsilon (IdNat(A,B) F)) )  =

 (IdNat (A,B) F

Problem we need associativity for functor record types. The old equality problem.

The term "Godement (FuncComp F G) (IdFunctor A) F F Epsilon (IdNat (A, B) F)" has type
 "NatTrans (A, B) (FuncComp (FuncComp F G) F) (FuncComp (IdFunctor A) F)"
while it is expected to have type
 "NatTrans (A, B) (FuncComp F (FuncComp G F)) (FuncComp (IdFunctor A) F)".

Solution: think coherence diagrams.

*)
















 
 



