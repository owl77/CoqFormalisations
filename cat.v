Record Cat : Type := mkCat 
{ Obj : Type
; hom: Obj * Obj -> Type
; id : forall A: Obj, hom (A,A)
; comp :  forall (A: Obj) ( B: Obj) (C : Obj) ( f: hom (A, B)) ( g : hom (B,C)), hom (A,C)
; id_ax : forall (A: Obj) (B : Obj) (f : hom (A,B)), (comp A A B (id A) f = f) /\ (comp A B B f (id B) = f)
; ass : forall (A: Obj)(B:Obj)(C:Obj)(D:Obj)(f:hom (A,B))(g : hom (B,C))(h: hom (C,D)), comp A C D (comp A B C f g) h =   comp A B D f (comp B C D g h) 
}.

Record Smallcat ( S : Set) :=  mkSmallcat { cat : Cat; small : (Obj cat) = S}.

Definition SmallCat := sigT Smallcat.

Definition Arrows ( C :Cat) := sigT (hom C).

Definition Src ( C :Cat) ( a : Arrows C) := fst (projT1 a).

Definition Targ ( C :Cat) ( a : Arrows C) := snd (projT1 a).

Definition Terminal (C : Cat) ( A : Obj C) := forall ( B : Obj C), exists ( f :(hom C) (B,A)), forall ( g: (hom C) (B,A)), g = f.

Definition Iso (C : Cat) (A : Obj C) ( B : Obj C) := exists ( f : (hom C) (A,B)), exists ( g : (hom C) (B,A)), ((comp C) A B A f g = (id C) A /\ (comp C) B A B g f = (id C) 
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


Record NatTrans ( X: Cat * Cat) ( F : Functor X) (G : Functor X) := mkNatTrans{
eta : forall ( A : Obj (fst X) ), (hom (snd X)) ((obj X F) A,  (obj X G) A );
nat_com : forall (A : Obj (fst X)) ( B : Obj (fst X)) ( f : (hom (fst X)) (A,B) ),  
(comp (snd X))  ((obj X F) A) ((obj X F) B) ((obj X G) B )   ((arr X F) A B f) (eta B) 
= (comp (snd X))  ((obj X F) A) ((obj X G) A) ((obj X G) B) (eta A) ((arr X G) A B f)  }.


Definition NatId ( F : Func) ( A : Obj( fst (projT1 F))) :=  (id (snd (projT1 F) )) ((  (obj (projT1 F) (projT2 F) )     A)).


Definition getCat (F : Func) := fst (projT1 F).

Definition getCat2 (F: Func) := snd (projT1 F).

Theorem Natidcom : forall (F : Func) (A : Obj (getCat F ) ) ( B : Obj ( getCat F)) (f : hom (getCat F) (A,B)),
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
Qed.

Definition IdNat ( F: Func) := mkNatTrans (projT1 F) (projT2 F) (projT2 F) (NatId F) (Natidcom F).



Definition NatCompEta (X: Cat * Cat) (F : Functor X) ( G : Functor X) ( H : Functor X) (eta1 : NatTrans X F G)
(eta2 : NatTrans X G H)  := fun (A : Obj (fst X))  => (comp (snd X)) (obj X F A) (obj X G A) (obj X H A) (((eta X F G) eta1) A) 
( ((eta X G H) eta2) A).

Theorem natcompeta : forall (X: Cat * Cat) (F : Functor X) ( G : Functor X) ( H : Functor X) (eta1 : NatTrans X F G)
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


Definition NatComp  (X: Cat * Cat) (F : Functor X) ( G : Functor X) ( H : Functor X) (eta1 : NatTrans X F G) (eta2 : NatTrans X G H)
:= mkNatTrans X F H (NatCompEta X F G H eta1 eta2) (natcompeta X F G H eta1 eta2).


(* To do: define the category of functors and natural transformations between two categories. We need to show identity
and associativity laws for NatComp and IdNat *)



Record Diagram := mkDiagram { index : SmallCat; Ct : Cat ; diag : Functor ( cat (projT1 index) (projT2 index), Ct)}.


Definition Shom (x : Set * Set) := let (a,b):= x in a ->b.

Definition Sid (x : Set) :=  fun (a : x) => a.

Definition Scomp (a : Set)(b : Set)(c :Set) (f : Shom(a,b)) (g : Shom(b,c)) := fun (x: a) => g (f x).

Theorem Sid_ax : forall ( a : Set) ( b : Set) ( f : Shom (a,b) ), (Scomp a a b (Sid a) f = f) /\     (Scomp a b b f (Sid b) = f).
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

Theorem  Sass : forall (A: Set)(B:Set)(C:Set)(D:Set)(f:Shom (A,B))(g : Shom (B,C))(h: Shom (C,D)), Scomp A C D (Scomp A B C f g) h =   Scomp A B D f 
(Scomp B C D g h).
Proof.
intros.
(unfold Scomp).
(pose proof (eq_refl (fun x : A => h (g (f x))))).
assumption.
Qed.

Definition SET := mkCat Set Shom Sid Scomp Sid_ax Sass.
 
Definition PShv ( A :Cat) := Functor (A, SET).







