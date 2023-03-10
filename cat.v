Record Cat : Type := mkCat 
{ Obj : Type
; hom: Obj * Obj -> Set
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


Record Diagram := mkDiagram { index : SmallCat; C : Cat ; diag : Functor ( cat (projT1 index) (projT2 index), C)}.

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



