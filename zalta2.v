

Axiom object: Set.


Fixpoint nrelation ( n : nat) := match n with
| 0 => Prop
| S n => object -> (nrelation n)
end.

Require Import Nat.

Definition property := nrelation 1.


Axiom encodes : forall (o : object) (p : property), Prop.

Axiom concrete : property.


Definition Abstract (o : object) :=  
 (fun (x: object) => not (concrete x)) o.


Definition D2_Eq (F G : property) := forall (x : object), (encodes x F -> encodes x G) /\ 
(encodes x G -> encodes x F).

Axiom abs : (property -> Prop) -> object.

Axiom AObj : forall (p : property -> Prop), ((Abstract (abs p )) /\ 
(forall (F : property), encodes (abs p) F <-> p F)).

Definition platonic_form (F : property) (x : object) := (Abstract x) /\
forall (G : property), encodes x G <-> D2_Eq G F.

Theorem plato1 : forall (F : property), exists (x : object), platonic_form F x.

Proof.
intros.
pose proof AObj (fun (W : property) => D2_Eq W F).
destruct H.
pose proof H0 F.
unfold platonic_form.
exists (abs (fun W : property => D2_Eq W F)).
split.
assumption.
assumption.
Qed.

Definition Con_Eq ( x y : object) := (concrete x) /\ (concrete y) /\ forall (F : property), 
(F x <-> F y).

Definition Abs_Eq (x y : object) := (Abstract x) /\ (Abstract y) /\ forall (F : property), 
(encodes x F <-> encodes y F).

Definition Obj_Eq (x y : object) := (Con_Eq x y) \/ (Abs_Eq x y).


Definition Unique_obj (o : object -> Prop) := (exists (x: object), o x) /\ forall (y z : object),
(o y /\ o z) ->  (Obj_Eq y z).
Theorem uniqueness :forall (p: property -> Prop), Unique_obj (fun (x : object) => ((Abstract x) /\ 
(forall (F : property), encodes x F <-> p F))   ).

Proof.
intros.
unfold Unique_obj.
pose proof AObj p.
split.
exists (abs p).
assumption.
intros.
destruct H0.
unfold Obj_Eq.
right.
unfold Abs_Eq.
destruct H0.
destruct H1.
split.
assumption.
split.
assumption.
intros.
pose proof H2 F.
pose proof H3 F.
split.
destruct H4.
destruct H5.
intro.
pose proof H4 H8.
pose proof H7 H9.
assumption.
intro.
destruct H4.
destruct H5.
pose proof H5 H6.
pose proof H7 H9.
assumption.
Qed.


Theorem plato2 : forall (F : property), Unique_obj (fun (x : object) => platonic_form F x).

Proof.
intros.
unfold Unique_obj.
split.
pose proof plato1 F.
assumption.
intros.
pose proof uniqueness (fun (W : property) => D2_Eq W F).
unfold Unique_obj in H0.
destruct H0.
pose proof H1 y.
pose proof H2 z.
destruct H.
unfold platonic_form in H.
unfold platonic_form in H4.
pose proof (conj H H4).
pose proof (H3 H5).
assumption.
Qed.

Axiom iota : forall ( f : object -> Prop) ( t : Unique_obj f), object.
Axiom iota_ax : forall (f : object -> Prop) (t : Unique_obj f), f (iota f t).

Definition Form ( F: property) :=  iota (fun ( x: object) => platonic_form F x)(plato2 F).

Theorem plato3 : forall (F : property), encodes (Form F) F.
































