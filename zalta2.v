

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

Proof.
intros.
unfold Form.
pose proof (iota_ax (fun (x : object) => platonic_form F x)(plato2 F)).
unfold platonic_form.
unfold platonic_form in H.
simpl.
simpl in H.
destruct H.
pose proof H0 F.
apply H1.
unfold D2_Eq.
intros.
split.
intros.
auto.
auto.
Qed.

Definition Part (y x : object) := exists (F : property), (encodes x F) /\ F y.

Theorem Obj_eq_refl_abs : forall (x : object), Abstract x -> Obj_Eq x x.
Proof.
intros.
unfold Obj_Eq.
right.
unfold Abs_Eq.
split.
assumption.
split.
assumption.
intro.
split.
intro.
assumption.
intro. assumption.
Qed.








Theorem plato4 : forall (x y : object) (F : property), (not (Obj_Eq x y) /\ F x /\ F y) -> 
exists (o : object), (Obj_Eq o (Form F) /\ Part x o /\ Part y o).

Proof.
intros.
destruct H.
destruct H0.
pose proof plato3 F.
pose proof conj H2 H0.
exists (Form F).
split.
pose proof Obj_eq_refl_abs (Form F).
pose proof iota_ax (fun ( x: object) => platonic_form F x)(plato2 F).
unfold Form.
simpl.
simpl in H5.
unfold platonic_form in H5.
destruct H5.
unfold Form in H4.
unfold platonic_form in H4.
pose proof H4 H5.
unfold platonic_form.
assumption.
unfold Part.
split.
exists F.
assumption.
exists F.
pose proof conj H2 H1.
assumption.
Qed.


Axiom identity_D2 : forall ( p : property -> Prop) ( F G : property), (D2_Eq F G) -> ( p F <-> p G).


Axiom identity_obj : forall ( p : object -> Prop) ( o1 o2 : object), (Obj_Eq o1 o2) 
-> ( p o1 <-> p o2).



Theorem plato5 : forall (x : object) (F : property), F x <-> Part x (Form F).



Proof.
intros.
split.
intro.
unfold Part.
exists F.
pose proof plato3 F. split. assumption. assumption. intro. unfold Part in H.
elim H.
intros. destruct H0. pose proof iota_ax (fun ( x: object) => platonic_form F x)(plato2 F).
simpl in H2. unfold platonic_form in H2. destruct H2. pose proof H3 x0.
unfold Form in H0. unfold platonic_form in H0. destruct H4. pose proof H4 H0.
pose proof identity_D2 (fun (p : property) => p x) x0 F. simpl in H7.
pose proof H7 H6. destruct H8.  pose proof H8 H1. assumption.
Qed.

Theorem plato6 : forall (x : object), ( exists (F : property), Obj_Eq x (Form F)) -> Abstract x.

Proof.
intros.
elim H.
intros. unfold Form in H0. unfold platonic_form in H0. simpl in H0.
pose proof iota_ax  (fun x : object => Abstract x /\ (forall G : property,
 encodes x G <-> D2_Eq G x0)) (plato2 x0). simpl in H1.
destruct H1.
pose proof identity_obj (fun (x : object) => Abstract x). simpl in H3.
pose proof H3 x. pose proof H4 (iota
          (fun x : object => Abstract x /\ (forall G : property, encodes x G <-> D2_Eq G x0))
          (plato2 x0)). pose proof H5 H0. destruct H6.  pose proof H7 H1. assumption.
Qed.

Theorem plato7: forall (x : object), (exists (F : property), Obj_Eq x (Form F)) ->
 Part x (Form Abstract).


Proof.
intros. elim H. intros. pose proof plato6 x. pose proof H1 H. pose proof plato5 x. 
pose proof (H3 Abstract). destruct H4. pose proof H4 H2. assumption. Qed.












































