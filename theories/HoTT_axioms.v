Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.


Definition eq_to_equiv A B : A = B -> A ≃ B :=
  fun e => e # (Equiv_id A).

Definition Funext := forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).

(* The frawework relies on the univalence axiom and functional extensionality *)

Axiom univalence : forall A B, IsEquiv (eq_to_equiv A B).
Axiom funext : Funext. 

Definition Fune {A : Type} {P : A-> Type} (f g : forall x:A, P x) :
  Equiv (f == g ) (f = g).
Proof.
  apply Equiv_inverse. unshelve econstructor.
  exact apD10. apply funext.
Defined.

Definition Univ {A B : Type} : Equiv (A = B) (Equiv A B).
Proof.
  unshelve econstructor. apply eq_to_equiv. apply univalence.
Defined. 

Instance funext_isequiv A P (f g : forall x : A, P x) : IsEquiv (@apD10 _ _ f g) := funext _ _ _ _.

Instance univalence_isequiv A B : IsEquiv (eq_to_equiv A B) := univalence _ _.

Definition transport_apD10 A B (f g : forall x:A, B x)
           (P : forall x:A, B x -> Type)
           (e : f = g) x v: transport_eq (fun X => P x (X x))
                                                       e v
                                          = transport_eq (fun X => P x X)
                                                (apD10 e x) v.
  destruct e. reflexivity.
Defined. 


Definition transport_funext {A B} {f g : forall x:A, B x}
           (P : forall x:A, B x -> Type) x 
           (v : P x (f x)) (e : forall x, f x = g x)
            : transport_eq (fun X => P x (X x))
                                                       (e_inv apD10 e) v
                                          = transport_eq (fun X => P x X)
                                                (e x) v.
Proof.
  rewrite transport_apD10. rewrite e_retr. reflexivity.
Defined.


(* for minor differences between Prop and Type (coming from impredicativity)  *)
(* we need to state again univalence for Prop, even if in principle Prop is  *)
(* a subtype iof Type *)

Definition Equiv_id_P (A:Prop) : A ≃ A := 
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).

Definition eq_to_equiv_P (A B:Prop) : A = B -> A ≃ B :=
  fun e => @transport_eq Prop (fun X => A ≃ X) A B e (Equiv_id_P A).
             
Axiom univalence_P : forall (A B:Prop), IsEquiv (eq_to_equiv_P A B).


Definition transport_sigma_1 A (P : A -> Type) Q x y (e : x = y) X :
  (transport_eq (fun x => {y : P x & Q x y}) e X).1  =
  transport_eq P e X.1.
  destruct e. reflexivity.
Defined.

Definition transport_funext_aux {A B} {f g : forall x:A, B x}
           (P : forall x : A, B x -> Type) x 
           (v : forall x, P x (f x)) (e : forall x, f x = g x)
            : (transport_eq (fun X => forall x, P x (X x)) (e_inv apD10 e) v x)
            = transport_eq (fun y => P x y) (e x) (v x).
Proof.
  rewrite <- transport_funext.
  generalize (e_inv apD10 e). destruct e0. reflexivity.
Defined. 


(*** IsContr ***)

Definition IsContr (A:Type) := { x : A & forall y, x = y}.
Existing Class IsContr. 

Fixpoint IsTrunc n A := match n with
                           | O => IsContr A
                           | S n => forall x y:A, IsTrunc n (x = y)
                           end.

Definition IsHProp A := IsTrunc 1 A.


(* begin contractible is the lowest level of truncation *)

Definition path_contr {A} `{IsContrA : IsContr A} (x y : A) : x = y
  := let contr := IsContrA.2 in (contr x)^ @ (contr y).

Definition path2_contr {A} `{IsContr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
  intro r; destruct r. unfold path_contr.
  symmetry. apply concat_Vp.
  transitivity (path_contr x y). apply K. symmetry; apply K. 
Defined.

Definition contr_paths_contr A `{IsContr A} (x y : A) : IsContr (x = y).
  unshelve econstructor.
  exact (path_contr x y).
  exact (path2_contr _).
Defined.

(* begin proof irrelevant is the same as IsHprop *)

Definition IsIrr A := forall x y : A, x = y. 

Definition IsIrr_inhab_IsContr A (H: IsIrr A) : A -> IsContr A :=
  fun x => existT _ x (H x).
  
Definition IsHProp_to_IsIrr A : IsHProp A -> IsIrr A :=
  fun H x y => (H x y).1. 

Definition IsIrr_to_IsHProp A : IsIrr A -> IsHProp A.
  unshelve econstructor.
  apply X.
  intro e. unshelve eapply path2_contr. apply IsIrr_inhab_IsContr; auto.
Defined. 
    
Definition IsHProp_inhab_isContr A {H:A -> IsContr A} : IsHProp A.
  apply IsIrr_to_IsHProp. intros x y.
  exact (@path_contr _ (H x) _ _).
Defined.

Definition IsHProp_inhab_isContr' {A:Type} (a:A) (H : IsHProp A) : IsContr A.
Proof.
  eapply IsIrr_inhab_IsContr.
  apply (IsHProp_to_IsIrr A H).
  exact a.
Defined.
  
Definition IsWeakEmb {A B : Type} (f : A -> B) := forall x y, (f x = f y) -> (x = y).

Definition IsHProp_WeakEmb {A B:Type} (f : A -> B)
      (wemb : IsWeakEmb f) (C : IsContr B) :
      IsHProp A.
Proof.
  apply IsIrr_to_IsHProp. intros x y.
  apply (wemb x y).
  apply path_contr.
Defined.

Definition IsHPropIsContr {A} : IsHProp (IsContr A).
Admitted. 


(* Preservation of homotopy level *)

Definition contr_equiv A B (f : A -> B)
  `{IsContr A} `{IsEquiv A B f}
  : IsContr B.
Proof.
  unshelve econstructor.
  - exact (f H.1).
  - intro b. eapply concat; try exact (e_retr f b).
    apply ap. apply H.2.
Defined. 

Definition contr_equiv2 (A B : Type) (H : Equiv A B) : (IsContr A) -> (IsContr B).
Proof. 
  destruct H. destruct e_isequiv. intros [x P]. econstructor. intro b. 
  exact ((ap e_fun (P (e_inv b))) @ (e_retr b)).
Qed.

Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  intro X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Defined.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  intro X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Defined.

Axiom admit : forall X, X.
Ltac cheat := apply admit.

Instance isequiv_ap A B {x y : A} (f:A->B) {H:IsEquiv f}
  : IsEquiv (@ap _ _ f x y).
Proof. 
  unshelve econstructor; cbn. 
  - apply ap_inv_equiv. auto. 
  - intro e. destruct e. unfold ap_inv_equiv. cbn. rewrite concat_refl.
    apply concat_Vp.
  - cheat.
  - cheat. 
Defined. 


Definition trunc_equiv n A B (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n; cbn ; intros.
  - apply (contr_equiv A B f).
  - unshelve eapply (IHn ((e_inv f x = e_inv f y)) _ (x = y)).
    + apply IsTrunc0. 
    + apply ap_inv_equiv. apply isequiv_inverse. 
    + exact (@isequiv_inverse _ _ (ap (e_inv f)) (isequiv_ap B A (e_inv f))).
Defined.

Definition IsTrunc_Forall {funext:Funext} A (B : A -> Type) n
           (H : forall x, IsTrunc n (B x)) : IsTrunc n (forall x, B x).
Proof.
  revert A B H. induction n; intros.
  - unshelve econstructor.
    + intro a. apply (H a).1.
    + intro f. apply funext. intro a. apply (H a).2.
  - intros f g. cbn in H. unshelve eapply (trunc_equiv _ _ _ (e_inv (apD10))). 
    + auto.
    + apply IHn. cbn in H. intro a. exact (H a (f a) (g a)). 
    + apply isequiv_inverse.
Defined. 


(*** lemma needing this file ***)

(* lemma needing funext *)

Definition ForallSigma {A : Type} {P : A -> Type} {Q : forall a:A, forall y:P a, Type} :
  Equiv (forall (a:A) (y:P a), Q a y) (forall z:{a:A & P a}, Q (z.1) (z.2)).
Proof.
  unshelve econstructor.
  * intro F. intro z. exact (F z.1 z.2).
  * unshelve eapply isequiv_adjointify.
    - intro G. intros a y. exact (G (a;y)).
    - intro F; cbn. reflexivity.
    - intro G; cbn. apply funext; intro z.
      destruct z as [a y]; cbn. reflexivity.
Defined.

Definition SigmaSigma {A:Type} (B: A -> Type) {Q : forall (a:A) (b:B a), Type} :
      Equiv ({a:A & {b: B a & Q a b}}) ({z:{a:A & B a} & Q z.1 z.2}).
Proof.
  unshelve econstructor.
  - intros [a [b c]]. exists (a;b). exact c.
  - unshelve eapply isequiv_adjointify.
    -- intros [[a b] c]. exists a, b. exact c.
    -- intros [a [b c]]. reflexivity.
    -- intros [[a b] c]. reflexivity.
Defined.

Definition EquivPtype {A : Type} {B B' : A -> Type} (h : forall (a:A), Equiv (B a) (B' a)) :
  Equiv (forall a, B a) (forall a, B' a).
Proof.
  unshelve econstructor.
  + intro f. intro a. exact ((e_fun (h a)) (f a)).
  + unshelve eapply isequiv_adjointify.
    - intro g. intro a. destruct (h a) as [e_fun hae]. destruct hae.
      exact (e_inv (g a)).
    - intro f. apply funext; intro a.
      destruct (h a) as [e_fun hae]; destruct hae; cbn. apply e_sect.
      - intro g. apply funext; intro a.
      destruct (h a) as [e_fun hae]; destruct hae; cbn. apply e_retr.
Defined.

(* Lemmas using IsContr *)
Instance IsContr_True : IsContr True.
Proof.
  unshelve econstructor. exact I.
  intro y; destruct y; reflexivity.
Defined.

Instance IsContr_unit : IsContr unit.
Proof.
  unshelve econstructor. exact tt.
  intro y; destruct y; reflexivity.
Defined.

Definition fib {A B : Type} (f:A->B) (b:B) : Type :=
  {a:A & f(a) = b}.

Definition IsContrMap {A B : Type} (f : A -> B) :=
  forall b:B, IsContr (fib f b).

Definition IsContrMap_IsShae {A B} (f:A->B) : IsContrMap f -> IsEquiv f.
Proof.
  intro H. unshelve eapply isequiv_adjointify.
  - intro b. exact (((H b).1).1).
  - intro a. exact (((H (f a)).2 (a; eq_refl))..1).
  - intro b. exact (((H b) .1) .2). 
Defined.

Definition IsContrSingleton_r {A:Type} {a:A} : IsContr {a':A & a = a'}.
Proof.
    refine ((a; eq_refl);_); intros [a' p].
    apply path_sigma_uncurried; unshelve econstructor; cbn.
    exact p. apply transport_paths_r.
Defined.

Definition IsContrSingleton_l {A:Type} {a:A} : IsContr {a':A & a' = a}.
Proof.
    refine ((a; eq_refl);_); intros [a' p].
    apply path_sigma_uncurried; unshelve econstructor; cbn.
    exact p^. rewrite transport_paths_l. rewrite concat_refl. apply inv2.
Defined.

Definition IsContrForall_domain {A : Type} {B : A -> Type} (C : IsContr A) :
  Equiv (forall a : A, B a) (B C.1).
Proof.
  unshelve econstructor.
  + intro h. exact (h C.1).
  + unshelve eapply isequiv_adjointify.
    - intros y a. exact ((C.2 a) # y).
    - intro h. apply funext; intro a. destruct (C.2 a); cbn. reflexivity.
    - intro y. cbn. rewrite (@path2_contr _ C _ _ (C.2 C.1) eq_refl).
      cbn. reflexivity.
Defined.

Definition IsContrForall_codomain {A : Type} {B : A -> Type} (C : forall a:A, IsContr(B a)) :
Equiv (forall a : A, B a) True.
Proof.
  unshelve econstructor.
  - intro f; exact I.
  - unshelve eapply isequiv_adjointify.
    -- intro r. intro a. exact ((C a).1).
    -- intro f. cbn. apply funext; intro a. exact ((C a).2 (f a)).
    -- intro r; destruct r. reflexivity.
Defined.
  
Definition IsContrSigma_domain {A : Type} {B : A -> Type} (C : IsContr A) :
      Equiv {a:A & B a} (B C.1).
Proof.
  unshelve econstructor.
  - intros [a b]. exact ((C.2 a)^ # b).
  - unshelve eapply isequiv_adjointify.
    -- intro b. exact (C.1; b).
    -- intros [a b]. apply path_sigma_uncurried; unshelve econstructor; cbn.
       exact (C.2 a). apply transport_pV.
    -- intro x. cbn beta zeta iota.
        assert (C.2 C.1 = eq_refl). apply path2_contr.
        rewrite X. reflexivity. 
Defined. 

Definition IsContrSigma_codomain {A : Type} {B : A -> Type} (C :forall a :A, IsContr(B a)) :
  Equiv {a : A & B a} A.
  unshelve econstructor.
  - intros [a b]. exact a.
  - unshelve eapply isequiv_adjointify.
    -- intro a. unshelve econstructor. exact a. exact ((C a).1).
    -- intros [a b]. eapply EqSigma. unshelve econstructor; cbn. reflexivity.
       cbn. exact ((C a).2 b).
    -- cbn. reflexivity.
Defined.
