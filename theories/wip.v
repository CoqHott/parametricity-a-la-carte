Require Import HoTT HoTT_axioms.

Set Universe Polymorphism.

Definition to_R {A B} {R : A -> B -> Type} {f : A -> B}
           (r : forall x, R x (f x)) :
  forall x y, f x = y -> R x y :=
  fun x y e => transport_eq (fun y => R x y) e (r x). 

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

Axiom IsEquiv_IsHProp : forall A B (f : A -> B), IsHProp (IsEquiv f).

Definition IsFunctional {A B} (R : A -> B -> Type) := 
  { f : A -> B & {r : forall x, R x (f x) & forall x y, IsEquiv (to_R r x y)}}.

Definition foo A B (R : A -> B -> Type) : IsHProp (IsFunctional R).
Proof.
  apply IsIrr_to_IsHProp.
  intros [f [r Hfr] ] [f' [r' Hfr'] ].
  apply path_sigma_uncurried; cbn. unshelve eexists.
  - apply funext. intro x. exact (e_inv (to_R r x (f' x)) (r' x)).
  - cbn. apply path_sigma_uncurried. cbn. unshelve eexists.
    + apply funext. intro x. cbn.
      rewrite (transport_sigma_1 _ (fun f0 => forall x0,  R x0 (f0 x0))
                                 (fun f0 r0 => 
                                    forall (x0 : A) (y : B), IsEquiv (to_R r0 x0 y))).
      cbn. revert x. apply apD10. apply (transport_inv  (fun f0 : A -> B => forall x0 : A, R x0 (f0 x0))).
      apply funext. intro x. 
      rewrite transport_funext_aux.
      exact (e_retr (to_R r x (f' x)) (r' x)).
    + eapply IsHProp_to_IsIrr. unshelve eapply IsTrunc_Forall.
      apply funext. intro x. unshelve eapply IsTrunc_Forall.
      apply funext. intro y. apply IsEquiv_IsHProp. 
Defined. 

Definition sym {A B} (R : A -> B -> Type) := fun b a => R a b. 

Definition bar A B (R : A -> B -> Type) : IsHProp (IsFunctional (sym R)) :=
  foo B A (sym R).

Definition toto A B (R : A -> B -> Type) :
  forall (f : IsFunctional R), IsFunctional (sym R) -> IsEquiv (f.1).
Proof.
  destruct f as [f [rf rfe] ]. intros [g [rg rge] ].
  unshelve eapply isequiv_adjointify.
  - exact g.
  - intro x. exact (e_inv (@to_R  _ _ (sym R) _ rg (f x) x) (rf x)). 
  - intro y. exact (e_inv (to_R rf (g y) y) (rg y)). 
Defined. 

Definition IsFun_forall_ (A A' : Type) (eA : A -> A' -> Type)
           (H : IsFunctional (sym eA)) 
(B : A -> Type) (B' : A' -> Type) (eB : forall a a', eA a a'
                                                     -> {R : B a -> B' a' -> Type & IsFunctional R}) :
  {R : (forall x : A, B x) -> (forall x : A', B' x) -> Type & IsFunctional R}.
Proof.
  unshelve eexists.
  - exact (fun f g => forall x y (e:eA x y), (eB x y e).1 (f x) (g y)).
  - unshelve econstructor.
    + intros f x. apply ((eB (H.1 x) x (H.2.1 x)).2.1 (f (H.1 x))).
    + unshelve econstructor.
      * intros f a a' ea. pose ((eB a a' ea).2.2.1 (f a)).
        assert (((eB a a' ea) .2) .1 (f a) = ((eB (H .1 a') a' ((H .2) .1 a')) .2) .1 (f (H .1 a'))).
        pose (e_inv (IsEquiv := H.2.2 a' a) _ ea).
        pose (e_retr (IsEquiv := H.2.2 a' a) _ ea).
        rewrite <- e0.
        change (((eB a a' (to_R (H .2) .1 a' a e)) .2) .1 (f a) =
  ((eB (H .1 a') a' ((H .2) .1 a')) .2) .1 (f (H .1 a'))).
        destruct e. reflexivity.
        rewrite <- X. exact p.
      *
Abort. 
  