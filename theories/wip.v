Require Import HoTT HoTT_axioms.

Set Universe Polymorphism.


Class IsFun {A B} (R : A -> B -> Type) := isFun : forall x, IsContr {y:B & R x y} .

Definition sym {A B} (R : A -> B -> Type) := fun b a => R a b. 

Class IsWeakEquiv {A B} (R : A -> B -> Type) :=
  { isWFun :> IsFun R;
    isWFunSym :> IsFun (sym R) }.

Arguments isFun {_ _ _} _.

Definition funR {A B R} : IsFun R -> A -> B := fun H x => (H.(isFun) x).1.1.

Definition center {A B} {R : A -> B -> Type} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
  unfold IsFun. unshelve eapply IsTrunc_Forall. apply funext. intro x. 
  eapply IsHPropIsContr.
Defined. 

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

                 
Definition IsWeakEquiv_IsEquiv A B (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsEquiv (funR isWFun).
Proof.
  destruct f as [f g].  
  unshelve eapply isequiv_adjointify.
  - exact (funR g).
  - intro x. pose (b := (funR f) x). pose (r := (center f) x).
    cbn. pose ((g b).2 (x;r)). exact (e..1).
  - intro y. pose (a := (funR g) y). pose (r := (center g) y).
    cbn. pose ((f a).2 (y;r)). exact (e..1).
Defined. 

Definition IsFunRf A B (f : A -> B) : IsFun (fun a b => f a = b).
Proof.
  intro a. unshelve econstructor. exists (f a). reflexivity.
  intros [b e]. apply path_sigma_uncurried. unshelve eexists.
  exact e. cbn. apply transport_paths_r.
Defined. 

Definition IsFunRfsymIsWeakEquiv A B (f : A -> B) : IsFun (sym (fun a b => f a = b)) -> IsWeakEquiv (fun a b => f a = b).
Proof.
  econstructor. apply IsFunRf. assumption.
Defined.


Definition IsFun_forall (A A' : Type) (eA : A -> A' -> Type)
           (FAsym : IsFun (sym eA)) 
(B : A -> Type) (B' : A' -> Type) (eB : forall a a', eA a a'
                                                     -> {R : B a -> B' a' -> Type & IsFun R}) :
  {R : (forall x : A, B x) -> (forall x : A', B' x) -> Type & IsFun R}.
Proof.
  unshelve eexists.
  - exact (fun f g => forall x y (e:eA x y), (eB x y e).1 (f x) (g y)).
  - intro f.
    unshelve econstructor.
    + unshelve eexists.
      * intros x. apply ((eB ((funR FAsym) x) x (FAsym.(center) x)).2.(funR) (f (FAsym.(funR) x))).
      * intros a a' ea. cbn. pose (e := (FAsym a').2 (_ ; ea)).
        apply (transport_eq (fun X => (eB a a' ea) .1 (f a)
                                                  (((eB X .1 a' X .2) .2 (f X .1)).1) .1) e^).
        exact ((eB a a' ea).2.(center) (f a)).
    + intros [g efg]. cbn in *. eapply path_sigma_uncurried.
      unshelve eexists. cbn. apply funext.
      * intros a'.
        exact ((((eB (funR FAsym a') a' (center FAsym a')).2 (f (funR FAsym a'))).2 (g a'; efg _ a' _))..1).
      * cbn.  rewrite transport_forall_cst.
        apply funext; intro a; apply funext; intro a'; apply funext ; intro e.
        rewrite (transport_funext_aux (fun y0 y  =>
                                         forall (e0 : eA a y0), (eB a y0 e0) .1 (f a) y)).
        rewrite transport_forall_cst.
        set (T := (eB a a' e) .1 (f a)).
        rewrite <- (transport_ap T ((fun X : {y : A & sym eA a' y} =>
                                       (((eB X .1 a' X .2) .2 (f X .1)) .1) .1))).
        rewrite <- transport_pp.
        unfold center, funR, isFun.
        set (isContrT := (eB a a' e) .2 (f a)).
        destruct ((FAsym a') .2 (a; e))^. cbn.
        change (transport_eq T (isContrT .2 (g a'; efg a a' e) ..1)
                             (isContrT .1) .2 = efg a a' e).
        apply transport_pr1_path. 
Defined.
  