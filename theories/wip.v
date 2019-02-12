Require Import HoTT HoTT_axioms.

Set Universe Polymorphism.


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

Definition to_R {A B} {R : A -> B -> Type} {f : A -> B}
           (r : forall x, R x (f x)) :
  forall x y, f x = y -> R x y :=
  fun x y e => transport_eq (fun y => R x y) e (r x). 

(* Class IsFun {A B} (R : A -> B -> Type) :=  *)
(*   { funR : A -> B ; *)
(*     center : forall x, R x (funR x); *)
(*     IsEquiv_center :> forall x y, IsEquiv (to_R center x y) }. *)

(* Arguments funR {_ _ _} _ _. *)
(* Arguments center {_ _ _} _ _. *)
(* Arguments IsEquiv_center {_ _ _} _ _. *)

Class IsFun {A B} (R : A -> B -> Type) := isFun : forall x, IsContr {y:B & R x y} .

Arguments isFun {_ _ _} _.

Definition funR {A B R} : IsFun R -> A -> B := fun H x => (H.(isFun) x).1.1.

(* Coercion funR : IsFun >-> Funclass. *)

Definition center {A B} {R : A -> B -> Type} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
  unfold IsFun. unshelve eapply IsTrunc_Forall. apply funext. intro x. 
  eapply IsHPropIsContr.
Defined. 

Definition sym {A B} (R : A -> B -> Type) := fun b a => R a b. 

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Class IsWeakEquiv {A B} (R : A -> B -> Type) :=
  { isWFun :> IsFun R;
    isWFunSym :> IsFun (sym R) }.
                 
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

Definition transport_forall_cst {A B} 
           (P : A -> B -> Type) b b' (e: b = b')
           (v : forall x, P x b) 
            : (transport_eq (fun y => forall x, P x y) e v)
            = fun x => transport_eq (fun y => P x y) e (v x).
Proof.
  destruct e; reflexivity. 
Defined.


Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
: transport_eq (fun x => { y : B x & C x y }) p yz
  = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
: transport_eq (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport_eq (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

(* Definition transport_on_sigma {A: Type} {B : A -> Type} *)
(*            (P :  { x : A & B x} -> Type) *)
(*            {x1 x2 : { x : A & B x}} (e : x1 = x2) *)
(*            yz *)
(*   : transport_eq (fun X : { x : A & B x} => P X) e yz = *)
(*     transport_eq (fun y => P (x1.1;y)) (e..2) *)
(*     (transport_eq (fun x => forall y: B x, P (x;y)) (e..1) yz). *)
(*   (yz.1 ; transport_eq (fun x => C x yz.1) p yz.2). *)
(* Proof. *)
(*   destruct p. destruct yz. reflexivity. *)
(* Defined. *)

Definition transport_pr1_path A (B:A->Type) 
           (X Y : {a:A & B a}) (e : X = Y) :
  transport_eq B (e..1) X.2 = Y .2. 
Proof. 
  destruct e. reflexivity.
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
  