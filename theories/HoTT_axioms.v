Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.


Definition Funext := forall (A : Type) (P : A -> Type)
                            (f g : forall a:A, P a), f == g -> f = g. 

Definition Propext := forall (P Q : SProp), P <-> Q -> P = Q. 

(* The frawework relies on functional extensionality *)

Axiom funext : Funext. 
Axiom propext : Propext.

Definition Fune : forall (A : Type) (P : A -> Type)
                         (f g : forall a:A, P a), f == g <-> f = g.
  intros; split. apply funext. apply apD10.
Defined. 

(*
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
*)

(*** IsContr ***)

Definition IsContr (A:Type) := { x : A & forall y, x = y}.
Existing Class IsContr. 

Fixpoint IsTrunc n A : Type := match n with
                           | O => IsContr A
                           | S n => forall x y:A, IsTrunc n (Box (x = y))
                           end.

Definition IsHProp A := IsTrunc 1 A.

Lemma IsEquivHProp {A B : Type} (f:A->B) : IsHProp (IsEquiv(f)).
Proof.
Admitted.


(* begin contractible is the lowest level of truncation *)

Definition path_contr {A} `{IsContrA : IsContr A} (x y : A) : x = y
  := let contr := IsContrA.2 in (contr x)^ @ (contr y).

Definition contr_paths_contr A `{IsContr A} (x y : A) : IsContr (Box (x = y)).
  unshelve econstructor.
  exact (box (path_contr x y)).
  intros []. reflexivity. 
Defined.

(* begin proof irrelevant is the same as IsHprop *)

Definition IsIrr A := forall x y : A, x = y. 

Definition IsIrr_inhab_IsContr A (H: IsIrr A) : A -> IsContr A :=
  fun x => existP _ x (H x).
  
Definition IsHProp_to_IsIrr A : IsHProp A -> IsIrr A :=
  fun H x y => match (H x y).1 with box e => e end. 

Definition IsIrr_to_IsHProp A : IsIrr A -> IsHProp A.
  unshelve econstructor.
  apply (box (H _ _)).
  intros []; reflexivity. 
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
  apply IsIrr_to_IsHProp. intros [x p] [y q]. apply path_sigma_uncurried.
  exact (p _).
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

Definition contr_equiv2 (A B : Type) (H : Equiv A B) : (IsContr A) -> (IsContr B).
Proof. 
  destruct H. destruct e_isequiv. intros [x P]. econstructor. intro b. 
  exact ((ap e_fun (P (e_inv b))) @ (e_retr b)).
Defined.

Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  intro X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Defined.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  intro X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Defined.

Definition trunc_equiv n A B (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n; cbn ; intros.
  - apply (contr_equiv A B f).
  - unshelve eapply (IHn (Box (e_inv f x = e_inv f y)) _ (Box (x = y))).
    + apply IsTrunc0. 
    + intros [e]. eapply box. unshelve eapply (ap_inv_equiv (e_inv f) _ _ e).
      apply isequiv_inverse. 
    + unshelve econstructor.
      * intros [e]. exact (box (ap (e_inv f) e)).
      * intros [e]. reflexivity.
      * intros [e]. reflexivity. 
Defined.

Definition Box_equiv (A B : SProp) (e : A <-> B) : Equiv (Box A) (Box B).
Proof.
  unshelve econstructor.
  - intros [a]. exact (box (Sfst e a)). 
  - unshelve econstructor.
    + intros [b]. exact (box (Ssnd e b)).
    + intros [a]. reflexivity. 
    + intros [b]. reflexivity. 
Defined.

Definition Box_forall (A:Type) (B: A -> SProp) :
  Equiv (forall a:A, Box (B a)) (Box (forall a:A, B a)).
Proof.
  unshelve econstructor.
  - intro f. apply box. intros a. exact (match f a with box b => b end). 
  - unshelve econstructor.
    * intros f a. apply box. exact (match f with box g => g a end). 
    * intro f. apply funext. intro a. destruct (f a). reflexivity.
    * intros [f]. reflexivity.
Defined. 

Definition IsTrunc_Forall {funext:Funext} A (B : A -> Type) n
           (H : forall x, IsTrunc n (B x)) : IsTrunc n (forall x, B x).
Proof.
  revert A B H. induction n; intros.
  - unshelve econstructor.
    + intro a. apply (H a).1.
    + intro f. apply funext. intro a. apply (H a).2.
  - intros f g. cbn in H. pose (Box_equiv (f = g) (f == g) (@apD10 _ _ f g  ,, funext _ _ f g )).
    unshelve refine (trunc_equiv _ (Box (f == g)) _ _).
    exact (e.(e_inv)). 
    + unshelve refine (trunc_equiv _ (forall a, Box (f a = g a)) _ _).
      exact (e_fun (Box_forall _ _)).
      eapply IHn. intro a. exact (H a (f a) (g a)).
      exact (@e_isequiv _ _ (Box_forall _ _)).
    + apply isequiv_inverse.
Defined.

(*** lemma needing this file ***)

(* lemma needing funext *)

Definition ForallSigma {A : Type} {P : A -> SProp} {Q : forall a:A, forall y:P a, SProp} :
  (forall (a:A) (y:P a), Q a y) <-> (forall z:{a:A & P a}, Q (z.1) (z.2)).
Proof.
  unshelve econstructor.
  * intro F. intro z. exact (F z.1 z.2).
  * intro G. intros a y. exact (G (a;y)).
Defined.

(*
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
 *)

Definition EquivPtype {A : Type} {B B' : A -> SProp}
           (h : forall (a:A), (B a) <-> (B' a)) :
  (forall a, B a) <-> (forall a, B' a).
Proof.
  unshelve econstructor; intros f a; destruct (h a); auto. 
Defined.
 
(* Lemmas using IsContr *)

Instance IsContr_Box {A:SProp} : A -> IsContr (Box A).
Proof.
  intro a; exists (box a). intro y; destruct y; reflexivity.
Defined.

Instance IsContr_True : IsContr (Box STrue) := IsContr_Box SI. 

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
  intro H. unshelve econstructor.
  - intro b. exact (((H b).1).1).
  - intro a. exact (((H (f a)).2 (a; eq_refl))..1).
  - intro b. exact (((H b) .1) .2). 
Defined.

Definition IsContrSingleton_r {A:Type} {a:A} : IsContr {a':A & a = a'}.
Proof.
    refine ((a; eq_refl);_); intros [a' p].
    apply path_sigma_uncurried.
    exact p.
Defined.

Definition IsContrSingleton_l {A:Type} {a:A} : IsContr {a':A & a' = a}.
Proof.
    refine ((a; eq_refl);_); intros [a' p].
    apply path_sigma_uncurried.
    exact p^.
Defined.

Definition IsContrForall_domain {A : Type} {B : A -> SProp} (C : IsContr A) :
  (forall a : A, B a) <-> (B C.1).
Proof.
  unshelve econstructor.
  + intro h. exact (h C.1).
  + intros y a. pose (C.2 a). exact (transport_eq B e y).
Defined.

(* Definition IsContrSigma_domain {A : Type} {B : A -> Type} (C : IsContr A) : *)
(*       Equiv {a:A & B a} (B C.1). *)
(* Proof. *)
(*   unshelve econstructor. *)
(*   - intros [a b]. exact ((C.2 a)^ # b). *)
(*   - unshelve eapply isequiv_adjointify. *)
(*     -- intro b. exact (C.1; b). *)
(*     -- intros [a b]. apply path_sigma_uncurried; unshelve econstructor; cbn. *)
(*        exact (C.2 a). apply transport_pV. *)
(*     -- intro x. cbn beta zeta iota. *)
(*         assert (C.2 C.1 = eq_refl). apply path2_contr. *)
(*         rewrite X. reflexivity.  *)
(* Defined.  *)

(* Definition IsContrSigma_codomain {A : Type} {B : A -> Type} (C :forall a :A, IsContr(B a)) : *)
(*   Equiv {a : A & B a} A. *)
(*   unshelve econstructor. *)
(*   - intros [a b]. exact a. *)
(*   - unshelve eapply isequiv_adjointify. *)
(*     -- intro a. unshelve econstructor. exact a. exact ((C a).1). *)
(*     -- intros [a b]. eapply EqSigma. unshelve econstructor; cbn. reflexivity. *)
(*        cbn. exact ((C a).2 b). *)
(*     -- cbn. reflexivity. *)
(* Defined. *)
