Require Import HoTT.
Require Import HoTT_axioms.
From Coq Require Import ssreflect.

Set Universe Polymorphism.

(* ----- Definition and properties ----- *)

Class Rel A B := rel : A -> B -> Type.

 Hint Mode Rel ! ! : typeclass_instances.
 Typeclasses Transparent Rel.
    
Arguments rel {_ _ _} _ _.
    
Notation "x ≈ y" := (rel x y) (at level 20).

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.

Definition sym {A B} (R : Rel A B) : Rel B A :=
  fun b a => a ≈ b.

Typeclasses Opaque sym.

(* Definition IsWeakEquiv and proof IsWeakEquiv ≈ IsEquiv*)
Class IsFun {A B} (R : Rel A B) :=
  isFun : forall x : A, IsContr {y:B & x ≈ y} .

Hint Mode IsFun - - ! : typeclass_instances.

Class IsWeakEquiv {A B} (R : A -> B -> Type) :=
  { isWFun :> IsFun R;
    isWFunSym : IsFun (sym R) }.

Arguments isFun {_ _ _} _.
Arguments isWFun {_ _ _} _.
Arguments isWFunSym {_ _ _} _.

#[export] Hint Extern 0 (IsFun ?A)  =>
  refine (@isWFunSym _ _ _ _) : typeclass_instances.
    
Class FR_Type A B := BuildFR_Type
    { _R :> Rel A B;
    _REquiv:> IsWeakEquiv (@rel _ _ _R);
    }.
    
Infix "⋈" := FR_Type (at level 25).
    
Arguments _R {_ _} _.
Arguments _REquiv {_ _} _.
Typeclasses Transparent _R.

Hint Extern 0 (_R _ _ _) => eassumption : typeclass_instances.

Hint Extern 0 (?x ⋈ ?y) => eassumption : typeclass_instances.

Definition IsWeakEquiv_sym A B (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsWeakEquiv (sym R).
Proof. 
  by move=> Rwe; split; [apply: isWFunSym|apply isWFun].
Defined.

Definition FR_sym {A B} : A ⋈ B -> B ⋈ A.
Proof.
  unshelve econstructor. exact (sym (_R X)).
  apply IsWeakEquiv_sym. typeclasses eauto. 
Defined.

(*** Properties about FR_Type *)

(*  Equality over R *)

Definition EqFR_Type {A B : Type} (e e' : FR_Type A B) (p : _R e = _R e')
  (q : (p # (_REquiv e) = _REquiv e')) : e = e'.
Proof.
  destruct e as [R FAB]; destruct e' as [R' FAB'].
  cbn in *. destruct p. simpl in q. destruct q. reflexivity.
Defined.


(* IsWeakEquiv is HProp *)
Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
Proof.
apply: IsTrunc_Forall => [|?]; [apply: funext|apply: IsHPropIsContr].
Defined.

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Definition EqIsWeakEquiv {A B : Type} {R : A->B->Type} (FAB FAB' : IsWeakEquiv R) 
  (p : isWFun FAB = isWFun FAB') (q : isWFunSym FAB = isWFunSym FAB') : FAB = FAB'.
Proof.
  destruct FAB as [WF WFsym]. destruct FAB' as [WF' WFsym']. cbn in *.
  destruct p. destruct q. reflexivity.
Defined.

Lemma IsFR_TypeHProp {A B : Type} (R: A->B->Type) : IsHProp (IsWeakEquiv(R)).
Proof.
  apply IsIrr_to_IsHProp; unfold IsIrr. intros FAB FAB'.
  apply EqIsWeakEquiv. apply IsFunIsHProp. apply IsFunSymIsHProp.
Defined.


(*** Properties about Equiv ***)

Definition EqEquiv {A B : Type} (e e' : Equiv A B) (p : e_fun e = e_fun e')
  (q : (p # (@e_isequiv _ _ e) = @e_isequiv _ _ e')) : e = e'.
Proof.
  destruct e as [f hae]; destruct e' as [f' hae'].
  cbn in *. destruct p. simpl in q. destruct q. reflexivity.
Defined.

(* ----- (A ≃ B) ≃ (A ⋈ B) ----- *)

(* ###  IsEquiv <- IsWeakEquiv### *)
Definition funR {A B R} : IsFun R -> A -> B := fun H x => (isFun H x).1.1.

Definition center {A B} {R : Rel A B} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsWeakEquiv_IsEquiv {A B:Type} (R : Rel A B) :
  forall (f : IsWeakEquiv R), IsEquiv (funR (isWFun f)).
Proof.
move=> [WF WFsym]. apply: (isequiv_adjointify _ (funR WFsym)) => [x|y] /=.
  exact: (((WFsym (funR WF x)).2 (x;(center WF) x))..1).
exact: (((WF (funR WFsym y)).2 (y;(center WFsym) y))..1).
Defined.
 
Definition Fun_inv (A B : Type) : (A ⋈ B) -> (A ≃ B).
Proof.
  move=>[R FAB].
  exact (BuildEquiv A B (funR (isWFun FAB)) (IsWeakEquiv_IsEquiv R FAB)).
Defined.


(* ### IsEquiv -> IsWeakEquiv  ### *)

Definition funToRel {A B : Type} (f : A -> B) : Rel A B := fun a b => f a = b.

Definition IsFunRf {A B : Type} (f : A -> B) : IsFun (funToRel f).
Proof.
  move=> a. exists (f a;eq_refl) => - [b b_fa].
  apply: path_sigma_uncurried. cbn. exists b_fa. apply transport_paths_r.
Defined.

Definition IsFun_Equiv A A' (R R': Rel A A') :
  (forall a a', R a a' ≃ R' a a') -> IsFun R -> IsFun R'.
Proof.
move=> ReR' WF x; set R'xFx := ReR' _ _ (center WF x).
exists (funR WF x; R'xFx) => - [y R'xy].
apply: path_sigma_uncurried; have Fxy := ((WF x).2 (y; e_inv' (ReR' _ _) R'xy)). cbn in *.
exists (Fxy..1); have /= := (Fxy..2); move: (Fxy..1) => /= {Fxy} Fxy.
by case: _ / Fxy R'xy => /= ??; apply: Move_equiv_equiv.
Defined.

Definition IsFunSymRf {A B : Type} (f: A -> B) : IsEquiv(f) -> IsFun (sym (funToRel f)).
Proof.
  unfold sym. move=> [e_inv e_rec e_sect e_adj]. move=> b .
  exists (e_inv b; e_sect b) => -[a p]. apply: path_sigma_uncurried. 
  exists ((ap e_inv p)^ @ (e_rec a)) => /=.
  rewrite transport_paths_Fl. 
  rewrite -(ap_V f) concat_inv inv2 ap_pp.
  rewrite ap_V -e_adj -concat_p_pp.
  destruct p. cbn. now apply concat_Vp.
Defined.

Definition IsEquiv_IsWeakEquiv {A B : Type} (f: A -> B) :
  IsEquiv(f) -> IsWeakEquiv (funToRel f).
Proof.
  move=>hae. split. apply IsFunRf. apply (IsFunSymRf _ _).
Defined.

Definition Fun (A B : Type) :  (Equiv A B) -> (FR_Type A B).
Proof.
  move=>[f hae].
  exact (BuildFR_Type A B (funToRel f) (IsEquiv_IsWeakEquiv f hae) ).
Defined.


(* ### (A ≃ B) ≃ (A ≅ B) ###*)

Definition EquivRabCenter {A B : Type} {R : A -> B -> Type} (IsFunR : IsFun R) :
  forall (a:A), forall (b:B), (funToRel (funR IsFunR) a b) ≃ R a b.
Proof.
  intros a b. unshelve econstructor.
  + exact (fun e:funR IsFunR a = b => transport_eq (fun y:B => R a y) e (center IsFunR a)).
  + apply IsContrMap_IsShae. unfold IsContrMap.
     intro y. unfold fib. have e := EqSigma (funR IsFunR a; center IsFunR a) (b; y).
     apply (contr_equiv2 _ _ e). apply contr_paths_contr. exact (IsFunR a).
Defined.

(* attention univalence s*)
Definition EqRabCenter {A B : Type} {R : A -> B -> Type} (IsFunR : IsFun R) :
  forall (a:A), forall (b:B), (funToRel (funR IsFunR) a b) = R a b.
Proof.
  intros a b. apply univalence. apply EquivRabCenter.
Defined. 

Definition IsEquiv_Equiv_Equiv_FR_Type {A B : Type} : IsEquiv (Fun A B).
Proof.
  apply: (isequiv_adjointify (Fun A B) (Fun_inv A B)) => [e|e_R] /=.
  + unshelve eapply EqEquiv.
    * destruct e as [f hae]. cbn. reflexivity.
    * apply IsEquivHProp.
  + unshelve eapply EqFR_Type.
    * destruct e_R as [R FAB]. destruct FAB as [WF WFsym] => /=.
      apply funext; move=> a; apply funext; move => b. 
      apply EqRabCenter.
    * apply IsFR_TypeHProp.
Defined.
   
Definition Equiv_Equiv_FR_Type {A B : Type} : Equiv (A ≃ B) (A ⋈ B).
Proof.
  exact (BuildEquiv _ _ (Fun A B) (IsEquiv_Equiv_Equiv_FR_Type)).
Defined.


