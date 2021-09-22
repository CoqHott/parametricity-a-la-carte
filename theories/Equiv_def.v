Require Import HoTT.
Require Import HoTT_axioms.
From Coq Require Import ssreflect.

Set Universe Polymorphism.

(* ----- Definition and properties ----- *)

(* Definition IsWeakEquiv and proof IsWeakEquiv ≈ IsEquiv*)
Class IsFun {A B} (R : A -> B -> Type) :=
  isFun : forall x, IsContr {y:B & R x y} .

Hint Mode IsFun - - ! : typeclass_instances.

Definition sym {A B} (R : A -> B -> Type) : B -> A -> Type := 
  fun b a => R a b.

Typeclasses Opaque sym.

Class IsWeakEquiv {A B} (R : A -> B -> Type) :=
  { isWFun :> IsFun R;
    isWFunSym : IsFun (sym R) }.

Arguments isFun {_ _ _} _.
Arguments isWFun {_ _ _} _.
Arguments isWFunSym {_ _ _} _.

#[export] Hint Extern 0 (IsFun ?A)  =>
  refine (@isWFunSym _ _ _ _) : typeclass_instances.

Class Rel A B := rel : A -> B -> Type.

 Hint Mode Rel ! ! : typeclass_instances.
 Typeclasses Transparent Rel.
    
Arguments rel {_ _ _} _ _.
    
Notation "x ≈ y" := (rel x y) (at level 20).
    
Class FR_Type A B := BuildFR_Type
    { _R :> Rel A B;
    _REquiv:> IsWeakEquiv (@rel _ _ _R);
    }.
    
Infix "⋈" := FR_Type (at level 25).
    
Arguments _R {_ _} _.
Arguments _REquiv {_ _} _.
Typeclasses Transparent _R.



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
Definition Proj1R {A B : Type} (e : FR_Type A B) : A -> B -> Type.
Proof.
  destruct e as [R FAB]. exact R.
Defined.

Definition Proj2R {A B : Type} (e : FR_Type A B) : IsWeakEquiv(Proj1R e).
Proof.
  destruct e as [R FAB]. unfold Proj1R. exact FAB.
Defined.

Definition EqFR_Type {A B : Type} (e e' : FR_Type A B) (p : Proj1R e = Proj1R e')
  (q : (p # (Proj2R e) = Proj2R e')) : e = e'.
Proof.
  destruct e as [R FAB]; destruct e' as [R' FAB'].
  unfold Proj1R in p; unfold Proj2R in q.
  destruct p. simpl in q. destruct q. reflexivity.
Defined.


(* IsWeakEquiv is HProp *)
Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
Proof.
apply: IsTrunc_Forall => [|?]; [apply: funext|apply: IsHPropIsContr].
Defined.

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Definition Proj1IWE {A B : Type} {R : A -> B -> Type} (FAB : IsWeakEquiv R) : IsFun(R).
Proof.
  destruct FAB as [WF WFsym]. exact WF.
Defined.

Definition Proj2IWE {A B : Type} {R : A->B->Type} (FAB : IsWeakEquiv R) : IsFun(sym R).
Proof.
  destruct FAB as [WF WFsym]. exact WFsym.
Defined.

Definition EqIsWeakEquiv {A B : Type} {R : A->B->Type} (FAB FAB' : IsWeakEquiv R) 
  (p : Proj1IWE FAB = Proj1IWE FAB') (q : Proj2IWE FAB = Proj2IWE FAB') : FAB = FAB'.
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
Definition Proj1Equiv {A B :Type} (e : Equiv A B) : A -> B.
Proof.
  destruct e as [f hae]. exact f.
Defined.

Definition Proj2Equiv {A B : Type} (e : Equiv A B) : IsEquiv(Proj1Equiv e).
Proof.
  destruct e as [f hae]. cbn. exact hae.
Defined.

Definition EqEquiv {A B : Type} (e e' : Equiv A B) (p : Proj1Equiv e = Proj1Equiv e')
  (q : (p # (Proj2Equiv e) = Proj2Equiv e')) : e = e'.
Proof.
  destruct e as [f hae]; destruct e' as [f' hae'].
  unfold Proj1Equiv in p; unfold Proj2Equiv in q.
  destruct p. simpl in q. destruct q. reflexivity.
Defined.

Lemma IsEquivHProp {A B : Type} (f:A->B) : IsHProp (IsEquiv(f)).
Proof.
Admitted.



(* ----- (A ≃ B) ≃ (A ⋈ B) ----- *)

(* ###  IsEquiv <- IsWeakEquiv### *)
Definition funR {A B R} : IsFun R -> A -> B := fun H x => (isFun H x).1.1.

Definition center {A B} {R : A -> B -> Type} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsWeakEquiv_IsEquiv {A B:Type} (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsEquiv (funR (isWFun f)).
Proof.
move=> [WF WFsym]. apply: (isequiv_adjointify _ (funR WFsym)) => [x|y] /=.
  exact: (((WFsym (funR WF x)).2 (x;(center WF) x))..1).
exact: (((WF (funR WFsym y)).2 (y;(center WFsym) y))..1).
Defined.
 
Definition Fun_inv (A B : Type) : (FR_Type A B) -> (Equiv A B).
Proof.
  move=>[R FAB].
  exact (BuildEquiv A B (funR (isWFun FAB)) (IsWeakEquiv_IsEquiv R FAB)).
Defined.


(* ### IsEquiv -> IsWeakEquiv  ### *)
Definition IsFunRf {A B : Type} (f : A -> B) : IsFun (fun a b => f a = b).
Proof.
  move=> a. exists (f a;eq_refl) => - [b b_fa].
  apply: path_sigma_uncurried. cbn. exists b_fa. apply transport_paths_r.
Defined.

Definition IsFun_sym A A' (R R': A -> A' -> Type) :
  (forall a a', R a a' ≃ R' a a') -> IsFun R -> IsFun R'.
Proof.
move=> ReR' WF x; set R'xFx := ReR' _ _ (center WF x).
exists (funR WF x; R'xFx) => - [y R'xy].
apply: path_sigma_uncurried; have Fxy := ((WF x).2 (y; e_inv' (ReR' _ _) R'xy)). cbn in *.
exists (Fxy..1); have /= := (Fxy..2); move: (Fxy..1) => /= {Fxy} Fxy.
by case: _ / Fxy R'xy => /= ??; apply: Move_equiv_equiv.
Defined.

Definition IsFunSymRf {A B : Type} (f: A -> B) : IsEquiv(f) -> IsFun (sym (fun a b => f a = b)).
Proof.
  unfold sym. move=> [e_inv e_rec e_sect e_adj]. move=> b .
  exists (e_inv b; e_sect b) => -[a p]. apply: path_sigma_uncurried. 
  exists ((ap e_inv p)^ @ (e_rec a)) => /=.
  rewrite transport_paths_Fl. 
  rewrite -(ap_V f) concat_inv inv2 ap_pp.
  rewrite ap_V -e_adj -concat_p_pp.
  destruct p. cbn. now apply concat_Vp.
Defined.

Definition IsEquiv_IsWeakEquiv {A B : Type} (f: A -> B) : IsEquiv(f) -> IsWeakEquiv(fun (a:A) (b:B) => f a = b).
Proof.
  move=>hae. split. apply IsFunRf. apply (IsFunSymRf _ _).
Defined.

Definition Fun (A B : Type) :  (Equiv A B) -> (FR_Type A B).
Proof.
  move=>[f hae].
  exact (BuildFR_Type A B (fun (a:A) (b:B) => (f a = b)) (IsEquiv_IsWeakEquiv f hae) ).
Defined.


(* ### (A ≃ B) ≃ (A ≅ B) ###*)

Definition EquivRabCenter {A B : Type} {R : A -> B -> Type} (IsFunR : IsFun R) :
  forall (a:A), forall (b:B), (funR IsFunR a = b) ≃ R a b.
Proof.
  intros a b. unshelve econstructor.
  + exact (fun e:funR IsFunR a = b => transport_eq (fun y:B => R a y) e (center IsFunR a)).
  + apply IsContrMap_IsShae. unfold IsContrMap.
     intro y. unfold fib. have e := EqSigma (funR IsFunR a; center IsFunR a) (b; y).
     apply (contr_equiv2 _ _ e). apply contr_paths_contr. exact (IsFunR a).
Defined.

(* attention univalence s*)
Definition EqRabCenter {A B : Type} {R : A -> B -> Type} (IsFunR : IsFun R) :
  forall (a:A), forall (b:B), (funR IsFunR a = b) = R a b.
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
   
Definition Equiv_Equiv_FR_Type {A B : Type} : Equiv (Equiv A B) (FR_Type A B).
Proof.
  exact (BuildEquiv _ _ (Fun A B) (IsEquiv_Equiv_Equiv_FR_Type)).
Defined.


