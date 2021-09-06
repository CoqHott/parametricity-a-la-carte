Require Import HoTT.
Require Import HoTT_axioms.
From Coq Require Import ssreflect.

Set Universe Polymorphism.



(* ### New Def ### *)

(* Definition IsWeakEquiv and proof IsWeakEquiv ≈ IsEquiv*)
Class IsFun {A B} (R : A -> B -> Type) :=
  isFun : forall x, IsContr {y:B & R x y} .

Hint Mode IsFun - - ! : typeclass_instances.

Definition sym {A B} (R : A -> B -> Type) : B -> A -> Type := 
  fun b a => R a b.

Typeclasses Opaque sym.

Class IsWeakEquiv {A B} (R : A -> B -> Type) :=
  { isWFun :> IsFun R;
    isWFunSym :> IsFun (sym R) }.

Arguments isFun {_ _ _} _.
Arguments isWFun {_ _ _} _.
Arguments isWFunSym {_ _ _} _.

Class EquivR A B := BuildEquivR {
      e_R :> A -> B -> Type ;
      e_isFun :> IsWeakEquiv e_R
    }.

Notation "A ≅ B" := (EquivR A B) (at level 20).

Instance IsWeakEquiv_sym A B (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsWeakEquiv (sym R).
Proof. by move=> Rwe; split; [apply: isWFunSym|apply isWFun]. Defined.



(*** Property about EquivR *)

(*  Equality over R *)
Definition Proj1R {A B : Type} (e_R : EquivR A B) : A -> B -> Type.
Proof.
  destruct e_R. exact e_R0.
Defined.

Definition Proj2R {A B : Type} (e_R : EquivR A B) : IsWeakEquiv(Proj1R e_R).
Proof.
  destruct e_R. unfold Proj1R. exact e_isFun0.
Defined.

Definition EqEquivR {A B : Type} (e e' : EquivR A B) (p : Proj1R e = Proj1R e')
  (q : (p # (Proj2R e) = Proj2R e')) : e = e'.
Proof.
  destruct e. destruct e'. unfold Proj1R in p. unfold Proj2R in q.
  destruct p. simpl in q. destruct q. reflexivity.
Defined.


(* IsWeakEquiv is HProp *)
Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
Proof.
apply: IsTrunc_Forall => [|?]; [apply: funext|apply: IsHPropIsContr].
Defined.

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Definition Proj1IWE {A B : Type} {R : A->B->Type} (e_R : IsWeakEquiv R) : IsFun(R).
Proof.
  destruct e_R. exact isWFun0.
Defined.

Definition Proj2IWE {A B : Type} {R : A->B->Type} (e_R : IsWeakEquiv R) : IsFun(sym R).
Proof.
  destruct e_R. exact isWFunSym0.
Defined.

Definition EqIsWeakEquiv {A B : Type} {R : A->B->Type} (e e' : IsWeakEquiv R) 
  (p : Proj1IWE e = Proj1IWE e') (q : Proj2IWE e = Proj2IWE e') : e = e'.
Proof.
  destruct e. destruct e'. cbn in *.
  destruct p. destruct q. reflexivity.
Defined.

Lemma IsEquivRHProp {A B : Type} (R: A->B->Type) : IsHProp (IsWeakEquiv(R)).
Proof.
  apply IsIrr_to_IsHProp. unfold IsIrr. intros e e'.
  apply EqIsWeakEquiv. apply IsFunIsHProp. apply IsFunSymIsHProp.
Defined.



(*** Property about Equiv ***)
Definition Proj1e {A B :Type} (e : Equiv A B) : A -> B.
Proof.
  destruct e. exact e_fun.
Defined.

Definition Proj2e {A B : Type} (e : Equiv A B) : IsEquiv(Proj1e e).
Proof.
  destruct e. cbn. exact e_isequiv.
Defined.

Definition EqEquiv {A B : Type} (e e' : Equiv A B) (p : Proj1e e = Proj1e e')
  (q : (p # (Proj2e e) = Proj2e e')) : e = e'.
Proof.
  destruct e. destruct e'. unfold Proj1e in p. unfold Proj2e in q.
  destruct p. simpl in q. destruct q. reflexivity.
Defined.

Lemma IsEquivHProp {A B : Type} (f:A->B) : IsHProp (IsEquiv(f)).
Proof.
Admitted.



(* ------------------------------------- *)

(* ###  IsEquiv <- IsWeakEquiv### *)
Definition funR {A B R} : IsFun R -> A -> B := fun H x => (isFun H x).1.1.

Definition center {A B} {R : A -> B -> Type} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsWeakEquiv_IsEquiv {A B:Type} (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsEquiv (funR (isWFun f)).
Proof.
move=> [f g]. apply: (isequiv_adjointify _ (funR g)) => [x|y] /=.
  exact: (((g (funR f x)).2 (x;(center f) x))..1).
exact: (((f (funR g y)).2 (y;(center g) y))..1).
Defined.
 
Definition Fun_inv (A B : Type) : (EquivR A B) -> (Equiv A B).
Proof.
  move=>[R e].
  exact (BuildEquiv A B (funR (isWFun e)) (IsWeakEquiv_IsEquiv R e)).
Defined.



(* ### IsEquiv -> IsWeakEquiv  ### *)
Definition IsFunRf {A B : Type} (f : A -> B) : IsFun (fun a b => f a = b).
Proof.
  move=> a. exists (f a;eq_refl) => - [b b_fa].
  apply: path_sigma_uncurried. exists b_fa. apply: transport_paths_r.
Defined.

Definition IsFunRfsymIsWeakEquiv A B (f : A -> B) :
  IsFun (sym (fun a b => f a = b)) -> IsWeakEquiv (fun a b => f a = b).
Proof. by move=> ?; split=> //; apply: IsFunRf. Defined.

Definition IsFun_sym A A' (R R': A -> A' -> Type) :
  (forall a a', R a a' ≃ R' a a') -> IsFun R -> IsFun R'.
Proof.
move=> ReR' FR x; set R'xFx := ReR' _ _ (center FR x).
exists (funR FR x;R'xFx) => - [y R'xy].
apply: path_sigma_uncurried; have Fxy := ((FR x).2 (y; e_inv' (ReR' _ _) R'xy)).
exists (Fxy..1); have /= := (Fxy..2); move: (Fxy..1) => /= {Fxy} Fxy.
by case: _ / Fxy R'xy => /= ??; apply: Move_equiv_equiv.
Defined.

Definition IsFunRfsym {A B : Type} (f: A -> B) : IsEquiv(f) -> IsFun (sym (fun a b => f a = b)).
Proof.
  unfold sym. move=> [e_inv e_rec e_sect e_adj]. move=> b .
  exists (e_inv b; e_sect b) => -[a p]. apply: path_sigma_uncurried. 
  exists ((ap e_inv p)^ @ (e_rec a)) => /=.
  rewrite transport_paths_Fl. 
  rewrite -(ap_V f) concat_inv inv2 ap_pp.
  rewrite ap_V -e_adj -concat_p_pp.
  destruct p. now apply concat_Vp.
Defined.

Definition IsEquiv_IsWeakEquiv {A B : Type} (f: A -> B) : IsEquiv(f) -> IsWeakEquiv(fun (a:A) (b:B) => f a = b).
Proof.
  move=>e. split. apply IsFunRf. apply (IsFunRfsym f e).
Defined.

Definition Fun (A B : Type) :  (Equiv A B) -> (EquivR A B).
Proof.
  move=>[f e].
  exact (BuildEquivR A B (fun (a:A) (b:B) => (f a = b)) (IsEquiv_IsWeakEquiv f e) ).
Defined.



(* ### (A ≃ B) ≃ (A ≅ B) ###*)

(* Lemma *)
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

Definition EquivSigma {A : Type} {P : A -> Type} (w w' : {a:A & P a}) : Equiv (w = w') {p: w .1 = w' .1 & p # (w .2) = w' .2}.
Proof.
  unshelve econstructor.
  + intro p. destruct p. unshelve econstructor.
    reflexivity. cbn. reflexivity.
  + unshelve eapply isequiv_adjointify.
    - move=>[p q]. destruct w as [w1 w2]. destruct w' as [w'1 w'2]. cbn in *.
    destruct p; destruct q; cbn. reflexivity.
    - intro p. destruct p. destruct w. cbn. reflexivity.
    - destruct w as [w1 w2]. destruct w' as [w'1 w'2]. intro r.
      destruct r as [p q]. cbn in *. destruct p. cbn in *. destruct q.
      reflexivity.
Defined.

Definition IsCTr {A B : Type} (H : Equiv A B) : (IsContr A) -> (IsContr B).
Proof. 
  destruct H. destruct e_isequiv. move=>[x P]. econstructor. intro b. 
  exact ((ap e_fun (P (e_inv b))) @ (e_retr b)).
Qed.

(* Proof *)
Definition IsEquiv_Equiv_Equiv_EquivR {A B : Type} : IsEquiv(Fun A B).
Proof.
  apply: (isequiv_adjointify (Fun A B) (Fun_inv A B)) => [e|e_R] /=.
  + unshelve eapply EqEquiv.
    * destruct e. cbn. reflexivity.
    * apply IsEquivHProp.
  + unshelve eapply EqEquivR.
    * destruct e_R as [R e_IsWeakEquiv]. destruct e_IsWeakEquiv as [IsFunR IsFunRsym]. cbn.
      apply funext; move=> a; apply funext; move => b. 
      apply univalence. unshelve econstructor.
      ++ exact (fun e:funR IsFunR a = b => transport_eq (fun y:B => R a y) e (center IsFunR a)).
      ++ apply IsContrMap_IsShae. unfold IsContrMap.
         intro y. unfold fib. have e := EquivSigma (funR IsFunR a; center IsFunR a) (b; y).
         apply (IsCTr e). apply contr_paths_contr. exact (IsFunR a).
    * apply IsEquivRHProp.
Defined.
   
Definition Equiv_Equiv_EquivR {A B : Type} : Equiv (Equiv A B) (EquivR A B).
Proof.
  exact (BuildEquiv _ _ (Fun A B) (IsEquiv_Equiv_Equiv_EquivR)).
Defined.