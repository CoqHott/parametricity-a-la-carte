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
    isWFunSym :> IsFun (sym R) }.

Arguments isFun {_ _ _} _.
Arguments isWFun {_ _ _} _.
Arguments isWFunSym {_ _ _} _.


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

Definition IsEquiv_Equiv_Equiv_FR_Type {A B : Type} : IsEquiv(Fun A B).
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



(* ----- Parametricity ----- *)

(*** Type ⋈ Type ***)
Instance FR_Type_def@{i j} : Rel@{j j j} Type@{i} Type@{i} :=
 FR_Type@{i i i i i}.

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.

Hint Extern 0 (_R _ _ _) => eassumption : typeclass_instances.
  
Instance FP_Type : Type ⋈ Type.
Proof.
  econstructor. unfold rel. unshelve econstructor => [A|B].
  all: unfold sym, FR_Type_def.
  + eapply (contr_equiv2 {B:Type & A = B}). 2: apply IsContrSingleton_r.
    apply EquivSigma; intro B. apply (@equiv_compose _ (Equiv A B) _).
    apply Univ. apply Equiv_Equiv_FR_Type.
  + eapply (contr_equiv2 {A:Type & A = B}). 2: apply IsContrSingleton_l.
  apply EquivSigma; intro A. apply (@equiv_compose _ (Equiv A B) _).
  apply Univ. apply Equiv_Equiv_FR_Type.
Defined.



(*** ∏(a:A) B ⋈ ∏(a':A') B' ***)
Definition FR_Forall {A A'} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
          (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) :
  Rel (forall x, B x) (forall y, B' y)
  :=
  fun f g => forall x y (H:x ≈ y), f x ≈ g y.


Definition IsFun_forall (A A' : Type) (B : A -> Type) (B' : A' -> Type)
  (RA : Rel A A') (RAEquiv : IsWeakEquiv RA)
  (RB: forall a a' (H: RA a a'), Rel (B a) (B' a'))
  (RBEquiv : forall a a' (H: RA a a'), IsWeakEquiv(RB a a' H)) :
IsFun (FR_Forall RA RB).
Proof.
  intro f. unfold FR_Forall. unfold rel. destruct RAEquiv as [WF WFsym]. 
  set CB := fun (a':A') => ((isWFun (RBEquiv (((WFsym a').1).1) a' (((WFsym a').1).2)) (f (((WFsym a').1).1))).1).1.
  apply (contr_equiv2 {g : forall a' : A', B' a' & CB = g }).
    2: apply IsContrSingleton_r.
  (* simpl g + a' *)
  apply Equiv_inverse. apply EquivSigma; intro g.
  eapply equiv_compose. eapply (@switch A A' _). cbn.
  eapply (@equiv_compose _ (CB == g) _). 2: apply Fune.
  apply EquivPtype; intro a'.
  (* simpl forall *)
  eapply equiv_compose. apply ForallSigma. cbn.
  eapply equiv_compose. unshelve eapply IsContrForall. exact (WFsym a').
  apply Equiv_inverse. unfold CB. apply EquivRabCenter.
Defined.

Definition Forall_sym_sym
           {A A'} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
           (RB: forall x y (H: RA x y), Rel (B x) (B' y)) :
  forall f g, FR_Forall RA RB f g ≃ sym (FR_Forall (sym RA) (fun x y e => sym (RB y x e))) f g.
Proof.
  intros. unshelve econstructor; cbn. 
  compute; intros; auto. 
  unshelve econstructor; compute => //=.
Defined. 

Definition FP_forall (A A' : Type) (eA : A ⋈ A')
           (B : A -> Type) (B' : A' -> Type) 
           (eB : forall (a:A) (a':A') (H: (_R eA) a a'), B a ⋈ B' a') :
  (forall x : A, B x) ⋈ (forall x : A', B' x).
Proof.
  unshelve econstructor. 
  * unshelve eapply FR_Forall. intros. apply (eB _ _ H).
  * split.
    + apply IsFun_forall; typeclasses eauto.
    + eapply IsFun_sym. eapply Forall_sym_sym. apply IsFun_forall.
      - destruct eA as [RA FA]. apply IsWeakEquiv_sym. exact FA.
      - intros a' a H. destruct (eB a a' H) as [RB FB].
        apply IsWeakEquiv_sym. exact FB.
Defined.



(*** List A ⋈ List B ***)

(* Definitions *)
Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Infix "::" := cons (at level 60, right associativity).

Inductive FR_list {A B} (R : A -> B -> Type) : list A -> list B -> Type :=
  listR_nil : FR_list R nil nil
| listR_cons : forall {a b l l'},
    (R a b) -> (FR_list R l l') -> FR_list R (a::l) (b::l').

Fixpoint List_center {A A' : Type} {R : A -> A' -> Type} (WF : IsFun R) (l: list A) : list A' :=
  match l with
  |[] => []
  |a::q => (funR WF a)::(List_center WF q)
  end.


(* Egalité *)
Definition List_code {A:Type} (l l' : list A) : Type :=
  match l, l' with
  |[],[] => True
  |a::q, [] => False
  |[], a'::q' => False
  |a::q, a'::q' => (a = a')*(q = q')
  end.

Definition List_encode {A:Type} {l l' : list A} : (l = l') -> (List_code l l').
Proof.
  + intro p. destruct p. destruct l => //=. 
Defined.

Definition List_decode {A:Type} {l l' : list A} : (List_code l l') -> (l = l').
Proof.
  intro r. destruct l, l' => //=; inversion r as [p q]. destruct p,q => //=.
Defined.

Definition EqList {A:Type} (l l' : list A) : Equiv (l = l') (List_code l l').
Proof.
  unshelve econstructor. 
  + exact List_encode.
  + unshelve eapply (isequiv_adjointify List_encode List_decode).
    - intro p. destruct p, l => //=.
    - intro r. destruct l, l' => //=. 
      ++ destruct r. reflexivity.
      ++ unfold List_code in r. destruct r as [p q] => //=. destruct p, q => //=. 
Defined.


(* Proof *)
Definition IsFun_list (A A' : Type) (RA : A -> A' -> Type)
           (WFA : IsFun RA) : IsFun (FR_list RA).
Proof.
  unfold IsFun. intro l. 
  apply (contr_equiv2 {l':list A' & List_center WFA l = l'}).
  + apply EquivSigma; intro l'. unshelve econstructor.
    * revert l'. induction l => l' p; induction l'; cbn in p.
      - exact (listR_nil RA).
      - destruct (EqList _ _ p). 
      - destruct (EqList _ _ p). 
      - destruct (EqList _ _ p).  unshelve eapply listR_cons. 
        -- apply (EquivRabCenter WFA a a0). exact e.
        -- eapply IHl. exact e0.
    * unshelve eapply isequiv_adjointify.
      - intro r. induction r => //=. refine (e_inv (EqList _ _) _).
        unfold List_code => //=. split.
        -- apply (e_inv (EquivRabCenter _ _ _) r).
        -- exact IHr.
      - revert l'. induction l => l' p; induction l'; destruct (EqList _ _ p); cbn in p.
        -- cbn. set d := (e_sect (EqList (@nil A') (@nil A'))) .
          refine (d p).
        -- cbn zeta beta. admit.
      - intro r. induction r => /=.
        -- reflexivity.
        -- admit.
  + apply IsContrSingleton_r.
Admitted.

Definition listR_sym_sym A A' (R : A -> A' -> Type) :
  forall l l', FR_list R l l' ≃ sym (FR_list (sym R)) l l'.
Proof.
  intros l l'. unshelve econstructor.
  * intro r; induction r. apply listR_nil. apply listR_cons => //=.
  *  unshelve eapply isequiv_adjointify.
    1 : {intro r; induction r. apply listR_nil. apply listR_cons => //=. }
    all: intro r; induction r; compute => //; apply ap; exact IHr.
Defined.

Definition FP_list (A A' : Type) (eA : A ⋈ A'):
  list A ⋈ list A'.
Proof.
  unshelve econstructor. exact (FR_list (_R eA)).
  split.
  apply IsFun_list; typeclasses eauto.
  eapply IsFun_sym. eapply listR_sym_sym. apply IsFun_list.
  destruct eA as [RA FA]. destruct FA as [WF WFsym].
  exact WFsym.
Defined.



(*** A ⊔ B ⋈ A' ⊔ B' ***)

Inductive somme (A:Type) (B:Type) : Type :=
  |inl : A -> somme A B
  |inr : B -> somme A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

Notation "A ⊔ B" := (somme A B) (at level 30).

Definition Somme_center {A A' B B' : Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type)
  (WFA : IsFun RA) (WFB : IsFun RB) : A ⊔ B -> A' ⊔ B'.
Proof.
  intro x; destruct x.
  + exact (inl(funR WFA a)).
  + exact (inr(funR WFB b)).
Defined.

Inductive FR_somme {A A' B B':Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type) : (A ⊔ B) -> (A' ⊔ B') -> Type :=
  | cons_l : forall {a a'}, RA a a' -> FR_somme RA RB (inl a) (inl a')
  | cons_r : forall {b b'}, RB b b' -> FR_somme RA RB (inr b) (inr b').

(* Egalité *)
Definition Somme_code {A B: Type} (x y : somme A B) : Type :=
  match x, y with
  |inl(a), inl(a') => a = a'
  |inl(a), inr(b) => False
  |inr(b), inl(a) => False
  |inr(b), inr(b') => b = b'
  end.

Definition Somme_encode {A B : Type} {x y : somme A B} : x = y -> Somme_code x y.
Proof.
  intro p. unfold Somme_code. destruct p, x => //=.
Defined.

Definition Somme_decode {A B : Type} {x y : A ⊔ B} : Somme_code x y -> x = y.
Proof.
  unfold Somme_code. intro r. destruct x, y; by inversion r.
Defined.

Definition EqSomme {A B : Type} (x y : A ⊔ B) : Equiv (x = y) (Somme_code x y).
Proof.
  unshelve econstructor.
  + exact Somme_encode.
  + unshelve eapply (isequiv_adjointify Somme_encode Somme_decode).
    - destruct x => -[] //=.
    - destruct x,y => // -[] //.
Defined.


(* Proof *)
Definition IsFun_somme {A A' B B' : Type} 
  (RA : A -> A' -> Type) (RB : B -> B' -> Type)
  (WFA : IsFun RA) (WFB : IsFun RB) : IsFun (FR_somme RA RB).
Proof.
  unfold IsFun. intro x.
  eapply (contr_equiv2 {y: A' ⊔ B' & Somme_center RA RB WFA WFB x = y}).
  2 : apply IsContrSingleton_r.
  apply EquivSigma; intro y. unshelve econstructor.
  * intro p. destruct x, y => /=; cbn in p.
    - eapply cons_l. eapply EquivRabCenter. refine ((EqSomme _ _) p).
    - destruct (Somme_encode p).
    - destruct (Somme_encode p).
    - eapply cons_r. eapply EquivRabCenter. refine ((EqSomme _ _) p).
  * unshelve eapply isequiv_adjointify.
    - intro r; destruct r; unfold Somme_center.
      all : eapply (e_inv (EqSomme _ _)); unfold Somme_code.
      all : eapply (e_inv (EquivRabCenter _ _ _)); exact r.
    - intro p. destruct x,y; cbn in p; cbn beta zeta.
      -- rewrite e_sect. refine (e_sect (EqSomme _ _) _).
      -- destruct (Somme_encode p). 
      -- destruct (Somme_encode p).
      -- rewrite e_sect. refine (e_sect (EqSomme _ _) _).
    - intro r; destruct r; cbn zeta beta.
      all : apply ap; rewrite e_retr e_retr => //=.
Defined.

Definition Somme_sym_sym {A A' B B': Type}
  (RA : A -> A' -> Type) (RB : B -> B' -> Type) : 
  forall {x y}, FR_somme RA RB x y ≃ sym (FR_somme (sym RA) (sym RB)) x y.
Proof.
  intros x y. unfold sym. unshelve econstructor. 
  + intro r. destruct r. 1: apply cons_l. 2: apply cons_r. all: exact r.
  + unshelve eapply isequiv_adjointify.
    1 : { intro r; destruct r. 1 :eapply cons_l. 2 :apply cons_r. all :exact r. }
    all : intro r; destruct r => //=.
Defined.

Definition FP_somme {A A' B B' : Type} (eA : A ⋈ A') (eB : B ⋈ B') : (A ⊔ B) ⋈ (A' ⊔ B').
Proof.
  destruct eA as [RA FA]; destruct eB as [RB FB].
  destruct FA as [WFA WFAsym]; destruct FB as [WFB WFBsym].
  unshelve econstructor.
  + exact (FR_somme RA RB).
  + unfold rel. unshelve econstructor.
    - apply IsFun_somme; assumption.
    - eapply IsFun_sym. eapply Somme_sym_sym. apply IsFun_somme.
      all: assumption.  
Defined.



(*** ∑(a:A) B ⋈ ∑(a':A') B' ***)

(* rappel 
Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.
 
Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Definition EqSigma {A : Type} {P : A -> Type} (w w' : {a:A & P a}) : Equiv (w = w') {p: w .1 = w' .1 & p # (w .2) = w' .2}.
Proof. *)

Definition FR_Sigma {A A' : Type} {B : A -> Type} {B' : A' -> Type}
          {RA : A -> A' -> Type} {RB : forall a a' (H:RA a a'), Rel (B a) (B' a')}
          : {a:A & B a} -> {a':A' & B' a'} -> Type.
Proof.
  intros z z'. destruct z as [a b]. destruct z' as [a' b'].
  exact ({H : RA a a' & RB a a' H b b'}).
Defined.


Definition transfert {A A'} {B : A -> Type} {B' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (H:RA a a'), Rel (B a) (B' a')} 
  {WFA : IsFun RA}
  {WFB : forall a a' (H: RA a a'), IsFun(RB a a' H)}
  (a : A) (b:B a):
  forall z:{x:A' & funR WFA a = x}, B' (z.1) .
Proof.
  intros [x p]; cbn.
  set trel := e_fun (EquivRabCenter WFA a x) p.
  exact (funR (WFB a x trel) b).
Defined. 

Definition Sigma_center {A A'} {P : A -> Type} {P' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (H:RA a a'), Rel (P a) (P' a')} 
  {WFA : IsFun RA}
  {WFB : forall a a' (H: RA a a'), IsFun(RB a a' H)} :
  { a : A & P a} -> { a' : A' & P' a'}.
Proof.
  intros [a b]. unshelve econstructor.
  exact (funR WFA a).
  exact (transfert a b ((funR WFA a); eq_refl)).
Defined.

(* Proof *)

Definition IsFun_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (H:RA a a'), Rel (B a) (B' a')} 
  (WFA : IsFun RA)
  (WFB : forall a a' (H: RA a a'), IsFun(RB a a' H)) :
  IsFun (@FR_Sigma _ _ _ _ RA RB).
Proof.
  intro z. destruct z as [a b].
  apply (contr_equiv2 {w : {a' : A' & B' a'} &  Sigma_center (a; b) = w}).
  2 : apply IsContrSingleton_r.
  apply EquivSigma; intro w. destruct w as [a' b']. 
  unfold FR_Sigma. unfold Sigma_center.
  (* Encode *)
  eapply (@equiv_compose _ {p : funR WFA a = a' & p # (transfert a b (funR WFA a; eq_refl)) = b' } _ ).
    apply EqSigma.
  (* cbn dep *)
  eapply (@equiv_compose _ {p : funR WFA a = a' & (transfert a b (a'; p) = b')} _).
    1 : { apply EquivSigma; intro p.
          destruct p; cbn. apply Equiv_id. }
  (* changement de dep ! *)
  eapply (@ equiv_compose _ {H : RA a a' & funR (WFB a a' H) b = b'} _).
    1 : { unfold transfert. unshelve econstructor.
      * intros [p r]. unshelve econstructor.
        - eapply EquivRabCenter. exact p.
        - cbn zeta beta. exact r.
      * unshelve eapply isequiv_adjointify.
        - intros [H r]. unshelve econstructor.
           -- eapply (e_inv (EquivRabCenter _ _ _) H).
           -- rewrite e_retr. exact r.
        - intros [p r]. cbn zeta beta.
          apply path_sigma_uncurried; unshelve econstructor.
          -- eapply e_sect.
          -- rewrite (@transport_paths_Fl _ _ (fun p0 : funR WFA a = a' =>
                funR (WFB a a' (EquivRabCenter WFA a a' p0)) b)).
              cheat.
        - intros [H R]. cbn beta zeta.
          apply path_sigma_uncurried; unshelve econstructor.
          -- eapply e_retr.
          -- rewrite transport_paths_Fl.
             cheat. 
    } 
  (* Equiv centre et relation *)
  eapply EquivSigma; intro H. apply EquivRabCenter.
Defined.

Definition Sigma_sym_sym {A A'} {P : A -> Type} {P' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (H:RA a a'), Rel (P a) (P' a')} :
  forall z w, (@FR_Sigma _ _ _ _ RA RB z w) ≃ sym (@FR_Sigma _ _ _ _ (sym RA) (fun x y e => sym (RB y x e))) z w.
Proof.
  intros [a b]; intros [a' b']. unfold sym. unfold FR_Sigma.
  eapply Equiv_id.
Defined.

Definition FP_sigma (A A' : Type) (B : A -> Type) (B' : A' -> Type) 
    (eA : A ⋈ A')
    (eB : forall (a:A) (a':A') (H: (_R eA) a a'), B a ⋈ B' a') :
  {a:A & B a} ⋈ {a':A' & B' a'}.
Proof.
  destruct eA as [RA FA]. destruct FA as [WFA WFAsym].
  unshelve econstructor. unfold Rel.
  * eapply FR_Sigma.
  * split.
    + apply IsFun_sigma; typeclasses eauto.
    + eapply IsFun_sym. eapply Sigma_sym_sym. apply IsFun_sigma.
      - exact WFAsym.
      - intros a' a H. destruct (eB a a' H) as [RB FB].
      destruct FB as [WFB WFBsym]. exact WFBsym.
Defined.
     

