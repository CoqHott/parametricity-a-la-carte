Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
Require Import V1_Param_CComega_fixpoint.
From Coq Require Import ssreflect.

Set Universe Polymorphism.



(* ########################################################### *)
(* ###        Parametricity for Inductive Types            ### *)
(* ########################################################### *)

(** Generic Lemma to prove contractibility of telescope **)

Definition IsContr_telescope {A} {P RA : A -> Type}
           {RP : forall a, RA a -> P a -> Type}
  : IsContr {a:A & RA a} ->
    (forall a H, IsContr {b : P a & RP a H b}) ->
    IsContr {a : A & {b : P a & {H : RA a & RP a H b}}}.
Proof.
  intros Ha Hb. apply (contr_equiv2 {a : A & RA a}); try apply Ha.
  apply EquivSigma. intro a. eapply Equiv_inverse.
  eapply equiv_compose. eapply swap_sigma.
  cbn. apply IsContrSigma_codomain. intro H. apply Hb. 
Defined.

Ltac isFun f :=
  let x := fresh "foo" in 
  intro x; induction x ;
  eapply contr_equiv2 ; try (apply Equiv_inverse; apply f);
  repeat (eapply IsContr_telescope; intros); try apply IsContr_True;
  match goal with | H : _ |- _ => eapply H end. 




(*** A ⊔ B ⋈ A' ⊔ B' ***)
Inductive somme (A:Type) (B:Type) : Type :=
  |inl : A -> somme A B
  |inr : B -> somme A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

Notation "A ⊔ B" := (somme A B) (at level 30).

Fixpoint FR_somme {A A' B B':Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type) 
                  (x:A ⊔ B) (y:A' ⊔ B') : Type.
Proof.
  destruct x as [a | b], y as [a' | b'].
  - exact (RA a a').
  - exact False.
  - exact False.
  - exact (RB b b').
Defined.

Definition code_somme_arg {A A' B B' : Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type) (x : A ⊔ B) : Type.
  destruct x as [a | b].
  - exact ({a':A' & FR_somme RA RB (inl a) (inl a')}).
  - exact ({b':B' & FR_somme RA RB (inr b) (inr b')}).
Defined.

Definition Equiv_somme_arg {A A' B B' : Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type) (x : A ⊔ B) : 
  Equiv ({y : A'⊔B' & FR_somme RA RB x y}) (code_somme_arg RA RB x).
  unfold code_somme_arg. induction x as [a | b].
  * unshelve econstructor.
    - intros [y r]; destruct y as [a' | b']. exact (a'; r). inversion r.
    - unshelve eapply isequiv_adjointify.
      -- intros [a' r]. exact (inl a'; r).
      -- intros [y r]; destruct y as [a' | b'] => //=; inversion r.
      -- intros [a' r]. reflexivity.
  * unshelve econstructor.
  - intros [y r]; destruct y as [a' | b']. inversion r. exact (b'; r). 
  - unshelve eapply isequiv_adjointify.
    -- intros [b' r]. exact (inr b'; r).
    -- intros [y r]; destruct y as [a' | b' ]=> //=; inversion r.
    -- intros [b' r] => //=.
Defined.

Definition IsFun_somme {A A' B B' : Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type)
  (WFA : IsFun RA) (WFB : IsFun RB) : IsFun (FR_somme RA RB).
Proof.
  isFun @Equiv_somme_arg.
Defined.

Definition Somme_sym_sym {A A' B B': Type}
(RA : A -> A' -> Type) (RB : B -> B' -> Type) : 
forall {x y}, FR_somme RA RB x y ≃ sym (FR_somme (sym RA) (sym RB)) x y.
Proof.
  intros x y. unshelve econstructor.
  - revert y. induction x as [a | b]; intro y; destruct y as [a' | b']; cbn;
    intro r; try (exact r).
  - unshelve eapply isequiv_adjointify.
    -- revert y. induction x as [a | b]; intro y; destruct y as [a' | b']; cbn;
    intro r; try (exact r).
    -- revert y. induction x as [a | b]; intro y; destruct y as [a' | b']; cbn;
       try reflexivity.
    -- revert y. induction x as [a | b]; intro y; destruct y as [a' | b']; cbn;
    try reflexivity.
Defined.

Definition Somme_sym_sym_bis {A A' B B': Type}
  (RA : A -> A' -> Type) (RB : B -> B' -> Type) : 
  forall {x y}, FR_somme RA RB x y ≃ sym (FR_somme (sym RA) (sym RB)) x y.
Proof.
  intros x y. destruct x as [a | b], y as [a' | b']; cbn; try (apply Equiv_id).
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



(*** List A ⋈ List B ***)

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _. 

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Infix "::" := cons (at level 60, right associativity).


Fixpoint FR_list {A A'} (RA : A -> A' -> Type) (l: list A) (l': list A') : Type.
Proof.
  destruct l as [ |a l], l' as [ |a' l'].
  - exact True.
  - exact False.
  - exact False.
  - exact ({H : RA a a' & FR_list A A' RA l l'}).
Defined.

Definition code_list_arg {A A' : Type} (RA : A -> A' -> Type) (x: list A) : Type.
Proof.
  destruct x as [ |a l].
  exact (FR_list RA [] []).
  exact ({a':A' &{l':list A' & FR_list RA (a::l) (a'::l')}}).
Defined.

Definition Equiv_list_arg {A A' : Type} (RA : A -> A' -> Type) (x: list A) :
  Equiv ({y : list A' & FR_list RA x y}) (code_list_arg RA x).
Proof.
  destruct x; unfold code_list_arg.
  * unshelve econstructor.
    - intros [l r]; destruct l. exact r. inversion r.
    - unshelve eapply isequiv_adjointify.
      -- intro r. exact ([]; r).
      -- intros [l r]; destruct l; cbn. reflexivity. inversion r.
      -- cbn. reflexivity.
  * unshelve econstructor.
    - intros [l r]; destruct l. inversion r. exact (a0;(l;r)).
    - unshelve eapply isequiv_adjointify.
      -- intros [a' [l' r]]. exact (a'::l'; r).
      -- intros [l r]; destruct l; cbn. inversion r. reflexivity.
      -- intros [a' [l' r]]. reflexivity.
Defined.

Definition IsFun_list (A A' : Type) (RA : A -> A' -> Type)
           (WFA : IsFun RA) : IsFun (FR_list RA).
Proof.
  isFun @Equiv_list_arg.  
Defined.

Definition listR_sym_sym A A' (R : A -> A' -> Type) :
  forall l l', FR_list R l l' ≃ sym (FR_list (sym R)) l l'.
Proof.
  intros l l'. unshelve econstructor.
  - revert l'. induction l; intro l'; destruct l'; cbn; intro r; try exact r.
    exists r.1. apply IHl. exact r.2.
  - unshelve eapply isequiv_adjointify.
    -- revert l'. induction l; intro l'; destruct l'; cbn; intro r; try exact r.
       exists r.1. apply IHl. exact r.2.
    -- revert l'. induction l; intro l'; destruct l'; cbn; try reflexivity.
       intros [Xa X]. rewrite (IHl l' X). reflexivity.
    -- revert l'. induction l; intro l'; destruct l'; cbn; try reflexivity.
      + intros [Xa X]. rewrite (IHl l' X). reflexivity.
Defined.

Definition listR_sym_sym_bis A A' (R : A -> A' -> Type) :
  forall l l', FR_list R l l' ≃ sym (FR_list (sym R)) l l'.
Proof.
  intros l; induction l as [ |a l]; intro l'; induction l' as [ |a' l']; cbn; try (apply Equiv_id).
  unshelve econstructor.
  - intros [H X]. exists H. apply IHl. exact X.
  - unshelve eapply isequiv_adjointify.
    -- intros [H X]. exists H. apply IHl. exact X.
    -- intros [H X]; apply path_sigma_uncurried; unshelve econstructor; try reflexivity.
       cbn. apply e_sect.
       -- intros [H X]; apply path_sigma_uncurried; unshelve econstructor; try reflexivity.
       cbn. apply e_retr.
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



(*** tree A ⋈ tree A' ***)
Inductive tree A : Type :=
  |nil_tree : tree A
  |cons_tree : tree A -> A -> tree A -> tree A.

Arguments nil_tree {_}.
Arguments cons_tree {_} _ _ _.
  
Fixpoint FR_tree {A A' : Type} (RA : A -> A' -> Type) (t : tree A) (t' : tree A') : Type.
Proof.
  destruct t as [ | ls a rs], t' as [ | ls' a' rs' ].
  - exact True.
  - exact False.
  - exact False.
  - exact ({Xl : FR_tree A A' RA ls ls' & {Xa : RA a a' & FR_tree A A' RA rs rs'}}).
Defined.

Definition code_tree_arg {A A' : Type} (RA : A -> A' -> Type) (t : tree A) : Type.
Proof.
  destruct t as [ | ls a rs].
  - exact (FR_tree RA nil_tree nil_tree).
  - exact ({ls' : tree A' & {a' :A' & {rs' : tree A' & FR_tree RA (cons_tree ls a rs) (cons_tree ls' a' rs') }}}).
Defined.

Definition Equiv_tree_arg {A A' : Type} (RA : A -> A' -> Type) (t : tree A) : 
      Equiv ({t' : tree A' & FR_tree RA t t'}) (code_tree_arg RA t).
Proof.
  destruct t as [ | ls a rs]; cbn.
  * unshelve econstructor.
    - intros [t' r]. destruct t' as [ | ls' a' rs'].
      exact I. destruct r.
    - unshelve eapply isequiv_adjointify.
      -- exists nil_tree. exact H.
      -- intros [t' r]. destruct t' as [ | ls' a' rs']; cbn in r; destruct r. 
         reflexivity.
      -- cbn. intro x; destruct x. reflexivity.
  * unshelve econstructor.
  - intros [t' r]. destruct t' as [ | ls' a' rs'].
    destruct r. exists ls', a', rs'. exact r.
  - unshelve eapply isequiv_adjointify.
    -- intros [ls' [a' [rs' r]]]. exists (cons_tree ls' a' rs'). exact r.
    -- intros [t' r]. destruct t' as [ | ls' a' rs']; cbn in r.
        destruct r. reflexivity.
    -- intros [ls' [a' [rs' r]]]. reflexivity.
Defined.

(* Pbl IsContr_telecop limité à 2 *)
Definition IsFun_tree {A A' : Type} (RA : A -> A' -> Type) (WFA : IsFun RA): IsFun(FR_tree RA).
Proof.
  intro t. induction t;
  eapply contr_equiv2; try (eapply Equiv_inverse; apply Equiv_tree_arg).
  - apply IsContr_True.
  - cbn.
    eapply contr_equiv2. apply Equiv_inverse; eapply EquivSigma; intro ls'. apply SigmaSigma.
    cbn.
    (* utilisation telescope *)
    apply (IsContr_telescope IHt1). intros ls' Xs.
    (* décurry *)
    eapply (@contr_equiv2 ({a':A' & {rs' : tree A' & {XA : RA a a' & FR_tree RA t2 rs' }}})). 
    apply (@SigmaSigma _ _ (fun a' rs' => {_ : RA a a' & FR_tree RA t2 rs'})).
    (* next *)
    apply ((IsContr_telescope) (WFA a) (fun a' XA => IHt2)).
Defined.

Definition Tree_sym_sym A A' (RA : A -> A' -> Type) :
  forall t t', FR_tree RA t t' ≃ sym (FR_tree (sym RA)) t t'.
Proof.
  intros t t'. unshelve econstructor.
  - revert t'. induction t; intro t'; destruct t'; cbn; intro r; try exact r.
    destruct r as [Xs [Xa Xr]].
      unshelve econstructor. apply IHt1; exact Xs.
      unshelve econstructor. exact Xa.
      apply IHt2; exact Xr.
  - unshelve eapply isequiv_adjointify.
    -- revert t'. induction t; intro t'; destruct t'; cbn; intro r; try exact r.
       destruct r as [Xs [Xa Xr]].
       unshelve econstructor. apply IHt1; exact Xs.
       unshelve econstructor. exact Xa.
       apply IHt2; exact Xr.
    -- revert t'. induction t; intro t'; destruct t'; cbn; intro r; try reflexivity.
       destruct r as [Xs [Xa Xr]]. rewrite (IHt1 t'1 Xs). rewrite (IHt2 t'2 Xr). reflexivity. 
    -- revert t'. induction t; intro t'; destruct t'; cbn; intro r; try reflexivity.
       destruct r as [Xs [Xa Xr]]. rewrite (IHt1 t'1 Xs). rewrite (IHt2 t'2 Xr). reflexivity. 
Defined.

Definition Tree_sym_sym_bis A A' (RA : A -> A' -> Type) :
  forall t t', FR_tree RA t t' ≃ sym (FR_tree (sym RA)) t t'.
Proof.
  intro t; induction t; intro t'; destruct t'; cbn; try (apply Equiv_id).
  unshelve econstructor.
  - intros [Xs [Xa Xr]]. 
    unshelve econstructor. apply IHt1; exact Xs.
    unshelve econstructor. exact Xa.
    apply IHt2; exact Xr.
  - unshelve eapply isequiv_adjointify.
    -- intros [Xs [Xa Xr]]. 
       unshelve econstructor. apply IHt1; exact Xs.
       unshelve econstructor. exact Xa.
       apply IHt2; exact Xr.
    -- intros [Xs [Xa Xr]]. cbn. rewrite e_sect. rewrite e_sect. reflexivity.
    -- intros [Xs [Xa Xr]]. cbn. rewrite e_retr. rewrite e_retr. reflexivity.
Defined.

Definition FP_tree {A A':Type} (eA : A ⋈ A') : tree A ⋈ tree A'.
Proof.
  unshelve econstructor.
  exact (FR_tree (_R eA)).
  unshelve econstructor.
  * unfold rel. apply IsFun_tree. typeclasses eauto.
  * eapply IsFun_sym. apply Tree_sym_sym. apply IsFun_tree.
    destruct eA as [RA [WFA WFAsym]]. exact WFAsym.
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

Fixpoint FR_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      (RA : A -> A' -> Type)
      (RB : forall (a:A) (a':A') (H:RA a a'), B a -> B' a' -> Type)
      (x : {a: A & B a}) (y:{a':A' & B' a'}) : Type.
Proof.
  destruct x as [a b], y as [a' b'].
  exact ({H: RA a a' & RB a a' H b b'}).
Defined.

Definition code_sigma_arg {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A -> A' -> Type)
      (RB : forall (a:A) (a':A') (H:RA a a'), B a -> B' a' -> Type)
      (x: {a:A & B a}) : Type.
Proof.
  destruct x as [a b].
  exact ({a' : A' & {b' : B' a' & FR_sigma RA RB (a;b) (a';b')}}).
Defined.

Definition Equiv_sigma_arg {A A':Type} {B : A -> Type} {B' : A' -> Type}
  (RA : A -> A' -> Type) (RB : forall (a:A) (a':A') (H:RA a a'), B a -> B' a' -> Type)
  (x: {a:A & B a}) : 
  Equiv ({y:{a':A' & B' a'} & FR_sigma RA RB x y}) (code_sigma_arg RA RB x).
Proof.
  destruct x as [a b]. unshelve econstructor.
  - intros [y r]. destruct y as [a' b']; cbn.
    exists a'. exists b'. exact r.
  - unshelve eapply isequiv_adjointify.
    -- intros [a' [b' r]]. exact ((a';b'); r).
    -- intros [y r]; destruct y; cbn. try reflexivity.
    -- intros [a' [b' r]]; cbn. try reflexivity.
Defined.

Definition IsFun_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      {RA : A -> A' -> Type} 
      {RB : forall a a' (H:RA a a'), Rel (B a) (B' a')} 
      (WFA : IsFun RA)
      (WFB : forall a a' (H: RA a a'), IsFun(RB a a' H)) :
      IsFun (FR_sigma RA RB).
Proof.
  isFun @Equiv_sigma_arg.
Defined.

Definition Sigma_sym_sym {A A'} {P : A -> Type} {P' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (H:RA a a'), Rel (P a) (P' a')} :
  forall z w, (FR_sigma RA RB z w) ≃ sym (FR_sigma (sym RA) (fun x y e => sym (RB y x e))) z w.
Proof.
  intros z w. unshelve econstructor.
  - revert w; induction z as [a b]; intro w; destruct w as [a' b']; cbn.
    intros [H X]. exists H. exact X.
  - unshelve eapply isequiv_adjointify.
    -- revert w; induction z as [a b]; intro w; destruct w as [a' b']; cbn.
    intros [H X]. exists H. exact X.
    -- revert w; induction z as [a b]; intro w; destruct w as [a' b']; cbn.
       intros [H X]. reflexivity.
    -- revert w; induction z as [a b]; intro w; destruct w as [a' b']; cbn.
       intros [H X]. reflexivity.
Defined.

Definition Sigma_sym_sym_bis {A A'} {P : A -> Type} {P' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (H:RA a a'), Rel (P a) (P' a')} :
  forall z w, (FR_sigma RA RB z w) ≃ sym (FR_sigma (sym RA) (fun x y e => sym (RB y x e))) z w.
Proof.
  intros z w. destruct z as [a b], w as [a' b']. cbn.
  unshelve econstructor.
  - intros [H X]. exists H. exact X.
  - unshelve eapply isequiv_adjointify.
    -- intros [H X]. exists H. exact X.
    -- intros [H X]; reflexivity.
    -- intros [H X]; reflexivity.
Defined.

Definition FP_sigma (A A' : Type) (B : A -> Type) (B' : A' -> Type) 
    (eA : A ⋈ A')
    (eB : forall (a:A) (a':A') (H: (_R eA) a a'), B a ⋈ B' a') :
  {a:A & B a} ⋈ {a':A' & B' a'}.
Proof.
  destruct eA as [RA FA]. destruct FA as [WFA WFAsym].
  unshelve econstructor. unfold Rel.
  * eapply (FR_sigma RA).
    intros a a' H b b'. exact (_R (eB a a' H) b b'). 
  * split.
    + apply IsFun_sigma. exact WFA.
      intros a a' H. destruct (eB a a' H) as [RB FB]. destruct FB as [WFB WFBsym].
      exact WFB.
    + eapply IsFun_sym. eapply Sigma_sym_sym. apply IsFun_sigma.
      - exact WFAsym.
      - intros a' a H. destruct (eB a a' H) as [RB FB].
      destruct FB as [WFB WFBsym]. exact WFBsym.
Defined.