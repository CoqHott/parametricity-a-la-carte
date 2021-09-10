Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
Require Import V3_Param_CComega_fixpoint.
Require Import V3_Param_ind_fixpoint.
From Coq Require Import ssreflect.

Set Universe Polymorphism.



(* ###########################################################*)
(* ###    WORK IN PROGRESS : Inductives types families     ###*)
(* ###########################################################*)

(*** Vect A n ⋈ Vect A' n ***)
Inductive vect (A:Type) : nat -> Type :=
  |nil_vect : vect A 0
  |cons_vect : forall n:nat, A -> vect A n -> vect A (S n).

Arguments nil_vect {_}.
Arguments cons_vect {_ _} _ _.

Notation "[| |]" := nil_vect (format "[| |]").
Notation "[| x |]" := (cons_vect x nil_vect).

Infix "□" := cons_vect (at level 60, right associativity).

Fixpoint Rnat (n m : nat) : Type :=
  match n , m with
    | 0 , 0 => True
    | S n , S m => Rnat n m
    | _ , _ => False
  end.

Fixpoint FR_vect {A A':Type} (RA : A -> A' -> Type) 
         (n m : nat) (p : Rnat n m) (v : vect A n) (v' : vect A' m)
         : Type.
  destruct v, v'.
  - exact True.
  - destruct p.
  - destruct p.
  - exact ({_ : RA a a0 & FR_vect A A' RA n n0 p v v'}).
Defined.

Definition code_vect_arg {A A' : Type} (RA : A -> A' -> Type) (n:nat) (m:nat) (p : Rnat n m) (v:vect A n) : Type.
Proof.
  destruct v.
  - destruct m.
    + exact (FR_vect RA 0 0 p [||] [||]).
    + destruct p. 
  - destruct m.
    + destruct p.
    + exact ({a':A' & {v':vect A' m &
              FR_vect RA (S n) (S m) p (a □ v) (a' □ v')}}).
Defined.

Definition Equiv_vect_arg {A A' : Type} (RA : A -> A' -> Type) (n:nat) (m:nat) (p : Rnat n m) (v:vect A n) :
  Equiv ({v' : vect A' m & FR_vect RA n m p v v'})
        (code_vect_arg RA n m p v).  
Proof.
  destruct v.
  * unshelve econstructor.
    - intros [v' r]; destruct v'.
      1 : exact r. all : destruct p. 
    - unshelve eapply isequiv_adjointify.
      -- intro r. destruct m. 
         1:{exists [||]. exact r. } all: destruct p. 
      -- intros [v' r]; destruct v'.
          1 : reflexivity. all :destruct p. 
      -- intro r. destruct m. 
         1 : reflexivity. all : destruct p.     
  * unshelve econstructor.
    - intros [v' r ]; destruct v'. 
      2 : {cbn in *. exists a0. exists v'. exact r. }
      all : destruct p.
    - unshelve eapply isequiv_adjointify.
      -- destruct m. 
         2 : {intros [a' [v' r]]. exists (a' □ v'). exact r. }
         all : destruct p.
      -- intros [v' r]; destruct v'; cbn.
         2 : reflexivity. all : destruct p.
      -- destruct m.
         2 : intros [a' [v' r]]; reflexivity. all : destruct p.
Defined.

Definition IsFun_vect {A A':Type} (RA : A -> A' -> Type) (WFA : IsFun(RA)) :
  forall n m p, IsFun (FR_vect RA n m p).
Proof.
  intros n m p v. revert m p; induction v; intros m p;
  eapply contr_equiv2; try (eapply Equiv_inverse; apply Equiv_vect_arg).
  - destruct m; cbn.
    + apply IsContr_True.
    + destruct p.
  - destruct m; cbn.
    + destruct p.
    + apply (IsContr_telescope (WFA a) (fun a' XA => IHv _ _ )). 
Defined.

Definition Rnat_sym {n m} (e: Rnat n m) : Rnat m n.
Proof.
  revert m e. induction n; destruct m; intro e. 
  - exact e.
  - destruct e. 
  - destruct e. 
  - exact (IHn _ e).
Defined. 

Definition vectR_sym_sym A A' (RA : A -> A' -> Type)
  (n m : nat) (p : Rnat n m) :
  forall v v', FR_vect RA m n (Rnat_sym p) v v' ≃ sym (FR_vect (sym RA) n m p) v v'.
Proof.
  intros v v'. unshelve econstructor.
  - revert n p v'. induction v; intros; destruct v'.
    + exact X.
    + destruct p.
    + destruct p.
    + cbn in *. destruct X as [Xa X]. exists Xa.
      apply (IHv n0 p v' X).
  - unshelve eapply isequiv_adjointify.
    + revert n p v'. induction v; intro ; destruct v'; cbn.
      * intro r; exact r. 
      * destruct p.
      * destruct p.
      * intros [Xa X]. exists Xa. apply (IHv n0 p v' X).
    + revert n p v'. induction v; intro ; destruct v'; cbn; try solve [destruct p].
      * reflexivity.
      * intros [Xa X]. rewrite (IHv n0 p v' X). reflexivity.
    + revert n p v'. induction v; intro ; destruct v'; cbn; try solve [destruct p].
      * reflexivity.
      * intros [Xa X]. rewrite (IHv n0 p v' X). reflexivity.
Defined.

(* visiblement cela passe aussi bien aux vect aussi
   Je ne saurais pas juger de si c'est mieux,
   de toute façon, il me semble que c'est un détail. *)
Definition vectR_sym_sym_bis A A' (RA : A -> A' -> Type)
      (n m : nat) (p : Rnat n m) :
      forall v v', FR_vect RA n m p v v' ≃ sym (FR_vect (sym RA) m n (Rnat_sym p)) v v'.
Proof.
  intro v. revert p. revert m. 
  induction v; intros m p v'; induction v'; cbn.
  * apply Equiv_id.
  * destruct p.
  * destruct p.
  * unshelve econstructor.
    - intros [H r]. exists H. eapply IHv. exact r.
    - unshelve eapply isequiv_adjointify.
      -- intros [H r]. exists H. eapply IHv. exact r.
      -- intros [H r]. apply path_sigma_uncurried; unshelve econstructor.
        cbn. reflexivity. cbn. apply e_sect.
      -- intros [H r]. apply path_sigma_uncurried; unshelve econstructor.
        cbn. reflexivity. cbn. apply e_retr.
Defined.

Definition FP_vect (A A' : Type) (eA : A ⋈ A')
  (n m : nat) (p : Rnat n m) :
  vect A n ⋈ vect A' m.
Proof.
  unshelve econstructor. exact (FR_vect (_R eA) n m p).
  split.
  apply IsFun_vect; typeclasses eauto.
  unfold rel. 
  eapply IsFun_sym. eapply vectR_sym_sym. apply IsFun_vect.
  destruct eA as [RA FA]. destruct FA as [WFA WFAsym].
  exact WFAsym.
Defined.


(* ########################################################### *)
(* ###     WORK IN PROGRESS : x = y ⋈ x' = y'             ### *)
(* ########################################################### *)

(*
Inductive eq@{i} (A:Type@{i}) (x:A) : A -> Type@{i} :=
    eq_refl : eq A x x.

Notation "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Arguments eq_refl {_ _}. *)

(* Version contracté *)
Definition FR_eq {A A' : Type } (RA : A -> A' -> Type)
          (x:A) (x':A') (Xx : RA x x')
          (y:A) (y':A') (Xy: RA y y') :
    forall (p : x = y) (q : x' = y'), Type. 
    intros p q. 
    exact (transport_eq (fun x => RA x y') p (transport_eq (fun x' => RA x x') q Xx) = Xy).
Defined. 

Definition IsFun_eq {A A' : Type } (RA : A -> A' -> Type) (WFA : IsFun(RA))
          (x:A) (x':A') (Xx : RA x x')
          (y:A) (y':A') (Xy: RA y y') :
          IsFun (FR_eq RA x x' Xx y y' Xy).
Proof.
  intro p; destruct p; unfold FR_eq; cbn.
  apply (contr_equiv2 ((x'; Xx) = (y'; Xy))).
  apply (@EqSigma (A') (fun z => RA x z) (x';Xx) (y';Xy)).
  apply contr_paths_contr. exact (WFA x).
Defined.

Definition Eq_sym_sym {A A':Type} (RA : A -> A' -> Type)
                      (x:A) (x':A') (Xx : RA x x')
                      (y:A) (y':A') (Xy: RA y y') :
    forall p q, Equiv (FR_eq RA x x' Xx y y' Xy p q) (sym (FR_eq (sym RA) x' x Xx y' y Xy) p q).
Proof.
  intros p q. destruct p, q. cbn. apply Equiv_id.
Defined.

Definition FP_eq (A A' : Type) (eA : A ⋈ A') 
    (x:A) (x':A') (Xx : _R eA x x')
    (y:A) (y':A') (Xy : _R eA y y') :
    eq A x y ⋈ eq A' x' y'.
Proof.
  unshelve econstructor. exact (FR_eq (_R eA) x x' Xx y y' Xy).
  unshelve econstructor.
  * apply IsFun_eq. typeclasses eauto.
  * unfold rel. eapply IsFun_sym. apply Eq_sym_sym. apply IsFun_eq.
    destruct eA as [RA FA]. destruct FA as [WFA WFAsym]. exact WFAsym.
Defined.




(* ########################################################### *)
(* ###     WORK IN PROGRESS : degenerated familly type     ### *)
(* ########################################################### *)

Inductive dft (A:Type) : Type -> Type :=
  |triv : dft A A.

Definition FR_dft (A A':Type) (RA : A -> A' -> Type)
                  (B B':Type) (RB : B -> B' -> Type) : 
                  dft A B -> dft A' B' -> Type.
Proof.
  intros x y. destruct x, y.
  exact (RA = RB).
Defined.

Definition IsFun_dft (A A':Type) (RA : A -> A' -> Type)
                     (B B':Type) (RB : B -> B' -> Type) : 
                      IsFun(FR_dft A A' RA B B' RB).
Proof.
  intro x; destruct x.
  admit.
Admitted.

Definition funext_double (A A':Type) (f g : A -> A' -> Type) : 
                         Equiv (f = g) (forall a b, f a b = g a b).
Proof.
  eapply (@equiv_compose _ (f == g)). 
  apply Equiv_inverse; apply Fune. 
  apply EquivPtype ; intro a. apply Equiv_inverse; apply Fune.
Defined.

Definition Dft_sym_sym (A A':Type) (RA : A -> A' -> Type)
                     (B B':Type) (RB : B -> B' -> Type) : 
  forall x y, Equiv (FR_dft A A' RA B B' RB x y) (sym (FR_dft A' A (sym RA) B' B (sym RB)) x y).
Proof.
  intros x y; destruct x, y; cbn. 
  eapply equiv_compose. apply funext_double.
  apply Equiv_inverse. eapply equiv_compose. apply funext_double.
  unshelve econstructor.
  - intro r. intros a a'. apply r.
  - unshelve eapply isequiv_adjointify.
    -- intro r. intros a' a. apply r.
    -- intro r. cbn. 
       apply funext; intro a'; apply funext; intro a. reflexivity.
       -- intro r. cbn. 
       apply funext; intro a; apply funext; intro a'. reflexivity.
Defined.




  

