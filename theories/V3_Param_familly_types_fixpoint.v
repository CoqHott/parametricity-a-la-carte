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

(*** indexed list ***)

Inductive indexed_list {A:Type} (B:Type) : A -> Type :=
  |nil_ind_list : forall a:A, indexed_list B a 
  |cons_ind_list : forall a:A, B -> indexed_list B a -> indexed_list B a.

Arguments nil_ind_list {_ _ _}.
Arguments cons_ind_list {_ _ _} _ _.
  
Notation "[* *]" := (nil_ind_list).
Infix "**" := cons_ind_list (at level 60, right associativity).

Fixpoint FR_indexed_list {A A' B B' : Type} 
                         (RA : A -> A' -> Type)
                         (a:A) (a':A') (Xa : RA a a')
                         (RB : B -> B' -> Type) 
                         (li : indexed_list B a)
                         (li' : indexed_list B' a') : Type.
Proof.
  destruct li, li'.
  - exact True.
  - exact False.
  - exact False.
  - exact ({Xb : RB b b0 & FR_indexed_list A A' B B' RA a a0 Xa RB li li'}).
Defined.

Definition code_indexed_list_arg {A A' B B' : Type} 
                         (RA : A -> A' -> Type)
                         (a:A) (a':A') (Xa : RA a a')
                         (RB : B -> B' -> Type) 
                         (li : indexed_list B a) :
                         Type.
Proof.
  destruct li.
  - exact (FR_indexed_list RA a a' Xa RB ([* *]) ([* *])).
  - exact ({b' : B' & {li' : indexed_list B' a' & FR_indexed_list RA a a' Xa RB (b**li) (b'**li')}}).
Defined.

Definition Equiv_indexed_list_arg {A A' B B' : Type} 
                          (RA : A -> A' -> Type)
                          (a:A) (a':A') (Xa : RA a a')
                          (RB : B -> B' -> Type) 
                          (li : indexed_list B a) :
          Equiv ({li' : indexed_list B' a' & FR_indexed_list RA a a' Xa RB li li'}) (code_indexed_list_arg RA a a' Xa RB li).
Proof.
  destruct li; unfold code_indexed_list_arg.
  * unshelve econstructor.
    - intros [li' r]. destruct li'; try destruct r; try reflexivity.
    - unshelve eapply isequiv_adjointify.
      -- intros r. exists [* *]. exact r.
      -- intros [li' r]. destruct li'; try destruct r; try reflexivity.
      -- intros r; destruct r; reflexivity.
  * unshelve econstructor.
    - intros [li' r]. destruct li'; try destruct r.
      exists b0, li', x. exact f.
    - unshelve eapply isequiv_adjointify.
      -- intros [b' [li' r]]. exists (b'**li'). exact r. 
      -- intros [li' r]. destruct li'; try destruct r; try reflexivity.
      -- intros [b' [li' r]]. destruct r; reflexivity.
Defined.


Definition IsFun_indexed_list {A A' B B' : Type} 
                         (RA : A -> A' -> Type)
                         (a:A) (a':A') (Xa : RA a a')
                         (RB : B -> B' -> Type) 
                         (WFB : IsFun RB) :
                         IsFun(FR_indexed_list RA a a' Xa RB).
Proof.
  intros li. induction li;
  eapply contr_equiv2; try (eapply Equiv_inverse; apply Equiv_indexed_list_arg).
  * apply IsContr_True.
  * cbn. apply (IsContr_telescope (WFB b) (fun b' Xb => IHli Xa)).
Defined.

Definition Indexed_list_sym_sym {A A' B B' : Type} 
        (RA : A -> A' -> Type)
        (a:A) (a':A') (Xa : RA a a')
        (RB : B -> B' -> Type) 
        (WFB : IsFun RB) :
  forall li li', Equiv (FR_indexed_list RA a a' Xa RB li li')
                       (sym (FR_indexed_list RA a a' Xa (sym RB)) li li').









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
         (n m : nat) (Xn : Rnat n m) (v : vect A n) (v' : vect A' m)
         : Type.
Proof.
  destruct v, v'.
  - exact True.
  - destruct Xn.
  - destruct Xn.
  - exact ({_ : RA a a0 & FR_vect A A' RA n n0 Xn v v'}).
Defined.

Definition code_vect_arg {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : Rnat n m) (v:vect A n) : Type.
Proof.
  destruct v.
  - destruct m.
    + exact (FR_vect RA 0 0 Xn [||] [||]).
    + destruct Xn. 
  - destruct m.
    + destruct Xn.
    + exact ({a':A' & {v':vect A' m &
              FR_vect RA (S n) (S m) Xn (a □ v) (a' □ v')}}).
Defined.

Definition Equiv_vect_arg {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : Rnat n m) (v:vect A n) :
  Equiv ({v' : vect A' m & FR_vect RA n m Xn v v'})
        (code_vect_arg RA n m Xn v).  
Proof.
  destruct v.
  * unshelve econstructor.
    - intros [v' r]; destruct v'; cbn; try destruct Xn. 
      exact r.
    - unshelve eapply isequiv_adjointify.
      -- intro r. destruct m; try destruct Xn. 
         exists [||]. exact r.
      -- intros [v' r]; destruct v'; try destruct Xn; try reflexivity. 
      -- intro r. destruct m; try destruct Xn; try reflexivity.
  * unshelve econstructor.
    - intros [v' r ]; destruct v'; try destruct Xn; cbn.
      exists a0, v'. exact r.
    - unshelve eapply isequiv_adjointify.
      -- destruct m; try destruct Xn. 
         intros [a' [v' r]]. exists (a' □ v'). exact r.
      -- intros [v' r]; destruct v'; try destruct Xn; try reflexivity.
      -- destruct m; try destruct Xn. intros [a' [v' r]]. reflexivity.
Defined.

Definition IsFun_vect {A A':Type} (RA : A -> A' -> Type) (WFA : IsFun(RA)) :
  forall n m Xn, IsFun (FR_vect RA n m Xn).
Proof.
  intros n m Xn v. revert m Xn; induction v; intros m Xn;
  eapply contr_equiv2; try (eapply Equiv_inverse; apply Equiv_vect_arg).
  - destruct m; try destruct Xn; try apply IsContr_True.
  - destruct m; try destruct Xn.
    apply (IsContr_telescope (WFA a) (fun a' XA => IHv _ _ )). 
Defined.

Definition Rnat_sym {n m} (Xn: Rnat n m) : Rnat m n.
Proof.
  revert m Xn. induction n; intro m; destruct m; intro Xn; try destruct Xn; cbn. 
  - exact I.
  - exact (IHn _ Xn).
Defined. 

Definition vectR_sym_sym A A' (RA : A -> A' -> Type)
  (n m : nat) (Xn : Rnat n m) :
  forall v v', FR_vect RA m n (Rnat_sym Xn) v v' ≃ sym (FR_vect (sym RA) n m Xn) v v'.
Proof.
  intros v v'. unshelve econstructor.
  - revert n Xn v'. induction v; intros; destruct v'; try destruct Xn.
    + exact X.
    + cbn. destruct X as [Xa Xv]. exists Xa.
      apply IHv. exact Xv.
  - unshelve eapply isequiv_adjointify.
    -- revert n Xn v'. induction v; intro ; destruct v'; try destruct Xn.
      + intro r; exact r. 
      + intros [Xa Xv]. exists Xa. apply IHv. exact Xv.
    -- revert n Xn v'. induction v; intro ; destruct v'; cbn; try destruct Xn.
      + reflexivity.
      + intros [Xa X]. rewrite IHv. reflexivity.
    -- revert n Xn v'. induction v; intro ; destruct v'; cbn; try destruct Xn.
      + reflexivity.
      + intros [Xa X]. rewrite IHv. reflexivity.
Defined.

Definition vectR_sym_sym_bis A A' (RA : A -> A' -> Type)
      (n m : nat) (Xn : Rnat n m) :
      forall v v', Equiv (FR_vect RA n m Xn v v')
                         (sym (FR_vect (sym RA) m n (Rnat_sym Xn)) v v').
Proof.
  intro v. revert Xn. revert m. 
  induction v; intros m Xn v'; induction v'; try destruct Xn; try apply Equiv_id.
  unshelve econstructor.
  - intros [Xa r]. exists Xa. eapply IHv. exact r.
  - unshelve eapply isequiv_adjointify.
    -- intros [Xa r]. exists Xa. eapply IHv. exact r.
    -- intros [Xa r]. apply path_sigma_uncurried; unshelve econstructor; cbn; try reflexivity; cbn.
       apply e_sect.
       -- intros [Xa r]. apply path_sigma_uncurried; unshelve econstructor; cbn; try reflexivity; cbn.
          apply e_retr.
Defined.

Definition FP_vect (A A' : Type) (eA : A ⋈ A')
  (n m : nat) (Xn : Rnat n m) :
  vect A n ⋈ vect A' m.
Proof.
  unshelve econstructor. exact (FR_vect (_R eA) n m Xn).
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

(* Version explicite avec des transports *)
Definition FR_eq {A A' : Type } (RA : A -> A' -> Type)
          (x:A) (x':A') (Xx : RA x x')
          (y:A) (y':A') (Xy: RA y y') :
    forall (p : x = y) (q : x' = y'), Type. 
    intros p q. 
    exact (transport_eq (fun x => RA x y') p (transport_eq (fun x' => RA x x') q Xx) = Xy).
Defined. 

(* code_eq_arg était inutile, juste une simplification 
   avec refl ce qui désormais automatique *)

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
  intros p q. destruct p, q; try apply Equiv_id.
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





  

