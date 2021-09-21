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
                         (RB : B -> B' -> Type) 
                         (a:A) (a':A') (li : indexed_list B a)
  : forall (li' : indexed_list B' a') (Xa : RA a a') , Type :=
  fun li' => match li , li' with
  | [* *] , [* *] => fun Xa => True
  | [* *] , b' ** l' =>  fun Xa => False
  | b ** l , [* *]  => fun Xa => False
  | b ** l , b' ** l' =>
    fun Xa => {Xb : RB b b' & FR_indexed_list RA RB _ _ l l' Xa}
  end.

Definition code_indexed_list_arg {A A' B B' : Type} 
           (RA : A -> A' -> Type)
           (RB : B -> B' -> Type)
           (a:A) (li : indexed_list B a) :
  forall (a':A') (Xa : RA a a'), Type :=
  match li with
   [* *] => fun a' Xa => FR_indexed_list RA RB _ a' ([* *]) ([* *]) Xa
  | b ** l => fun a' Xa => {b' : B' &
                    {l' : indexed_list B' a' &
                          FR_indexed_list RA RB _ a' (b ** l) (b'**l') Xa}}
  end.
   
Definition Equiv_indexed_list_arg {A A' B B' : Type} 
                          (RA : A -> A' -> Type)
                          (a:A) (a':A') (Xa : RA a a')
                          (RB : B -> B' -> Type) 
                          (li : indexed_list B a) :
          Equiv ({li' : indexed_list B' a' & FR_indexed_list RA RB a a' li li' Xa}) (code_indexed_list_arg RA RB a li a' Xa).
Proof.
  destruct li; unfold code_indexed_list_arg.
  * unshelve econstructor.
    - intros [li' r]. destruct li'; try destruct r; try reflexivity.
    - unshelve eapply isequiv_adjointify.
      -- intros r. exists [* *]. exact r.
      -- intros [li' r]. destruct li'; try destruct r; try reflexivity.
      -- intros r; destruct r; reflexivity.
  * unshelve econstructor. cbn.
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
  IsFun (fun l l' => FR_indexed_list RA RB a a' l l' Xa).
Proof.
  intro l; induction l; isFun @Equiv_indexed_list_arg.
Defined.


Fixpoint Indexed_list_sym_sym {A A' B B' : Type} 
        (RA : A -> A' -> Type)
        (a:A) (a':A') 
        (RB : B -> B' -> Type) 
        (WFB : IsFun RB) li :
  forall li' (Xa : RA a a') , FR_indexed_list RA RB a a' li li' Xa ≃
                                              (sym (fun l l' => FR_indexed_list (sym RA) (sym RB) a' a l l' Xa)) li li' :=
  fun li' =>
    match li , li' with
      [* *] , [* *] => fun _ => Equiv_id True
    | [* *] , b' ** l' => fun _ => Equiv_id False
    | b ** l , [* *] => fun _ => Equiv_id False
    | b ** l , b' ** l' =>
      fun Xa => EquivSigma (fun r => Indexed_list_sym_sym RA _ _ RB WFB  l l' Xa)
    end.

Definition FP_indexed_list (A A' B B' : Type) 
           (eA : A ⋈ A')
           (a:A) (a':A') (Xa : _R eA a a')
           (eB : B ⋈ B') : indexed_list B a ⋈ indexed_list B' a'.
Proof.
  unshelve econstructor.
  - exact (fun l l' => FR_indexed_list (_R eA) (_R eB) a a' l l' Xa).
  - split.
    + apply IsFun_indexed_list; typeclasses eauto.
    + eapply IsFun_sym. refine (fun l l' => Indexed_list_sym_sym _ _ _ _ _ _ _ _).
      apply IsFun_indexed_list ; typeclasses eauto .
Defined.


(*** Vect A n ⋈ Vect A' n ***)
Inductive vect (A:Type) : nat -> Type :=
  |nil_vect : vect A 0
  |cons_vect : forall n:nat, A -> vect A n -> vect A (S n).

Arguments nil_vect {_}.
Arguments cons_vect {_ _} _ _.

Notation "[| |]" := nil_vect (format "[| |]").
Notation "[| x |]" := (cons_vect x nil_vect).

Infix "□" := cons_vect (at level 60, right associativity).


(* Inductive Rnat : forall (n m : nat), Type := *)
(*   Rnat0 : Rnat 0 0 *)
(* | RnatS : forall n m, Rnat n m -> Rnat (S m) (S n). *)

Fixpoint FR_vect {A A':Type} (RA : A -> A' -> Type) 
         (n m : nat) (v : vect A n)
  : forall  (v' : vect A' m) (Xn : FR_nat n m) , Type :=
  fun v' => match v , v' with
  | [| |] , [| |] => fun Xn => True
  | [| |] , a' □ v' => fun Xn => False
  | a □ v , [| |] => fun Xn => False
  | a □ v , a' □ v' => fun Xn =>
                         {_ : RA a a' & FR_vect RA _ _  v v' Xn}
  end.

Definition liftnil {A n} : forall (e : FR_nat 0 n), vect A n :=
  match n with
  | 0 => fun _ => [| |]
  | S n => fun e => match e with end
  end.

Definition code_vect_arg {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (v:vect A n) : forall (m:nat) , FR_nat n m -> Type
  :=
    match v with
      [| |] => fun m Xn => FR_vect RA 0 m [||] (liftnil Xn) Xn
    | a □ v =>
      fun m =>
        match m with
        | 0 => fun _ => False
        | S m => fun Xn =>
                   {a':A' & {v':vect A' m &
                                FR_vect RA (S _) (S m) (a □ v) (a' □ v') Xn}}
        end
    end.

Definition Equiv_vect_arg {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : FR_nat n m) (v:vect A n) :
  Equiv ({v' : vect A' m & FR_vect RA n m v v' Xn})
        (code_vect_arg RA n v m Xn).  
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
      exists a0, v'. cbn in * . exact r.
    - unshelve eapply isequiv_adjointify.
      -- destruct m; try destruct Xn. 
         intros [a' [v' r]]. exists (a' □ v'). exact r.
      -- intros [v' r]; destruct v'; try destruct Xn; try reflexivity.
      -- destruct m; try destruct Xn. intros [a' [v' r]]. reflexivity.
Defined.

Definition IsFun_vect {A A':Type} (RA : A -> A' -> Type) (WFA : IsFun(RA)) :
  forall n m Xn, IsFun (fun v v' => FR_vect RA n m v v' Xn).
Proof.
  intros n m Xn v. revert m Xn. induction v; intros m Xn;
  eapply contr_equiv2; try (eapply Equiv_inverse; apply Equiv_vect_arg).
  - destruct m; try destruct Xn. apply IsContr_True.
  - destruct m; try destruct Xn.
    apply (IsContr_telescope2 (WFA a) (fun a' _ => IHv _ Xn)). 
Defined.

Fixpoint  vectR_sym_sym {A A'} (RA : A -> A' -> Type)
  (n : nat) v :
  forall m v' (Xn : FR_nat m n), FR_vect RA n m v v' (Nat_sym_sym _ _ Xn) ≃
               sym (fun v v' => FR_vect (sym RA) m n v v' Xn) v v' :=
  fun m v' =>
    match v , v' with
      [| |] , [| |] => fun _ => Equiv_id True 
    | [| |] , cons_vect a' l' => fun _ => Equiv_id False
    | cons_vect a l , [| |] => fun _ => Equiv_id False
    | cons_vect a l , cons_vect a' l' => fun Xn => EquivSigma (fun r => vectR_sym_sym RA _ l _ l' Xn)
    end.

Definition FP_vect (A A' : Type) (eA : A ⋈ A')
  (n m : nat) (Xn : FR_nat n m) :
  vect A n ⋈ vect A' m.
Proof.
  unshelve econstructor.
  - refine (fun v v' => FR_vect (_R eA) _ _ v v' Xn).
  - split.
    + apply IsFun_vect; typeclasses eauto.
    + eapply IsFun_sym; [ eapply (fun v v' => vectR_sym_sym _ _ v _ v' _) |
                          apply IsFun_vect ; typeclasses eauto ].
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
          (y:A) (y':A') (Xy: RA y y') (p : x = y) (q : x' = y') : Type := 
    transport_eq (fun x' => RA x x') q Xx = transport_eq (fun x => RA x y') (inverse p) Xy.

(* code_eq_arg était inutile, juste une simplification 
   avec refl ce qui désormais automatique *)

Instance IsFun_eq {A A' : Type } (RA : A -> A' -> Type) (WFA : IsFun(RA))
          (x:A) (x':A') (Xx : RA x x')
          (y:A) (y':A') (Xy: RA y y') :
          IsFun (FR_eq RA x x' Xx y y' Xy).
Proof.
  intro p. destruct p; unfold FR_eq; cbn.
  apply (contr_equiv2 ((x'; Xx) = (y'; Xy))). 
  apply (@EqSigma A' (RA x) (x';Xx) (y';Xy)).
  apply contr_paths_contr. exact (WFA x).
Defined.

#[export] Hint Extern 0 (IsContr { _ : _ = _ & _})  =>
  apply IsFun_eq: typeclass_instances.

Instance IsFun_eq_sym {A A' : Type } (RA : A -> A' -> Type) (WFA : IsFun(sym RA))
          (x:A) (x':A') (Xx : RA x x')
          (y:A) (y':A') (Xy: RA y y') :
          IsFun (sym (FR_eq RA x x' Xx y y' Xy)).
Proof.
  intro p. destruct p; unfold FR_eq; cbn.
  apply (contr_equiv2 ((@existT _ (fun a => RA a x') x Xx) = (y; Xy))).
  eapply equiv_compose. 
  apply (@EqSigma A (fun z => RA z x') (x;Xx) (y;Xy)).
  apply EquivSigma. cbn. intro e; destruct e. apply Equiv_id. 
  apply contr_paths_contr. exact (WFA x').
Defined.

#[export] Hint Extern 0 (IsContr { _ : _ = _ & _})  =>
  apply IsFun_eq_sym: typeclass_instances.

Definition FP_eq (A A' : Type) (eA : A ⋈ A') 
    (x:A) (x':A') (Xx : _R eA x x')
    (y:A) (y':A') (Xy : _R eA y y') :
    eq A x y ⋈ eq A' x' y'.
Proof.
  unshelve econstructor.
  - exact (FR_eq (_R eA) x x' Xx y y' Xy).
  - split; typeclasses eauto.
Defined.

(*** Vectors with fording à la McBride ***)

Inductive vectF (A:Type) (n : nat) : Type :=
  |nilF : n = 0 -> vectF A n
  |consF : forall m:nat, A -> vectF A m -> S m = n -> vectF A n.

Arguments nilF {_ _} _.
Arguments consF {_ _} _ _ _ _.

Fixpoint FRvectF {A A':Type} (RA : A -> A' -> Type) 
         (n m : nat) (Xn : FR_nat n m) (v : vectF A n)
  : forall  (v' : vectF A' m) , Type :=
  fun v' => match v , v' with
  | nilF e , nilF e' => FR_eq FR_nat _ _ Xn 0 0 I e e'
  | nilF e , consF m' a' v' e' => False
  | consF m a v e , nilF e' => False
  | consF m a v e , consF m' a' v' e' => 
    {Rm : FR_nat m m' & { _ : RA a a' &
    { _ : FR_eq FR_nat (S m) (S m') Rm _ _ Xn e e' & FRvectF RA _ _  Rm v v'}}}
  end.

Definition codeF_arg {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : FR_nat n m) (v:vectF A n) : Type
  :=
    match v with
      nilF e => { e' : m = 0 & FRvectF RA n m Xn (nilF e) (nilF e') }
    | consF n' a v e =>
      {m' : nat & { a':A' & { e' : S m' = m &
      {v':vectF A' m' & FRvectF RA n m Xn (consF n' a v e) (consF m' a' v' e')}}}}
    end.

Definition EquivF_arg {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : FR_nat n m) (v:vectF A n) :
  Equiv ({v' : vectF A' m & FRvectF RA n m Xn v v'})
        (codeF_arg RA n m Xn v).  
Proof.
  destruct v.
  * unshelve econstructor.
  - intros [v' r]; destruct v'; cbn in *; try solve [destruct r]. 
    exact (e0 ; r). 
    - unshelve eapply isequiv_adjointify; cbn. 
      -- intros [em r]. exact (nilF em; r). 
      -- intros [v' r]; destruct v'; try destruct r; try reflexivity. 
      -- intros [e' r]. reflexivity.
  * unshelve econstructor.
    - intros [v' r ]; destruct v' as [ e' | m' a' v' e'] ; try solve [destruct r]; cbn.
      exists m', a', e' , v'. exact r.
    - unshelve eapply isequiv_adjointify; cbn. 
      -- intros [m' [ a' [ e' [v' r]]]]. exists (consF m' a' v' e'). exact r.
      -- intros [v' r]; destruct v'; try destruct r; try reflexivity.
      -- intros [m' [ a' [ e' [v' r]]]]. reflexivity.
Defined.

#[export] Hint Extern 0 (IsContr { _ : nat & _})  =>
  apply IsFun_nat: typeclass_instances.

#[export] Hint Extern 0 (IsContr { _ : nat & _})  =>
  apply IsFun_sym_nat: typeclass_instances.

Instance IsFunF {A A':Type} (RA : A -> A' -> Type) (WFA : IsFun(RA)) :
  forall n m Xn, IsFun (FRvectF RA n m Xn).
Proof.
  intros n m Xn. intro v. revert m Xn.
  induction v; intros;  isFun @EquivF_arg.  
Defined.

Definition codeF_arg_sym {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : FR_nat n m) (v:vectF A' m) : Type
  :=
    match v with
      nilF e' => { e : n = 0 & FRvectF RA n m Xn (nilF e) (nilF e') }
    | consF m' a' v' e' =>
      {n' : nat & { a:A & { e : S n' = n &
      {v:vectF A n' & FRvectF RA n m Xn (consF n' a v e) (consF m' a' v' e')}}}}
    end.

Definition EquivF_argSym {A A' : Type} (RA : A -> A' -> Type)
      (n:nat) (m:nat) (Xn : FR_nat n m) (v':vectF A' m) :
  Equiv ({v : vectF A n & FRvectF RA n m Xn v v'})
        (codeF_arg_sym RA n m Xn v').  
Proof.
  rename v' into v. destruct v.
  * unshelve econstructor.
  - intros [v' r]; destruct v'; cbn in *; try solve [destruct r]. 
    exact (e0 ; r). 
    - unshelve eapply isequiv_adjointify; cbn. 
      -- intros [em r]. exact (nilF em; r). 
      -- intros [v' r]; destruct v'; try destruct r; try reflexivity. 
      -- intros [e' r]. reflexivity.
  * unshelve econstructor.
    - intros [v' r ]; destruct v' as [ e' | m' a' v' e'] ; try solve [destruct r]; cbn.
      exists m', a', e' , v'. exact r.
    - unshelve eapply isequiv_adjointify; cbn. 
      -- intros [m' [ a' [ e' [v' r]]]]. exists (consF m' a' v' e'). exact r.
      -- intros [v' r]; destruct v'; try destruct r; try reflexivity.
      -- intros [m' [ a' [ e' [v' r]]]]. reflexivity.
Defined.

Instance IsFunFSym {A A':Type} (RA : A -> A' -> Type) (WFA : IsFun (sym RA)) :
  forall n m Xn, IsFun (sym (FRvectF RA n m Xn)).
Proof.
  intros n m Xn. intro v. revert n Xn. unfold sym. 
  induction v; intros; isFun @EquivF_argSym.  
Defined.

Definition FP_vectF (A A' : Type) (eA : A ⋈ A')
  (n m : nat) (Xn : FR_nat n m) :
  vectF A n ⋈ vectF A' m.
Proof.
  FP @FRvectF.
Defined.




  

