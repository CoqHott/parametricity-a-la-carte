Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
Require Import Param_CComega.
Require Import Param_ind_parameters.
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
  | [* *] , [* *] => fun Xa => unit
  | [* *] , b' ** l' =>  fun Xa => empty
  | b ** l , [* *]  => fun Xa => empty
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
      [* *] , [* *] => fun _ => Equiv_id unit
    | [* *] , b' ** l' => fun _ => Equiv_id empty
    | b ** l , [* *] => fun _ => Equiv_id empty
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
  |nil_vect : vect A O
  |cons_vect : forall n:nat, A -> vect A n -> vect A (S n).

Arguments nil_vect {_}.
Arguments cons_vect {_ _} _ _.

Notation "[| |]" := nil_vect (format "[| |]").
Notation "[| x |]" := (cons_vect x nil_vect).

Infix "□" := cons_vect (at level 60, right associativity).


Fixpoint FR_vect {A A':Type} (RA : A ≈ A') 
         (n m : nat) (v : vect A n)
  : forall  (v' : vect A' m) (Xn : n ≈ m) , Type :=
  fun v' => match v , v' with
  | [| |] , [| |] => fun Xn => unit
  | [| |] , a' □ v' => fun Xn => empty
  | a □ v , [| |] => fun Xn => empty
  | a □ v , a' □ v' => fun Xn =>
                         {_ : a ≈ a' & FR_vect RA _ _  v v' Xn}
  end.

Instance Rel_vect {A A':Type} (RA : A ≈ A') 
         (n m : nat) (Xn : n ≈ m) : Rel (vect A n) (vect A' m) :=
  fun v v' => FR_vect RA n m v v' Xn.

Definition liftnil {A n} : forall (e : O ≈ n), vect A n :=
  match n with
  | O => fun _ => [| |]
  | S n => fun e => match e with end
  end.

Definition code_vect_arg {A A' : Type} (RA : A ≈ A')
      (n:nat) (v:vect A n) : forall (m:nat) , n ≈ m -> Type
  :=
    match v with
      [| |] => fun m Xn => [||] ≈ liftnil Xn
    | a □ v =>
      fun m =>
        match m with
        | O => fun _ => empty
        | S m => fun Xn =>
                   {a':A' & {v':vect A' m & (a □ v) ≈ (a' □ v')}}
        end
    end.

Definition Equiv_vect_arg {A A' : Type} (RA : A ≈ A')
      (n:nat) (m:nat) (Xn : n ≈ m) (v:vect A n) :
  Equiv ({v' : vect A' m & v ≈ v'})
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

Instance IsFun_vect {A A':Type} (RA : A ≈ A') :
  forall n m Xn, IsFun (Rel_vect RA n m Xn).
Proof.
  intros n m Xn v. revert m Xn.
  induction v; intros [ | m] Xn; isFun @Equiv_vect_arg;
    try destruct Xn. 
Defined.

Definition liftnil_sym {A n} : forall (e : n ≈ O), vect A n :=
  match n with
  | O => fun _ => [| |]
  | S n => fun e => match e with end
  end.

Definition code_vect_arg_sym {A A' : Type} (RA : A ≈ A')
      (m:nat) (v':vect A' m) : forall (n:nat) , n ≈ m -> Type
  :=
    match v' with
      [| |] => fun n Xn => liftnil_sym Xn ≈ [||] 
    | a' □ v' =>
      fun n =>
        match n with
        | O => fun _ => empty
        | S n => fun Xn =>
                   {a:A & {v:vect A n & (a □ v) ≈ (a' □ v')}}
        end
    end.

Definition Equiv_vect_arg_sym {A A' : Type} (RA : A ≈ A')
      (n:nat) (m:nat) (Xn : n ≈ m) (v':vect A' m) :
  Equiv ({v : vect A n & v ≈ v'})
        (code_vect_arg_sym RA m v' n Xn).  
Proof.
  destruct v'.
  * unshelve econstructor.
    - intros [v' r]; destruct v'; cbn; try destruct Xn. 
      exact r.
    - unshelve eapply isequiv_adjointify.
      -- intro r. destruct n; try destruct Xn. 
         exists [||]. exact r. 
      -- intros [v' r]; destruct v'; try destruct Xn; try reflexivity. 
      -- intro r. destruct n; try destruct Xn; try reflexivity.
  * unshelve econstructor.
    - intros [v r ]; destruct v; try destruct Xn; cbn.
      exists a0, v. cbn in * . exact r.
    - unshelve eapply isequiv_adjointify.
      -- destruct n; try destruct Xn. 
         intros [a' [v r]]. exists (a' □ v). exact r.
      -- intros [v r]; destruct v; try destruct Xn; try reflexivity.
      -- destruct n; try destruct Xn. intros [a' [v r]]. reflexivity.
Defined.

Instance IsFun_vect_sym {A A':Type} (RA : A ≈ A') :
  forall n m Xn, IsFun (sym (Rel_vect RA n m Xn)).
Proof.
  intros n m Xn v. revert n Xn.
  induction v; intros [ | m] Xn; isFun @Equiv_vect_arg_sym;
    try destruct Xn.
Defined.

Definition _FP_vect : @vect ≈ @vect.
  FP. 
Defined.

Instance FP_vect (A A' : Type) (eA : A ⋈ A')
  (n m : nat) (Xn : FR_nat n m) :
  vect A n ⋈ vect A' m := _FP_vect _ _ eA _ _ Xn. 


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
Definition Rel_eq {A A' : Type } (RA : A ≈ A')
          (x:A) (x':A') (Xx : x ≈ x')
          (y:A) (y':A') (Xy: y ≈ y') : Rel (x = y) (x' = y') := fun p q =>
    transport_eq (fun x' => x ≈ x') q Xx = transport_eq (fun x => x ≈ y') (inverse p) Xy.

#[export] Hint Extern 0 (Rel (_ = _) (_ = _))  =>
  unshelve refine (@Rel_eq _ _ _ _ _ _ _ _ _) : typeclass_instances.

(* code_eq_arg était inutile, juste une simplification 
   avec refl ce qui désormais automatique *)

Instance IsFun_eq {A A' : Type} (RA : A ≈ A')
          (x:A) (x':A') (Xx : x ≈ x')
          (y:A) (y':A') (Xy: y ≈ y') :
          IsFun (Rel_eq RA x x' Xx y y' Xy).
Proof.
  intro p. destruct p.
  apply (contr_equiv2 ((x'; Xx) = (y'; Xy))). 
  apply (@EqSigma A' (_R RA x) (x';Xx) (y';Xy)).
  apply contr_paths_contr. exact (isWFun (_REquiv RA) x).
Defined.

#[export] Hint Extern 0 (IsContr { _ : _ = _ & _})  =>
  apply IsFun_eq: typeclass_instances.

Instance IsFun_eq_sym {A A' : Type } (RA : A ≈ A')
          (x:A) (x':A') (Xx : x ≈ x')
          (y:A) (y':A') (Xy: y ≈ y') :
          IsFun (sym (Rel_eq RA x x' Xx y y' Xy)).
Proof.
  intro p. destruct p.
  apply (contr_equiv2 ((@existT _ (fun a => a ≈ x') x Xx) = (y; Xy))).
  eapply equiv_compose. 
  apply (@EqSigma A (fun z => z ≈ x') (x;Xx) (y;Xy)).
  apply EquivSigma. cbn. intro e; destruct e. apply Equiv_id. 
  apply contr_paths_contr. exact (isWFunSym (_REquiv RA) x').
Defined.

#[export] Hint Extern 0 (IsContr { _ : _ = _ & _})  =>
  apply IsFun_eq_sym: typeclass_instances.

Definition _FP_eq : @eq ≈ @eq. 
  FP.
Defined.

Instance FP_eq (A A' : Type) (eA : A ⋈ A') 
    (x:A) (x':A') (Xx : _R eA x x')
    (y:A) (y':A') (Xy : _R eA y y') :
    eq A x y ⋈ eq A' x' y' := _FP_eq _ _ eA _ _ Xx _ _ Xy. 

(*** Vectors with fording à la McBride ***)

#[export] Hint Extern 0 (_ ≈ _) =>
  compute: typeclass_instances.

Inductive vectF (A:Type) (n : nat) : Type :=
  |nilF : 0 = n -> vectF A n
  |consF : forall m:nat, A -> vectF A m -> S m = n -> vectF A n.

Arguments nilF {_ _} _.
Arguments consF {_ _} _ _ _ _.

Fixpoint FRvectF {A A':Type} (RA : A ≈ A') 
         (n m : nat) (Xn : n ≈ m) (v : vectF A n)
  : forall  (v' : vectF A' m) , Type :=
  fun v' => match v , v' with
  | nilF e , nilF e' => e ≈ e'
  | consF m a v e , consF m' a' v' e' => 
    {Rm : FR_nat m m' & { _ : (_R RA) a a' &
    { _ : FRvectF RA _ _  Rm v v' & e ≈ e' }}}
  | _ , _ => empty
  end.

Instance Rel_vectF {A A':Type} (RA : A ≈ A') 
         (n m : nat) (Xn : n ≈ m) : Rel (vectF A n) (vectF A' m)
  := FRvectF RA n m Xn. 

Definition codeF_arg {A A' : Type} (RA : A ≈ A')
      (n:nat) (m:nat) (Xn : n ≈ m) (v:vectF A n) : Type
  :=
    match v with
      nilF e => { e' : O = m & nilF e ≈ nilF e' }
    | consF n' a v e =>
      {m' : nat & { a':A' &  {v':vectF A' m' & { e' : S m' = m &
      consF n' a v e ≈ consF m' a' v' e'}}}}
    end.

Definition EquivVectF_arg {A A' : Type} (RA : A ≈ A')
      (n:nat) (m:nat) (Xn : n ≈ m) (v:vectF A n) :
  Equiv ({v' : vectF A' m & v ≈ v'})
        (codeF_arg RA n m Xn v).  
Proof.
  destruct v.
  * unshelve econstructor.
  - exact (fun lr =>
        match lr with
        | (nilF e0 ; r) => (e0 ; r)
        | (consF m a e v ; r) => match r with end
        end). 
  - unshelve econstructor. 
      -- exact (fun lr => match lr with (e0 ; r) => (nilF e0 ; r) end).
      -- exact (fun lr =>
                  match lr with
                  | (nilF e0 ; r) => eq_refl
                  | (consF m' a' e' v' ; r) => match r with end
                  end). 
      -- exact (fun lr => match lr with (e0 ; r) => eq_refl end).
      -- intros [v' r]. destruct v'; try destruct r; cbn;  reflexivity. 
  * unshelve econstructor.
  - exact (fun lr =>
        match lr with
        | (nilF e0 ; r) => match r with end 
        | (consF m' a' v' e' ; r) => (m' ; ( a' ; (v' ; (e' ; r)))) 
        end).
    - unshelve econstructor; cbn. 
      -- exact (fun lr =>
                  match lr with
                  | (m' ; ( a' ; (v' ; (e' ; r)))) => (consF m' a' v' e' ; r)
                  end). 
      -- exact (fun lr =>
                  match lr with
                  | (nilF e0 ; r) => match r with end 
                  | (consF m' a' e' v' ; r) => eq_refl
                  end). 
      -- exact (fun lr =>
                  match lr with
                  | (m' ; ( a' ; (v' ; (e' ; r)))) => eq_refl
                  end).
      -- intros [v' r]. destruct v'; try destruct r; reflexivity. 
 Defined.

#[export] Hint Extern 0 (IsContr { _ : nat & _})  =>
  apply IsFun_nat: typeclass_instances.

#[export] Hint Extern 0 (IsContr { _ : nat & _})  =>
  apply IsFun_sym_nat: typeclass_instances.



Instance IsFunF {A A' : Type} (RA : A ≈ A') :
  forall n m Xn, IsFun (Rel_vectF RA n m Xn).
Proof.
  intros n m Xn. intro v. revert m Xn.
  induction v; intros; isFun @EquivVectF_arg.
Defined.


Definition codeF_arg_sym {A A' : Type} (RA : A ≈ A')
      (n:nat) (m:nat) (Xn : n ≈ m) (v:vectF A' m) : Type
  :=
    match v with
      nilF e' => { e : O = n & nilF e ≈ nilF e' }
    | consF m' a' v' e' =>
      {n' : nat & { a:A & {v:vectF A n' & { e : S n' = n &
      consF n' a v e ≈ consF m' a' v' e'}}}}
    end.

Definition EquivVectF_argSym {A A' : Type} (RA : A ≈ A')
      (n:nat) (m:nat) (Xn : n ≈ m) (v':vectF A' m) :
  Equiv ({v : vectF A n & v ≈ v'})
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
      exists m', a', v' , e'. exact r.
    - unshelve eapply isequiv_adjointify; cbn. 
      -- intros [m' [ a' [ v' [e' r]]]]. exists (consF m' a' v' e'). exact r.
      -- intros [v' r]; destruct v'; try destruct r; try reflexivity.
      -- intros [m' [ a' [ v' [e' r]]]]. reflexivity.
Defined.

Instance IsFunFSym {A A':Type} (RA : A ≈ A') :
  forall n m Xn, IsFun (sym (FRvectF RA n m Xn)).
Proof.
  intros n m Xn. intro v. revert n Xn. unfold sym. 
  induction v; intros; isFun @EquivVectF_argSym.  
Defined.

#[export] Hint Extern 0 (IsFun _ ) =>
  apply IsFunF: typeclass_instances.

#[export] Hint Extern 0 (IsFun _ ) =>
  apply IsFunFSym: typeclass_instances.

Definition _FP_vectR : @vectF ≈ @vectF.
  intros A A' eA n m en. FP.
Defined.

Instance FP_vectF (A A' : Type) (eA : A ≈ A')
  (n m : nat) (Xn : n ≈ m) :
  vectF A n ⋈ vectF A' m := _FP_vectR A A' eA n m Xn.



(* Some definitions *)

Ltac contr_refl :=
  unfold rel; unfold Rel_eq; cbn;
  try (apply contr_paths_contr; apply IsContr_unit);
  try unfold FR_S; try reflexivity.

Fixpoint vect_to_forded {A:Type} {n:nat} (v : vect A n) : vectF A n.
Proof.
  destruct v.
  exact (nilF eq_refl).
  exact (consF n a (vect_to_forded A n v) eq_refl).
Defined.

Fixpoint forded_to_vect {A:Type} {n:nat} (vF : vectF A n) : vect A n.
Proof.
  destruct vF.
  - exact (e # [||]). 
  - exact (e # (a □ forded_to_vect A m vF)).
Defined.

Fixpoint vect_sect {A:Type} {n:nat} (v : vect A n) :
      forded_to_vect (vect_to_forded v) = v.
Proof.
  destruct v; cbn.
  - reflexivity.
  - apply ap. apply vect_sect.
Defined.

Fixpoint vect_retr {A:Type} {n:nat} (vF : vectF A n) :
      vect_to_forded (forded_to_vect vF) = vF.
Proof.
  destruct vF; destruct e; cbn. 
  - reflexivity. 
  - apply (ap (fun vF => consF m a vF eq_refl)). apply vect_retr.
Defined.

Instance vectF_vect {A:Type} {n : nat} : vectF A n ≃ vect A n.
unshelve econstructor.
- apply forded_to_vect.
- unshelve eapply isequiv_adjointify.
  + apply vect_to_forded.
  + apply vect_retr.  
  + apply vect_sect.  
Defined. 

(* ###########################################################*)
(* ###    WORK IN PROGRESS : vectors by forded one         ###*)
(* ###########################################################*)

Definition FR_vect_bis {A A':Type} (RA : A ≈ A') (n : nat) (v : vect A n)
        (m : nat) (v' : vect A' m) (Xn : n ≈ m) : Type :=
        FRvectF RA n m Xn (vect_to_forded v) (vect_to_forded v').

Instance Rel_vect_bis {A A':Type} (RA : A ≈ A') 
     (n m : nat) (Xn : n ≈ m) : Rel (vect A n) (vect A' m) :=
     fun v v' => FR_vect_bis RA n v m v' Xn.

Definition IsFun_vect_bis {A A':Type} (RA : A ≈ A') :
     forall n m Xn, IsFun (Rel_vect_bis RA n m Xn).
Proof.
  intros n m Xn v.
  eapply contr_equiv2; [ idtac | apply (IsFunF RA n m Xn (vect_to_forded v)) ].
  unfold Rel_vect_bis, FR_vect_bis. unfold Rel_vectF.
  unshelve eapply EquivSigmaGen. intro v'. rewrite vect_retr.
  apply Equiv_id.
Defined. 

Definition IsFun_vect_bis_sym {A A':Type} (RA : A ≈ A') :
     forall n m Xn, IsFun (sym (Rel_vect_bis RA n m Xn)).
Proof.
  intros n m Xn v'.
  eapply contr_equiv2; [ idtac | apply (IsFunFSym RA n m Xn (vect_to_forded v')) ].
  unfold Rel_vect_bis, FR_vect_bis. unfold Rel_vectF.
  unshelve eapply EquivSigmaGen. intro v. cbn. rewrite vect_retr.
  apply Equiv_id.
Defined. 

#[export] Hint Extern 0 (IsFun _ ) =>
  apply IsFun_vect_bis: typeclass_instances.

#[export] Hint Extern 0 (IsFun _ ) =>
  apply IsFun_vect_bis_sym: typeclass_instances.

Definition _FP_vect_bis : @vect ≈ @vect.
  intros A A' eA n m Xn. FP.
Defined.

Instance FP_vect_bis (A A' : Type) (eA : A ≈ A')
  (n m : nat) (Xn : n ≈ m) :
  vect A n ⋈ vect A' m := _FP_vect_bis A A' eA n m Xn.

  
  
(*** proof that the lifting preserve relation ***)
Definition FRvect_to_FRvectF {A A':Type} (RA : A ≈ A') {n : nat} (v : vect A n) :
  forall {m} v' Xn,  Rel_vect RA n m Xn v v' -> Rel_vect_bis RA n m Xn v v'.
Proof.
  induction v; intros m v' Xn; destruct v'; cbn; intro Xv; try auto.
  - contr_refl. 
  - destruct Xv as [Xa Xv]. exists Xn, Xa.
    exists (IHv n0 v' Xn Xv). contr_refl. 
Defined.

Definition FRvectF_to_FRvect {A A':Type} (RA : A ≈ A') {n : nat} (v : vect A n) :
  forall {m:nat} v' Xn,  Rel_vect_bis RA n m Xn v v' -> Rel_vect RA n m Xn v v'. 
Proof.
  unfold Rel_vect_bis, FR_vect_bis, Rel_vect.
  induction v; intros m v' Xn; destruct v'; cbn; intro Xv; try auto.
  destruct Xv as [Xn' [Xa [Xv Xeq]]].
  unfold rel, Rel_eq in Xeq; cbn in Xeq; unfold FR_S in Xeq; destruct Xeq.
  exists Xa. exact (IHv n0 v' Xn' Xv).
Defined.

Definition FRvect_sect {A A':Type} (RA : A ≈ A') {n : nat} (v : vect A n) :
  forall {m:nat} (v':vect A' m) Xn Xv,  FRvectF_to_FRvect RA v v' Xn (FRvect_to_FRvectF RA v v' Xn Xv) = Xv.
Proof.
  induction v; intros m v' Xn; destruct v'; intro Xv; try auto; try reflexivity.
  - destruct Xn, Xv; reflexivity.
  - destruct Xv as [Xa Xv]. 
    apply path_sigma_uncurried; unshelve econstructor.
    reflexivity. unfold transport_eq. admit.
Admitted.

Definition FRvect_retr {A A':Type} (RA : A ≈ A') {n : nat} (v : vect A n) :
  forall {m:nat} (v':vect A' m) Xn XFv,  FRvect_to_FRvectF RA v v' Xn (FRvectF_to_FRvect RA v v' Xn XFv) = XFv.
Proof.
  unfold Rel_vect_bis, FR_vect_bis, Rel_vect.
  induction v; intros m v' Xn; destruct v'; intro Xv; try auto; try reflexivity.
  - destruct Xn; cbn. eapply path_contr.
  - destruct Xv as [Xn' [Xa [Xv Xeq]]].
    unfold rel, Rel_eq in Xeq; cbn in Xeq; unfold FR_S in Xeq; destruct Xeq.
    apply path_sigma_uncurried; unshelve econstructor. cbn. reflexivity. unfold transport_eq.
    apply path_sigma_uncurried; unshelve econstructor. cbn. reflexivity. unfold transport_eq.
    admit.
Admitted. 
