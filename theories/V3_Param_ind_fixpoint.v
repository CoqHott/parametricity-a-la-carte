Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
Require Import V3_Param_CComega_fixpoint.
From Coq Require Import ssreflect.

Set Universe Polymorphism.





(* ########################################################### *)
(* ###        Parametricity for Inductive Types            ### *)
(* ########################################################### *)

(** Generic Lemma to prove contractibility of telescope **)

Definition IsContr_telescope2 {A} {P RA : A -> Type}
           {RP : forall a, RA a -> P a -> Type}
  : IsContr {a:A & RA a} ->
    (forall a Xa, IsContr {b : P a & RP a Xa b}) ->
    IsContr {a : A & {b : P a & {Xa : RA a & RP a Xa b}}}.
Proof.
  intros WFa WFb. apply (contr_equiv2 {a : A & RA a}); try apply WFa.
  apply EquivSigma. intro a. eapply Equiv_inverse.
  eapply equiv_compose. eapply swap_sigma.
  cbn. apply IsContrSigma_codomain. intro H. apply WFb. 
Defined.

Definition IsContr_telescope3 {A} {B RA : A -> Type}
           {RB : forall a, RA a -> B a -> Type}
           {C : forall a, B a -> Type}
           {RC : forall a (Ra : RA a) (b : B a) , RB a Ra b -> C a b -> Type}
  : IsContr {a:A & RA a} ->
    (forall a Xa, IsContr {b : B a & RB a Xa b}) ->
    (forall a Xa b Xb, IsContr {c : C a b & RC a Xa b Xb c}) ->
    IsContr {a : A & {b : B a & {c : C a b & {Xa : RA a & {Xb : RB a Xa b & RC a Xa b Xb c}}}}}.
Proof.
  intros WFa WFb WFc.
  apply (contr_equiv2 {a : A & RA a}); try apply WFa.
  apply EquivSigma. intro a. eapply Equiv_inverse.
  eapply equiv_compose. eapply EquivSigma. intro. eapply swap_sigma. cbn.
  eapply equiv_compose. eapply swap_sigma. cbn.
  cbn. apply IsContrSigma_codomain. intro Ha.
  apply IsContr_telescope2; auto.  
Defined.

Ltac isFun f :=
  let x := fresh "foo" in 
  intro x; induction x ;
  eapply contr_equiv2 ; try (apply Equiv_inverse; apply f);
  try first [ eapply IsContr_telescope3 |
              eapply IsContr_telescope2 |
              apply IsContr_True ];
  intros; match goal with | H : _ |- _ => eapply H end. 


(* ###########################################################*)
(* ###                   A ⊔ B ⋈ A' ⊔ B'                  ###*)
(* ###########################################################*)

Inductive somme (A:Type) (B:Type) : Type :=
  |inl : A -> somme A B
  |inr : B -> somme A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

Notation "A ⊔ B" := (somme A B) (at level 30).

Definition FR_somme {A A' B B':Type} (RA : A -> A' -> Type) (RB : B -> B' -> Type) 
         (x:A ⊔ B) (y:A' ⊔ B') : Type :=
  match x , y with
    inl a , inl a' => RA a a'
  | inl a , inr b' => False
  | inr b , inl a' => False
  | inr b , inr b' => RB b b'
  end. 

Definition code_somme_arg {A A' B B' : Type} (RA : A -> A' -> Type)
                          (RB : B -> B' -> Type) (x : A ⊔ B) : 
  Type :=
  match x with
    inl a => {a':A' & FR_somme RA RB (inl a) (inl a')}
  | inr b => {b':B' & FR_somme RA RB (inr b) (inr b')}
  end. 

Definition Equiv_somme_arg {A A' B B' : Type} (RA : A -> A' -> Type)
      (RB : B -> B' -> Type) (x : A ⊔ B) : 
  Equiv ({y : A'⊔B' & FR_somme RA RB x y}) (code_somme_arg RA RB x). 
Proof.
  destruct x as [a | b ]; unshelve econstructor ; cbn. 
  - exact (fun lr => match lr with
                         ( inl a' ; r ) => (a' ; r)
                       | ( inr b' ; r ) => match r with end  
                       end).
  - exact (fun lr => match lr with
                         ( inl a' ; r ) => match r with end 
                       | ( inr b' ; r ) => (b' ; r)
                       end).
  - unshelve eapply isequiv_adjointify.
    -- intros [a' r]. exact (inl a' ; r).
    -- intros [[a' | b'] r]; [ reflexivity | destruct r ].
    -- intros [a' r]. reflexivity.
  - unshelve eapply isequiv_adjointify.
    -- intros [b' r]. exact (inr b' ; r ).
    -- intros [[a' | b'] r]; [ destruct r | reflexivity ].
    -- intros [b' r]; try reflexivity.
Defined.

Definition IsFun_somme {A A' B B' : Type} 
                       (RA : A -> A' -> Type)
                       (RB : B -> B' -> Type)
                       (WFA : IsFun RA)
                       (WFB : IsFun RB) :
                       IsFun (FR_somme RA RB).
Proof.
  isFun @Equiv_somme_arg.
Defined.

Definition Somme_sym_sym {A A' B B': Type}
      (RA : A -> A' -> Type) (RB : B -> B' -> Type) : 
      forall {x y}, Equiv (FR_somme RA RB x y) 
                          (sym (FR_somme (sym RA) (sym RB)) x y) :=
  fun x y => match x , y with
    inl a , inl a' => Equiv_id (RA a a')
  | inl a , inr b' => Equiv_id False
  | inr b , inl a' => Equiv_id False
  | inr b , inr b' => Equiv_id (RB b b')
  end. 

Definition FP_somme {A A' B B' : Type} (eA : A ⋈ A') (eB : B ⋈ B') : (A ⊔ B) ⋈ (A' ⊔ B').
Proof.
  unshelve econstructor.
  - exact (FR_somme (_R eA) (_R eB)).
  - split.
    + apply IsFun_somme; typeclasses eauto.
    + eapply IsFun_sym; [ eapply Somme_sym_sym |
                          apply IsFun_somme ; typeclasses eauto ].
Defined.



(* ###########################################################*)
(* ###                   list A ⋈ list A'                 ###*)
(* ###########################################################*)

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _. 

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Infix "::" := cons (at level 60, right associativity).


Fixpoint FR_list {A A'} (RA : A -> A' -> Type) (l: list A) (l': list A') : Type :=
  match l , l' with
    [] , [] => True
  | [] , cons a' l' => False
  | cons a l , [] => False
  | cons a l , cons a' l' => {Xa : RA a a' & FR_list RA l l'}
  end.

Definition code_list_arg {A A' : Type} (RA : A -> A' -> Type) (l : list A) : Type :=
  match l with
    [] => FR_list RA [] []
  | cons a l => {a':A' &{l':list A' & FR_list RA (a::l) (a'::l')}}
  end.

Definition Equiv_list_arg {A A' : Type} (RA : A -> A' -> Type) (l: list A) :
      Equiv ({y : list A' & FR_list RA l y}) (code_list_arg RA l).
Proof.
  destruct l as [ | a l]; unfold code_list_arg; unshelve econstructor.  
  - exact (fun lr => match lr with
                         ([] ; r) => I
                       | (a' :: l' ; r) => match r with end
                       end).
  - exact (fun lr => match lr with
                         ([] ; r) => match r with end
                       | (a' :: l' ; r) => (a' ; ( l' ; r)) 
                       end).
  - unshelve eapply isequiv_adjointify.
    -- intro r. exact ( [] ; r).
    -- intros [[| a' l'] []] ; reflexivity.
    -- intro r; destruct r. reflexivity. 
  - unshelve eapply isequiv_adjointify.
    -- intros [a' [l' r]]. exact ( a'::l' ; r).
    -- intros [[|a' l'] []]; reflexivity.
    -- intros [a' [l' []]]; reflexivity.
Defined.

Definition IsFun_list (A A' : Type) (RA : A -> A' -> Type)
           (WFA : IsFun RA) : IsFun (FR_list RA).
Proof.
  isFun @Equiv_list_arg.  
Defined.

Fixpoint listR_sym_sym A A' (R : A -> A' -> Type) (l : list A) : forall l',
    FR_list R l l' ≃ sym (FR_list (sym R)) l l' :=
  fun l' =>
    match l , l' with
      [] , [] => Equiv_id True 
    | [] , cons a' l' => Equiv_id False
    | cons a l , [] => Equiv_id False
    | cons a l , cons a' l' => EquivSigma (fun r => listR_sym_sym _ _ _ l l')
    end.

Definition FP_list (A A' : Type) (eA : A ⋈ A'):
  list A ⋈ list A'.
Proof.
  unshelve econstructor.
  - exact (FR_list (_R eA)).
  - split.
    + apply IsFun_list; typeclasses eauto.
    + eapply IsFun_sym; [ eapply listR_sym_sym |
                          apply IsFun_list ; typeclasses eauto ].
Defined.



(* ###########################################################*)
(* ###                   tree A ⋈ tree A'                 ###*)
(* ###########################################################*)

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
    - intros [t' r]. destruct t' as [ | ls' a' rs']; try destruct r.
      exact I.
    - unshelve eapply isequiv_adjointify.
      -- intro r. exists nil_tree. exact r.
      -- intros [t' r]. destruct t' as [ | ls' a' rs']; try destruct r. 
         reflexivity.
      -- intro r; destruct r. reflexivity.
  * unshelve econstructor.
  - intros [t' r]. destruct t' as [ | ls' a' rs']; try destruct r.
    exists ls', a', rs', x. exact s.
  - unshelve eapply isequiv_adjointify.
    -- intros [ls' [a' [rs' r]]]. exists (cons_tree ls' a' rs'). exact r.
    -- intros [t' r]. destruct t' as [ | ls' a' rs']; try destruct r.
       reflexivity.
    -- intros [ls' [a' [rs' r]]]. destruct r. reflexivity.
Defined.

Definition IsFun_tree {A A' : Type} (RA : A -> A' -> Type)
                      (WFA : IsFun RA): IsFun(FR_tree RA).
Proof.
  isFun @Equiv_tree_arg.  
Defined.

Fixpoint Tree_sym_sym A A' (RA : A -> A' -> Type) (t : tree A) :
  forall t', FR_tree RA t t' ≃ sym (FR_tree (sym RA)) t t' :=
  fun t' =>
    match t , t' with
      nil_tree , nil_tree => Equiv_id True 
    | nil_tree , cons_tree ls' a' rs' => Equiv_id False
    | cons_tree ls a rs , nil_tree => Equiv_id False
    | cons_tree ls a rs , cons_tree ls' a' rs' =>
      EquivSigmaNoDep (Tree_sym_sym A A' RA ls ls')
         (EquivSigmaNoDep (Equiv_id (RA a a'))
                        (Tree_sym_sym A A' RA rs rs')) 
    end.

Definition FP_tree {A A':Type} (eA : A ⋈ A') : tree A ⋈ tree A'.
Proof.
  unshelve econstructor.
  - refine (FR_tree (_R eA)).
  - split.
    + apply IsFun_tree; typeclasses eauto.
    + eapply IsFun_sym; [ eapply Tree_sym_sym |
                          apply IsFun_tree ; typeclasses eauto ].
Defined.

(* ###########################################################*)
(* ###                 Σ(a:A) B ⋈ Σ(a':A') B'             ###*)
(* ###########################################################*)

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
      (RB : forall (a:A) (a':A') (Xa : RA a a'), B a -> B' a' -> Type)
      (x : {a: A & B a}) (y:{a':A' & B' a'}) : Type :=
  match x , y with 
    (a ; b) , (a' ; b') => {Xa: RA a a' & RB a a' Xa b b'}
  end.

Definition code_sigma_arg {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A -> A' -> Type)
      (RB : forall (a:A) (a':A') (Xa:RA a a'), B a -> B' a' -> Type)
      (x: {a:A & B a}) : Type :=
  match x with
    (a ; b) => {a' : A' & {b' : B' a' & FR_sigma RA RB (a;b) (a';b')}}
  end.

Definition Equiv_sigma_arg {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A -> A' -> Type)
      (RB : forall (a:A) (a':A') (Xa : RA a a'), B a -> B' a' -> Type)
      (x: {a:A & B a}) : 
      Equiv ({y:{a':A' & B' a'} & FR_sigma RA RB x y})
            (code_sigma_arg RA RB x).
Proof.
  destruct x as [a b]; unfold code_sigma_arg.
  unshelve econstructor.
  - intros [y r]. destruct y as [a' b']; try destruct r.
    exists a', b', x. exact r.
  - unshelve eapply isequiv_adjointify.
    -- intros [a' [b' r]]. exists (a';b'). exact r.
    -- intros [y r]; destruct y; try destruct r; try reflexivity.
    -- intros [a' [b' r]]; try destruct r; try reflexivity.
Defined.

Definition IsFun_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      {RA : A -> A' -> Type} 
      {RB : forall a a' (Xa : RA a a'), Rel (B a) (B' a')} 
      (WFA : IsFun RA)
      (WFB : forall a a' (Xa : RA a a'), IsFun(RB a a' Xa)) :
      IsFun (FR_sigma RA RB).
Proof.
  isFun @Equiv_sigma_arg.
Defined.

Definition Sigma_sym_sym {A A'} {P : A -> Type} {P' : A' -> Type} 
  {RA : A -> A' -> Type} 
  {RB : forall a a' (Xa : RA a a'), Rel (P a) (P' a')}
  (z: {a:A & P a}):
  forall w, (FR_sigma RA RB z w) ≃ sym (FR_sigma (sym RA) (fun x y X => sym (RB y x X))) z w :=
  fun w =>
    match z , w with
      (a ; b) , (a' ; b') => EquivSigmaGen (Equiv_id _)
                                           (fun X => Equiv_id _)
    end.

Definition FP_sigma (A A' : Type) (B : A -> Type) (B' : A' -> Type) 
    (eA : A ⋈ A')
    (eB : forall (a:A) (a':A') (Xa: (_R eA) a a'), B a ⋈ B' a') :
    {a:A & B a} ⋈ {a':A' & B' a'}.
Proof.
 unshelve econstructor.
  - refine (FR_sigma (_R eA) (fun a a' Xa => _R (eB a a' Xa))).
  - split.
    + apply IsFun_sigma; typeclasses eauto.
    + eapply IsFun_sym; [ eapply Sigma_sym_sym |
                          apply IsFun_sigma ; typeclasses eauto ].
Defined.
