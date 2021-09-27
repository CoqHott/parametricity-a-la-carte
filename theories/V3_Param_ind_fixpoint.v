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

Definition IsContr_telescope4 {A} {RA : A -> Type}
           {B :A -> Type}
           {RB : forall a, RA a -> B a -> Type}
           {C : forall a, B a -> Type}
           {RC : forall a (Ra : RA a) (b : B a) , RB a Ra b -> C a b -> Type}
           {D : forall a (b : B a), C a b -> Type}
           {RD : forall a (Ra : RA a) (b : B a) (Rb : RB a Ra b) (c : C a b)
                        (Rc : RC a Ra b Rb c), D a b c -> Type}           
  : IsContr {a:A & RA a} ->
    (forall a Xa, IsContr {b : B a & RB a Xa b}) ->
    (forall a Xa b Xb, IsContr {c : C a b & RC a Xa b Xb c}) ->
    (forall a Xa b Xb c Xc, IsContr {d : D a b c & RD a Xa b Xb c Xc d}) ->
    IsContr {a : A & {b : B a & {c : C a b & { d : D a b c &
            {Xa : RA a & {Xb : RB a Xa b & { Xc : RC a Xa b Xb c & RD a Xa b Xb c Xc d}}}}}}}.
Proof.
  intros WFa WFb WFc WFd.
  apply (contr_equiv2 {a : A & RA a}); try apply WFa.
  apply EquivSigma. intro a. eapply Equiv_inverse.
  eapply equiv_compose. eapply EquivSigma. intro.
  eapply equiv_compose. eapply EquivSigma. intro.
  eapply swap_sigma. cbn. 
  eapply swap_sigma. cbn. 
  eapply equiv_compose. eapply swap_sigma. cbn.
  cbn. apply IsContrSigma_codomain. intro Ha.
  apply IsContr_telescope3; auto.  
Defined.

Definition IsContr_telescope5 {A} {RA : A -> Type}
           {B :A -> Type}
           {RB : forall a, RA a -> B a -> Type}
           {C : forall a, B a -> Type}
           {RC : forall a (Ra : RA a) (b : B a) , RB a Ra b -> C a b -> Type}
           {D : forall a (b : B a), C a b -> Type}
           {RD : forall a (Ra : RA a) (b : B a) (Rb : RB a Ra b) (c : C a b)
                        (Rc : RC a Ra b Rb c), D a b c -> Type}           
           {E : forall a (b : B a) (c: C a b), D a b c -> Type}
           {RE : forall a (Ra : RA a) (b : B a) (Rb : RB a Ra b)
                        (c : C a b) (Rc : RC a Ra b Rb c)
                        (d : D a b c) (Rd : RD a Ra b Rb c Rc d),
               E a b c d -> Type}           
  : IsContr {a:A & RA a} ->
    (forall a Xa, IsContr {b : B a & RB a Xa b}) ->
    (forall a Xa b Xb, IsContr {c : C a b & RC a Xa b Xb c}) ->
    (forall a Xa b Xb c Xc, IsContr {d : D a b c & RD a Xa b Xb c Xc d}) ->
    (forall a Xa b Xb c Xc d Xd,
        IsContr {e : E a b c d & RE a Xa b Xb c Xc d Xd e}) ->
    IsContr {a : A & {b : B a & {c : C a b & { d : D a b c & { e : E a b c d &
            {Xa : RA a & {Xb : RB a Xa b & { Xc : RC a Xa b Xb c & {Xd : RD a Xa b Xb c Xc d & RE a Xa b Xb c Xc d Xd e}}}}}}}}}.
Proof.
  intros WFa WFb WFc WFd WFe.
  apply (contr_equiv2 {a : A & RA a}); try apply WFa.
  apply EquivSigma. intro a. eapply Equiv_inverse.
  eapply equiv_compose. eapply EquivSigma. intro.
  eapply equiv_compose. eapply EquivSigma. intro.
  eapply equiv_compose. eapply EquivSigma. intro.
  eapply swap_sigma. cbn. 
  eapply swap_sigma. cbn. 
  eapply swap_sigma. cbn. 
  eapply equiv_compose. eapply swap_sigma. cbn.
  cbn. apply IsContrSigma_codomain. intro Ha.
  apply IsContr_telescope4; auto.  
Defined.

Ltac erefine f  := first [ refine f | refine (f _) | refine (f _ _) | refine (f _ _ _) | refine (f _ _ _ _) | refine (f _ _ _ _ _) | refine (f _ _ _ _ _ _) | refine (f _ _ _ _ _ _ _) | refine (f _ _ _ _ _ _ _ _) | refine (f _ _ _ _ _ _ _ _ _) | refine (f _ _ _ _ _ _ _ _ _ _) | refine (f _ _ _ _ _ _ _ _ _ _ _) | refine (f _ _ _ _ _ _ _ _ _ _ _ _)  ].

Ltac isFun f :=
  eapply contr_equiv2 ; try (apply Equiv_inverse; erefine f);
  try first [ eapply IsContr_telescope5 |
              eapply IsContr_telescope4 |
              eapply IsContr_telescope3 |
              eapply IsContr_telescope2 |
              idtac 
             ];
  try first [
        intros; match goal with | H : _ |- _ => eapply H end |
        cbn; typeclasses eauto ].

Ltac FP :=
   unshelve econstructor; split ; typeclasses eauto.

(* Ltac isFunSym fsym := *)
(*   eapply IsFun_sym; [ eapply fsym | typeclasses eauto ]. *)

#[export] Hint Unfold sym : typeclass_instances.

#[export] Hint Unfold rel : typeclass_instances.

#[export] Hint Extern 0 (Rel _ _)  =>
 match goal with | H : _ ≈ _ |- _ => progress (compute in H) end: typeclass_instances.

(* ###########################################################*)
(* ###                     nat ⋈ nat                       ###*)
(* ###########################################################*)


Fixpoint FR_nat (n m : nat) : Type :=
  match n , m with
    | 0 , 0 => unit
    | S n , S m => FR_nat n m
    | _ , _ => empty
  end.

Instance Rel_nat : Rel nat nat := FR_nat. 

Definition code_nat_arg (n : nat) : 
  Type :=
  match n with
    0 => FR_nat 0 0
  | S n => {m : nat & FR_nat (S n) (S m)}
  end. 

Definition Equiv_nat_arg (n : nat) : 
  Equiv ({m : nat & n ≈ m}) (code_nat_arg n). 
Proof.
  destruct n as [ | n ]; unshelve econstructor ; cbn. 
  - exact (fun lr => match lr with
                         ( 0 ; r ) => tt
                       | ( S m ; r ) => match r with end  
                       end).
  - exact (fun lr => match lr with
                         ( 0 ; r ) => match r with end 
                       | ( S m ; r ) => (m ; r)
                       end).
  - unshelve eapply isequiv_adjointify.
    -- exact (fun r => (0 ; r)).
    -- intros [[| n] []]; reflexivity. 
    -- intros []. reflexivity.
  - unshelve eapply isequiv_adjointify.
    -- intros [m r]. exact (S m ; r ).
    -- intros [[ | m] r]; [ destruct r | reflexivity ].
    -- intros [m r]; try reflexivity.
Defined.

Instance IsFun_nat : IsFun FR_nat.
Proof.
  intro n; induction n; isFun @Equiv_nat_arg.
Defined.

Definition code_nat_arg_sym (n : nat) : 
  Type :=
  match n with
    0 => FR_nat 0 0
  | S n => {m : nat & FR_nat (S m) (S n)}
  end.

Definition Equiv_nat_arg_sym (m : nat) : 
  Equiv ({n : nat & n ≈ m}) (code_nat_arg_sym m). 
Proof.
  destruct m as [ | m ]; unshelve econstructor ; cbn. 
  - exact (fun lr => match lr with
                         ( 0 ; r ) => tt
                       | ( S m ; r ) => match r with end  
                       end).
  - exact (fun lr => match lr with
                         ( 0 ; r ) => match r with end 
                       | ( S n ; r ) => (n ; r)
                       end).
  - unshelve eapply isequiv_adjointify.
    -- exact (fun r => (0 ; r)).
    -- intros [[| n] []]; reflexivity. 
    -- intros []. reflexivity.
  - unshelve eapply isequiv_adjointify.
    -- intros [n r]. exact (S n ; r ).
    -- intros [[ | n] r]; [ destruct r | reflexivity ].
    -- intros [n r]; try reflexivity.
Defined.

Instance IsFun_sym_nat : IsFun (sym FR_nat). 
Proof.
  intro n; induction n; isFun @Equiv_nat_arg_sym.
Defined.
  
Instance FP_nat : nat ⋈ nat.
Proof.
  FP. 
Defined.


(* ###########################################################*)
(* ###                   A ⊔ B ⋈ A' ⊔ B'                  ###*)
(* ###########################################################*)

Inductive somme (A:Type) (B:Type) : Type :=
  |inl : A -> somme A B
  |inr : B -> somme A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

Notation "A ⊔ B" := (somme A B) (at level 30).

Definition FR_somme {A A' B B':Type} (RA : A ≈ A') (RB : B ≈ B') 
         (x:A ⊔ B) (y:A' ⊔ B') : Type :=
  match x , y with
    inl a , inl a' => a ≈ a'
  | inl a , inr b' => empty
  | inr b , inl a' => empty
  | inr b , inr b' => b ≈ b'
  end.

Instance Rel_Somme {A A' B B':Type} (RA : A ≈ A')
         (RB : B ≈ B') : Rel (A ⊔ B) (A' ⊔ B') := FR_somme RA RB. 

Definition code_somme_arg {A A' B B' : Type} (RA : A ≈ A')
                          (RB : B ≈ B') (x : A ⊔ B) : 
  Type :=
  match x with
    inl a => {a':A' & inl a ≈ inl a'}
  | inr b => {b':B' & inr b ≈ inr b'}
  end. 

Definition Equiv_somme_arg {A A' B B' : Type} (RA : A ≈ A')
      (RB : B ≈ B') (x : A ⊔ B) : 
  Equiv ({y : A' ⊔ B' & x ≈ y}) (code_somme_arg RA RB x). 
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

Instance IsFun_somme {A A' B B' : Type} 
                       (RA : A ≈ A')
                       (RB : B ≈ B') :
                       IsFun (FR_somme RA RB).
Proof.
  intro x; induction x; isFun @Equiv_somme_arg.
Defined.

Definition code_somme_arg_sym {A A' B B' : Type} (RA : A ≈ A')
                          (RB : B ≈ B') (x : A' ⊔ B') : 
  Type :=
  match x with
    inl a' => {a:A & inl a ≈ inl a'}
  | inr b' => {b:B & inr b ≈ inr b'}
  end. 

Definition Equiv_somme_arg_sym {A A' B B' : Type} (RA : A ≈ A')
      (RB : B ≈ B') (x : A' ⊔ B') : 
  Equiv ({y : A ⊔ B & y ≈ x}) (code_somme_arg_sym RA RB x). 
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

Instance IsFun_sym_somme {A A' B B' : Type} 
                       (RA : A ≈ A')
                       (RB : B ≈ B') :
                       IsFun (sym (FR_somme RA RB)).
Proof.
  intro x; induction x; isFun @Equiv_somme_arg_sym.
Defined.

Definition FP_somme_ : somme ≈ somme.
  FP.
Defined.

Instance FP_somme {A A' B B' : Type} (eA : A ≈ A') (eB : B ≈ B') : (A ⊔ B) ⋈ (A' ⊔ B')
  := FP_somme_ A A' eA B B' eB.

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

Fixpoint FR_list {A A'} (RA : A ≈ A') (l: list A) (l': list A') : Type :=
  match l , l' with
    [] , [] => unit
  | [] , cons a' l' => empty
  | cons a l , [] => empty
  | cons a l , cons a' l' => {Xa : a ≈ a' & FR_list RA l l'}
  end.

Instance Rel_list {A A'} (RA : A ≈ A') : Rel (list A) (list A') := FR_list RA.

Definition code_list_arg {A A' : Type} (RA : A ≈ A') (l : list A) : Type :=
  match l with
    [] => [] ≈ []
  | cons a l => {a':_ & {l':_ & (a::l) ≈ (a'::l')}}
  end.

Definition Equiv_list_arg {A A' : Type} (RA : A ≈ A') (l: list A) :
      Equiv ({y : list A' & l ≈ y}) (code_list_arg RA l).
Proof.
  destruct l as [ | a l]; unfold code_list_arg; unshelve econstructor.  
  - exact (fun lr => match lr with
                         ([] ; r) => tt
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

Instance IsFun_list (A A' : Type) (RA : A ≈ A') : IsFun (FR_list RA).
Proof.
  intro l; induction l; isFun @Equiv_list_arg.  
Defined.

Definition code_list_arg_sym {A A' : Type} (RA : A ≈ A') (l' : list A') : Type :=
  match l' with
    [] => [] ≈ []
  | cons a' l' => {a:_ & {l: _ & (a::l) ≈ (a'::l')}}
  end.

Definition Equiv_list_arg_sym {A A' : Type} (RA : A ≈ A') (l': list A') :
      Equiv ({l : list A & l ≈ l'}) (code_list_arg_sym RA l').
Proof.
  destruct l' as [ | a l]; unfold code_list_arg; unshelve econstructor.  
  - exact (fun lr => match lr with
                         ([] ; r) => tt
                       | (a' :: l' ; r) => match r with end
                       end).
  - exact (fun lr => match lr with
                         ([] ; r) => match r with end
                       | (a' :: l' ; r) => (a' ; ( l' ; r)) 
                       end).
  - unshelve eapply isequiv_adjointify.
    -- intro r. exists []. exact r.
    -- intros [[| a' l'] []] ; reflexivity.
    -- intro r; destruct r. reflexivity. 
  - unshelve eapply isequiv_adjointify.
    -- intros [a' [l' r]]. exact ( a'::l' ; r).
    -- intros [[|a' l'] []]; reflexivity.
    -- intros [a' [l' []]]; reflexivity.
Defined.

Instance IsFun_sym_list (A A' : Type) (RA : A ≈ A') : IsFun (sym (FR_list RA)).
Proof.
  intro l; induction l; isFun @Equiv_list_arg_sym.  
Defined.

Definition _FP_list : @list ≈ @list.
  FP.
Defined.

Instance FP_list (A A' : Type) (eA : A ≈ A') : list A ⋈ list A'
  := _FP_list A A' eA. 

(* ###########################################################*)
(* ###                   tree A ⋈ tree A'                 ###*)
(* ###########################################################*)

Inductive tree A : Type :=
  |nil_tree : tree A
  |cons_tree : tree A -> A -> tree A -> tree A.

Arguments nil_tree {_}.
Arguments cons_tree {_} _ _ _.
  
Fixpoint FR_tree {A A' : Type} (RA : A ≈ A') (t : tree A) (t' : tree A') : Type :=
  match t, t' with
    | nil_tree , nil_tree => unit
    | nil_tree , cons_tree ls' a' rs' => empty
    | cons_tree ls a rs , nil_tree => empty
    | cons_tree ls a rs , cons_tree ls' a' rs' =>
      {Xl : FR_tree RA ls ls' & {Xa : a ≈ a' & FR_tree RA rs rs'}}
  end. 

Instance Rel_tree {A A' : Type} (RA : A ≈ A') : Rel (tree A) (tree A') := FR_tree RA. 
  
Definition code_tree_arg {A A' : Type} (RA : A ≈ A') (t : tree A) : Type :=
  match t with
  | nil_tree => nil_tree ≈ nil_tree
  | cons_tree ls a rs =>
    {ls' : _ & {a':_ & {rs' : _ & cons_tree ls a rs ≈ cons_tree ls' a' rs' }}}
  end.

Definition Equiv_tree_arg {A A' : Type} (RA : A ≈ A') (t : tree A) : 
      Equiv ({t' : tree A' & t ≈ t'}) (code_tree_arg RA t).
Proof.
  destruct t as [ | ls a rs]; cbn.
  * unshelve econstructor.
    - intros [t' r]. destruct t' as [ | ls' a' rs']; try destruct r.
      exact tt.
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

Instance IsFun_tree {A A' : Type} (RA : A ≈ A') : IsFun (FR_tree RA).
Proof.
  intro t; induction t; isFun @Equiv_tree_arg.  
Defined.

Definition code_tree_arg_sym {A A' : Type} (RA : A ≈ A') (t : tree A') : Type :=
  match t with
  | nil_tree => nil_tree ≈ nil_tree
  | cons_tree ls' a' rs' =>
    {ls : _ & {a:_ & {rs : _ & cons_tree ls a rs ≈ cons_tree ls' a' rs' }}}
  end.

Definition Equiv_tree_arg_sym {A A' : Type} (RA : A ≈ A') (t' : tree A') : 
      Equiv ({t : tree A & t ≈ t'}) (code_tree_arg_sym RA t').
Proof.
  destruct t' as [ | ls a rs]; cbn.
  * unshelve econstructor.
    - intros [t' r]. destruct t' as [ | ls' a' rs']; try destruct r.
      exact tt.
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

Instance IsFun_sym_tree {A A' : Type} (RA : A ≈ A') : IsFun (sym (FR_tree RA)).
Proof.
  intro t; induction t; isFun @Equiv_tree_arg_sym.  
Defined. 

Definition _FP_tree : @tree ≈ @tree.
Proof.
  FP.
Defined.

Instance FP_tree {A A':Type} (eA : A ≈ A') : tree A ⋈ tree A' :=
  _FP_tree _ _ eA.

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

#[export] Hint Extern 0 (Rel (?B ?a) (?B' ?a')) =>
  match goal with | H : ?R a a' , H' : _ |- _ => specialize (H' _ _ H) end
: typeclass_instances.

Fixpoint FR_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      (RA : A ≈ A')
      (RB : B ≈ B')
      (x : {a: A & B a}) (y:{a':A' & B' a'}) : Type :=
  match x , y with 
    (a ; b) , (a' ; b') => {_ : a ≈ a' & b ≈ b' }
  end.

Instance Rel_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      (RA : A ≈ A')
      (RB : B ≈ B') : Rel {a: A & B a} {a':A' & B' a'} := FR_sigma RA RB.

#[export] Hint Extern 0 (Rel (sigT _) (sigT _)) =>
 refine (Rel_sigma _ _) ; intros : typeclass_instances.

Definition code_sigma_arg {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A ≈ A')
      (RB : B ≈ B')
      (x: {a:A & B a}) : Type :=
  match x with
    (a ; b) => { a' : A' & { b' : B' a' & (a;b) ≈ (a';b')} }
  end.

Definition Equiv_sigma_arg {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A ≈ A')
      (RB : B ≈ B')
      (x: {a:A & B a}) : 
      Equiv ({y:{a':A' & B' a'} & x ≈ y}) (code_sigma_arg RA RB x).
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

Instance IsFun_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      (RA : A ≈ A')
      (RB : B ≈ B') :
      IsFun (Rel_sigma RA RB).
Proof.
  intro x; induction x; isFun @Equiv_sigma_arg.
Defined.

(* Instance is not sufficient here *)

#[export] Hint Extern 0 (IsFun (Rel_sigma _ _))  =>
refine (IsFun_sigma _ _) : typeclass_instances.

Definition code_sigma_arg_sym {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A ≈ A')
      (RB : B ≈ B')
      (x: {a':A' & B' a'}) : Type :=
  match x with
    (a' ; b') => {a:A & {b : B a & (a;b) ≈ (a';b')}}
  end.

Definition Equiv_sigma_arg_sym {A A':Type} {B : A -> Type} {B' : A' -> Type}
      (RA : A ≈ A')
      (RB : B ≈ B')
      (x: {a':A' & B' a'}) : 
      Equiv ({y:{a:A & B a} & y ≈ x})
            (code_sigma_arg_sym RA RB x).
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

Instance IsFun_sym_sigma {A A'} {B : A -> Type} {B' : A' -> Type} 
      (RA : A ≈ A') 
      (RB : B ≈ B') :
      IsFun (sym (Rel_sigma RA RB)).
Proof.
  intro x; induction x; isFun @Equiv_sigma_arg_sym.
Defined. 

(* Instance is not sufficient here *)

#[export] Hint Extern 0 (IsFun (sym (Rel_sigma _ _)))  =>
refine (IsFun_sym_sigma _ _) : typeclass_instances.

Definition _FP_sigma : @sigT ≈ @sigT.
Proof.
  intros A A' eA B B' eB. FP. 
Defined.

Instance FP_sigma (A A' : Type) (B : A -> Type) (B' : A' -> Type) 
    (eA : A ≈ A') (eB : B ≈ B') :
    {a:A & B a} ⋈ {a':A' & B' a'} := _FP_sigma A A' eA B B' eB.
