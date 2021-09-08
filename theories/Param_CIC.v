Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
From Coq Require Import ssreflect.


Set Universe Polymorphism.


(* ########################################################### *)
(* ###               Parametricity for CCω                 ### *)
(* ########################################################### *)


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
  eapply equiv_compose. eapply (@swap_forall A A' _). cbn.
  eapply (@equiv_compose _ (CB == g) _). 2: apply Fune.
  apply EquivPtype; intro a'.
  (* simpl forall *)
  eapply equiv_compose. apply ForallSigma. cbn.
  eapply equiv_compose. unshelve eapply IsContrForall_domain. exact (WFsym a').
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



(* ########################################################### *)
(* ###        Parametricity for Inductive Types            ### *)
(* ########################################################### *)


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
  intro x. induction x as [a | b]; eapply contr_equiv2; 
  try (apply Equiv_inverse; apply Equiv_somme_arg); cbn.
  * exact (WFA a).
  * exact (WFB b).
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

(* shorter but less generalizable ? cf list than sigma types *)
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
  destruct l as [|a l], l' as [|a' l'].
  - exact True.
  - exact False.
  - exact False.
  - exact ({H : RA a a' & FR_list A A' RA l l'}).
Defined.

Definition code_list_arg {A A' : Type} (RA : A -> A' -> Type) (x: list A) : Type.
Proof.
  destruct x as [|a l].
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
  intro l. induction l ;
  eapply contr_equiv2 ; try (apply Equiv_inverse; apply Equiv_list_arg).
  - cbn. apply IsContr_True.
  - cbn. apply (contr_equiv2 {a':A' & RA a a'}). 2: exact (WFA a).
    eapply EquivSigma; intro a'.
    eapply Equiv_inverse. eapply equiv_compose. eapply swap_sigma.
    cbn. apply IsContrSigma_codomain. intro H. apply IHl. 
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

(* moins pratique avec inductif ? Mieux ?*)
Definition listR_sym_sym_bis A A' (R : A -> A' -> Type) :
  forall l l', FR_list R l l' ≃ sym (FR_list (sym R)) l l'.
Proof.
  intros l; induction l as [|a l]; intro l'; induction l' as [|a' l']; cbn; try (apply Equiv_id).
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
  intro x. destruct x as [a b].
  eapply contr_equiv2; try (apply Equiv_inverse; apply Equiv_sigma_arg).
  apply (contr_equiv2 {a':A' & RA a a'}). 2 : exact (WFA a).
  cbn. apply Equiv_inverse. apply EquivSigma; intros a'.
  eapply equiv_compose. apply swap_sigma. cbn.
  apply IsContrSigma_codomain; intro H. exact (WFB a a' H b).
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

(* Pratique sans inductif ? *)
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
  intros n m p v.
  eapply contr_equiv2. apply Equiv_inverse. apply Equiv_vect_arg.
  revert m p. induction v; intros m p.
  - destruct m; cbn.
    + apply IsContr_True.
    + destruct p. 
  - destruct m; cbn.
    + destruct p.
    + apply (contr_equiv2 {a':A' & RA a a'}). 2: exact (WFA a).
      eapply Equiv_inverse; cbn. eapply EquivSigma; intro a'.
      eapply equiv_compose. eapply swap_sigma. cbn.
      apply IsContrSigma_codomain. intro H.
      eapply contr_equiv2. apply Equiv_inverse. apply Equiv_vect_arg.
      exact (IHv m p). 
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

Definition FR_eq {A A':Type} (RA : A -> A' -> Type) 
    (x:A) (x':A') (p:RA x x') :
    forall y y', RA y y' -> x = y -> x' = y' -> Type.
Proof.
  intros y y' p' e e'. destruct e , e'.
  exact (p = p').
Defined. 
  (* |eqR : FR_eq RA x x' p x x' p eq_refl eq_refl. *)

Definition code_eq_arg {A A' : Type} (RA : A -> A' -> Type)
           (x:A) (x':A') (p:RA x x')
           (y:A) (y':A') (p':RA y y') (e : x = y): Type.
Proof.
  destruct e.
  + exact ({e' : x' = y' & e' # p = p' }).
Defined.

Definition Equiv_eq_arg {A A' : Type} (RA : A -> A' -> Type)
           (x:A) (x':A') (p:RA x x')
           (y:A) (y':A') (p':RA y y') (e : x = y) :
  Equiv ({e' : x' = y' & FR_eq RA x x' p y y' p' e e'})
        (code_eq_arg RA x x' p y y' p' e).
Proof.
  destruct e. unfold code_eq_arg.
  eapply EquivSigma; intros e. destruct e; cbn.
  apply Equiv_id.
Defined. 

Definition path_sigma_uncurried_eq {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & p # u.2 = v.2})
           (e : u = v) :
  e = path_sigma_uncurried P u v pq -> (e..1 ; e..2) = pq.
Proof.
  destruct u, v. cbn in *. destruct pq. cbn. destruct x1.
  destruct e0. intro E. cbn in *. rewrite E. reflexivity.
Defined. 

Definition IsFun_eq {A A':Type} (RA : A -> A' -> Type)
           (WFA : IsFun(RA))
  (x:A) (x':A') (xe:RA x x') :
  forall y y' ye, IsFun (FR_eq RA x x' xe y y' ye).
Proof.
  intros. intro e.
  eapply contr_equiv2. apply Equiv_inverse. apply Equiv_eq_arg.
  destruct e. cbn.
  assert ( (x' ; xe) = (y' ; ye)).
  1: unshelve eapply path_contr; exact (WFA x).
  unshelve econstructor. exists (X..1). exact (X..2).
  intros. 
  apply (path_sigma_uncurried_eq _ (x'; xe) (y'; ye) y X).
  unshelve eapply path2_contr. exact (WFA x).
Defined.

Definition Eq_sym_sym {A A':Type} (RA : A -> A' -> Type) (x:A) (x':A') (xe : RA x x')
    (y:A) (y':A') (ye: RA y y') :
    forall e e', Equiv (FR_eq RA x x' xe y y' ye e e') (sym (FR_eq (sym RA) x' x xe y' y ye) e e').
Proof.
  intros e e'. destruct e, e'. cbn. apply Equiv_id.
Defined.

Definition FP_eq (A A' : Type) (eA : A ⋈ A') 
    (x:A) (x':A') (xe : _R eA x x')
    (y:A) (y':A') (ye : _R eA y y') :
    eq A x y ⋈ eq A' x' y'.
Proof.
  unshelve econstructor. exact (FR_eq (_R eA) x x' xe y y' ye).
  unshelve econstructor.
  * apply IsFun_eq. typeclasses eauto.
  * unfold rel. eapply IsFun_sym. apply Eq_sym_sym. apply IsFun_eq.
    destruct eA as [RA FA]. destruct FA as [WFA WFAsym]. exact WFAsym.
Defined.

