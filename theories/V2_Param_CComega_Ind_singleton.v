Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
From Coq Require Import ssreflect.
From Equations Require Import Equations.

Set Universe Polymorphism.


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
          -- set d := (e_retr (EquivRabCenter WFA a a') H).
             set e := ap (fun H => funR (WFB a a' H) b) d.
             exact (e@r).
        - intros [p r]. cbn zeta beta.
          apply path_sigma_uncurried; unshelve econstructor.
          -- exact (e_sect (EquivRabCenter WFA a a') p).
          -- rewrite (@transport_paths_Fl _ _ (fun p0 : funR WFA a = a' =>
                funR (WFB a a' (EquivRabCenter WFA a a' p0)) b)).
              rewrite concat_p_pp. rewrite e_adj. rewrite -ap_compose.
              now rewrite inv_inv.
        - intros [H R]. cbn beta zeta.
          apply path_sigma_uncurried; unshelve econstructor.
          -- exact (e_retr (EquivRabCenter WFA a a') H).
          -- rewrite transport_paths_Fl concat_p_pp.
             now rewrite inv_inv.
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



(*** Vect(A) ⋈ Vect(A') ***)
Inductive vect (A:Type) : nat -> Type :=
  |nil_vect : vect A 0
  |cons_vect : forall n:nat, A -> vect A n -> vect A (S n).

Arguments nil_vect {_}.
Arguments cons_vect {_ _} _ _.

Notation "[| |]" := nil_vect (format "[| |]").
Notation "[| x |]" := (cons_vect x nil_vect).

Infix "□" := cons_vect (at level 60, right associativity).

Inductive FR_vect {A A':Type} (RA : A ->A' -> Type) : 
      forall n m, n = m -> (vect A n) -> (vect A' m) -> Type :=
  |nil_vectR : FR_vect RA 0 0 (eq_refl) ([| |]) ([| |])
  |cons_vectR : forall {n m a a' v v'} (p:n = m), RA a a' -> FR_vect RA n m p v v' -> FR_vect RA (S n) (S m) (ap S p) (a □ v) (a' □ v').

Definition Vect_center {A A':Type} (RA : A ->A' -> Type) (WFA : IsFun(RA)):
    forall n, vect A n -> vect A' n.
Proof.
  intros n v. induction v.
  - exact [||].
  - exact ((funR WFA a) □ IHv).
Defined.

Definition Vect_code {A : Type} (n m : nat) (p : n = m) (v : vect A n ) (v' : vect A m) : Type.
Proof.
  destruct v, v'. 
  - exact True.
  - exact False.
  - exact False.
  - inversion p. destruct H0. exact (prod (a = a0) (v = v')).
Defined.


(* MEME PBL :
  On a besoin de dst p pour =
  On a besoin de m pour les ind ! *)
Definition IsFun_vect {A A':Type} (RA : A -> A' -> Type) (WFA : IsFun(RA)) :
  forall n m p, IsFun(FR_vect RA n m p).
Proof.
  intros n m p. intro v. inversion p. destruct H.
  apply (contr_equiv2 {v' : vect A' n & Vect_center RA WFA n v = v'}).
  2 : apply IsContrSingleton_r.
  unshelve econstructor.
  - intros [v' r].
Admitted.


     

