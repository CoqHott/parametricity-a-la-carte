Require Import HoTT.
Require Import HoTT_axioms.
Require Import Equiv_def.
From Coq Require Import ssreflect.


Set Universe Polymorphism.


(* ########################################################### *)
(* ###               Parametricity for CCω                 ### *)
(* ########################################################### *)





(* ########################################################### *)
(* ###                      Type ⋈ Type                   ### *)
(* ########################################################### *)

Instance FR_Type_def@{i j} : Rel@{j j j} Type@{i} Type@{i} :=
 FR_Type@{i i i i i}.

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.

Hint Extern 0 (_R _ _ _) => eassumption : typeclass_instances.

Hint Extern 0 (?x ⋈ ?y) => eassumption : typeclass_instances.

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





(* ########################################################### *)
(* ###                 Π(a:A) B ⋈ Π(a':A') B'             ### *)
(* ########################################################### *)

Definition FR_Forall {A A'} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
          (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) :
  Rel (forall x, B x) (forall y, B' y)
  :=
  fun f g => forall x y (H:x ≈ y), f x ≈ g y.

#[export] Hint Extern 0 (Rel (forall x:_ , _) (forall x:_ , _)) =>
 refine (FR_Forall _ _) ; intros : typeclass_instances.

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
  (forall x : A,
      B x) ⋈ (forall x : A', B' x).
Proof.
  unshelve econstructor. 
  * split.
    + apply IsFun_forall; typeclasses eauto.
    + eapply IsFun_sym. eapply Forall_sym_sym. apply IsFun_forall.
      - destruct eA as [RA FA]. apply IsWeakEquiv_sym. exact FA.
      - intros a' a H. destruct (eB a a' H) as [RB FB].
        apply IsWeakEquiv_sym. exact FB.
Defined.

#[export] Hint Extern 0 ((forall x : _ , _) ⋈ (forall y : _ , _)) =>
unshelve refine (FP_forall _ _ _ _ _ _) ; intros : typeclass_instances.
