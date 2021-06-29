Require Import ssreflect HoTT HoTT_axioms.
(* Declare ML Module "paramcoq". *)

Set Universe Polymorphism.

Class IsFun {A B} (R : A -> B -> Type) := isFun : forall x, IsContr {y:B & R x y} .

Hint Mode IsFun - - ! : typeclass_instances.

Definition sym {A B} (R : A -> B -> Type) := fun b a => R a b.

Typeclasses Opaque sym.

Class IsWeakEquiv {A B} (R : A -> B -> Type) :=
  { isWFun :> IsFun R;
    isWFunSym :> IsFun (sym R) }.

Arguments isFun {_ _ _} _.
Arguments isWFun {_ _ _} _.
Arguments isWFunSym {_ _ _} _.

Definition funR {A B R} : IsFun R -> A -> B := fun H x => (isFun H x).1.1.

Definition center {A B} {R : A -> B -> Type} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
  unfold IsFun. unshelve eapply IsTrunc_Forall. apply funext. intro x.
  eapply IsHPropIsContr.
Defined.

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Instance IsWeakEquiv_sym A B (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsWeakEquiv (sym R).
Proof.
  intros WER; unshelve econstructor.
  apply isWFunSym. assumption.
  apply isWFun. assumption.
Defined.

Definition IsWeakEquiv_IsEquiv A B (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsEquiv (funR (isWFun f)).
Proof.
  destruct f as [f g].
  unshelve eapply isequiv_adjointify.
  - exact (funR g).
  - intro x. pose (b := (funR f) x). pose (r := (center f) x).
    cbn. pose ((g b).2 (x;r)). exact (e..1).
  - intro y. pose (a := (funR g) y). pose (r := (center g) y).
    cbn. pose ((f a).2 (y;r)). exact (e..1).
Defined.

Definition IsEquiv_IsWeakEquiv A B (f : A -> B) :
  forall (e : IsEquiv f), IsWeakEquiv (fun a b => f a = b).
Proof.
  intros [g sect retr adj].
  econstructor.   
  - intros a. unshelve econstructor.
    + exists (f a). reflexivity.
    + intros [y ey]. apply path_sigma_uncurried. exists ey. 
      apply transport_paths_r. 
  - intros b. unshelve econstructor.
    + exists (g b). compute. exact (retr b). 
    + intros [a ea]. apply path_sigma_uncurried. compute in ea. 
      exists ((ap g ea)^ @ sect a). unfold sym. cbn. 
      rewrite transport_paths_Fl. destruct ea. cbn.
      rewrite adj. apply inverse. apply inverse_left_inverse. 
Defined. 
      
Definition IsFunRf A B (f : A -> B) : IsFun (fun a b => f a = b).
Proof.
  intro a. unshelve econstructor. exists (f a). reflexivity.
  intros [b e]. apply path_sigma_uncurried. unshelve eexists.
  exact e. cbn. apply transport_paths_r.
Defined.

Definition IsFunRfsymIsWeakEquiv A B (f : A -> B) : IsFun (sym (fun a b => f a = b)) -> IsWeakEquiv (fun a b => f a = b).
Proof.
  econstructor. apply IsFunRf. assumption.
Defined.


Definition IsFun_sym A A' (R R': A -> A' -> Type) :
  (forall a a', R a a' ≃ R' a a') -> IsFun R -> IsFun R'.
Proof.
  intros equiv FR. unshelve econstructor.
  - exists (funR FR x). apply equiv. apply center.
  - intros [a' r']. apply path_sigma_uncurried. unshelve eexists; cbn.
    + exact (((FR x).2 (a'; e_inv' (equiv _ _) r'))..1).
    + pose (((FR x).2 (a'; e_inv' (equiv _ _) r'))..2).
      cbn in e. set ((FR x) .2 (a'; e_inv' (equiv x a') r') ..1) in *.
      cbn in *. clearbody e e0. destruct e0. cbn in *.
      apply Move_equiv_equiv. exact e.
Defined.

Class Rel A B : Type := rel : A -> B -> Type.

Hint Mode Rel ! ! : typeclass_instances.
Typeclasses Transparent Rel.

Arguments rel {_ _ _} _ _.

Notation "x ≈ y" := (rel x y) (at level 20).

Class FR_Type A B :=
  { _Rel :> Rel A B;
    _REquiv:> IsWeakEquiv (@rel _ _ _Rel);
  }.

Infix "⋈" := FR_Type (at level 25).

Arguments _Rel {_ _} _.
Arguments _REquiv {_ _} _.
Typeclasses Transparent _Rel.

(*! Universe !*)

Instance FR_Type_def@{i j} : Rel@{j j j} Type@{i} Type@{i} :=
 FR_Type@{i i i i i}.

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.

Hint Extern 0 (_Rel _ _ _) => eassumption : typeclass_instances.

Definition FRForall {A A'} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
          (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) :
  Rel (forall x, B x) (forall y, B' y)
  :=
  fun f g => forall x y (H:x ≈ y), f x ≈ g y.

Definition IsFun_id A : IsFun (fun a a' : A => a = a').
  intro a. unshelve econstructor. exact (a; eq_refl).
  intros [b e]. apply path_sigma_uncurried. unshelve eexists.
  exact e. cbn. apply transport_paths_r.
Defined.

Definition FR_Type_id A: FR_Type_def A A.
  unshelve econstructor.
  refine (fun a a' => a = a').
  unshelve econstructor.
  apply IsFun_id.
  unfold sym, rel.
  intro a. unshelve econstructor. exact (a; eq_refl).
  intros [b e]. apply path_sigma_uncurried. unshelve eexists.
  exact e^. destruct e. reflexivity.
Defined.

Instance FP_Type : Type ⋈ Type.
Proof.
  econstructor. unfold rel. unshelve econstructor.
  intro A. unshelve econstructor.
  exists A. apply FR_Type_id.
  intros [B e]. apply path_sigma_uncurried. unshelve eexists.
  cbn. apply univalence.
  unshelve econstructor.
  exact (funR (e.(_REquiv).(isWFun))). apply IsWeakEquiv_IsEquiv.
  cbn. cheat.
  intro A. unshelve econstructor.
  exists A. apply FR_Type_id.
  intros [B e]. apply path_sigma_uncurried. unshelve eexists.
  cbn. apply univalence.
  unshelve econstructor.
  exact (funR (e.(_REquiv).(isWFunSym))).
  unfold sym in e.
  apply (IsWeakEquiv_IsEquiv _ _ _ (IsWeakEquiv_sym _ _ _ (_REquiv e))).
  cbn.
  cheat.
Defined.

Definition IsFun_forall (A A' : Type)
           (B : A -> Type) (B' : A' -> Type)
           (RA : Rel A A')
           (RB: forall x y (H: x ≈ y), Rel (B x) (B' y))
           (eAsym : IsFun (sym RA))
           (eB : forall a a' e, IsFun (RB a a' e)):
  IsFun (FRForall RA RB).
Proof.
  intro f.
  unshelve econstructor.
  - unshelve eexists.
    + intros x. apply (funR (eB ((funR eAsym) x) x (center eAsym x)) (f (funR eAsym x))).
    + intros a a' ea. cbn.
      pose (e := (eAsym a').2 (a ; ea)).
      apply (transport_eq (fun X => (RB a a' ea) (f a)
                                                  (((eB X .1 a' X .2) (f X .1)).1) .1) e^).
        exact (center (eB a a' ea) (f a)).
  - intros [g efg]. cbn in *. eapply path_sigma_uncurried.
    unshelve eexists. cbn. apply funext.
    + intros a'.
        exact ((((eB (funR eAsym a') a' (center eAsym a')) (f (funR eAsym a'))).2 (g a'; efg _ a' _))..1).
    + cbn. unfold FRForall.
      rewrite transport_forall_cst.
      apply funext; intro a; apply funext; intro a'; apply funext ; intro e. unfold rel in eB.
      rewrite (transport_funext_aux (fun y0 y  =>
                                       forall (e0 : RA a y0), (RB a y0 e0) (f a) y)).
        rewrite transport_forall_cst.
        set (T := (RB a a' e) (f a)).
        rewrite <- (transport_ap T ((fun X : {y : A & sym RA a' y} =>
                                       (((eB X .1 a' X .2)(f X .1)) .1) .1))).
        rewrite <- transport_pp.
        unfold center, funR, isFun.
        set (isContrT := (eB a a' e) (f a)).
        destruct ((eAsym a') .2 (a; e))^. cbn.
        change (transport_eq T (isContrT .2 (g a'; efg a a' e) ..1)
                             (isContrT .1) .2 = efg a a' e).
        apply transport_pr1_path.
Defined.

Hint Extern 1 (Rel (forall x:?A, _) (forall x:?A', _)) =>
  refine (@FRForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

Definition Forall_sym_sym
           {A A'} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
           (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) :
  forall f g, FRForall RA RB f g ≃ sym (FRForall (sym RA) (fun x y e => sym (RB y x e))) f g.
Proof.
  intros. unshelve econstructor; cbn.
  compute; intros; auto.
  unshelve eapply isequiv_adjointify.
  - compute; intros; auto.
  - reflexivity.
  - reflexivity.
Defined.

Definition FP_forall (A A' : Type) (eA : A ⋈ A')
           (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') :
  (forall x : A, B x) ⋈ (forall x : A', B' x).
Proof.
  unshelve econstructor.
  unshelve eapply FRForall.
  intros. eapply eB. typeclasses eauto.
  split.
  apply IsFun_forall; typeclasses eauto.
  eapply IsFun_sym. eapply Forall_sym_sym.
  apply IsFun_forall. destruct eA. destruct _REquiv0. assumption.
  intros. destruct (eB a' a e). destruct _REquiv0. assumption.
Defined.

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Infix "::" := cons (at level 60, right associativity).

Parametricity list.
Arguments list_R {A B} : rename.
Arguments list_R_nil_R {A B} : rename.
Arguments list_R_cons_R {A B} : rename.

Definition IsFun_list (A A' : Type) (eA : A -> A' -> Type)
           (FA : IsFun eA) : IsFun (list_R eA).
Proof.
move=> l; pose f := (list_rect A (fun _ => list A') []
                      (fun a _ l' => cons (funR FA a) l')).
unshelve eexists (f l; _).
- elim: l => //= [|a l fl]; first exact: list_R_nil_R.
  by apply: list_R_cons_R => //; apply: center.
- move=> [l']; elim=> //= a b r {l}l {l'}l' ell'.
  change b with (b; r).1; change r with (b; r).2.
  elim: _ / (((FA a).2 (b; r))).
  change l' with (l'; ell').1; change ell' with (l';ell').2.
  by elim : _ /.
Defined.

Definition list_R_sym_sym A A' (R : A -> A' -> Type) :
  forall l l', list_R R l l' ≃ sym (list_R (sym R)) l l'.
Proof.
unshelve econstructor.
  induction 1; constructor; assumption.
unshelve eapply isequiv_adjointify.
- induction 1; constructor; assumption.
- intro e; induction e; cbn; [reflexivity|exact: ap].
- intro e; induction e; cbn; [reflexivity|exact: ap].
Defined.

Definition FP_list (A A' : Type) (eA : A ⋈ A'):
  list A ⋈ list A'.
Proof.
  unshelve econstructor.
  exact (list_R (_Rel eA)).
  split.
  apply IsFun_list; apply eA.
  eapply IsFun_sym.
    eapply list_R_sym_sym.
  apply IsFun_list; apply eA.
Defined.
