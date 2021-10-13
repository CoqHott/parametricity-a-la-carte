(************************************************************************)
(* This files introduced basic ingredients of HoTT, most of them already *)
(* presents in https://github.com/HoTT. We have created our own library *)
(* to be independent from their framework which requires a tailored version of Coq  *)
(************************************************************************)

Set Universe Polymorphism.

Notation id := (fun x => x). 

Notation compose := (fun g f x => g (f x)).

Inductive SFalse : SProp := .

Inductive STrue : SProp := SI : STrue.

Inductive Box (A : SProp) : Type := box : A -> Box A.

Arguments box {_} _.

Definition unbox {A:SProp} : Box A -> A := Box_sind A (fun _ => A) id.

Inductive sigP {A:Type} (P:A -> SProp) : Type :=
    existP : forall x:A, P x -> sigP P.

Arguments existP {_} _ _.

Inductive Sprod (A B : SProp) : SProp :=  Spair : A -> B -> Sprod A B.

Arguments Spair {_ _} _ _.

Notation "x ** y" := (Sprod x y) (at level 40) : type_scope.
Notation "( x ,, y ,, .. ,, z )" := (Spair .. (Spair x y) .. z): type_scope.

Inductive prod (A B : Type) : Type :=  pair : A -> B -> prod A B.
Arguments pair {_ _} _ _.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z): type_scope.

Section projections.
  Context {A : SProp} {B : SProp}.

  Definition Sfst (p:A ** B) : A := Sprod_sind _ _ (fun _ => A) (fun x y => x) p.

  Definition Ssnd (p:A ** B) : B := Sprod_sind _ _ (fun _ => B) (fun x y => y) p.

End projections.

Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p:A * B) : A := prod_rect _ _ (fun _ => A) (fun x y => x) p.
  Definition snd (p:A * B) : B := prod_rect _ _ (fun _ => B) (fun x y => y) p.

End projections.

Inductive unit : Type := tt. 

Inductive empty : Type :=. 

Inductive eq@{i} (A:Type@{i}) (x:A) : A -> SProp :=
    eq_refl : eq A x x.

Notation "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Arguments eq_refl {_ _}. 

Definition projP1 {A} {P:A -> SProp} (p:sigP P) : A :=
  sigP_rect _ _ (fun _ => A) (fun x y => x) p.

Definition projP2  {A} {P:A -> SProp} (p:sigP P) : P (projP1 p) :=
  sigP_sind _ _ (fun x => P (projP1 x)) (fun x y => y) p.

Notation "g ∘ f" := (compose g%function f%function) (at level 1): function_scope.
(* Notation "g ∘ f" := (compose f g) (at level 1). *)

Notation "{ x : A & P }" := (sigP (A:=A) (fun x => P)) : type_scope.
Notation " ( x ; p ) " := (existP _ x p).

Notation "x .1" := (projP1 x) (at level 3).
Notation "x .2" := (projP2 x) (at level 3).

Notation "f == g" := (forall x, f x = g x) (at level 3).

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.

Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with eq_refl => match q with eq_refl => eq_refl end end.

Definition ap3 {A A' A'' B:Type} (f:A -> A' -> A'' -> B) {x y:A} (p:x = y)
  {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'') : f x x' x''= f y y' y''
  := match p with eq_refl => match p' with eq_refl => match p'' with eq_refl => eq_refl end end end.

Definition ap4 {A A' A'' A''' B:Type} (f:A -> A' -> A'' -> A''' -> B) {x y:A} (p:x = y)
           {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'')
           {x''' y''':A'''} (p''':x''' = y''') : f x x' x'' x'''= f y y' y'' y'''
  := match p with eq_refl =>
     match p' with eq_refl =>
     match p'' with eq_refl =>
     match p''' with eq_refl => eq_refl end end end end.


Definition eq_sym {A} {x y : A} (H : x = y) : y = x :=
  match H with eq_refl => eq_refl end.
(* ET: the [in ... return ...] does not seem needed *)
(* match H in (_ = y0) return (y0 = x) with *)
(* | eq_refl => eq_refl *)
(* end. *)

(* Instance EqSymm A : Symmetric (eq A) := @eq_sym A. *)

(* From HoTT/Coq *)

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with eq_refl => eq_refl  end.

Definition transport_eq {A : Type} (P : A -> SProp) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with eq_refl => u end.

Notation "p # x" := (transport_eq _ p x) (right associativity, at level 65, only parsing).

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  destruct p; exact q.
Defined.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with eq_refl => eq_refl end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Definition transportD {A : Type} (B : A -> SProp) (C : forall a:A, B a -> SProp)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y). destruct p. exact z. Defined. 

Definition transportD2 {A : Type} (B : A -> SProp) (B' : A -> SProp) (C : forall a:A, B a -> B' a -> SProp)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)  (y' : B' x1) (z : C x1 y y')
  : C x2 (p # y) (p # y'). destruct p. cbn. exact z. Defined. 

Definition transportD3 {A : Type} (B : A -> SProp) (B' : A -> SProp) (B'' : forall a:A, B a -> B' a -> SProp)
           (C : forall (a:A) (x: B a) (y: B' a), B'' a x y -> SProp)
  {x1 x2 : A} (p : x1 = x2) y y' y'' (z : C x1 y y' y'')
  : C x2 (p # y) (p # y') (transportD2 _ _ _ p _ _ y'').
  destruct p. cbn. exact z. Defined. 

(* Definition transport_double A (P : A -> A -> SProp) x y (e : x = y) (f : forall a, P a a) : *)
(*   transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e (f x)) = f y.   *)
(*   destruct e. reflexivity. *)
(* Defined. *)

(* Definition transport_forall A (B:A->SProp) (f : forall x : A , B x)  y z (e : z = y) : *)
(*   (* ET: why not [e # (f z) = f y]. *) *)
(*                 transport_eq B e (f z) = *)
(*                 f y. *)
(* Proof. *)
(*   reflexivity.  *)
(* Defined. *)

(* Definition transport_forall2 (P:Type->Type) A A' B (f : P A -> P A') (y z : P A) (H : z = y) *)
(*                  (g : forall x , B A x -> B A' (f x))  *)
(*                  (h : forall x , B A x) : *)
(*                  (transport_eq (B _) (ap _ H) *)
(*                                (g z (h z))) = *)
(*                  g y (h y). *)
(* Proof. *)
(*   destruct H; reflexivity. *)
(* Defined. *)

(* Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) : *)
(*   p @ q # u = q # p # u. *)
(*   destruct  *)
(*     := *)
(*   match q with eq_refl => *)
(*     match p with eq_refl => eq_refl end *)
(*   end. *)

(* Definition inverse_left_inverse A (x y : A) (p : x = y) : eq_refl = (p ^ @ p). *)
(* Proof. destruct p; reflexivity. Defined. *)

(* Definition transport_pV {A : Type} (P : A -> Prop) {x y : A} (p : x = y) (z : P y) *)
(*   : p # p^ # z = z. *)
(* Proof. *)
(*   destruct p; reflexivity. *)
(* Defined. *)

(* Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y) *)
(*   : p^ # p # z = z. *)
(* Proof. *)
(*   destruct p; reflexivity. *)
(* Defined. *)
                   

Definition path_sigma_uncurried {A : Type} (P : A -> SProp) (u v : sigP P) (pq : u.1 = v.1)
: u = v.
Proof.
  destruct u, v. simpl in *. destruct pq. reflexivity.
Defined.

Definition pr1_path {A} `{P : A -> SProp} {u v : sigP P} (p : u = v) : u.1 = v.1 := ap projP1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

Definition path_prod_uncurried {A B : Type} (u v : A * B)
           (pq : (fst u = fst v) ** (snd u = snd v))
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition unpack_prod {A B: Type} `{P : A * B -> Type} (u : A * B) :
  P (fst u , snd u) -> P u.
  destruct u. exact id. 
Defined.

Definition pack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u).
  destruct u; exact id.
Defined. 


(* equivalences *)


Class IsEquiv {A : Type} {B : Type} (f : A -> B) := BuildIsEquiv {
  e_inv :> B -> A ;
  e_sect : forall x, e_inv (f x) = x;
  e_retr : forall y, f (e_inv y) = y;
}.

(** A class that includes all the data of an adjoint equivalence. *)
Class Equiv A B := BuildEquiv {
  e_fun :> A -> B ;
  e_isequiv :> IsEquiv e_fun
}.

Notation "A ≃ B" := (Equiv A B) (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_inv {_ _} _ {_} _.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_isequiv {_ _ _}.

Typeclasses Transparent e_fun e_inv.

Coercion e_fun : Equiv >-> Funclass.

Definition univalent_transport {A B : Type} {e: A ≃ B} : A -> B := e_fun e.  

Notation "↑" := univalent_transport (at level 65, only parsing).

(* Instance IsEquiv_Equiv A B (e:A ≃ B) : IsEquiv (e_fun e) := e_isequiv (Equiv:=e). *)

Definition e_inv' {A B : Type} (e : A ≃ B) : B -> A := e_inv (e_fun e).
Definition e_sect' {A B : Type} (e : A ≃ B) := e_sect (e_fun e).
Definition e_retr' {A B : Type} (e : A ≃ B) := e_retr (e_fun e).

Definition issect'  {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g ∘ f == id) (isretr : f  ∘ g == id) :=
  fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

Definition Equiv_id A : A ≃ A := 
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => eq_refl) (fun _ => eq_refl)).

Definition isequiv_compose A B C f g `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (g ∘ f).
Proof.
  unshelve econstructor. 
  - exact ((e_inv f) ∘ (e_inv g)).
  - exact (fun a => ap (e_inv f) (e_sect g (f a)) @ e_sect f a).
  - exact (fun c => ap g (e_retr f (e_inv g c)) @ e_retr g c).
Defined.

Definition equiv_compose {A B C : Type} (f: A ≃ B) (g : B ≃ C) 
  : A ≃ C 
  := BuildEquiv A C ((e_fun g) ∘ (e_fun f)) (isequiv_compose _ _ _ _ _).

Notation "g ∘∘ f" := (equiv_compose f g) (at level 50).

Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.
                                                 
Definition isequiv_inverse : IsEquiv (e_inv f) 
    := BuildIsEquiv _ _ (e_inv f) f (e_retr f) (e_sect f).
End EquivInverse.

Definition Equiv_inverse {A B : Type} (e: A ≃ B) : B ≃ A := BuildEquiv _ _ (e_inv (e_fun e)) (isequiv_inverse _).  

Definition Move_equiv {A B} (e : A ≃ B) x y : x = e_inv' e y -> e_fun e x = y.
Proof.
  intro X. apply (ap (e_fun e)) in X. exact (X @ e_retr' e _).
Defined.

Definition Move_equiv' {A B} (e : A ≃ B) x y : e_fun e x = y -> x = e_inv' e y.
Proof.
  intro X. apply (ap (e_inv' e)) in X. exact ((e_sect' e _)^ @ X).
Defined.

(* Definition transport_e_fun A B (P : A -> SProp) a a' (e : a = a') (e' : P a ≃ B) x *)
(*     : *)
(*       e_fun e' (transport_eq P e^ x) = *)
(*       e_fun (transport_eq (fun X => P X ≃ _) e e') x. *)
(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)

(* Definition transport_e_fun' A B (P : A -> Type) a a' (e : a = a') (e' : B ≃ P a) x *)
(*     : *)
(*       transport_eq P e (e_fun e' x) = *)
(*       e_fun (transport_eq (fun X => _ ≃ P X) e e') x. *)
(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)


Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  intro X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Defined.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  intro X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Defined.

(* Definition IsEquiv_ap A (P : A -> SProp) {x y : A} (p : x = y) (u v : P x) *)
(*   : IsEquiv (@ap _ _ (fun (X : P x) => p # X) u v). *)
(* Proof.  *)
(*   unshelve econstructor; cbn.  *)
(*   - intros. destruct p. exact H. *)
(*   - intro e. cbn. reflexivity.  *)
(*   - intro e. destruct p. cbn. apply ap_id. *)
(* Defined.  *)

(**

Hedberg theorem is a standard theorem of HoTT: it states that if a
type [A] has decle equality, then it is a hSet, i.e. its equality
is proof-irrelevant. See the proof at [https://github.com/HoTT] in
[HoTT/theories/Basics/Decidable.v] *)

Inductive Ssum (A B : SProp) : SProp :=
| inl : A -> Ssum A B
| inr : B -> Ssum A B. 

Notation "x + y" := (Ssum x y) : type_scope.

Class DecidableEq A := { dec_paths : forall a b : A, (a = b) + (a = b -> SFalse)}.

Definition logic_eq_is_eq {A} {x y:A} : @Logic.eq A x y -> x = y.
Proof.
  destruct 1. reflexivity.
Defined. 
 
Instance DecidableEq_eq_nat : DecidableEq nat.
constructor. intros x y; revert y. 
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (ap S H).
    intro H; right. intro e. inversion e. apply (H (logic_eq_is_eq H1)).
Defined.

Instance DecidableEq_eq_bool : DecidableEq bool.
constructor. intros x y; revert y. induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- destruct y.
 + right; intro H; inversion H.
 + left ;reflexivity.
Defined.

Definition isequiv_ap (A B:Type) {H : A ≃ B} a a' :
  (e_fun H a = e_fun H a') -> (a= a').
Proof.
  - intro X. apply (ap (e_inv' H)) in X. exact ((e_sect' H a)^ @ X @ e_sect' H _).
Defined.

Definition DecidableEq_equiv A B (eB : A ≃ B) `{DecidableEq A} : DecidableEq B. 
Proof.
  constructor. pose (eB' := Equiv_inverse eB).
  intros x y. destruct (dec_paths (↑ x) (↑ y)). 
  - left. apply (@isequiv_ap _ _ eB'). exact e.
  - right. intro e. apply s. exact (ap _ e).
Defined. 

(*** Some Equivalences for types *)

Notation "A <-> B" := ((A -> B) ** (B -> A)) : type_scope. 

Definition EquivSigmaNoDep {A A' : Type} {B B' : SProp} 
           (HA : Equiv A A')
           (HB : B <-> B') :
  Equiv {a:A & B} {a':A' & B'}.
Proof.
  unshelve econstructor. 
  * intros [x y]. exact (HA x; Sfst HB y). 
  * unshelve econstructor.
    + intros [x y]. refine (e_inv HA x; Ssnd HB y).
    + intros [x y]. apply path_sigma_uncurried. exact (e_sect HA x).
    + intros [x y]. apply path_sigma_uncurried. exact (e_retr HA x).
Defined. 

Definition EquivSigmaGen {A A' : Type} {B : A -> SProp} {B': A' -> SProp} 
           (HA : Equiv A A')
           (HB : forall a, (B a) <-> (B' (HA a))) :
  Equiv {a:A & B a} {a':A' & B' a'}.
Proof.
  unshelve econstructor. 
  * intros [x y]. exact (HA x; Sfst (HB x) y). 
  * unshelve econstructor. 
  + intros [x y]. refine (e_inv HA x; Ssnd (HB (e_inv HA x)) _).
    refine (transport_eq B' _ y). apply inverse. exact (e_retr HA x).
  + intros [x y]. apply path_sigma_uncurried. exact (e_sect HA x).
  + intros [x y]. apply path_sigma_uncurried. exact (e_retr HA x).
Defined. 

Definition EquivSigma {A : Type} {B B' : A -> SProp} 
  (H : forall a:A, (B a) <-> (B' a)) : Equiv {a:A & B a} {a:A & B' a}.
Proof.
  unshelve econstructor. 
  * intros [x y]. exact (x; Sfst (H x) y). 
  * unshelve econstructor.
    + intros [x y]. exact (x; Ssnd (H x) y).
    + intros [x y]. reflexivity. 
    + intros [x y]. reflexivity.
Defined.


(* Definition swap_sigma {A B : Type} {Q : A -> B -> SProp} : *)
(*     Equiv {a:A & {b:B & Q a b}} {b:B & {a:A & Q a b}}. *)
(* Proof. *)
(*     unshelve econstructor. *)
(*     - intros [a q]. destruct q as [b r]. exact (b; (a; r)). *)
(*     - unshelve eapply isequiv_adjointify. *)
(*       -- intros [b q]. destruct q as [a r]. exact (a; (b; r)). *)
(*       -- intros [a q]. destruct q as [b r]. reflexivity. *)
(*       -- intros [b q]. destruct q as [a r]. reflexivity. *)
(* Defined. *)

Definition swap_forall {A B : Type} {Q: A->B->SProp} : 
  (forall (a:A) (b:B), Q a b) <-> (forall (b:B) (a:A), Q a b).
Proof.
  unshelve econstructor; intros; auto. 
Defined.

(*


(* Instance DecidableEq_Sigma A (B : A -> Type) `{DecidableEq A} `{forall a, DecidableEq (B a)} : *)
(*   DecidableEq {a : A & B a}. *)
(* Proof. *)
(*   constructor. intros [a b] [a' b' ]. *)
(*   destruct (dec_paths a a'). *)
(*   - destruct e. destruct (dec_paths b b'). *)
(*     + apply inl. apply path_sigma_uncurried. exists eq_refl. exact e. *)
(*     + apply inr; intro Hf; apply f. pose (Hf..2). *)
(*       assert (Hf..1 = eq_refl). apply is_hset. rewrite X in e. exact e. *)
(*   - apply inr; intro Hf; apply f. exact (Hf..1). *)
(* Defined. *)
                
Definition Move_equiv_equiv {A B} (e : A ≃ B) x y : (x = e_inv' e y) ≃ (e_fun e x = y).
Proof.
  apply (transport_eq (fun X =>  (x = e_inv' e y) ≃ (e x = X)) (e_retr _ y)).
  apply isequiv_ap.
Defined.

Definition isequiv_sym (A:Type) (a a':A) :
  (a = a') ≃ (a' = a).
Proof.
  unshelve econstructor.
  apply inverse.
  unshelve refine (isequiv_adjointify _ _ _ _ ).
  - apply inverse. 
  - intro. cbn. apply inv2.
  - intro. cbn. apply inv2.
Defined.


Definition transport_equiv A X (a b:A) Q (e : a = b) (x : Q a) (e' : Q b ≃ X):
  e_fun e' (transport_eq Q e x) =
  e_fun
    (transport_eq (fun X : A => Q X ≃ _) e^
       e') x.
Proof.
  destruct e. reflexivity.
Defined.




Definition transport_paths_naturality' {A : Type} {g : A -> A} {y1 y2 : A} 
  (p : y1 = y2) (q : forall x, g x = x)
  : (q _) @ p = (ap g p) @ q _.
Proof.
  destruct p. apply concat_refl.
Defined.

Instance isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p. apply (@e_isequiv _ _ (Equiv_id _)).
Defined.


Definition transport_inverse A B (a b : A) (c : B) P (EE : a = b) (XX : Type) (XXX : XX ≃ (P c a)):
      Equiv_inverse (transport_eq (fun X : A => XX ≃ (P c X)) EE XXX) =
      transport_eq (fun X : A => (P c X) ≃ XX) EE (Equiv_inverse XXX).
  destruct EE; reflexivity.
Defined. 

Definition transport_inverse' A B (a b : A) (c:B) P (EE : a = b) (XX : Type) (XXX : (P c a) ≃ XX):
      Equiv_inverse (transport_eq (fun X : A => (P c X) ≃ XX) EE XXX) =
      transport_eq (fun X : A => XX ≃ (P c X)) EE (Equiv_inverse XXX).
  destruct EE; reflexivity.
Defined. 

Definition transport_fun_eq A (a:A) P (f : forall a', a = a' -> P a') b c (e : b = c) (e' : a = b):
  transport_eq P e (f b e') = f c (e' @ e).
Proof.
  destruct e. cbn. rewrite concat_refl. reflexivity.
Defined.



Definition transport_forall_cst {A B} 
           (P : A -> B -> Type) b b' (e: b = b')
           (v : forall x, P x b) 
            : (transport_eq (fun y => forall x, P x y) e v)
            = fun x => transport_eq (fun y => P x y) e (v x).
Proof.
  destruct e; reflexivity. 
Defined.


Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
: transport_eq (fun x => { y : B x & C x y }) p yz
  = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
: transport_eq (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport_eq (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

Definition transport_pr1_path A (B:A->Type) 
           (X Y : {a:A & B a}) (e : X = Y) :
  transport_eq B (e..1) X.2 = Y .2. 
Proof. 
  destruct e. reflexivity.
Defined. 

*)
