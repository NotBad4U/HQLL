From HB Require Import structures.
From mathcomp Require Import all_boot ssralg ssrnum reals constructive_ereal.

(**md**************************************************************************)
(* # Syntax of HQLL                                                           *)
(*                                                                            *)
(* The syntax of HQLL (Section "Syntax" of main.typ): a simply typed          *)
(* lambda-calculus in the style of Church's simple theory of types as         *)
(* mechanised in HOL, over a signature of typed constants.  Formulas are the  *)
(* terms of type [TOmega]; every logical operator, quantifiers included, is a *)
(* constant applied to its arguments, and binder notation is sugar.           *)
(*                                                                            *)
(* Terms are intrinsically typed, with de Bruijn indices: a term              *)
(* [M : tm Σ Γ A] is a derivation of the paper's judgement [Γ ⊢ M : A], so    *)
(* the four typing rules Var/Con/Abs/App are the four constructors of [tm],   *)
(* a context is a list of types, and the side condition that the variables    *)
(* of a context be distinct disappears.                                       *)
(*                                                                            *)
(* The signature Σ of the paper is the fixed table of constants plus one      *)
(* family [sample_mu : TMeas A] indexed by the s-finite measures mu on [[A]]. *)
(* The syntax does not know the semantics, so these indices are abstracted    *)
(* into a family of symbols [meas Σ A]; the model instantiates [meas Σ A]     *)
(* with the s-finite measures on [[A]].                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*                   ty == types:  TUnit | TReal | TOmega | A × B | A → B     *)
(*                         | TMeas A   (the s-finite measure type 𝒯 A)         *)
(*               Pred A == A → TOmega, predicates on A                        *)
(*          signature R == model-dependent part of the signature: the family  *)
(*                         [meas A] of symbols for constant s-finite measures  *)
(*                         (R is the realType the softness p lives in)        *)
(*            const Σ A == constants of type A (Table tab:sig)                 *)
(*                  ctx == typing contexts, lists of types                     *)
(*              var Γ A == de Bruijn variables of type A in Γ                  *)
(*             tm Σ Γ A == terms of type A in context Γ (derivations of        *)
(*                         Γ ⊢ M : A); constructors Var, Con, Abs, App         *)
(*            ren Γ Δ, rename rho M == renamings and their action on terms    *)
(*            sub Γ Δ, subst sigma M == substitutions and their action        *)
(*             weaken M == M in a context extended by one variable            *)
(*               M.[N] == M[N/x], substitution for the last variable          *)
(*   Star, Pair, Fst, Snd, Zero, One, Tens, Plus, Inv, Pow p, Int, Ret, Bind, *)
(*   Sample mu, Factor, Mass, Norm                                            *)
(*                      == the constants of Σ applied to their arguments       *)
(*   Infty, Bot, Top, CoTens, Limp, Por p, Pand p, Exists p, Forall p         *)
(*                      == the derived constants (D1)--(D9)                    *)
(*   qbind Q nu phi, Int_x nu phi, Exists_x p nu phi, Forall_x p nu phi       *)
(*                      == binder sugar  Q (x ~ nu). phi  :=  Q nu (λx. phi)   *)
(*     Letin M N, M ;; N == let x <- M in N  and  M ; N                        *)
(* ```                                                                        *)
(*                                                                            *)
(* Notations (scope [hqll_scope], key [hqll]):                                *)
(* ```                                                                        *)
(*   ⟨ M , N ⟩   M ⊗ N   M ⊕ N   M `*   M ⊗* N   M -o N   M ∨ [ p ] N        *)
(*   M ∧ [ p ] N   M.[N]   M ;; N                                             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Types *)

(** A, B ::= 1 | RR | Omega | A × B | A → B | 𝒯 A *)
Inductive ty : Type :=
| TUnit                 (** the unit type 1 *)
| TReal                 (** RR, the type of individuals (standard Borel) *)
| TOmega                (** Omega, the type of truth values *)
| TProd of ty & ty      (** A × B *)
| TArr of ty & ty       (** A → B *)
| TMeas of ty.          (** 𝒯 A, s-finite measures on A *)

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.

Notation "A × B" := (TProd A B) (at level 40, left associativity) : ty_scope.
Notation "A → B" := (TArr A B)
  (at level 99, right associativity, B at level 200) : ty_scope.

Local Open Scope ty_scope.

(** The type of predicates on A. *)
Definition Pred (A : ty) : ty := A → TOmega.

(** Types have decidable equality. *)
Fixpoint ty_eqb (A B : ty) : bool :=
  match A, B with
  | TUnit, TUnit | TReal, TReal | TOmega, TOmega => true
  | TProd A1 A2, TProd B1 B2 | TArr A1 A2, TArr B1 B2 =>
      ty_eqb A1 B1 && ty_eqb A2 B2
  | TMeas A1, TMeas B1 => ty_eqb A1 B1
  | _, _ => false
  end.

Lemma ty_eqP : Equality.axiom ty_eqb.
Proof.
elim=> [| | |A1 IH1 A2 IH2|A1 IH1 A2 IH2|A1 IH1] [| | |B1 B2|B1 B2|B1] /=;
  try by constructor.
- by apply: (iffP andP) => [[/IH1-> /IH2->] //|[<- <-]];
    split; [exact/IH1|exact/IH2].
- by apply: (iffP andP) => [[/IH1-> /IH2->] //|[<- <-]];
    split; [exact/IH1|exact/IH2].
- by apply: (iffP (IH1 _)) => [->|[->]].
Qed.

HB.instance Definition _ := hasDecEq.Build ty ty_eqP.

(* Arguments determined by the conclusion alone, i.e. the type indices of the *)
(* constants and the context of a closed term, are declared implicit by hand  *)
(* below (Rocq only infers implicits from later arguments), and maximally     *)
(* inserted, so that [Zero : tm Σ Γ TOmega] and [vz : var (A :: Γ) A].        *)

(** * Contexts and variables *)

(** Contexts Γ ::= ◇ | Γ, x : A.  Variables are positions, so a context is
    a list of types; the last declared variable is the head of the list. *)
Definition ctx := seq ty.

(** De Bruijn variables: [vz] is the last variable declared in the context,
    [vs x] is the variable [x] of the tail. *)
Inductive var : ctx -> ty -> Type :=
| vz Γ A : var (A :: Γ) A
| vs Γ A B : var Γ A -> var (B :: Γ) A.
Arguments vz {Γ A}.
Arguments vs {Γ A B}.

(** Renamings. *)
Definition ren (Γ Δ : ctx) := forall A, var Γ A -> var Δ A.

Definition ren_id Γ : ren Γ Γ := fun A x => x.
Arguments ren_id {Γ}.

(** Weakening by one variable. *)
Definition ren_wk Γ B : ren Γ (B :: Γ) := fun A x => @vs _ _ B x.
Arguments ren_wk {Γ} B.

(** Lifting a renaming under a binder. *)
Definition ren_lift Γ Δ B (rho : ren Γ Δ) : ren (B :: Γ) (B :: Δ) :=
  fun A (x : var (B :: Γ) A) =>
    match x in var Γ' A' return
      (match Γ' return Type with
       | [::] => unit
       | B' :: Γ0 => ren Γ0 Δ -> var (B' :: Δ) A'
       end)
    with
    | @vz _ _ => fun _ => vz
    | @vs _ _ _ y => fun rho => vs (rho _ y)
    end rho.
Arguments ren_lift {Γ Δ B}.

(** * Signature and terms *)

(** The model-dependent part of the signature: [meas A] are the symbols for
    the constant s-finite measures mu on [[A]] that index [sample_mu].  The
    parameter [R] fixes the reals in which the softness indices p live. *)
Record signature (R : realType) := Signature { meas : ty -> Type }.
Arguments Signature : clear implicits.

Declare Scope hqll_scope.
Delimit Scope hqll_scope with hqll.

Section Terms.
Context {R : realType} {Σ : signature R}.

(** The constants of the signature Σ (Table tab:sig), as families indexed
    by types A, B, by a softness p ∈ [-oo, oo] and by measure symbols mu. *)
Inductive const : ty -> Type :=
| CStar : const TUnit                                   (** ∗ *)
| CPair A B : const (A → B → A × B)                     (** pair *)
| CFst A B : const (A × B → A)                          (** π1 *)
| CSnd A B : const (A × B → B)                          (** π2 *)
| CZero : const TOmega                                  (** 0 *)
| COne : const TOmega                                   (** 1 *)
| CTens : const (TOmega → TOmega → TOmega)              (** ⊗ *)
| CPlus : const (TOmega → TOmega → TOmega)              (** ⊕ *)
| CInv : const (TOmega → TOmega)                        (** (-)^* *)
| CPow (p : \bar R) : const (TOmega → TOmega)           (** (-)^p *)
| CInt A : const (TMeas A → (A → TOmega) → TOmega)      (** ∫_A *)
| CRet A : const (A → TMeas A)                          (** return *)
| CBind A B : const (TMeas A → (A → TMeas B) → TMeas B) (** bind *)
| CSample A (mu : meas Σ A) : const (TMeas A)           (** sample_mu *)
| CFactor : const (TOmega → TMeas TUnit)                (** factor *)
| CMass : const (TMeas TUnit → TOmega)                  (** mass *)
| CNorm A : const (TMeas A → TMeas A).                  (** norm *)
#[global] Arguments CPair {A B}.
#[global] Arguments CFst {A B}.
#[global] Arguments CSnd {A B}.
#[global] Arguments CInt {A}.
#[global] Arguments CRet {A}.
#[global] Arguments CBind {A B}.
#[global] Arguments CSample {A} mu.
#[global] Arguments CNorm {A}.

(** Terms M, N ::= x | c | M N | λx : A. M, intrinsically typed.  The
    constructors are the typing rules:
<<
      (Var) Γ, x : A, Γ' ⊢ x : A          (Con) (c : A) ∈ Σ  ⇒  Γ ⊢ c : A
      (Abs) Γ, x : A ⊢ M : B  ⇒  Γ ⊢ λx : A. M : A → B
      (App) Γ ⊢ M : A → B,  Γ ⊢ N : A  ⇒  Γ ⊢ M N : B
>>
    Formulas are the terms of type [TOmega], predicates on A those of type
    [Pred A]. *)
Inductive tm (Γ : ctx) : ty -> Type :=
| Var A : var Γ A -> tm Γ A
| Con A : const A -> tm Γ A
| Abs A B : tm (A :: Γ) B -> tm Γ (A → B)
| App A B : tm Γ (A → B) -> tm Γ A -> tm Γ B.
#[global] Arguments Con {Γ A}.

Bind Scope hqll_scope with tm.

(** ** Renaming and substitution *)

Fixpoint rename Γ Δ A (rho : ren Γ Δ) (M : tm Γ A) : tm Δ A :=
  match M with
  | Var _ x => Var (rho _ x)
  | Con _ c => Con c
  | Abs _ _ M => Abs (rename (ren_lift rho) M)
  | App _ _ M N => App (rename rho M) (rename rho N)
  end.

(** Weakening: the term M in a context extended by a fresh variable. *)
Definition weaken Γ B A (M : tm Γ A) : tm (B :: Γ) A := rename (ren_wk B) M.
#[global] Arguments weaken {Γ B A}.

(** Simultaneous substitutions. *)
Definition sub (Γ Δ : ctx) := forall A, var Γ A -> tm Δ A.

Definition sub_id Γ : sub Γ Γ := fun A x => Var x.
#[global] Arguments sub_id {Γ}.

(** Lifting a substitution under a binder. *)
Definition sub_lift Γ Δ B (sigma : sub Γ Δ) : sub (B :: Γ) (B :: Δ) :=
  fun A (x : var (B :: Γ) A) =>
    match x in var Γ' A' return
      (match Γ' return Type with
       | [::] => unit
       | B' :: Γ0 => sub Γ0 Δ -> tm (B' :: Δ) A'
       end)
    with
    | @vz _ _ => fun _ => Var vz
    | @vs _ _ _ y => fun sigma => weaken (sigma _ y)
    end sigma.
#[global] Arguments sub_lift {Γ Δ B}.

Fixpoint subst Γ Δ A (sigma : sub Γ Δ) (M : tm Γ A) : tm Δ A :=
  match M with
  | Var _ x => sigma _ x
  | Con _ c => Con c
  | Abs _ _ M => Abs (subst (sub_lift sigma) M)
  | App _ _ M N => App (subst sigma M) (subst sigma N)
  end.

(** The substitution [N, sigma] sending the last variable to N. *)
Definition sub_cons Γ Δ B (N : tm Δ B) (sigma : sub Γ Δ) : sub (B :: Γ) Δ :=
  fun A (x : var (B :: Γ) A) =>
    match x in var Γ' A' return
      (match Γ' return Type with
       | [::] => unit
       | B' :: Γ0 => tm Δ B' -> sub Γ0 Δ -> tm Δ A'
       end)
    with
    | @vz _ _ => fun N _ => N
    | @vs _ _ _ y => fun _ sigma => sigma _ y
    end N sigma.

(** M[N/x] for the last variable x of the context of M. *)
Definition subst1 Γ A B (M : tm (A :: Γ) B) (N : tm Γ A) : tm Γ B :=
  subst (sub_cons N sub_id) M.

(** ** The constants applied to their arguments *)

Definition Star Γ : tm Γ TUnit := Con CStar.
#[global] Arguments Star {Γ}.
Definition Pair Γ A B (M : tm Γ A) (N : tm Γ B) : tm Γ (A × B) :=
  App (App (Con CPair) M) N.
Definition Fst Γ A B (M : tm Γ (A × B)) : tm Γ A := App (Con CFst) M.
Definition Snd Γ A B (M : tm Γ (A × B)) : tm Γ B := App (Con CSnd) M.
Definition Zero Γ : tm Γ TOmega := Con CZero.
#[global] Arguments Zero {Γ}.
Definition One Γ : tm Γ TOmega := Con COne.
#[global] Arguments One {Γ}.
Definition Tens Γ (M N : tm Γ TOmega) : tm Γ TOmega :=
  App (App (Con CTens) M) N.
Definition Plus Γ (M N : tm Γ TOmega) : tm Γ TOmega :=
  App (App (Con CPlus) M) N.
Definition Inv Γ (M : tm Γ TOmega) : tm Γ TOmega := App (Con CInv) M.
Definition Pow Γ (p : \bar R) (M : tm Γ TOmega) : tm Γ TOmega :=
  App (Con (CPow p)) M.
(** ∫_A nu u *)
Definition Int Γ A (nu : tm Γ (TMeas A)) (u : tm Γ (A → TOmega)) :
    tm Γ TOmega :=
  App (App (Con (@CInt A)) nu) u.
Definition Ret Γ A (M : tm Γ A) : tm Γ (TMeas A) := App (Con (@CRet A)) M.
Definition Bind Γ A B (M : tm Γ (TMeas A)) (f : tm Γ (A → TMeas B)) :
    tm Γ (TMeas B) :=
  App (App (Con (@CBind A B)) M) f.
Definition Sample Γ A (mu : meas Σ A) : tm Γ (TMeas A) := Con (CSample mu).
#[global] Arguments Sample {Γ A} mu.
Definition Factor Γ (M : tm Γ TOmega) : tm Γ (TMeas TUnit) :=
  App (Con CFactor) M.
Definition Mass Γ (M : tm Γ (TMeas TUnit)) : tm Γ TOmega := App (Con CMass) M.
Definition Norm Γ A (M : tm Γ (TMeas A)) : tm Γ (TMeas A) :=
  App (Con (@CNorm A)) M.

(** ** Derived constants (D1)--(D9)

    As in HOL, a defined constant is an abbreviation together with its
    defining equation [c ≡ M].  Here the abbreviation is a Rocq definition,
    so the defining equation holds by conversion and need not be added to
    the equational theory.  Throughout p ∈ [-oo, oo] and 1/p is [p^-1] in
    [\bar R] (so 1/0 = +oo and 1/+oo = 0). *)

(* de Bruijn indices: v0 is the innermost bound variable *)
Local Notation v0 := vz.
Local Notation v1 := (vs vz).
Local Notation v2 := (vs (vs vz)).

(** (D1) oo := 0^* *)
Definition Infty Γ : tm Γ TOmega := Inv Zero.
#[global] Arguments Infty {Γ}.
(** (D2) ⊥ := 0 *)
Definition Bot Γ : tm Γ TOmega := Zero.
#[global] Arguments Bot {Γ}.
(** (D3) ⊤ := oo *)
Definition Top Γ : tm Γ TOmega := Infty.
#[global] Arguments Top {Γ}.
(** (D4) ⊗* := λa b. (a^* ⊗ b^* )^* *)
Definition CoTens Γ : tm Γ (TOmega → TOmega → TOmega) :=
  Abs (Abs (Inv (Tens (Inv (Var v1)) (Inv (Var v0))))).
#[global] Arguments CoTens {Γ}.
(** (D5) ⊸ := λa b. a^* ⊗* b *)
Definition Limp Γ : tm Γ (TOmega → TOmega → TOmega) :=
  Abs (Abs (App (App CoTens (Inv (Var v1))) (Var v0))).
#[global] Arguments Limp {Γ}.
(** (D6) ∨^p := λa b. (a^p ⊕ b^p)^(1/p) *)
Definition Por Γ (p : \bar R) : tm Γ (TOmega → TOmega → TOmega) :=
  Abs (Abs (Pow (p^-1)%E (Plus (Pow p (Var v1)) (Pow p (Var v0))))).
#[global] Arguments Por {Γ} p.
(** (D7) ∧^p := λa b. (a^* ∨^p b^* )^*, the De Morgan dual of (D6) *)
Definition Pand Γ (p : \bar R) : tm Γ (TOmega → TOmega → TOmega) :=
  Abs (Abs (Inv (App (App (Por p) (Inv (Var v1))) (Inv (Var v0))))).
#[global] Arguments Pand {Γ} p.
(** (D8) ∃^p_A := λnu u. (∫_A nu (λx. (u x)^p))^(1/p) *)
Definition Exists Γ A (p : \bar R) :
    tm Γ (TMeas A → (A → TOmega) → TOmega) :=
  Abs (Abs (Pow (p^-1)%E (Int (Var v1) (Abs (Pow p (App (Var v1) (Var v0))))))).
#[global] Arguments Exists {Γ} A p.
(** (D9) ∀^p_A := λnu u. (∃^p_A nu (λx. (u x)^* ))^* *)
Definition Forall Γ A (p : \bar R) :
    tm Γ (TMeas A → (A → TOmega) → TOmega) :=
  Abs (Abs (Inv (App (App (Exists A p) (Var v1))
                     (Abs (Inv (App (Var v1) (Var v0))))))).
#[global] Arguments Forall {Γ} A p.

(** ** Binder sugar

    For a quantifier Q : 𝒯 A → (A → Omega) → Omega,  Q (x ~ nu). phi  stands
    for  Q nu (λx : A. phi); the body phi lives in the context extended by x. *)
Definition qbind Γ A (Q : tm Γ (TMeas A → (A → TOmega) → TOmega))
    (nu : tm Γ (TMeas A)) (phi : tm (A :: Γ) TOmega) : tm Γ TOmega :=
  App (App Q nu) (Abs phi).

(** ∫_{x ~ nu} phi *)
Definition Int_x Γ A (nu : tm Γ (TMeas A)) (phi : tm (A :: Γ) TOmega) :
    tm Γ TOmega :=
  Int nu (Abs phi).
(** ∃^p (x ~ nu). phi *)
Definition Exists_x Γ A (p : \bar R) (nu : tm Γ (TMeas A))
    (phi : tm (A :: Γ) TOmega) : tm Γ TOmega :=
  qbind (Exists A p) nu phi.
(** ∀^p (x ~ nu). phi *)
Definition Forall_x Γ A (p : \bar R) (nu : tm Γ (TMeas A))
    (phi : tm (A :: Γ) TOmega) : tm Γ TOmega :=
  qbind (Forall A p) nu phi.

(** let x <- M in N := bind M (λx : A. N) *)
Definition Letin Γ A B (M : tm Γ (TMeas A)) (N : tm (A :: Γ) (TMeas B)) :
    tm Γ (TMeas B) :=
  Bind M (Abs N).
(** M ; N := let x <- M in N, x fresh *)
Definition Seq Γ A B (M : tm Γ (TMeas A)) (N : tm Γ (TMeas B)) :
    tm Γ (TMeas B) :=
  Letin M (weaken N).

End Terms.

Arguments const {R} Σ A%_ty.
Arguments tm {R} Σ Γ A%_ty.

Notation "⟨ M , N ⟩" := (Pair M N) : hqll_scope.
Notation "M ⊗ N" := (Tens M N) (at level 46, left associativity) : hqll_scope.
Notation "M ⊕ N" := (Plus M N) (at level 50, left associativity) : hqll_scope.
Notation "M `*" := (Inv M) : hqll_scope.
Notation "M ⊗* N" := (App (App CoTens M) N)
  (at level 46, left associativity) : hqll_scope.
Notation "M -o N" := (App (App Limp M) N)
  (at level 51, right associativity) : hqll_scope.
Notation "M ∨ [ p ] N" := (App (App (Por p) M) N)
  (at level 50, left associativity) : hqll_scope.
Notation "M ∧ [ p ] N" := (App (App (Pand p) M) N)
  (at level 50, left associativity) : hqll_scope.
Notation "M .[ N ]" := (subst1 M N) : hqll_scope.
Notation "M ;; N" := (Seq M N) (at level 100, right associativity) : hqll_scope.

(** * Examples *)

Section Examples.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.

(** The derivation of Section "Typing":  Γ ⊢ ∫_A nu (λx : A. phi) : Omega. *)
Example int_example Γ A (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) :
  tm Σ Γ TOmega := App (App (Con CInt) nu) (Abs phi).

Example int_example_sugar Γ A (nu : tm Σ Γ (TMeas A))
    (phi : tm Σ (A :: Γ) TOmega) :
  int_example nu phi = Int_x nu phi.
Proof. by []. Qed.

(** The defining equations of the derived constants hold by conversion. *)
Example top_def Γ : (Top : tm Σ Γ TOmega) = Zero `*.
Proof. by []. Qed.

(** A sequent-like formula:  ∀^p (x ~ nu). (psi -o phi). *)
Example forall_limp Γ A (p : \bar R) (nu : tm Σ Γ (TMeas A))
    (psi phi : tm Σ (A :: Γ) TOmega) : tm Σ Γ TOmega :=
  Forall_x p nu (psi -o phi).

(** β-reduction on the syntax: (λx. x) N  and  N  are related by [subst1]. *)
Example beta_id Γ A (N : tm Σ Γ A) : (Var vz : tm Σ (A :: Γ) A).[N] = N.
Proof. by []. Qed.

End Examples.
