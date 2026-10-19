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
(* the four typing rules Var/Con/Lam/App are the four constructors of [tm],   *)
(* a context is a list of types, and the side condition that the variables    *)
(* of a context be distinct disappears.                                       *)
(*                                                                            *)
(* The signature Σ of the paper is the fixed table of constants, the two      *)
(* primitive distributions uniform(a, b) and normal(m, s) on RR (with their    *)
(* side conditions a < b and 0 < s as proof arguments, as in mathcomp), plus   *)
(* one family [sample_mu : TMeas A] indexed by the s-finite measures mu on [[A]].*)
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
(*                         Γ ⊢ M : A); constructors Var, Con, Lam, App         *)
(*            ren Γ Δ, rename rho M == renamings and their action on terms    *)
(*            sub Γ Δ, subst sigma M == substitutions and their action        *)
(*             weaken M == M in a context extended by one variable            *)
(*               M.[N] == M[N/x], substitution for the last variable          *)
(*   Star, Pair, Fst, Snd, Zero, One, Tens, Plus, Inv, Pow p, Int, Ret, Bind, *)
(*   Sample mu, Uniform a b ab, Normal m s hs, Factor, Mass, Norm             *)
(*                      == the constants of Σ applied to their arguments       *)
(*   Infty, Bot, Top, CoTens, Limp, Por p, Pand p, Exists p, Forall p         *)
(*                      == the derived constants (D1)--(D9)                    *)
(*   qbind Q nu phi, Int_x nu phi, Exists_x p nu phi, Forall_x p nu phi       *)
(*                      == binder sugar  Q (x ~ nu). phi  :=  Q nu (λx. phi)   *)
(*     Letin M N, M ;; N == let x <- M in N  and  M ; N                        *)
(*   const_map ι c, tm_map ι M == renaming of the measure symbols along     *)
(*                         ι : meas Σ A -> meas Σ' A (a map of signatures)   *)
(* ```                                                                        *)
(*                                                                            *)
(* Notations (scope [hqll_scope], key [hqll]; see the section Notations):      *)
(* ```                                                                        *)
(*   #0 #1 #2 #3   M · N   λ M            variables, application, abstraction *)
(*   ⟨ M , N ⟩   π1 M   π2 M              pairing and projections             *)
(*   0   𝟙   M ⊗ N   M ⊕ N   M `*   M ^ p  the primitive connectives          *)
(*   ∫_A nu u   M >>= f   M.[N]           integral, bind, substitution        *)
(*   ∞   ⊥   ⊤   M ⊗* N   M -o N   M ∨^p N   M ∧^p N   the derived ones       *)
(*   ∫ nu , phi   ∃^p nu , phi   ∀^p nu , phi   M ;; N     binders, sequencing *)
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
| CUniform (a b : R) (ab : (a < b)%R) : const (TMeas TReal)  (** uniform(a, b) *)
| CNormal (m s : R) (hs : (0 < s)%R) : const (TMeas TReal)   (** normal(m, s) *)
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
      (Lam) Γ, x : A ⊢ M : B  ⇒  Γ ⊢ λx : A. M : A → B
      (App) Γ ⊢ M : A → B,  Γ ⊢ N : A  ⇒  Γ ⊢ M N : B
>>
    Formulas are the terms of type [TOmega], predicates on A those of type
    [Pred A]. *)
Inductive tm (Γ : ctx) : ty -> Type :=
| Var A : var Γ A -> tm Γ A
| Con A : const A -> tm Γ A
| Lam A B : tm (A :: Γ) B -> tm Γ (A → B)
| App A B : tm Γ (A → B) -> tm Γ A -> tm Γ B.
#[global] Arguments Con {Γ A}.

Bind Scope hqll_scope with tm.

(** ** Renaming and substitution *)

Fixpoint rename Γ Δ A (rho : ren Γ Δ) (M : tm Γ A) : tm Δ A :=
  match M with
  | Var _ x => Var (rho _ x)
  | Con _ c => Con c
  | Lam _ _ M => Lam (rename (ren_lift rho) M)
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
  | Lam _ _ M => Lam (subst (sub_lift sigma) M)
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

(** The primitive distributions on RR, with their side conditions carried as
    proof arguments exactly as [uniform_prob a b ab] and
    [qbs_normal_distribution m s hs] do in mathcomp. *)
Definition Uniform Γ (a b : R) (ab : (a < b)%R) : tm Γ (TMeas TReal) :=
  Con (@CUniform a b ab).

Definition Normal Γ (m s : R) (hs : (0 < s)%R) : tm Γ (TMeas TReal) :=
  Con (@CNormal m s hs).

Definition Factor Γ (M : tm Γ TOmega) : tm Γ (TMeas TUnit) :=
  App (Con CFactor) M.

Definition Mass Γ (M : tm Γ (TMeas TUnit)) : tm Γ TOmega := App (Con CMass) M.

Definition Norm Γ A (M : tm Γ (TMeas A)) : tm Γ (TMeas A) :=
  App (Con (@CNorm A)) M.

End Terms.

Arguments const {R} Σ A%_ty.
Arguments tm {R} Σ Γ A%_ty.
(* The side conditions determine a, b and s, so Rocq would make them implicit;
   they are kept explicit to read as uniform(a, b) and normal(m, s). *)
Arguments CUniform {R Σ} a%_R b%_R ab.
Arguments CNormal {R Σ} m%_R s%_R hs.
Arguments Uniform {R Σ Γ} a%_R b%_R ab.
Arguments Normal {R Σ Γ} m%_R s%_R hs.

(** * Notations

    Scope [hqll_scope] (key [hqll]).  Application binds tightest (level 10,
    as Rocq's own), then [^] (30), [⊗] and [⊗*] (46), [⊕], [∨[p]], [∧[p]]
    (50), [>>=] (49), [-o] (51, right), binders ([λ], [∫], [∃], [∀]) extend as
    far to the right as possible (200), and [;;] is at 100.  The levels of
    the connectives are those of their semantic counterparts in
    [nonneg_ereal.v], so that a formula and its interpretation read alike. *)

(** De Bruijn variables: [#0] is the last variable declared in the context,
    i.e. the innermost bound variable, [#1] the one before, etc. *)
Notation "#0" := (Var vz) : hqll_scope.
Notation "#1" := (Var (vs vz)) : hqll_scope.
Notation "#2" := (Var (vs (vs vz))) : hqll_scope.
Notation "#3" := (Var (vs (vs (vs vz)))) : hqll_scope.

(** λ-calculus: application [M · N] and abstraction [λ M], whose bound
    variable is [#0] in [M] (its type is determined by the context of [M]). *)
Notation "M · N" := (App M N) (at level 10, left associativity) : hqll_scope.
Notation "'λ' M" := (Lam M) (at level 200, M at level 200,
  format "'λ'  M") : hqll_scope.

(** Products. *)
Notation "⟨ M , N ⟩" := (Pair M N) : hqll_scope.
Notation "'π1' M" := (Fst M) (at level 10, M at level 9) : hqll_scope.
Notation "'π2' M" := (Snd M) (at level 10, M at level 9) : hqll_scope.

(** The connectives of the logic. *)
Notation "0" := Zero : hqll_scope.
Notation "𝟙" := One : hqll_scope.
Notation "M ⊗ N" := (Tens M N) (at level 46, left associativity) : hqll_scope.
Notation "M ⊕ N" := (Plus M N) (at level 50, left associativity) : hqll_scope.
Notation "M `*" := (Inv M) : hqll_scope.
Notation "M ^ p" := (Pow p M) : hqll_scope.

(** The integral [∫_A nu u] (the type A is explicit, as in the paper). *)
Notation "∫_ A nu u" := (@Int _ _ _ A nu u)
  (at level 10, A at level 0, nu at level 9, u at level 9,
   format "∫_ A  nu  u") : hqll_scope.

(** The monad. *)
Notation "M >>= f" := (Bind M f) (at level 49, left associativity) : hqll_scope.

(** Substitution for the last variable. *)
Notation "M .[ N ]" := (subst1 M N) : hqll_scope.

(** ** Derived constants (D1)--(D9)

    As in HOL, a defined constant is an abbreviation together with its
    defining equation [c ≡ M].  Here the abbreviation is a Rocq definition,
    so the defining equation holds by conversion and need not be added to
    the equational theory.  Throughout p ∈ [-oo, oo] and 1/p is [p^-1] in
    [\bar R] (so 1/0 = +oo and 1/+oo = 0). *)

Section Derived.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.

(** (D1) ∞ := 0^* *)
Definition Infty Γ : tm Σ Γ TOmega := 0 `*.
#[global] Arguments Infty {Γ}.

(** (D2) ⊥ := 0 *)
Definition Bot Γ : tm Σ Γ TOmega := 0.
#[global] Arguments Bot {Γ}.

(** (D3) ⊤ := ∞ *)
Definition Top Γ : tm Σ Γ TOmega := Infty.
#[global] Arguments Top {Γ}.

(** (D4) ⊗* := λa b. (a^* ⊗ b^* )^* *)
Definition CoTens Γ : tm Σ Γ (TOmega → TOmega → TOmega) :=
  λ λ (#1 `* ⊗ #0 `*) `*.
#[global] Arguments CoTens {Γ}.

(** (D5) ⊸ := λa b. a^* ⊗* b *)
Definition Limp Γ : tm Σ Γ (TOmega → TOmega → TOmega) :=
  λ λ CoTens · #1 `* · #0.
#[global] Arguments Limp {Γ}.

(** (D6) ∨^p := λa b. (a^p ⊕ b^p)^(1/p) *)
Definition Por Γ (p : \bar R) : tm Σ Γ (TOmega → TOmega → TOmega) :=
  λ λ (#1 ^ p ⊕ #0 ^ p) ^ p^-1.
#[global] Arguments Por {Γ} p.

(** (D7) ∧^p := λa b. (a^* ∨^p b^* )^*, the De Morgan dual of (D6) *)
Definition Pand Γ (p : \bar R) : tm Σ Γ (TOmega → TOmega → TOmega) :=
  λ λ (Por p · #1 `* · #0 `*) `*.
#[global] Arguments Pand {Γ} p.

(** (D8) ∃^p_A := λnu u. (∫_A nu (λx. (u x)^p))^(1/p) *)
Definition Exists Γ A (p : \bar R) :
    tm Σ Γ (TMeas A → (A → TOmega) → TOmega) :=
  λ λ (∫_A #1 (λ (#1 · #0) ^ p)) ^ p^-1.
#[global] Arguments Exists {Γ} A p.

(** (D9) ∀^p_A := λnu u. (∃^p_A nu (λx. (u x)^* ))^* *)
Definition Forall Γ A (p : \bar R) :
    tm Σ Γ (TMeas A → (A → TOmega) → TOmega) :=
  λ λ (Exists A p · #1 · (λ (#1 · #0) `*)) `*.
#[global] Arguments Forall {Γ} A p.

(** ** Binder sugar

    For a quantifier Q : 𝒯 A → (A → Omega) → Omega,  Q (x ~ nu). phi  stands
    for  Q nu (λx : A. phi); the body phi lives in the context extended by x,
    where x is [#0]. *)
Definition qbind Γ A (Q : tm Σ Γ (TMeas A → (A → TOmega) → TOmega))
    (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) : tm Σ Γ TOmega :=
  Q · nu · (λ phi).

(** ∫_{x ~ nu} phi *)
Definition Int_x Γ A (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) :
    tm Σ Γ TOmega :=
  ∫_A nu (λ phi).

(** ∃^p (x ~ nu). phi *)
Definition Exists_x Γ A (p : \bar R) (nu : tm Σ Γ (TMeas A))
    (phi : tm Σ (A :: Γ) TOmega) : tm Σ Γ TOmega :=
  qbind (Exists A p) nu phi.

(** ∀^p (x ~ nu). phi *)
Definition Forall_x Γ A (p : \bar R) (nu : tm Σ Γ (TMeas A))
    (phi : tm Σ (A :: Γ) TOmega) : tm Σ Γ TOmega :=
  qbind (Forall A p) nu phi.

(** let x <- M in N := bind M (λx : A. N) *)
Definition Letin Γ A B (M : tm Σ Γ (TMeas A)) (N : tm Σ (A :: Γ) (TMeas B)) :
    tm Σ Γ (TMeas B) :=
  M >>= λ N.

(** M ; N := let x <- M in N, x fresh *)
Definition Seq Γ A B (M : tm Σ Γ (TMeas A)) (N : tm Σ Γ (TMeas B)) :
    tm Σ Γ (TMeas B) :=
  Letin M (weaken N).

End Derived.

(** The derived connectives. *)
Notation "∞" := Infty : hqll_scope.
Notation "⊥" := Bot : hqll_scope.
Notation "⊤" := Top : hqll_scope.
Notation "M ⊗* N" := (App (App CoTens M) N)
  (at level 46, left associativity) : hqll_scope.
Notation "M -o N" := (App (App Limp M) N)
  (at level 51, right associativity) : hqll_scope.
Notation "M ∨^ p N" := (App (App (Por p) M) N)
  (at level 50, p at level 2, left associativity, format "M  ∨^ p  N")
  : hqll_scope.
Notation "M ∧^ p N" := (App (App (Pand p) M) N)
  (at level 50, p at level 2, left associativity, format "M  ∧^ p  N")
  : hqll_scope.

(** The binders:  ∫ (x ~ nu). phi,  ∃^p (x ~ nu). phi,  ∀^p (x ~ nu). phi,
    with x = [#0] in phi. *)
Notation "∫ nu , phi" := (Int_x nu phi)
  (at level 200, nu at level 99, format "∫  nu ,  phi") : hqll_scope.
Notation "∃^ p nu , phi" := (Exists_x p nu phi)
  (at level 200, p at level 2, nu at level 99, format "∃^ p  nu ,  phi")
  : hqll_scope.
Notation "∀^ p nu , phi" := (Forall_x p nu phi)
  (at level 200, p at level 2, nu at level 99, format "∀^ p  nu ,  phi")
  : hqll_scope.

(** Sequencing. *)
Notation "M ;; N" := (Seq M N)
  (at level 100, right associativity, format "M  ;;  N") : hqll_scope.

(** * Maps of signatures

    The fixed constants are the same in every signature; two signatures
    differ only by their measure symbols.  A map of symbols
    ι : meas Σ A → meas Σ' A therefore acts on constants and on terms by
    renaming the [sample_mu].  This is how a model interprets the terms
    over a signature of named measures: it maps each symbol to a measure
    of [meas sem_sig A] and interprets the image. *)

Section SigMap.
Context {R : realType} {Σ Σ' : signature R}.
Variable ι : forall A, meas Σ A -> meas Σ' A.

Definition const_map A (c : const Σ A) : const Σ' A :=
  match c in const _ A return const Σ' A with
  | CStar => CStar
  | CPair _ _ => CPair
  | CFst _ _ => CFst
  | CSnd _ _ => CSnd
  | CZero => CZero
  | COne => COne
  | CTens => CTens
  | CPlus => CPlus
  | CInv => CInv
  | CPow p => CPow p
  | CInt _ => CInt
  | CRet _ => CRet
  | CBind _ _ => CBind
  | CSample _ mu => CSample (ι mu)
  | CUniform a b ab => CUniform a b ab
  | CNormal m s hs => CNormal m s hs
  | CFactor => CFactor
  | CMass => CMass
  | CNorm _ => CNorm
  end.

Fixpoint tm_map Γ A (M : tm Σ Γ A) : tm Σ' Γ A :=
  match M with
  | Var _ x => Var x
  | Con _ c => Con (const_map c)
  | Lam _ _ M => Lam (tm_map M)
  | App _ _ M N => App (tm_map M) (tm_map N)
  end.

End SigMap.

(** * Examples *)

Section Examples.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.

(** The derivation of Section "Typing", Γ ⊢ ∫_A nu (λx : A. phi) : Ω:
<<
  (∫_A : 𝒯A → (A → Ω) → Ω) ∈ Σ
  ————————————————————————————— (Con)
  Γ ⊢ ∫_A : 𝒯A → (A → Ω) → Ω     Γ ⊢ nu : 𝒯A
  ——————————————————————————————————————————— (App)   Γ, x : A ⊢ phi : Ω
  Γ ⊢ ∫_A nu : (A → Ω) → Ω                            ———————————————————————— (Lam)
                                                      Γ ⊢ λx : A. phi : A → Ω
  ———————————————————————————————————————————————————————————————————————— (App)
                      Γ ⊢ ∫_A nu (λx : A. phi) : Ω
>>
    Read bottom-up, the derivation is the term: [Con CInt] is the (Con) leaf,
    each [·] an (App), [λ phi] the (Lam), and x is [#0] in phi. *)
Example int_example Γ A (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) :
  tm Σ Γ TOmega := Con CInt · nu · (λ phi).

Example int_example_sugar Γ A (nu : tm Σ Γ (TMeas A))
    (phi : tm Σ (A :: Γ) TOmega) :
  int_example nu phi = ∫ nu, phi.
Proof. by []. Qed.

(** The defining equations of the derived constants hold by conversion:
    ⊤ := ∞ := 0^* by (D3), (D1), and Γ ⊢ 0^* : Ω is
<<
  ((-)^* : Ω → Ω) ∈ Σ        (0 : Ω) ∈ Σ
  ———————————————————— (Con) ——————————— (Con)
  Γ ⊢ (-)^* : Ω → Ω          Γ ⊢ 0 : Ω
  ————————————————————————————————————— (App)
              Γ ⊢ 0^* : Ω
>> *)
Example top_def Γ : (⊤ : tm Σ Γ TOmega) = 0 `*.
Proof. by []. Qed.

(** phi ⊸ psi is the derived constant (D5) applied to phi and psi:
<<
  Γ ⊢ ⊸ : Ω → Ω → Ω (D5)   Γ ⊢ phi : Ω
  ———————————————————————————————————— (App)
  Γ ⊢ ⊸ phi : Ω → Ω                      Γ ⊢ psi : Ω
  ——————————————————————————————————————————————————— (App)
                 Γ ⊢ phi ⊸ psi : Ω
>>
    where the leaf (D5) is the derivation of the closed term
    ◇ ⊢ λa b. a^* ⊗* b : Ω → Ω → Ω, read in any context Γ. *)
Example limp_def Γ (phi psi : tm Σ Γ TOmega) :
  phi -o psi = Limp · phi · psi.
Proof. by []. Qed.

(** A sequent-like formula, ∀^p (x ~ nu). (psi ⊸ phi), i.e. the quantifier
    (D9) applied to nu and to the abstraction of the body:
<<
  Γ ⊢ ∀^p_A : 𝒯A → (A → Ω) → Ω (D9)   Γ ⊢ nu : 𝒯A
  ———————————————————————————————————————————————— (App)
  Γ ⊢ ∀^p_A nu : (A → Ω) → Ω

                                 Γ, x : A ⊢ psi ⊸ phi : Ω   (as in limp_def)
  Γ ⊢ ∀^p_A nu : (A → Ω) → Ω     ——————————————————————————————— (Lam)
                                 Γ ⊢ λx : A. psi ⊸ phi : A → Ω
  —————————————————————————————————————————————————————————————— (App)
             Γ ⊢ ∀^p_A nu (λx : A. psi ⊸ phi) : Ω
>> *)
Example forall_limp Γ A (p : \bar R) (nu : tm Σ Γ (TMeas A))
    (psi phi : tm Σ (A :: Γ) TOmega) : tm Σ Γ TOmega :=
  ∀^p nu, psi -o phi.

(** A program,  let x <- sample_mu in (factor (phi x) ; ret x),  which is
    bind sample_mu (λx : A. P) with P := factor (phi x) ; ret x:
<<
  Γ ⊢ bind : 𝒯A → (A → 𝒯A) → 𝒯A (Con)   Γ ⊢ sample_mu : 𝒯A (Con)
  ———————————————————————————————————————————————————————————— (App)
  Γ ⊢ bind sample_mu : (A → 𝒯A) → 𝒯A

                                           Γ, x : A ⊢ P : 𝒯A
                                           ———————————————————————— (Lam)
  Γ ⊢ bind sample_mu : (A → 𝒯A) → 𝒯A       Γ ⊢ λx : A. P : A → 𝒯A
  ————————————————————————————————————————————————————————————————— (App)
                 Γ ⊢ bind sample_mu (λx : A. P) : 𝒯A
>>
    and, writing Δ for Γ, x : A and unfolding  M ; N := bind M (λy : 1. N)
    with y fresh, the body P is typed by
<<
                        Δ ⊢ phi : A → Ω   Δ ⊢ x : A (Var)
                        ————————————————————————————————— (App)
  Δ ⊢ factor : Ω → 𝒯1 (Con)       Δ ⊢ phi x : Ω
  −−————————————————————————————————————————————————— (App)
  Δ ⊢ factor (phi x) : 𝒯1

  Δ, y : 1 ⊢ ret : A → 𝒯A (Con)   Δ, y : 1 ⊢ x : A (Var)
  ————————————————————————————————————————————————————— (App)
  Δ, y : 1 ⊢ ret x : 𝒯A
  ——————————————————————————— (Lam)
  Δ ⊢ λy : 1. ret x : 1 → 𝒯A

  Δ ⊢ bind : 𝒯1 → (1 → 𝒯A) → 𝒯A (Con)   Δ ⊢ factor (phi x) : 𝒯1
  ————————————————————————————————————————————————————————————— (App)
  Δ ⊢ bind (factor (phi x)) : (1 → 𝒯A) → 𝒯A       Δ ⊢ λy : 1. ret x : 1 → 𝒯A
  ———————————————————————————————————————————————————————————————————————— (App)
            Δ ⊢ bind (factor (phi x)) (λy : 1. ret x) : 𝒯A
>>
    In the paper phi : A → Ω, typed in Γ, is used in Δ by the (Var) rule
    with a non-empty Γ'; here that weakening is the explicit [weaken phi].
    Likewise [;;] weakens its second argument under the fresh y, which is
    why [Ret #0] refers to x and not to y. *)
Example program Γ A (mu : meas Σ A) (phi : tm Σ Γ (A → TOmega)) :
  tm Σ Γ (TMeas A) :=
  Sample mu >>= λ (Factor (weaken phi · #0) ;; Ret #0).

(** β-reduction on the syntax: (λx : A. x) N and N are related by [subst1].
    The redex is typed by
<<
  Γ, x : A ⊢ x : A (Var)
  ——————————————————————— (Lam)
  Γ ⊢ λx : A. x : A → A     Γ ⊢ N : A
  ——————————————————————————————————— (App)
       Γ ⊢ (λx : A. x) N : A
>>
    and x[N/x] = N holds by computation. *)
Example beta_id Γ A (N : tm Σ Γ A) : (#0 : tm Σ (A :: Γ) A).[N] = N.
Proof. by []. Qed.

End Examples.

(** * Examples with the primitive distributions *)

Section Distributions.
Context {R : realType} {Σ : signature R}.
Import Num.Theory.
Local Open Scope hqll_scope.

(** The standard normal and the uniform distribution on [0, 1], as terms
    of type 𝒯 RR; [ltr01 : 0 < 1] discharges the side conditions, as in
    mathcomp's [uniform_prob ltr01]. *)
Example normal01 Γ : tm Σ Γ (TMeas TReal) := Normal 0 1 ltr01.
#[global] Arguments normal01 {Γ}.
Example uniform01 Γ : tm Σ Γ (TMeas TReal) := Uniform 0 1 ltr01.
#[global] Arguments uniform01 {Γ}.

(** A Bayesian program: condition a standard normal prior on an
    observation model phi : RR → Ω and return the unnormalised posterior,
      let x <- normal(0, 1) in (factor (phi x) ; ret x). *)
Example posterior Γ (phi : tm Σ Γ (TReal → TOmega)) : tm Σ Γ (TMeas TReal) :=
  normal01 >>= λ (Factor (weaken phi · #0) ;; Ret #0).

(** A formula about it: psi holds (with softness p) of the normalised
    posterior,
      ∀^p (x ~ norm (let x <- normal(0, 1) in ...)). psi x *)
Example posterior_forall Γ (p : \bar R) (phi psi : tm Σ Γ (TReal → TOmega)) :
  tm Σ Γ TOmega :=
  ∀^p Norm (posterior phi), weaken psi · #0.

(** The L^p-mean of psi under uniform(0, 1),
      ∃^p (x ~ uniform(0, 1)). psi x,
    and the mass of the prior rescored by psi, which is its expectation. *)
Example uniform_exists Γ (p : \bar R) (psi : tm Σ Γ (TReal → TOmega)) :
  tm Σ Γ TOmega :=
  ∃^p uniform01, weaken psi · #0.

Example uniform_mass Γ (psi : tm Σ Γ (TReal → TOmega)) : tm Σ Γ TOmega :=
  Mass (uniform01 >>= λ Factor (weaken psi · #0)).

End Distributions.
