From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets boolp interval_inference constructive_ereal ereal exp.
From HQLL Require Import nonneg_ereal omega syntax.

(**md**************************************************************************)
(* # The equational theory of HQLL                                            *)
(*                                                                            *)
(* The judgement Γ ⊢ M ≡ N : A of Section "Equational theory" of main.typ,   *)
(* as an inductive relation [conv] on the intrinsically typed terms of        *)
(* syntax.v, written [M ≡ N] (Γ and A are those of M and N).  It is the      *)
(* least congruence containing the λ-calculus equations (β, η, products,     *)
(* unit), the identities of the algebra Omega, the monad laws, the factor    *)
(* and mass laws, and the three axioms ∫-prog, ∫-lin, ∫-zero for the         *)
(* integral.  The definitional equations (D1)-(D9) hold by conversion.       *)
(*                                                                            *)
(* De Bruijn makes the side conditions of the paper explicit: a term that    *)
(* must not mention a variable is weakened ([weaken], [weaken1]), and the    *)
(* commutativity law swaps the last two variables ([swap]).  The first part  *)
(* of the file is the metatheory of renaming and substitution this needs.   *)
(*                                                                            *)
(* ```                                                                        *)
(*     var_cons_rect == case analysis on a variable of a non-empty context   *)
(*     rename_ext, rename_comp, rename_id, subst_ext, subst_id,              *)
(*     subst_rename, rename_subst, subst_comp                                *)
(*                     == the usual lemmas on renaming and substitution;     *)
(*                        rename_*, subst_* == their action on the applied   *)
(*                        constants and the sugar                            *)
(*         weaken1 A M == M : tm (B :: Γ) C read in B :: A :: Γ  (x ∉ FV(M)) *)
(*              swap M == M : tm (B :: A :: Γ) C read in A :: B :: Γ          *)
(*         oexp V, oeval rho s, oexp_tm phi s                                *)
(*                     == Omega-expressions with variables in V, their value *)
(*                        in the algebra Omega = [0, oo] under rho, and the  *)
(*                        formula they denote once phi : V -> tm Γ Omega     *)
(*                        instantiates the variables                         *)
(*               M ≡ N == the equational judgement [conv M N]               *)
(*   conv_ret, conv_letin, conv_seq, conv_mass, conv_factor, conv_tens, ... *)
(*                     == congruence of the applied constants and the sugar  *)
(*   conv_rename, conv_subst == the judgement is closed under renaming and   *)
(*                        substitution (the weakening and exchange left      *)
(*                        implicit by the paper's (Var) rule)                *)
(*         conv_subst1 == substitution is a congruence: N ≡ N' -> M.[N] ≡ M.[N'] *)
(*   conv_int_ret, conv_int_bind, conv_int_factor, conv_int_hom, conv_fubini *)
(*                     == the lemma "Derived integration laws"               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ty_scope.

(** * Metatheory of renaming and substitution *)

Section Metatheory.
Context {R : realType} {Σ : signature R}.
Implicit Types (Γ Δ Θ : ctx).

(** Case analysis on a variable of a non-empty context: it is the last
    variable [vz] or the successor [vs y] of a variable of the tail. *)
Lemma var_cons_rect Γ B (P : forall A, var (B :: Γ) A -> Prop) :
  P B vz -> (forall A (y : var Γ A), P A (vs y)) ->
  forall A (x : var (B :: Γ) A), P A x.
Proof.
move=> Hz Hs A x.
exact: (match x in var Γ' A' return
    (match Γ' return forall A', var Γ' A' -> Prop with
     | [::] => fun _ _ => True
     | B' :: Γ0 => fun A' x' =>
         forall P : forall A, var (B' :: Γ0) A -> Prop,
           P B' vz -> (forall A (y : var Γ0 A), P A (vs y)) -> P A' x'
     end) A' x
  with
  | @vz _ _ => fun P Hz _ => Hz
  | @vs _ _ _ y => fun P _ Hs => Hs _ y
  end P Hz Hs).
Qed.

(** ** Lifting a renaming or a substitution under a binder *)

Lemma ren_lift_ext Γ Δ B (rho rho' : ren Γ Δ) :
  (forall A x, rho A x = rho' A x) ->
  forall A x, ren_lift (B := B) rho A x = ren_lift rho' A x.
Proof. by move=> eq; apply: var_cons_rect => //= A y; rewrite eq. Qed.

Lemma ren_lift_comp Γ Δ Θ B (rho : ren Γ Δ) (rho' : ren Δ Θ) :
  forall A x, ren_lift (B := B) (fun A x => rho' A (rho A x)) A x
              = ren_lift rho' A (ren_lift rho A x).
Proof. by apply: var_cons_rect. Qed.

Lemma ren_lift_id Γ B : forall A x, ren_lift (B := B) (@ren_id Γ) A x = ren_id A x.
Proof. by apply: var_cons_rect. Qed.

Lemma sub_lift_ext Γ Δ B (sigma sigma' : sub (Σ := Σ) Γ Δ) :
  (forall A x, sigma A x = sigma' A x) ->
  forall A x, sub_lift (B := B) sigma A x = sub_lift sigma' A x.
Proof. by move=> eq; apply: var_cons_rect => //= A y; rewrite eq. Qed.

Lemma sub_lift_id Γ B :
  forall A x, sub_lift (B := B) (@sub_id R Σ Γ) A x = @sub_id R Σ (B :: Γ) A x.
Proof. by apply: var_cons_rect. Qed.

(** ** Renaming *)

Lemma rename_ext Γ A (M : tm Σ Γ A) Δ (rho rho' : ren Γ Δ) :
  (forall A x, rho A x = rho' A x) -> rename rho M = rename rho' M.
Proof.
elim: M Δ rho rho' => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ rho rho' eq /=.
- by rewrite eq.
- by [].
- by rewrite (IH _ _ _ (ren_lift_ext eq)).
- by rewrite (IHM _ _ _ eq) (IHN _ _ _ eq).
Qed.

Lemma rename_comp Γ A (M : tm Σ Γ A) Δ Θ (rho : ren Γ Δ) (rho' : ren Δ Θ) :
  rename rho' (rename rho M) = rename (fun A x => rho' A (rho A x)) M.
Proof.
elim: M Δ Θ rho rho' => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ Θ rho rho' //=.
- by rewrite IH (rename_ext _ (ren_lift_comp _ _)).
- by rewrite IHM IHN.
Qed.

Lemma rename_id Γ A (M : tm Σ Γ A) : rename ren_id M = M.
Proof.
elim: M => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN] //=.
- by rewrite (rename_ext _ (@ren_lift_id _ _)) IH.
- by rewrite IHM IHN.
Qed.

(** ** Substitution *)

Lemma subst_ext Γ A (M : tm Σ Γ A) Δ (sigma sigma' : sub (Σ := Σ) Γ Δ) :
  (forall A x, sigma A x = sigma' A x) -> subst sigma M = subst sigma' M.
Proof.
elim: M Δ sigma sigma' => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ sigma sigma' eq /=.
- by rewrite eq.
- by [].
- by rewrite (IH _ _ _ (sub_lift_ext eq)).
- by rewrite (IHM _ _ _ eq) (IHN _ _ _ eq).
Qed.

Lemma subst_id Γ A (M : tm Σ Γ A) : subst sub_id M = M.
Proof.
elim: M => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN] //=.
- by rewrite (subst_ext _ (@sub_lift_id _ _)) IH.
- by rewrite IHM IHN.
Qed.

(** A substitution after a renaming is a substitution. *)
Lemma subst_rename Γ A (M : tm Σ Γ A) Δ Θ (rho : ren Γ Δ) (sigma : sub (Σ := Σ) Δ Θ) :
  subst sigma (rename rho M) = subst (fun A x => sigma A (rho A x)) M.
Proof.
elim: M Δ Θ rho sigma => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ Θ rho sigma //=.
- by rewrite IH; congr Lam; apply: subst_ext; apply: var_cons_rect.
- by rewrite IHM IHN.
Qed.

(** A renaming after a substitution is a substitution. *)
Lemma rename_subst Γ A (M : tm Σ Γ A) Δ Θ (sigma : sub (Σ := Σ) Γ Δ) (rho : ren Δ Θ) :
  rename rho (subst sigma M) = subst (fun A x => rename rho (sigma A x)) M.
Proof.
elim: M Δ Θ sigma rho => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ Θ sigma rho //=.
- rewrite IH; congr Lam; apply: subst_ext; apply: var_cons_rect => //= C y.
  by rewrite /weaken !rename_comp.
- by rewrite IHM IHN.
Qed.

Lemma subst_comp Γ A (M : tm Σ Γ A) Δ Θ (sigma : sub (Σ := Σ) Γ Δ) (sigma' : sub (Σ := Σ) Δ Θ) :
  subst sigma' (subst sigma M) = subst (fun A x => subst sigma' (sigma A x)) M.
Proof.
elim: M Δ Θ sigma sigma' => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ Θ sigma sigma' //=.
- rewrite IH; congr Lam; apply: subst_ext; apply: var_cons_rect => //= C y.
  by rewrite /weaken subst_rename rename_subst.
- by rewrite IHM IHN.
Qed.

(** Renaming commutes with substitution for the last variable. *)
Lemma rename_subst1 Γ A B (M : tm Σ (A :: Γ) B) (N : tm Σ Γ A) Δ (rho : ren Γ Δ) :
  rename rho (subst1 M N) = subst1 (rename (ren_lift rho) M) (rename rho N).
Proof.
rewrite /subst1 rename_subst subst_rename; apply: subst_ext.
by apply: var_cons_rect.
Qed.

(** Weakening then substituting the new variable is the identity. *)
Lemma subst1_weaken Γ A B (M : tm Σ Γ B) (N : tm Σ Γ A) : subst1 (weaken M) N = M.
Proof.
rewrite /subst1 /weaken subst_rename -[RHS](subst_id M).
by apply: subst_ext.
Qed.

(** ** Contexts extended by two variables *)

(** M : tm (B :: Γ) C read in the context B :: A :: Γ, for the side
    conditions x ∉ FV(M) of the paper. *)
Definition weaken1 Γ A B C (M : tm Σ (B :: Γ) C) : tm Σ (B :: A :: Γ) C :=
  rename (ren_lift (ren_wk A)) M.

(** Swapping the last two variables of a context. *)
Definition ren_swap Γ A B : ren (B :: A :: Γ) (A :: B :: Γ) :=
  fun C (x : var (B :: A :: Γ) C) =>
    match x in var Γ' C' return
      (match Γ' return Type with
       | B' :: Γ1 =>
           match Γ1 return Type with
           | A' :: Γ0 => var (A' :: B' :: Γ0) C'
           | [::] => unit
           end
       | [::] => unit
       end)
    with
    | @vz Γ1 B' =>
        match Γ1 as Γ1' return
          (match Γ1' return Type with
           | A' :: Γ0 => var (A' :: B' :: Γ0) B'
           | [::] => unit
           end)
        with
        | [::] => tt
        | A' :: Γ0 => vs vz
        end
    | @vs Γ1 C' B' y =>
        match y in var Γ1' C'' return
          (match Γ1' return Type with
           | A' :: Γ0 => var (A' :: B' :: Γ0) C''
           | [::] => unit
           end)
        with
        | @vz _ _ => vz
        | @vs _ _ _ z => vs (vs z)
        end
    end.

Definition swap Γ A B C (M : tm Σ (B :: A :: Γ) C) : tm Σ (A :: B :: Γ) C :=
  rename (@ren_swap Γ A B) M.

(** The renamings commute with lifting, as needed to rename the equations. *)
Lemma ren_lift_wk Γ Δ A B (rho : ren Γ Δ) C (x : var (B :: Γ) C) :
  ren_lift (B := B) (ren_lift (B := A) rho) C (ren_lift (ren_wk A) C x)
  = ren_lift (ren_wk A) C (ren_lift rho C x).
Proof. by move: C x; apply: var_cons_rect. Qed.

Lemma ren_lift_swap Γ Δ A B (rho : ren Γ Δ) C (x : var (B :: A :: Γ) C) :
  ren_lift (B := A) (ren_lift (B := B) rho) C (@ren_swap Γ A B C x)
  = @ren_swap Δ A B C (ren_lift (ren_lift rho) C x).
Proof. by move: C x; apply: var_cons_rect => //; apply: var_cons_rect. Qed.

Lemma rename_weaken Γ Δ A B (rho : ren Γ Δ) (M : tm Σ Γ B) :
  rename (ren_lift (B := A) rho) (weaken M) = weaken (rename rho M).
Proof. by rewrite /weaken !rename_comp. Qed.

Lemma rename_weaken1 Γ Δ A B C (rho : ren Γ Δ) (M : tm Σ (B :: Γ) C) :
  rename (ren_lift (ren_lift rho)) (weaken1 A M)
  = weaken1 A (rename (ren_lift rho) M).
Proof.
by rewrite /weaken1 !rename_comp; apply: rename_ext => D y; exact: ren_lift_wk.
Qed.

Lemma rename_swap Γ Δ A B C (rho : ren Γ Δ) (M : tm Σ (B :: A :: Γ) C) :
  rename (ren_lift (ren_lift rho)) (swap M) = swap (rename (ren_lift (ren_lift rho)) M).
Proof.
by rewrite /swap !rename_comp; apply: rename_ext => D y; exact: ren_lift_swap.
Qed.

(** ** The renamings and substitutions on the variables, by computation *)

Lemma ren_wk_eq Γ A B (x : var Γ A) : ren_wk B A x = vs x.
Proof. by []. Qed.

Lemma ren_lift_vz Γ Δ B (rho : ren Γ Δ) : ren_lift (B := B) rho B vz = vz.
Proof. by []. Qed.

Lemma ren_lift_vs Γ Δ A B (rho : ren Γ Δ) (y : var Γ A) :
  ren_lift (B := B) rho A (vs y) = vs (rho A y).
Proof. by []. Qed.

Lemma sub_lift_vz Γ Δ B (sigma : sub (Σ := Σ) Γ Δ) :
  sub_lift (B := B) sigma B vz = Var vz.
Proof. by []. Qed.

Lemma sub_lift_vs Γ Δ A B (sigma : sub (Σ := Σ) Γ Δ) (y : var Γ A) :
  sub_lift (B := B) sigma A (vs y) = weaken (sigma A y).
Proof. by []. Qed.

Lemma sub_cons_vz Γ Δ B (N : tm Σ Δ B) (sigma : sub (Σ := Σ) Γ Δ) :
  sub_cons N sigma vz = N.
Proof. by []. Qed.

Lemma sub_cons_vs Γ Δ A B (N : tm Σ Δ B) (sigma : sub (Σ := Σ) Γ Δ) (y : var Γ A) :
  sub_cons N sigma (vs y) = sigma A y.
Proof. by []. Qed.

Lemma ren_swap_vz Γ A B : @ren_swap Γ A B B vz = vs vz.
Proof. by []. Qed.

Lemma ren_swap_vsz Γ A B : @ren_swap Γ A B A (vs vz) = vz.
Proof. by []. Qed.

Lemma ren_swap_vss Γ A B C (z : var Γ C) : @ren_swap Γ A B C (vs (vs z)) = vs (vs z).
Proof. by []. Qed.

(** Substituting after weakening forgets the substituted term. *)
Lemma subst_cons_weaken Γ Δ A B (N : tm Σ Δ A) (sigma : sub (Σ := Σ) Γ Δ)
    (M : tm Σ Γ B) :
  subst (sub_cons N sigma) (weaken M) = subst sigma M.
Proof. by rewrite /weaken subst_rename. Qed.

(** Swapping after weakening is weakening under the last variable. *)
Lemma swap_weaken Γ A B C (M : tm Σ (A :: Γ) C) :
  swap (weaken (B := B) M) = weaken1 B M.
Proof. by rewrite /swap /weaken /weaken1 rename_comp; apply: rename_ext; apply: var_cons_rect. Qed.

End Metatheory.

(** * Omega-expressions

    The axiom schema  s[φ⃗] ≡ t[φ⃗]  (s = t in [0, oo])  of the paper: s and t
    are expressions over the signature of Omega (0, 1, ⊗, ⊕, (-)^*, (-)^p)
    with variables in V, s = t means that they have the same value in the
    algebra Omega = [0, oo] of omega.v under every valuation, and s[φ⃗]
    is the formula obtained by instantiating the variables by formulas. *)

Section OmegaExpressions.
Context {R : realType}.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Inductive oexp (V : Type) : Type :=
| OVar of V
| OZero
| OOne
| OTens of oexp V & oexp V
| OPlus of oexp V & oexp V
| OInv of oexp V
| OPow of \bar R & oexp V.

Fixpoint oeval V (rho : V -> {nonneg \bar R}) (s : oexp V) : {nonneg \bar R} :=
  match s with
  | OVar v => rho v
  | OZero => 0%:E%:nng
  | OOne => 1%:E%:nng
  | OTens s t => mulnnge (oeval rho s) (oeval rho t)
  | OPlus s t => addnnge (oeval rho s) (oeval rho t)
  | OInv s => invnnge (oeval rho s)
  | OPow p s => pownnge p (oeval rho s)
  end.

Context {Σ : signature R}.

Fixpoint oexp_tm V Γ (phi : V -> tm Σ Γ TOmega) (s : oexp V) : tm Σ Γ TOmega :=
  match s with
  | OVar v => phi v
  | OZero => Zero
  | OOne => One
  | OTens s t => Tens (oexp_tm phi s) (oexp_tm phi t)
  | OPlus s t => Plus (oexp_tm phi s) (oexp_tm phi t)
  | OInv s => Inv (oexp_tm phi s)
  | OPow p s => Pow p (oexp_tm phi s)
  end.

Lemma rename_oexp_tm V Γ Δ (rho : ren Γ Δ) (phi : V -> tm Σ Γ TOmega) s :
  rename rho (oexp_tm phi s) = oexp_tm (fun v => rename rho (phi v)) s.
Proof. by elim: s => //= [s -> t ->|s -> t ->|s ->|p s ->]. Qed.

Lemma subst_oexp_tm V Γ Δ (sigma : sub (Σ := Σ) Γ Δ) (phi : V -> tm Σ Γ TOmega) s :
  subst sigma (oexp_tm phi s) = oexp_tm (fun v => subst sigma (phi v)) s.
Proof. by elim: s => //= [s -> t ->|s -> t ->|s ->|p s ->]. Qed.

End OmegaExpressions.

Arguments oexp : clear implicits.
Arguments OZero {R V}.
Arguments OOne {R V}.

(** * Renaming and substitution on the applied constants and the sugar

    By computation, except for the terms that weaken: there the lemmas of
    the metatheory are needed.  They let the rules of the judgement be
    renamed and substituted without unfolding the sugar. *)

Section Shapes.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.
Variables (Γ Δ : ctx) (rho : ren Γ Δ) (sigma : sub (Σ := Σ) Γ Δ).

Lemma rename_lam A B (M : tm Σ (A :: Γ) B) :
  rename rho (λ M) = λ rename (ren_lift rho) M.
Proof. by []. Qed.
Lemma rename_app A B (M : tm Σ Γ (A → B)) (N : tm Σ Γ A) :
  rename rho (M · N) = rename rho M · rename rho N.
Proof. by []. Qed.
Lemma rename_v0 A : rename (ren_lift (B := A) rho) (#0 : tm Σ (A :: Γ) A) = #0.
Proof. by []. Qed.
Lemma rename_star : rename rho (Star : tm Σ Γ TUnit) = Star.
Proof. by []. Qed.
Lemma rename_pair A B (M : tm Σ Γ A) (N : tm Σ Γ B) :
  rename rho ⟨ M , N ⟩ = ⟨ rename rho M , rename rho N ⟩.
Proof. by []. Qed.
Lemma rename_fst A B (M : tm Σ Γ (A × B)) : rename rho (π1 M) = π1 (rename rho M).
Proof. by []. Qed.
Lemma rename_snd A B (M : tm Σ Γ (A × B)) : rename rho (π2 M) = π2 (rename rho M).
Proof. by []. Qed.
Lemma rename_zero : rename rho (0 : tm Σ Γ TOmega) = 0.
Proof. by []. Qed.
Lemma rename_one : rename rho (𝟙 : tm Σ Γ TOmega) = 𝟙.
Proof. by []. Qed.
Lemma rename_tens (M N : tm Σ Γ TOmega) : rename rho (M ⊗ N) = rename rho M ⊗ rename rho N.
Proof. by []. Qed.
Lemma rename_plus (M N : tm Σ Γ TOmega) : rename rho (M ⊕ N) = rename rho M ⊕ rename rho N.
Proof. by []. Qed.
Lemma rename_inv (M : tm Σ Γ TOmega) : rename rho (M `*) = (rename rho M) `*.
Proof. by []. Qed.
Lemma rename_pow p (M : tm Σ Γ TOmega) : rename rho (M ^ p) = (rename rho M) ^ p.
Proof. by []. Qed.
Lemma rename_ret A (M : tm Σ Γ A) : rename rho (Ret M) = Ret (rename rho M).
Proof. by []. Qed.
Lemma rename_factor (M : tm Σ Γ TOmega) : rename rho (Factor M) = Factor (rename rho M).
Proof. by []. Qed.
Lemma rename_mass (M : tm Σ Γ (TMeas TUnit)) : rename rho (Mass M) = Mass (rename rho M).
Proof. by []. Qed.
Lemma rename_letin A B (M : tm Σ Γ (TMeas A)) (N : tm Σ (A :: Γ) (TMeas B)) :
  rename rho (Letin M N) = Letin (rename rho M) (rename (ren_lift rho) N).
Proof. by []. Qed.
Lemma rename_seq A B (M : tm Σ Γ (TMeas A)) (N : tm Σ Γ (TMeas B)) :
  rename rho (M ;; N) = (rename rho M ;; rename rho N).
Proof. by rewrite /Seq rename_letin rename_weaken. Qed.
Lemma rename_int_x A (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) :
  rename rho (∫ nu, phi) = ∫ rename rho nu, rename (ren_lift rho) phi.
Proof. by []. Qed.

Lemma subst_lam A B (M : tm Σ (A :: Γ) B) :
  subst sigma (λ M) = λ subst (sub_lift sigma) M.
Proof. by []. Qed.
Lemma subst_app A B (M : tm Σ Γ (A → B)) (N : tm Σ Γ A) :
  subst sigma (M · N) = subst sigma M · subst sigma N.
Proof. by []. Qed.
Lemma subst_v0 A : subst (sub_lift (B := A) sigma) (#0 : tm Σ (A :: Γ) A) = #0.
Proof. by []. Qed.
Lemma subst_star : subst sigma (Star : tm Σ Γ TUnit) = Star.
Proof. by []. Qed.
Lemma subst_pair A B (M : tm Σ Γ A) (N : tm Σ Γ B) :
  subst sigma ⟨ M , N ⟩ = ⟨ subst sigma M , subst sigma N ⟩.
Proof. by []. Qed.
Lemma subst_fst A B (M : tm Σ Γ (A × B)) : subst sigma (π1 M) = π1 (subst sigma M).
Proof. by []. Qed.
Lemma subst_snd A B (M : tm Σ Γ (A × B)) : subst sigma (π2 M) = π2 (subst sigma M).
Proof. by []. Qed.
Lemma subst_zero : subst sigma (0 : tm Σ Γ TOmega) = 0.
Proof. by []. Qed.
Lemma subst_one : subst sigma (𝟙 : tm Σ Γ TOmega) = 𝟙.
Proof. by []. Qed.
Lemma subst_tens (M N : tm Σ Γ TOmega) : subst sigma (M ⊗ N) = subst sigma M ⊗ subst sigma N.
Proof. by []. Qed.
Lemma subst_plus (M N : tm Σ Γ TOmega) : subst sigma (M ⊕ N) = subst sigma M ⊕ subst sigma N.
Proof. by []. Qed.
Lemma subst_ret A (M : tm Σ Γ A) : subst sigma (Ret M) = Ret (subst sigma M).
Proof. by []. Qed.
Lemma subst_factor (M : tm Σ Γ TOmega) : subst sigma (Factor M) = Factor (subst sigma M).
Proof. by []. Qed.
Lemma subst_mass (M : tm Σ Γ (TMeas TUnit)) : subst sigma (Mass M) = Mass (subst sigma M).
Proof. by []. Qed.
Lemma subst_letin A B (M : tm Σ Γ (TMeas A)) (N : tm Σ (A :: Γ) (TMeas B)) :
  subst sigma (Letin M N) = Letin (subst sigma M) (subst (sub_lift sigma) N).
Proof. by []. Qed.
Lemma subst_int_x A (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) :
  subst sigma (∫ nu, phi) = ∫ subst sigma nu, subst (sub_lift sigma) phi.
Proof. by []. Qed.

(** The terms that weaken. *)
Lemma subst_weaken A B (M : tm Σ Γ B) :
  subst (sub_lift (B := A) sigma) (weaken M) = weaken (subst sigma M).
Proof. by rewrite /weaken subst_rename rename_subst. Qed.

Lemma subst_seq A B (M : tm Σ Γ (TMeas A)) (N : tm Σ Γ (TMeas B)) :
  subst sigma (M ;; N) = (subst sigma M ;; subst sigma N).
Proof. by rewrite /Seq subst_letin subst_weaken. Qed.

Lemma subst_weaken1 A B C (M : tm Σ (B :: Γ) C) :
  subst (sub_lift (sub_lift (B := A) sigma)) (weaken1 A M)
  = weaken1 A (subst (sub_lift sigma) M).
Proof.
rewrite /weaken1 subst_rename rename_subst; apply: subst_ext.
apply: var_cons_rect => // D y.
by rewrite ren_lift_vs ren_wk_eq !sub_lift_vs /weaken !rename_comp.
Qed.

Lemma subst_swap A B C (M : tm Σ (B :: A :: Γ) C) :
  subst (sub_lift (sub_lift sigma)) (swap M) = swap (subst (sub_lift (sub_lift sigma)) M).
Proof.
rewrite /swap subst_rename rename_subst; apply: subst_ext.
apply: var_cons_rect => //; apply: var_cons_rect => // D z.
by rewrite ren_swap_vss !sub_lift_vs /weaken !rename_comp.
Qed.

Lemma subst_subst1 A B (M : tm Σ (A :: Γ) B) (N : tm Σ Γ A) :
  subst sigma (M.[N]) = (subst (sub_lift sigma) M).[subst sigma N].
Proof.
rewrite /subst1 !subst_comp; apply: subst_ext.
apply: var_cons_rect => // C y.
by rewrite sub_cons_vs sub_lift_vs subst_cons_weaken subst_id.
Qed.

End Shapes.

(** * The equational judgement *)

Reserved Notation "M ≡ N" (at level 70, no associativity).

Section Conv.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.

(** Γ ⊢ M ≡ N : A, for M N : tm Σ Γ A.  The constructors are the rules of
    Section "Equational theory": the congruence rules, the equations of the
    λ-calculus with products and unit, the identities of Omega, the monad
    laws, the laws of factor and mass, and the three axioms for ∫. *)
Inductive conv : forall Γ A, tm Σ Γ A -> tm Σ Γ A -> Prop :=
(** ** Congruence *)
| conv_refl Γ A (M : tm Σ Γ A) : M ≡ M
| conv_sym Γ A (M N : tm Σ Γ A) : M ≡ N -> N ≡ M
| conv_trans Γ A (M N P : tm Σ Γ A) : M ≡ N -> N ≡ P -> M ≡ P
| conv_lam Γ A B (M M' : tm Σ (A :: Γ) B) : M ≡ M' -> (λ M) ≡ (λ M')
| conv_app Γ A B (M M' : tm Σ Γ (A → B)) (N N' : tm Σ Γ A) :
    M ≡ M' -> N ≡ N' -> M · N ≡ M' · N'
(** ** The λ-calculus with products and unit *)
(** (λx : A. M) N ≡ M[N/x] *)
| conv_beta Γ A B (M : tm Σ (A :: Γ) B) (N : tm Σ Γ A) : (λ M) · N ≡ M.[N]
(** λx : A. (M x) ≡ M,  x ∉ FV(M) *)
| conv_eta Γ A B (M : tm Σ Γ (A → B)) : (λ weaken M · #0) ≡ M
(** π_i ⟨M_1, M_2⟩ ≡ M_i *)
| conv_fst Γ A B (M : tm Σ Γ A) (N : tm Σ Γ B) : π1 ⟨ M , N ⟩ ≡ M
| conv_snd Γ A B (M : tm Σ Γ A) (N : tm Σ Γ B) : π2 ⟨ M , N ⟩ ≡ N
(** ⟨π_1 M, π_2 M⟩ ≡ M *)
| conv_pair Γ A B (M : tm Σ Γ (A × B)) : ⟨ π1 M , π2 M ⟩ ≡ M
(** M ≡ ∗  for M : 1 *)
| conv_unit Γ (M : tm Σ Γ TUnit) : M ≡ Star
(** ** The algebra of Omega:  s[φ⃗] ≡ t[φ⃗]  when s = t in [0, oo] *)
| conv_omega Γ V (s t : oexp R V) (phi : V -> tm Σ Γ TOmega) :
    (forall rho, oeval rho s = oeval rho t) -> oexp_tm phi s ≡ oexp_tm phi t
(** ** The monad *)
(** let x <- ret M in N ≡ N[M/x] *)
| conv_let_ret Γ A B (M : tm Σ Γ A) (N : tm Σ (A :: Γ) (TMeas B)) :
    Letin (Ret M) N ≡ N.[M]
(** let x <- M in ret x ≡ M *)
| conv_ret_let Γ A (M : tm Σ Γ (TMeas A)) : Letin M (Ret #0) ≡ M
(** let y <- (let x <- M in N) in P ≡ let x <- M in let y <- N in P,
    x ∉ FV(P) *)
| conv_let_assoc Γ A B C (M : tm Σ Γ (TMeas A)) (N : tm Σ (A :: Γ) (TMeas B))
    (P : tm Σ (B :: Γ) (TMeas C)) :
    Letin (Letin M N) P ≡ Letin M (Letin N (weaken1 A P))
(** let x <- M in let y <- N in P ≡ let y <- N in let x <- M in P,
    x ∉ FV(N), y ∉ FV(M) *)
| conv_let_comm Γ A B C (M : tm Σ Γ (TMeas A)) (N : tm Σ Γ (TMeas B))
    (P : tm Σ (B :: A :: Γ) (TMeas C)) :
    Letin M (Letin (weaken N) P) ≡ Letin N (Letin (weaken M) (swap P))
(** ** factor and mass *)
(** factor 1 ≡ ret ∗ *)
| conv_factor_one Γ : (Factor 𝟙 : tm Σ Γ (TMeas TUnit)) ≡ Ret Star
(** factor φ ; factor ψ ≡ factor (φ ⊗ ψ) *)
| conv_factor_tens Γ (phi psi : tm Σ Γ TOmega) :
    (Factor phi ;; Factor psi) ≡ Factor (phi ⊗ psi)
(** mass (factor φ) ≡ φ *)
| conv_mass_factor Γ (phi : tm Σ Γ TOmega) : Mass (Factor phi) ≡ phi
(** factor (mass m) ≡ m *)
| conv_factor_mass Γ (m : tm Σ Γ (TMeas TUnit)) : Factor (Mass m) ≡ m
(** ** The integral *)
(** (∫-prog)  ∫_{x ~ ν} φ ≡ mass (let x <- ν in factor φ) *)
| conv_int_prog Γ A (nu : tm Σ Γ (TMeas A)) (phi : tm Σ (A :: Γ) TOmega) :
    (∫ nu, phi) ≡ Mass (Letin nu (Factor phi))
(** (∫-lin)  ∫_{x ~ ν} (φ ⊕ ψ) ≡ ∫_{x ~ ν} φ ⊕ ∫_{x ~ ν} ψ *)
| conv_int_lin Γ A (nu : tm Σ Γ (TMeas A)) (phi psi : tm Σ (A :: Γ) TOmega) :
    (∫ nu, phi ⊕ psi) ≡ (∫ nu, phi) ⊕ (∫ nu, psi)
(** (∫-zero)  ∫_{x ~ ν} 0 ≡ 0 *)
| conv_int_zero Γ A (nu : tm Σ Γ (TMeas A)) : (∫ nu, 0) ≡ 0
where "M ≡ N" := (@conv _ _ M N).

End Conv.

Notation "M ≡ N" := (conv M N) : hqll_scope.

(** * Congruence of the applied constants and of the sugar *)

Section Congruence.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.
Implicit Types (Γ : ctx).

(** A constant applied to convertible arguments. *)
Lemma conv_app1 Γ A B {c : tm Σ Γ (A → B)} (M M' : tm Σ Γ A) :
  M ≡ M' -> c · M ≡ c · M'.
Proof. exact: conv_app (conv_refl _). Qed.

Lemma conv_app2 Γ A B C {c : tm Σ Γ (A → B → C)} (M M' : tm Σ Γ A)
    (N N' : tm Σ Γ B) :
  M ≡ M' -> N ≡ N' -> c · M · N ≡ c · M' · N'.
Proof. by move=> HM HN; apply: conv_app HN; exact: conv_app1 HM. Qed.

Lemma conv_pair_cong Γ A B (M M' : tm Σ Γ A) (N N' : tm Σ Γ B) :
  M ≡ M' -> N ≡ N' -> ⟨ M , N ⟩ ≡ ⟨ M' , N' ⟩.
Proof. exact: conv_app2. Qed.

Lemma conv_fst_cong Γ A B (M M' : tm Σ Γ (A × B)) : M ≡ M' -> π1 M ≡ π1 M'.
Proof. exact: conv_app1. Qed.

Lemma conv_snd_cong Γ A B (M M' : tm Σ Γ (A × B)) : M ≡ M' -> π2 M ≡ π2 M'.
Proof. exact: conv_app1. Qed.

Lemma conv_tens Γ (M M' N N' : tm Σ Γ TOmega) :
  M ≡ M' -> N ≡ N' -> M ⊗ N ≡ M' ⊗ N'.
Proof. exact: conv_app2. Qed.

Lemma conv_plus Γ (M M' N N' : tm Σ Γ TOmega) :
  M ≡ M' -> N ≡ N' -> M ⊕ N ≡ M' ⊕ N'.
Proof. exact: conv_app2. Qed.

Lemma conv_inv Γ (M M' : tm Σ Γ TOmega) : M ≡ M' -> M `* ≡ M' `*.
Proof. exact: conv_app1. Qed.

Lemma conv_pow Γ (p : \bar R) (M M' : tm Σ Γ TOmega) : M ≡ M' -> M ^ p ≡ M' ^ p.
Proof. exact: conv_app1. Qed.

Lemma conv_int Γ A (nu nu' : tm Σ Γ (TMeas A)) (u u' : tm Σ Γ (A → TOmega)) :
  nu ≡ nu' -> u ≡ u' -> ∫_A nu u ≡ ∫_A nu' u'.
Proof. exact: conv_app2. Qed.

Lemma conv_ret Γ A (M M' : tm Σ Γ A) : M ≡ M' -> Ret M ≡ Ret M'.
Proof. exact: conv_app1. Qed.

Lemma conv_bind Γ A B (M M' : tm Σ Γ (TMeas A)) (f f' : tm Σ Γ (A → TMeas B)) :
  M ≡ M' -> f ≡ f' -> M >>= f ≡ M' >>= f'.
Proof. exact: conv_app2. Qed.

Lemma conv_factor Γ (M M' : tm Σ Γ TOmega) : M ≡ M' -> Factor M ≡ Factor M'.
Proof. exact: conv_app1. Qed.

Lemma conv_mass Γ (M M' : tm Σ Γ (TMeas TUnit)) : M ≡ M' -> Mass M ≡ Mass M'.
Proof. exact: conv_app1. Qed.

Lemma conv_norm Γ A (M M' : tm Σ Γ (TMeas A)) : M ≡ M' -> Norm M ≡ Norm M'.
Proof. exact: conv_app1. Qed.

(** The sugar. *)
Lemma conv_qbind Γ A (Q : tm Σ Γ (TMeas A → (A → TOmega) → TOmega))
    (nu nu' : tm Σ Γ (TMeas A)) (phi phi' : tm Σ (A :: Γ) TOmega) :
  nu ≡ nu' -> phi ≡ phi' -> qbind Q nu phi ≡ qbind Q nu' phi'.
Proof. by move=> Hnu Hphi; apply: conv_app2 Hnu _; exact: conv_lam. Qed.

Lemma conv_int_x Γ A (nu nu' : tm Σ Γ (TMeas A)) (phi phi' : tm Σ (A :: Γ) TOmega) :
  nu ≡ nu' -> phi ≡ phi' -> (∫ nu, phi) ≡ (∫ nu', phi').
Proof. by move=> Hnu Hphi; apply: conv_app2 Hnu _; exact: conv_lam. Qed.

Lemma conv_exists_x Γ A (p : \bar R) (nu nu' : tm Σ Γ (TMeas A))
    (phi phi' : tm Σ (A :: Γ) TOmega) :
  nu ≡ nu' -> phi ≡ phi' -> (∃^p nu, phi) ≡ (∃^p nu', phi').
Proof. exact: conv_qbind. Qed.

Lemma conv_forall_x Γ A (p : \bar R) (nu nu' : tm Σ Γ (TMeas A))
    (phi phi' : tm Σ (A :: Γ) TOmega) :
  nu ≡ nu' -> phi ≡ phi' -> (∀^p nu, phi) ≡ (∀^p nu', phi').
Proof. exact: conv_qbind. Qed.

Lemma conv_letin Γ A B (M M' : tm Σ Γ (TMeas A)) (N N' : tm Σ (A :: Γ) (TMeas B)) :
  M ≡ M' -> N ≡ N' -> Letin M N ≡ Letin M' N'.
Proof. by move=> HM HN; apply: conv_app2 HM _; exact: conv_lam. Qed.

End Congruence.

(** * Admissible rules: renaming and substitution

    The judgement is closed under renaming (the weakening and exchange
    that the paper leaves implicit in its (Var) rule) and under
    substitution, and substitution is a congruence. *)

Section Admissible.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.

Lemma conv_rename Γ A (M N : tm Σ Γ A) (H : M ≡ N) Δ (rho : ren Γ Δ) :
  rename rho M ≡ rename rho N.
Proof.
elim: H Δ rho => {Γ A M N}.
- move=> Γ A M Δ rho; exact: conv_refl.
- move=> Γ A M N _ IH Δ rho; exact: conv_sym (IH _ _).
- move=> Γ A M N P _ IH1 _ IH2 Δ rho; exact: conv_trans (IH1 _ _) (IH2 _ _).
- move=> Γ A B M M' _ IH Δ rho; rewrite !rename_lam; exact: conv_lam (IH _ _).
- move=> Γ A B M M' N N' _ IH1 _ IH2 Δ rho; rewrite !rename_app.
  exact: conv_app (IH1 _ _) (IH2 _ _).
- move=> Γ A B M N Δ rho; rewrite rename_app rename_lam rename_subst1.
  exact: conv_beta.
- move=> Γ A B M Δ rho; rewrite rename_lam rename_app rename_weaken rename_v0.
  exact: conv_eta.
- move=> Γ A B M N Δ rho; rewrite rename_fst rename_pair; exact: conv_fst.
- move=> Γ A B M N Δ rho; rewrite rename_snd rename_pair; exact: conv_snd.
- move=> Γ A B M Δ rho; rewrite rename_pair rename_fst rename_snd; exact: conv_pair.
- move=> Γ M Δ rho; rewrite rename_star; exact: conv_unit.
- move=> Γ V s t phi eq Δ rho; rewrite !rename_oexp_tm; exact: conv_omega _ eq.
- move=> Γ A B M N Δ rho; rewrite rename_letin rename_ret rename_subst1.
  exact: conv_let_ret.
- move=> Γ A M Δ rho; rewrite rename_letin rename_ret rename_v0; exact: conv_ret_let.
- move=> Γ A B C M N P Δ rho; rewrite !rename_letin rename_weaken1.
  exact: conv_let_assoc.
- move=> Γ A B C M N P Δ rho; rewrite !rename_letin !rename_weaken rename_swap.
  exact: conv_let_comm.
- move=> Γ Δ rho; rewrite rename_factor rename_one rename_ret rename_star.
  exact: conv_factor_one.
- move=> Γ phi psi Δ rho; rewrite rename_seq !rename_factor rename_tens.
  exact: conv_factor_tens.
- move=> Γ phi Δ rho; rewrite rename_mass rename_factor; exact: conv_mass_factor.
- move=> Γ m Δ rho; rewrite rename_factor rename_mass; exact: conv_factor_mass.
- move=> Γ A nu phi Δ rho.
  rewrite rename_int_x rename_mass rename_letin rename_factor; exact: conv_int_prog.
- move=> Γ A nu phi psi Δ rho; rewrite !rename_int_x !rename_plus; exact: conv_int_lin.
- move=> Γ A nu Δ rho; rewrite rename_int_x !rename_zero; exact: conv_int_zero.
Qed.

Lemma conv_weaken Γ A B (M N : tm Σ Γ A) : M ≡ N -> weaken (B := B) M ≡ weaken N.
Proof. by move=> H; exact: conv_rename. Qed.

Lemma conv_subst Γ A (M N : tm Σ Γ A) (H : M ≡ N) Δ (sigma : sub (Σ := Σ) Γ Δ) :
  subst sigma M ≡ subst sigma N.
Proof.
elim: H Δ sigma => {Γ A M N}.
- move=> Γ A M Δ sigma; exact: conv_refl.
- move=> Γ A M N _ IH Δ sigma; exact: conv_sym (IH _ _).
- move=> Γ A M N P _ IH1 _ IH2 Δ sigma; exact: conv_trans (IH1 _ _) (IH2 _ _).
- move=> Γ A B M M' _ IH Δ sigma; rewrite !subst_lam; exact: conv_lam (IH _ _).
- move=> Γ A B M M' N N' _ IH1 _ IH2 Δ sigma; rewrite !subst_app.
  exact: conv_app (IH1 _ _) (IH2 _ _).
- move=> Γ A B M N Δ sigma; rewrite subst_app subst_lam subst_subst1.
  exact: conv_beta.
- move=> Γ A B M Δ sigma; rewrite subst_lam subst_app subst_weaken subst_v0.
  exact: conv_eta.
- move=> Γ A B M N Δ sigma; rewrite subst_fst subst_pair; exact: conv_fst.
- move=> Γ A B M N Δ sigma; rewrite subst_snd subst_pair; exact: conv_snd.
- move=> Γ A B M Δ sigma; rewrite subst_pair subst_fst subst_snd; exact: conv_pair.
- move=> Γ M Δ sigma; rewrite subst_star; exact: conv_unit.
- move=> Γ V s t phi eq Δ sigma; rewrite !subst_oexp_tm; exact: conv_omega _ eq.
- move=> Γ A B M N Δ sigma; rewrite subst_letin subst_ret subst_subst1.
  exact: conv_let_ret.
- move=> Γ A M Δ sigma; rewrite subst_letin subst_ret subst_v0; exact: conv_ret_let.
- move=> Γ A B C M N P Δ sigma; rewrite !subst_letin subst_weaken1.
  exact: conv_let_assoc.
- move=> Γ A B C M N P Δ sigma; rewrite !subst_letin !subst_weaken subst_swap.
  exact: conv_let_comm.
- move=> Γ Δ sigma; rewrite subst_factor subst_one subst_ret subst_star.
  exact: conv_factor_one.
- move=> Γ phi psi Δ sigma; rewrite subst_seq !subst_factor subst_tens.
  exact: conv_factor_tens.
- move=> Γ phi Δ sigma; rewrite subst_mass subst_factor; exact: conv_mass_factor.
- move=> Γ m Δ sigma; rewrite subst_factor subst_mass; exact: conv_factor_mass.
- move=> Γ A nu phi Δ sigma.
  rewrite subst_int_x subst_mass subst_letin subst_factor; exact: conv_int_prog.
- move=> Γ A nu phi psi Δ sigma; rewrite !subst_int_x !subst_plus; exact: conv_int_lin.
- move=> Γ A nu Δ sigma; rewrite subst_int_x !subst_zero; exact: conv_int_zero.
Qed.

(** Substitution is a congruence in the substituted terms. *)
Lemma conv_subst_pw Γ A (M : tm Σ Γ A) Δ (sigma sigma' : sub (Σ := Σ) Γ Δ) :
  (forall A x, sigma A x ≡ sigma' A x) -> subst sigma M ≡ subst sigma' M.
Proof.
elim: M Δ sigma sigma' => [Γ' A' x|Γ' A' c|Γ' A' B' M IH|Γ' A' B' M IHM N IHN]
  Δ sigma sigma' H.
- exact: H.
- exact: conv_refl.
- rewrite !subst_lam; apply: conv_lam; apply: IH.
  apply: var_cons_rect => [|C y]; first exact: conv_refl.
  by rewrite !sub_lift_vs; exact: conv_weaken (H _ _).
- rewrite !subst_app; exact: conv_app (IHM _ _ _ H) (IHN _ _ _ H).
Qed.

Lemma conv_subst1 Γ A B (M : tm Σ (A :: Γ) B) (N N' : tm Σ Γ A) :
  N ≡ N' -> M.[N] ≡ M.[N'].
Proof.
move=> H; apply: conv_subst_pw; apply: var_cons_rect => [|C y]; first exact: H.
exact: conv_refl.
Qed.

(** The substitution rule (Subst) of the paper:
    Γ, x : A ⊢ M ≡ M' : B  and  Γ ⊢ N ≡ N' : A  give  Γ ⊢ M[N/x] ≡ M'[N'/x] : B. *)
Lemma conv_subst_cong Γ A B (M M' : tm Σ (A :: Γ) B) (N N' : tm Σ Γ A) :
  M ≡ M' -> N ≡ N' -> M.[N] ≡ M'.[N'].
Proof.
move=> HM HN; apply: (conv_trans (conv_subst HM (sub_cons N sub_id))).
exact: conv_subst1.
Qed.

(** The derived congruence of sequencing. *)
Lemma conv_seq Γ A B (M M' : tm Σ Γ (TMeas A)) (N N' : tm Σ Γ (TMeas B)) :
  M ≡ M' -> N ≡ N' -> (M ;; N) ≡ (M' ;; N').
Proof. by move=> HM HN; apply: conv_letin HM _; exact: conv_weaken. Qed.

(** A term over Γ, x : 1 is its instance at ∗ (from M ≡ ∗). *)
Lemma conv_unit_var Γ A (M : tm Σ (TUnit :: Γ) A) : M ≡ weaken (M.[Star]).
Proof.
rewrite /subst1 /weaken rename_subst -[X in X ≡ _](subst_id M).
apply: conv_subst_pw; apply: var_cons_rect => [|C y]; last exact: conv_refl.
exact: conv_unit.
Qed.

End Admissible.

(** * Derived integration laws

    The lemma "Derived integration laws" of the paper: ∫-ret, ∫-bind,
    ∫-factor, ∫-hom and Fubini follow from the axioms, the monad laws and
    the factor/mass laws. *)

Section Derived.
Context {R : realType} {Σ : signature R}.
Local Open Scope hqll_scope.

(** (∫-ret)  ∫_{x ~ ret M} φ ≡ φ[M/x] *)
Lemma conv_int_ret Γ A (M : tm Σ Γ A) (phi : tm Σ (A :: Γ) TOmega) :
  (∫ Ret M, phi) ≡ phi.[M].
Proof.
apply: (conv_trans (conv_int_prog _ _)).
apply: (conv_trans (conv_mass (conv_let_ret _ _))).
exact: conv_mass_factor.
Qed.

(** (∫-bind)  ∫_{y ~ let x <- M in N} φ ≡ ∫_{x ~ M} ∫_{y ~ N} φ,  x ∉ FV(φ) *)
Lemma conv_int_bind Γ A B (M : tm Σ Γ (TMeas A)) (N : tm Σ (A :: Γ) (TMeas B))
    (phi : tm Σ (B :: Γ) TOmega) :
  (∫ Letin M N, phi) ≡ (∫ M, ∫ N, weaken1 A phi).
Proof.
apply: (conv_trans (conv_int_prog _ _)); apply: conv_sym.
apply: (conv_trans (conv_int_prog _ _)); apply: conv_mass.
apply: (conv_trans (conv_letin (conv_refl _) (conv_factor (conv_int_prog _ _)))).
apply: (conv_trans (conv_letin (conv_refl _) (conv_factor_mass _))).
apply: conv_sym; exact: conv_let_assoc.
Qed.

(** (∫-factor)  ∫_{x ~ factor ψ} φ ≡ ψ ⊗ φ[∗/x] *)
Lemma conv_int_factor Γ (psi : tm Σ Γ TOmega) (phi : tm Σ (TUnit :: Γ) TOmega) :
  (∫ Factor psi, phi) ≡ psi ⊗ phi.[Star].
Proof.
apply: (conv_trans (conv_int_prog _ _)).
apply: (conv_trans (conv_mass (conv_letin (conv_refl _)
  (conv_factor (conv_unit_var phi))))).
apply: (conv_trans (conv_mass (conv_factor_tens psi (phi.[Star])))).
exact: conv_mass_factor.
Qed.

(** mass (factor ψ ; m) ≡ ψ ⊗ mass m *)
Lemma conv_mass_seq Γ (psi : tm Σ Γ TOmega) (m : tm Σ Γ (TMeas TUnit)) :
  Mass (Factor psi ;; m) ≡ psi ⊗ Mass m.
Proof.
apply: (conv_trans (conv_mass (conv_seq (conv_refl _) (conv_sym (conv_factor_mass m))))).
apply: (conv_trans (conv_mass (conv_factor_tens _ _))).
exact: conv_mass_factor.
Qed.

(** (∫-hom)  ∫_{x ~ ν} (ψ ⊗ φ) ≡ ψ ⊗ ∫_{x ~ ν} φ,  x ∉ FV(ψ) *)
Lemma conv_int_hom Γ A (nu : tm Σ Γ (TMeas A)) (psi : tm Σ Γ TOmega)
    (phi : tm Σ (A :: Γ) TOmega) :
  (∫ nu, weaken psi ⊗ phi) ≡ psi ⊗ (∫ nu, phi).
Proof.
apply: (conv_trans (conv_int_prog _ _)).
apply: (conv_trans (conv_mass (conv_letin (conv_refl _)
  (conv_sym (conv_factor_tens _ _))))).
apply: (conv_trans (conv_mass (conv_let_comm nu (Factor psi) (weaken (Factor phi))))).
rewrite swap_weaken.
apply: (conv_trans (conv_mass_seq psi (Letin nu (Factor phi)))).
exact: conv_tens (conv_refl _) (conv_sym (conv_int_prog _ _)).
Qed.

(** (Fubini)  ∫_{x ~ ν} ∫_{y ~ ρ} φ ≡ ∫_{y ~ ρ} ∫_{x ~ ν} φ,
    x ∉ FV(ρ), y ∉ FV(ν) *)
Lemma conv_fubini Γ A B (nu : tm Σ Γ (TMeas A)) (mu : tm Σ Γ (TMeas B))
    (phi : tm Σ (B :: A :: Γ) TOmega) :
  (∫ nu, ∫ weaken mu, phi) ≡ (∫ mu, ∫ weaken nu, swap phi).
Proof.
apply: (conv_trans (conv_int_prog _ _)).
apply: (conv_trans (conv_mass (conv_letin (conv_refl _)
  (conv_factor (conv_int_prog _ _))))).
apply: (conv_trans (conv_mass (conv_letin (conv_refl _) (conv_factor_mass _)))).
apply: (conv_trans (conv_mass (conv_let_comm _ _ _))).
apply: conv_sym.
apply: (conv_trans (conv_int_prog _ _)).
apply: (conv_trans (conv_mass (conv_letin (conv_refl _)
  (conv_factor (conv_int_prog _ _))))).
apply: (conv_trans (conv_mass (conv_letin (conv_refl _) (conv_factor_mass _)))).
exact: conv_refl.
Qed.

End Derived.
