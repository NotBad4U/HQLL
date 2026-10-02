From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets boolp interval_inference constructive_ereal ereal
  measurable_structure measurable_function measurable_realfun
  lebesgue_stieltjes_measure lebesgue_integral exp.
From QBS Require Import quasi_borel measure_qbs_adjunction.
From HQLL Require Import interval_einference algebra_order_utils nonneg_ereal
  syntax.

(**md**************************************************************************)
(* # Denotational semantics of HQLL in quasi-Borel spaces                     *)
(*                                                                            *)
(* The semantics of Section "Semantics" of main.typ: types denote             *)
(* quasi-Borel spaces, contexts denote finite products, and a term            *)
(* [Gamma |- M : A] denotes a QBS morphism [[Gamma]] -> [[A]].  The           *)
(* interpretation is the standard one of a simply typed lambda-calculus in    *)
(* a cartesian closed category, instantiated to QBS (library [QBS]).          *)
(*                                                                            *)
(* The type Omega of truth values denotes the non-negative extended reals     *)
(* [{nonneg \bar R}], equipped here with the QBS structure induced by the     *)
(* Borel structure of [\bar R] (file nonneg_ereal.v provides the algebra of   *)
(* connectives on this carrier).  The logical constants of the signature      *)
(* are interpreted by the corresponding operations, packaged as QBS           *)
(* morphisms (the measurability proofs are the lemmas [measurable_*] below).  *)
(*                                                                            *)
(* The s-finite measure type 𝒯 A is interpreted through a *model structure*:  *)
(* a record [hqll_model] packaging a monad [TQ] on QBS together with the      *)
(* interpretation of return, bind, ∫, factor, mass and norm as QBS            *)
(* morphisms.  This matches the paper, which introduces T axiomatically       *)
(* from the literature (Ścibior et al. 2018, Vákár 2026); constructing a      *)
(* concrete s-finite model on top of QBS/probability_qbs.v is future work,    *)
(* as are the equations of these operations (they belong to the soundness     *)
(* theorem, not to the interpretation).                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*            OmegaQ R == the QBS of truth values: carrier {nonneg \bar R},   *)
(*                        random elements the alpha with measurable           *)
(*                        (fun r => (alpha r)%:num)                           *)
(*             mk_nng x0 == the element of {nonneg \bar R} packaging x with   *)
(*                        the proof x0 : 0 <= x                               *)
(*           addnnge a b == a ⊕ b, addition on {nonneg \bar R}                *)
(*            pow_infe x == x^oo = lim_p x^p on [0, oo]: 0, 1 or +oo          *)
(*            powO p x == x^p on [0, oo] for p in [-oo, +oo], Section        *)
(*                        "Interpretation of the logical constants":          *)
(*                        x^0 = 1, x^p = x `^ p (0 < p < oo),                 *)
(*                        x^p = (x^-1) `^ (-p) (-oo < p < 0),                 *)
(*                        x^+oo = pow_infe x, x^-oo = pow_infe (x^-1)         *)
(*          pownnge p a == the same, packaged on {nonneg \bar R}              *)
(*   qbs_tens, qbs_plus == ⊗ and ⊕ as morphisms Omega × Omega -> Omega        *)
(*     qbs_inv, qbs_pow p == (-)^* and (-)^p as morphisms Omega -> Omega      *)
(*             qbs_lam f == the transpose X -> Z^Y of f : X × Y -> Z          *)
(*                        (the half of cartesian closure missing from         *)
(*                        quasi_borel.v)                                      *)
(*          hqll_model R == the model structure: TQ with retQ, bindQ, intQ,   *)
(*                        factorQ, massQ, normQ                               *)
(*              sem_ty A == [[A]], by recursion on A (the paper's section    *)
(*                        on types and contexts): [[1]] = unitQ, RR = realQ,  *)
(*                        [[Omega]] = OmegaQ, products, exponentials, and     *)
(*                        [[𝒯 A]] = TQ [[A]]                                  *)
(*               sem_sig == the model signature: meas A := TQ [[A]], so      *)
(*                        that sample_mu is indexed by the points of          *)
(*                        TQ [[A]]                                            *)
(*             sem_ctx Γ == [[Γ]], the product of the [[A]], A in Γ           *)
(*             sem_var x == the projection [[Γ]] -> [[A]] of a variable       *)
(*           sem_const c == [[c]], a point of [[A]] (Table tab:sig and        *)
(*                        Section "Interpretation of the logical constants")  *)
(*              sem_tm == [[Γ ⊢ M : A]] : [[Γ]] -> [[A]], by recursion:     *)
(*                        variables are projections, constants constant      *)
(*                        morphisms, Abs is qbs_lam, App is eval ∘ pairing    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** * The truth values Omega as a quasi-Borel space

    [[Omega]] = [0, oo], the non-negative extended reals, with the QBS
    structure induced by the standard Borel structure of [\bar R]: a map
    alpha : R -> [0, oo] is a random element iff it is Borel. *)

Section omega_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** Packaging an extended real known to be non-negative. *)
Lemma nng_spec (x : \bar R) : 0 <= x ->
  Itv.spec (@ext_num_sem R) (Itv.Real `[Posz 0, +oo[) x.
Proof.
by move=> x0; apply/and3P; split; rewrite ?bnd_simp//=.
Qed.

Definition mk_nng (x : \bar R) (x0 : 0 <= x) : {nonneg \bar R} :=
  Itv.mk (nng_spec x0).

Lemma mk_nng_num (x : \bar R) (x0 : 0 <= x) : (mk_nng x0)%:num = x.
Proof. by []. Qed.

(** The QBS structure on {nonneg \bar R}. *)
Let OMx : set (mR -> {nonneg \bar R}) :=
  [set alpha | measurable_fun setT (fun r => (alpha r)%:num)].

Let OMx_comp : forall (alpha : mR -> {nonneg \bar R}) (f : {mfun mR >-> mR}),
    OMx alpha -> OMx (alpha \o f).
Proof. by move=> alpha f ha; exact: (measurableT_comp ha). Qed.

Let OMx_const : forall x : {nonneg \bar R}, OMx (fun _ => x).
Proof. by move=> x; exact: measurable_cst. Qed.

Let OMx_glue : forall (P : {mfun mR >-> nat})
    (Fi : nat -> mR -> {nonneg \bar R}),
    (forall i, OMx (Fi i)) -> OMx (fun r => Fi (P r) r).
Proof.
by move=> P Fi hFi; exact: (measurable_glue (Fi := fun i r => (Fi i r)%:num)).
Qed.

HB.instance Definition _ :=
  @isQBS.Build R {nonneg \bar R} OMx OMx_comp OMx_const OMx_glue.

(** The QBS of truth values. *)
Definition OmegaQ : qbsType R := {nonneg \bar R}.

Lemma OmegaQ_Mx (alpha : mR -> OmegaQ) :
  qbs_Mx alpha = measurable_fun setT (fun r => (alpha r)%:num).
Proof. by []. Qed.

End omega_qbs.

(** * The connectives on Omega and their measurability

    The operations of Section "Interpretation of the logical constants":
    ⊗ and ⊕ are [mulnnge] (from nonneg_ereal.v) and [addnnge], the
    involution (-)^* is [invnnge], and the powers (-)^p for p in [-oo, +oo]
    are [pownnge].  [powO] is the same power function on the carrier
    \bar R, where the measurability arguments take place. *)

Section omega_operations.
Variable R : realType.

Implicit Types (a b : {nonneg \bar R}) (x : \bar R).

Lemma nngenum_ge0 a : 0 <= a%:num.
Proof. by []. Qed.

(** ⊕, the additive connective (the paper's a ⊕ b = a + b). *)
Definition addnnge a b : {nonneg \bar R} :=
  mk_nng (adde_ge0 (nngenum_ge0 a) (nngenum_ge0 b)).

Lemma addnnge_num a b : (addnnge a b)%:num = a%:num + b%:num.
Proof. by []. Qed.

(** x^oo = lim_{p -> oo} x^p on [0, oo]: 0 below 1, 1 at 1, +oo above 1. *)
Definition pow_infe x : \bar R :=
  if x < 1 then 0 else if x == 1 then 1 else +oo.

(** x^p on [0, oo] for a softness p in [-oo, +oo] (Section
    "Interpretation of the logical constants"): x^0 = 1 for every x,
    positive finite powers are poweR, negative ones go through the
    involution, and the infinite ones are the limits [pow_infe]. *)
Definition powO (p : \bar R) x : \bar R :=
  match p with
  | p'%:E => if p' == 0%R then 1
             else if (0 < p')%R then x `^ p'
             else x^-1 `^ (- p')
  | +oo => pow_infe x
  | -oo => pow_infe (x^-1)
  end.

Lemma powO_ge0 (p : \bar R) x : 0 <= x -> 0 <= powO p x.
Proof.
move=> x0; case: p => [p'| |] /=; rewrite ?/pow_infe.
- by case: ifP => _ //; case: ifP => _; exact: poweR_ge0.
- by case: ifP => _ //; case: ifP.
- by case: ifP => _ //; case: ifP.
Qed.

Definition pownnge (p : \bar R) a : {nonneg \bar R} :=
  mk_nng (powO_ge0 p (nngenum_ge0 a)).

Lemma pownnge_num (p : \bar R) a : (pownnge p a)%:num = powO p a%:num.
Proof. by []. Qed.

(** The composite (a^p ⊕ b^p)^(1/p) of (D6) is the p-sum of
    nonneg_ereal.v, for a finite softness 0 < p < oo. *)
Lemma pownnge_p_sum (p : R) (hp : (0 < p)%R) a b :
  pownnge ((p%:E)^-1) (addnnge (pownnge p%:E a) (pownnge p%:E b))
  = p_sum p%:E a b.
Proof.
apply/val_inj; rewrite /= /p_sum ltry/=.
rewrite /powO (gt_eqF hp) hp/= /inve/= (gt_eqF hp).
by rewrite invr_eq0 (gt_eqF hp) invr_gt0 hp.
Qed.

(** ** Measurability of the connectives (as actions on random elements) *)

(** Inversion is Borel on the non-negative extended reals. *)
Lemma measurable_funT_inve d (T : measurableType d) (f : T -> \bar R) :
  (forall t, 0 <= f t) -> measurable_fun setT f ->
  measurable_fun setT (fun t => (f t)^-1).
Proof.
move=> f0 mf.
rewrite [X in measurable_fun _ X](_ : _ = fun t =>
    if f t == 0 then +oo else if f t == +oo then 0 else (f t) `^ (-1)).
  apply: measurable_fun_ifT => //.
    by apply: measurable_fun_eqe mf _; exact: measurable_cst.
  apply: measurable_fun_ifT => //.
    by apply: measurable_fun_eqe mf _; exact: measurable_cst.
  exact: (measurableT_comp (@measurable_poweR R (-1)%R) mf).
apply/funext => t; have := f0 t.
case E : (f t) => [r| |]// => r0.
have [r_eq0|r_neq0] := eqVneq r 0%R.
  by rewrite r_eq0 eqxx inve0.
rewrite ifF; last by rewrite eqe (negbTE r_neq0).
by rewrite /inve (negbTE r_neq0) poweR_EFin powR_inv1.
Qed.

(** The limit power x^oo is Borel. *)
Lemma measurable_funT_pow_infe d (T : measurableType d) (f : T -> \bar R) :
  measurable_fun setT f -> measurable_fun setT (fun t => pow_infe (f t)).
Proof.
move=> mf; rewrite /pow_infe.
apply: measurable_fun_ifT => //.
  by apply: measurable_fun_lte mf _; exact: measurable_cst.
apply: measurable_fun_ifT => //.
by apply: measurable_fun_eqe mf _; exact: measurable_cst.
Qed.

(** The powers x^p are Borel on the non-negative extended reals. *)
Lemma measurable_funT_powO d (T : measurableType d) (p : \bar R)
    (f : T -> \bar R) :
  (forall t, 0 <= f t) -> measurable_fun setT f ->
  measurable_fun setT (fun t => powO p (f t)).
Proof.
move=> f0 mf; case: p => [p'| |] /=.
- have [_|p'neq0] := eqVneq p' 0%R; first exact: measurable_cst.
  have [p'pos|p'npos] := boolP (0 < p')%R.
    exact: (measurableT_comp (@measurable_poweR R p') mf).
  apply: (measurableT_comp (@measurable_poweR R (- p')%R)).
  exact: (measurable_funT_inve f0 mf).
- exact: (measurable_funT_pow_infe mf).
- by apply: measurable_funT_pow_infe; exact: (measurable_funT_inve f0 mf).
Qed.

End omega_operations.

(** ** The connectives as bundled QBS morphisms *)

Section omega_morphisms.
Variable R : realType.

Local Notation Omega := (OmegaQ R).

(** ⊗ : Omega × Omega -> Omega. *)
Section qbs_tens_instance.
Let f : prodQ Omega Omega -> Omega := fun p => mulnnge p.1 p.2.
Let hf : qbs_morphism f.
Proof. by move=> alpha h; exact: emeasurable_funM h.1 h.2. Qed.
HB.instance Definition _ :=
  @isQBSMorphism.Build R (prodQ Omega Omega) Omega f hf.
Definition qbs_tens : qbsHomType (prodQ Omega Omega) Omega := f.
End qbs_tens_instance.

(** ⊕ : Omega × Omega -> Omega. *)
Section qbs_plus_instance.
Let f : prodQ Omega Omega -> Omega := fun p => addnnge p.1 p.2.
Let hf : qbs_morphism f.
Proof. by move=> alpha h; exact: emeasurable_funD h.1 h.2. Qed.
HB.instance Definition _ :=
  @isQBSMorphism.Build R (prodQ Omega Omega) Omega f hf.
Definition qbs_plus : qbsHomType (prodQ Omega Omega) Omega := f.
End qbs_plus_instance.

(** (-)^* : Omega -> Omega. *)
Section qbs_inv_instance.
Let f : Omega -> Omega := @invnnge R.
Let hf : qbs_morphism f.
Proof.
move=> alpha h.
exact: (measurable_funT_inve (fun r => nngenum_ge0 (alpha r)) h).
Qed.
HB.instance Definition _ := @isQBSMorphism.Build R Omega Omega f hf.
Definition qbs_inv : qbsHomType Omega Omega := f.
End qbs_inv_instance.

(** (-)^p : Omega -> Omega. *)
Section qbs_pow_instance.
Variable p : \bar R.
Let f : Omega -> Omega := @pownnge R p.
Let hf : qbs_morphism f.
Proof.
move=> alpha h.
exact: (measurable_funT_powO p (fun r => nngenum_ge0 (alpha r)) h).
Qed.
HB.instance Definition _ := @isQBSMorphism.Build R Omega Omega f hf.
Definition qbs_pow : qbsHomType Omega Omega := f.
End qbs_pow_instance.

End omega_morphisms.

(** * Transpose: the missing half of cartesian closure

    quasi_borel.v provides evaluation [qbs_eval] and the partial
    application [qbs_curry f x]; here we show that the transpose
    x |-> f(x, -) is itself a QBS morphism X -> Z^Y, which is what the
    interpretation of Abs requires. *)

Section qbs_lam_instance.
Variables (R : realType) (X Y Z : qbsType R).
Variable f : qbsHomType (prodQ X Y) Z.

Let lam_fun : X -> expQ Y Z := fun x => qbs_curry f x.

Let lam_morph : qbs_morphism lam_fun.
Proof.
move=> alpha halpha beta [hb1 hb2].
have hpair : qbs_Mx (s := prodQ X Y)
    (fun r => (alpha ((beta r).1), (beta r).2)).
  by split => /=; [exact: (qbs_Mx_compT halpha hb1) | exact: hb2].
exact: (@qbs_hom_proof R (prodQ X Y) Z f _ hpair).
Qed.

HB.instance Definition _ :=
  @isQBSMorphism.Build R X (expQ Y Z) lam_fun lam_morph.

(** Transpose (currying) as a bundled QBS morphism X -> Z^Y. *)
Definition qbs_lam : qbsHomType X (expQ Y Z) := lam_fun.

End qbs_lam_instance.

(** * The model structure

    What the signature needs of the s-finite measure monad T on QBS
    (Definition "The monad T" of the paper), packaged as a record: the
    functor TQ together with the constants of Table tab:sig that involve
    it, each as a (bundled) QBS morphism.  Their equations (the monad
    laws, ∫-prog/∫-lin/∫-zero, mass ∘ factor = id, ...) belong to the
    soundness theorem and are deferred to a separate interface. *)

Record hqll_model (R : realType) := HQLLModel {
  TQ : qbsType R -> qbsType R ;
  (** return : A -> 𝒯 A *)
  retQ : forall X : qbsType R, qbsHomType X (TQ X) ;
  (** bind : 𝒯 A × (A -> 𝒯 B) -> 𝒯 B, uncurried *)
  bindQ : forall X Y : qbsType R,
    qbsHomType (prodQ (TQ X) (expQ X (TQ Y))) (TQ Y) ;
  (** ∫_A : 𝒯 A × (A -> Omega) -> Omega, uncurried *)
  intQ : forall X : qbsType R,
    qbsHomType (prodQ (TQ X) (expQ X (OmegaQ R))) (OmegaQ R) ;
  (** factor : Omega -> 𝒯 1,  a |-> a · δ_* *)
  factorQ : qbsHomType (OmegaQ R) (TQ (unitQ R)) ;
  (** mass : 𝒯 1 -> Omega,  m |-> m({*}) *)
  massQ : qbsHomType (TQ (unitQ R)) (OmegaQ R) ;
  (** norm : 𝒯 A -> 𝒯 A, normalisation *)
  normQ : forall X : qbsType R, qbsHomType (TQ X) (TQ X) }.

(** * Interpretation *)

Section semantics.
Context {R : realType} (M : hqll_model R).

Local Open Scope ty_scope.

(** ** Types (Section "Types and contexts")

    [[1]] = 1, [[RR]] = RR, [[Omega]] = [0, oo], [[A × B]] = [[A]] × [[B]],
    [[A -> B]] = [[B]]^[[A]], [[𝒯 A]] = T [[A]]. *)
Fixpoint sem_ty (A : ty) : qbsType R :=
  match A with
  | TUnit => unitQ R
  | TReal => realQ R
  | TOmega => OmegaQ R
  | TProd A B => prodQ (sem_ty A) (sem_ty B)
  | TArr A B => expQ (sem_ty A) (sem_ty B)
  | TMeas A => TQ M (sem_ty A)
  end.

(** The model signature: the symbols for constant s-finite measures on
    [[A]] are the points of T [[A]] (the realisation promised in
    syntax.v, where [meas] is abstract). *)
Definition sem_sig : signature R := Signature R (fun A => TQ M (sem_ty A)).

(** ** Contexts: [[Γ]] is the product of the types of Γ, [[◇]] = 1. *)
Fixpoint sem_ctx (G : ctx) : qbsType R :=
  if G is A :: G' then prodQ (sem_ctx G') (sem_ty A) else unitQ R.

(** ** Variables are projections. *)
Fixpoint sem_var G A (x : var G A) :
    qbsHomType (sem_ctx G) (sem_ty A) :=
  match x in var G A return qbsHomType (sem_ctx G) (sem_ty A) with
  | vz _ _ => qbs_snd _ _
  | vs _ _ _ y => qbs_comp (qbs_fst _ _) (sem_var y)
  end.

(** ** Constants (Table tab:sig and Section "Interpretation of the
       logical constants")

    A constant c : A denotes a point of [[A]]; for a higher-order
    constant that point is a bundled morphism, obtained by transposing
    ([qbs_lam]) its uncurried interpretation. *)
Definition sem_const A (c : const sem_sig A) : sem_ty A :=
  match c in const _ A return sem_ty A with
  | CStar => tt
  | CPair A B => qbs_lam (qbs_id (prodQ (sem_ty A) (sem_ty B)))
  | CFst A B => qbs_fst (sem_ty A) (sem_ty B)
  | CSnd A B => qbs_snd (sem_ty A) (sem_ty B)
  | CZero => 0%:E%:nng
  | COne => 1%:E%:nng
  | CTens => qbs_lam (qbs_tens R)
  | CPlus => qbs_lam (qbs_plus R)
  | CInv => qbs_inv R
  | CPow p => qbs_pow p
  | CInt A => qbs_lam (intQ M (sem_ty A))
  | CRet A => retQ M (sem_ty A)
  | CBind A B => qbs_lam (bindQ M (sem_ty A) (sem_ty B))
  | CSample A mu => mu
  | CFactor => factorQ M
  | CMass => massQ M
  | CNorm A => normQ M (sem_ty A)
  end.

(** ** Terms (Section "Terms")

    [[x]] is a projection, [[c]] a constant morphism at the point [[c]],
    [[λx : A. M]] = cur([[M]]) and [[M N]] = ev ∘ ⟨[[M]], [[N]]⟩. *)
Fixpoint sem_tm G A (t : tm sem_sig G A) :
    qbsHomType (sem_ctx G) (sem_ty A) :=
  match t in tm _ _ A return qbsHomType (sem_ctx G) (sem_ty A) with
  | Var _ x => sem_var x
  | Con _ c => qbs_const _ (sem_const c)
  | Abs _ _ M => qbs_lam (sem_tm M)
  | App _ _ M N => qbs_comp (qbs_pair (sem_tm M) (sem_tm N)) (qbs_eval _ _)
  end.

End semantics.

(** * Sanity checks

    The interpretation computes: the CCC equations used implicitly in
    the paper hold by conversion, and the interpretation of the derived
    constants (D1)-(D9) unfolds to the expected operations of
    Section "Interpretation of the logical constants". *)

Section examples.
Context {R : realType} (M : hqll_model R).
Local Open Scope hqll_scope.

Local Notation tmM := (tm (sem_sig M)).

(** β at the level of points: [[(λx. M) N]](g) = [[M]](g, [[N]](g)). *)
Example sem_beta G A B (N : tmM G A) (P : tmM (A :: G) B) g :
  (sem_tm (App (Abs P) N) : _ -> _) g
  = (sem_tm P : _ -> _) (g, (sem_tm N : _ -> _) g).
Proof. by []. Qed.

(** [[⊥]] = 0 and [[⊤]] = oo (D1)-(D3). *)
Example sem_bot G g : (sem_tm (Bot : tmM G TOmega) : _ -> _) g = 0%:E%:nng.
Proof. by []. Qed.

Example sem_top G g :
  (sem_tm (Top : tmM G TOmega) : _ -> _) g = +oo%:nng.
Proof. by apply/val_inj; rewrite /= inve0. Qed.

(** [[φ ⊗ ψ]](g) = [[φ]](g) ⊗ [[ψ]](g), multiplication with 0 · oo = 0. *)
Example sem_tens G (phi psi : tmM G TOmega) g :
  (sem_tm (phi ⊗ psi) : _ -> _) g
  = mulnnge ((sem_tm phi : _ -> _) g) ((sem_tm psi : _ -> _) g).
Proof. by []. Qed.

(** [[∫_{x ~ ν} φ]](g) = [[∫]]([[ν]](g), [[λx. φ]](g)), the first
    unwinding equation of Section "Logic operators". *)
Example sem_int_x G A (nu : tmM G (TMeas A)) (phi : tmM (A :: G) TOmega) g :
  (sem_tm (Int_x nu phi) : _ -> _) g
  = (intQ M (sem_ty M A) : _ -> _)
      ((sem_tm nu : _ -> _) g, qbs_curry (sem_tm phi) g).
Proof. by []. Qed.

(** The derived disjunction (D6) computes to the p-sum of
    nonneg_ereal.v: [[φ ∨^p ψ]](g) = p_sum p ([[φ]]g) ([[ψ]]g) for
    finite p > 0. *)
Example sem_por_fin G (p : R) (hp : (0 < p)%R) (phi psi : tmM G TOmega) g :
  (sem_tm (phi ∨ [ p%:E ] psi) : _ -> _) g
  = p_sum p%:E ((sem_tm phi : _ -> _) g) ((sem_tm psi : _ -> _) g).
Proof. exact: pownnge_p_sum hp _ _. Qed.

(** Caveat on the softness p = oo (reported as a paper issue): with the
    conventions of Section "Interpretation of the logical constants"
    ((+oo)^-1 = 0 and a^0 = 1), the outer power of the *derived* (D8)
    collapses, so [[∃^oo (x ~ ν). φ]] is the constant 1 — not the
    essential supremum claimed in the remark after (D9).  The hard
    quantifiers need to be primitives (or (D6)-(D9) restricted to
    finite p, with the p = oo instances defined separately, as p_sum
    does in nonneg_ereal.v). *)
Example sem_exists_oo_collapses G A (nu : tmM G (TMeas A))
    (phi : tmM (A :: G) TOmega) g :
  (sem_tm (Exists_x +oo nu phi) : _ -> _) g = 1%:E%:nng.
Proof. by apply/val_inj; rewrite /= eqxx. Qed.

End examples.
