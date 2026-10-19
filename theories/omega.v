From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets boolp interval_inference constructive_ereal ereal exp.
From HQLL Require Import interval_einference algebra_order_utils nonneg_ereal.

(**md**************************************************************************)
(* # The algebra of truth values Omega = [0, oo]                              *)
(*                                                                            *)
(* The operations of Section "Interpretation of the logical constants" on    *)
(* the non-negative extended reals {nonneg \bar R}: ⊗ and ⊕ are [mulnnge]     *)
(* (nonneg_ereal.v) and [addnnge], the involution (-)^* is [invnnge], and the *)
(* powers (-)^p for p in [-oo, +oo] are [pownnge].  [powO] is the same power  *)
(* function on the carrier \bar R.                                            *)
(*                                                                            *)
(* They are shared by the equational theory (equational.v), whose axiom      *)
(* schema for Omega quantifies over the identities of this algebra, and by   *)
(* the semantics (semantics.v), which interprets the constants by them; the  *)
(* measurability of the operations is proved in semantics.v.                 *)
(*                                                                            *)
(* ```                                                                        *)
(*            mk_nng x0 == x : \bar R packaged as {nonneg \bar R} from 0 <= x *)
(*           addnnge a b == a ⊕ b = a + b                                      *)
(*             powO p x == x^p on \bar R, with x^0 = 1, x^(-p) = (x^-1)^p,    *)
(*                         x^(+oo) = lim x^p in {0, 1, oo} and                *)
(*                         x^(-oo) = (x^-1)^(+oo)                             *)
(*          pownnge p a == a^p on {nonneg \bar R}                             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section omega_algebra.
Variable R : realType.

Implicit Types (a b : {nonneg \bar R}) (x : \bar R).

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

End omega_algebra.
