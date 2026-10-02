From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets functions mathcomp_extra.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology tvs normedtype landau sequences derive.
From mathcomp Require Import realfun interval_inference convex interval exp lebesgue_integral.
From mathcomp Require Import hoelder counting_measure cardinality measure all_algebra.
From mathcomp Require Import ess_sup_inf finmap ring lra.

From HQLL Require Import interval_einference algebra_order_utils.

Import Order.TTheory GRing.Theory Num.Theory.

(** * Connectives on the Non-negative Extended Reals *)
(** ** Definitions **)
Section definitions.

Context {R: realType}.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.

(** Inversion of non-negative extended reals *)
Definition invnnge (a: {nonneg \bar R}) := a%:num^-1%:nng.

(** Multiplication of non-negative extended reals *)
Definition mulnnge (a b: {nonneg \bar R}) := (a%:num * b%:num)%:nng.

(** Comultiplication of non-negative extended reals *)
Definition comulnnge (a b: {nonneg \bar R}) :=
  invnnge (mulnnge (invnnge a) (invnnge b)).

(** Division of non-negative extended reals *)
Definition divnnge (a b: {nonneg \bar R}) := comulnnge (invnnge a) b.

(** Core part of p-sum's definition *)
Definition p_sum (p: \bar R) (a b: {nonneg \bar R}) :=
  if p < +oo then
    ((a%:num `^ (fine p) + b%:num `^ (fine p)) `^ (fine p)^-1)%:nng
  else
    maxe a b.

(** (harmonic) p-sum, both for positive p and negative p *)
Definition p_sum_de_morgan (p: \bar R) (a b: {nonneg \bar R}): {nonneg \bar R} :=
  if (p > 0%R) then
    p_sum p a b
  else if (p < 0%R) then
    invnnge (p_sum (-p) (invnnge a) (invnnge b))
  else 0%:E%:nng.

End definitions.

Declare Scope nngereal_scope.

Notation "x `*" := (invnnge x) : nngereal_scope.
Notation "x -o y" := (divnnge x y) (at level 51, right associativity) : nngereal_scope.
Notation "x ⊗ y" := (mulnnge x y) (at level 46, left associativity) : nngereal_scope.
Notation "x ⊗* y" := (comulnnge x y) (at level 46, left associativity) : nngereal_scope.
Notation "x ⊕ [ p ] y" := (p_sum_de_morgan p x y) (at level 50, left associativity) : nngereal_scope.

Delimit Scope nngereal_scope with NNGE.

(** ** Properties of the Multiplicative Fragment *)
Section results.

Context {R: realType}.

Open Scope classical_set_scope.
Open Scope ring_scope.
Open Scope order_scope.
Open Scope ereal_scope.
Open Scope nngereal_scope.

Lemma invnnge_involutive:
  involutive (fun a: {nonneg \bar R} => a `*).
Proof.
  rewrite /involutive /cancel /invnnge /= => a.
  apply/val_inj => /=. by rewrite inveK.
Qed.

Lemma invnng0:
  (0 : R)%:E%:nng `* = +oo%:nng.
Proof.
  apply/val_inj => /=.
  have ->: 0%:E = 0%R by done.
  by rewrite inve0.
Qed.

Lemma invnngy:
  +oo%:nng `* = (0 : R)%:E%:nng.
Proof.
  apply/val_inj => /=. by rewrite invey.
Qed.

Lemma le_minvnnge:
  {homo (@invnnge R) : a b /~ (a <= b)%O}.
Proof.
  move=> a b Hb_lea.
  suff /=: ((a `*)%:num <= (b `*)%:num) by done.
  by rewrite lee_pV2 // inE.
Qed.

Lemma comulnnge_invnnge (a b: {nonneg \bar R}):
  (a ⊗* b) `* = a `* ⊗ b `*.
Proof.
  by rewrite /comulnnge invnnge_involutive.
Qed.

Lemma mulnngeC:
  commutative (fun (a b: {nonneg \bar R}) => a ⊗ b).
Proof.
  move=> a b. apply/val_inj => /=.
  by rewrite muleC.
Qed.

Lemma mulnngeA:
  associative (fun (a b: {nonneg \bar R}) => a ⊗ b).
Proof.
  move=> a b c. apply /val_inj => /=.
  by rewrite muleA.
Qed.

Lemma mul0nng (a b: {nonneg \bar R}):
  a%:num = 0 -> a ⊗ b = 0%:E%:nng.
Proof.
  move=> Ha. apply /val_inj => /=.
  by rewrite Ha mul0e.
Qed.

Lemma mulnng0 (a b: {nonneg \bar R}):
  b%:num = 0 -> a ⊗ b = 0%:E%:nng.
Proof.
  move=> Hb. apply /val_inj => /=.
  by rewrite Hb mule0.
Qed.

Lemma mul1nng (a b: {nonneg \bar R}):
  a%:num = 1 -> a ⊗ b = b.
Proof.
  move=> Ha. apply /val_inj => /=.
  by rewrite Ha mul1e.
Qed.

Lemma mulnng1 (a b: {nonneg \bar R}):
  b%:num = 1 -> a ⊗ b = a.
Proof.
  move=> Hb. apply /val_inj => /=.
  by rewrite Hb mule1.
Qed.

Lemma gt0_mulnngy (a b: {nonneg \bar R}):
  0 < a%:num -> b%:num = +oo -> a ⊗ b = +oo%:nng.
Proof.
  move=> Ha_gt0 Hb_eq0. apply/val_inj => /=.
  by rewrite Hb_eq0 gt0_muley.
Qed.

Lemma gt0_mulynng (a b: {nonneg \bar R}):
  0 < b%:num -> a%:num = +oo -> a ⊗ b = +oo%:nng.
Proof.
  rewrite mulnngeC. by apply gt0_mulnngy.
Qed.

Lemma mulnnge_left_monotone (a a' b: {nonneg \bar R}):
  (a <= a')%O -> (a ⊗ b <= a' ⊗ b)%O.
Proof.
  move=> Ha_leqa'. by apply: lee_pmul.
Qed.

Lemma mulnnge_right_monotone (a b b': {nonneg \bar R}):
  (b <= b')%O -> (a ⊗ b <= a ⊗ b')%O.
Proof.
  move=> Ha_leqa'. by apply: lee_pmul.
Qed.

Remark mulnnge_not_idempotent:
  (2: \bar R)%:nng ⊗ 2%:nng != 2%:nng.
Proof.
  apply/eqP => Heq.
  inversion Heq.
  move: H0. by lra.
Qed.

Lemma comulnngeC : commutative (fun a b : {nonneg \bar R} => a ⊗* b).
Proof. by move=> a b; rewrite /comulnnge mulnngeC. Qed.

Lemma comulnngeA : associative (fun a b : {nonneg \bar R} => a ⊗* b).
Proof. by move=> a b c; rewrite /comulnnge !invnnge_involutive mulnngeA. Qed.

Lemma comulynng (a b: {nonneg \bar R}):
  a%:num = +oo -> a ⊗* b = +oo%:nng.
Proof.
  move=> Ha. apply/val_inj => /=.
  by rewrite Ha invey mul0e inve0.
Qed.

Lemma comulnngy (a b: {nonneg \bar R}):
  b%:num = +oo -> a ⊗* b = +oo%:nng.
Proof.
  move=> Hb. apply/val_inj => /=.
  by rewrite Hb invey mule0 inve0.
Qed.

Lemma comul1nng (a b: {nonneg \bar R}):
  a%:num = 1 -> a ⊗* b = b.
Proof.
  move=> Ha. apply /val_inj => /=.
  by rewrite Ha inve1 mul1e inveK.
Qed.

Lemma comulnng1 (a b: {nonneg \bar R}):
  b%:num = 1 -> a ⊗* b = a.
Proof.
  move=> Hb. apply /val_inj => /=.
  by rewrite Hb inve1 mule1 inveK.
Qed.

Lemma lty_comulnng0 (a b: {nonneg \bar R}):
  a%:num < +oo -> b%:num = 0 -> a ⊗* b = 0%:E%:nng.
Proof.
  move=> Ha_lty Hb_eq0. apply/val_inj => /=.
  have [->|Ha_neq0] := eqVneq (a%:num) 0.
  - by rewrite Hb_eq0 inve0. 
  - rewrite Hb_eq0 inve0 gt0_muley ?inve_gt0 //.
    + rewrite lt0e. apply/andP. by split.
    + by rewrite -lteey.
Qed.

Lemma lty_comul0nng (a b: {nonneg \bar R}):
  b%:num < +oo -> a%:num = 0 -> a ⊗* b = 0%:E%:nng.
Proof.
  rewrite comulnngeC. by apply lty_comulnng0.
Qed.

Lemma comulnnge_left_monotone (a a' b: {nonneg \bar R}):
  (a <= a')%O -> (a ⊗* b <= a' ⊗* b)%O.
Proof.
  move=> Ha_leqa'. suff: (a ⊗* b)%:num <= (a' ⊗* b)%:num by done.
  rewrite /comulnnge /invnnge /= inve_ple ?inE //.
  rewrite inveK. apply: lee_pmul => //.
  by rewrite inve_ple ?inE // inveK.
Qed.

Lemma comulnnge_right_monotone (a b b': {nonneg \bar R}):
  (b <= b')%O -> (a ⊗* b <= a ⊗* b')%O.
Proof.
  rewrite (comulnngeC _ b) (comulnngeC _ b').
  by apply comulnnge_left_monotone.
Qed.

Remark comulnnge_not_idempotent:
  (2: \bar R)%:nng ⊗* 2%:nng != 2%:nng.
Proof.
  apply/eqP. rewrite /comulnnge /invnnge /= => Heq.
  inversion Heq.
  rewrite inveM in H0.
  - rewrite inveK /= in H0.
    suff: ((2: R) * 2)%R = 2%R by lra.
    by apply EFin_inj in H0.
  - by rewrite fin_inveM_def ?fin_numV ?gt_eqF ?inve_gt0// ltNye.
Qed.

Lemma fin_gt0_comulnnge_eq_mulnnge (r s: R):
  0 < r%:E -> 0 < s%:E -> (r%:E^-1 * s%:E^-1)^-1 = r%:E * s%:E.
Proof.
  move=> Hr Hs.
  rewrite -inveM; last by (apply: fin_inveM_def_by_ineq; try apply: ltry).
  by rewrite inveK.
Qed.

Lemma comulnngery_eq_mulnngery (r: R):
  0 < r%:E -> (r%:E^-1 * +oo^-1)^-1 = r%:E * +oo.
Proof.
  move=> Hr.
  by rewrite gt0_muley // invey mule0 inve0.
Qed.

Lemma comulnnger0_eq_mulnnger0 (r: R):
  0 < r%:E -> (r%:E^-1 * 0^-1)^-1 = r%:E * 0.
Proof.
  move=> Hr.
  rewrite inve0 mule0 gt0_muley; first by rewrite invey.
  rewrite inve_gt0 //. apply/eqP. move=> H. rewrite H in Hr.
  by rewrite ltxx in Hr.
Qed.

Lemma neq0y_comulnnge_eq_mulnnge (a b: {nonneg \bar R}):
  (0 < a%:num \/ b%:num < +oo) /\ (0 < b%:num \/ a%:num < +oo)
     -> a ⊗* b = a ⊗ b.
Proof.
  move=> [[Ha1|Hb1] [Hb2|Ha2]]; apply/val_inj => /=.
  - move: (gt0_nng_posy Ha1) (gt0_nng_posy Hb2).
    move => [->|[r Hr ->]] [->|[s Hs ->]].
    + by rewrite invey mul0e inve0 gt0_muley.
    + by rewrite muleC (muleC +oo) comulnngery_eq_mulnngery.
    + by rewrite comulnngery_eq_mulnngery.
    + by rewrite fin_gt0_comulnnge_eq_mulnnge.
  - move: (gt0_nng_posy Ha1) => [Ha|[r Hr Hr']].
    + by rewrite Ha in Ha2.
    + rewrite Hr'. move: (nng_0posy b) => [->|[->|[s Hs ->]]].
      * by rewrite comulnngery_eq_mulnngery.
      * by rewrite comulnnger0_eq_mulnnger0.
      * by rewrite fin_gt0_comulnnge_eq_mulnnge.
  - move: (gt0_nng_posy Hb2) => [Hb|[r Hr Hr']].
    + by rewrite Hb in Hb1.
    + rewrite Hr'. move: (nng_0posy a) => [->|[->|[s Hs ->]]].
      * by rewrite muleC (muleC +oo) comulnngery_eq_mulnngery.
      * by rewrite muleC (muleC 0%R) comulnnger0_eq_mulnnger0.
      * by rewrite fin_gt0_comulnnge_eq_mulnnge.
  - move: (lty_nng_0pos Ha2) (lty_nng_0pos Hb1).
    move => [->|[r Hr ->]] [->|[s Hs ->]].
    + by rewrite !inve0 mule0 invey.
    + by rewrite muleC (muleC 0%R) comulnnger0_eq_mulnnger0.
    + by rewrite comulnnger0_eq_mulnnger0.
    + by rewrite fin_gt0_comulnnge_eq_mulnnge.
Qed.

Lemma mul_le_comul (a b : {nonneg \bar R}): (a ⊗ b <= a ⊗* b)%O.
Proof.
  rewrite le_nng_eq_e.
  move: (nng_0posy a) => [Hay|[Ha0|[r Hr Ha_eqr]]].
  - rewrite comulynng //=. by apply: leey.
  - rewrite mul0nng //=. by have ->: 0%:E = (0: \bar R)%R by done.
  - move: (nng_0posy b) => [Hby|[Hb0|[s Hs Hb_eqs]]].
    + rewrite comulnngy //=. by apply: leey.
    + by rewrite mulnng0 //= [leLHS](_ : _ = 0).
    + rewrite /= Ha_eqr Hb_eqs inveM; first by rewrite !inveK.
      by apply fin_inveM_def; (try by rewrite inve_eq0);
        apply pos_implies_fin_num.
Qed.

Lemma mul_comul_linear_distributivity (a b c: {nonneg \bar R}):
  ((a ⊗* b) ⊗ c <= a ⊗* (b ⊗ c))%O.
Proof.
  move: (nng_0posy a). move => [Ha_eqy|[Ha_eq0|[r Hr Ha_eqr]]].
  - rewrite (comulynng a (b ⊗ c)) //. by apply: leey.
  - move: (nng_0posy b). move => [Hb_eqy|[Hb_eq0|[s Hs Hb_eqs]]].
    + rewrite (comulnngy a) //.
      move: (nng_0posy c). move => [Hc_eqy|[Hc_eq0|[t Ht Hc_eqt]]].
      * have ->: (b ⊗ c) = +oo%:nng.
          by apply/val_inj => /=; rewrite Hb_eqy Hc_eqy gt0_muley.
        rewrite comulnngy //. by apply: leey.
      * rewrite mulnng0 //=.
        suff: 0 <= (a ⊗* (b ⊗ c))%:num by done.
        done.
      * have ->: (b ⊗ c) = +oo%:nng.
          by apply/val_inj => /=; rewrite Hb_eqy Hc_eqt gt0_mulye.
        rewrite comulnngy //. by apply: leey.
    + have ->: a ⊗* b = 0%:E%:nng.
        by apply/val_inj => /=; rewrite Ha_eq0 Hb_eq0 !inve0 gt0_muley.
      rewrite mul0nng //.
      suff: 0 <= (a ⊗* (b ⊗ c))%:num by done.
      done.
    + move: (nng_0posy c). move => [Hc_eqy|[Hc_eq0|[t Ht Hc_eqt]]].
      * have ->: (b ⊗ c) = +oo%:nng.
          by apply/val_inj => /=; rewrite Hb_eqs Hc_eqy gt0_muley.
        rewrite (comulnngy a +oo%:nng) //.
        by apply: leey.
      * rewrite (mulnng0 (a ⊗* b)) //.
        suff: 0 <= (a ⊗* (b ⊗ c))%:num by done.
        done.
      * rewrite (neq0y_comulnnge_eq_mulnnge a b);
          first by (rewrite -mulnngeA; apply mul_le_comul).
        by split; [right; rewrite Hb_eqs; apply: ltry | right; rewrite Ha_eq0].
  - rewrite (neq0y_comulnnge_eq_mulnnge a b);
      first by (rewrite -mulnngeA; apply mul_le_comul).
    by split; rewrite Ha_eqr; [left | right; apply: ltry].
Qed.

Lemma mul_comul_equiv (a b c : {nonneg \bar R}):
  (a ⊗ b <= c`*)%O <-> (a <= (b ⊗ c)`*)%O.
Proof.
  suff: ((a ⊗ b)%:num <= c`*%:num) <-> (a%:num <= (b ⊗ c)`*%:num) by done.
  split.
  - move: (nng_0pos a) => /= [->|Ha] Hineq; first by rewrite inve_ge0.
    move: (nng_0pos b) Hineq => /= [->|Hb] Hineq.
    * rewrite mul0e inve0. by apply (leey (a%:nngnum)).
    * have Hc: c%:num < +oo.
      suff: c%:num != +oo by rewrite ltey.
      apply/eqP. move=> Hc. rewrite Hc invey in Hineq.
      have: 0%R < a%:num * b%:num by apply mule_gt0.
      by move: (le_gtF Hineq) => ->.
      move: (nng_0pos c) Hineq => [->|Hc'] Hineq; first by rewrite mule0 inve0 leey.
      have Hineq': a%:num * b%:num < +oo.
      apply (le_lt_trans Hineq).
      move: Hc'. rewrite ltey lt0e. move=> /andP [/eqP Hc' _].
      apply/eqP. move=> Hc''. apply Hc'. rewrite -invey.
      have <-: c%:num^-1^-1 = +oo^-1 by apply f_equal.
      by rewrite inveK.
      move: (mule_lty_gt0 a%:num b%:num Ha Hb Hineq') => /andP [Ha' Hb'].
      rewrite inveM.
      + rewrite -(mule1 a%:nngnum) muleC.
        have Hb'': b%:num != 0%R by move: Hb; rewrite lt0e; move=> /andP [// _].
        rewrite -(@divee _ b%:num); last done; last by apply nngNy_fin_num.
        rewrite (muleC b%:nngnum b%:nngnum^-1). rewrite muleC in Hineq.
        move: (@lee_pmul _ (b%:num^-1) (b%:num^-1) (b%:num * a%:num) (c%:num^-1)).
        rewrite inve_ge0 muleA.
        have Hineq'': 0%R <= b%:nngnum * a%:nngnum.
          by apply ltW in Ha, Hb; apply mule_ge0. 
        move=> /(_ (ltW Hb) Hineq'') Hdone. by apply Hdone.
      + move: Hc' Hb. rewrite !lt0e. move=> /andP [Hc' Hc''] /andP [Hb Hb''].
        by apply fin_inveM_def; try done; apply nngNy_fin_num. 
  - move: (nng_0pos a) => /= [->|Ha] Hineq; first by rewrite mul0e inve_ge0.
    move: (nng_0pos b) => /= [->|Hb]; first by rewrite mule0 inve_ge0.
    have Hc: c%:num < +oo.
      suff: c%:num != +oo by rewrite ltey.
      apply/eqP. move=> Hc. rewrite Hc in Hineq.
      rewrite gt0_muley // invey in Hineq. by move: (lt_geF Ha) Hineq => ->.
    move: (nng_0pos c) => [->|Hc'];
      first by (rewrite inve0; apply (leey (a%:nngnum * b%:nngnum))).
    have Hb': b%:num < +oo.
      rewrite ltey. apply/eqP. move=> Hb'.
      by rewrite Hb' (gt0_mulye Hc') invey (lt_geF Ha) in Hineq.
    rewrite inveM in Hineq; last by apply fin_inveM_def_by_ineq.
    rewrite muleC.
    move: (@lee_pmul _ (b%:num) (b%:num) (a%:num) (b%:num^-1 / c%:num)).
    move=> /(_  (ltW Hb) (ltW Ha) _ Hineq). rewrite muleA.
    have Hb'': (b%:num != 0%R).
      by move: Hb; rewrite lt0e; move=> /andP [// _].
    rewrite (@divee _ b%:num) //; last by (apply nngNy_fin_num; apply ltW in Hb).
    rewrite mul1e. move=> Hineq'. by apply Hineq'.
Qed.

Lemma div_adjoint (a b c: {nonneg \bar R}):
  (a <= b -o c)%O <-> (a ⊗ b <= c)%O.
Proof.
  suff: a%:num <= (b -o c)%:num <-> (a ⊗ b)%:num <= c%:num by done.
  rewrite /divnnge /=. split; rewrite inveK; move=> Hineq.
  - move: (mul_comul_equiv a b (c `*)) => [_ H]. rewrite -(inveK c%:num).
    by apply H.
  - move: (mul_comul_equiv a b (c `*)) => [H _]. apply H.
    by rewrite /= invnnge_involutive.
Qed.

(** ** Properties of the Additive Fragment *)
(** p-sum and harmonic p-sum are dual to each other *)
Lemma p_sum_duality (p: \bar R) (a b: {nonneg \bar R}):
  p != 0 -> a ⊕[p] b = ((a `*) ⊕[-p] (b `*)) `*.
Proof.
  move=> Hp. rewrite /p_sum_de_morgan.
  destruct (0%R < p) eqn:E.
  - have ->: 0%R < -p = false by rewrite oppe_gt0; apply lt_gtF.
    by rewrite -oppe_gt0 !oppeK E !invnnge_involutive.
  - have Hp': p < 0%R.
      by move: (lt_total Hp) => /orP [//|H]; rewrite E in H.
    have ->: 0%R < -p by rewrite oppe_gt0.
    by rewrite Hp'.
Qed.

Lemma p_sum_inv (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> (a ⊕[p] b) `* = a `* ⊕[-p] b `*.
Proof.
by move=> Hp_gt0; rewrite (p_sum_duality _ a b) ?invnnge_involutive // gt_eqF.
Qed.

Lemma harmonic_p_sum_inv (a b : {nonneg \bar R}) (p : \bar R) :
  p < 0 -> (a ⊕[p] b) `* = a `* ⊕[-p] b `*.
Proof.
move=> p0.
by rewrite (p_sum_duality _ a b) ?invnnge_involutive// lt_eqF.
Qed.

Lemma p_sum_fin (p: R) (a b: {nonneg \bar R}):
  (0 < p)%R -> a ⊕[p%:E] b =  ((a%:num `^ p + b%:num `^ p)%E `^ p^-1)%:nng.
Proof.
  move=> Hp. apply/val_inj => /=.
  rewrite /p_sum_de_morgan. have ->: 0%R < p%:E by done.
  by rewrite /p_sum ltry.
Qed.

(** 1-sum is just addition *)
Lemma p_sum_1 (a b: {nonneg \bar R}):
  a ⊕[1] b = (adde a%:num b%:num)%:nng.
Proof.
  rewrite p_sum_fin //. apply/val_inj => /=.
  by rewrite invr1 !poweRe1 //.
Qed.

Lemma harmonic_p_sum_fin (p : R) (a b : {nonneg \bar R}):
  (p < 0)%R -> a ⊕[p%:E] b =
  (((a `*)%:num `^ (-p) + (b `*)%:num `^ (-p)) `^ (-p)^-1)%:nng`*.
Proof.
move=> p0; apply/val_inj => /=.
by rewrite p_sum_duality ?lt_eqF// p_sum_fin//= oppr_gt0.
Qed.

Lemma harmonic_p_sum_1 (a b: {nonneg \bar R}):
  a ⊕[-1] b = (adde a%:num^-1 b%:num^-1)^-1%:nng.
Proof.
  rewrite harmonic_p_sum_fin //=.
  apply/val_inj => /=. rewrite opprK invr1.
  by rewrite !poweRe1 //.
Qed.

(** The following shows that we can't define harmonic
   p-sum by the formula ((a%:num `^ p) + (b%:num `^ p)) `^ (1/p)
   as this would result in errors if a = 0 or b = 0 as evidenced
   by the subsequent lemma: The computation yields 1,
   whereas Capucci defines harmonic p-sum as 0 if either
   summand is 0, so the case analysis in neg_p_sum_notNy
   is needed *)
Remark harmonic_p_sum_naive_incorrect:
  (((0: R)%:E `^ (-1)) + (1 `^ (-1))) `^ (-1^-1) = 1.
Proof.
  by rewrite poweR0r // add0e !poweR1r.
Qed.

(** oo-sum is just binary maximum *)
Lemma p_sum_y (a b: {nonneg \bar R}):
  a ⊕[+oo] b = (maxe a b).
Proof.
  apply/val_inj => /=.
  rewrite /p_sum_de_morgan /= lt0y /p_sum.
  have ->: (+oo: \bar R) < +oo = false by done.
  done.
Qed.

(** harmonic -oo-sum is just binary minimum *)
Lemma harmonic_p_sum_Ny (a b: {nonneg \bar R}):
  a ⊕[-oo] b = (mine a b).
Proof.
  apply/val_inj => /=.
  rewrite p_sum_duality //= p_sum_y maxe_translation /=.
  have /orP [Ha_ltb|Hb_lta] := le_total a%:num b%:num.
  - rewrite max_l ?inveK ?min_l //.
    by rewrite lee_pV2 //= /in_mem /=.
  - rewrite max_r ?inveK //= ?min_r //.
    by rewrite lee_pV2 //= /in_mem /=.
Qed.

(** p-sums can equivalently be defined as certain Lebesgue integrals.
    The lemma p_sum_integral_correct
    establishes the correspondence between both definitions. *)
Definition p_sum_int_fun (a b: {nonneg \bar R}) (n: nat) :=
  if n == 0%N then a else if n == 1%N then b else 0%:E%:nng.

Definition p_sum_integral (p: \bar R) (a b: {nonneg \bar R}) :=
  'N[counting]_p [(fun n => (p_sum_int_fun a b n)%:num)].

Lemma p_sum_integral_fine (p : R) (a b: {nonneg \bar R}):
  (0 < p)%R -> p_sum_integral p%:E a b =
                  ((a%:num `^ p) + (b%:num `^ p)) `^ p^-1.
Proof.
  intros Hp. rewrite /p_sum_integral.
  rewrite (Lnorm_generalised_counting p (fun n => (p_sum_int_fun a b n)%:num)) //;
    last by apply lt0r_neq0.
  rewrite (nneseries_split _ 2).
  - rewrite eseries0.
    * have ->: (0%nat + 2%nat)%nat = 2%nat by rewrite add0n.
      rewrite addr0 big_ltn // big_ltn //.
      rewrite big_geq //=. rewrite !gee0_abs //.
      by rewrite addr0.
    * rewrite /p_sum_int_fun //=.
      move=> [|[|i]] _ _ //=. rewrite normr0.
      by rewrite powR0 //= lt0r_neq0. (* x `^ 1 for x < 0 is not defined *)
  - by move=> [|[|k]] _ //=; apply poweR_ge0.
Qed.

Lemma p_sum_integral_y (a b: {nonneg \bar R}):
  p_sum_integral +oo a b = maxe a%:num b%:num.
Proof.
  rewrite /p_sum_integral.
  rewrite unlock /Lnorm /= counting_nat.
  (* abse is absolute value for extended real *)
  (* \o is function composition *)
  apply le_anti. apply /andP. split.
  - apply /ess_supP. exists set0. split; try done.
    apply subsetCl. rewrite setC0.
    move=> [|[|_]] _ /=; rewrite /p_sum_int_fun ?gee0_abs // num_lee_max; apply /orP.
    * by left.
    * by right.
    * left. rewrite normr0. by apply: ge0e.
  - rewrite /ess_sup /mkset. apply /ereal_infP. move=> y Hyae.
    have Hy: forall x : nat, (abse \o (fun n => (p_sum_int_fun a b n)%:num)) x <= y.
    by apply (@ae_counting R).
    clear Hyae. rewrite num_gee_max. apply/andP. split.
    * move: Hy=> /(_ 0%N) /=. by rewrite gee0_abs // /p_sum_int_fun.
    * move: Hy=> /(_ 1%N) /=. by rewrite gee0_abs // /p_sum_int_fun.
Qed.

Lemma p_sum_integral_correct (p: \bar R) (a b: {nonneg \bar R}):
  0 < p -> (a ⊕[p] b)%:num = p_sum_integral p a b.
Proof.
  move => Hp_gt0.
  have [->|Hp_neqy] := eqVneq p +oo.
  - by rewrite p_sum_y maxe_translation p_sum_integral_y.
  - destruct p as [r| |] => //.
    by rewrite p_sum_fin //= p_sum_integral_fine.
Qed.

Lemma adde_p_sum_bounds (a b: \bar R) (p: R):
  0 < a < +oo -> 0 < b < +oo -> 0 < a `^ p + b `^ p < +oo.
Proof.
  move=> /andP [Ha1 Ha2] /andP [Hb1 Hb2]. apply/andP. split.
  - by apply (@adde_gt0 _ (a `^ p) (b `^ p)); apply poweR_gt0.
  - by apply (@lte_add_pinfty _ (a `^ p) (b `^ p)); apply poweR_lty.
Qed.

Lemma p_sum_bounds (a b: \bar R) (p: R):
  0 < a < +oo -> 0 < b < +oo -> 0 < (a `^ p + b `^ p) `^ p^-1 < +oo.
Proof.
  move=> /andP [Ha1 Ha2] /andP [Hb1 Hb2]. apply/andP. split.
  - by apply poweR_gt0, (@adde_gt0 _ (a `^ p) (b `^ p)); apply poweR_gt0.
  - by apply poweR_lty, (@lte_add_pinfty _ (a `^ p) (b `^ p)); apply poweR_lty.
Qed.

(** p-sum and harmonic p-sum are commutative *)
Lemma p_sumC (p: \bar R):
  (0 < p) -> commutative (fun a b => a ⊕[p] b).
Proof.
  move=> Hp a b. apply/val_inj. simpl.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _].
  - by rewrite !p_sum_y comparable_maxC.
  - clear Hr. have Hr: (0 < r)%R by rewrite -lte_fin -Hr'.
    rewrite Hr' !(p_sum_fin _ _ _ Hr) /=.
    by rewrite [adde _ _]addeC.
Qed.

Lemma harmonic_p_sumC (p : \bar R) :
  p < 0 -> commutative (fun a b => a ⊕[p] b).
Proof.
move=> p0 a b; rewrite p_sum_duality ?lt_eqF//.
by rewrite (p_sumC (- p)) ?oppe_gt0 // -p_sum_duality // lt_eqF.
Qed.

Lemma p_sumA_explicit (a b c: {nonneg \bar R}) (r: R) (Hr: r != 0%R):
  (a%:nngnum `^ r + ((b%:nngnum `^ r + c%:nngnum `^ r) `^ r^-1) `^ r) `^ r^-1 =
    (((a%:nngnum `^ r + b%:nngnum `^ r) `^ r^-1) `^ r + c%:nngnum `^ r) `^ r^-1.
Proof.
by rewrite  -!poweRrM !mulVf// ?poweRe1// ?addeA// adde_ge0//.
Qed.

(** p-sum and harmonic p-sum are associative *)
Lemma p_sumA (p: \bar R):
  (0 < p) -> associative (fun a b => a ⊕[p] b).
Proof.
  move=> Hp a b c. apply/val_inj. simpl.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _];
    first by rewrite !p_sum_y comparable_maxA.
  clear Hr. have Hr: (0 < r)%R by rewrite -lte_fin -Hr'.
  rewrite Hr' !(p_sum_fin _ _ _ Hr)/=. apply p_sumA_explicit.
  move: Hr. rewrite lt0r. by move=> /andP [// _].
Qed.

Lemma harmonic_p_sumA (p : \bar R) :
  p < 0 -> associative (fun a b => a ⊕[p] b).
Proof.
move=> Hp a b c.
rewrite p_sum_duality ?lt_eqF // (p_sum_duality _ b c) ?lt_eqF //.
rewrite invnnge_involutive (p_sum_duality _ a b) ?lt_eqF //.
rewrite p_sumA ?oppe_gt0 // (p_sum_duality _ _ c) ?lt_eqF //.
by rewrite invnnge_involutive.
Qed.

Lemma p_sum_0nng (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num = 0 -> a ⊕[p] b = b.
Proof.
  move=> Hp Ha. apply/val_inj => /=.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - rewrite p_sum_y maxe_translation /maxe Ha.
    destruct (0 < b%:num) eqn:E => //.
    have: 0 <= b%:num by done.
    rewrite le_eqVlt => /orP [/eqP //|Hb]. by rewrite Hb in E.  
  - subst. rewrite p_sum_fin //= Ha poweR0r;
      last by (apply/eqP => Hr; rewrite Hr ltxx in Hp).
    have ->: adde 0%R (b%:num `^ r)  = 0 + b%:num `^ r by done.
    by rewrite add0e -poweRrM divff ?gt_eqF//; first by rewrite poweRe1.
Qed.

Lemma p_sum_nng0 (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> b%:num = 0 -> a ⊕[p] b = a.
Proof.
  move=> Hp. rewrite p_sumC //. by apply p_sum_0nng.
Qed.

Lemma harmonic_p_sum_ynng (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> a%:num = +oo -> a ⊕[p] b = b.
Proof.
  move=> Hp Ha. rewrite p_sum_duality ?lt_eqF//.
  have Hainv: (a `*)%:num = 0 by rewrite -invey /=; f_equal.
  rewrite p_sum_0nng //; last by rewrite oppe_gt0.
  by rewrite invnnge_involutive.
Qed.

Lemma harmonic_p_sum_nngy (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> b%:num = +oo -> a ⊕[p] b = a.
Proof.
  move=> Hp. rewrite harmonic_p_sumC //. by apply harmonic_p_sum_ynng.
Qed.

Lemma p_sum_ynng (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num = +oo -> a ⊕[p] b = +oo%:nng.
Proof.
  move=> Hp Ha. apply/val_inj => /=.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - by rewrite p_sumC // p_sum_y maxe_translation Ha real_maxey.
  - subst. rewrite p_sum_fin //= Ha.
    have ->: adde (+oo `^ r) (b%:num `^ r) = +oo `^ r + b%:num `^ r by done.
    rewrite poweRyr; last by (apply/eqP => H; rewrite H ltxx in Hp).
    rewrite addye; last by (rewrite -ltNye; apply: (@lt_le_trans _ _ 0)).
    rewrite poweRyr //.
    suff: (r^-1%R == 0%R = false) by move => /eqP Hr; apply/eqP.
    by rewrite gt_eqF // invr_gt0.
Qed.

Lemma p_sum_nngy  (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> b%:num = +oo -> a ⊕[p] b = +oo%:nng.
Proof.
  move=> Hp Hb. by rewrite p_sumC // p_sum_ynng.
Qed.

Lemma harmonic_p_sum_0nng (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> a%:num = 0 -> a ⊕[p] b = 0%:E%:nng.
Proof.
  move=> Hp Ha. rewrite p_sum_duality ?lt_eqF//.
  have Hainv: (a `*)%:num = +oo by rewrite -inve0 /=; f_equal.
  rewrite p_sum_ynng //; last by rewrite oppe_gt0.
  apply/val_inj => /=. by rewrite invey.
Qed.

Lemma harmonic_p_sum_nng0 (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> b%:num = 0 -> a ⊕[p] b = 0%:E%:nng.
Proof.
  move=> Hp Hb. rewrite harmonic_p_sumC //.
  by rewrite harmonic_p_sum_0nng.
Qed.

(** Inequalities Concerning p-sums *)
Local Ltac itv_poweR_solve := rewrite in_itv /=; apply/andP; split; first done; rewrite leey.

Lemma p_sum_left_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> (a <= a ⊕[p] b)%O.
Proof.
  move=> Hp. suff: a%:num <= (a ⊕[p] b)%:num by done.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - rewrite p_sum_y maxe_translation num_lee_max.
    apply/orP. by left.
  - rewrite Hr. rewrite Hr in Hp.
    rewrite p_sum_fin //=.
    rewrite <- (@poweRe1 _ a%:num) at 1; try done.
    have ->: a%:nngnum `^ 1 = a%:nngnum `^ (r / r).
      by rewrite -(@divff _ r)// gt_eqF.
    rewrite (@poweRrM _ _ r r^-1).
    apply gt0_ler_poweR.
    * rewrite invr_ge0. by apply ltW in Hp.
    * by itv_poweR_solve.
    * by itv_poweR_solve.
    * rewrite <- adde0 at 1. by rewrite leeD.
Qed.

Lemma p_sum_right_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> (b <= a ⊕[p] b)%O.
Proof.
  move=> Hp. rewrite p_sumC //.
  by apply p_sum_left_semiadditive.
Qed.

Lemma harmonic_p_sum_left_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a ⊕[p] b <= a)%O.
Proof.
  move=> Hp. suff: (a ⊕[p] b)%:num <= a%:num by done.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality //= -lee_pV2; try rewrite /in_mem //=.
  rewrite inveK.
  have ->: a%:num^-1 = (a `*)%:num by done.
  suff: (a `* <= a `* ⊕ [- p] b `*)%O by done.
  apply p_sum_left_semiadditive. by rewrite oppe_gt0.
Qed.

Lemma harmonic_p_sum_right_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a ⊕[p] b <= b)%O.
Proof.
  move=> Hp. rewrite harmonic_p_sumC //.
  by apply harmonic_p_sum_left_semiadditive.
Qed.

Lemma lty_p_sum_lty (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num < +oo -> b%:num < +oo -> (a ⊕[p] b)%:num < +oo.
Proof.
  move=> Hp Ha Hb.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - rewrite p_sum_y maxe_translation num_gte_max.
    apply/andP. by split.
  - subst. rewrite p_sum_fin //=. apply poweR_lty.
    by apply: lte_add_pinfty; apply poweR_lty.
Qed.

Local Ltac itv_solve := rewrite in_itv /=; apply/andP; split; first done; apply (@leey R).

Lemma p_sum_left_monotone (a a' b: {nonneg \bar R}) (p: \bar R):
  0 < p -> (a <= a')%O -> (a ⊕[p] b <= a' ⊕[p] b)%O.
Proof.
  move=> Hp Haa'. rewrite le_nng_eq_e.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _].
  - rewrite !p_sum_y !maxe_translation num_gee_max. apply/andP.
    split; rewrite num_lee_max; apply/orP; last by right.
    by left.
  - rewrite Hr' in Hp. rewrite Hr' !p_sum_fin //=. apply gt0_ler_poweR; try by itv_solve.
    + by rewrite invr_ge0.
    + apply (leeD2r (b%:nngnum `^ r)).
      by apply gt0_ler_poweR; try by itv_solve. 
Qed.

Lemma p_sum_right_monotone (a b b': {nonneg \bar R}) (p: \bar R):
  0 < p -> (b <= b')%O -> (a ⊕[p] b <= a ⊕[p] b')%O.
Proof.
  move=> Hp. rewrite (p_sumC _ _ a b) // (p_sumC _ _ a b') //.
  by apply p_sum_left_monotone.
Qed.

Lemma p_sum_both_monotone (a a' b b': {nonneg \bar R}) (p: \bar R):
  0 < p -> (a <= a')%O -> (b <= b')%O
    -> ((a ⊕[p] b) <= (a' ⊕[p] b'))%O.
Proof.
  move=> Hp Ha Hb.
  eapply le_trans; first by apply (p_sum_left_monotone a a').
  by apply p_sum_right_monotone.
Qed.
  
Lemma harmonic_p_sum_left_monotone (a a' b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a <= a')%O -> (a ⊕[p] b <= a' ⊕[p] b)%O.
Proof.
  move=> Hp Haa'. rewrite le_nng_eq_e.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality // (p_sum_duality _ a' _) //=.
  rewrite lee_pV2; try rewrite /in_mem //=.
  apply p_sum_left_monotone=> /=; first by rewrite oppe_gt0.
  by rewrite le_minvnnge //; rewrite /in_mem //=.
Qed.

Lemma harmonic_p_sum_right_monotone (a b b': {nonneg \bar R}) (p: \bar R):
  p < 0 -> (b <= b')%O -> (a ⊕[p] b <= a ⊕[p] b')%O.
Proof.
  move=> Hp. rewrite (harmonic_p_sumC _ _ a b) //.
  rewrite (harmonic_p_sumC _ _ a b') //.
  by apply harmonic_p_sum_left_monotone.
Qed.

Lemma harmonic_p_sum_both_monotone (a a' b b': {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a <= a')%O -> (b <= b')%O
    -> ((a ⊕[p] b) <= (a' ⊕[p] b'))%O.
Proof.
  move=> Hp Ha Hb.
  eapply le_trans; first by apply (harmonic_p_sum_left_monotone a a').
  by apply harmonic_p_sum_right_monotone.
Qed.

Lemma lty_p_sum_softly_idempotent (a: {nonneg \bar R}) (p: R):
  (0 < p)%R -> ((2 `^ p^-1)%:E%:nng <= a -o a ⊕[p%:E] a)%O.
Proof.
  move=> Hp_gt0.
  move: (nng_0posy a) => [Ha|[Ha|[r Hr Hr']]].
  - rewrite /divnnge p_sum_ynng // comulnngy //. by apply: leey.
  - rewrite /divnnge p_sum_nng0 // comulynng //; first by apply: leey.
    have ->: a = 0%:E%:nng by apply/val_inj.
    by rewrite invnng0.
  - suff: (2 `^ p^-1)%:E <= (a -o a ⊕[p%:E] a)%:num by done.
    rewrite /divnnge /= p_sum_fin //= inveK Hr' /=.
    have ->: (r `^ p + r `^ p = 2 * (r `^ p))%R by ring.
    rewrite powRM //; last by apply powR_ge0.
    rewrite -powRrM mulfV; last by apply lt0r_neq0.
    rewrite powRr1; last by apply ltW. rewrite -invr_non0;
      last by apply lt0r_neq0, mulr_gt0.
    rewrite -EFinM invfM -powRN (mulrC _ r^-1%R) mulrA mulfV;
      last by apply lt0r_neq0.
    rewrite mul1r -invr_non0; last by apply lt0r_neq0, powR_gt0.
    by rewrite -powRN opprK.
Qed.

Lemma lty_harmonic_p_sum_softly_idempotent (a: {nonneg \bar R}) (p: R):
  (p < 0)%R -> ((2 `^ (-p)^-1)%:E%:nng <= a ⊕[p%:E] a -o a)%O.
Proof.
  move=> Hp_lt0.
  rewrite p_sum_duality ?lt_eqF//.
  rewrite /divnnge comulnngeC invnnge_involutive.
  rewrite [X in X ⊗* _] (_ : _ = a `* `*);
    last by rewrite invnnge_involutive.
  apply: (lty_p_sum_softly_idempotent (a `*) (-p)).
  by rewrite oppr_gt0.
Qed.

          
(** ** Interplay Between the Additive and Multiplicative Fragments *)
Lemma p_sum_mulDr (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> c ⊗ (a ⊕[p] b) = (c ⊗ a) ⊕[p] (c ⊗ b).
Proof.
  move=> Hp. apply/val_inj => /=.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _].
  - rewrite !p_sum_y !maxe_translation /=.
    destruct (nng_nngy c) as [Hc|[x Hx Hx']].
    + rewrite Hc /maxe. move: (nng_0pos a) (nng_0pos b) => [->|Ha] [->|Hb].
      * rewrite !mule0.
        by destruct ((0%R: \bar R) < 0%R) eqn:E; rewrite E mule0.
      * rewrite Hb mule0 gt0_mulye //.
        by have ->: 0%R < +oo by done.
      * have ->: a%:num < 0%R = false by apply lt_gtF.
        by rewrite mule0 gt0_mulye.
      * rewrite (@gt0_mulye _ a%:num) // (@gt0_mulye _ b%:num) //.
        by destruct (a%:num < b%:num) eqn:E; rewrite E;
          destruct ((+oo: \bar R) < +oo) eqn:E'; rewrite E' gt0_mulye.
    + rewrite Hx'. by apply: maxe_pMr.
  - subst. rewrite !p_sum_fin //=.
    have ->: c%:num * (a%:num `^ r + b%:num `^ r) `^ r^-1
         = c%:num `^ (r * r^-1) * ((a%:num `^ r + b%:num `^ r)) `^ r^-1.
      by rewrite divrr; [rewrite poweRe1 | apply unitf_gt0].
    by rewrite poweRrM -poweRM ?adde_ge0// ge0_muleDr // !poweRM.
Qed.

Lemma p_sum_mulDl (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> (a ⊕[p] b) ⊗ c = (a ⊗ c) ⊕[p] (b ⊗ c).
Proof.
  rewrite (mulnngeC (a ⊕[p] b)) (mulnngeC a) (mulnngeC b).
  by apply p_sum_mulDr.
Qed.

Corollary harmonic_p_sum_divDr (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> c -o (a ⊕[p] b) = (c -o a) ⊕[p] (c -o b).
Proof.
  move=> Hp_lt0.
  rewrite /divnnge /comulnnge (p_sum_duality _ a b) ?invnnge_involutive ?lt_eqF//.
  rewrite (p_sum_duality _ ((c ⊗ a `*) `*)) ?lt_eqF//.
  by rewrite !invnnge_involutive p_sum_mulDr // oppe_gt0.
Qed.

Lemma harmonic_p_sum_comulDr (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> c ⊗* (a ⊕[p] b) = (c ⊗* a) ⊕[p] (c ⊗* b).
Proof.
  move=> Hp.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality // (p_sum_duality _ (c ⊗* a) _) //.
  rewrite !comulnnge_invnnge -p_sum_mulDr;
    last by rewrite oppe_gt0.
  by rewrite /comulnnge invnnge_involutive.
Qed.

Lemma harmonic_p_sum_comulDl (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a ⊕[p] b) ⊗* c = (a ⊗* c) ⊕[p] (b ⊗* c).
Proof.
  rewrite (comulnngeC (a ⊕[p] b)) (comulnngeC a) (comulnngeC b).
  by apply harmonic_p_sum_comulDr.
Qed.

Corollary p_sum_divDl (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> (a ⊕[p] b) -o c = (a -o c) ⊕[-p] (b -o c).
Proof.
move=> Hp_gt0.
rewrite /divnnge (p_sum_duality _ a b) ?gt_eqF//.
rewrite invnnge_involutive harmonic_p_sum_comulDl //.
by rewrite oppe_lt0.
Qed.

Lemma p_sum_comulDr (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> c ⊗* (a ⊕[p] b) = (c ⊗* a) ⊕[p] (c ⊗* b).
Proof.
  move=> Hp. apply/val_inj => /=.
  move: (nng_0posy c) => [Hc|[Hc|[r Hr Hr']]].
  - rewrite !comulynng // (p_sum_ynng +oo%:nng) //=.
    by rewrite Hc invey mul0e inve0.
  - rewrite Hc inve0.
    move: (nng_0posy a) => [Ha|[Ha|[s Hs Hs']]].
    + rewrite comulnngy // (p_sum_ynng +oo%:nng) //.
      by rewrite (p_sum_ynng a) //= invey mule0 inve0.
    + rewrite (p_sum_0nng a) //.
      move: (nng_0posy b) => [Hb|[Hb|[t Ht Ht']]].
      * rewrite (comulnngy _ b) // p_sum_nngy //= Hb.
        by rewrite invey mule0 inve0.
      * rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Hb | right; rewrite Hc].
        rewrite -p_sum_mulDr // (p_sum_0nng a) //= Hc mul0e.
        by rewrite Hb inve0 gt0_muley.
      * rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Ht' ltry | right; rewrite Hc].
        rewrite -p_sum_mulDr // (p_sum_0nng a) //= Hc mul0e.
        by rewrite gt0_mulye // inve_gt0 ?Ht' // gt_eqF.
    + move: (nng_0posy b) => [Hb|[Hb|[t Ht Ht']]].
      * rewrite (p_sum_nngy a) //= invey mule0 inve0.
        by rewrite (comulnngy _ b) // (p_sum_nngy _ +oo%:nng).
      * rewrite (p_sum_nng0 a) //.
        rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Hs' ltry | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Hb | right; rewrite Hc].
        rewrite -p_sum_mulDr // mul0nng //= gt0_mulye ?invey //.
        by rewrite inve_gt0 Hs' // gt_eqF.
      * rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Hs' ltry | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Ht' ltey | right; rewrite Hc].
        rewrite -p_sum_mulDr // mul0nng //= gt0_mulye ?invey //.
        have Hab: 0%R < (a ⊕ [p] b)%:num.
          eapply lt_le_trans; last by apply: p_sum_left_semiadditive.
          by rewrite /= Hs'.
        rewrite inve_gt0 //; first by rewrite gt_eqF.
        rewrite -ltey. by apply lty_p_sum_lty; rewrite ?Hs' ?Ht' ?ltry.
  - move: (nng_0posy a) => [Ha|[Ha|[s Hs Hs']]].
    + rewrite p_sum_ynng //= invey mule0 inve0.
      by rewrite (comulnngy c a) // (p_sum_ynng +oo%:nng).
    + move: (nng_0posy b) => [Hb|[Hb|[t Ht Ht']]].
      * rewrite p_sum_nngy //= invey mule0 inve0.
        by rewrite (comulnngy c b) // (p_sum_nngy _ +oo%:nng).
      * rewrite (p_sum_nng0 a) //.
        rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hr' ltry].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Hb | right; rewrite Hr' ltry].
        rewrite -p_sum_mulDr // p_sum_0nng // mulnng0 //=.
        rewrite Ha inve0 gt0_muley ?invey // Hr'.
        by rewrite inve_gt0 // gt_eqF.
      * rewrite p_sum_0nng //.
        rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hr' ltry].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Ht' ltry | right; rewrite Hr' ltry].
        rewrite -p_sum_mulDr // p_sum_0nng //= Hr' Ht'.
        by apply fin_gt0_comulnnge_eq_mulnnge.
    + rewrite (neq0y_comulnnge_eq_mulnnge c a);
        last by split; [right; rewrite Hs' ltry | right; rewrite Hr' ltry].
      rewrite (neq0y_comulnnge_eq_mulnnge c b);
        last by split; [left; rewrite Hr' | right; rewrite Hr' ltry].
      rewrite -p_sum_mulDr // -neq0y_comulnnge_eq_mulnnge // Hr'.
      split; first by left.
      right. by rewrite ltry.
Qed.

Lemma p_sum_comulDl (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> (a ⊕[p] b) ⊗* c = (a ⊗* c) ⊕[p] (b ⊗* c).
Proof.
  rewrite (comulnngeC (a ⊕[p] b)) (comulnngeC a) (comulnngeC b).
  by apply p_sum_comulDr.
Qed.

Corollary p_sum_divDr (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> c -o (a ⊕[p] b) = (c -o a) ⊕[p] (c -o b).
Proof.
  move=> Hp_gt0. 
  by rewrite /divnnge p_sum_comulDr.
Qed.

Lemma harmonic_p_sum_mulDr (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> c ⊗ (a ⊕[p] b) = (c ⊗ a) ⊕[p] (c ⊗ b).
Proof.
  move=> Hp. rewrite p_sum_duality ?lt_eqF//.
  rewrite (p_sum_duality _ (c ⊗ a)) ?lt_eqF//.
  rewrite -(invnnge_involutive c).
  have ->: ((c `*) `* ⊗ a) = ((c `*) `* ⊗ (a `*) `*)
    by rewrite (invnnge_involutive a).
  have ->: ((c `*) `* ⊗ b) = ((c `*) `* ⊗ (b `*) `*)
    by rewrite (invnnge_involutive b).
  rewrite -!comulnnge_invnnge.
  rewrite p_sum_comulDr ?oppe_gt0 //.
  by rewrite !invnnge_involutive.
Qed.

Lemma harmonic_p_sum_mulDl (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a ⊕[p] b) ⊗ c = (a ⊗ c) ⊕[p] (b ⊗ c).
Proof.
  rewrite (mulnngeC (a ⊕[p] b)) (mulnngeC a) (mulnngeC b).
  by apply harmonic_p_sum_mulDr.
Qed.

Corollary harmonic_p_sum_divDl (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a ⊕[p] b) -o c = (a -o c) ⊕[-p] (b -o c).
Proof.
  move=> Hp_lt0.
  rewrite /divnnge /comulnnge !invnnge_involutive harmonic_p_sum_mulDl //.
  by rewrite p_sum_duality ?invnnge_involutive ?lt_eqF.
Qed.

Lemma mul_p_sum_le_max_mul_fin_gt0 (a b c d: R) (p: R):
  (0 < p -> 0 < a -> 0 < b -> 0 < c -> 0 < d
   -> (a `^ p + b `^ p) `^ p^-1 * ((c^-1 `^ p + d^-1 `^ p) `^ p^-1)^-1
      <= Num.max (a * c) (b * d))%R.
Proof.
  wlog: a b c d / (b * d <= a * c)%R.
  - move=> Hwlog Hp_gt0 Ha_gt0 Hb_gt0 Hc_gt0 Hd_gt0.
    have /orP [Hac_lebd|Hbd_leac] := le_total (a * c)%R (b * d)%R;
      last by apply Hwlog.
    rewrite (addrC (a `^ _)%R) (addrC (c^-1 `^ _)%R) maxC.
    by apply Hwlog.
  - move=> Hbd_leac Hp_gt0 Ha_gt0 Hb_gt0 Hc_gt0 Hd_gt0.
    rewrite max_l //.
    have Hbd_leac' : ((b * d) `^ p <= (a * c) `^ p)%R.
      by apply: ge0_ler_powR; rewrite // ?ltW // nnegrE mulr_ge0 // ltW.
    rewrite !powRM in Hbd_leac'; try by apply ltW.
    have Hdp_inv: (0 <= (d `^ p)^-1)%R by rewrite invr_ge0 powR_ge0.
    have Hdp_muldp: (0 <= b `^ p * d `^ p)%R by rewrite mulr_ge0 // powR_ge0.
    apply (ler_pM Hdp_inv Hdp_muldp (lexx ((d `^ p)^-1)%R)) in Hbd_leac'.
    rewrite (mulrC _ ((b `^ p) * _)%R) (mulrC _ ((a `^ p) * _)%R) in Hbd_leac'.
    rewrite -mulrA mulfV ?mulr1 in Hbd_leac';
      last by rewrite lt0r_neq0 // powR_gt0.
    apply (lerD (lexx (a `^ p)%R)) in Hbd_leac'.
    rewrite [X in (_ <= X + _)%R] (_ : _ = (a `^ p * 1)%R) in Hbd_leac';
      last by rewrite mulr1.
    rewrite -(@divff _ (c `^ p)%R) in Hbd_leac';
      last by rewrite lt0r_neq0 // powR_gt0 //.
    rewrite mulrA -mulrDr in Hbd_leac'.
    have H_cpinv_dpinv_inv: (0 <= ((c `^ p)^-1 + (d `^ p)^-1)^-1)%R.
      by rewrite invr_ge0 addr_ge0 // invr_ge0 powR_ge0.
    have Hap_bp: (0 <= a `^ p + b `^ p)%R.
      by rewrite addr_ge0 // powR_ge0.
    apply (ler_pM H_cpinv_dpinv_inv Hap_bp
             (lexx ((c `^ p)^-1 + (d `^ p)^-1)^-1%R)) in Hbd_leac'.
    rewrite (mulrC _ (_ * _)%R) -mulrA divff in Hbd_leac';
      last by rewrite lt0r_neq0 // addr_gt0 // invr_gt0 powR_gt0 //. 
    rewrite mulr1 (mulrC _ (_ + _)%R) -powRM in Hbd_leac';
      try by apply ltW.
    rewrite -powRN -mulrN1 (mulrC _ (-1)%R) powRrM powR_inv1;
      last by rewrite addr_ge0 // powR_ge0.
    rewrite -powRM ?invr_ge0 ?addr_ge0 // ?powR_ge0 //.
    rewrite -(@powR_inv1 _ c _); last by apply ltW.
    rewrite -(@powR_inv1 _ d _); last by apply ltW.
    rewrite -!powRrM !(mulrC (-1)%R) !mulrN1 !powRN.
    rewrite -(@powRr1 _ (a * c)%R); last by rewrite mulr_ge0 // ltW.
    rewrite -(@divff _ p) ?powRrM; last by apply lt0r_neq0.
    rewrite (@ge0_ler_powR _ p^-1%R) //= ?nnegrE.
    + by rewrite invr_ge0 // ltW.
    + by rewrite mulr_ge0 // ?invr_ge0 ?addr_ge0 // ?invr_ge0 powR_ge0.
    + by rewrite powR_ge0.
Qed.

Lemma prod_max_min_le_max_prod (a b c d: \bar R):
  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d
    -> maxe a b * mine c d <= maxe (a * c) (b * d).
Proof.
  move=> Ha_ge0 Hb_ge0 Hc_ge0 Hd_ge0.
  have /orP [Ha_leb|Hb_lea] := le_total a b.
  - rewrite max_r //.
    have /orP [Hc_led|Hd_lec] := le_total c d.
    + rewrite min_l // le_max. apply/orP. right.
      by apply: lee_pmul.
    + rewrite min_r // le_max. apply/orP. by right.
  - rewrite max_l //.
    have /orP [Hc_led|Hd_lec] := le_total c d.
    + rewrite min_l // le_max. apply/orP. by left.
    + rewrite min_r // le_max. apply/orP. left.
      by apply: lee_pmul.
Qed.

Lemma mul_p_sum_le_max_mul (a b c d: {nonneg \bar R}) (p: \bar R):
  0 < p -> ((a ⊕[p] b) ⊗ (c ⊕[-p] d) <= maxe (a ⊗ c) (b ⊗ d))%O.
Proof.
  move=> Hp_gt0. rewrite !le_nng_eq_e.
  suff: ((a ⊕[p] b) ⊗ (c ⊕[-p] d))%:num <= (maxe (a ⊗ c) (b ⊗ d))%:num by done.
  rewrite maxe_translation.
  move: (nng_0posy c) => [Hc_eqy|[Hc_eq0|[s [Hs_gt0 Hs_eqc]]]].
  - move: (nng_0pos a) => [Ha_eq0|Ha_gt0];
       rewrite num_lee_max.
    + rewrite (@p_sum_0nng _ _ p) // (@harmonic_p_sum_ynng _ _ (-p)) ?oppe_lt0 //.
      apply/orP. by right.
    + apply/orP. left.
      rewrite (gt0_mulnngy _ c) //=. by apply: leey.
  - rewrite (@harmonic_p_sum_0nng _ _ (-p)) // ?oppe_lt0 //.
    rewrite mulnng0 //=.
    by have ->: 0%:E = 0%R by done.
  - move: (nng_0posy a) => [Ha_eqy|[Ha_eq0|[t [Ht_gt0 Ht_eqa]]]].
    + rewrite num_lee_max.
      apply/orP. left.
      rewrite (gt0_mulynng a) ?Hs_eqc //=. by apply: leey.
    + rewrite (@p_sum_0nng _ _ p) // num_lee_max.
      apply/orP. right. apply mulnnge_right_monotone.
      apply harmonic_p_sum_right_semiadditive.
      by rewrite oppe_lt0.
    + move: (nng_0posy d) => [Hd_eqy|[Hd_eq0|[u [Hu_gt0 Hu_eqd]]]].
      * rewrite (@harmonic_p_sum_nngy _ _ (-p)) ?oppe_lt0 //.
        move: (nng_0pos b) => [Hb_eq0|Hb_gt0];
          rewrite num_lee_max.
        -- rewrite (@p_sum_nng0 _ _ p) //.
           apply/orP. by left.
        -- apply/orP. right.
           rewrite (gt0_mulnngy b) //=. by apply: leey.
      * rewrite (@harmonic_p_sum_nng0 _ _ (-p)) ?oppe_lt0 //.
        rewrite (@mulnng0 (_ ⊕[_] _)) //=.
        by have ->: 0%:E = 0%R by done.
      * move: (nng_0posy b) => [Hb_eqy|[Hb_eq0|[v [Hv_gt0 Hv_eqb]]]].
        -- rewrite num_lee_max. apply/orP. right.
           rewrite (gt0_mulynng b) //= ?Hu_eqd //. by apply: leey.
        -- rewrite (@p_sum_nng0 _ _ p) // num_lee_max.
           apply/orP. left. apply mulnnge_right_monotone.
           apply harmonic_p_sum_left_semiadditive.
           by rewrite oppe_lt0.
        -- rewrite !/mulnnge /=.
           destruct p as [q| |] => //=; subst;
             last by rewrite p_sum_y harmonic_p_sum_Ny
                   maxe_translation mine_translation prod_max_min_le_max_prod.
           rewrite p_sum_fin //= harmonic_p_sum_fin ?oppr_lt0 // opprK /=.
           rewrite Hs_eqc Ht_eqa Hu_eqd Hv_eqb /=.
           rewrite -!invr_non0 ?lt0r_neq0 //;
             last by rewrite powR_gt0 // addr_gt0 // powR_gt0 // invr_gt0.
           rewrite -!EFinM.
           have ->: maxe (t * s)%:E (v * u)%:E = (Num.max (t * s)%R (v * u)%R)%:E.
             by move: (le_total (t * s)%R (v * u)%R) => /orP [H|H];
             [rewrite !max_r | rewrite !max_l].
           by apply mul_p_sum_le_max_mul_fin_gt0.
Qed.

Lemma mul_p_sum_mix_le_max_mul (a b c d: {nonneg \bar R}) (p: \bar R):
  p != 0 -> ((a ⊕[p] b) ⊗ (c ⊕[-p] d) <= maxe (a ⊗ c) (b ⊗ d))%O.
Proof.
  move=> Hp_neq0.
  have /orP [Hp_gt0|Hp_gt0] := lt_total Hp_neq0;
    last by apply mul_p_sum_le_max_mul.
  rewrite (mulnngeC (a ⊕[p] b)) (mulnngeC a) (mulnngeC b).
  have ->: a ⊕ [p] b = a ⊕ [--p] b by rewrite oppeK.
  apply mul_p_sum_le_max_mul. by rewrite oppe_gt0.
Qed.

End results.