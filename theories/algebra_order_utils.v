From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets functions mathcomp_extra.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology tvs normedtype landau sequences derive.
From mathcomp Require Import realfun interval_inference convex interval exp lebesgue_integral.
From mathcomp Require Import hoelder counting_measure cardinality measure all_algebra.
From mathcomp Require Import ess_sup_inf finmap.

From HQLL Require Import interval_einference.

Import Order.TTheory GRing.Theory Num.Theory.

Section properties.

Context {R: realType}.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.

Lemma Lnorm_generalised_counting (p : R) (f: (\bar R)^nat):
  (p != 0%R) -> 'N[counting]_p%:E [f] = (\sum_(k <oo) (`| f k | `^ p)) `^ p^-1.
Proof.
  by move=> p0; rewrite unlock ge0_integral_count// => k; rewrite poweR_ge0.
Qed.

(** Case analysis lemmas *)
Lemma nng_in_itv (a : \bar R) :
  Itv.spec ext_num_sem (Itv.Real `[0%Z, +oo[) a -> 0 <= a.
Proof.
  rewrite /ext_num_sem /Itv.spec. move=> /andP. rewrite in_itv /=.
  by move=> [_ /andP [Ha _]].
Qed.

Lemma nng_nngy (a : {nonneg \bar R}):
  a%:num = +oo \/ exists2 r, r%:E >= 0 & a%:num = r%:E.
Proof.
  destruct a as [a Ha].
  have Hnng /=: 0 <= a by apply nng_in_itv.
  move: (gee0P a)=> [/(_ Hnng) [->|Hr] _]; first by left.
  by right.
Qed.

Lemma nng_0posy (a : {nonneg \bar R}):
  a%:num = +oo \/ a%:num = 0 \/ exists2 r, r%:E > 0 & a%:num = r%:E.
Proof.
  move: (nng_nngy a)=> [->|[r Hrnng ->]]; first by left.
  rewrite le_eqVlt in Hrnng.
  move: Hrnng => /orP [/eqP <-|Hr].
  - right. by left.
  - right. right. by exists r.
Qed.

Lemma nng_0posy' (a : {nonneg \bar R}):
  a = +oo%:nng \/ a = 0%:E%:nng \/ 0 < a%:num < +oo.
Proof.
  move: (nng_0posy a) => /= [Hy|[H0|[r Hr ->]]].
  - left. by apply/val_inj.
  - right. left. by apply/val_inj.
  - right. right. apply/andP. split; first done.
    apply (ltry r).
Qed.

Lemma gt0_nng_posy {a : {nonneg \bar R}}:
  0 < a%:num -> a%:num = +oo \/ exists2 r, r%:E > 0 & a%:num = r%:E.
Proof.
  move=> Ha. destruct (nng_0posy a) as [->|[Ha'|[r Hr Hr']]]; subst.
  - by left.
  - rewrite Ha' in Ha. by rewrite ltxx in Ha.
  - right. exists r => //.
Qed.

Lemma lty_nng_0pos {a : {nonneg \bar R}}:
  a%:num < +oo -> a%:num = 0 \/ exists2 r, r%:E > 0 & a%:num = r%:E.
Proof.
  move=> Ha. destruct (nng_0posy a) as [Ha'|[->|[r Hr Hr']]]; subst.
  - rewrite Ha' in Ha. by rewrite ltxx in Ha.
  - by left.
  - right. exists r => //.
Qed.

Lemma nng_0pos (a : {nonneg \bar R}) : a%:num = 0 \/ a%:num > 0.
Proof.
have : 0 <= a%:num by [].
by rewrite le_eqVlt => /orP[/eqP->|]; [left|right].
Qed.

Lemma pos_implies_fin_num (r : R) : 0 < r%:E -> r%:E^-1 \is a fin_num.
Proof. by move=> r0; rewrite fin_numV// gt_eqF. Qed.

Lemma pos_implies_nng (r : R) : 0%R < r%:E -> (0 <= r)%R.
Proof. by rewrite lte_fin => /ltW. Qed.

Lemma lee0P (p: \bar R) : p <= 0 <-> p = -oo \/ exists2 r, (r <= 0)%R & p = r%:E.
Proof.
  split.
  - move=> Hp. rewrite -(oppeK p) oppe_le0 in Hp.
    move: (gee0P (-p)) => [/(_ Hp) [-Hp'|[r Hr Hr']] _].
    * left. by have -> /=: p = -(+oo) by rewrite -(oppeK p); f_equal.
    * right. exists (-r)%R; first by rewrite oppr_lte0.
      rewrite -(oppeK p). by rewrite Hr'.
  - by move=> [->|[r Hr ->]].
Qed.

Lemma posP (p: \bar R): 0 < p < +oo -> exists2 r, (0 < r)%R & p = r%:E.
Proof.
  move=> /andP [Hp0 Hpy]. move: (gee0P p) => [/(_ (ltW Hp0)) [Hpy'|[r Hr Hr']] _].
  - move: Hpy' Hpy. by rewrite ltey => ->.
  - exists r => //. by rewrite -lte_fin -Hr'.
Qed.

Lemma nonneg_not_Ny (a : {nonneg \bar R}) : a%:num != -oo.
Proof. by rewrite -ltNye (@lt_le_trans _ _ 0). Qed.

Lemma nonneg_not_0 (p q : R): (q <= p)%R -> (0 < q)%R -> p != 0%R.
Proof. by move=> qp q0; rewrite gt_eqF// (lt_le_trans _ qp). Qed.

Lemma invr_non0 (r : R) : r != 0%R -> r^-1%:E = r%:E^-1.
Proof. by move=> /negbTE r0; rewrite inver// r0. Qed.

Lemma mule_lty_gt0 (a b : \bar R):
  0 < a -> 0 < b -> a * b < +oo -> (a < +oo) && (b < +oo).
Proof.
  move=> Ha Hb Hab. destruct a as [s| | ]; last done.
  - destruct b as [t| | ]; last done.
    + apply/andP. split; apply (@ltry R).
    + move: (gt0_mulye Ha) Hab. rewrite muleC.
      move=> ->. by rewrite ltxx.
  - move: (gt0_mulye Hb) Hab=> ->. by rewrite ltxx.
Qed.

Lemma nngNy_fin_num (a : \bar R) : 0 <= a -> a < +oo -> a \is a fin_num.
Proof. by move=> a0 ay; rewrite fin_real// ay andbT (lt_le_trans _ a0). Qed.

Lemma fin_inveM_def_by_ineq (a b: \bar R):
  0%R < a -> 0%R < b -> a < +oo -> b < +oo -> (inveM_def (R:=R) a b).
Proof.
  rewrite !lt0e. move=> /andP [Ha Ha'] /andP [Hb Hb'] Ha'' Hb''.
  apply fin_inveM_def; try done.
  - apply fin_real. apply/andP. split; last done.
    apply (@lt_le_trans _ _ 0%R%:E -oo a); last done.
    by rewrite ltNye.
  - apply fin_real. apply/andP. split; last done.
    apply (@lt_le_trans _ _ 0%R%:E -oo b); last done.
    by rewrite ltNye.
Qed.

Lemma le_nng_eq_e (a b : {nonneg \bar R}) : (a <= b)%O = (a%:num <= b%:num).
Proof. by []. Qed.

Lemma lt_nng_eq_e (a b : {nonneg \bar R}) : (a < b)%O = (a%:num < b%:num).
Proof. by []. Qed.

(** The only null set wrt the counting measure is the empty set *)
Lemma counting_zero {X : choiceType} (S: set X) :
  @counting _ R S = 0 -> S = set0.
Proof.
  rewrite /counting.
  destruct (`[< finite_set S >]) eqn:E => //.
  move /eqP. rewrite eqe pnatr_eq0 size_eq0.
  move=> HS. apply fset_set_set0.
  - by apply /asboolP.
  - by apply /eqP.
Qed.

(** A property holding ae wrt the counting measure holds universally *)
Lemma ae_counting  (P: nat -> bool):
  (\forall x \ae (@counting _ R), P x) <-> forall x, P x.
Proof.
  split.
  - move=> [S [_ HS HSP]] x. move: HSP.
    have ->: S = set0 by apply counting_zero.
    clear HS. move=> Hemp.
    apply subsetCl in Hemp. rewrite setC0 in Hemp.
    by apply Hemp.
  - move=> HP. exists set0. split; try done.
    apply subsetCl. rewrite setC0. move=> n _. by apply HP.
Qed.

Lemma counting_nat: 0%R < @counting _ R [set: nat].
Proof.
  rewrite /counting.
  by have /asboolF -> //: ~finite_set [set: nat] by apply infinite_nat.
Qed.

Lemma ess_sup_bin_fun  (f: nat -> {nonneg \bar R}):
  (forall n, (2 <= n)%N -> f n = 0%:E%:nng) -> (forall n, 0 <= (f n)%:num)
  -> ess_sup counting (fun n => (f n)%:num) = maxe (f 0%N)%:num (f 1%N)%:num.
Proof.
  move=> Hfinsupp Hnng.  apply le_anti. apply /andP. split.
  - apply /ess_supP. exists set0. split; try done.
    apply subsetCl. rewrite setC0.
    move=> [|[|k]] _ /=; rewrite num_lee_max; apply /orP.
    * by left.
    * by right.
    * left. by rewrite Hfinsupp.
  - rewrite /ess_sup /mkset. apply /ereal_infP. move=> y Hyae.
    have Hy: forall x : nat, (f x)%:num <= y by apply ae_counting.
    clear Hyae. rewrite num_gee_max. apply/andP. split.
    * by move: Hy=> /(_ 0%N) /=.
    * by move: Hy=> /(_ 1%N) /=.
Qed.

Lemma maxe_translation (a b: {nonneg \bar R}):
  (maxe a b)%:num = maxe a%:num b%:num.
Proof.
  have Heq: (a < b)%O = (a%:num < b%:num) by done.
  by destruct (a%:num < b%:num) eqn:E; rewrite !/maxe E Heq.
Qed.

Lemma mine_translation (a b: {nonneg \bar R}):
  (mine a b)%:num = mine a%:num b%:num.
Proof.
  have Heq: (a < b)%O = (a%:num < b%:num) by done.
  by destruct (a%:num < b%:num) eqn:E; rewrite !/mine E Heq.
Qed.

Lemma invp_add_le1 (a b: R):
  (0 < a)%R -> (0 < b)%R -> ((a + b)^-1 * a <= 1)%R.
Proof.
  move=> Ha Hb.
  have: (0 < a + b)%R by apply addr_gt0.
  rewrite lt0r=> /andP [Hab _].
  rewrite -(@mulVf _ (a + b)%R) //. apply ltW in Ha, Hb.
  apply ler_pM => //; last by rewrite lerDl.
  by rewrite invr_ge0 addr_ge0.
Qed.

(** Power function for real exponent greater equal 1 is subadditive
    Should be added to exp.v *)
(* Lemma ge1_poweR_subadditive (a b: {nonneg \bar R}) (p: R):
  (1 <= p)%R -> a%:num `^ p + b%:num `^ p <= (a%:num + b%:num) `^ p.
Proof.
  intros Hp.
  move: (nng_0posy a) => [->|[->|[r Hr Hr']]].
  - rewrite addye; last by apply nonneg_not_Ny.
    rewrite poweRyr; last by apply (nonneg_not_0 _ 1 Hp).
    by rewrite addye; last by apply nonneg_not_Ny.
  - rewrite poweR0r; last by apply (nonneg_not_0 _ 1 Hp).
    by rewrite !add0e.
  - move: (nng_0posy b) => [->|[->|[s Hs Hs']]].
    * rewrite addey; last by rewrite Hr' -ltNye ltNyr.
      rewrite poweRyr; last by apply (nonneg_not_0 _ 1 Hp).
      by rewrite addey; last by rewrite Hr' -ltNye ltNyr.
    * rewrite adde0 poweR0r; last by apply (nonneg_not_0 _ 1 Hp).
      by rewrite adde0.
    * have Hrsnon0: (a%:num + b%:num) `^ p != 0.
        by rewrite Hr' Hs'; apply pos_implies_non0e, poweR_gt0, adde_gt0.
      have Hrsinvfin: ((adde a%:num b%:num) `^ p)^-1 \is a fin_num.
        by apply (@fin_numV _ ((adde a%:num b%:num) `^ p));
          first done; apply nonneg_not_Ny.
      have  Hrsinvgt0: 0 < ((adde a%:num b%:num) `^ p)^-1.
        by rewrite inve_gt0 // Hr' Hs';
          first by apply poweR_gt0, (@adde_gt0 _ r%:E s%:E).
      rewrite -(@lee_pmul2l _ (((a%:num + b%:num) `^ p)^-1)) //.
      rewrite mulVe //; last by apply fin_num_poweR; rewrite fin_numD Hr' Hs'.
      rewrite muleDr //; last by rewrite Hr'; apply fin_num_adde_defr.
      rewrite Hs' Hr' -(@fineK _ (r%:E + s%:E)) //=.
      rewrite inver /=. rewrite Hs' Hr' /= in Hrsnon0.
      have Hrs': ((r + s) `^ p)%R == 0%R = false.
        by apply/eqP; move=> H; move: H Hrsnon0 => -> /eqP H; apply H.
      rewrite Hrs' -EFinM -EFinD -powRN -mulN1r powRrM powRN.
      rewrite !powRr1; last by apply ltW, addr_gt0.
      rewrite Hs' Hr' inver Hrs' in Hrsinvgt0.
      have Hrsinvgt0': (0%R < ((r + s)^-1))%R.
        by rewrite invr_gt0 addr_gt0 //; apply ltW.
      rewrite -!powRM //; try by apply ltW.
      have ->: 1%R = ((r + s)^-1 * r + (r + s)^-1 * s)%R.
      rewrite -mulrDr mulVf //; first by apply/eqP => Hfls; move: Hrsinvgt0';
        rewrite Hfls invr0 ltxx.
      apply lee_tofin, lerD; apply ge1r_powR => //;
        apply/andP; split; try by apply mulr_gt0.
      + by rewrite invp_add_le1.
      + by rewrite addrC invp_add_le1.
Qed.

Local Ltac gt0_pred_solve := rewrite inE; apply/andP;  split; first rewrite unitf_gt0 //; by apply powR_gt0.

(* TODO: This lemma should be added to exp.v *)
Lemma lt0_ler_powR (r: R) : (r <= 0)%R ->
  {in Num.pos &, {homo ((@powR R) ^~ r) : x y / (x <= y)%R >-> (y <= x)%R}}.
Proof.
  move=> r0 x y. rewrite !posrE. move=> Hx Hy Hxy.
  destruct (r == 0%R) eqn:E.
  + have ->: r = 0%R by apply/eqP. by rewrite !powRr0.
  + have E': r != 0%R by apply /eqP; move: E => /eqP.
    have ->: r = (--r)%R by rewrite opprK.
    have Hoppr: (0 <= -r)%R by rewrite oppr_ge0.
    rewrite (powRN y) (powRN x). rewrite ler_pV2 //; try by gt0_pred_solve.
    rewrite ge0_ler_powR //; by rewrite nnegrE; apply pos_implies_nng.
Qed. *)

Lemma poweR_gt0_lty (a: \bar R) (p: R):
  0 < a < +oo -> 0 < a `^ p < +oo.
Proof.
  move=> /andP [Ha0 Hay]. apply/andP. split; first by apply poweR_gt0.
  by apply poweR_lty.
Qed.

(* Lemma lt0r_ler_poweR (r: R) (a b: \bar R): (r <= 0)%R ->
  0 < a < +oo -> 0 < b < +oo -> (a <= b) -> (b `^ r <= a `^ r).
Proof.
  move=> Hr Ha Hb Hba.
  move: (posP _ Ha) (posP _ Hb) => [s Hs Hs'] [t Ht Ht'].
  rewrite Hs' Ht' !poweR_EFin lee_fin lt0_ler_powR //.
  by rewrite -lee_fin -Ht' -Hs'.
Qed. *)

End properties.
