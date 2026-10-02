(**md**************************************************************************)
(* # Interval inference for extended real operations                          *)
(*                                                                            *)
(* This file complements the interval-inference automation of MathComp's      *)
(* interval_inference.v and of the [ext_num_sem] instances of                 *)
(* constructive_ereal.v with canonical instances for the extended real        *)
(* operations that are not covered upstream.  Once these instances are        *)
(* available, goals such as [0 <= x^-1], [0 < x `^ p] or [0 <= expeR x] are   *)
(* discharged by the [ge0e]/[gt0e]/... hints of constructive_ereal.v as soon  *)
(* as an enclosing interval of [x] is known, and casts such as [x^-1 %:nng]   *)
(* are inferred.                                                              *)
(*                                                                            *)
(* ## interval transformers                                                   *)
(*                                                                            *)
(* They live in module [ExtIntItv], mirroring MathComp's [IntItv].            *)
(* ```                                                                        *)
(* keep_neg_strict_bound b == upper bound of [x^-1] out of an upper bound     *)
(*                            [b] of [x].  Unlike [IntItv.keep_neg_bound],    *)
(*                            only *strictly* negative bounds are kept, since *)
(*                            [0^-1 = +oo] in \bar R                          *)
(*      keep_pos_bound0 b == like [IntItv.keep_pos_bound], but for operations *)
(*                           that are non-negative everywhere: an unknown      *)
(*                           sign is turned into [BLeft 0] instead of [-oo]   *)
(*        keep_fin_bound b == lower bound of an operation that is non-negative *)
(*                            everywhere and positive on []-oo, +oo]]         *)
(*        keep_ge1_bound b == lower bound of an operation mapping [1 <= x] to *)
(*                            [0 <= _] and [1 < x] to [0 < _] (e.g. [lne])    *)
(*        keep_le1_bound b == upper bound of an operation mapping [x <= 1] to *)
(*                            [_ <= 0] and [x < 1] to [_ < 0] (e.g. [lne])    *)
(*                inve i == interval of [x^-1] when [x] is in [i]             *)
(*                expe i == interval of [x ^+ n] when [x] is in [i]           *)
(*                 lne i == interval of [lne x] when [x] is in [i]            *)
(*              poweR i == interval of [x `^ p] when [x] is in [i]            *)
(*              expeR i == interval of [expeR x] when [x] is in [i]           *)
(* ```                                                                        *)
(*                                                                            *)
(* ## bound transfer lemmas                                                   *)
(*                                                                            *)
(* The [ext_num_itv_bound_*] lemmas are the extended real counterparts of     *)
(* [num_itv_bound_keep_pos] and [num_itv_bound_keep_neg] of                   *)
(* interval_inference.v: they turn a homomorphism property of an operation    *)
(* into the corresponding bound inequality, so that each canonical instance   *)
(* below is a three-line proof.                                               *)
(*                                                                            *)
(* ## canonical instances                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*    inve_inum == instance for [x^-1]      (realDomainType)                  *)
(*    expe_inum == instance for [x ^+ n]    (realDomainType)                  *)
(*   poweR_inum == instance for [x `^ p]    (realType)                        *)
(*   expeR_inum == instance for [expeR x]   (realType)                        *)
(*     lne_inum == instance for [lne x]     (realType)                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import order interval ssralg.
From mathcomp Require Import orderedzmod numdomain numfield ssrint.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval interval_inference reals rat.
From mathcomp Require Import boolp classical_sets functions mathcomp_extra.
From mathcomp Require Import constructive_ereal exp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.

(** * Interval Inference for extended real operations *)
Module ExtIntItv.
Import IntItv.

(** Upper bound of [x^-1] knowing an upper bound of [x].  In [\bar R] we have
    [0^-1 = +oo], so a non-strict upper bound [x <= 0] carries no information:
    only strictly negative upper bounds are kept. *)
Definition keep_neg_strict_bound (b : itv_bound int) :=
  match b with
  | BSide true 0%Z => BLeft 0%Z
  | BSide _ (Negz _) => BLeft 0%Z
  | _ => +oo%O
  end.
Arguments keep_neg_strict_bound /.

(** Like [IntItv.keep_pos_bound], for operations that are non-negative
    everywhere: no information on the argument still yields [0 <= _]. *)
Definition keep_pos_bound0 (b : itv_bound int) :=
  match b with
  | BSide s 0%Z => BSide s 0%Z
  | BSide _ (Posz _) => BRight 0%Z
  | _ => BLeft 0%Z
  end.
Arguments keep_pos_bound0 /.

(** Lower bound of an operation that is non-negative everywhere and positive
    on []-oo, +oo]] (e.g. [expeR]): any finite bound rules out [-oo]. *)
Definition keep_fin_bound (b : itv_bound int) :=
  if b is BInfty _ then BLeft 0%Z else BRight 0%Z.
Arguments keep_fin_bound /.

(** Lower bound of an operation sending [1 <= x] to [0 <= _] and [1 < x] to
    [0 < _] (e.g. [lne]). *)
Definition keep_ge1_bound (b : itv_bound int) :=
  match b with
  | BSide _ 0%Z => -oo%O
  | BSide s 1%Z => BSide s 0%Z
  | BSide _ (Posz _) => BRight 0%Z
  | _ => -oo%O
  end.
Arguments keep_ge1_bound /.

(** Upper bound of an operation sending [x <= 1] to [_ <= 0] and [x < 1] to
    [_ < 0] (e.g. [lne]). *)
Definition keep_le1_bound (b : itv_bound int) :=
  match b with
  | BSide _ 0%Z => BRight 0%Z
  | BSide s 1%Z => BSide s 0%Z
  | BSide _ (Negz _) => BRight 0%Z
  | _ => +oo%O
  end.
Arguments keep_le1_bound /.

Definition inve i :=
  let: Interval l u := i in
  Interval (keep_nonneg_bound l) (keep_neg_strict_bound u).
Arguments inve /.

Definition expe i := let: Interval l _ := i in Interval (keep_pos_bound l) +oo%O.
Arguments expe /.

Definition lne i :=
  let: Interval l u := i in
  Interval (keep_ge1_bound l) (keep_le1_bound u).
Arguments lne /.

Definition poweR (i : Itv.t) :=
  match i with
  | Itv.Top => Itv.Real `[0%Z, +oo[
  | Itv.Real (Interval l _) => Itv.Real (Interval (keep_pos_bound0 l) +oo%O)
  end.
Arguments poweR /.

Definition expeR (i : Itv.t) :=
  match i with
  | Itv.Top => Itv.Real `[0%Z, +oo[
  | Itv.Real (Interval l _) => Itv.Real (Interval (keep_fin_bound l) +oo%O)
  end.
Arguments expeR /.

End ExtIntItv.

(** * Bound transfer lemmas *)

(** Extended real counterparts of [num_itv_bound_keep_pos] and
    [num_itv_bound_keep_neg] of interval_inference.v. *)
Section ExtNumItvBound.
Context {R : numDomainType}.
Local Notation ext_num_itv_bound :=
  (@map_itv_bound _ (\bar R) (EFin \o intr)).

Lemma ext_num_itv_bound_keep_nonneg (op : \bar R -> \bar R) (x : \bar R) b :
  {homo op : x / (0 <= x)%E} ->
  (ext_num_itv_bound b <= BLeft x)%O ->
  (ext_num_itv_bound (IntItv.keep_nonneg_bound b) <= BLeft (op x))%O.
Proof.
case: b => [[] [n | n] | []] //= hge; rewrite !bnd_simp.
all: rewrite mulr0z => lex; apply: hge.
- by apply: le_trans lex; rewrite lee_fin ler0z.
- by apply/ltW/(le_lt_trans _ lex); rewrite lee_fin ler0z.
Qed.

Lemma ext_num_itv_bound_keep_pos (op : \bar R -> \bar R) (x : \bar R) b :
  {homo op : x / (0 <= x)%E} -> {homo op : x / (0 < x)%E} ->
  (ext_num_itv_bound b <= BLeft x)%O ->
  (ext_num_itv_bound (IntItv.keep_pos_bound b) <= BLeft (op x))%O.
Proof.
case: b => [[] [[| n] | n] | []] //= hge hgt; rewrite !bnd_simp !mulr0z.
- exact: hge.
- by move=> lex; apply: hgt; apply: lt_le_trans lex; rewrite lte_fin ltr0z.
- exact: hgt.
- by move=> ltx; apply: hgt; apply: le_lt_trans ltx; rewrite lee_fin ler0z.
Qed.

Lemma ext_num_itv_bound_keep_pos0 (op : \bar R -> \bar R) (x : \bar R) b :
  (forall y, (0 <= op y)%E) -> {homo op : x / (0 < x)%E} ->
  (ext_num_itv_bound b <= BLeft x)%O ->
  (ext_num_itv_bound (ExtIntItv.keep_pos_bound0 b) <= BLeft (op x))%O.
Proof.
case: b => [[] [[| n] | n] | []] //= hge hgt; rewrite !bnd_simp !mulr0z //.
- by move=> lex; apply: hgt; apply: lt_le_trans lex; rewrite lte_fin ltr0z.
- exact: hgt.
- by move=> ltx; apply: hgt; apply: lt_trans ltx; rewrite lte_fin ltr0z.
Qed.

Lemma ext_num_itv_bound_keep_neg_strict (op : \bar R -> \bar R) (x : \bar R) b :
  {homo op : x / (x < 0)%E} ->
  (BRight x <= ext_num_itv_bound b)%O ->
  (BRight (op x) <= ext_num_itv_bound (ExtIntItv.keep_neg_strict_bound b))%O.
Proof.
case: b => [[] [[| n] | n] | []] //= hlt; rewrite !bnd_simp !mulr0z //.
- exact: hlt.
- by move=> ltx; apply: hlt; apply: (lt_trans ltx); rewrite lte_fin ltrz0.
- by move=> lex; apply: hlt; apply: (le_lt_trans lex); rewrite lte_fin ltrz0.
Qed.

Lemma ext_num_itv_bound_keep_ge1 (op : \bar R -> \bar R) (x : \bar R) b :
  {homo op : x / (1 <= x)%E >-> (0 <= x)%E} ->
  {homo op : x / (1 < x)%E >-> (0 < x)%E} ->
  (ext_num_itv_bound b <= BLeft x)%O ->
  (ext_num_itv_bound (ExtIntItv.keep_ge1_bound b) <= BLeft (op x))%O.
Proof.
case: b => [[] [[| [| n]] | n] | []] //= hge hgt;
  rewrite !bnd_simp !mulr0z ?mulr1z //.
- exact: hge.
- by move=> lex; apply: hgt; apply: (lt_le_trans _ lex); rewrite lte_fin ltr1z.
- exact: hgt.
- by move=> ltx; apply: hgt; apply: (le_lt_trans _ ltx); rewrite lee_fin ler1z.
Qed.

Lemma ext_num_itv_bound_keep_le1 (op : \bar R -> \bar R) (x : \bar R) b :
  {homo op : x / (x <= 1)%E >-> (x <= 0)%E} ->
  {homo op : x / (x < 1)%E >-> (x < 0)%E} ->
  (BRight x <= ext_num_itv_bound b)%O ->
  (BRight (op x) <= ext_num_itv_bound (ExtIntItv.keep_le1_bound b))%O.
Proof.
case: b => [[] [[| [| n]] | n] | []] //= hle hlt;
  rewrite !bnd_simp !mulr0z ?mulr1z //.
- by move=> ltx; apply: hle; apply/ltW/(lt_le_trans ltx); rewrite lee_fin ler01.
- exact: hlt.
- by move=> ltx; apply: hle; apply/ltW/(lt_le_trans ltx); rewrite lee_fin lerz1.
- by move=> lex; apply: hle; apply: (le_trans lex); rewrite lee_fin ler01.
- exact: hle.
- by move=> lex; apply: hle; apply: (le_trans lex); rewrite lee_fin lerz1.
Qed.

End ExtNumItvBound.

(** [-oo < r%:E] only holds unconditionally on a totally ordered base type,
    hence the stronger assumption on [R] here. *)
Section ExtRealDomainItvBound.
Context {R : realDomainType}.
Local Notation ext_num_itv_bound :=
  (@map_itv_bound _ (\bar R) (EFin \o intr)).

Lemma ext_num_itv_bound_keep_fin (op : \bar R -> \bar R) (x : \bar R) b :
  (forall y, (0 <= op y)%E) -> (forall y, (-oo < y)%E -> (0 < op y)%E) ->
  (ext_num_itv_bound b <= BLeft x)%O ->
  (ext_num_itv_bound (ExtIntItv.keep_fin_bound b) <= BLeft (op x))%O.
Proof.
case: b => [s n | []] //= hge hgt; rewrite !bnd_simp !mulr0z // => lex.
by apply: hgt; move: lex; case: s; rewrite bnd_simp; case: x => //= r _;
  exact: ltNyr.
Qed.

End ExtRealDomainItvBound.

(** If [x] is comparable to [0], then so is [x^-1].  On a [realDomainType]
    this is subsumed by [comparableT], [\bar R] being totally ordered. *)
Lemma realIe (R : realDomainType) (x : \bar R) :
  (0%:E >=< x)%O -> (0%:E >=< (x^-1)%E)%O.
Proof. by move=> _; exact: comparableT. Qed.

(** * Canonical Instances *)
Module Instances.

Section ExtRealDomainInstances.
Context {R : realDomainType}.

Local Notation ext_num_spec := (Itv.spec (@ext_num_sem R)).
Local Notation ext_num_def := (Itv.def (@ext_num_sem R)).
Local Open Scope ereal_scope.

(** ** Inversion *)
Lemma ext_num_spec_inve i (x : ext_num_def i)
    (r := Itv.real1 ExtIntItv.inve i) :
  ext_num_spec r (x%:inum^-1 : \bar R).
Proof.
apply: Itv.spec_real1 (Itv.P x).
case: x => x /= _ [l u] /and3P[_ /= lx xu]; apply/and3P; split.
- exact: comparableT.
- by apply: ext_num_itv_bound_keep_nonneg lx => y; rewrite inve_ge0.
- by apply: ext_num_itv_bound_keep_neg_strict xu => y; rewrite inve_lt0.
Qed.

Canonical inve_inum i (x : ext_num_def i) := Itv.mk (ext_num_spec_inve x).

(** ** Natural Powers *)
Lemma ext_num_spec_expe i (x : ext_num_def i) n
    (r := Itv.real1 ExtIntItv.expe i) :
  ext_num_spec r (x%:inum ^+ n : \bar R).
Proof.
apply: (@Itv.spec_real1 _ _ (fun x => x ^+ n) _ _ _ _ (Itv.P x)).
case: x => x /= _ [l u] /and3P[_ /= lx _]; apply/and3P; split => //.
by apply: (@ext_num_itv_bound_keep_pos _ (fun y => y ^+ n)) lx => y;
  [exact: expe_ge0 | exact: expe_gt0].
Qed.

Canonical expe_inum i (x : ext_num_def i) n :=
  Itv.mk (ext_num_spec_expe x n).

End ExtRealDomainInstances.

Section ExtRealInstances.
Context {R : realType}.

Local Notation ext_num_spec := (Itv.spec (@ext_num_sem R)).
Local Notation ext_num_def := (Itv.def (@ext_num_sem R)).
Local Open Scope ereal_scope.

(** ** Powers with Real Exponent and Extended Real Base *)
Lemma ext_num_spec_poweR i (x : ext_num_def i) p (r := ExtIntItv.poweR i) :
  ext_num_spec r (x%:inum `^ p : \bar R).
Proof.
rewrite {}/r; case: i x => [| [l u]] x /=.
  apply/and3P; split; [exact: comparableT | | by []].
  by rewrite /= bnd_simp mulr0z poweR_ge0.
case: x => x /= /and3P[_ /= lx _]; apply/and3P;
  split; [exact: comparableT | | by []].
by apply: (@ext_num_itv_bound_keep_pos0 _ (fun y => y `^ p)) lx;
  [move=> y; exact: poweR_ge0 | move=> y; exact: poweR_gt0].
Qed.

Canonical poweR_inum i (x : ext_num_def i) p :=
  Itv.mk (ext_num_spec_poweR x p).

(** ** Exponential *)
Lemma ext_num_spec_expeR i (x : ext_num_def i) (r := ExtIntItv.expeR i) :
  ext_num_spec r (expeR x%:inum).
Proof.
rewrite {}/r; case: i x => [| [l u]] x /=.
  apply/and3P; split; [exact: comparableT | | by []].
  by rewrite /= bnd_simp mulr0z expeR_ge0.
case: x => x /= /and3P[_ /= lx _]; apply/and3P;
  split; [exact: comparableT | | by []].
by apply: (@ext_num_itv_bound_keep_fin _ (@expeR R)) lx;
  [exact: expeR_ge0 | move=> y; exact: expeR_gt0].
Qed.

Canonical expeR_inum i (x : ext_num_def i) := Itv.mk (ext_num_spec_expeR x).

(** ** Logarithm *)
Lemma ext_num_spec_lne i (x : ext_num_def i)
    (r := Itv.real1 ExtIntItv.lne i) :
  ext_num_spec r (lne x%:inum).
Proof.
apply: Itv.spec_real1 (Itv.P x).
case: x => x /= _ [l u] /and3P[_ /= lx xu]; apply/and3P; split.
- exact: comparableT.
- by apply: (@ext_num_itv_bound_keep_ge1 _ (@lne R)) lx;
    [move=> y; rewrite lne_ge0 | move=> y; rewrite lne_gt0].
- by apply: (@ext_num_itv_bound_keep_le1 _ (@lne R)) xu;
    [move=> y; rewrite lne_le0 | move=> y; rewrite lne_lt0].
Qed.

Canonical lne_inum i (x : ext_num_def i) := Itv.mk (ext_num_spec_lne x).

End ExtRealInstances.

End Instances.
Export (canonicals) Instances.

(** * Order Structure of Extended Real Interval Types *)

(** MathComp's interval_inference.v endows every [Itv.def f i] with a
    [porderType] structure inherited from the carrier ([POrder of _ by <:]),
    and then declares an [Order.Total] instance for the *real* interval types
    [Itv.def (@Itv.num_sem R) (Itv.Real i)].  That instance occupies the single
    canonical slot attached to the head symbol [Itv.def], so no second
    [Order.Total] instance can be attached to [Itv.def (@ext_num_sem R) i]:
    HB would just report "no new instance is generated".

    We therefore only provide the *proof* that extended real interval types are
    totally ordered.  Clients that need the lattice structure of an extended
    real interval type (e.g. [{nonneg \bar R}]) must introduce a type alias with
    a fresh head constant and declare
    [Order.POrder_isTotal.Build ereal_display alias ext_itv_le_total] on it. *)
Section ExtItvOrder.
Variables (R : realDomainType) (i : Itv.t).

Lemma ext_itv_le_total : total (<=%O : rel (Itv.def (@ext_num_sem R) i)).
Proof. by move=> x y; exact: le_total. Qed.

End ExtItvOrder.

Arguments ext_itv_le_total {R i}.

(** * Examples *)

(** The instances above make the sign side conditions of the extended real
    operations disappear, exactly like for the real ones. *)
Section Examples.
Local Open Scope ereal_scope.
Variable R : realType.

Example inve_ge0_auto (x : {nonneg \bar R}) : 0 <= x%:num^-1.
Proof. by []. Qed.

Example inve_le0_auto (x : Itv.def (@ext_num_sem R) (Itv.Real `[(-3)%Z, (-1)%Z])):
  x%:num^-1 <= 0.
Proof. by []. Qed.

Example inve_lt0_auto (x : Itv.def (@ext_num_sem R) (Itv.Real `[(-3)%Z, (-1)%Z])):
  x%:num^-1 < 0.
Proof. by []. Qed.

Example poweR_ge0_auto (x : \bar R) p : 0 <= x `^ p.
Proof. by []. Qed.

Example poweR_gt0_auto (x : {posnum \bar R}) p : 0 < x%:num `^ p.
Proof. by []. Qed.

Example expeR_ge0_auto (x : \bar R) : 0 <= expeR x.
Proof. by []. Qed.

Example expe_ge0_auto (x : {nonneg \bar R}) n : 0 <= x%:num ^+ n.
Proof. by []. Qed.

Example expe_gt0_auto (x : {posnum \bar R}) n : 0 < x%:num ^+ n.
Proof. by []. Qed.

(** [expeR x > 0] as soon as [x > -oo], which any finite lower bound
    guarantees. *)
Example expeR_gt0_auto (x : {nonneg \bar R}) : 0 < expeR x%:num.
Proof. by []. Qed.

Example lne_ge0_auto (x : Itv.def (@ext_num_sem R) (Itv.Real `[1%Z, +oo[)) :
  0 <= lne x%:num.
Proof. by []. Qed.

Example lne_le0_auto (x : Itv.def (@ext_num_sem R) (Itv.Real `[0%Z, 1%Z])) :
  lne x%:num <= 0.
Proof. by []. Qed.

(** Casts are inferred as well. *)
Example inve_nng (x : {nonneg \bar R}) : {nonneg \bar R} := (x%:num^-1)%:nng.

Example poweR_nng (x : \bar R) p : {nonneg \bar R} := (x `^ p)%:nng.

Example expeR_pos (x : {posnum \bar R}) : {posnum \bar R} := (expeR x%:num)%:pos.

End Examples.