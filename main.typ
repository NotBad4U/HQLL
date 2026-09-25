#import "lib.typ": *

#import "@preview/cetz:0.4.2"
#import "@preview/showybox:2.0.4": showybox
#import "@preview/mannot:0.3.1": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/commute:0.3.0": arr, commutative-diagram, node

#let abstract = ""

#show: para-lipics.with(
  title: [Higher order QLL with QBS],
  title-running: [],
  authors: (
    // (
    //   name: [Alessio Coltellacci],
    //   email: "alecol@itu.dk",
    //   website: "httr://www.myhomepage.edu",
    //   orcid: "0009-0005-3580-2075",
    //   affiliations: [
    //   ],
    // ),
  ),
  abstract: abstract,
  keywords: [],
)



// ---------------- notation ----------------
#let sem(x) = $lr(⟦ #x ⟧)$
#let nm(x) = $lr(⌜ #x ⌝)$
#let Prd = math.op("Pred")
// Type of s-finite measures on A (formerly Dist A, the probability type).
#let Dst = math.cal("T")
#let Qbs = math.op("QBS")
#let Meas = math.op("Meas")
#let Sbs = math.op("Sbs")
#let ev = math.op("ev")
#let cur = math.op("cur")
#let esssup = math.op("ess sup")
#let essinf = math.op("ess inf")
#let ctx = math.op("ctx")
#let ty = math.op("type")
#let qdom = math.op("q-dom")
#let ret = math.op("return")
#let smp = math.op("sample")
#let scr = math.op("score")
#let nrm = math.op("norm")
#let Leb = math.op("Leb")
// s-finite kernel arrow, absolute continuity, 0-∞-absolute continuity,
// and the density action of [0,∞]-valued functions on measures.
#let kto = math.class("relation", sym.arrow.r.squiggly)
#let ac = math.class("relation", sym.lt.double)
#let acinf = math.class("relation", math.attach(sym.lt.double, t: sym.infinity))
#let act = math.class("binary", sym.triangle.stroked.r)
// sequencing M ; N inside function calls (a bare ";" would split the arguments)
#let seq = math.class("binary", ";")
// Typing colons for context extensions: cartesian (∞) and probabilistic (p)
#let coo = math.attach(sym.colon, br: sym.infinity)
#let cp = math.attach(sym.colon, br: math.italic("p"))
#let sof = math.bb("S")
#let bG = math.bb("G")
#let bL = math.bb("L")

#let defbox(ttl, body) = showybox(
  title: ttl,
  frame: (
    border-color: rgb("#334155"),
    title-color: rgb("#334155"),
    body-color: rgb("#f8fafc"),
  ),
  breakable: true,
  body,
)

#let rem(body) = block(
  inset: (left: 7pt),
  above: 5pt,
  below: 5pt,
  stroke: (left: 1.3pt + rgb("#94a3b8")),
  text(9pt, body),
)

#let prov = box(
  fill: rgb("#fef3c7"),
  inset: (x: 3pt, y: 1pt),
  radius: 2pt,
  text(size: 7.5pt, weight: "bold", fill: rgb("#92400e"), "PROV"),
)

#let tb(..args) = table(
  inset: 5pt,
  stroke: 0.4pt + rgb("#cbd5e1"),
  ..args,
)

// ============================================================

= Multiplicative Extended Reals $RR_times.o$

*Truth values* $Omega = [0,oo]$.

#tb(
  columns: (1fr, auto),
  table.header([*operations*], [*unit*]),
  [$a ⊗ b = a b$ #h(1em) ($0 ⊗ oo = 0$)],
  [$1$],
  [$a ⊗^* b = a b$ #h(1em) ($0 ⊗^* oo = oo$)],
  [$1$],
  [$a^* = 1 slash a$, #h(0.4em) $0^* = oo$],
  [---],
  [$a multimap b = sup{c mid(|) a ⊗ c <= b} = a^* ⊗^* b$],
  [---],
  [$a ⊕^p b = (a^p + b^p)^(1 slash p)$, #h(0.4em) $a ⊕^(-p) b = (a^(-p) + b^(-p))^(-1 slash p)$],
  [$0$ / $oo$],
)

// #rem[
//   The two corner conventions $0 ⊗ oo = 0$ and $0 ⊗^* oo = oo$ are forced, not ad hoc:
//   they are exactly what makes $multimap$ the residual of $⊗$ at every boundary
//   ($a ⊗ b <= c$ iff $b <= a multimap c$, e.g. $0 multimap 0 = oo$ needs
//   $oo ⊗^* 0 = oo$), what makes $(-)^*$ an involution with dualizing element $1$
//   (so $(Omega, ⊗, 1, (-)^*)$ is a *Girard quantale* and $⊗^*$ its "par"), and what
//   makes reflexivity of the graded entailment of @sec:quasitripos exact. Via $-log$,
//   $(Omega, <=, ⊗, 1)$ is isomorphic to the extended Lawvere quantale
//   $([-oo,+oo], >=, +, 0)$ @lawvere1973, with $(-)^*$ becoming negation.
// ]

*Grades* $sof = [0,oo]$.

#tb(
  columns: (1fr, auto),
  table.header([*operations*], [*unit*]),
  [$p ⊕^* q = (p^(-1) + q^(-1))^(-1)$ #h(0.6em) (harmonic sum)],
  [$oo$],
  [$p and q$ #h(0.6em) (meet, used by thinning and substitution)],
  [$oo$],
)

= Syntax

*Grammar of types*

$
  & "Regular" quad & A, B & ::= 1 mid(|) RR mid(|) Omega mid(|) A times B mid(|) A -> B mid(|) Dst A \
  & "Domain" quad  & D, E & ::= D times.o E mid(|) A_omega \
  \
  & "Carrier" quad &      & |A_omega| ≡ A quad quad |D times.o E| ≡ |D| times |E| \
$

#v(1em)

Formulas are the terms of type $Omega$.
Regular types $A$ or $RR$ are interpreted as QBS without measure associated, and
$A_omega$ is interpreted as a QBS with the *s-finite measure* $omega: Dst A$ associated.
The measure is not required to be normalised: $omega$ may be a probability distribution,
but also an unnormalised or infinite measure such as Lebesgue measure on $RR$ (an improper
prior), or the unnormalised posterior computed by a program that uses $scr$. Following
@staton2017commutative, s-finite measures are the smallest class of measures that contains
the probability distributions and is closed under the constructs of the computational
language ($"let"$, $smp$, $scr$); their basic theory is developed in @vakar2026sfinite.
The sort separation between $A$ and $A_omega$  is what preserves cartesian closure i.e
$A_omega -> B$, $Dst A_omega$ and $(A_omega)_omega'$ are not well-formed types , so no exponential of a measured object is ever demanded.


===== Terms

$
     t, s & ::= x mid(|) ast mid(|) ⟨ t\, s ⟩
            mid(|) pi_1 t mid(|) pi_2 t mid(|) lambda x : A. t mid(|) t space s
            mid(|) c_Omega
            mid(|) hat(forall)^p (t\, s) mid(|) hat(exists)^p (t\, s) \
     M, N & ::= ret t mid(|) "let" x <- M "in" N
            mid(|) smp_mu mid(|) scr(t) mid(|) nrm (M) \
  c_Omega & ::= 0 mid(|) 1 mid(|) oo mid(|) ⊗
            mid(|) ⊗^* mid(|) multimap mid(|) (-)^*
            mid(|) ⊕^p mid(|) ⊕^(-p) mid(|) (-)^p
$

#v(1em)

Arities, by arity:
- $0, 1, oo : Omega$ #h(0.4em) (nullary);
- $(-)^*, (-)^p : Omega -> Omega$;
- $⊗, ⊗^*, multimap, ⊕^(plus.minus p) : Omega times Omega -> Omega$;
- $hat(forall)^p, hat(exists)^p : Dst A times Prd A -> Omega$.

The computation $smp_mu$ draws from a constant s-finite measure $mu$: a probability
distribution, but also Lebesgue measure $Leb$ on $RR$ or counting measure $\#_NN$ on $NN$.
The computation $scr(phi)$ is a *soft constraint*: it multiplies the weight of the current
execution by the truth value of the formula $phi$. Since formulas already take values in
$Omega = [0,oo]$, no coercion is needed: $Omega$ is exactly the type $Dst 1$ of s-finite
measures on the unit type (@def:sfinite). We write $M ; N$ for $"let" x <- M "in" N$ with
$x$ fresh.


#definition[
  - $"Pred" A ≔ A -> Omega$
  - $"Pred"^2 A ≔ ("Pred" A) -> Omega$
  - $forall^p (x : A_omega). phi ≔ hat(forall)^p (omega\, lambda x : A. phi),$
  - $exists^p (x : A_omega). phi ≔ hat(exists)^p (omega\, lambda x : A. phi),$
]

// #rem[
//   Note the regrade in the sugar: Q-Bind types the bound variable $x cp A_omega$,
//   while the right-hand side $lambda$-abstracts it at $x coo A$. The two are
//   coherent because both are interpreted over the same underlying space
//   $sem(A)$ --- the grade and the measure of the discharged slot are consumed by
//   the quantifier, not by the $lambda$ --- but this deserves an explicit coherence
//   lemma.
// ]


*Conversion rules:*

#grid(
  columns: (1fr, 1fr),
  column-gutter: 16pt,
  row-gutter: 7pt,
  align: left,
  $(lambda x : A. space t) space s ≡ t[s slash x]$, $⟨ pi_1 t, pi_2 t ⟩ ≡ t$,
  $(lambda x : A. space phi) space t ≡ phi[t slash x]$, $pi_i ⟨ t_1, t_2 ⟩ ≡ t_i$,
  $(lambda u : Prd A. space Phi) space psi ≡ Phi[psi slash u]$,
  $lambda x : A. space (t space x) ≡ t quad (x in.not "FV"(t))$,

  $"let" x <- ret t "in" N ≡ N[t slash x]$, $lambda x : A. space (u space x) ≡ u quad (u : Prd A)$,
  $"let" x <- M "in" ret x ≡ M$, $hat(forall)^p (nu, u) = hat(forall)^p (nu', u) quad ("if" nu equiv nu')$,

  $scr(1) ≡ ret ast$, $scr(phi) seq scr(psi) ≡ scr(phi ⊗ psi)$,
)

#v(4pt)

$
  "let" x <- M "in" "let" y <- N "in" P quad ≡ quad "let" y <- N "in" "let" x <- M "in" P
  quad quad (x in.not "FV"(N), space y in.not "FV"(M))
$

The last equation is *commutativity*: the order of independent computations is
immaterial. It is sound because the s-finite monad is commutative
(@vakar2026sfinite[Thm. 19], @staton2017commutative), and it is the equation that fails for
general (non s-finite) measures, where Fubini's theorem is unavailable.

== Judgement

We have the basic judgement forms:

- $A ty$ \ saying that "$A$ is a well-formed *value* type";
- $D "dom"$\ saying that "$D$ is a well-formed *domain* type";
- $Gamma ctx$ \ saying that "$Gamma$ is a well-formed context"
- $Gamma tack t : A$ \ saying that "$t$ is a well-typed term of value type $A$ in context $Gamma$";
- $Gamma tack phi "prop"$ for the special case $A = Omega$;

#v(2em)

In addition, there are judgements for definitional equality of types and of
terms:


#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 6pt,
  $A ≡ A' ty$, $D ≡ D' "dom"$, $Gamma tack t ≡ t' : A$,
))




== Context

Contexts are ordered lists and admit neither exchange nor contraction in general.
The grade sits on the variable; the measure sits on its domain type.

$
  Gamma ::= diamond.small mid(|) Gamma attach(:, br: infinity) A mid(|) Gamma attach(:, br: p) D quad (p < infinity)
$

*Context formation rules:*

#grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 6pt,
  prooftree(rule(name: [C-Emp], $diamond.small ctx$)),
  prooftree(rule(name: [$"C-Ext"_oo$], $Gamma ctx$, $A ty$, $Gamma\, x coo A ctx$)),
  prooftree(rule(name: [$"C-Ext"_D$], $Gamma ctx$, $D "dom"$, $Gamma\, x cp D ctx$)),
)

== Typing and formation

#grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  row-gutter: 12pt,
  prooftree(rule(name: [Dom], $A ty$, $dot.c tack omega : Dst A$, $A_omega "dom"$)),
  prooftree(rule(name: [$"Dom"^⊗$], $D "dom"$, $E "dom"$, $D ⊗ E "dom"$)),

  prooftree(rule(name: [Prop], $Gamma tack phi : Omega$, $Gamma tack phi "prop"$)),
  prooftree(rule(
    name: [$"Var"_oo$],
    $Gamma\, x coo A \, Gamma' tack x : A$,
  )),

  prooftree(rule(
    name: [$"Var"_D$],
    $Gamma\, x cp D \, Gamma' tack x : |D|$,
  )),
  prooftree(rule(name: [Unit], $Gamma ctx$, $Gamma tack ast : 1$)),

  prooftree(rule(name: [Pair], $Gamma tack t : A$, $Gamma tack s : B$, $Gamma tack ⟨ t\, s ⟩ : A times B$)),
  prooftree(rule(name: [Proj], $Gamma tack t : A_1 times A_2$, $Gamma tack pi_i t : A_i$)),

  prooftree(rule(name: [Abs], $Gamma\, x coo A tack t : B$, $Gamma tack lambda x : A. t : A -> B$)),
  prooftree(rule(name: [App], $Gamma tack t : A -> B$, $Gamma tack s : A$, $Gamma tack t space s : B$)),

  prooftree(rule(name: [P-Abs], $Gamma\, x coo A tack phi "prop"$, $Gamma tack lambda x : A. phi : Prd A$)),
  prooftree(rule(name: [P-App], $Gamma tack u : Prd A$, $Gamma tack t : A$, $Gamma tack u space t "prop"$)),

  prooftree(rule(
    name: [Conn],
    $c_Omega "of arity" n$,
    $Gamma tack phi_i "prop" #h(0.3em) (i <= n)$,
    $Gamma tack c_Omega (phi_1\, dots.c\, phi_n) "prop"$,
  )),
  prooftree(rule(
    name: [Q-Int],
    $Gamma tack nu : Dst A$,
    $Gamma tack u : Prd A$,
    $Gamma tack hat(forall)^p (nu\, u) "prop"$,
  )),
)

#v(6pt)
#align(center, prooftree(rule(
  name: [Q-Bind],
  $Gamma\, x cp D tack phi "prop"$,
  $D "dom"$,
  $p < oo$,
  $Gamma tack forall^p (x : D). phi "prop"$,
)))

// #rem[
//   Conn is indexed by the arity of the constant, so it covers the whole signature
//   $c_Omega$ at once. At $n = 0$ it types the *constants*: $Gamma tack 0 : Omega$,
//   $Gamma tack 1 : Omega$ and $Gamma tack oo : Omega$ in every well-formed
//   context, with no premise beyond $Gamma ctx$; at $n = 1$ the involution and the
//   powers $phi^*, phi^p$; at $n = 2$ the binary connectives. We keep the usual
//   infix and postfix notation ($phi ⊗ psi$, $phi^*$) as sugar for the official
//   applicative form $c_Omega (phi_1, dots.c, phi_n)$. Via Prop, every such term
//   is also a proposition, which is what the operator semantics below interprets.
// ]

#v(1em)

*Monadic rules:*

#v(1em)

#grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 7pt,
  row-gutter: 10pt,
  prooftree(rule(name: [Ret], $Gamma tack t : A$, $Gamma tack ret t : Dst A$)),
  prooftree(rule(name: [Smp], $mu "s-finite on" A$, $Gamma tack smp_mu : Dst A$)),
  prooftree(rule(name: [Score], $Gamma tack phi : Omega$, $Gamma tack scr(phi) : Dst 1$)),
)
#v(6pt)
#grid(
  columns: (1fr, 1fr),
  gutter: 7pt,
  prooftree(rule(name: [Nrm], $Gamma tack M : Dst A$, $Gamma tack nrm (M) : Dst A$)),
  prooftree(rule(
    name: [Let],
    $Gamma tack M : Dst A$,
    $Gamma\, x coo A tack N : Dst B$,
    $Gamma tack "let" x <- M "in" N : Dst B$,
  )),
)

The side condition of Smp reads: $mu$ is an s-finite measure on the space denoted by $A$
(a constant of the language, as in @staton2017commutative). The probability version
deliberately had no normalisation construct, since normalisation is the identity on
probability measures. Over s-finite measures $nrm$ is the (partial) operation that turns
an unnormalised model such as $"let" x <- smp_mu "in" scr(phi space x) ; ret x$ into a
posterior distribution (@def:normalise).


= Semantics

== Preliminaries

#definition("QBS")[
  $X = (|X|, M_X)$ is a *quasi-Borel space* with a underlying set $|X|$ and a set of functions $M_X subset.eq { RR -> |X|}$ closed under precomposition with Borel maps, containing constants, closed under countable Borel gluing. Given $f: X -> Y$ is a morphism if and only if $f compose alpha in M_Y$ for all $alpha in M_X$.
  - QBS is cartesian closed: $M_(Y^X) = { alpha mid(|) "uncurry"(alpha) in "QBS"(RR times X, Y)}$
  - QBS is well pointed
  - $Sigma_(M_X) = { U mid(|) forall alpha in M_X dot alpha^(-1) U in Sigma_RR}$ is the induced 𝜎-algebra.
  - $M_X = Qbs(RR, X)$, and for a standard Borel space $X$ (regarded as a QBS with
    $M_X = Meas(RR, X)$) one has $Qbs(X, Y) = Meas(X, Sigma_(M_Y))$
    @vakar2026sfinite[Thm. 18].
]

Measures on a QBS are introduced through the *s-finite monad* $T$ of
@scibior2018denotational, in the presentation of @vakar2026sfinite[§11]. Recall that a
measure $mu$ on a measurable space is *s-finite* if it is a countable sum of finite
measures, and that a kernel $k : X kto Y$ is s-finite if it is a countable sum of
kernels $k_i$ with $sup_x k_i (x, Y) < oo$ @vakar2026sfinite[Def. 1]. S-finite kernels are
closed under composition @staton2017commutative and contain the probability kernels,
Lebesgue measure and counting measure on $NN$; counting measure on $RR$ is not s-finite.

#definition([S-finite measures on a QBS: the monad $T$])[
  Let $X in Qbs$ and let $Sbs$ denote the standard Borel spaces.
  - A *(randomisable) s-finite measure* on $X$ is a triple $⟨W, mu, alpha⟩$ with
    $W in Sbs$, $mu$ an s-finite measure on $W$ and $alpha in Qbs(W, X)$
    @vakar2026sfinite[Def. 6]. It integrates every $f in Qbs(X, Omega)$ by
    $
      integral_X f dif ⟨W, mu, alpha⟩ := integral_W f(alpha(w)) space dif mu(w).
    $
  - Two triples are identified when they define the same integral operator on
    $Qbs(X, Omega)$; equivalently @vakar2026sfinite[Thm. 20], when the push-forward
    measures $alpha_* mu$ and $alpha'_* mu'$ on $Sigma_(M_X)$ coincide. The carrier
    $|T X|$ is the set of classes $[W, mu, alpha]$.
  - The random elements are the s-finite *kernels* into $X$:
    $
      M_(T X) := { r |-> [W, k(r, -), alpha(r, -)] mid(|) & W in Sbs, space k : RR kto W "an s-finite kernel", \
      & alpha in Qbs(RR times W, X) }.
    $
  - $T$ is a *commutative* monad on $Qbs$, with unit and bind inherited from the
    continuation monad $((-) => Omega) => Omega$ into which $T$ embeds by
    $nu |-> integral_X (-) dif nu$ @vakar2026sfinite[Thm. 19].
  - If $X in Sbs$, then $|T X|$ is the set of *all* s-finite measures on $X$, and for
    $X, Y in Sbs$ the Kleisli hom $Qbs(X, T Y)$ is the set of all s-finite kernels
    $X kto Y$ @vakar2026sfinite[Cor. 2]. In particular $T 1 = [0, oo] = Omega$.
  - The probability monad $cal(P)$ of @qbs is the sub-monad of $T$ obtained by requiring
    $mu$ to be a probability measure, so every object and construction of the probability
    version is a special case of what follows. ($T$ is the semantic incarnation of the
    type constructor written $Dst$ above.)
] <def:sfinite>

#lemma([One parameter line suffices])[
  Every s-finite measure on $X$ has a representative on $W = RR$, and every random
  element of $T X$ has a representative with a fixed random element of $X$:
  $
    |T X| &= { [alpha, mu] mid(|) alpha in M_X, space mu "s-finite on" RR } slash ~, \
    M_(T X) &= { r |-> [alpha, k(r, -)] mid(|) alpha in M_X, space k : RR kto RR "an s-finite kernel" }.
  $
  #proof[
    Every $W in Sbs$ is a measurable retract of $RR$ @vakar2026sfinite[Prop. 1]:
    $W -->^f RR -->^g W$ with $g compose f = "id"_W$. Then
    $[W, mu, alpha] = [RR, f_* mu, alpha compose g]$ because
    $(alpha compose g)_* f_* mu = alpha_* (g compose f)_* mu = alpha_* mu$; here $f_* mu$
    is s-finite as a push-forward of an s-finite measure @vakar2026sfinite[Thm. 1] and
    $alpha compose g in Qbs(RR, X) = M_X$. For random elements apply the same retraction to
    $k(r, -)$ pointwise, then absorb the $r$-dependence of $alpha(r, -)$ into the kernel
    through a Borel isomorphism $phi : RR tilde.equiv RR times RR$:
    $[alpha(r, -), k(r, -)] = [alpha compose phi, space (phi^(-1))_* (delta_r ⊗ k(r, -))]$,
    where $r |-> delta_r ⊗ k(r, -)$ is an s-finite kernel $RR kto RR times RR$ by
    @vakar2026sfinite[Thm. 5(3)].
  ]
]

Henceforth we write $[alpha, mu]$ for elements of $T X$, exactly as in the probability
version, with the single difference that $mu$ is an s-finite measure on $RR$ rather than
a probability measure.

#definition([Monad structure, strength and density action])[
  In the representation $[alpha, mu]$:
  - *Functor.* On morphisms $f : X -> Y$ the action is $T(f)[alpha, mu] := [f compose alpha, mu]$.
  - *Unit* $eta_X (x) := [lambda r. x, space delta_0]$, the Dirac measure at $x$.
  - *Kleisli extension.* For $f : X -> T Y$ the composite $f compose alpha in M_(T Y)$ has
    the form $r |-> [beta, k(r, -)]$ by the previous lemma, and
    $
      f^dagger [alpha, mu] := [beta, space mu ; k], quad quad
      (mu ; k)(V) := integral_RR k(r, V) space dif mu(r),
    $
    the composite of the s-finite kernels $mu : 1 kto RR$ and $k : RR kto RR$, which is
    s-finite @vakar2026sfinite[Thm. 1]. Equivalently, $f^dagger$ is characterised on
    integrals by $I_Y (f^dagger nu, v) = I_X (nu, space lambda x. I_Y (f x, v))$ for all
    $v in Omega^Y$, with $I$ the integration operator of @def:integration.
  - *Strength* $"st"_(X, Y)(x, [alpha, mu]) := [lambda r. (x, alpha(r)), space mu]$.
  - *Density action.* For $nu = [alpha, mu] in T X$ and $u in Omega^X$,
    $
      nu act u := [alpha, space mu act (u compose alpha)], quad quad
      (mu act g)(U) := integral_U g space dif mu,
    $
    an s-finite measure by @vakar2026sfinite[Thm. 5(3)]. It depends only on the class of
    $nu$, since $(alpha)_* (mu act (u compose alpha)) = (alpha_* mu) act u$, and it
    satisfies $(nu act u)(|X|) = I_X (nu, u)$. Scalar multiplication
    $c dot nu := nu act (lambda x. c)$ for $c in [0, oo]$ (with $0 dot oo = 0$) is the
    special case of a constant density.
]

We now define the category of measured quasi-Borel spaces that will interpret our domain types.

#definition($"Category QBS"_C$)[
  - Objects are $(|X|, M_X, omega_X)$, *measured quasi-Borel spaces*, written
    $(X, omega)$, with a QBS structure $(|X|, M_X)$ and an s-finite measure
    $omega_X in |T X|$. Objects whose measure is a probability distribution are the
    measured spaces of the probability version; improper priors such as $(RR, Leb)$ and
    unnormalised posteriors are now objects as well.

  - Morphisms $f : (X, omega) -> (Y, rho)$ are QBS morphisms $f : X -> Y$ of
    *finite compression*, $C(f) < oo$. Writing
    $f_* omega := l_Y (T(f)(omega)) = (f compose alpha)_* mu$ for the induced s-finite
    measure on $Sigma_(M_Y)$ (where $l_Y [alpha, mu] := alpha_* mu$), the *measure
    compression* of $f$ is
    $
      C(f) := ⋀ {B in [0,oo] mid(|) forall U in Sigma_(M_Y). space
        (f_* omega)(U) <= B ⊗^* rho(U)},
    $
    the least $B$ with $f_* omega <= B ⊗^* rho$. One has $C(f) <= 1$ iff
    $f_* omega <= rho$. When $omega$ and $rho$ are probability measures this forces
    $f_* omega = rho$, so on probability objects $C(f) = 1$ iff $f$ is measure-preserving;
    for unnormalised measures $f_* omega <= rho$ is a genuine inequality.

  - Identities and composition are those of $"QBS"$. This is well defined
    because $C("id"_X) = 1$ and $C$ is lax,
    $ C(g compose f) <= C(f) dot C(g), $
    so finite compression is closed under composition.
]

#lemma([Compression, densities and $0$-$oo$-sets])[
  Let $f : (X, omega) -> (Y, rho)$ be a QBS morphism with $C(f) < oo$, and let
  $oo[rho]$ be the *top $0$-$oo$-set* of $rho$ @vakar2026sfinite[Thm. 8]: $rho$ is
  $sigma$-finite on $Y without oo[rho]$ and takes only the values $0$ and $oo$ on
  measurable subsets of $oo[rho]$ (for $sigma$-finite $rho$, in particular for
  probability measures, $oo[rho]$ is null).
  + $f_* omega ac rho$ (absolute continuity), but not necessarily
    $f_* omega acinf rho$; hence a density $dif f_* omega slash dif rho$ need not exist
    @vakar2026sfinite[Thm. 21]. For instance $"id" : (RR, cal(N)(0,1)) -> (RR, oo dot Leb)$
    has $C("id") = 0$, but $cal(N)(0,1)$ has no density with respect to $oo dot Leb$.
  + On $oo[rho]$ the compression condition reduces to absolute continuity: it is vacuous
    on sets of infinite $rho$-measure and forces $f_* omega (V) = 0$ on $rho$-null $V$.
  + On $Y without oo[rho]$ the restriction of $f_* omega$ has a measurable density $g$
    with respect to $rho$ (Radon-Nikodým for s-finite measures,
    @vakar2026sfinite[Thm. 10]; the $0$-$oo$ condition is vacuous for $sigma$-finite
    $rho$), and
    $
      C(f) = esssup_rho { g(y) mid(|) y in Y without oo[rho] }.
    $
  So for $sigma$-finite $rho$ we recover the previous description of $C(f)$ as the
  essential bound of the density, while the badly infinite part $oo[rho]$ of the target
  measure is invisible to $C$.
  #proof[
    (1) If $rho(U) = 0$ then $f_* omega (U) <= C(f) ⊗^* 0 = 0$ as $C(f) < oo$. In the
    example, $oo dot Leb$ takes only the values $0$ and $oo$, so $B = 0$ satisfies
    $cal(N)(0,1)(U) <= 0 ⊗^* (oo dot Leb)(U)$ for every $U$; the absence of a density
    is the counterexample of @vakar2026sfinite[Thm. 10]. (2) is immediate from
    $B ⊗^* oo = oo$. (3) On the $sigma$-finite part, $integral_U g dif rho <= B ⊗^* rho(U)$
    for all $U$ iff $g <= B$ $rho$-a.e., by testing on sets of finite $rho$-measure.
  ]
]

#lemma([Monoidal product in $"QBS"_C$])[
  $
    (X, omega) ⊗ (Y, rho) := (X times Y, space omega ⊗ rho), quad quad
    I := (1, delta_ast),
  $
  where for $omega = [alpha, mu]$ and $rho = [beta, mu']$ the product measure
  $omega ⊗ rho := [alpha times beta, space mu ⊗ mu']$ is the double strength of the
  commutative monad $T$ @vakar2026sfinite[Thm. 19]. Here $mu ⊗ mu'$ is the product of
  s-finite measures on $RR^2$ defined by iterated integration; the order of integration is
  immaterial by the limited Fubini theorem for s-finite kernels
  (@staton2017commutative, @vakar2026sfinite[Thm. 4]):
  $
    (omega ⊗ rho)(W)
      = integral_X omega(dif x) integral_Y rho(dif y) space chi_W (x, y)
      = integral_Y rho(dif y) integral_X omega(dif x) space chi_W (x, y).
  $
  This is the product that interprets $"let" x <- M "in" "let" y <- N "in" ret ⟨x, y⟩$.
  It may differ from the maximal (Carathéodory) product $omega ⊠ rho$
  @vakar2026sfinite[Thm. 3]; we never use the latter.

  The marginals of a product are scaled by the *mass* of the discarded factor,
  $
    (pi_1)_* (omega ⊗ rho) = rho(|Y|) dot omega, quad quad
    (pi_2)_* (omega ⊗ rho) = omega(|X|) dot rho, quad quad
    !_* omega = omega(|X|) dot delta_ast,
  $
  so $C(pi_1) = rho(|Y|)$ and $C(pi_2) = omega(|X|)$ (as soon as the retained factor has
  a set of finite positive measure), and $C(!) = omega(|X|)$ for the unique map
  $! : (X, omega) -> I$. Hence projections and $!$ are morphisms of $"QBS"_C$ exactly
  when the discarded measure has *finite total mass*. The structure $⊗$ is symmetric
  monoidal; it is *semicartesian* (unit terminal, projections everywhere) only on the full
  subcategory $"QBS"_C^"fin"$ of finite measures, and on probability objects
  $C(pi_i) = C(!) = 1$ as before.

  #align(center)[
    #commutative-diagram(
      node((0, 1), $(Z, tau)$),
      node((1, 0), $(X, omega)$),
      node((1, 1), $(X times Y, space omega ⊗ rho)$),
      node((1, 2), $(Y, rho)$),
      arr((0, 1), (1, 0), $f$, label-pos: right),
      arr((0, 1), (1, 1), $⟨f\, g⟩$, "dashed"),
      arr((0, 1), (1, 2), $g$),
      arr((1, 1), (1, 0), $pi_1$),
      arr((1, 1), (1, 2), $pi_2$, label-pos: right),
    )
  ]

  It is *not* cartesian: the pairing factors as
  $⟨f,g⟩ = (f times g) compose Delta_Z$, so
  $C(⟨f,g⟩) <= C(Delta_Z) dot C(f) dot C(g)$ and the dashed map exists only
  where $Delta_Z$ does.
]

#lemma([Diagonals in $"QBS"_C$])[
  Assume $Sigma_(M_X)$ is countably separated with measurable singletons
  (e.g. $X$ standard Borel). Then
  $Delta_X = ⟨"id", "id"⟩$ is a morphism of $"QBS"_C$ iff $omega$ is *purely
  atomic* with its finite atom masses bounded below, i.e.
  $omega = sum_i m_i delta_(a_i)$ with countably many atoms, $m_i in (0, oo]$, and
  $inf {m_i mid(|) m_i < oo} > 0$, in which case
  $
    C(Delta_X) = 1 slash inf {m_i mid(|) m_i < oo}
  $
  (with $inf emptyset = oo$, so $C(Delta_X) = 0$ when every atom has infinite mass).
  In particular $Delta_X$ is never a morphism when $omega$ has an atomless part, while
  atoms of infinite mass, and more generally the top $0$-$oo$-set $oo[omega]$, impose no
  constraint. For a probability measure the condition forces finitely many atoms and
  reduces to $C(Delta_X) = 1 slash min_i m_i$.

  #align(center)[
    #commutative-diagram(
      node((0, 0), $(X, omega)$),
      node((0, 1), $(X times X, space omega ⊗ omega)$),
      node((0, 2), $(X, omega)$),
      arr((0, 0), (0, 1), $Delta_X$),
      arr((0, 1), (0, 2), $pi_i$),
      arr((0, 0), (0, 2), $"id"_X$, curve: -15deg),
    )
  ]
]

#definition([Forgetful functor V])[
  $V : "QBS"_C -> "QBS"$ acts by $(X, omega) |-> (|X|, M_X)$ on objects and by
  $f |-> f$ on morphisms. The functor drops the measure and forgets the compression condition.
  It is *faithful* but not full: a $"QBS"$-morphism with
  $C(f) = oo$ is not a morphism of $"QBS"_C$. It sends $⊗$ to the cartesian
  product, $V((X,omega) ⊗ (Y,rho)) = V(X,omega) times V(Y,rho)$, and the unit
  to the terminal object.
]

== Types

We define the semantics of types recursively as follows:

#grid(
  columns: (1fr, 1fr, 1fr),
  align: center,
  row-gutter: 10pt,
  $sem(1) = 1$, $sem(RR) = RR$, $sem(Omega) = [0,oo] = T 1$,
  $sem(A times B) = sem(A) times sem(B)$, $sem(A -> B) = sem(B)^(sem(A))$, $sem(Dst A) = T sem(A)$,
  $sem(Prd A) = Omega^(sem(A))$,
) <eq:types>


Where $[0, oo]$ is standard Borel with $M_Omega = {"Borel" RR -> [0, oo] }$. We interpret domain types as the followings:

$
  sem(A_omega) := (sem(A), sem(omega)) in Qbs_C, quad quad
  sem(D ⊗ E) := sem(D) times sem(E) "with" omega_D ⊗ omega_E, quad quad
$ <eq:dom>

where $sem(omega) in |T sem(A)|$ is the s-finite measure denoted by the closed
computation $dot.c tack omega : Dst A$.

== Contexts

#definition([Category $"Ctx"$ of graded contexts])[
  - *Objects* are finite ordered lists $Gamma = ((X_1, p_1), dots, (X_n, p_n))$
    of *slots*, where $p_i in SS = [0,oo]$ is a softness and
    $
      cases(
        X_i in "QBS"_C quad p_i < oo,
        X_i in "QBS" quad p_i = oo
      )
    $
    Write $P = (p_1, dots, p_n) in SS^n$ to denotes the grade vector of $Gamma$ and $|Gamma| = n$.

  - *Morphisms* $(rho, f) : ((X_i, p_i))_(i <= n) -> ((Y_j, q_j))_(j <= m)$
    consist of a *thinning* --- a monotone injection $rho : [m] -> [n]$ ---
    together with, for each $j <= m$, a morphism $f_j : X_(rho(j)) -> Y_j$, subject
    to the *grade compatibility* condition $q_j < oo ==> p_(rho(j)) < oo$: a
    measured target slot must be fed by a measured source slot, and there
    $f_j$ is a morphism of $"QBS"_C$ (finite compression); if $q_j = oo$ then
    $f_j$ is a plain $"QBS"$ morphism $V X_(rho(j)) -> Y_j$.

  - *Identities and composition.* For $(rho, f) : Gamma -> Delta$ and
    $(rho', f') : Delta -> Theta$ with $|Gamma| = n$, $|Delta| = m$, $|Theta| = l$:
    $
      "id"_Gamma := ("id"_([n]), ("id"_(X_i))_(i <= n)), quad quad
      (rho', f') compose (rho, f) := (rho compose rho',
        space (f'_k compose f_(rho'(k)))_(k <= l)).
    $
    This is well defined: monotone injections compose ($rho compose rho' : [l] -> [n]$
    is the composite thinning), grade compatibility composes
    ($r_k < oo ==> q_(rho'(k)) < oo ==> p_(rho(rho'(k))) < oo$), and finite
    compression is closed under composition since $C$ is lax
    ($C(g compose f) <= C(f) dot C(g)$, $C("id") = 1$). Associativity and unit laws
    are componentwise.

  - *Ordered products* by concatenation,
    $Gamma ; Delta := (X_1, p_1; dots; X_n, p_n; Z_1, r_1; dots; Z_k, r_k)$.
]

#lemma([Grading and monoidal structure of $"Ctx"$])[
  Concatenation makes $"Ctx"$ a *semicartesian symmetric monoidal category*: the
  unit is the empty list $diamond.small$, which is terminal (the empty
  thinning), and the projections $Gamma ; Delta -> Gamma$ are thinnings with
  identity components. There are no diagonals in general. Each morphism carries
  the *compression grade*
  $
    C(rho, f) := product_(j : q_j < oo) C(f_j) in sof,
  $
  which is lax: $C("id"_Gamma) = 1$ and
  $C((rho', f') compose (rho, f)) <= C(rho, f) dot C(rho', f')$, by laxity of
  $C$ on each component. Entailment grades transport along thinnings by
  $rho_* (P)_i := and.big_(rho(j) = i) p_j$ (with $and.big emptyset = oo$):
  thinning acts on grades by the meet $and$ of the grade quantale.
]

#definition([Underlying-space functor])[
  We can retrieve the underlying space of a context by a functor
  $U : "Ctx" -> "QBS"$ and come back by $iota : "QBS" -> "Ctx"$ are given by
  - $U((X_i, p_i)_(i <= n)) := V X_1 times dots.c times V X_n$
  - $U(rho, f) := ⟨ f_1 compose pi_(rho(1)), dots.c, f_m compose pi_(rho(m)) ⟩
    : U Gamma -> U Delta$ (project along the thinning, then apply the components;
    the bare product $f_1 times dots.c times f_m$ is not a map out of $U Gamma$
    when $rho$ is a proper thinning)
  - $iota(X) := (X, oo)$
  - $iota(g) := ("id"_([bb(1)]), (g)),$
  Thus $U$ discards *both*
  grades and measures, and $iota$ is the full and faithful embedding of $"QBS"$
  as the unmeasured one-slot contexts, corestricting to an equivalence
  $"QBS" tilde.equiv "Ctx"_oo$.

  #align(center, commutative-diagram(
    node((0, 0), $"QBS"$),
    node((0, 1), $"Ctx"$),
    node((1, 1), $"QBS"$),
    arr((0, 0), (0, 1), $iota$, "inj"),
    arr((0, 1), (1, 1), $U$),
    arr((0, 0), (1, 1), $"id"_("QBS")$, label-pos: right),
  ))

  So $U compose iota = "id"_("QBS")$: $U$ is a retraction of $iota$, and it
  lands in a cartesian closed category although $"Ctx"$ is not even cartesian.
  Terms and predicates are interpreted over $U Gamma$.
]

*Semantics of context:*

For $Gamma = (x_1 attach(:, br: p_1) T_1\, dots\, x_n attach(:, br: p_n) T_n)$, one slot per variable we interpret the context as object in the category $"Ctx"$ of graded contexts:
$
  sem(Gamma) := (sem(T_1), p_1) ; dots.c ; (sem(T_n), p_n),
  quad quad
  U sem(Gamma) = V sem(T_1) times dots.c times V sem(T_n),
$ <eq:ctx>


== Terms and computations

We will define the logical connectors in the next section, but here we give the semantics of the basic term constructors. The interpretation of a term $Gamma tack t : A$ is a morphism in $"QBS"$:

The interpretation $sem(Gamma tack -) : U sem(Gamma) -> sem(A)$ is defined by:

#grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 10pt,
  $sem(x) = pi_i$, $sem(ast) = !$,
  $sem(⟨ t, s ⟩) = ⟨ sem(t), sem(s) ⟩$, $sem(pi_i t) = pi_i compose sem(t)$,
  $sem(lambda x : A. t) = cur (sem(Gamma\, x attach(:, br: oo) A tack t))$,
  $sem(t space s) = ev compose ⟨ sem(t), sem(s) ⟩$,

  $sem(ret t) = eta compose sem(t)$,
  $sem("let" x <- M "in" N) = sem(N)^dagger compose "st" compose ⟨ "id", sem(M) ⟩$,
  $sem(smp_mu) = mu quad ("constant")$, $sem(scr(phi)) = sem(phi) quad (Omega = T 1)$,
  $sem(nrm (M)) = "normalise" compose sem(M)$,
  $sem(t[s slash x]) = sem(t) compose ⟨ "id", sem(s) ⟩$,
  $sem(Phi[psi slash u]) = sem(Phi) compose ⟨ "id", cur (sem(psi)) ⟩$,
) <eq:term-sem>

#rem[
  In the last clause $Gamma\, x coo A tack psi "prop"$ may have free variables of
  $Gamma$: $sem(psi) : U sem(Gamma) times sem(A) -> Omega$ and
  $cur (sem(psi)) : U sem(Gamma) -> Omega^(sem(A))$ curries the $A$-argument. The
  simpler clause $cur (sem(psi) compose pi_2)$ is the special case of $psi$ closed.
]

// TODO: define cur, ev, etc.

Here $"st"$ is the strength and $(-)^dagger$ the Kleisli extension of $T$, so that in
kernel notation
$
  sem("let" x <- M "in" N)(g, V) = integral_(sem(A)) sem(M)(g, dif x) space sem(N)((g, x), V),
$
the composition of s-finite kernels of @staton2017commutative. The interpretation of
$scr(phi)$ is the formula itself, read as a measure on the one-point space:
$sem(scr(phi))(g) = sem(phi)(g) dot delta_ast$. Consequently
$sem(scr(phi) seq M) = sem(phi) dot sem(M)$ and, for $u : Prd A$,
$
  sem("let" x <- M "in" scr(u space x) seq ret x) = sem(M) act sem(u),
$
the density action: scoring is reweighting.

#definition([Normalisation])[
  $"normalise" : T X -> T X$ is
  $
    "normalise"(nu) := cases(
      nu slash nu(|X|) quad & "if" 0 < nu(|X|) < oo,
      0 & "otherwise (the zero measure)."
    )
  $
  It is a QBS morphism: on a random element $r |-> [alpha, k(r, -)]$ it returns
  $r |-> [alpha, k(r, -) act c(r)]$ with $c(r) := 1 slash k(r, RR)$ on the measurable set
  ${0 < k(r, RR) < oo}$ and $c(r) := 0$ elsewhere, which is an s-finite kernel by
  @vakar2026sfinite[Thm. 5(3)]. On a probability measure it is the identity.
] <def:normalise>

#proposition([Computations are s-finite kernels])[
  If all types in $Gamma$ and $A$ are first order (built from $1$, $RR$, $Omega$ and
  $times$), then $U sem(Gamma)$ and $sem(A)$ are standard Borel and
  $sem(Gamma tack M : Dst A) in Qbs(U sem(Gamma), T sem(A))$ is precisely an s-finite
  kernel $U sem(Gamma) kto sem(A)$ @vakar2026sfinite[Cor. 2]. On this fragment the
  semantics is that of @staton2017commutative; the monad $T$ extends it to higher types
  and to the predicate types $Prd A$ over which the logic quantifies.
]

= HQLL Logic



#definition([Integration operator])[
  For $X in "QBS"$ the *integration operator* is
  $
    I_X : T X times Omega^X --> Omega, quad quad
    I_X ([alpha, mu], space u) := integral_RR u(alpha(r)) space dif mu(r),
  $
  the integral of @def:sfinite; it is well defined on classes because two representatives
  with the same push-forward have the same integrals @vakar2026sfinite[Thm. 20]. Its
  value may be $oo$. For $f : X -> Y$ we have $I_Y (T(f)(nu), space v) = I_X (nu, space v compose f)$

  #align(center)[
    #commutative-diagram(
      node((0, 0), $T X times Omega^Y$),
      node((0, 1), $T Y times Omega^Y$),
      node((1, 0), $T X times Omega^X$),
      node((1, 1), $Omega$),
      arr((0, 0), (0, 1), $T(f) times "id"$),
      arr((0, 1), (1, 1), $I_Y$),
      arr((0, 0), (1, 0), $"id" times f^*$, label-pos: right),
      arr((1, 0), (1, 1), $I_X$, label-pos: right),
    )
  ]
] <def:integration>

// #v(5pt)
// #lemma([Integration Lemma])[
//   $I_X : cal(P) X times Omega^X -> Omega$ is well defined and a morphism of
//   quasi-Borel spaces, and it satisfies the naturality law
//   $I_Y (cal(P)(f)(nu), v) = I_X (nu, v compose f)$ for every $"QBS"$ morphism
//   $f : X -> Y$.
// ] <lem:integration>

// #proof[
//   *Step 1: well-definedness.* Every $u in Omega^X = "QBS"(X, Omega)$ is
//   $Sigma_(M_X)$-measurable: for Borel $U subset.eq Omega$ and any $alpha in M_X$,
//   $alpha^(-1)(u^(-1) U) = (u compose alpha)^(-1) U in Sigma_RR$ since
//   $u compose alpha$ is Borel, so $u^(-1) U in Sigma_(M_X)$ by definition of the
//   induced $sigma$-algebra. If $[alpha, mu] = [alpha', mu']$, i.e.
//   $alpha_* mu = alpha'_* mu'$ on $Sigma_(M_X)$, then by the change-of-variables
//   formula for pushforwards of $[0,oo]$-valued measurable maps,
//   $
//     integral_RR u(alpha(r)) dif mu(r)
//     = integral_X u thin dif (alpha_* mu)
//     = integral_X u thin dif (alpha'_* mu')
//     = integral_RR u(alpha'(r)) dif mu'(r),
//   $
//   so $I_X (nu, u)$ does not depend on the representative of $nu$; the integral
//   always exists in $[0,oo]$.

//   *Step 2: reduction along a random element.* Let
//   $gamma = ⟨gamma_1, gamma_2⟩ in M_(cal(P) X times Omega^X)$, so
//   $gamma_1 in M_(cal(P) X)$ and $gamma_2 in M_(Omega^X)$. By the definition of
//   $M_(cal(P)(X))$ there are $alpha in M_X$ and $g in Meas(RR, G(RR))$ with
//   $gamma_1 (s) = (alpha, g(s))$ for all $s$; by cartesian closure,
//   $h := "uncurry"(gamma_2) : RR times X -> Omega$ is a $"QBS"$ morphism. Hence
//   $
//     k := h compose ("id"_RR times alpha) : RR times RR -> [0, oo]
//   $
//   is a $"QBS"$ morphism between standard Borel spaces, i.e. a Borel map
//   @qbs, and
//   $
//     (I_X compose gamma)(s)
//     = integral_RR gamma_2 (s)(alpha(r)) dif g(s)(r)
//     = integral_RR k(s, r) dif g(s)(r).
//   $

//   *Step 3: the parametric integral is Borel.* Define
//   $J : RR times G(RR) -> [0,oo]$ by $J(s, nu) := integral_RR k(s,r) dif nu(r)$.
//   For $k = bb(1)_B$ with $B in Sigma_(RR times RR)$, $J(s, nu) = nu(B_s)$ where
//   $B_s$ is the section: the class of $B$ for which $(s, nu) |-> nu(B_s)$ is Borel
//   contains the rectangles $B_1 times B_2$ (the map is
//   $bb(1)_(B_1)(s) dot nu(B_2)$, Borel because evaluation
//   $nu |-> nu(B_2)$ generates the $sigma$-algebra of $G(RR)$), and is a
//   $lambda$-system by $sigma$-additivity and closure of Borel maps under pointwise
//   limits; by the $pi$--$lambda$ theorem it contains all of
//   $Sigma_(RR times RR)$. Linearity extends Borel-ness of $J$ to simple $k$, and
//   monotone convergence to arbitrary Borel $k >= 0$ via simple approximations
//   $k_n arrow.tr k$. Finally $s |-> (s, g(s))$ is Borel, so
//   $I_X compose gamma = J compose ⟨"id", g⟩$ is Borel, i.e.
//   $I_X compose gamma in M_Omega$. As $gamma$ was arbitrary, $I_X$ is a $"QBS"$
//   morphism.

//   *Naturality.* $cal(P)(f)[alpha, mu] = [f compose alpha, mu]$, so
//   $I_Y (cal(P)(f)(nu), v) = integral_RR v(f(alpha(r))) dif mu(r)
//   = I_X (nu, v compose f)$.
// ]

#v(5pt)
#lemma([Integration Lemma])[
  $I_X$ is a morphism of quasi-Borel spaces.
  #proof[
    A random element of $T X times Omega^X$ is a pair
    $r |-> ([alpha, k(r, -)], space u(r, -))$ with $k : RR kto RR$ an s-finite kernel
    and $u in Qbs(RR times X, Omega)$ (cartesian closure). Then
    $
      r |-> I_X ([alpha, k(r, -)], u(r, -)) = integral_RR u(r, alpha(r')) space k(r, dif r')
      = (k act h)(r, RR),
    $
    where $h(r, r') := u(r, alpha(r'))$ is measurable on $RR^2$ because
    $Qbs(RR^2, Omega) = Meas(RR^2, [0,oo])$.
    By @vakar2026sfinite[Thm. 5(3)], $k act h$ is again an s-finite kernel, in particular
    measurable in $r$; so the composite lies in $M_Omega$. Equivalently, $I_X$ is the
    uncurrying of the embedding $T X arrow.r.hook Omega^(Omega^X)$ through which $T$
    inherits its monad structure @vakar2026sfinite[Thm. 19].
  ]
] <lem:integration>

#remark[
  The integration operator is definable in the computational language: by the density
  action, $I_X (nu, u) = (nu act u)(|X|) = sem("let" x <- nu "in" scr(u space x))$, an
  element of $T 1 = Omega$. So quantifying is running a program: the soft quantifiers
  below are $hat(exists)^p (nu, u) = ("let" x <- nu "in" scr((u space x)^p))^(1 slash p)$
  and dually for $hat(forall)^p$.
]

#v(5pt)
#definition([Soft quantifiers])[
  For $p in (0, oo)$, writing $(-)^(plus.minus p)$ for post-composition with
  $t |-> t^(plus.minus p)$ on $[0,oo]$:
  $
    hat(exists)^p (nu, u) := (I_X (nu, space u^p))^(1 slash p), quad quad
    hat(forall)^p (nu, u) := (I_X (nu, space u^(-p)))^(-1 slash p),
  $
  both morphisms $T X times Omega^X -> Omega$, since $(-)^(plus.minus p)$
  is Borel on $[0,oo]$ and $I_X$ is a morphism. With the conventions
  $hat(exists)^oo (nu, u) := esssup_nu u$ and $hat(forall)^oo (nu, u) := essinf_nu u$,
  the definitions make sense for every s-finite $nu$: they are the $L^p (nu)$ norm of
  $u$ and the reciprocal $L^p (nu)$ norm of $u^*$, and are means only when $nu$ is a
  probability measure.

  #align(center)[
    #commutative-diagram(
      node((0, 0), $T X times Omega^X$),
      node((0, 1), $T X times Omega^X$),
      node((1, 1), $Omega$),
      node((1, 0), $Omega$),
      arr((0, 0), (0, 1), $"id" times (-)^(-p)$),
      arr((0, 1), (1, 1), $I_X$),
      arr((1, 1), (1, 0), $(-)^(-1 slash p)$, label-pos: right),
      arr((0, 0), (1, 0), $hat(forall)^p$, label-pos: right),
    )]
]

#remark[
  $I_X (nu, u)$ is the expectation $EE_(x tilde nu)[u(x)]$ when $nu$ is a probability
  measure, and we write the latter as sugar for the former
  $EE_(x tilde nu)[e] := I_X (nu, lambda x. e)$ in that case.
]

#lemma([Mass scaling])[
  Let $nu in T X$ with $0 < nu(|X|) < oo$ and $overline(nu) := "normalise"(nu)$. For
  $p in (0, oo)$,
  $
    hat(exists)^p (nu, u) = nu(|X|)^(1 slash p) ⊗ hat(exists)^p (overline(nu), u),
    quad quad
    hat(forall)^p (nu, u) = nu(|X|)^(-1 slash p) ⊗ hat(forall)^p (overline(nu), u).
  $
  In particular $hat(forall)^p (nu, 1) = nu(|X|)^(-1 slash p)$: the constant $1$ is no
  longer a unit for $hat(forall)^p$ under an unnormalised measure, and
  $hat(forall)^p (nu, 1) = 0$ when $nu(|X|) = oo$. At $p = oo$ the mass is invisible:
  $hat(forall)^oo (nu, 1) = 1$ for every $nu eq.not 0$. Consequently the reflexivity of
  graded entailment, $1 <= hat(forall)^p (omega, phi multimap phi) = omega(|A|)^(-1 slash p)$
  for a slot $A_omega$ at grade $p < oo$, holds exactly over sub-probability domains
  $omega(|A|) <= 1$; hard entailment ($p = oo$) is unaffected. A sequent calculus over
  s-finite domains must therefore restrict soft grades to sub-probability slots, normalise
  the slot ($A_(nrm omega)$), or record the masses $omega(|A|)$ in the grade.
  #proof[
    $integral u^(plus.minus p) dif nu = nu(|X|) integral u^(plus.minus p) dif overline(nu)$,
    then take the $plus.minus 1 slash p$ power.
  ]
] <lem:mass>

#example([Improper prior, scoring and normalisation])[
  Let $Leb$ be Lebesgue measure on $RR$: an s-finite measure of infinite mass, so
  $RR_Leb "dom"$ although $Leb$ is not a probability distribution. With the formula
  $phi := lambda x : RR. space e^(-x^2 slash 2)$ form the program
  $
    M := "let" x <- smp_(Leb) "in" scr(phi space x) ; ret x quad : quad Dst RR,
  $
  whose denotation is the density action $sem(M) = Leb act sem(phi)$: the unnormalised
  Gaussian, of total mass $sqrt(2 pi)$. Then $sem(nrm(M)) = cal(N)(0, 1)$, and all three of
  $RR_Leb$, $RR_M$ and $RR_(nrm(M))$ are domain types. For $psi := lambda x : RR. abs(x)$
  the same soft quantifier takes three different values:
  $
    exists^2 (x : RR_Leb). psi space x &= (integral_RR x^2 dif x)^(1 slash 2) = oo, \
    exists^2 (x : RR_M). psi space x &= (integral_RR x^2 e^(-x^2 slash 2) dif x)^(1 slash 2)
      = (sqrt(2 pi))^(1 slash 2) = (2 pi)^(1 slash 4) approx 1.583, \
    exists^2 (x : RR_(nrm(M))). psi space x &= (EE_(x tilde cal(N)(0,1))[x^2])^(1 slash 2) = 1,
  $
  in accordance with @lem:mass: $(2 pi)^(1 slash 4) = (sqrt(2 pi))^(1 slash 2) dot 1$.
  Dually, $forall^1 (x : RR_Leb). 1 = Leb(RR)^(-1) = 0$ while
  $forall^1 (x : RR_M). 1 = (sqrt(2 pi))^(-1) approx 0.399$ and
  $forall^1 (x : RR_(nrm(M))). 1 = 1$: under an improper prior nothing is universally
  valid at a finite grade, and the mass of the posterior is what $nrm$ removes. None of
  these domains is available in the probability version, where $smp_(Leb)$ and $scr$ are
  not expressible.
]


== Operators semantics

Each clause below interprets a proposition $Gamma tack phi "prop"$ as a
morphism $U sem(Gamma) -> Omega$, and the operations on the right-hand sides act
*pointwise*. In particular the three constants denote the corresponding
*constant morphisms*, $sem(Gamma tack 0 : Omega) = lambda arrow(z). 0$ and
likewise for $1$ and $oo$; we abbreviate these to $sem(0) = 0$ etc. Every
right-hand side is a $"QBS"$ morphism $Omega times Omega -> Omega$ (resp.
$Omega -> Omega$), so each fiber $Omega^X$ is closed under the whole signature
and reindexing commutes with it strictly.

#grid(
  columns: (1fr, 1fr),
  align: center,
  row-gutter: 10pt,
  $sem(0) = 0$, $sem(1) = 1$,
  $sem(oo) = oo$, $sem(psi ⊗ phi) = sem(psi) sem(phi)$,
  $sem(psi ⊗^* phi) = sem(psi) sem(phi)$, $sem(psi multimap phi) = sem(phi) slash sem(psi)$,
  $sem(psi^*) = 1 slash sem(psi)$, $sem(psi^p) = sem(psi)^p$,
  $sem(psi ⊕^p phi) = (sem(psi)^p + sem(phi)^p)^(1 slash p)$,
  $sem(psi ⊕^(-p) phi) = (sem(psi)^(-p) + sem(phi)^(-p))^(-1 slash p)$,

  $sem(exists^p (x : A_omega). phi) = (I_X (sem(omega), sem(phi)^p))^(1 slash p)$,
  $sem(forall^p (x : A_omega). phi) = (I_X (sem(omega), sem(phi)^(-p)))^(-1 slash p)$,
) <eq:ops>

Unwinding $I_X$ with $sem(omega) = [alpha, mu]$, $mu$ s-finite on $RR$:

$
  sem(forall^p (x : A_omega). phi)(g)
  = (integral_RR sem(phi)(g, alpha(r))^(-p) dif mu(r))^(-1 slash p)
  = integral^(-p)_(x in sem(A)) sem(phi)(g, x) dif omega,
$ <eq:unwind>

$
  sem(forall^p (u : (Prd A)_pi). Phi)(g)
  = integral^(-p)_(u in Omega^(sem(A))) sem(Phi)(g, u) dif pi.
$ <eq:ho>

Dually, $integral^(p)$ (positive exponent) abbreviates the $hat(exists)^p$
integral: $integral^(p)_(x in sem(A)) sem(phi)(g, x) dif omega =
(integral sem(phi)(g, x)^p dif omega)^(1 slash p)$.


#bibliography("bibliography.bib")
