#import "@preview/polylux:0.4.0": *
#import "@preview/metropolis-polylux:0.1.0" as metropolis
#import metropolis: focus, new-section
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#show: metropolis.setup

#let blue = rgb("#153e9f")
#let purple = rgb("#6a35a3")
#let teal = rgb("#087a78")
#let soft-blue = rgb("#f3f7ff")
#let soft-purple = rgb("#f7f2ff")
#let soft-teal = rgb("#effafa")
#let warn = rgb("#b71919")

// Monadic bind: a single relation with the glyphs packed tightly,
// instead of the `>>=` shorthand which renders as `≫=`.
#let bind = math.class("relation", math.upright(">>="))

// λ*-FQLL* helpers: sensitivity colon, graded turnstile, soft connectives.
#let tcol(r) = $attach(:, tr: #r)$
#let ent(p) = $attach(tack.r, br: #p)$
#let psum(s) = $attach(plus.o, tr: #s)$
#let fa(s) = $attach(forall, tr: #s)$
#let ex(s) = $attach(exists, tr: #s)$

#let card(title, body, fill: soft-blue, color: blue) = block(
  width: 100%,
  fill: fill,
  stroke: 0.8pt + color,
  radius: 6pt,
  inset: 9pt,
)[
  #text(fill: color, weight: "bold")[#title]
  #v(0.35em)
  #body
]

#let smallnote(body, color: teal) = block(
  width: 100%,
  fill: rgb("#ffffff"),
  stroke: 0.5pt + color,
  radius: 5pt,
  inset: 7pt,
)[#body]

#slide[
  #set page(header: none, footer: none, margin: 3em)

  #text(size: 1.25em)[
    *Higher-Order QLL with QBS*
  ]

  #metropolis.divider

  #set text(size: .82em, weight: "light")
]

#slide[
  = The category QBS

  A quasi-Borel space is a pair
  $
    X = (X, M_X)
  $
  where $M_X subset.eq (RR -> X)$ is the set of admissible random elements.

  #v(0.5em)

  - *Constants:* Every map $RR -> X$ lies in $M_X$.
  - *Reparametrization:* If $alpha in M_X$ and $f: RR -> RR$ is measurable, then $alpha compose f in M_X$.
]

#slide[
  = The morphism in QBS

  A QBS morphism $h: X -> Y$ is a function such that:
  $
    alpha in M_X ==> h compose alpha in M_Y.
  $

]

#slide[
  = Example of QBS: a coin

  The coin outcomes form the two-point QBS $C = ({H, T}, M_C)$.

  #v(0.4em)

  Since $C$ is countable, a random element $alpha in M_C$ is just a Borel-measurable
  map $alpha: RR -> {H, T}$, i.e. a Borel partition $RR = A_H union.sq A_T$ with
  $alpha = H$ on $A_H$ and $alpha = T$ on $A_T$.

  #v(0.4em)

  For instance, splitting $RR$ at $0$:
  $
    alpha(r) = cases(H & "if " r < 0, T & "if " r >= 0).
  $
  The preimages are Borel, so $alpha in M_C$ is admissible.
]





#slide[
  = QBS is CCC

  QBS is cartesian closed: it has an exponential object $Y^X$ for all $X, Y$,
  so we can form function types.

  #v(0.4em)

  - *Carrier:* its points are the QBS morphisms,
    $
      Y^X = "QBS"(X, Y).
    $
  - *Random elements:* $alpha: RR -> Y^X$ lies in $M_(Y^X)$ exactly when its uncurrying
    $
      hat(alpha): RR times X -> Y, quad hat(alpha)(r, x) = alpha(r)(x)
    $
    is a QBS morphism.

  #v(0.4em)

  This gives the natural bijection $"QBS"(Z times X, Y) tilde.equiv "QBS"(Z, Y^X)$ (curry / uncurry).


]


#slide[
  = The probability monad P

  Measures enter through a strong monad $P$ on QBS.

  A measure on $X$ is presented by a
  random element together with a law on the parameter line:
  $
    P(X) = { (alpha, mu) : alpha in M_X, mu in G(RR) },
  $
  where $G(RR)$ are the probability measures on $RR$.
]

#slide[
  = From QBS to QProb

  QProb equips QBS types with a chosen probability law:

  - *Objects:*  $(X, rho_X)$ where $X$ is a QBS and $rho_X in P(X)$ is a probability measure on it.
  - *Morphisms:*  $f: (X, rho_X) -> (Y, rho_Y)$ is a QBS morphism $f: X -> Y$ such that $P(f)(rho_X) <= rho_Y$.


  #smallnote[
    - QProb is a category of *probabilistic spaces* that supports higher-order functions because its object are QBS.

    - QProb is a monoidal category but not CCC.
  ]

]

#slide[
  = QProb example: a fair coin

  Equip a coin QBS $C$ with the law from the monad $P$:
  $
    rho_C = (alpha, "Unif"[0,1]) = 1/2 delta_H + 1/2 delta_T in P(C).
  $
  The object $(C, rho_C)$ is a fair coin in QProb.
]

#slide[
  = The three monad laws

  For $p in P(X)$, $f: X -> P(Y)$, $g: Y -> P(Z)$:

  #v(0.5em)

  - *Left unit:*
    $eta_X (x) bind f := f(x)$

  - *Right unit:* $ p bind eta_X := p $

  - *Associativity:*
    $
      (p bind f) bind g := p bind (lambda x. thin f(x) bind g).
    $
    Sequencing is order-insensitive in how it is bracketed.


  Moreover $P$ is *strong* and *commutative*: the order of independent samples does
  not matter, which is what gives well-defined product measures $rho_X times.o rho_Y$.
]

#slide[
  = QProb higher-order predicates

  Because QBS is cartesian closed, a *function type is itself an object*, so we
  can put a law on it and quantify over it. Take the strategy type:
  $
    S = [0, infinity]^C = "QBS"(C, [0, infinity])
  $
  A point of $S$ is a predicate $s: C -> [0, infinity]$ on coin outcomes:
  #v(0.4em)

  Equip $S$ with a law from the monad $P$ (a *random strategy*):
  $
    rho_S = 1/2 delta_(s_("safe")) + 1/2 delta_(s_("risky")) in P(S),
    quad s_("safe") = (3,3), thin s_("risky") = (8,1).
  $
]

#slide[
  = Hyperdoctrines and the functor L

  $
    L_("QBS"): "QProb"^"op" -> (plus.o^*, times.o)"-Prd"
  $

  // #v(.4em)

  - *On objects:* $(X, rho_X) |-> "QBS"(X, W)$, the quantale of $W$-valued
    predicates, $W = [0,infinity]_(plus.o^*)$ as a QBS.
  - *On morphisms:* $(f: (X,rho_X) -> (Y, rho_Y)) |-> f^* = (-) compose f :
    "QBS"(Y, W) -> "QBS"(X, W)$ (reindexing).

  For $phi, psi: X -> W$, define graded entailment by
  $
    phi attach(⊢, tr: rho_X, br: p) psi
    := integral_X^(-p) (phi multimap psi) space d rho_X.
  $

  #smallnote[
    - φ(x) is the local logical weight at x.
    - $rho_X$ tells us how to average those local weights over the context.
  ]
]

#slide[
  = Graded entailment, unrolled

  Abstract form in the fibre $L(X, rho_X)$:
  $
    phi attach(tack.r.short, tr: rho_X, br: p) psi
    := integral_(x in X)^(-p) (phi multimap psi)(x) dif rho_X (x).
  $

  Unfold the representative $rho_X = (alpha, mu)$ so integration reduces to $RR$:
  $
    = integral_(r in RR)^(-p) (phi multimap psi)(alpha(r)) dif mu(r).
  $

  Unfold the harmonic $p$-mean and $multimap$:
  $
    = (integral_(r in RR) (frac(psi, phi) dot alpha(r))^(-p) dif mu(r))^(-1/p)
  $
]


#slide[
  = The exponential object on a finite QBS
  For $2 = {0,1}$ and $W = [0,infinity]$:
  $
    W^2 = "QBS"(2, W) tilde.equiv [0,infinity] times.o [0,infinity],\
    quad phi <-> (phi(0), phi(1)).
  $

  Random elements are random functions:
  $
    alpha(r) = (a(r), b(r)), quad a, b colon RR -> [0,infinity] "measurable".
  $
]

#slide[
  = A random predicate is sampled from $RR$

  A measure on the predicate $[0,infinity]^X$ is $rho = (alpha, mu)$ with
  $mu in G(RR)$ and $alpha in M_([0,infinity]^X)$.
  $
    alpha in M_([0,infinity]^X)
    quad <==> quad
    hat(alpha) := "uncurry"(alpha) colon RR times X -> [0,infinity]""
  $

  So $alpha(r) = hat(alpha)(r, -) colon X -> [0,infinity]$ is a family of predicates indexed by $RR$.

  #v(0.5em)

  Integration of a higher-order $Phi colon [0,infinity]^X -> [0,infinity]$ collapses to $RR$:
  $
    integral_([0,infinity]^X) Phi dif rho
    = integral_RR Phi(alpha(r)) dif mu(r)
    = integral_RR Phi(hat(alpha)(r, -)) dif mu(r).
  $
]

// #slide[
//   = Example
//   $X = {0,1}$ and $mu = cal(N)(0,1)$

//   *Curried family* $hat(alpha)(r, x) = e^(r x)$, random element $alpha colon RR -> [0,infinity]^X$, $#h(0.3em) alpha(r) = (1, e^r)$.

//   Pick $rho = (alpha, mu) in P([0,infinity]^X)$ i.e output the predicate $(1, e^r)$.

//   *Integrate* $Phi(phi)$ for $phi(1)$ collapses to $RR$ as:
//   $
//     integral_([0,infinity]^X) Phi dif rho
//     = integral_(r ∈ RR) e^r dif cal(N)(0,1)(r)
//     = e^(1 slash 2) approx 1.65.
//   $

// ]

#slide[
  = Example: a random distribution
  $X = {0,1}$ and $mu = cal(N)(0,1)$ and $P(X):$

  - $hat(alpha)(r) = sigma(r) delta_0 + (1 - sigma(r)) delta_1$ with $sigma(r) = 1 / (1 + e^(-r)) in (0,1)$.

  random element $alpha colon RR -> P(X)$, each $alpha(r)$ a
  distribution on $X$

  *Integrate* $Phi(nu) = nu({0})$ — collapses to $RR$:
  $
    integral_(P(X)) Phi dif rho
    = integral_RR sigma(r) dif cal(N)(0,1)(r)
    = 1 / 2.
  $
]

#slide[
  = Quantifiers as graded adjoints

  Along a projection $pi_X: X times Y -> X$, reindexing $pi_X^*$ has $p$-graded adjoints:
  $
    (exists^p_Y phi)(x) = integral_Y^p phi(x, y) space d rho_Y
    quad quad
    (forall^p_Y phi)(x) = integral_Y^(-p) phi(x, y) space d rho_Y
  $

  #v(0.9em)
  Sequent:

  #align(center, stack(
    dir: ltr,
    spacing: 4em,
    prooftree(rule(
      name: $exists^p$,
      $x :^q X, thin y :^p Y | Gamma attach(⊢, tr: rho_X times.o rho_Y) theta$,
      $x :^q X | Gamma attach(⊢, tr: rho_X) exists^p y . thin theta$,
    )),
    prooftree(rule(
      name: $forall^p$,
      $x :^q X, thin y :^p Y | Gamma ⊢ theta$,
      $x :^q X | Gamma ⊢ forall^p y . thin theta$,
    )),
  ))

  #v(0.7em)

  #align(center, text(size: .8em, fill: teal)[
    $exists^p tack.l pi_X^* tack.l forall^p$ #h(1.5em) ($y$ not free in $Gamma$)
  ])
]

#slide[
  = Leibniz equality

  Higher-order, quantifying over the predicate space $W^X = "QBS"(X, W)$:
  $
    thin forall^infinity phi : W^X . space phi(x) multimap.double phi(y).
  $

  #v(0.9em)

  #align(center, stack(
    dir: ltr,
    spacing: 4em,
    prooftree(rule(
      name: [refl],
      $Gamma ⊢ Delta$,
      $Gamma ⊢ r(x = x), Delta$,
    )),
    prooftree(rule(
      name: [subst],
      $Gamma, x :^r A ⊢ phi$,
      $Delta ⊢ u, v : A$,
      $Gamma, r Delta | r(u = v) ⊢ phi[u] = phi[v]$,
    )),
  ))


]

#slide[
  = Leibniz equality

  Two points are equal when *every* predicate cannot tell them apart:
  $
    x =_X y thin := thin forall phi : W^X . space phi(x) multimap.double phi(y).
  $
  Quantifying over the predicate space $W^X = "QBS"(X, W)$ — an object only because QBS is CCC.

  #v(0.9em)

  #align(center, stack(
    dir: ltr,
    spacing: 1em,
    prooftree(rule(
      name: [refl],
      $x attach(:, tr: r) X | Gamma ⊢ Delta$,
      $x attach(:, tr: r) X | Gamma ⊢ (x = x), Delta$,
    )),
    prooftree(rule(
      name: [subst],
      $x, y attach(:, tr: r) X | Gamma ⊢ (x = y)$,
      $x, y attach(:, tr: r) X | Delta ⊢ phi(x)$,
      $x, y attach(:, tr: r) X | Gamma, Delta ⊢ phi(y)$,
    )),
  ))
]


#slide[
  = Equality recovers distance

  On $RR$ with $W = [0, infinity]$, restrict to $1$-Lipschitz predicates
  $phi$ (the natural probes). Equality unfolds as
  $
    (x =_RR y) = forall phi in "Lip"_1 . space phi(x) multimap.double phi(y).
  $

  with $phi = |dot - y|$ is $1$-Lipschitz with $phi(y) = 0$
  $
    (x =_RR y) = sup_(phi in "Lip"_1) (phi(x) multimap.double phi(y)) = |x - y|.
  $
]




#slide[
  #set page(header: none, footer: none, margin: 3em)

  #text(size: 1.25em)[
    $lambda$*-FQLL*
  ]

  #metropolis.divider

  #set text(size: .82em, weight: "light")

  - the category *CExtMet* and its closed monoidal structure (i.e. SLTC),
  - FQLL as an internal logic
]

#slide[
  = The category CExtMet

  An *extended metric space* $(X, d_X)$ with
  $
    d_X : X times X -> [0, infinity].
  $

  #v(0.4em)

  - *Morphisms:* _short maps_ (non-expansive),
    $
      d_Y (phi(x), phi(x')) <= d_X (x, x').
    $
  - *Complete:* every Cauchy sequence converges.
]

#slide[
  = CExtMet is closed monoidal

  $("CExtMet", times.o, bold(1))$ is symmetric monoidal closed:

  - *Tensor:* additive distance $(X times.o Y, thin d_X + d_Y)$.
  - *Internal hom:* short maps $X multimap Y$ with sup distance
    $
      d(phi, psi) = sup_(x in X) d_Y (phi(x), psi(x)).
    $

  #v(0.4em)
  $
    "CExtMet"(X times.o Y, Z) tilde.equiv "CExtMet"(X, Y multimap Z).
  $
]

#slide[
  = Scaling = sensitivity

  The scaling functor $r(-)$ rescales distance, $d_(r X) = r dot d_X$, so
  $
    "short " r X -> Y quad <==> quad r"-Lipschitz " X -> Y.
  $

  - $0 X = bold(1)$: a $0$-sensitive variable is *discarded*.
  - $infinity X$: the $infinity$-separated space is *copyable* ($infinity + infinity = infinity$).

]

#slide[
  = Guarded recursion

  No general $"fix"$ — but on *complete* objects Banach gives one for *contractions* ($p < 1$):
  $
    "fix" : (p Y multimap Y) -> (1 - p) Y.
  $

  #v(0.3em)

  A non-expansive $p Y -> Y$ is a $p$-contraction $Y -> Y$
]

#slide[
  = The Wasserstein monad W

  Probability enters through $cal(W)_p$ on *CExtMet* ($p >= 1$):

  - $cal(W)_p X$: Radon measures on $X$ with the *Wasserstein distance*;
  - unit $delta_X$ (Dirac)

  #v(0.4em)

  Algebraically the *free interpolative barycentric algebra*: convex choice
  $
    mu amp.inv_p nu = p thin mu + (1 - p) thin nu.
  $
]

#slide[
  = $lambda$*-FQLL*: the calculus

  A simply-typed $lambda$-calculus over *CExtMet*, with probability and recursion:
  $
    M, N ::= & x | () | lambda x. M | M thin N | chevron.l M, N chevron.r | pi_i M | (M, N) | "let" (x,y) = M "in" N \
           | & "inl" M | "inr" M | "case" M ... | delta M | M amp.inv_p N | "fix" x. M
  $

  Types:
  $
    A, B ::= NN | 1 | A times B | A + B | A attach(times.o, bl: r, br: s) B | A multimap_r B | cal(W) A.
  $


]

#slide[
  = Typing tracks sensitivity

  Variables carry a sensitivity index $x tcol(r) A$; application *scales* the argument context.

  #v(0.6em)

  #align(center, stack(
    dir: ltr,
    spacing: 3em,
    prooftree(rule(
      name: [(ABS)],
      $Γ, x tcol(r) A ⊢ t : B$,
      $Γ ⊢ λ x. t : A multimap_r B$,
    )),
    prooftree(rule(
      name: [(APP)],
      $Γ ⊢ t : A multimap_r B$,
      $Γ' ⊢ u : A$,
      $Γ ⧺ r Γ' ⊢ t thin u : B$,
    )),
  ))

  #v(0.9em)

  #align(center, stack(
    dir: ltr,
    spacing: 3em,
    prooftree(rule(
      name: [($amp.inv_p$)],
      $Γ ⊢ t : cal(W) A$,
      $Γ' ⊢ u : cal(W) A$,
      $p Γ ⧺ (1-p) Γ' ⊢ t amp.inv_p u : cal(W) A$,
    )),
    prooftree(rule(
      name: [(FIX)],
      $(1-r) Γ, x tcol(r) A ⊢ t : A$,
      $Γ ⊢ "fix" x. t : A$,
    )),
  ))
]

#slide[
  = The inner logic Prop

  Predicates are terms of type $"Prop" = [0, infinity]$:
  $
    "Prop" = ([0, infinity], <=, times.o, times.o^*, multimap, (-)^*, plus.o^s, plus.o^(-s), exists^s, forall^s).
  $


  #smallnote[
    Softness $s$ is a *grade on entailment*, not on the typing judgement.
  ]
]

#slide[
  = Graded entailment

  $
    Δ thin | thin Ψ ent(p) φ
    quad "valid when" quad
    1 <= integral_x^(-p) ((times.o.big Ψ) multimap φ).
  $
  The grade $p$ is the exponent of a harmonic $p$-mean; $p = infinity$ is *hard* entailment.


  #align(center, stack(
    dir: ltr,
    spacing: 3em,
    prooftree(rule(name: [(ASS)], $Δ | Ψ, φ ent(oo) φ$)),
    prooftree(rule(
      name: [(CUT)],
      $Δ | Ψ ent(p) φ$,
      $Δ | Φ, φ ent(q) χ$,
      $Δ | Φ, Ψ ent(p plus.o^* q) χ$,
    )),
  ))
]

#slide[
  = Example: robustness of a NN

  For $cal(N) : RR^m -> RR^n$, $epsilon$-$delta$-robustness is a single predicate:
  $
    forall x. space |x - v| <= epsilon space multimap space |cal(N)(x) - cal(N)(v)| <= delta.
  $
]
