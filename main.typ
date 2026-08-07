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
#let Dst = math.op("Dist")
#let Qbs = math.op("QBS")
#let Meas = math.op("Meas")
#let ev = math.op("ev")
#let cur = math.op("cur")
#let esssup = math.op("ess sup")
#let essinf = math.op("ess inf")
#let ctx = math.op("ctx")
#let ty = math.op("type")
#let qdom = math.op("q-dom")
#let ret = math.op("return")
#let smp = math.op("sample")
#let nrm = math.op("norm")
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
  [$a multimap b = a^* ⊗^* b = b slash a$],
  [---],
  [$a ⊕^p b = (a^p + b^p)^(1 slash p)$, #h(0.4em) $a ⊕^(-p) b = (a^(-p) + b^(-p))^(-1 slash p)$],
  [$0$ / $oo$],
)

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
Regular type $A$ or $RR$ are interpreted as QBS without measure associated and
$A_omega$ is interpreted as QBS with the measure $omega: "Dist" A$ associated.
The sort separation between $A$ and $A_omega$  is what preserves cartesian closure i.e
$A_omega -> B$, $"Dist" A_omega$ and $(A_omega)_omega'$ are not well-formed types , so no exponential of a measured object is ever demanded.


===== Terms

$
     t, s & ::= x mid(|) ast mid(|) ⟨ t\, s ⟩
            mid(|) pi_1 t mid(|) pi_2 t mid(|) lambda x : A. t mid(|) t space s
            mid(|) c_Omega
            mid(|) hat(forall)^p (t\, s) mid(|) hat(exists)^p (t\, s) \
     M, N & ::= ret t mid(|) "let" x <- M "in" N
            mid(|) smp_cal(D) mid(|) nrm (M) \
  c_Omega & ::= 0 mid(|) 1 mid(|) oo mid(|) ⊗
            mid(|) ⊗^* mid(|) multimap mid(|) (-)^*
            mid(|) ⊕^p mid(|) ⊕^(-p) mid(|) (-)^p
$

#v(1em)

Arities:
- $⊗, ⊗^*, multimap, ⊕^(plus.minus p) : Omega times Omega -> Omega$;
- $(-)^*, (-)^p : Omega -> Omega$;
- $hat(forall)^p, hat(exists)^p : Dst A times Prd A -> Omega$.


#definition[
  - $"Pred" A ≔ A -> Omega$
  - $"Pred"^2 A ≔ ("Pred" A) -> Omega$
  - $forall^p (x : A_omega). phi ≔ hat(forall)^p (omega\, lambda x : A. phi),$
  - $exists^p (x : A_omega). phi ≔ hat(exists)^p (omega\, lambda x : A. phi),$
]


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
)

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
    name: [Var],
    $Gamma\, x cp A \, Gamma' tack x : A$,
  )),

  prooftree(rule(name: [Unit], $Gamma ctx$, $Gamma tack ast : 1$)),

  prooftree(rule(name: [Pair], $Gamma tack t : A$, $Gamma tack s : B$, $Gamma tack ⟨ t\, s ⟩ : A times B$)),
  prooftree(rule(name: [Proj], $Gamma tack t : A_1 times A_2$, $Gamma tack pi_i t : A_i$)),

  prooftree(rule(name: [Abs], $Gamma\, x coo A tack t : B$, $Gamma tack lambda x : A. t : A -> B$)),
  prooftree(rule(name: [App], $Gamma tack t : A -> B$, $Gamma tack s : A$, $Gamma tack t space s : B$)),

  prooftree(rule(name: [P-Abs], $Gamma\, x coo A tack phi "prop"$, $Gamma tack lambda x : A. phi : Prd A$)),
  prooftree(rule(name: [P-App], $Gamma tack u : Prd A$, $Gamma tack t : A$, $Gamma tack u space t "prop"$)),

  prooftree(rule(name: [Conn], $Gamma tack phi "prop"$, $Gamma tack psi "prop"$, $Gamma tack phi star psi "prop"$)),
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

#v(1em)

*Monadic rules:*

#v(1em)

#grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 7pt,
  row-gutter: 10pt,
  prooftree(rule(name: [Ret], $Gamma tack t : A$, $Gamma tack ret t : Dst A$)),
  prooftree(rule(name: [Smp], $cal(D) "std. Borel on" A$, $Gamma tack smp_cal(D) : Dst A$)),
  prooftree(rule(name: [Nrm], $Gamma tack M : Dst A$, $Gamma tack nrm (M) : Dst A$)),
)
#v(6pt)
#align(center, prooftree(rule(
  name: [Let],
  $Gamma tack M : Dst A$,
  $Gamma\, x coo A tack N : Dst B$,
  $Gamma tack "let" x <- M "in" N : Dst B$,
)))


= Semantics

== Preliminaries

#definition("QBS")[
  $X = (|X|, MM_X)$ is a *quasi-Borel space* with a underlying set $|X|$ and a set of functions $M_X subset.eq { RR -> |X|}$ closed under precomposition with Borel maps, containing constants, closed under countable Borel gluing. Given $f: X -> Y$ is a morphism if and only if $f compose alpha in M_Y$ for all $alpha in M_X$.
  - QBS is cartesian closed: $M_(Y^X) = { alpha mid(|) "uncurry"(alpha) in "QBS"(RR times X, Y)}$
  - QBS is well pointed
  - $Sigma_(M^X) = { U mid(|) forall alpha in M_X dot alpha^(-1) U in Sigma_RR}$ is the induced 𝜎-algebra.
  - The commutative monad  $"Dist" X = { [alpha, mu] mid(|) alpha in M_X, mu in "Prob"(RR) }$ modulo equal push-forward, with
    $
      integral_(X) f d[alpha, mu] = integral_(RR) f compose alpha d mu
    $
]

#definition("Probability measure")[
  A probability measure on a QBS $X$ is a pair $(alpha, mu)$ with $alpha in M_X$ and $mu$ a probability measure on $RR$, modulo equal push-forward. Then
  - $|cal(P)(X)| = { (alpha, mu) "probability measure on" (X, M_X) } slash ~$
  - $M_(cal(P)(X)) = { beta : RR -> cal(P)(X) mid(|) exists alpha in M_X, g in "Meas"(RR, G(RR)), forall r, beta(r) = (alpha, g(r)) }$
  so that $cal(P)(X) = (|cal(P)(X)|, M_(cal(P)(X)))$ is a QBS with the induced 𝜎-algebra $Sigma_(M^X)$.
]

We now define the category of measured quasi-Borel spaces that will interpret our domain types.

#definition($"Category QBS"_C$)[
  - Objects are $(|X|, M_X, omega_X)$, *measured quasi-Borel spaces*, written
    $(X, omega)$, with a QBS structure $(|X|, M_X)$ and a measure
    $omega_X in |cal(P)(X)|$.

  - Morphisms $f : (X, omega) -> (Y, rho)$ are QBS morphisms $f : X -> Y$ of
    *finite compression*, $C(f) < oo$. Writing
    $f_* omega := l_Y (cal(P)(f)(omega))$ for the induced measure on
    $Sigma_(M_Y)$, the *measure compression* of $f$ is
    $
      C(f) := ⋀ {B in [0,oo] mid(|) forall U in Sigma_(M_Y). space
        (f_* omega)(U) <= B dot rho(U)},
    $
    the least $B$ with $f_* omega <= B ⊗^* rho$. Equivalently
    $f_* omega << rho$ with $(dif f_* omega) slash (dif rho)$ essentially
    bounded by $C(f)$; and $C(f) = 1$ iff $f$ is measure-preserving.

  - Identities and composition are those of $"QBS"$. This is well defined
    because $C("id"_X) = 1$ and $C$ is lax,
    $ C(g compose f) <= C(f) dot C(g), $
    so finite compression is closed under composition.
]

#lemma([Monoidal product in $"QBS"_C$])[
  $
    (X, omega) ⊗ (Y, rho) := (X times Y, space omega ⊗ rho), quad quad
    I := (1, delta_ast),
  $
  where $omega ⊗ rho$ is the product measure, available because $cal(P)$ is
  commutative. The projections are morphisms with $C(pi_i) = 1$, since
  $(pi_1)_* (omega ⊗ rho) = omega$ and $(pi_2)_* (omega ⊗ rho) = rho$; so is
  $! : (X,omega) -> I$. Hence $⊗$ is *semicartesian monoidal*: unit terminal,
  projections everywhere.

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
  For $Delta_X = ⟨"id", "id"⟩$ one has
  $(Delta_X)_* omega (A times B) = omega(A inter B)$, so the compression
  condition at $A = B$ reads $omega(A) <= C dot omega(A)^2$. Hence
  $
    C(Delta_X) = ⋁ {1 slash omega(A) mid(|) A in Sigma_(M_X), space omega(A) > 0}
    = 1 slash inf{omega(A) mid(|) omega(A) > 0},
  $
  so $Delta_X$ is a morphism of $"QBS"_C$ iff $omega$ is *atomic with atoms
  bounded below*, and never when $omega$ is atomless.

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
  $sem(1) = 1$, $sem(RR) = RR$, $sem(Omega) = [0,oo]$,
  $sem(A times B) = sem(A) times sem(B)$, $sem(A -> B) = sem(B)^(sem(A))$, $sem(Dst A) = cal(P) sem(A)$,
  $sem(Prd A) = Omega^(sem(A))$,
) <eq:types>


Where $[0, oo]$ is standard Borel with $M_Omega = {"Borel" RR -> [0, oo] }$. We interpret domain types as the followings:

$
  sem(A_omega) := (sem(A), sem(omega)) in Qbs_C, quad quad
  sem(D ⊗ E) := sem(D) times sem(E) "with" omega_D ⊗ omega_E, quad quad
$ <eq:dom>

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
    together with, for each $j <= m$, a morphism
    $f_j : X_(rho(j)) -> Y_j$ of $"QBS"_C$ if the slot $Y_j$ is measured, and of
    $"QBS"$ otherwise.

  // - *Identities and composition.*
  //   $
  //     "id"_Gamma := ("id"_([n]), ("id"_(X_i))_(i <= n)), quad quad
  //     (rho, f) compose (rho', f') := (rho compose rho',
  //       space (f'_j compose f_(rho'(j)))_(j)).
  //   $
  //   Well defined because thinnings compose and each $"QBS"_C$-hom is closed
  //   under composition ($C$ is lax, $C("id") = 1$).

  - *Ordered products* by concatenation,
    $Gamma ; Delta := (X_1, p_1; dots; X_n, p_n; Z_1, r_1; dots; Z_k, r_k)$,.
  // with unit the empty list. Projections are the thinnings $(epsilon, ("id"))$;
  // there are *no diagonals* in general, so this is a semicartesian monoidal
  // structure and not a cartesian one.

  // - *Grading.* Each hom carries $K^(rho, f)_P := ⨂_(j <= m) K_(q_j) (f_j)$, and
  //   grades transport along thinnings by
  //   $rho_* (P)_i := and_(rho(j) = i) p_j$ (with $and emptyset = oo$).

  // - *Subcategories.* $"Ctx"_1$ is the wide sub-2-category on morphisms with
  //   $K^(rho,f)_P = 1$ (all components measure-preserving); $"Ctx"_oo$ is the
  //   full subcategory of one-slot unmeasured lists, and $"Ctx"_oo tilde.equiv "QBS"$.

  // #v(4pt)
  // The forgetful functor $U$ takes a context to its underlying space, and $iota$
  // embeds $"QBS"$ back as the unmeasured one-slot contexts:
  // $
  //   U((X_i, p_i)_(i <= n)) := V X_1 times dots.c times V X_n, quad quad
  //   iota(X) := (X, oo),
  // $

  // #align(center, commutative-diagram(
  //   node((0, 0), $"QBS"$),
  //   node((0, 1), $"Ctx"$),
  //   node((1, 1), $"QBS"$),
  //   arr((0, 0), (0, 1), $iota$, "inj"),
  //   arr((0, 1), (1, 1), $U$),
  //   arr((0, 0), (1, 1), $"id"$, label-pos: right),
  // ))

  // so $U compose iota = "id"_("QBS")$, and $U$ lands in a cartesian closed
  // category while $"Ctx"$ itself is not even cartesian.
]

#definition([Underlying-space functor])[
  We can retrieve the underlying space of a context by a functor
  $U : "Ctx" -> "QBS"$ and come back by $iota : "QBS" -> "Ctx"$ are given by
  - $U((X_i, p_i)_(i <= n)) := V X_1 times dots.c times V X_n$
  - $U(rho, f) := f_1 times dots.c times f_m$
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

  $sem(ret t) = eta compose sem(t)$, $sem("let" x <- M "in" N) = sem(N)^dagger compose ⟨ "id", sem(M) ⟩$,
  $sem(smp_cal(D)) = cal(D)$, $sem(nrm (M)) = "normalise"(sem(M))$,
  $sem(t[s slash x]) = sem(t) compose ⟨ "id", sem(s) ⟩$,
  $sem(Phi[psi slash u]) = sem(Phi) compose ⟨ "id", "cur"(sem(psi) compose pi_2 ) ⟩$,
) <eq:term-sem>


// TODO: define dagger , cur, etc.

= HQLL Logic



#definition([Integration operator])[
  For $X in "QBS"$ the *integration operator* is
  $
    I_X : cal(P) X times Omega^X --> Omega, quad quad
    I_X ([alpha, mu], space u) := integral_RR u(alpha(r)) space dif mu(r),
  $
  For $f : X -> Y$ we have $I_Y (cal(P)(f)(nu), space v) = I_X (nu, space v compose f)$

  #align(center)[
    #commutative-diagram(
      node((0, 0), $cal(P) X times Omega^Y$),
      node((0, 1), $cal(P) Y times Omega^Y$),
      node((1, 0), $cal(P) X times Omega^X$),
      node((1, 1), $Omega$),
      arr((0, 0), (0, 1), $cal(P)(f) times "id"$),
      arr((0, 1), (1, 1), $I_Y$),
      arr((0, 0), (1, 0), $"id" times f^*$, label-pos: right),
      arr((1, 0), (1, 1), $I_X$, label-pos: right),
    )
  ]
]

#v(5pt)
#lemma([Integration Lemma])[
  $I_X$ is a morphism of quasi-Borel spaces.
  #proof[TODO]
]

#v(5pt)
#definition([Soft quantifiers])[
  For $p in (0, oo)$, writing $(-)^(plus.minus p)$ for post-composition with
  $t |-> t^(plus.minus p)$ on $[0,oo]$:
  $
    hat(exists)^p (nu, u) := (I_X (nu, space u^p))^(1 slash p), quad quad
    hat(forall)^p (nu, u) := (I_X (nu, space u^(-p)))^(-1 slash p),
  $
  both morphisms $cal(P) X times Omega^X -> Omega$, since $(-)^(plus.minus p)$
  is Borel on $[0,oo]$ and $I_X$ is a morphism.

  #align(center)[
    #commutative-diagram(
      node((0, 0), $cal(P) X times Omega^X$),
      node((0, 1), $cal(P) X times Omega^X$),
      node((1, 1), $Omega$),
      node((1, 0), $Omega$),
      arr((0, 0), (0, 1), $"id" times (-)^(-p)$),
      arr((0, 1), (1, 1), $I_X$),
      arr((1, 1), (1, 0), $(-)^(-1 slash p)$, label-pos: right),
      arr((0, 0), (1, 0), $hat(forall)^p$, label-pos: right),
    )]
]

#remark[
  $I_X (nu, u)$ is the expectation $EE_(x tilde nu)[u(x)]$, and we write the
  latter as sugar for the former $EE_(x tilde nu)[e] := I_X (nu, lambda x. e)$
]


== Operators semantics

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

Unwinding $I_X$:

$
  sem(forall^p (x : A_omega). phi)(g)
  = (integral_RR sem(phi)(g, alpha(r))^(-p) dif mu(r))^(-1 slash p)
  = integral^(-p)_(x in sem(A)) sem(phi)(g, x) dif omega,
$ <eq:unwind>

$
  sem(forall^p (u : (Prd A)_pi). Phi)(g)
  = integral^(-p)_(u in Omega^(sem(A))) sem(Phi)(g, u) dif pi.
$ <eq:ho>




== Sequent Calculus


$ Gamma mid(|) Xi tack Theta quad quad $

where:
- $Gamma$ ctx of grade vector $P in sof^n$,
- $Xi, Theta$ finite multisets of formulas in $Gamma$



== Tripos semantics

We need to define the Tripos construction on the category of quasi-Borel spaces.
The main ingredient is the hyperdoctrine $LL : "Ctx"^op -> "Poset"$ hyperdoctrine to interpret the logic.
We first define a partial order on predicates $Omega$.

#theorem([*Poset* QBS(X, $infinity$)])[
  Let $Omega = [0,oo]$ and $attach(lt.eq, br: Omega) := {(a,b) in Omega^2 : a <= b}$. For
  $X in "QBS"$ define, for $phi, psi in Omega^X = "QBS"(X, Omega)$,
  $
    phi attach(lt.eq, br: X) psi quad :<==> quad ⟨phi, psi⟩ : X -> Omega times Omega
    "factors through" attach(lt.eq, br: Omega) arrow.r.hook Omega times Omega.
  $
  Then:
  - $attach(lt.eq, br: Omega) arrow.r.hook Omega times Omega$ is a subobject in $"QBS"$;
  - $phi attach(lt.eq, br: X) psi$ iff $phi(x) <= psi(x)$ for every $x in X$, and the
    factorisation is then unique;
  - $(|Omega^X|, attach(lt.eq, br: X))$ is a *partial* order;
  - for every $f : Y -> X$ in $"QBS"$, $(-) compose f$ is monotone, so
    $Omega^((-))$ lifts to a functor $"QBS"^"op" -> "Poset"$.
]

#example($"Order in" Omega$)[
  Take $X := RR$, so that $|Omega^RR| = "QBS"(RR, Omega)$ is the poset of Borel
  maps $RR -> [0,oo]$. Let
  $
    phi := lambda x. space abs(x) quad
    psi := lambda x. space abs(x) + 1 quad
    "and" theta := lambda x. space 1.
  $

  - *Comparable.* $phi attach(lt.eq, br: RR) psi$: for every $x$, $⟨phi, psi⟩(x) = (abs(x), abs(x) + 1) in attach(lt.eq, br: Omega)$, so
  $⟨phi,psi⟩$ factors through $attach(lt.eq, br: Omega) arrow.r.hook Omega times Omega$.

  - *Incomparable.* $phi$ and $theta$: at $x = 0$ we get $(0,1) in attach(lt.eq, br: Omega)$, but at $x = 2$ we get $(2,1) in.not attach(lt.eq, br: Omega)$. Neither factorisation exists, so the order is *partial*, not total.

  - *Antisymmetric.* $lambda x. abs(x)$ and $lambda x. sqrt(x^2)$ compare both ways, hence are equal as they are, being the same function. This is the step that uses well-pointedness.
]

== Tripos like semantics

#definition([Tripos semantics??])[
  We define the semantics of sequents $Gamma mid(|) Xi tack Theta$ as the functor
  $
    LL : "Ctx"^op -> "Poset" \
    Gamma |-> (|Omega^(U sem(Gamma))|, attach(lt.eq, br: U sem(Gamma)))
  $
  and together with a natural bijection
  $
    "Obj"(LL X) ≊ "Ctx"(X, Omega)
  $
]

#definition([Sequent semantics])[
  The semantics of a sequent is a morphism in $"Poset"$:
  $
    sem(Gamma tack phi : Omega) := sem(phi) : U sem(Gamma) -> Omega
  $

  $
    sem(Gamma mid(|) Xi tack Theta) in Omega :=
    integral^(-P)_(arrow(z) in sem(Gamma))
    ( (⨂_(gamma in Xi) gamma) multimap (⨂^*_(delta in Theta) delta) )(arrow(z))
    dif omega_Gamma,
  $ <eq:seq>

  $
    phi ⊑_P psi quad :=quad
    mark(integral^(-p_1)_(z_1 in X_1) dots.c integral^(-p_n)_(z_n in X_n), tag: #<mix>)
    (phi multimap psi)(arrow(z)) dif omega_n dots.c dif omega_1
  $ <eq:ent>
]



= Examples


Let $I := [0,1]$, $upsilon := [iota, "Unif"[0,1]] in Dst I$, so $I_upsilon "dom"$ and we define the predicate
$phi := lambda x : I. space x$. The sequents:

$
  x attach(:, br: p) I_upsilon mid(|) diamond.small tack phi space x, quad
  x attach(:, br: p) I_upsilon mid(|) phi space x tack phi space x times.o 2, quad
$

are interpreted as follows:

$
  sem((x attach(:, br: p) I_upsilon) mid(|) dot.c tack phi space x) & = integral^(-p)_(x in I) x dif upsilon = (1-p)^(1 slash p)
  quad quad (0 "for" p >= 1), \
  sem((x attach(:, br: p) I_upsilon) mid(|) phi space x tack phi space x ⊗ 2) & = integral^(-p)_(x in I) (x multimap 2 x) dif upsilon
  = integral^(-p)_(x in I) 2 dif upsilon = 2.
$ <eq:ex1a>



#bibliography("bibliography.bib")
