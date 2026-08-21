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
  [$a multimap b = sup{c mid(|) a ⊗ c <= b} = a^* ⊗^* b$],
  [---],
  [$a ⊕^p b = (a^p + b^p)^(1 slash p)$, #h(0.4em) $a ⊕^(-p) b = (a^(-p) + b^(-p))^(-1 slash p)$],
  [$0$ / $oo$],
)

#rem[
  The two corner conventions $0 ⊗ oo = 0$ and $0 ⊗^* oo = oo$ are forced, not ad hoc:
  they are exactly what makes $multimap$ the residual of $⊗$ at every boundary
  ($a ⊗ b <= c$ iff $b <= a multimap c$, e.g. $0 multimap 0 = oo$ needs
  $oo ⊗^* 0 = oo$), what makes $(-)^*$ an involution with dualizing element $1$
  (so $(Omega, ⊗, 1, (-)^*)$ is a *Girard quantale* and $⊗^*$ its "par"), and what
  makes reflexivity of the graded entailment of @sec:quasitripos exact. Via $-log$,
  $(Omega, <=, ⊗, 1)$ is isomorphic to the extended Lawvere quantale
  $([-oo,+oo], >=, +, 0)$ @lawvere1973, with $(-)^*$ becoming negation.
]

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
            mid(|) smp_cal(D) \
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


#definition[
  - $"Pred" A ≔ A -> Omega$
  - $"Pred"^2 A ≔ ("Pred" A) -> Omega$
  - $forall^p (x : A_omega). phi ≔ hat(forall)^p (omega\, lambda x : A. phi),$
  - $exists^p (x : A_omega). phi ≔ hat(exists)^p (omega\, lambda x : A. phi),$
]

#rem[
  Note the regrade in the sugar: Q-Bind types the bound variable $x cp A_omega$,
  while the right-hand side $lambda$-abstracts it at $x coo A$. The two are
  coherent because both are interpreted over the same underlying space
  $sem(A)$ --- the grade and the measure of the discharged slot are consumed by
  the quantifier, not by the $lambda$ --- but this deserves an explicit coherence
  lemma.
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

#rem[
  Conn is indexed by the arity of the constant, so it covers the whole signature
  $c_Omega$ at once. At $n = 0$ it types the *constants*: $Gamma tack 0 : Omega$,
  $Gamma tack 1 : Omega$ and $Gamma tack oo : Omega$ in every well-formed
  context, with no premise beyond $Gamma ctx$; at $n = 1$ the involution and the
  powers $phi^*, phi^p$; at $n = 2$ the binary connectives. We keep the usual
  infix and postfix notation ($phi ⊗ psi$, $phi^*$) as sugar for the official
  applicative form $c_Omega (phi_1, dots.c, phi_n)$. Via Prop, every such term
  is also a proposition, which is what the operator semantics below interprets.
]

#v(1em)

*Monadic rules:*

#v(1em)

#grid(
  columns: (1fr, 1fr),
  gutter: 7pt,
  row-gutter: 10pt,
  prooftree(rule(name: [Ret], $Gamma tack t : A$, $Gamma tack ret t : Dst A$)),
  prooftree(rule(name: [Smp], $cal(D) "std. Borel on" A$, $Gamma tack smp_cal(D) : Dst A$)),
)

#rem[
  There is deliberately no normalisation construct: $Dst A$ is interpreted by the
  *probability* monad $cal(P)$, on whose values normalisation is the identity, so a
  $nrm$ rule would be vacuous. Conditioning requires moving to s-finite or
  subprobability kernels with a partial $nrm$; we leave this extension to future
  work.
]
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
  $X = (|X|, M_X)$ is a *quasi-Borel space* with a underlying set $|X|$ and a set of functions $M_X subset.eq { RR -> |X|}$ closed under precomposition with Borel maps, containing constants, closed under countable Borel gluing. Given $f: X -> Y$ is a morphism if and only if $f compose alpha in M_Y$ for all $alpha in M_X$.
  - QBS is cartesian closed: $M_(Y^X) = { alpha mid(|) "uncurry"(alpha) in "QBS"(RR times X, Y)}$
  - QBS is well pointed
  - $Sigma_(M_X) = { U mid(|) forall alpha in M_X dot alpha^(-1) U in Sigma_RR}$ is the induced 𝜎-algebra.
  - The commutative monad  $"Dist" X = { [alpha, mu] mid(|) alpha in M_X, mu in "Prob"(RR) }$ modulo equal push-forward, with
    $
      integral_(X) f d[alpha, mu] = integral_(RR) f compose alpha d mu
    $
]

#definition("Probability measure")[
  Write $G(RR)$ for the set of probability measures on $RR$ with the
  $sigma$-algebra generated by the evaluations $nu |-> nu(B)$, $B$ Borel (the
  Giry space). A probability measure on a QBS $X$ is a pair $(alpha, mu)$ with $alpha in M_X$ and $mu in G(RR)$, modulo equal push-forward. Then
  - $|cal(P)(X)| = { (alpha, mu) "probability measure on" (X, M_X) } slash ~$
  - $M_(cal(P)(X)) = { beta : RR -> cal(P)(X) mid(|) exists alpha in M_X, g in "Meas"(RR, G(RR)), forall r, beta(r) = (alpha, g(r)) }$
  so that $cal(P)(X) = (|cal(P)(X)|, M_(cal(P)(X)))$ is a QBS. On morphisms
  $f : X -> Y$ the action is $cal(P)(f)[alpha, mu] := [f compose alpha, mu]$.
  ($cal(P)$ is the semantic incarnation of the monad written $"Dist"$ above.)
]

We now define the category of measured quasi-Borel spaces that will interpret our domain types.

#definition($"Category QBS"_C$)[
  - Objects are $(|X|, M_X, omega_X)$, *measured quasi-Borel spaces*, written
    $(X, omega)$, with a QBS structure $(|X|, M_X)$ and a measure
    $omega_X in |cal(P)(X)|$.

  - Morphisms $f : (X, omega) -> (Y, rho)$ are QBS morphisms $f : X -> Y$ of
    *finite compression*, $C(f) < oo$. Writing
    $f_* omega := l_Y (cal(P)(f)(omega))$ for the induced measure on
    $Sigma_(M_Y)$ (where $l_Y [alpha, mu] := alpha_* mu$), the *measure
    compression* of $f$ is
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
  Assume $Sigma_(M_X)$ is countably separated with measurable singletons
  (e.g. $X$ standard Borel). Then
  $Delta_X = ⟨"id", "id"⟩$ is a morphism of $"QBS"_C$ iff $omega$ is *purely
  atomic* with atom masses bounded below, i.e. $omega = sum_i m_i delta_(a_i)$
  with $inf_i m_i > 0$ (hence finitely many atoms), in which case
  $
    C(Delta_X) = 1 slash min_i m_i.
  $
  In particular $Delta_X$ is never a morphism when $omega$ has an atomless part.

  #rem[
    The compression condition quantifies over *all* $U in Sigma_(M_(X times X))$,
    and a measure inequality verified on the rectangles $A times B$ alone does not
    extend to the generated $sigma$-algebra, so testing rectangles only
    *lower-bounds* $C(Delta_X)$. The correct route: (lower bounds / necessity)
    $(Delta_X)_* omega (A times A) = omega(A)$ against
    $(omega ⊗ omega)(A times A) = omega(A)^2$ gives $C >= 1 slash omega(A)$; taking
    $A$ a singleton atom, resp.\ subsets of the atomless part with
    $omega(A) -> 0$, forces the stated characterisation. (Upper bound) for purely
    atomic $omega$ and *any* $U$, with $m := min_i m_i$,
    $
      (Delta_X)_* omega (U)
      = sum_(i : (a_i, a_i) in U) m_i
      <= 1/m sum_(i : (a_i, a_i) in U) m_i^2
      <= 1/m (omega ⊗ omega)(U),
    $
    since the singletons ${(a_i, a_i)} subset.eq U$ are disjoint of product measure
    $m_i^2$; equality is attained at $U = {(a_j, a_j)}$ for the smallest atom $a_j$.
  ]

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

  $sem(ret t) = eta compose sem(t)$, $sem("let" x <- M "in" N) = sem(N)^dagger compose ⟨ "id", sem(M) ⟩$,
  $sem(smp_cal(D)) = cal(D)$,
  $sem(t[s slash x]) = sem(t) compose ⟨ "id", sem(s) ⟩$,
  $sem(Phi[psi slash u]) = sem(Phi) compose ⟨ "id", cur (sem(psi)) ⟩$,
) <eq:term-sem>

#rem[
  In the last clause $Gamma\, x coo A tack psi "prop"$ may have free variables of
  $Gamma$: $sem(psi) : U sem(Gamma) times sem(A) -> Omega$ and
  $cur (sem(psi)) : U sem(Gamma) -> Omega^(sem(A))$ curries the $A$-argument. The
  simpler clause $cur (sem(psi) compose pi_2)$ is the special case of $psi$ closed.
]

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
  $I_X : cal(P) X times Omega^X -> Omega$ is well defined and a morphism of
  quasi-Borel spaces, and it satisfies the naturality law
  $I_Y (cal(P)(f)(nu), v) = I_X (nu, v compose f)$ for every $"QBS"$ morphism
  $f : X -> Y$.
] <lem:integration>

#proof[
  *Step 1: well-definedness.* Every $u in Omega^X = "QBS"(X, Omega)$ is
  $Sigma_(M_X)$-measurable: for Borel $U subset.eq Omega$ and any $alpha in M_X$,
  $alpha^(-1)(u^(-1) U) = (u compose alpha)^(-1) U in Sigma_RR$ since
  $u compose alpha$ is Borel, so $u^(-1) U in Sigma_(M_X)$ by definition of the
  induced $sigma$-algebra. If $[alpha, mu] = [alpha', mu']$, i.e.
  $alpha_* mu = alpha'_* mu'$ on $Sigma_(M_X)$, then by the change-of-variables
  formula for pushforwards of $[0,oo]$-valued measurable maps,
  $
    integral_RR u(alpha(r)) dif mu(r)
    = integral_X u thin dif (alpha_* mu)
    = integral_X u thin dif (alpha'_* mu')
    = integral_RR u(alpha'(r)) dif mu'(r),
  $
  so $I_X (nu, u)$ does not depend on the representative of $nu$; the integral
  always exists in $[0,oo]$.

  *Step 2: reduction along a random element.* Let
  $gamma = ⟨gamma_1, gamma_2⟩ in M_(cal(P) X times Omega^X)$, so
  $gamma_1 in M_(cal(P) X)$ and $gamma_2 in M_(Omega^X)$. By the definition of
  $M_(cal(P)(X))$ there are $alpha in M_X$ and $g in Meas(RR, G(RR))$ with
  $gamma_1 (s) = (alpha, g(s))$ for all $s$; by cartesian closure,
  $h := "uncurry"(gamma_2) : RR times X -> Omega$ is a $"QBS"$ morphism. Hence
  $
    k := h compose ("id"_RR times alpha) : RR times RR -> [0, oo]
  $
  is a $"QBS"$ morphism between standard Borel spaces, i.e. a Borel map
  @qbs, and
  $
    (I_X compose gamma)(s)
    = integral_RR gamma_2 (s)(alpha(r)) dif g(s)(r)
    = integral_RR k(s, r) dif g(s)(r).
  $

  *Step 3: the parametric integral is Borel.* Define
  $J : RR times G(RR) -> [0,oo]$ by $J(s, nu) := integral_RR k(s,r) dif nu(r)$.
  For $k = bb(1)_B$ with $B in Sigma_(RR times RR)$, $J(s, nu) = nu(B_s)$ where
  $B_s$ is the section: the class of $B$ for which $(s, nu) |-> nu(B_s)$ is Borel
  contains the rectangles $B_1 times B_2$ (the map is
  $bb(1)_(B_1)(s) dot nu(B_2)$, Borel because evaluation
  $nu |-> nu(B_2)$ generates the $sigma$-algebra of $G(RR)$), and is a
  $lambda$-system by $sigma$-additivity and closure of Borel maps under pointwise
  limits; by the $pi$--$lambda$ theorem it contains all of
  $Sigma_(RR times RR)$. Linearity extends Borel-ness of $J$ to simple $k$, and
  monotone convergence to arbitrary Borel $k >= 0$ via simple approximations
  $k_n arrow.tr k$. Finally $s |-> (s, g(s))$ is Borel, so
  $I_X compose gamma = J compose ⟨"id", g⟩$ is Borel, i.e.
  $I_X compose gamma in M_Omega$. As $gamma$ was arbitrary, $I_X$ is a $"QBS"$
  morphism.

  *Naturality.* $cal(P)(f)[alpha, mu] = [f compose alpha, mu]$, so
  $I_Y (cal(P)(f)(nu), v) = integral_RR v(f(alpha(r))) dif mu(r)
  = I_X (nu, v compose f)$.
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

Dually, $integral^(p)$ (positive exponent) abbreviates the $hat(exists)^p$
integral: $integral^(p)_(x in sem(A)) sem(phi)(g, x) dif omega =
(integral sem(phi)(g, x)^p dif omega)^(1 slash p)$.




= A graded quasi-tripos over QBS <sec:quasitripos>

A tripos in the sense of Hyland--Johnstone--Pitts @hjp1980 @pitts2002 asks for a
functor into $"Poset"$ with (i) Heyting-algebra fibers, (ii) left and right
adjoints to reindexing along projections satisfying the Beck--Chevalley and
Frobenius conditions, and (iii) a generic predicate. Our semantics *cannot* form
a tripos: we record four obstructions in @rem:no-tripos, each structural rather
than technical. What it does form is a precisely axiomatisable weakening, which
we call a *graded quasi-tripos*: the fibers are Girard-quantale ordered rather
than Heyting, the soft quantifiers are measure-indexed graded operators that are
adjoint in an $Omega$-enriched sense (@prop:enriched-adj) and order-adjoint only
at the limit grade $p = oo$, Beck--Chevalley holds laxly with a defect measured
exactly by the compression grade, and the generic predicate --- the ingredient
that makes the logic higher order --- survives on the nose.

== The predicate functor

We first define a partial order on predicates $Omega$.

#theorem([*Poset* QBS(X, $Omega$)])[
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

  - *Antisymmetric.* $lambda x. abs(x)$ and $lambda x. sqrt(x^2)$ compare both ways, hence are equal as they are, being the same function. This is the step that uses concreteness of $"QBS"$: morphisms are plain functions, so mutual pointwise domination forces equality.
]

== The doctrine and its generic predicate

The theorem above gives a functor $L : "QBS"^op -> "Poset"$ with
$L(X) := (|Omega^X|, attach(lt.eq, br: X))$ and $L(f) := (-) compose f$. This ---
and not a functor on $"Ctx"$ --- is the indexing of our predicates.

#definition([Predicate doctrine])[
  The *predicate doctrine* of HQLL is
  $
    LL := L compose U^"op" : "Ctx"^"op" -> "QBS"^"op" -> "Poset",
    quad quad
    LL(Gamma) = (|Omega^(U sem(Gamma))|, attach(lt.eq, br: U sem(Gamma))),
  $
  and the semantics of a proposition is a point of the fiber:
  $sem(Gamma tack phi : Omega) := sem(phi) : U sem(Gamma) -> Omega$.
  Predicates over $Gamma$ are reindexed along *arbitrary* $"QBS"$ morphisms
  between the underlying spaces $U sem(Gamma)$; the category $"Ctx"$ contributes
  only the bookkeeping of grades and measures, through $U$. In particular
  substitution $sem(t[s slash x]) = sem(t) compose ⟨"id", sem(s)⟩$ is reindexing
  along a $"QBS"$ morphism $U sem(Gamma) -> U sem(Gamma\, x coo A)$; no such
  morphism exists in $"Ctx"$, whose maps are thinnings with slotwise components.
]

#proposition([Generic predicate])[
  $sigma := "id"_Omega in L(Omega)$ is a generic predicate: for every $X$ and
  every $phi in L(X)$,
  $
    phi = "id"_Omega compose phi = L(phi)(sigma),
  $
  with classifying map $[phi] := phi : X -> Omega$ itself (here $[phi] = phi$ is
  in fact the *unique* classifying map, although the tripos definition does not
  demand uniqueness). Consequently the doctrine is genuinely higher
  order: $Prd A = Omega^(sem(A))$ is an object by cartesian closure of $"QBS"$,
  $Prd^2 A$ makes sense, and Leibniz equality is expressible on the cartesian
  fragment.
]

#remark([Why the doctrine is not indexed over $"Ctx"$])[
  One might hope for a natural bijection
  $"Obj"(LL Gamma) ≊ "Ctx"(Gamma, iota(Omega))$, exhibiting a generic predicate
  inside $"Ctx"$ itself. This fails. Against $iota(Omega)$: a $"Ctx"$-morphism
  factors through a single slot, so on $Gamma = ((RR, oo); (RR, oo))$ the joint
  predicate $phi(x, y) = abs(x - y)$ is unrepresentable ($phi(0,0) = 0 != 1 =
  phi(0,1)$ kills factoring through the first slot, $phi(0,1) = 1 != 0 = phi(1,1)$
  through the second). Against an *arbitrary* candidate $Sigma$ --- note a
  higher-order slot can recombine slots, e.g. $Sigma = ((Omega^RR, oo); (RR, oo))$
  with $sigma = ev$ represents all binary predicates --- genericity still fails:
  $"Ctx"(diamond.small, Sigma) = emptyset$ for every nonempty $Sigma$ (there is
  no monotone injection $[k] -> [0]$) while $LL(diamond.small) ≅ Omega$ is a
  continuum, and a context with more slots than $|Sigma|$ has genuinely joint
  predicates depending on more slots than any thinning can select. Hence
  predicates must be indexed over $"QBS"$, as above.
]

== Why there is no tripos

#remark([The four obstructions])[
  + *Soft quantifiers are not order-adjoint to weakening for $p < oo$.* The unit
    law $phi <= pi^* hat(exists)^p phi$ fails on any spike: on $[0,1]$ with the
    uniform measure and $p = 2$, $phi = bb(1)_([0, 1 slash 4])$ has
    $hat(exists)^2 = 1 slash 2 < 1 = phi(1 slash 8)$; the counit fails dually for
    $hat(forall)^p$. Worse, *no* graded Galois connection
    $hat(exists)^p phi <= B ⊗ psi <==> phi <= G(psi)$ exists for any finite $B$:
    the constant-norm spikes $phi_epsilon = epsilon^(-1 slash p)
    bb(1)_([0, epsilon])$ (all with $hat(exists)^p phi_epsilon = 1 <= B ⊗ 1$)
    force $G(1)(x) >= sup_(epsilon >= x) epsilon^(-1 slash p) = x^(-1 slash p)$,
    whence $hat(exists)^p G(1) >= (integral_0^1 x^(-1) dif x)^(1 slash p) = oo$,
    contradicting the biconditional at $phi = G(1)$, which bounds
    $hat(exists)^p G(1)$ by $B ⊗ 1 < oo$. Averaging operators cannot extremise.
  + *Even at $p = oo$, the pointwise order does not support adjoints.* For a
    Borel $B subset.eq [0,1]^2$ whose projection $A$ is analytic but not Borel,
    $sup_y bb(1)_B (x, y) = bb(1)_A (x)$ is not a morphism, and no least Borel
    majorant exists. The genuine adjunction $esssup tack.l pi^* tack.l essinf$
    holds only in the mixed order of @prop:enriched-adj (iii): measure-indexed
    quantification is *forced* by $"QBS"$, not a design choice.
  + *Fibers are Girard-quantale ordered, not Heyting.* $(Omega, ⊗, 1, (-)^*)$ is
    a commutative Girard quantale, so the internal logic is classical *linear*
    logic with graded quantifiers. The chain $[0, oo]$ does carry a min/max/$=>$
    Heyting structure, but it is not the structure of our connectives
    ($2 ⊗ 2 = 4 != min(2,2) = 2$; Heyting negation on a chain is
    ${0, oo}$-valued and kills the involution $(-)^*$): a Heyting tripos over
    these fibers would model the wrong logic.
  + *No diagonals on measured slots.* By the diagonal lemma, $Delta$ exists in
    $"QBS"_C$ only over purely atomic measures, so the tripos equality predicate
    $exists_Delta (top)$ and contraction are unavailable --- by design: exchange
    already fails at unequal grades (mean-of-sup $3 slash 4$ vs sup-of-mean
    $1 slash 2$ in the two-variable example), and Leibniz equality survives on
    the cartesian fragment.
] <rem:no-tripos>

== Quantifier calculus

We write $hat(exists)^p_omega (u) := hat(exists)^p (omega, u)$ and
$hat(forall)^p_omega (u) := hat(forall)^p (omega, u)$ when the measure matters,
and drop $omega$ when it is clear.

#lemma([Quantifier calculus])[
  Let $(A, omega)$ be a measured slot with $omega$ a probability measure,
  $pi : X times A -> X$ the projection, $phi, chi in Omega^(X times A)$,
  $psi in Omega^X$, quantification acting on the $A$-slot. For all
  $p, q in (0, oo]$:
  + *(monotone retractions)* $hat(exists)^p, hat(forall)^p$ are monotone and
    $hat(exists)^p (pi^* psi) = psi = hat(forall)^p (pi^* psi)$;
  + *(one-way rules)* $phi <= pi^* psi ==> hat(exists)^p phi <= psi$, and
    $pi^* psi <= phi ==> psi <= hat(forall)^p phi$;
  + *(Frobenius, with the correct pairing)*
    $hat(exists)^p (pi^* psi ⊗ phi) = psi ⊗ hat(exists)^p phi$ and
    $hat(forall)^p (pi^* psi ⊗^* phi) = psi ⊗^* hat(forall)^p phi$, on the nose,
    boundary values of $psi$ included; the cross pairings fail at
    $psi in {0, oo}$;
  + *(grade monotonicity)* for $q <= p$:
    $hat(forall)^p phi <= hat(forall)^q phi <= hat(exists)^q phi <=
    hat(exists)^p phi$, with $hat(exists)^p phi arrow.tr esssup_omega phi$ and
    $hat(forall)^p phi arrow.br essinf_omega phi$ as $p -> oo$;
  + *(Hölder)* $hat(exists)^(p ⊕^* q) (phi ⊗ chi) <= hat(exists)^p phi ⊗
    hat(exists)^q chi$: the harmonic sum of the grade algebra is realised by the
    Hölder conjugacy law;
  + *(Markov)* for $t > 0$:
    $omega{a mid(|) phi(x, a) > t ⊗ hat(exists)^p phi (x)} <= t^(-p)$
    --- the sound quantitative residue of the instantiation axiom, which is
    itself unsound by @rem:no-tripos (i).
  The proofs are standard consequences of the power-mean and Hölder inequalities
  and are omitted.
] <lem:qcalc>

#proposition([Soft quantifiers as $Omega$-enriched adjoints])[
  In the setting of @lem:qcalc, for every $p in (0, oo)$, pointwise in $x in X$:
  + $(hat(exists)^p phi multimap psi) = hat(forall)^p (phi multimap pi^* psi)$;
  + $(psi multimap hat(forall)^p phi) = hat(forall)^p (pi^* psi multimap phi)$;
  + at $p = oo$, in the *mixed order* (pointwise in $x$, $omega$-a.e. in the
    quantified slot), $esssup_omega tack.l pi^* tack.l essinf_omega$ are genuine
    adjoints, and both operators are $"QBS"$ morphisms.
  Reading $multimap$ as the $Omega$-valued hom of the fiber and $hat(forall)^p$
  as the graded aggregation of homs, (i)--(ii) say precisely that
  $hat(exists)^p$ is left adjoint and $hat(forall)^p$ right adjoint to $pi^*$
  *in the $Omega$-enriched sense*: the object of morphisms from
  $hat(exists)^p phi$ to $psi$ equals the aggregated object of morphisms from
  $phi$ to $pi^* psi$. The order-theoretic adjunction would be the image of
  (i)--(ii) under "$1 <=$", and holds only at $p = oo$.
] <prop:enriched-adj>

#proof[
  Fix $x in X$ and abbreviate $u := phi(x, -) in Omega^A$, $c := psi(x) in Omega$,
  $M_p (u) := hat(exists)^p (omega, u) = (integral u^p dif omega)^(1 slash p)$,
  $M_(-p)(u) := hat(forall)^p (omega, u) = (integral u^(-p) dif omega)^(-1 slash p)$.
  Recall $a multimap b = a^* ⊗^* b$, so $0 multimap b = oo$,
  $oo multimap b = 0$ for $b < oo$, and $a multimap oo = oo$ for every $a$.

  *(i) $M_p (u) multimap c = M_(-p)(u multimap c)$.* By cases on $c$.

  _Case $0 < c < oo$._ Pointwise $(u multimap c)^(-p) = u^p slash c^p$: at
  interior $u$ this is arithmetic; at $u = 0$,
  $(0 multimap c)^(-p) = oo^(-p) = 0 = 0 slash c^p$; at $u = oo$,
  $(oo multimap c)^(-p) = 0^(-p) = oo = oo slash c^p$. Hence, with
  $I := integral u^p dif omega in [0, oo]$,
  $
    M_(-p)(u multimap c) = (c^(-p) I)^(-1 slash p).
  $
  If $0 < I < oo$ this is $c slash I^(1 slash p) = M_p (u) multimap c$. If
  $I = 0$ then $M_p (u) = 0$ and both sides are $oo$
  ($0 multimap c = oo$; $(c^(-p) dot 0)^(-1 slash p) = 0^(-1 slash p) = oo$). If
  $I = oo$ then $M_p (u) = oo$ and both sides are $0$
  ($oo multimap c = 0$ as $c < oo$; $oo^(-1 slash p) = 0$).

  _Case $c = oo$._ The left side is $M_p (u) multimap oo = oo$. Pointwise
  $u multimap oo = oo$, so $(u multimap oo)^(-p) = 0$, and the right side is
  $0^(-1 slash p) = oo$.

  _Case $c = 0$._ The left side is $oo$ if $M_p (u) = 0$ and $0$ otherwise.
  Pointwise $u multimap 0$ is $oo$ on ${u = 0}$ and $0$ on ${u > 0}$, so
  $(u multimap 0)^(-p)$ is $0$ on ${u = 0}$ and $oo$ on ${u > 0}$; hence
  $integral (u multimap 0)^(-p) dif omega = oo dot omega(u > 0)$ and the right
  side is $oo$ if $omega(u > 0) = 0$ and $0$ otherwise. The two agree because
  $M_p (u) = 0$ iff $u = 0$ $omega$-a.e.

  *(ii) $c multimap M_(-p)(u) = M_(-p)(c multimap u)$.* By cases on $c$.

  _Case $0 < c < oo$._ Pointwise $(c multimap u)^(-p) = c^p u^(-p)$ (at $u = 0$:
  $(c multimap 0)^(-p) = 0^(-p) = oo = c^p dot oo$; at $u = oo$:
  $oo^(-p) = 0 = c^p dot 0$). With $I := integral u^(-p) dif omega$,
  $M_(-p)(c multimap u) = (c^p I)^(-1 slash p)$, which for $0 < I < oo$ equals
  $I^(-1 slash p) slash c = c multimap M_(-p)(u)$; at $I = 0$ both sides are
  $oo$, at $I = oo$ both sides are $0$ (using $0 < c < oo$).

  _Case $c = 0$._ The left side is $0 multimap M_(-p)(u) = oo$. Pointwise
  $0 multimap u = oo$ (including $u = 0$, by $oo ⊗^* 0 = oo$), so the right side
  is $M_(-p)(oo) = oo$.

  _Case $c = oo$._ The left side is $0$ if $M_(-p)(u) < oo$ and $oo$ if
  $M_(-p)(u) = oo$. Pointwise $oo multimap u$ is $0$ on ${u < oo}$ and $oo$ on
  ${u = oo}$, so $(oo multimap u)^(-p)$ is $oo$ on ${u < oo}$ and $0$ on
  ${u = oo}$; the right side is therefore $oo$ if $omega(u < oo) = 0$ and $0$
  otherwise, which agrees since $M_(-p)(u) = oo$ iff $u = oo$ $omega$-a.e.

  *(iii)* For each fixed $x$, $esssup_omega phi(x, -) <= psi(x)$ iff
  $phi(x, a) <= psi(x)$ for $omega$-almost-every $a$: this is the definition of
  the essential supremum. Since the $x$-coordinate is compared pointwise, this
  is exactly the adjunction $esssup_omega tack.l pi^*$ in the mixed order, and
  dually $pi^* tack.l essinf_omega$. Morphism-hood: by @lem:qcalc (iv),
  $M_p (phi(x, -)) arrow.tr esssup_omega phi(x, -)$ pointwise as $p -> oo$
  through any sequence (the classical $L^p -> L^oo$ limit for probability
  measures), each $M_p$ is a morphism by @lem:integration, and pointwise
  limits of morphisms into $Omega$ are morphisms because Borel maps into
  $[0, oo]$ are closed under pointwise limits; dually for $essinf_omega$.
]

#rem[
  For $p < oo$, the identities (i)--(ii) are the *only* adjunction there is: by
  @rem:no-tripos (i) no order-theoretic Galois connection, graded or not,
  exists. The sequent rules for $exists^p$ and $forall^p$ remain sound because
  they use only the one-way laws of @lem:qcalc (ii); instantiation axioms are
  unsound, their quantitative residue being Markov's inequality
  (@lem:qcalc (vi)).
]

#proposition([Substitution and graded Beck--Chevalley])[
  Let $p in (0, oo]$.
  + *(passive slots, strict)* for any $"QBS"$ morphism $f : X -> Y$, measured
    slot $(A, nu)$ and $phi in Omega^(Y times A)$:
    $hat(exists)^p_nu (phi compose (f times "id")) =
    (hat(exists)^p_nu phi) compose f$, and likewise for $hat(forall)^p_nu$:
    reindexing that does not touch the quantified slot commutes with
    quantification on the nose.
  + *(measure-preserving substitution, strict)* if $f : (X, omega) -> (Y, rho)$
    has $C(f) = 1$ then $f_* omega = rho$ (both are probabilities), and for
    every $u in Omega^Y$:
    $hat(exists)^p_omega (u compose f) = hat(exists)^p_rho (u)$ and
    $hat(forall)^p_omega (u compose f) = hat(forall)^p_rho (u)$, by the
    naturality law of @lem:integration.
  + *(graded lax Beck--Chevalley)* if $C(f) = B < oo$ then for every
    $u in Omega^Y$
    $
      hat(exists)^p_omega (u compose f) <= B^(1 slash p) ⊗ hat(exists)^p_rho (u),
      quad quad
      hat(forall)^p_omega (u compose f) >= B^(-1 slash p) ⊗ hat(forall)^p_rho (u).
    $
    The constants $B^(plus.minus 1 slash p)$ are attained: for the inclusion
    $([0, 1 slash B], B dot "Leb") arrow.r.hook ([0, 1], "Leb")$, take
    $u = bb(1)_([0, 1 slash B])$ for the $hat(exists)$-constant and
    $u' = bb(1)_([0, 1 slash B]) + oo dot bb(1)_((1 slash B, 1])$ for the
    $hat(forall)$-constant (then $hat(forall)^p_rho (u') = B^(1 slash p)$ and
    both sides equal $1$). No reverse inequalities hold, and the defect
    vanishes as $p -> oo$: *the compression grade exactly measures the failure
    of Beck--Chevalley*. Proof: extend $f_* omega <= B rho$ from sets to
    integrals of nonnegative functions by simple approximation and monotone
    convergence; omitted.
] <prop:bc>

#rem[
  $log C(f)$ is the Rényi divergence of order $oo$, $D_oo (f_* omega || rho)$,
  i.e. the max privacy-loss bound of differential privacy; @prop:bc (iii) is
  the categorical form of the Rényi post-processing law @sato2019span.
]

== Sequent calculus and graded entailment

$ Gamma mid(|) Xi tack Theta $

where $Gamma$ is a context with grade vector $P in sof^n$ and $Xi, Theta$ are
finite multisets of formulas in $Gamma$.

#definition([Sequent semantics])[
  For a slot $(X_i, p_i)$ of $sem(Gamma)$ and a predicate $v$ on (the
  underlying space of) $X_i$, define
  $
    integral^(-p_i)_(z_i in X_i) v :=
    cases(
      hat(forall)^(p_i) (omega_i, v) & quad p_i < oo,
      inf_(z_i) v(z_i) & quad p_i = oo,
    )
  $
  *unmeasured slots are quantified by the plain infimum* --- grade-$oo$ validity
  in the cartesian variables --- since they carry no measure to integrate
  against. Then
  $
    sem(Gamma mid(|) Xi tack Theta) :=
    integral^(-p_1)_(z_1 in X_1) dots.c integral^(-p_n)_(z_n in X_n)
    ( (⨂_(gamma in Xi) sem(gamma)) multimap (⨂^*_(delta in Theta) sem(delta)) )(arrow(z)),
  $ <eq:seq>
  discharging slots from the rightmost (innermost) to the leftmost, and the
  graded entailment between $phi, psi in LL(Gamma)$ is
  $
    phi ⊑_P psi :=
    integral^(-p_1)_(z_1 in X_1) dots.c integral^(-p_n)_(z_n in X_n)
    (phi multimap psi)(arrow(z)).
  $ <eq:ent>
  A sequent is *valid at grade $P$* when $1 <= sem(Gamma mid(|) Xi tack Theta)$.
]

#lemma([$Omega$-enriched graded structure])[
  Graded entailment is *reflexive*, $1 <= (phi ⊑_P phi)$; on fully measured
  contexts (all $p_i < oo$) equality holds iff $phi$ avoids ${0, oo}$ almost
  everywhere (on grade-$oo$ slots the infimum needs only one interior witness
  per section, so avoidance is sufficient but not necessary). It satisfies
  *graded cut*
  $
    (phi ⊑_P psi) ⊗ (psi ⊑_Q chi) <= (phi ⊑_(P ⊕^* Q) chi),
  $
  with grade vectors composing by the slotwise harmonic sum; the grade
  $P ⊕^* Q$ is *sharp* (no larger grade validates cut in general). Hence each
  fiber is an $sof$-graded $Omega$-enriched category --- after $-log$, a graded
  Lawvere generalized metric space @lawvere1973 --- of which the pointwise order
  of the predicate functor is the $p = oo$ shadow. Proof by the reverse Hölder
  inequality with conjugate exponents $p slash r, q slash r$; omitted.
] <lem:cut>

== The graded quasi-tripos

We can now name the structure the semantics actually forms.

#definition([Graded quasi-tripos])[
  Let $sof = ([0, oo], ⊕^*, and)$ be the grade quantale and $Omega$ a
  commutative Girard quantale. A *graded quasi-tripos* consists of:
  + *(graded semicartesian base)* a semicartesian symmetric monoidal category
    $(cal(B), ⊗, I)$ --- unit terminal, projections everywhere, diagonals *not*
    required --- with a lax $sof$-grading on morphisms: $C("id") = 1$,
    $C(g compose f) <= C(f) dot C(g)$ @ghl2021;
  + *(fibers)* a functor $P : cal(B)^"op" -> "Poset"$ landing in partially
    ordered $Omega$-modules carrying the monoidal-closed signature
    $(⊗, ⊗^*, multimap, (-)^*, ⊕^(plus.minus p))$, with reindexing a strict
    homomorphism for all of it;
  + *(generic predicate)* an object $hat(Omega)$ with $sigma in P(hat(Omega))$
    such that every $phi in P(X)$ equals $P([phi])(sigma)$ for some
    $[phi] : X -> hat(Omega)$ --- here supplied by cartesian closure of the
    ambient category ($"QBS"$), not of the base;
  + *(graded quantifiers)* for each measured slot and grade $p in (0, oo]$,
    monotone operators $hat(exists)^p, hat(forall)^p$ satisfying the quantifier
    calculus of @lem:qcalc, the $Omega$-enriched adjunctions of
    @prop:enriched-adj, order adjunction at $p = oo$, and Beck--Chevalley
    strict on the $C = 1$ sub-base and lax with defect
    $C(f)^(plus.minus 1 slash p)$ in general (@prop:bc);
  + *(graded entailment)* an $Omega$-valued, $sof$-graded entailment on each
    fiber with identity at grade $oo$, cut composing grades by $⊕^*$
    (@lem:cut), and thinning acting by $and$.
] <def:gqt>

#theorem([HQLL forms a graded quasi-tripos])[
  The data $("Ctx", C)$, $LL = L compose U^"op"$, $sigma = "id"_Omega$,
  $(hat(exists)^p, hat(forall)^p)$ and $⊑_P$ satisfy @def:gqt, with
  @lem:qcalc, @prop:enriched-adj, @prop:bc and @lem:cut supplying the axioms.
]

#remark([Relation to the tripos-to-topos construction])[
  Applying the tripos-to-topos recipe to $LL$ yields the category of
  $Omega$-valued partial equivalence relations (symmetric, $⊗$-transitive
  $E in LL(X ⊗ X)$): after $-log$, measurable *partial-metric-like spaces* in
  the sense of Lawvere generalized metric spaces @lawvere1973 @hohlekubiak2011.
  Because $Omega$ is not idempotent, this category is symmetric monoidal closed
  and semicartesian but *not* an elementary topos --- over a semicartesian
  non-idempotent quantale the truth-value object collapses to the quantale
  itself @tenoriomariano2022 --- and the rule of unique choice corresponds to
  Cauchy completeness of the $Omega$-enriched objects @dagninopasquali-tac.
  This justifies the name *quasi*-tripos. The closest existing notions are the
  Lipschitz and quantitative doctrines of Dagnino--Pasquali
  @dagninopasquali2022 @dagninopasquali2025 (substructural fibers, graded
  structural rules, equality-as-distance, over a cartesian base) and the
  monad-algebra predicate transformers of Kozen and Hasuo
  @kozen1985 @hasuo2015: our $I_X$ is the Eilenberg--Moore expectation algebra
  of $cal(P)$ on $Omega$, and the soft quantifiers are its conjugates by
  $(-)^(plus.minus p)$; the compression grading instantiates divergence-graded
  reasoning at $D_oo$ @sato2019span. None of the three contains the other two;
  the graded quasi-tripos is their common generalization.
]



= Examples



#example([Propositional])[
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
]

#example([Quantifying over predicates: $Prd^2 I$])[
  Let $I := [0,1]$ with $dot.c tack.r upsilon : Dst I$ uniform, and
  $phi := lambda x : I. space x$.

  *A functional on predicates.* By $lambda$-abstracting the bound predicate,
  $
    "Avg"^p := lambda u : Prd I. space exists^p (x : I_upsilon). space u space x
    quad : quad Prd^2 I,
  $
  whose denotation is a *point of a function space*,
  $sem("Avg"^p) = cur (hat(exists)^p)(sem(upsilon)) in |Omega^(Omega^I)|$: the
  soft quantifier, curried at its measure argument. Applying it is $ev$:
  $
    "Avg"^2 space phi = (integral_0^1 x^2 dif x)^(1 slash 2) = (1 slash 3)^(1 slash 2)
      approx 0.577, quad quad
    "Avg"^1 space phi = 1 slash 2.
  $

  *Quantifying over the predicate variable.* This needs a measure *on
  $Prd I = Omega^I$*, which must be supplied. Take
  $
    kappa &:= lambda s : I. space lambda x : I. space abs(x - s) quad &: quad I -> Prd I, \
    M &:= "let" s <- "sample"_upsilon "in" "return"(kappa space s) quad &: quad Dst (Prd I),
  $
  and put $pi := M$, so $sem(pi) = cal(P)(sem(kappa))(sem(upsilon)) in |cal(P)(Omega^I)|$
  and $(Prd I)_pi$ is a domain type. Then
  $
    Psi := exists^2 (u : (Prd I)_pi). space "Avg"^2 space u quad : quad Omega
  $
  is a *closed* formula, and 
  $
    sem(Psi) = integral^2_(u in Omega^I) sem("Avg"^2 space u) dif sem(pi)
      = (integral_0^1 Phi(s)^2 dif s)^(1 slash 2), quad
    Phi(s) := "Avg"^2 (kappa space s) = (s^2 - s + 1 slash 3)^(1 slash 2),
  $
  giving $sem(Psi) = (1 slash 6)^(1 slash 2) approx 0.408$.
]

#remark[
  The outer integral never runs over $Omega^I$. Since
  $sem(pi) = [kappa compose iota, "Unif"]$, integrating against it *is*
  integrating the seed $s$ over $[0,1]$ --- this is the definition of $I_X$ at
  $X := Omega^I$. Nothing canonical selects $pi$: the two-point prior
  $(delta_0 + delta_1) slash 2$ gives $(1 slash 3)^(1 slash 2) approx 0.577$
  for the same $Psi$.
]

#example([Two variables, and why contexts are ordered])[
  In $Gamma = (x attach(:, br: p) I_upsilon, space y attach(:, br: q) I_upsilon)$ take
  $
    phi := abs(x - y) quad "with" quad Gamma tack.r phi "prop", quad
    sem(phi) : I times I -> Omega.
  $
  Nested quantification discharges the *rightmost* slot first, so
  $exists^p (x). space exists^q (y). space phi$ means
  $hat(exists)^p (upsilon, space lambda x. space hat(exists)^q (upsilon, space lambda y. space phi))$.

  *Equal grades commute.* At $p = q = 2$, Fubini merges the two integrals:
  $
    exists^2 (x : I_upsilon). space exists^2 (y : I_upsilon). space abs(x-y)
    = (integral_0^1 integral_0^1 (x-y)^2 dif x dif y)^(1 slash 2)
    = (1 slash 6)^(1 slash 2) approx 0.408,
  $
  the same in either order.

  *Different grades do not.* Take $p = 1$ (mean) and $q = oo$ (sup):
  $
    exists^1 (x : I_upsilon). space exists^oo (y : I_upsilon). space abs(x-y)
      &= integral_0^1 space sup_y abs(x-y) dif x
       = integral_0^1 max(x, 1-x) dif x = 3 slash 4, \
    exists^oo (y : I_upsilon). space exists^1 (x : I_upsilon). space abs(x-y)
      &= sup_y integral_0^1 abs(x-y) dif x
       = sup_y (y^2 + (1-y)^2) slash 2 = 1 slash 2.
  $
  A mean of suprema is not a supremum of means: $3 slash 4 eq.not 1 slash 2$.
  This is why $Gamma$ is an *ordered* list and why exchange is unavailable at
  unequal grades.
]

#remark[
  The two examples are the same computation. Because $pi$ is presented by
  $kappa$, the higher-order $Psi$ of the $Prd^2 I$ example unfolds to the first-order
  double quantification
  $exists^2 (s : I_upsilon). space exists^2 (x : I_upsilon). space abs(x - s)$
  of the two-variable example --- both $(1 slash 6)^(1 slash 2)$. Quantification over
  predicates is genuinely higher-order in its *syntax*, but is computed on the
  seed whenever the prior comes from a program.
]


#bibliography("bibliography.bib")
