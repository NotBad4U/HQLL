#import "lib.typ": *

#import "@preview/cetz:0.4.2"
#import "@preview/showybox:2.0.4": showybox
#import "@preview/mannot:0.3.1": *


#let abstract = ""

#show: para-lipics.with(
  title: [Higher order QLL with QBS],
  title-running: [],
  authors: (
    (
      name: [Alessio Coltellacci],
      email: "alecol@itu.dk",
      website: "http://www.myhomepage.edu",
      orcid: "0009-0005-3580-2075",
      affiliations: [

      ],
    ),
  ),
  abstract: abstract,
  keywords: [Dyck paths, Temporal logics, Interval temporal logics, Model checking],
)


// = Preliminaries: Quasi-Borel Spaces

// The standard measure-theoretic formalization of probability theory is built on
// the category *Meas* of measurable spaces and measurable functions.
// While adequate for most classical purposes, this category fails to accommodate
// higher-order probabilistic reasoning: as shown by Aumann @Aumann1961BorelSF, *Meas* is
// not cartesian closed, and in particular there is no measurable space of
// functions $RR -> RR$ @qbs. Quasi-Borel spaces @qbs provide a convenient category in which probability distributions, higher-order functions, and continuous sample spaces coexist.

// The guiding intuition is a shift of emphasis. In the traditional setting one
// fixes a sample space $(Omega, Sigma_Omega)$ and studies random variables,
// i.e. measurable maps $Omega -> X$. The $sigma$-algebra $Sigma_X$ on the
// target plays only an auxiliary role, constraining which maps count as
// measurable. Quasi-Borel spaces take the set of admissible random variables as
// primitive, fixing the sample space once and for all to be $RR$, one of the
// best-behaved standard Borel spaces.

// #definition("Quasi-Borel space")[
//   A _quasi-Borel space_ is a pair $(X, M_X)$ consisting of a set $X$ together
//   with a set $M_X subset.eq [RR -> X]$ of functions, called _random elements_
//   of $X$, satisfying:
//   + if $alpha in M_X$ and $f colon RR -> RR$ is measurable, then
//     $alpha compose f in M_X$;
//   + every constant function $alpha colon RR -> X$ belongs to $M_X$;
//   + if $RR = union.plus.big_(i in NN) S_i$ is a partition into Borel sets and
//     $alpha_1, alpha_2, dots in M_X$, then the function $beta$ defined by
//     $beta(r) = alpha_i (r)$ for $r in S_i$ is also in $M_X$.
// ]

// The first condition says that $M_X$ is closed under measurable reparametrization
// of the sample space; the second guarantees that every point of $X$ is observable
// as a (constant) random element; and the third provides the piecewise-gluing
// required to make $M_X$ behave like a $sigma$-algebra of random variables.

// #observation("Canonical examples")[
//   Every measurable space $(X, Sigma_X)$ induces a quasi-Borel space
//   $(X, M_(Sigma_X))$, where $M_(Sigma_X)$ is the set of measurable functions
//   $RR -> X$. In particular:
//   - $RR$ is a quasi-Borel space with $M_RR$ the measurable maps $RR -> RR$;
//   - the two-element discrete space $2$ is a quasi-Borel space whose random
//     elements are exactly the characteristic functions of Borel subsets of $RR$.
// ]


// #definition("Category of quasi-Borel spaces")[
//   The _category of quasi-Borel spaces_ $bold("QBS")$ is defined as follows:
//   - Objects: quasi-Borel spaces
//     $ (X, M_X) $  where $M_(Sigma_X)$ is the set of measurable functions $RR -> X$;
//   - Morphisms:
//     $(X, M_X) -> (Y, M_Y)$ is a function $f colon X -> Y$ such that $f compose alpha in M_Y$ whenever $alpha in M_X$.
//     Morphisms compose as functions, and identity functions are morphisms.
// ]

// Morphisms between quasi-Borel spaces are analogous to measurable functions between measurable space in *Meas*.
// We can for example integrate over them. Integration against $(alpha, mu)$ reduces to
// integration on $RR$ for any morphism $f colon (X, M_X) -> RR$:
// $
//   integral f dif (alpha, mu) #h(0.4em) eq.def #h(0.4em)
//   integral_RR (f compose alpha) dif mu.
// $

// #example("Probability measures on quasi-Borel spaces")[
//   Take the two-element discrete space $2 = {0, 1}$ as a quasi-Borel space
//   $(2, M_2)$, where $M_2$ is the set of measurable maps $RR -> 2$ and $Sigma_2 = {emptyset,{0},{1},{0,1}}$.
//   These are exactly the characteristic functions $chi_B$ (i.e. indicator functions $bb(1)_B$) of Borel sets $B subset.eq RR$.

//   Two random variables in $M_2$:

//   $ alpha = chi_([0, 1)), quad alpha(r) = cases(1 "if" 0 <= r < 1, 0 "otherwise"), $
//   $ beta = chi_(QQ), quad beta(r) = cases(1 "if" r in QQ, 0 "otherwise"). $

//   Equip $RR$ with $mu = cal(N)(0,1)$. The push-forwards are Bernoulli measures: $ alpha_* mu = "Bern"(Phi(1) - Phi(0)), quad beta_* mu = "Bern"(0) = delta_0, $ since $QQ$ has Lebesgue (hence Gaussian) measure zero.
// ]

// Unlike *Meas*, the category *QBS* is cartesian closed @qbs. Given the quasi-Borel spaces $(X, M_X)$ and $(Y, M_Y)$, the exponential $Y^X$ has as
// underlying set the hom-set $bold("QBS")((X, M_X), (Y, M_Y))$ of morphisms, equipped with the random elements
// $
//   M_(Y^X) eq.def { alpha colon RR -> Y^X #h(0.3em) | #h(0.3em)
//     "uncurry"(alpha) in bold("QBS")(RR times X, Y) },
// $
// so that a random element of $Y^X$ is exactly a random function $RR times X -> Y$.
// The evaluation map $Y^X times X -> Y$ is then a morphism with the expected universal property.
// Cartesian closure is what recovers function spaces such as $RR^RR$, which have no counterpart in *Meas*, and is the structural feature that lets $bold("QBS")$ serve as a semantic domain for higher-order probabilistic programs.


= A Locally graded enriched preorders

The following is an enriched version of the notion of locally $cal(M)$-graded category.
We first give a direct (and slightly more general) definition of the concept. Let $(cal(M), ⪯, i , dot.o)$
be an ordered monoid and $(cal(V), <=, I, times.o)$ be a symmetric monoidal preorder.

#definition()[
  A locally $cal(M)$-graded, $cal(V)$-enriched preorder $((cal(M), cal(V))-bold("Pre")$ for short) $P$  is comprised of the following data
  - a set of elements $P$
  - for each $a, b ∈ P$ , and grade $m ∈ cal(M)$, an m-witness of inequality
    $
      (a ⊑#sub[m] b) ∈ V ,
    $
  - *Graded reflexvity*: $forall a in P, <= a ⊑#sub[i] a$
  - *Graded transitivity*: $∀a, b, c ∈ P , m, n ∈ cal(M), (a ⊑#sub[m] b) ⊗ (b ⊑#sub[n] c) ≤ (a ⊑_(m dot.o n) c).$
  - *Relaxation:* $∀a, b ∈ P , m, n ∈ cal(M), m ⪯ n arrow.r (a ⊑#sub[n] b) ≤ (a ⊑#sub[m] b)$.
]

#definition("Opposite graded order")[
  The opposite of an $((cal(M), cal(V))$-preorder $(P , ⊑(−))$ is the $((cal(M), cal(V))$-preorder  $P^op$ := (P , ⊒(−)) where
  $
    ∀m ∈ cal(M), a, b ∈ P , (a ⊒#sub[m] b) equiv (b ⊑#sub[m] a)
  $
]

#definition()[
  The 2-category $(cal(M), cal(V))-bold("Pre")$ has:
  - _objects_: $(cal(M), cal(V))-bold("Pre")$,
  - _morphisms_:  their maps,
  - _2-cells_: i-witnessed transformations.

  It is monoidal once equipped  with the tensor product of $(cal(M), cal(V))$-preorders.
]

We can now define the preorder: $(cal(M), cal(V))-bold("Pre")$ for $cal(M) = [0, ∞]_(⊕^*)$ and $cal(V) = [0, ∞]_⊗$

= The QProb category

Objects of $bold("QBS")$ ignore measures: a QBS-morphism is just a function that pulls
random elements back to random elements. To get a doctrine that tracks how measures
transport, we assemble QBS-spaces equipped with a probability measure into a category
whose morphisms are _measure-non-increasing_, mirroring Capucci's $bold("Prob")$ but built
on $bold("QBS")$ rather than $bold("Meas")$.

#definition("Objects of QProb")[
  An object of $bold("QProb")$ is a pair $((X, M_X), p_X)$ where $(X, M_X)$ is a quasi-Borel
  space and $p_X in P(X)$ is a probability measure on it. Concretely, $p_X$ is represented
  by a pair $(alpha, mu)$ with $alpha in M_X$ and $mu in G(RR)$, taken modulo the
  equivalence
  $
    (alpha, mu) tilde (alpha', mu') quad "iff" quad alpha_* mu = alpha'_* mu'
    quad "on" (X, Sigma_(M_X)).
  $
]

#definition("Morphisms of QProb")[
  A morphism $f colon ((X, M_X), p_X) -> ((Y, M_Y), p_Y)$ is a QBS-morphism $f colon X -> Y$
  that is _measure-non-increasing_: for every QBS-morphism $phi colon Y -> [0, infinity]$,
  $
    integral_X (phi compose f) dif p_X
    quad <= quad
    integral_Y phi dif p_Y. quad (*)
  $
  Equivalently, $P(f)(p_X) <= p_Y$ as measures on $(Y, Sigma_(M_Y))$.
]

#lemma("QProb is a category")[
  Identities are measure-preserving. For composability, given
  $f colon (X, p_X) -> (Y, p_Y)$ and $g colon (Y, p_Y) -> (Z, p_Z)$ and a test QBS-morphism
  $phi colon Z -> [0, infinity]$, the function $phi compose g$ is itself a QBS-morphism into
  $[0, infinity]$ and so qualifies as a test for $f$; chaining $(*)$ twice gives
  $
    integral_X phi compose g compose f dif p_X
    <= integral_Y phi compose g dif p_Y
    <= integral_Z phi dif p_Z.
  $
  Associativity and identity laws are inherited from $bold("QBS")$.
  \
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#observation("Structure of QProb")[
  $bold("QProb")$ has:
  - a _terminal object_ $(*, delta_*)$: the singleton QBS with its unique probability measure;
  - _binary products_ $((X times Y, M_(X times Y)), p_X times.o p_Y)$, where $times.o$
    is the product measure given by the strength of the probability monad $P$ on $bold("QBS")$;
    the projections $pi_X, pi_Y$ are measure-preserving, since the marginals of
    $p_X times.o p_Y$ are exactly $p_X$ and $p_Y$;
  - an _embedding of_ $bold("Prob")$: the right adjoint $R colon bold("Meas") -> bold("QBS")$
    restricts to a fully faithful embedding of standard Borel probability spaces into
    $bold("QProb")$.
]


= A doctrine of Quasi-Borel Spaces

We can now assemble the doctrine
$
  L colon bold("QProb")^op -> ([0, infinity]_(plus.o^*), [0, infinity]_(times.o))-bold("Pre")
$
whose grading monoid is $[0, infinity]_(plus.o^*)$ and whose enrichment is
$[0, infinity]_(times.o)$. The fibre over a QProb object $(X, p_X)$ is the set of
$[0, infinity]$-valued predicates on $X$:

$
  L(X, p_X) #h(0.3em) := #h(0.3em)
    bold("QBS")((X, M_X), ([0, infinity], M_([0, infinity]))),
$

i.e. the set of QBS-morphisms $X -> [0, infinity]$. By Proposition 15(1) of @qbs this
coincides with the $Sigma_(M_X)$-measurable functions $X -> [0, infinity]$, so on standard
Borel spaces we recover Capucci's fibres verbatim.

#observation("Pointwise quantale on predicates")[
  The quantale operations $times.o, multimap colon [0, infinity]^2 -> [0, infinity]$ are
  Borel-measurable, hence QBS-morphisms with respect to the product QBS structure on
  $[0, infinity]^2$. They therefore restrict to pointwise operations on $L(X, p_X)$:
  $
    (phi times.o psi)(x) := phi(x) times.o psi(x),
    quad
    (phi multimap psi)(x) := phi(x) multimap psi(x).
  $
  This is the only point of contact between the QBS layer and the quantale layer: the QBS
  structure decides _which functions count as predicates_, the quantale acts on _values_,
  and pointwise application bridges the two.
]

== Graded entailment

#definition("Graded entailment")[
  For $(X, p_X) in bold("QProb")$, $phi, psi in L(X, p_X)$, and softness $p in [0, infinity]$,
  the _$p$-graded entailment_ is
  $
    phi attach(tack.r.short, tr: p_X, br: p) psi
    #h(0.3em) := #h(0.3em)
    integral_(x in X)^(-p) (phi multimap psi)(x) dif p_X(x)
    #h(0.3em) in #h(0.3em) [0, infinity].
  $
]

Unfolding a representative $p_X = [alpha, mu]$, the QBS integral reduces to a $p$-graded
harmonic integral on $RR$:

#v(3em)  // space for the top annotations
$
  phi attach(tack.r.short, tr: p_X, br: p) psi #h(0.3em) = #h(0.3em)
  markul(integral_(r in RR)^(-p), tag: #<pmean>, color: #blue)
  markul((phi multimap psi), tag: #<impl>, color: #purple)
  (markul(alpha(r), tag: #<probe>, color: #red))
  dif markul(mu(r), tag: #<base>, color: #teal)
  #annot(<pmean>, pos: top, dy: -1.6em, leader-connect: "elbow")[Harmonic $p$-mean]
  #annot(<impl>, pos: bottom, dy: 1.2em, leader-connect: "elbow")[$psi / phi$]
  #annot(<probe>, pos: bottom, dy: 2.4em, leader-connect: "elbow")[Sample $X$ through a RV]
  #annot(<base>, pos: bottom + right, dy: 1.2em, leader-connect: "elbow")[Base probability on $RR$]
$
#v(3em)  // space for the bottom annotations

Independence of the representative $(alpha, mu)$ follows from the QBS-integration identity
$ integral_X g dif (alpha, mu) = integral_RR (g compose alpha) dif mu $
and the equivalence relation $tilde$ defining $p_X$.

== Action on morphisms

For a QProb morphism $f colon (X, p_X) -> (Y, p_Y)$, the action of $L$ is precomposition:

$ f^* colon L(Y, p_Y) -> L(X, p_X), quad f^* (psi) := psi compose f. $

Well-definedness ($psi compose f$ is a QBS-morphism into $[0, infinity]$) is immediate from
composition in $bold("QBS")$.

== Soft-first-order properties

#lemma("Graded reflexivity")[
  For every $phi in L(X, p_X)$ and every $p in [0, infinity]$,
  $ phi attach(tack.r.short, tr: p_X, br: p) phi #h(0.3em) >= #h(0.3em) 1, $
  the unit of $times.o$. Indeed $(phi multimap phi)(x) = 1$ wherever $phi(x) in (0, infinity)$,
  so $ integral_(x in X)^(-p) 1 dif p_X(x) = 1. $
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#lemma("Graded transitivity (Hölder)")[
  For every $phi, psi, chi in L(X, p_X)$ and every $p, q in [0, infinity]$,
  $
    (phi attach(tack.r.short, tr: p_X, br: p) psi)
    #h(0.3em) times.o #h(0.3em)
    (psi attach(tack.r.short, tr: p_X, br: q) chi)
    quad <= quad
    (phi attach(tack.r.short, tr: p_X, br: p plus.o^* q) chi).
  $
  Equivalently, the dual generalized Hölder inequality:
  $
    integral_(x in X)^(-p) psi/phi dif p_X (x)
    #h(0.3em) times.o #h(0.3em)
    integral_(x in X)^(-q) chi/psi dif p_X (x)
    quad <= quad
    integral_(x in X)^(-p plus.o^* q) chi/phi dif p_X (x).
  $
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#lemma("Relaxation")[
  For every $phi, psi in L(X, p_X)$ and every $p, q in [0, infinity]$ with $p <= q$,
  $
    phi attach(tack.r.short, tr: p_X, br: q) psi
    #h(0.3em) <= #h(0.3em)
    phi attach(tack.r.short, tr: p_X, br: p) psi.
  $
  This is monotonicity of $L^q$-norms in $q$ on a probability space, applied to the QBS
  integration on $(X, p_X)$ via its reduction to $(RR, mu)$.
  \
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#lemma("Pullback preserves entailment")[
  For every morphism $f colon (X, p_X) -> (Y, p_Y)$ in $bold("QProb")$ and every
  $psi_1, psi_2 in L(Y, p_Y)$,
  $
    psi_1 attach(tack.r.short, tr: p_Y, br: p) psi_2
    #h(0.3em) <= #h(0.3em)
    f^* psi_1 attach(tack.r.short, tr: p_X, br: p) f^* psi_2.
  $
  Key identity: $(psi_1 compose f) multimap (psi_2 compose f) = (psi_1 multimap psi_2) compose f$
  (pointwise quantale operations commute with precomposition), so the right-hand side is
  exactly the morphism inequality $(*)$ applied to the test function $psi_1 multimap psi_2 in L(Y, p_Y)$.
  \
  Proof.

  #text(fill: colors.emerald, "TODO")
]

== Quantifiers as projection adjoints

#theorem("Projection adjoints")[
  For objects $(X, p_X), (Y, p_Y) in bold("QProb")$ and softness $p in [0, infinity]$,
  reindexing along the projection
  $pi_X colon (X times Y, p_X times.o p_Y) -> (X, p_X)$
  $
    pi_X^* colon L(X, p_X) -> L(X times Y, p_X times.o p_Y)
  $
  admits both a $p$-graded left and right adjoint:
  $
    (exists_(pi_X)^p theta)(x)
    #h(0.3em) = #h(0.3em)
    integral_(y in Y)^p theta(x, y) dif p_Y (y),
    quad
    (forall_(pi_X)^p theta)(x)
    #h(0.3em) = #h(0.3em)
    integral_(y in Y)^(-p) theta(x, y) dif p_Y (y),
  $
  satisfying the adjunction laws
  $
    exists_(pi_X)^p theta attach(tack.r.short, tr: p_X, br: p) phi
    #h(0.3em) <==> #h(0.3em)
    theta attach(tack.r.short, tr: p_X times.o p_Y, br: p) pi_X^* phi,
  $
  and dually for $forall_(pi_X)^p$.
  \
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#corollary("Higher-order hyperdoctrine of QBS")[
  The functor
  $ L colon bold("QProb")^op -> ([0, infinity]_(plus.o^*), [0, infinity]_(times.o))-bold("Pre") $
  is a soft-first-order hyperdoctrine. Cartesian closure of $bold("QBS")$ then promotes it
  to a _higher-order_ hyperdoctrine: predicate types $bold("Pred")(X) = [0, infinity]^X$ live
  in $bold("QBS")$ as bona fide function spaces, enabling internal quantification over
  predicates, predicates-of-predicates, and function-space contexts.
]

// === Old draft (kept for reference) ===

// We fix a Borel probability measure $mu in P(RR)$, one may take $mu$ to be the uniform distribution on the unit interval $[0, 1]$ without loss of generality.

// #observation()[
//   A probability measure on a quasi-Borel space $(X, M_X)$ is a pair $(alpha, mu)$ of $alpha in M_X$ and a probability measure $mu$ on $RR$.
// ]

// Consider now the sets $L(X, M_X)$ of QBS morphisms $(X, M_X) -> [0, infinity]$, where $[0, infinity]$ is the quasi-Borel space with underlying set $[0, infinity]$ and random elements the measurable functions $RR -> [0, infinity]$. For each $p in (0 , + infinity)$ define

// // $
// //   phi scripts(tack.r.short)^mu_p psi := and.big_(alpha in M_X) integral_(x in RR)^(-p) psi(x) multimap psi(x) dot mu(x)
// // $
// //

// #v(3em)  // space for the top annotations
// $
//   phi scripts(tack.r.short)^mu_p psi :=
//   markul(and.big_(alpha in M_X), tag: #<meet>, color: #olive)
//   markul(integral_(r in RR)^(-p), tag: #<pmean>, color: #blue)
//   markul((phi multimap psi), tag: #<impl>, color: #purple)
//   (markul(alpha(r), tag: #<probe>, color: #red))
//   dif markul(mu(r), tag: #<base>, color: #teal)
//   #annot(<meet>, pos: top + left, dy: -1.6em, leader-connect: "elbow")[Meet over QBS probes]
//   #annot(<pmean>, pos: top, dy: -1.6em, leader-connect: "elbow")[Harmonic $p$-mean ]
//   #annot(<impl>, pos: bottom, dy: 1.2em, leader-connect: "elbow")[$psi / phi$]
//   #annot(<probe>, pos: bottom, dy: 2.4em, leader-connect: "elbow")[Sample $X$ through a RV]
//   #annot(<base>, pos: bottom + right, dy: 1.2em, leader-connect: "elbow")[Base probability on $RR$]
// $
// #v(3em)  // space for the bottom annotations

// This definition satisfies the following properties:

// #lemma("Graded reflexivity")[
//   For every $phi in L(X, M_X)$ and every $p in (0, infinity)$,
//   $ phi attach(tack.r.short, tr: mu, br: p) phi. $
//   in other words,
//   $
//     1 = and.big_(alpha in M_X) integral_(r in RR)^(-infinity)1 dif mu(x) <= and.big_(alpha in M_X) integral_(r in RR)^(-infinity) phi/phi dif mu(x).
//   $
//   Proof.

//   #text(fill: colors.emerald, "TODO")
// ]

// #lemma("Graded transitivity")[
//   For every $phi, psi, chi in L(X, M_X)$ and every $p, q in (0, infinity)$,
//   $
//     phi attach(tack.r.short, tr: mu, br: p) psi quad "and" quad psi attach(tack.r.short, tr: mu, br: q) chi
//     quad ==> quad phi attach(tack.r.short, tr: mu, br: p plus.o^* q) chi.
//   $
//   which amounts to dual generalized Hölder inequality:
//   $
//     and.big_(alpha in M_X) integral_(r in RR)^(-p) psi/phi dif mu(x)
//     times.o integral_(r in RR)^(-q) chi/psi dif mu(x)
//     <= and.big_(alpha in M_X) integral_(r in RR)^(-p plus.o^* q) chi/phi dif mu(x).
//   $
//   Proof.

//   #text(fill: colors.emerald, "TODO")
// ]

// #lemma("Relaxation")[
//   For every $phi, psi in L(X, M_X)$ and every $p, q in (0, infinity)$ with $p <= q$,
//   $
//     phi attach(tack.r.short, tr: mu, br: p) psi <= phi attach(tack.r.short, tr: mu, br: q) psi.
//   $
//   by general properties of $L^p$ norms over probability spaces.
//   \
//   Proof.

//   #text(fill: colors.emerald, "TODO")
// ]

// #corollary("The higher-order hyperdoctrine of Quasi-Borel Spaces")[
//   The higher-order hyperdoctrine of Quasi-Borel Spaces is the functor $L : bold("QBS")^op -> (plus.o^*, times.o) bold("-Prd")$
// ]

= Sequent calculus



#bibliography("bibliography.bib")


