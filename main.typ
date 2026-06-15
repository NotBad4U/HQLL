#import "lib.typ": *

#import "@preview/cetz:0.4.2"
#import "@preview/showybox:2.0.4": showybox
#import "@preview/mannot:0.3.1": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

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


#let tacklnot = scale(x: -100%)[#sym.tack.r.not]



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

// Objects of $bold("QBS")$ ignore measures: a QBS-morphism is just a function that pulls
// random elements back to random elements.
To get a doctrine that tracks how measures transport, we consider QBS equipped with a probability measure into a category whose morphisms are _measure-non-increasing_, mirroring built on $bold("QBS")$ (i.e. $bold("Meas")$) rather than $bold("Prob")$.

#definition("The category QProb")[
  - An object of $bold("QProb")$ is a pair $((X, M_X), rho_X)$ where $(X, M_X)$ is a quasi-Borel
  space and $rho_X in P(X)$ is a probability measure on it. Concretely, $rho_X$ is represented
  by a pair $(alpha, mu)$ with $alpha in M_X$ and $mu in G(RR)$.

  - A morphism $f colon ((X, M_X), rho_X) -> ((Y, M_Y), p_Y)$ is a QBS-morphism $f colon X -> Y$
  that is _measure-non-increasing_: for every QBS-morphism $phi colon Y -> [0, infinity]$,
  $
    integral_X (phi compose f) dif rho_X
    quad <= quad
    integral_Y phi dif p_Y. quad
  $
  Equivalently, $P(f)(rho_X) <= p_Y$ as measures on $(Y, Sigma_(M_Y))$.
]

I will omit to write $M_Y$ and $M_X$ when they are clear from context, and write $(X, rho_X)$ for brevity.

#lemma("QProb is a category")[
  - Identities are measure-preserving;
  - For composability, given
  $f colon (X, rho_X) -> (Y, p_Y)$ and $g colon (Y, p_Y) -> (Z, p_Z)$ and a test QBS-morphism
  $phi colon Z -> [0, infinity]$, the function $phi compose g$ is itself a QBS-morphism into
  $[0, infinity]$ and so qualifies as a test for $f$; chaining $(*)$ twice gives
  $
    integral_X phi compose g compose f dif rho_X
    <= integral_Y phi compose g dif p_Y
    <= integral_Z phi dif p_Z.
  $
  Associativity and identity laws are inherited from $bold("QBS")$.

]

#lemma("QProb has terminal object")[
  $bold("QProb")$ has a _terminal object_ $(*, delta_*)$ i.e. the singleton QBS with its
  dirac measure at $*$.
]

#lemma("QProb has an independent tensor, not binary products")[
  $bold("QProb")$ has a natural _independent tensor_ given by
  $
    (X, rho_X) ⊗ (Y, p_Y)
    #h(0.3em) := #h(0.3em)
    (X times Y, rho_X times.o p_Y),
  $
  where $rho_X times.o p_Y$ is the product measure. The projections
  $pi_X, pi_Y$ are measure-preserving, since the marginals of
  $rho_X times.o p_Y$ are exactly $rho_X$ and $p_Y$.

  Associativity, symmetry, and the unit $(*, delta_*)$ are inherited from the QBS
  product and from ordinary product measures, so this gives an affine symmetric
  monoidal structure on $bold("QProb")$.

  However, this tensor is not generally a categorical product. The missing part is
  the universal pairing map. For example, take the finite discrete QBS
  $2 = {0, 1}$ with the fair measure
  $
    gamma = 1/2 delta_0 + 1/2 delta_1.
  $
  Let $f, g colon (2, gamma) -> (2, gamma)$ both be the identity morphism. If
  $(2, gamma) ⊗ (2, gamma)$ were a categorical product, the pairing
  $angle.l f, g angle.r colon (2, gamma) -> (2 times 2, gamma times.o gamma)$
  would have to be a QProb morphism. But this pairing is the diagonal map
  $Delta(z) = (z, z)$. Its push-forward measure gives mass $1$ to the diagonal
  $D = { (0, 0), (1, 1) }$, while
  $
    (gamma times.o gamma)(D) = 1/2.
  $
  Hence $P(Delta)(gamma) <= gamma times.o gamma$ fails. Thus the independent
  tensor does not satisfy the categorical product universal property.
]

#lemma($"QProb" tacklnot tack.r.not "QBS"$)[
  There is a forgetful functor $U: bold("QProb") -> bold("QBS")$ such that $U(((X, M_X), rho_X)) = (X, M_X)$,
  but it does not generally have a left or a right ajoint.

  - If $F: bold("QBS") -> bold("QProb")$, so
  $
    bold("QProb")(F X, ((Y, M_Y), p_Y)) ≌ bold("QBS")(X, U(Y)),
  $
  Let $X$ be the terminal object of QBS i.e. 1 and $Y = {0, 1} = 2$. In QBS we have two maps from $1 -> Y$,
  one selecting 1 and one selecting 0.
  In QProb, however, there is only one morphism from $F 1$ to $((Y, M_Y), delta)$, since any such morphism must be measure-preserving and the only probability measure on $1$ is the dirac at its unique point.


  Because for having a morphism from $F 1 -> (Y, delta_0)$ we would need $delta_1 <= delta_0$ which is false because $delta_1({1}) = 1 > 0 = delta_0({1})$.

  Hence, no such generic $F$ can exist.

  - If $R: bold("QBS") -> bold("QProb")$,
  $
    bold("QProb")((X, rho_X), R Y) ≌ bold("QBS")(U(X), Y)
  $
  a contradiction by a similar argument can be found by taking $X = 2$ and $Y = 1$.
]

#observation("Embedding of Prob into QProb")[
  ??? _(Should work only for standard Borel spaces)_
]

#remark("Truth-value object versus random-weight context")[
  Let
  $
    W := ([0, infinity], M_([0, infinity]))
  $
  be the quasi-Borel space whose random elements are the measurable maps
  $RR -> [0, infinity]$. This is the object of quantitative truth values/weights.
  No probability measure on $W$ is part of this truth-value structure.

  If we additionally choose a measure $rho_W in P(W)$, then $(W, rho_W)$ is an
  object of $bold("QProb")$, but it should be read as a _probabilistic context of
  random weights_, not as the truth-value object itself. For example, one may use:
  - $rho_W = (lambda r. 1, delta_0)$, representing a degenerate context constantly equal to $1$;
  - $rho_W = (lambda r. e^r, cal(N)(0, 1))$, giving a log-normal random-weight context;
  - $rho_W = (lambda r. (1 - r)^(-1/s), "Unif"[0, 1])$ for $s > 0$, giving a Pareto random-weight context supported on $[1, infinity)$.

  These choices are optional context data. In the doctrine below, the measure used for
  graded entailment is the measure on the _context_ $(X, rho_X)$, not a measure on $W$.
]

= A doctrine of Quasi-Borel Spaces

We can now define the doctrine functor:
$
  L colon bold("QProb")^op -> ([0, infinity])_(times.o,plus.o^*)-bold("Pre")
$
whose grading monoid is $[0, infinity]_(plus.o^*)$ and whose enrichment is
$[0, infinity]_(times.o)$. The fibre over a QProb object $(X, rho_X)$ is the set of
$W$-valued quantitative predicates on $X$:

$
  L(X, rho_X) #h(0.3em) := #h(0.3em)
  bold("QBS")((X, M_X), W),
$

i.e. the set of QBS-morphisms $X -> W$. By Proposition 15(1) of @qbs this
coincides with the $Sigma_(M_X)$-measurable functions $X -> [0, infinity]$, so on standard
Borel spaces we recover Capucci's fibres verbatim. Notice that $rho_X$ is not used to
_define_ the set of predicates; it is used only below, when graded entailment integrates
pointwise implication over the context $X$.

== Graded entailment

#remark("The generalized means")[
  If $p$ is a non-zero real number, and ${ x_1, dots, x_n } subset RR_(times.o)$ then the generalized mean or power mean with exponent $p$
  of these positive real numbers is
  $
    M_p (x_1, dots, x_n) := (1/n sum_(i=1)^n x_i^p)^(1/p).
  $
]

#definition("Graded entailment")[
  For $(X, rho_X) in bold("QProb")$ and $phi, psi in L(X, rho_X)$, and a softness $p in (0, infinity)$,
  the _$p$-graded entailment_ is
  $
    phi attach(tack.r.short, tr: rho_X, br: p) psi
    #h(0.3em) := #h(0.3em)
    integral_(x in X)^(-p) (phi multimap psi)(x) dif rho_X (x)
    #h(0.3em) in #h(0.3em) [0, infinity]_(times.o)
  $
]

Unfolding a representative $rho_X = (alpha, mu)$, the expression reduces to:

#v(3em)  // space for the top annotations
$
  phi attach(tack.r.short, tr: rho_X, br: p) psi #h(0.3em) = #h(0.3em)
  markul(integral_(r in RR)^(-p), tag: #<pmean>, color: #blue)
  markul((phi multimap psi), tag: #<impl>, color: #purple)
  (markul(alpha(r), tag: #<probe>, color: #red))
  dif markul(mu(r), tag: #<base>, color: #teal)
  #annot(<impl>, pos: bottom, dy: 1.2em, leader-connect: "elbow")[$psi / phi$]
  #annot(<probe>, pos: bottom, dy: 2.4em, leader-connect: "elbow")[Sample $X$ through a RV]
  #annot(<base>, pos: bottom + right, dy: 1.2em, leader-connect: "elbow")[Base probability on $RR$]
$
#v(3em)  // space for the bottom annotations


== Action on morphisms

For a QProb morphism $f colon (X, rho_X) -> (Y, p_Y)$, the action of $L$ is precomposition:

$
  f^* colon L(Y, p_Y) -> L(X, rho_X)
  f^* (psi) := psi compose f.
$

Well-definedness ($psi compose f$ is a QBS-morphism into $[0, infinity]$) is immediate from
composition in $bold("QBS")$.

== Soft-first-order properties

#lemma("Graded reflexivity")[
  For every $phi in L(X, rho_X)$ and every $p in [0, infinity]$,
  $ phi attach(tack.r.short, tr: rho_X, br: p) phi #h(0.3em) >= #h(0.3em) 1, $
  the unit of $times.o$. Indeed $(phi multimap phi)(x) = 1$ wherever $phi(x) in (0, infinity)$,
  so $ integral_(x in X)^(-p) 1 dif rho_X(x) = 1. $
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#lemma("Graded transitivity (Hölder)")[
  For every $phi, psi, chi in L(X, rho_X)$ and every $p, q in [0, infinity]$,
  $
    (phi attach(tack.r.short, tr: rho_X, br: p) psi)
    #h(0.3em) times.o #h(0.3em)
    (psi attach(tack.r.short, tr: rho_X, br: q) chi)
    quad <= quad
    (phi attach(tack.r.short, tr: rho_X, br: p plus.o^* q) chi).
  $
  Equivalently, the dual generalized Hölder inequality:
  $
    integral_(x in X)^(-p) psi/phi dif rho_X (x)
    #h(0.3em) times.o #h(0.3em)
    integral_(x in X)^(-q) chi/psi dif rho_X (x)
    quad <= quad
    integral_(x in X)^(-p plus.o^* q) chi/phi dif rho_X (x).
  $
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#lemma("Relaxation")[
  For every $phi, psi in L(X, rho_X)$ and every $p, q in [0, infinity]$ with $p <= q$,
  $
    phi attach(tack.r.short, tr: rho_X, br: q) psi
    #h(0.3em) <= #h(0.3em)
    phi attach(tack.r.short, tr: rho_X, br: p) psi.
  $
  This is monotonicity of $L^q$-norms in $q$ on a probability space, applied to the QBS
  integration on $(X, rho_X)$ via its reduction to $(RR, mu)$.
  \
  Proof.

  #text(fill: colors.emerald, "TODO")
]

#lemma("Pullback preserves entailment")[
  For every morphism $f colon (X, rho_X) -> (Y, p_Y)$ in $bold("QProb")$ and every
  $psi_1, psi_2 in L(Y, p_Y)$,
  $
    psi_1 attach(tack.r.short, tr: p_Y, br: p) psi_2
    #h(0.3em) <= #h(0.3em)
    f^* psi_1 attach(tack.r.short, tr: rho_X, br: p) f^* psi_2.
  $

  Proof.

  #text(fill: colors.emerald, "TODO")
]

== Quantifiers as projection adjoints

#theorem("Projection adjoints")[
  For objects $(X, rho_X), (Y, p_Y) in bold("QProb")$ and softness $p in (0, infinity)$,
  reindexing along the projection from the independent tensor context
  $pi_X colon (X, rho_X) ⊗ (Y, p_Y) = (X times Y, rho_X times.o p_Y) -> (X, rho_X)$
  $
    pi_X^* colon L(X, rho_X) -> L(X times Y, rho_X times.o p_Y)
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
    exists_(pi_X)^p theta attach(tack.r.short, tr: rho_X, br: p) phi
    #h(0.3em) <==> #h(0.3em)
    theta attach(tack.r.short, tr: rho_X times.o p_Y, br: p) pi_X^* phi,
  $
  and dually for $forall_(pi_X)^p$.
  \
  Proof.

  We argue the left-adjoint equivalence; the right-adjoint is dual, with the roles of
  $integral^p$ and $integral^(-p)$ exchanged.

  Unfolding graded entailment turns the two sides of the claim into
  $
    (exists_(pi_X)^p theta) attach(tack.r.short, tr: rho_X, br: p) phi
    & = integral_X^(-p) ((integral_Y^p theta(x, y) dif p_Y) multimap phi(x)) dif rho_X, \
    theta attach(tack.r.short, tr: rho_X times.o p_Y, br: p) pi_X^* phi
    & = integral_(X times Y)^(-p) (theta(x, y) multimap phi(x)) dif (rho_X times.o p_Y).
  $

  Since $rho_X times.o p_Y$ is the product measure on the independent tensor context,
  ordinary Fubini--Tonelli applied to the non-negative integrand $G^(-p)$, where
  $G(x, y) := theta(x, y) multimap phi(x)$, lets us decompose the joint integral as an
  iterated one:
  $
    integral_(X times Y)^(-p) G dif (rho_X times.o p_Y) & = (integral_X integral_Y G^(-p) dif p_Y dif rho_X)^(-1/p) \
                                                        & = integral_X^(-p) integral_Y^(-p) G dif p_Y dif rho_X.
  $

  It remains to compare the inner integrals fibrewise. For each fixed $x in X$ we claim
  $
    (integral_Y^p theta(x, y) dif p_Y) multimap phi(x)
    = integral_Y^(-p) (theta(x, y) multimap phi(x)) dif p_Y.
  $
  Indeed, residuation in $([0, infinity], times.o)$ is division, $a multimap b = b slash a$,
  and $phi(x)$ is constant in $y$, so both sides evaluate to
  $phi(x) dot (integral_Y theta^p dif p_Y)^(-1/p)$: the left side directly by definition of
  $integral^p$, and the right side after pulling the $y$-constant $phi(x)^(-p)$ out of the
  inner integral,
  $
    (integral_Y (phi(x) slash theta)^(-p) dif p_Y)^(-1/p)
    = (phi(x)^(-p) integral_Y theta^p dif p_Y)^(-1/p)
    = phi(x) dot (integral_Y theta^p dif p_Y)^(-1/p).
  $

  Chaining the two displays inside the outer $integral_X^(-p)(-) dif rho_X$,
  $
    integral_X^(-p) ((exists_(pi_X)^p theta) multimap phi) dif rho_X
    & = integral_X^(-p) integral_Y^(-p) (theta multimap pi_X^* phi) dif p_Y dif rho_X \
    & = integral_(X times Y)^(-p) (theta multimap pi_X^* phi) dif (rho_X times.o p_Y),
  $
  whose leftmost and rightmost terms are precisely the two graded entailments of the claim.

  For the right adjoint, the same chain applies once $(star)$ is replaced by its dual
  $
    phi(x) multimap (integral_Y^(-p) theta(x, y) dif p_Y)
    = integral_Y^(-p) (phi(x) multimap theta(x, y)) dif p_Y,
  $
  which again reduces to factoring the $y$-constant $1 slash phi(x)$ through the
  $L^(-p)$-integral.
]

#remark("Higher-order layer from QBS")[
  The functor
  $ L colon bold("QProb")^op -> ([0, infinity])_(times.o,plus.o^*)-bold("Pre") $
  is best regarded as a soft _monoidal/affine_ doctrine over measured QBS contexts,
  not as an ordinary cartesian hyperdoctrine: context extension in $bold("QProb")$ is
  the independent tensor above, not a categorical product. Cartesian closure of
  $bold("QBS")$ gives the higher-order structure: for every QBS $X$, the predicate
  object
  $
    bold("Pred")(X) := W^X
  $
  exists in $bold("QBS")$, and evaluation
  $bold("Pred")(X) times X -> W$ is a QBS-morphism.

  However, $bold("Pred")(X)$ is not canonically an object of $bold("QProb")$; making it a
  probabilistic context would require an additional choice of measure
  $rho_(bold("Pred")(X)) in P(W^X)$. Consequently, soft quantification over predicates is
  measure-dependent and is not part of the canonical truth-value structure. Without such
  an extra measure, quantification over predicates should be understood in the ambient
  QBS higher-order layer, not as a canonical QProb soft quantifier.
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

== Universal

#align(center)[
  #prooftree(rule(
    name: $forall^q "R"$,
    $x :^p X, y :^q Y | Gamma attach(tack.r, tr: rho) theta, Delta$,
    $x :^p X | Gamma attach(tack.r, tr: rho) forall^q y : Y . theta, Delta$,
  ))

  #v(0.8em)

  #prooftree(rule(
    name: $forall^q "L"$,
    $x :^p X, y :^q Y | Gamma, theta attach(tack.r, tr: rho) Delta$,
    $x :^p X | Gamma, forall^q y : Y . theta attach(tack.r, tr: rho) Delta$,
  ))
]

Side condition: $y$ does not appear free in $Gamma, Delta$.
Soundness: $forall^q_(pi_X)$ is the $q$-graded right adjoint to $pi_X^*$.

== Leibniz equivalence

Since $bold("Pred")(X) = W^X$ lives canonically in $bold("QBS")$ but not canonically in
$bold("QProb")$, the Leibniz formulation should first be read as an extensional principle
in the QBS higher-order layer:

$ forall x. forall y. x attach(=, br: X) y equiv forall phi in bold("QBS")(X, W). phi(x) multimap.double phi(y) $

If one wants to read the quantifier over $phi$ as a soft QProb quantifier, one must first
choose an additional probability measure on $W^X$; the resulting equality notion is then
relative to that chosen measure.

#v(1em)

#align(center)[
  #prooftree(rule(
    name: $"eq-i"$,
    $x :^p X | Gamma attach(tack.r, tr: rho) Delta$,
    $x :^p X | Gamma attach(tack.r, tr: rho) r(x = x), Delta$,
  ))
]

#v(0.5em)

#align(center)[
  #prooftree(rule(
    name: $"eq-e"$,
    $Gamma, x :^r A | Psi attach(tack.r, tr: rho) phi$,
    $Delta attach(tack.r, tr: rho) u : A$,
    $Delta attach(tack.r, tr: rho) v : A$,
    $Gamma, r Delta | Psi[u\/x], r(u = v) attach(tack.r, tr: rho) phi[v\/x]$,
  ))
]




#bibliography("bibliography.bib")




