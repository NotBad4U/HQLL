#import "lib.typ": *

#import "@preview/cetz:0.4.2"
#import "@preview/showybox:2.0.4": showybox


#let abstract = ""

#show: para-lipics.with(
  title: [∞-Dyck paths and Interval temporal logics],
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


= Preliminaries: Quasi-Borel Spaces

The standard measure-theoretic formalization of probability theory is built on
the category *Meas* of measurable spaces and measurable functions.
While adequate for most classical purposes, this category fails to accommodate
higher-order probabilistic reasoning: as shown by Aumann @Aumann1961BorelSF, *Meas* is
not cartesian closed, and in particular there is no measurable space of
functions $RR -> RR$ @qbs. Quasi-Borel spaces @qbs provide a convenient category in which probability distributions, higher-order functions, and continuous sample spaces coexist.

The guiding intuition is a shift of emphasis. In the traditional setting one
fixes a sample space $(Omega, Sigma_Omega)$ and studies random variables,
i.e. measurable maps $Omega -> X$. The $sigma$-algebra $Sigma_X$ on the
target plays only an auxiliary role, constraining which maps count as
measurable. Quasi-Borel spaces take the set of admissible random variables as
primitive, fixing the sample space once and for all to be $RR$, one of the
best-behaved standard Borel spaces.

#definition("Quasi-Borel space")[
  A _quasi-Borel space_ is a pair $(X, M_X)$ consisting of a set $X$ together
  with a set $M_X subset.eq [RR -> X]$ of functions, called _random elements_
  of $X$, satisfying:
  + if $alpha in M_X$ and $f colon RR -> RR$ is measurable, then
    $alpha compose f in M_X$;
  + every constant function $alpha colon RR -> X$ belongs to $M_X$;
  + if $RR = union.plus.big_(i in NN) S_i$ is a partition into Borel sets and
    $alpha_1, alpha_2, dots in M_X$, then the function $beta$ defined by
    $beta(r) = alpha_i (r)$ for $r in S_i$ is also in $M_X$.
]

The first condition says that $M_X$ is closed under measurable reparametrization
of the sample space; the second guarantees that every point of $X$ is observable
as a (constant) random element; and the third provides the piecewise-gluing
required to make $M_X$ behave like a $sigma$-algebra of random variables.

#observation("Canonical examples")[
  Every measurable space $(X, Sigma_X)$ induces a quasi-Borel space
  $(X, M_(Sigma_X))$, where $M_(Sigma_X)$ is the set of measurable functions
  $RR -> X$. In particular:
  - $RR$ is a quasi-Borel space with $M_RR$ the measurable maps $RR -> RR$;
  - the two-element discrete space $2$ is a quasi-Borel space whose random
    elements are exactly the characteristic functions of Borel subsets of $RR$.
]


#definition("Category of quasi-Borel spaces")[
  The _category of quasi-Borel spaces_ $bold("QBS")$ is defined as follows:
  - Objects: quasi-Borel spaces
    $ (X, M_X) $  where $M_(Sigma_X)$ is the set of measurable functions $RR -> X$;
  - Morphisms:
    $(X, M_X) -> (Y, M_Y)$ is a function $f colon X -> Y$ such that $f compose alpha in M_Y$ whenever $alpha in M_X$.
    Morphisms compose as functions, and identity functions are morphisms.
]

Morphisms between quasi-Borel spaces are analogous to measurable functions between measurable space in *Meas*.
We can for example integrate over them. Integration against $(alpha, mu)$ reduces to
integration on $RR$ for any morphism $f colon (X, M_X) -> RR$:
$
  integral f dif (alpha, mu) #h(0.4em) eq.def #h(0.4em)
  integral_RR (f compose alpha) dif mu.
$

Unlike *Meas*, the category *QBS* is cartesian closed @qbs. Given the quasi-Borel spaces $(X, M_X)$ and $(Y, M_Y)$, the exponential $Y^X$ has as
underlying set the hom-set $bold("QBS")((X, M_X), (Y, M_Y))$ of morphisms, equipped with the random elements
$
  M_(Y^X) eq.def { alpha colon RR -> Y^X #h(0.3em) | #h(0.3em)
    "uncurry"(alpha) in bold("QBS")(RR times X, Y) },
$
so that a random element of $Y^X$ is exactly a random function $RR times X -> Y$.
The evaluation map $Y^X times X -> Y$ is then a morphism with the expected universal property.
Cartesian closure is what recovers function spaces such as $RR^RR$, which have no counterpart in *Meas*, and is the structural feature that lets $bold("QBS")$ serve as a semantic domain for higher-order probabilistic programs.


= A doctrine of Quasi-Borel Spaces

We fix a Borel probability measure $mu in P(RR)$, one may take $mu$ to be the uniform distribution on the unit interval $[0, 1]$ without loss of generality.

#observation()[
  A probability measure on a quasi-Borel space $(X, M_X)$ is a pair $(alpha, mu)$ of $alpha in M_X$ and a probability measure $mu$ on $RR$.
]

Consider now the sets $L(X, M_X)$ of "QBS" morphisms $(X, M_X) -> [0, infinity]$, where $[0, infinity]$ is the quasi-Borel space with underlying set $[0, infinity]$ and random elements the measurable functions $RR -> [0, infinity]$. For each $p in (0 , + infinity)$ define

$
  phi scripts(tack.r.short)^mu_p psi := and.big_(alpha in M_X) integral_(x \in RR)^(-p) psi(x) multimap psi(i) dot mu(x)
$

This definitions satisfies the following properties:

TODO

#corollary("The higher-order hyperdoctrine of Quasi-Borel Spaces")[
  The higher-order hyperdoctrine of Quasi-Borel Spaces is the functor $L : bold("QBS")^op -> (plus.o^*, times.o) bold("-Prd")$
]


#bibliography("bibliography.bib")


