#import "lib.typ": *

#import "@preview/showybox:2.0.4": showybox
#import "@preview/curryst:0.6.0": prooftree, rule
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
#let ret = math.op("return")
#let smp = math.op("sample")
#let scr = math.op("score")
#let mss = math.op("mass")
#let nrm = math.op("norm")
#let bnd = math.op("bind")
#let pr = math.op("pair")
#let Leb = math.op("Leb")
// The signature of constants.
#let Sig = math.bold(sym.Sigma)
// s-finite kernel arrow, absolute continuity, 0-∞-absolute continuity,
// and the density action of [0,∞]-valued functions on measures.
#let kto = math.class("relation", sym.arrow.r.squiggly)
#let ac = math.class("relation", sym.lt.double)
#let acinf = math.class("relation", math.attach(sym.lt.double, t: sym.infinity))
#let act = math.class("binary", sym.triangle.stroked.r)
// sequencing M ; N inside function calls (a bare ";" would split the arguments)
#let seq = math.class("binary", ";")
// Binder sugar  Q (x ∼ ν). φ  :=  Q ν (λx. φ)
#let qb(Q, x, nu, body) = $#Q thin (#x tilde #nu). thin #body$
#let letin(x, M, N) = $"let" #x <- #M "in" #N$
#let sof = math.bb("S")

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

= Multiplicative Extended Reals $RR_times.o$ <sec:omega>

*Truth values* $Omega = [0,oo]$.

#tb(
  columns: (1fr, auto, auto),
  table.header([*operation*], [*unit*], [*status*]),
  [$a ⊗ b = a b$ #h(1em) ($0 ⊗ oo = 0$)],
  [$1$],
  [primitive],
  [$a ⊕ b = a + b$],
  [$0$],
  [primitive],
  [$a^* = 1 slash a$, #h(0.4em) $0^* = oo$],
  [---],
  [primitive],
  [$a^p$ #h(1em) ($0^p = 0$, #h(0.3em) $oo^p = oo$, #h(0.3em) $p in (0, oo)$)],
  [---],
  [primitive],
  [$a ⊗^* b = a b$ #h(1em) ($0 ⊗^* oo = oo$)],
  [$1$],
  [defined (D2)],
  [$a multimap b = sup{c mid(|) a ⊗ c <= b} = a^* ⊗^* b$],
  [---],
  [defined (D3)],
  [$a ⊕^p b = (a^p + b^p)^(1 slash p)$, #h(0.4em) $a ⊕^(-p) b = (a^(-p) + b^(-p))^(-1 slash p)$],
  [$0$ / $oo$],
  [defined (D4, D5)],
)

The first four operations, together with the elements $0$ and $1$, are the primitive
constants of the signature of @sec:sig; the remaining ones are *defined* from them in
@sec:defs, in the way HOL defines its connectives from $=$, $supset$ and $epsilon$
@gordonmelham1993. The algebraic theory of this structure --- a $*$-autonomous isomix
monoidal poset whose additives come as a family indexed by a softness $p$ --- is worked out
in @capucci2024quantifiers @capucci2026notes; we only use that every identity valid in it
becomes an axiom of the logic (@sec:eqth).

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

= Syntax

We present HQLL in the style of Church's simple theory of types as mechanised in HOL
@church1940 @gordonmelham1993: a simply typed $lambda$-calculus over a *signature* of typed
constants, in which formulas are the terms of type $Omega$ and every logical operator,
quantifiers included, is a constant applied to its arguments; binder notation is sugar. We
follow @jacobsmelham1993 in making contexts explicit, written in the now-standard form
$Gamma tack M : A$ @jacobs1999cltt @harrison2009hollight. Two things differ from HOL. There
is no Hilbert choice operator $epsilon$. And the quantifiers are not defined from equality
(nor from $epsilon$) but *computed*: they are $p$-means of the body against an s-finite
measure, taken through an integration constant, following @capucci2024quantifiers
@capucci2026notes.

== Types

$
  A, B ::= 1 mid(|) RR mid(|) Omega mid(|) A times B mid(|) A -> B mid(|) Dst A
  quad quad quad quad
  Prd A ≔ A -> Omega
$

The type constants are $1$, $RR$ and the type $Omega$ of truth values; the type operators
are $times$, $->$ and the s-finite measure type $Dst$. In HOL the type constants are
$"bool"$ and $"ind"$ and the only operator is $->$. Here $Omega$ plays the role of $"bool"$,
and $RR$ that of $"ind"$: it is standard Borel, and the "one parameter line" lemma of
@sec:prelim makes it the canonical sample space, so no axiom of infinity is needed. There
are no type variables. Constants such as $integral_A$ or $ret_A$ are *families* indexed by
types, and we omit the index whenever it is determined by the arguments, exactly as HOL
instantiates the generic type of a polymorphic constant.

A term of type $Dst A$ denotes an s-finite measure on the space denoted by $A$. The measure
is not required to be normalised: it may be a probability distribution, but also an
unnormalised or infinite measure such as Lebesgue measure on $RR$ (an improper prior), or
the unnormalised posterior computed by a program that uses $scr$. Following
@staton2017commutative, s-finite measures are the smallest class of measures that contains
the probability distributions and is closed under the constructs of the computational
language ($"let"$, $smp$, $scr$); their basic theory is developed in @vakar2026sfinite. The
measure enters the logic only as a *term* of type $Dst A$ --- the argument of a quantifier
--- and never as a decoration of a type. Hence cartesian closure needs no separation of
sorts: $Dst A -> B$, $Dst (A -> B)$ and $Dst Dst A$ are all types, and a predicate on
measures, or a measure on predicates, is nothing special.

== Terms and signature <sec:sig>

$
  M, N ::= x mid(|) c mid(|) M space N mid(|) lambda x : A. space M
  quad quad quad quad (c : A) in Sig
$

Terms are those of the simply typed $lambda$-calculus over the signature $Sig$ of
@tab:sig, whose constants come in families indexed by types $A, B$, by a *softness*
$p in (0, oo)$, by s-finite measures $mu$ and by Borel functions $f$. *Formulas* are the
terms of type $Omega$ and *predicates* on $A$ the terms of type $Prd A$; there is no
separate judgement for either.

#figure(
  tb(
    columns: (auto, auto, 1fr),
    align: (left, left, left),
    table.header([*group*], [*constant*], [*type*]),
    table.cell(rowspan: 3)[unit, product],
    [$ast$],
    [$1$],
    [$pr_(A, B)$],
    [$A -> B -> A times B$],
    [$pi_1$, #h(0.3em) $pi_2$],
    [$A times B -> A$, #h(0.3em) $A times B -> B$],
    [truth values],
    [$0$, #h(0.3em) $1$],
    [$Omega$],
    [multiplicative, additive],
    [$⊗$, #h(0.3em) $⊕$],
    [$Omega -> Omega -> Omega$],
    table.cell(rowspan: 2)[duality, softening],
    [$(-)^*$],
    [$Omega -> Omega$],
    [$(-)^p$ #h(0.4em) ($p in (0, oo)$)],
    [$Omega -> Omega$],
    [integration],
    [$integral_A$],
    [$Dst A -> (A -> Omega) -> Omega$],
    [hard existential],
    [$exists^oo_A$],
    [$Dst A -> (A -> Omega) -> Omega$],
    table.cell(rowspan: 2)[monad],
    [$ret_A$],
    [$A -> Dst A$],
    [$bnd_(A, B)$],
    [$Dst A -> (A -> Dst B) -> Dst B$],
    [measures],
    [$smp_mu$ #h(0.4em) ($mu$ s-finite on $sem(A)$)],
    [$Dst A$],
    table.cell(rowspan: 3)[conditioning],
    [$scr$],
    [$Omega -> Dst 1$],
    [$mss$],
    [$Dst 1 -> Omega$],
    [$nrm_A$],
    [$Dst A -> Dst A$],
    table.cell(rowspan: 2)[arithmetic],
    [$f$ #h(0.4em) (Borel $f : RR^n -> RR$)],
    [$RR -> dots.c -> RR$],
    [$f$ #h(0.4em) (Borel $f : RR^n -> [0, oo]$)],
    [$RR -> dots.c -> Omega$],
  ),
  caption: [The signature $Sig$ of HQLL. Every logical operator is a constant; the
    quantifiers take the measure they average against as their first argument.],
) <tab:sig>

The computation $smp_mu$ draws from a constant s-finite measure $mu$ on $sem(A)$: a
probability distribution, but also Lebesgue measure $Leb$ on $RR$ or counting measure
$\#_NN$ on $NN$ (a constant of the language, as in @staton2017commutative). The soft
constraint $scr(phi)$ multiplies the weight of the current execution by the truth value of
the formula $phi$; its inverse $mss$ reads a measure on the one-point type back as a truth
value. Both are interpreted by the identity, since $Omega$ and $Dst 1$ denote the same
space $[0, oo]$ (@def:sfinite); we nevertheless keep the two types apart, so that the
logical fragment --- connectives, $integral$, $exists^oo$ --- can be read independently of
the computational constants. Arithmetic constants make measurable functions available as
terms, so that e.g. $lambda x : RR. space e^(-x^2 slash 2) : Prd RR$ is a predicate.

== Typing

Contexts $Gamma ::= diamond.small mid(|) Gamma, x : A$ are finite lists of distinct typed
variables. The judgements are $Gamma tack M : A$, "$M$ is a well-typed term of type $A$ in
context $Gamma$", and the equational judgement $Gamma tack M ≡ N : A$ of @sec:eqth. As in
HOL there are exactly four typing rules:

#grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  row-gutter: 14pt,
  prooftree(rule(name: [Var], $Gamma\, x : A\, Gamma' tack x : A$)),
  prooftree(rule(name: [Con], $(c : A) in Sig$, $Gamma tack c : A$)),

  prooftree(rule(name: [Abs], $Gamma\, x : A tack M : B$, $Gamma tack lambda x : A. space M : A -> B$)),
  prooftree(rule(name: [App], $Gamma tack M : A -> B$, $Gamma tack N : A$, $Gamma tack M space N : B$)),
)

Types are unique: a term has at most one type in a given context. Everything that used to
need a rule of its own --- pairing and projections, the connectives, the quantifiers,
$"let"$, $smp$, $scr$ --- is now an instance of Con followed by App. For example, from
$Gamma tack nu : Dst A$ and $Gamma, x : A tack phi : Omega$ one derives
$Gamma tack integral_A space nu space (lambda x : A. space phi) : Omega$ by Con, Abs and two
applications of App. There is no binding rule for quantifiers, no grade on the bound
variable, and no well-formedness judgement for types or contexts: types are generated by
the grammar and contexts are lists.

== Definitions and notation <sec:defs>

HOL builds $top, forall, exists, bot, not, and, or$ from the three primitives $=$,
$supset$ and $epsilon$ by *definitions* $tack c = M$, each introducing a new constant
@gordonmelham1993. We do the same, without $epsilon$: each line below adds a constant to
$Sig$ with the displayed type, together with the equation $c ≡ M$ (@sec:eqth). Throughout,
$p in (0, oo)$ unless stated otherwise, and $lambda a b. space M$ abbreviates
$lambda a. space lambda b. space M$.

#defbox([Definitions])[
  $
    "D1" quad & oo & ≔ 0^* & : Omega \
    "D2" quad & ⊗^* & ≔ lambda a b. space (a^* ⊗ b^*)^* & : Omega -> Omega -> Omega \
    "D3" quad & multimap & ≔ lambda a b. space (a ⊗ b^*)^* quad (= a^* ⊗^* b) & : Omega -> Omega -> Omega \
    "D4" quad & ⊕^p & ≔ lambda a b. space (a^p ⊕ b^p)^(1 slash p) & : Omega -> Omega -> Omega \
    "D5" quad & ⊕^(-p) & ≔ lambda a b. space (a^* ⊕^p b^*)^* & : Omega -> Omega -> Omega \
    "D6" quad & exists^p_A & ≔ lambda nu u. space (integral_A space nu space (lambda x. space (u space x)^p))^(1 slash p) & : Dst A -> (A -> Omega) -> Omega \
    "D7" quad & forall^p_A & ≔ lambda nu u. space (exists^p_A space nu space (lambda x. space (u space x)^*))^* & : Dst A -> (A -> Omega) -> Omega quad (p in (0, oo])
  $
]

D3 is the place where HOL defines $exists P$ as $P (epsilon P)$. Here the existential is
instead *computed*: D6 says that $exists^p_nu u$ is the $L^p (nu)$-norm of $u$, an
arithmetic $p$-mean when $nu$ is a probability measure, and D7 makes $forall^p$ its De
Morgan dual, the harmonic $p$-mean, exactly as in @capucci2024quantifiers. Both are
definable from the single integration constant $integral_A$ because
$(a^*)^p = (a^p)^* = a^(-p)$ and $(t^(1 slash p))^* = t^(-1 slash p)$ hold in $[0, oo]$,
including at the corners $0^* = oo$, $0^p = 0$, $oo^p = oo$; hence
$forall^p_nu u = (integral u^(-p) dif nu)^(-1 slash p)$ (@lem:dendef). The hard existential
$exists^oo$ (essential supremum) remains primitive: it is the limit of $exists^p$ only for
measures of finite mass --- $exists^p_Leb 1 = oo$ for every $p < oo$ while
$exists^oo_Leb 1 = 1$ --- so it is not a term in the other constants. D7 at $p = oo$ gives
$forall^oo_nu u = (exists^oo_nu u^*)^*$, the essential infimum.

*Notation.* We use the following abbreviations; each right-hand side is an official term.

- $⟨M, N⟩ ≔ pr space M space N$, and, for $M : Dst A$,
  $"let" x <- M "in" N ≔ bnd space M space (lambda x : A. space N)$ @moggi1991, with
  $M ; N ≔ "let" x <- M "in" N$ for $x$ fresh.
- Infix and postfix notation for the $Omega$-constants: $phi ⊗ psi$, $phi ⊕^p psi$,
  $phi multimap psi$, $phi^*$, $phi^p$.
- *Binders.* For any constant $Q : Dst A -> (A -> Omega) -> Omega$ --- in particular
  $integral_A$, $exists^p_A$ and $forall^p_A$ ---
  $
    Q space (x tilde nu). space phi quad ≔ quad Q space nu space (lambda x : A. space phi),
  $
  read "$Q$ over $x$ drawn from $nu$". The type of $x$ is determined by $nu : Dst A$ and
  is omitted. We write $integral_(x tilde nu) phi$ for the integral binder,
  $EE_(x tilde nu)[phi]$ as a synonym when $nu$ is a probability measure, and $x tilde mu$
  for $x tilde smp_mu$ when $mu$ is a constant measure. The term $nu$ may contain free
  variables of the context: $Gamma tack nu : Dst A$ is then a *kernel*, and
  $forall^p (x tilde nu). forall^q (y tilde kappa space x). phi$ quantifies $y$ along the
  kernel $kappa : A -> Dst B$ at the point $x$.

This is exactly HOL's reading of $forall x : sigma. space phi$ as
$forall (lambda x : sigma. space phi)$, with one more argument. Compared with a
presentation in which the bound variable ranges over a *measured type* $A_omega$, the
binder $forall^p (x : A_omega). phi$ becomes $forall^p (x tilde omega). phi$ with
$omega : Dst A$ an ordinary term, and the softness $p$ is an index of the constant rather
than a grade on the bound variable.

== Equational theory <sec:eqth>

The judgement $Gamma tack M ≡ N : A$ is the least congruence --- reflexive, symmetric,
transitive, closed under Abs and App --- containing the definitional equations of
@sec:defs and the axioms below. It plays the role of HOL's axioms and conversion rules. The
inequational part of the logic, graded entailment, is not treated here (@sec:quasitripos).

*Cartesian closed structure.*

#grid(
  columns: (1fr, 1fr),
  column-gutter: 16pt,
  row-gutter: 7pt,
  align: left,
  $(lambda x : A. space M) space N ≡ M[N slash x]$, $pi_i ⟨M_1, M_2⟩ ≡ M_i$,
  $lambda x : A. space (M space x) ≡ M quad (x in.not "FV"(M))$, $⟨pi_1 M, pi_2 M⟩ ≡ M$,
  $M ≡ ast quad (M : 1)$, [],
)

*Monad laws* @moggi1991*, with commutativity.*

#grid(
  columns: (1fr, 1fr),
  column-gutter: 16pt,
  row-gutter: 7pt,
  align: left,
  $"let" x <- ret M "in" N ≡ N[M slash x]$, $"let" x <- M "in" ret x ≡ M$,
)

$
  "let" y <- ("let" x <- M "in" N) "in" P & ≡ "let" x <- M "in" "let" y <- N "in" P, \
    "let" x <- M "in" "let" y <- N "in" P & ≡ "let" y <- N "in" "let" x <- M "in" P,
$
with $x in.not "FV"(P)$ in the first equation (associativity) and $x in.not "FV"(N)$,
$y in.not "FV"(M)$ in the second. The second equation is *commutativity*: the order of independent computations is
immaterial. It is sound because the s-finite monad is commutative
(@vakar2026sfinite[Thm. 19], @staton2017commutative), and it is the equation that fails for
general (non s-finite) measures, where Fubini's theorem is unavailable.

*Score and mass.*
$
  scr(1) ≡ ret ast, quad quad scr(phi) seq scr(psi) ≡ scr(phi ⊗ psi), \
  mss(scr(phi)) ≡ phi, quad quad scr(mss(m)) ≡ m .
$

*Truth-value identities.* For every identity $s = t$ between terms built from variables
and $0, 1, ⊗, ⊕, (-)^*, (-)^p$ that holds at *all* points of $[0, oo]$ under the
conventions $0 ⊗ oo = 0$ and $0^* = oo$ (@sec:omega; @capucci2026notes[Def. 2.1 and
  Lemmas 2.19--2.20]),
$
  Gamma tack s[arrow(phi)] ≡ t[arrow(phi)] : Omega .
$
Thus $a ⊗ (b ⊕ c) ≡ (a ⊗ b) ⊕ (a ⊗ c)$, $(a^*)^* ≡ a$ and $(a ⊗ b)^p ≡ a^p ⊗ b^p$ are
axioms, whereas $a ⊗ a^* ≡ 1$ is not: it fails at $0$ and at $oo$. This schema is
Capucci's "structural schema" @capucci2026notes[§7.2] and replaces HOL's axioms for
$"bool"$ (two truth values, antisymmetry of implication): $Omega$ is a Girard quantale,
not a two-element Boolean algebra.

*Integration.* Where HOL has the axiom of choice for $epsilon$, we have three axioms for
$integral$:
$
  ("∫-prog") quad & integral_(x tilde nu) phi ≡ mss("let" x <- nu "in" scr(phi)) \
   ("∫-lin") quad & integral_(x tilde nu) (phi ⊕ psi) ≡ integral_(x tilde nu) phi ⊕ integral_(x tilde nu) psi \
  ("∫-zero") quad & integral_(x tilde nu) 0 ≡ 0
$
The first says that *quantifying is running a program*: integrating $phi$ against $nu$ is
sampling $x$ from $nu$, scoring by $phi$ and reading off the mass. The other two are
additivity of the integral, which no monad law provides. Everything else follows.

#lemma([Derived integration laws])[
  The following equations are derivable, with $x in.not "FV"(phi)$ in ∫-bind and
  $x in.not "FV"(psi)$ in ∫-hom:
  $
      ("∫-ret") quad & integral_(x tilde ret M) phi ≡ phi[M slash x] \
     ("∫-bind") quad & integral_(y tilde ("let" x <- M "in" N)) phi ≡ integral_(x tilde M) integral_(y tilde N) phi \
    ("∫-score") quad & integral_(x tilde scr(psi)) phi ≡ psi ⊗ phi[ast slash x] \
      ("∫-hom") quad & integral_(x tilde nu) (psi ⊗ phi) ≡ psi ⊗ integral_(x tilde nu) phi \
     ("Fubini") quad & integral_(x tilde nu) integral_(y tilde rho) phi ≡ integral_(y tilde rho) integral_(x tilde nu) phi
  $
  #proof[
    Unfold ∫-prog. For ∫-ret use the left unit law and $mss compose scr ≡ "id"$. For
    ∫-bind, associativity moves the outer $"let"$ inside, and
    $scr(phi) ≡ scr(mss("let" y <- N "in" scr(phi)))$ by $scr compose mss ≡ "id"$. For
    ∫-score, $phi ≡ phi[ast slash x]$ since $x : 1$, then the score law and
    $mss compose scr ≡ "id"$. For ∫-hom, $scr(psi ⊗ phi) ≡ scr(psi) seq scr(phi)$,
    commutativity moves $scr(psi)$ out of the $"let"$ because $x in.not "FV"(psi)$, and
    $scr(psi) seq m ≡ scr(psi ⊗ mss(m))$ by the score laws. Fubini is commutativity.
  ]
]

#remark[
  Two things are deliberately absent. There is no *discard* law
  $"let" y <- N "in" M ≡ M$: it is unsound for unnormalised $N$, since discarding a factor
  scales the result by its mass (@lem:marginals). And $nrm$ has no axiom: normalisation is
  partial (zero and infinite masses), so its behaviour is fixed only semantically
  (@def:normalise). Inequalities --- Hölder, Minkowski, monotonicity of $p$-means in $p$,
  mass scaling (@lem:mass) --- are the business of graded entailment, not of $≡$.
]

= Semantics

== Preliminaries <sec:prelim>

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
      |T X| & = { [alpha, mu] mid(|) alpha in M_X, space mu "s-finite on" RR } slash ~, \
    M_(T X) & = { r |-> [alpha, k(r, -)] mid(|) alpha in M_X, space k : RR kto RR "an s-finite kernel" }.
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
  - *Strength* $"st"_(X, Y)(x, [alpha, mu]) := [lambda r. (x, alpha(r)), space mu]$, and
    symmetrically the costrength $"st"'_(X, Y) : T X times Y -> T(X times Y)$.
  - *Double strength.* For $nu = [alpha, mu] in T X$ and $rho = [beta, mu'] in T Y$ the
    product measure is $nu ⊗ rho := [alpha times beta, space mu ⊗ mu'] in T(X times Y)$,
    the double strength of the commutative monad $T$ @vakar2026sfinite[Thm. 19]. Here
    $mu ⊗ mu'$ is the product of s-finite measures on $RR^2$ defined by iterated
    integration; the order of integration is immaterial by the limited Fubini theorem for
    s-finite kernels (@staton2017commutative, @vakar2026sfinite[Thm. 4]). It interprets
    $"let" x <- M "in" "let" y <- N "in" ret ⟨x, y⟩$, and may differ from the maximal
    (Carathéodory) product, which we never use.
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

== Types and contexts

We define the semantics of types recursively as follows:

#grid(
  columns: (1fr, 1fr, 1fr),
  align: center,
  row-gutter: 10pt,
  $sem(1) = 1$, $sem(RR) = RR$, $sem(Omega) = [0,oo] = T 1$,
  $sem(A times B) = sem(A) times sem(B)$, $sem(A -> B) = sem(B)^(sem(A))$, $sem(Dst A) = T sem(A)$,
) <eq:types>

where $[0, oo]$ is standard Borel with $M_Omega = {"Borel" RR -> [0, oo] }$; in particular
$sem(Prd A) = Omega^(sem(A))$ and $sem(Omega) = sem(Dst 1)$. A context is interpreted by
the cartesian product in $"QBS"$,
$
  sem(x_1 : A_1\, dots\, x_n : A_n) := sem(A_1) times dots.c times sem(A_n),
$ <eq:ctx>
the terminal object $1$ for the empty context. This is the standard interpretation of a
simply typed $lambda$-calculus in a cartesian closed category @jacobs1999cltt: no measure
and no grade is attached to a context. Measures live in the terms of type $Dst A$, and
grades in the entailment layer (@sec:quasitripos).

== Terms <sec:terms>

The interpretation of $Gamma tack M : A$ is a morphism
$sem(Gamma tack M : A) : sem(Gamma) -> sem(A)$ of $"QBS"$, defined by four clauses:

#grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 10pt,
  $sem(x_i) = pi_i$, $sem(c) = sem(c) compose !_(sem(Gamma))$,
  $sem(lambda x : A. space M) = cur (sem(Gamma\, x : A tack M))$, $sem(M space N) = ev compose ⟨ sem(M), sem(N) ⟩$,
) <eq:term-sem>

Here $sem(c) : 1 -> sem(A)$ is the global element assigned to the constant $c$ in
@sec:consts, $cur : "QBS"(Z times X, Y) -> "QBS"(Z, Y^X)$ is currying and
$ev : Y^X times X -> Y$ evaluation. Substitution is composition:
$sem(M[N slash x]) = sem(M) compose ⟨ "id", sem(N) ⟩$; in particular, for
$Gamma, x : A tack psi : Omega$ one has $sem(lambda x : A. space psi) = cur (sem(psi))$,
which curries the $A$-argument and keeps the free variables of $Gamma$.

#lemma([The sugar denotes what it used to])[
  Put $sem(bnd) := ev^dagger compose "st"' : T X times (T Y)^X -> T Y$, so that pointwise
  $sem(bnd)(nu, f) = f^dagger (nu)$. Then
  $
    sem("let" x <- M "in" N) = sem(N)^dagger compose "st" compose ⟨ "id", sem(M) ⟩,
  $
  the strong-monad interpretation of $"let"$; moreover $sem(scr(phi) seq M) = sem(phi) dot sem(M)$
  and, for $u : Prd A$, $sem("let" x <- M "in" scr(u space x) seq ret x) = sem(M) act sem(u)$.
  #proof[
    $sem(bnd space M space (lambda x. N)) = ev^dagger compose "st"' compose ⟨ sem(M), cur sem(N) ⟩
    = (ev compose ("id" times cur sem(N)))^dagger compose "st"' compose ⟨ sem(M), "id" ⟩$ by
    naturality of the costrength, and $ev compose ("id" times cur sem(N)) = sem(N) compose "swap"$,
    with $"st"' = T("swap") compose "st" compose "swap"$. The remaining identities are the
    density action of @def:sfinite: $sem(scr(phi))(g) = sem(phi)(g) dot delta_ast$, so
    scoring is reweighting.
  ]
]

In kernel notation,
$
  sem("let" x <- M "in" N)(g, V) = integral_(sem(A)) sem(M)(g, dif x) space sem(N)((g, x), V),
$
the composition of s-finite kernels of @staton2017commutative.

== Interpretation of the constants <sec:consts>

Every constant $(c : A) in Sig$ is interpreted by a global element $sem(c) : 1 -> sem(A)$,
which we describe as an element of $|sem(A)|$ or, for constants of function type, as the
corresponding morphism.

*Truth values and connectives.* The constants of type $Omega$ denote the elements $0$ and
$1$ of $[0, oo]$, and the primitive connectives the Borel maps
#grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(⊗)(a, b) = a b quad (0 dot oo = 0)$, $sem(⊕)(a, b) = a + b$,
  $sem((-)^*)(a) = 1 slash a quad (1 slash 0 = oo)$, $sem((-)^p)(a) = a^p quad (0^p = 0, space oo^p = oo)$,
)
Every Borel map $[0, oo]^n -> [0, oo]$ is a $"QBS"$ morphism $Omega^n -> Omega$, so each
fibre $Omega^X$ is closed under the whole signature and reindexing along any morphism
$X -> Y$ commutes with it strictly; the connectives act *pointwise* on formulas.

*Integration.*

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

The primitive constant $integral_A$ is interpreted by $I_(sem(A))$, curried:
$sem(integral_A) : T X -> Omega^(Omega^X)$, $nu |-> I_X (nu, -)$ with $X = sem(A)$. This is
precisely the embedding of $T X$ into the continuation monad of @def:sfinite --- the
primitive of the logic identifies a measure with its integration functional.

*Hard existential.* $sem(exists^oo_A)(nu, u) := esssup_nu u$, the essential supremum of
$u$ with respect to (the push-forward on $Sigma_(M_X)$ of) $nu$.

#lemma([Essential suprema are morphisms])[
  $(nu, u) |-> esssup_nu u$ is a $"QBS"$ morphism $T X times Omega^X -> Omega$.
  #proof[
    $esssup_nu u = inf { c in QQ_(>= 0) mid(|) nu(u > c) = 0 }$, since the set of all
    such $c in [0, oo]$ is upward closed (with $inf emptyset = oo$). Along a random
    element $r |-> ([alpha, k(r, -)], u(r, -))$ as in @lem:integration, the set
    $B_c := { (r, r') mid(|) u(r, alpha(r')) > c }$ is Borel in $RR^2$, and
    $r |-> k(r, (B_c)_r) = (k act bb(1)_(B_c))(r, RR)$ is measurable by
    @vakar2026sfinite[Thm. 5(3)]. Hence $f_c (r) := c$ if $k(r, (B_c)_r) = 0$ and
    $f_c (r) := oo$ otherwise is measurable, and the composite $inf_(c in QQ_(>= 0)) f_c$
    is a countable infimum of measurable maps.
  ]
]

Two caveats. $esssup_nu$ is *not* the limit of the $L^p (nu)$ norms unless $nu$ has finite
mass (for $u = 1$ and $nu = Leb$ the norms are all $oo$ while the essential supremum is
$1$), which is why $exists^oo$ is a primitive rather than a definition. And
$esssup_0 u = 0$ for the zero measure, so $forall^oo (x tilde nu). phi$ denotes $oo$ when
$nu$ denotes $0$: universal quantification over nothing is vacuously true, as it should be.

*Monadic and arithmetic constants.*
#grid(
  columns: (1fr, 1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(ret) = eta$, $sem(bnd) = ev^dagger compose "st"'$, $sem(smp_mu) = mu in |T sem(A)|$,
  $sem(scr) = sem(mss) = "id"_([0, oo])$, $sem(nrm) = "normalise"$, $sem(f) = f$,
)
using $sem(Omega) = T 1 = [0, oo]$ for $scr$ and $mss$, and the fact that Borel maps between
standard Borel spaces are $"QBS"$ morphisms for $f$. The constants $ast$, $pr$, $pi_i$
denote the cartesian structure of $"QBS"$.

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
  $times$), then $sem(Gamma)$ and $sem(A)$ are standard Borel and
  $sem(Gamma tack M : Dst A) in Qbs(sem(Gamma), T sem(A))$ is precisely an s-finite
  kernel $sem(Gamma) kto sem(A)$ @vakar2026sfinite[Cor. 2]. On this fragment the
  semantics is that of @staton2017commutative; the monad $T$ extends it to higher types
  and to the predicate types $Prd A$ over which the logic quantifies. In particular the
  measure argument $Gamma tack nu : Dst A$ of a quantifier is an s-finite kernel from the
  context to the domain of quantification.
] <prop:kernels>

#lemma([Denotation of the defined constants])[
  The definitions D1--D7 denote: $sem(oo) = oo$; $sem(⊗^*)(a, b) = a b$ with
  $0 ⊗^* oo = oo$; $sem(multimap)(a, b) = sup { c mid(|) a c <= b }$, the residual of
  $⊗$, with $0 multimap 0 = oo$ and $oo multimap b = 0$ for $b < oo$;
  $sem(⊕^(plus.minus p))$ as in @sec:omega; and, writing $u^(plus.minus p)$ for
  post-composition with $t |-> t^(plus.minus p)$ on $[0, oo]$,
  $
    sem(exists^p_A)(nu, u) = (I_X (nu, space u^p))^(1 slash p), quad quad
    sem(forall^p_A)(nu, u) = (I_X (nu, space u^(-p)))^(-1 slash p),
  $
  and $sem(forall^oo_A)(nu, u) = essinf_nu u$. These are the soft quantifiers of
  @capucci2024quantifiers: the $L^p (nu)$ norm of $u$ and the reciprocal $L^p (nu)$ norm of
  $u^*$, which are means only when $nu$ is a probability measure.

  #align(center)[
    #commutative-diagram(
      node((0, 0), $T X times Omega^X$),
      node((0, 1), $T X times Omega^X$),
      node((1, 1), $Omega$),
      node((1, 0), $Omega$),
      arr((0, 0), (0, 1), $"id" times (-)^(-p)$),
      arr((0, 1), (1, 1), $I_X$),
      arr((1, 1), (1, 0), $(-)^(-1 slash p)$, label-pos: right),
      arr((0, 0), (1, 0), $sem(forall^p)$, label-pos: right),
    )]
  #proof[
    Unfold D1--D7 through @sec:terms and use the pointwise identities
    $(a^*)^p = a^(-p)$ and $(t^(1 slash p))^* = t^(-1 slash p)$, valid at $0$ and $oo$; for
    $forall^oo$, $(esssup_nu u^*)^* = essinf_nu u$ with the same conventions.
  ]
] <lem:dendef>

== Soundness

#proposition([Soundness of the equational theory])[
  If $Gamma tack M ≡ N : A$ then $sem(M) = sem(N) : sem(Gamma) -> sem(A)$.
  #proof[
    By induction on derivations. The clauses of @sec:terms are compositional, so the
    congruence rules are preserved and it suffices to check the axioms.
    - *Cartesian closed laws*: $"QBS"$ is cartesian closed.
    - *Monad laws and commutativity*: $T$ is a commutative monad (@def:sfinite);
      commutativity is the limited Fubini theorem for s-finite kernels
      (@staton2017commutative, @vakar2026sfinite[Thm. 4]).
    - *Score and mass*: $sem(scr) = sem(mss) = "id"$, and
      $sem(scr(phi) seq scr(psi)) = sem(phi) sem(psi) dot delta_ast$ by the density action.
    - *Truth-value identities*: the connectives are interpreted pointwise, so an identity
      valid at all points of $[0, oo]$ holds between the composites.
    - *∫-prog*: $I_X (nu, u) = (nu act u)(|X|) = sem("let" x <- nu "in" scr(u space x))$,
      the density action of @def:sfinite read as a measure on the one-point space, and
      $mss$ is the identity.
    - *∫-lin, ∫-zero*: the integral is additive and $integral 0 space dif nu = 0$.
    The derived laws then hold automatically; ∫-bind is also directly the characterisation
    $I_Y (f^dagger nu, v) = I_X (nu, lambda x. I_Y (f x, v))$ of Kleisli extension in
    @def:sfinite.
  ]
]

= Quantifiers

== Means along kernels

#theorem([Quantifiers are means along kernels])[
  Let $Gamma tack nu : Dst A$ and $Gamma, x : A tack phi : Omega$, put $X := sem(A)$, and
  for $g in sem(Gamma)$ write $nu_g := sem(nu)(g) in T X$, an s-finite measure on
  $(|X|, Sigma_(M_X))$. Then for $p in (0, oo)$
  $
    sem(forall^p (x tilde nu). phi)(g) & = (integral_X sem(phi)(g, x)^(-p) space nu_g (dif x))^(-1 slash p)
                                         = integral^(-p)_(x tilde nu_g) sem(phi)(g, x), \
    sem(exists^p (x tilde nu). phi)(g) & = (integral_X sem(phi)(g, x)^(p) space nu_g (dif x))^(1 slash p)
                                         = integral^(p)_(x tilde nu_g) sem(phi)(g, x),
  $ <eq:unwind>
  and at $p = oo$ the essential infimum, respectively supremum, of $sem(phi)(g, -)$ with
  respect to $nu_g$. Here $integral^(plus.minus p)$ are the (harmonic) $p$-means of
  @capucci2024quantifiers. When $Gamma$ and $A$ are first order, $g |-> nu_g$ is an s-finite
  kernel $sem(Gamma) kto X$ (@prop:kernels) and the right-hand sides are the $p$-means of
  $phi$ *along that kernel*.
  #proof[
    By @sec:terms, $sem(forall^p space nu space (lambda x. phi))(g) = sem(forall^p)(nu_g, sem(phi)(g, -))$,
    since $sem(lambda x. phi) = cur sem(phi)$. Apply @lem:dendef and unwind $I_X$ with
    $nu_g = [alpha_g, mu_g]$: $I_X (nu_g, sem(phi)(g, -)^(-p)) = integral_RR sem(phi)(g, alpha_g (r))^(-p) dif mu_g (r)
    = integral_X sem(phi)(g, x)^(-p) dif (alpha_g)_* mu_g$.
  ]
] <thm:kernel>

#corollary[
  + *(Closed measure.)* If $nu$ is closed, $nu_g = [alpha, mu]$ does not depend on $g$ and
    $sem(forall^p (x tilde nu). phi)(g) = (integral_RR sem(phi)(g, alpha(r))^(-p) dif mu(r))^(-1 slash p)$:
    the semantics of quantification over a fixed measured space, as in
    @capucci2026notes[§5].
  + *(Higher order.)* For $A = Prd B$ and $Gamma tack pi : Dst (Prd B)$,
    $
      sem(forall^p (u tilde pi). Phi)(g) = integral^(-p)_(u tilde pi_g) sem(Phi)(g, u),
      quad u in Omega^(sem(B)),
    $ <eq:ho>
    quantification over predicates needs nothing beyond the type $Dst (B -> Omega)$.
  + *(Kernels.)* For $Gamma tack kappa : A -> Dst B$,
    $
      sem(forall^p (x tilde nu). forall^q (y tilde kappa space x). phi)(g)
      = integral^(-p)_(x tilde nu_g) integral^(-q)_(y tilde sem(kappa)(g, x)) sem(phi)(g, x, y),
    $
    quantification along a disintegration, in the sense of @capucci2026notes[§5], obtained
    for free because $kappa space x$ is a term.
]

== Quantifying is running a program

By the axiom ∫-prog and its soundness, the integration operator is definable in the
computational fragment: $I_X (nu, u) = (nu act u)(|X|) = sem("let" x <- nu "in" scr(u space x))$,
an element of $T 1 = Omega$. Through D6 and D7 the soft quantifiers are therefore programs
too,
$
  exists^p (x tilde nu). phi & ≡ mss("let" x <- nu "in" scr(phi^p))^(1 slash p), \
  forall^p (x tilde nu). phi & ≡ mss("let" x <- nu "in" scr(phi^(-p)))^(-1 slash p):
$
sample $x$ from $nu$, score by the softened body, read off the mass, and unsoften. When
$nu$ is a probability measure, $I_X (nu, u)$ is the expectation $EE_(x tilde nu)[u(x)]$, which
is why we allow $EE_(x tilde nu)[phi]$ as a synonym for $integral_(x tilde nu) phi$ in that
case.

== Mass scaling and normalisation

#lemma([Mass scaling])[
  Let $Gamma tack nu : Dst A$ and $g in sem(Gamma)$ with $0 < nu_g (|X|) < oo$, so that
  $"normalise"(nu_g) = sem(nrm(nu))(g)$. For $p in (0, oo)$,
  $
    sem(exists^p (x tilde nu). phi)(g) & = nu_g (|X|)^(1 slash p) ⊗ sem(exists^p (x tilde nrm(nu)). phi)(g), \
    sem(forall^p (x tilde nu). phi)(g) & = nu_g (|X|)^(-1 slash p) ⊗ sem(forall^p (x tilde nrm(nu)). phi)(g).
  $
  In particular $sem(forall^p (x tilde nu). 1)(g) = nu_g (|X|)^(-1 slash p)$: the constant
  $1$ is no longer a unit for $forall^p$ under an unnormalised measure, and
  $forall^p (x tilde nu). 1$ denotes $0$ where $nu_g (|X|) = oo$. At $p = oo$ the mass is
  invisible: $sem(forall^oo (x tilde nu). 1)(g) = 1$ whenever $nu_g eq.not 0$.
  Consequently, for $phi$ with values in $(0, oo)$ $nu_g$-almost everywhere,
  $sem(forall^p (x tilde nu). phi multimap phi)(g) = nu_g (|X|)^(-1 slash p)$ (in general
  only $>=$, since $0 multimap 0 = oo multimap oo = oo$): reflexivity of a graded entailment
  $1 <= forall^p (x tilde nu). phi multimap phi$ holds exactly for sub-probability $nu$,
  while hard entailment ($p = oo$) is unaffected. The consequences for the entailment layer
  are drawn in @sec:quasitripos.
  #proof[
    $integral u^(plus.minus p) dif nu_g = nu_g (|X|) integral u^(plus.minus p) dif "normalise"(nu_g)$,
    then take the $plus.minus 1 slash p$ power.
  ]
] <lem:mass>

#example([Improper prior, scoring and normalisation])[
  Let $Leb$ be Lebesgue measure on $RR$: an s-finite measure of infinite mass, so
  $smp_Leb : Dst RR$ is a closed term although $Leb$ is not a probability distribution.
  With the Borel constant $phi := lambda x : RR. space e^(-x^2 slash 2) : Prd RR$ form the
  program
  $
    M := "let" x <- smp_(Leb) "in" scr(phi space x) seq ret x quad : quad Dst RR,
  $
  whose denotation is the density action $sem(M) = Leb act sem(phi)$: the unnormalised
  Gaussian, of total mass $sqrt(2 pi)$. Then $sem(nrm(M)) = cal(N)(0, 1)$, and
  $smp_Leb$, $M$ and $nrm(M)$ are three closed terms of type $Dst RR$. For
  $psi := lambda x : RR. abs(x)$ the same soft quantifier takes three different values:
  $
       exists^2 (x tilde Leb). psi space x & = (integral_RR x^2 dif x)^(1 slash 2) = oo, \
         exists^2 (x tilde M). psi space x & = (integral_RR x^2 e^(-x^2 slash 2) dif x)^(1 slash 2)
                                             = (sqrt(2 pi))^(1 slash 2) = (2 pi)^(1 slash 4) approx 1.583, \
    exists^2 (x tilde nrm(M)). psi space x & = (EE_(x tilde cal(N)(0,1))[x^2])^(1 slash 2) = 1,
  $
  in accordance with @lem:mass: $(2 pi)^(1 slash 4) = (sqrt(2 pi))^(1 slash 2) dot 1$.
  Dually, $forall^1 (x tilde Leb). 1 = Leb(RR)^(-1) = 0$ while
  $forall^1 (x tilde M). 1 = (sqrt(2 pi))^(-1) approx 0.399$ and
  $forall^1 (x tilde nrm(M)). 1 = 1$: under an improper prior nothing is universally
  valid at a finite grade, and the mass of the posterior is what $nrm$ removes. Finally,
  the measure may depend on the context. With
  $kappa := lambda x : RR. space "let" z <- smp_(cal(N)(0,1)) "in" ret (x + z) : RR -> Dst RR$,
  the open formula $x : RR tack exists^2 (y tilde kappa space x). psi space y : Omega$ denotes
  $g |-> (EE_(y tilde cal(N)(g, 1))[y^2])^(1 slash 2) = sqrt(g^2 + 1)$ by @thm:kernel: the
  $2$-mean of $abs(y)$ along the Gaussian kernel centred at $g$. None of $smp_Leb$, $scr$
  or an open measure argument is expressible in the probability version.
]

= Measured contexts (towards graded entailment) <sec:quasitripos>

The term semantics of the previous sections lives in $"QBS"$ and attaches no measure and
no grade to a context: measures are terms, and the softness $p$ is an index of the
quantifier constants. The *entailment layer* of the logic --- sequents whose validity is
an $Omega$-valued, graded quantity, in the sense of @capucci2026notes[§§5--7] --- needs
more: each variable of a sequent carries the measure it is averaged against and the
softness at which it is averaged. This section records the categorical structure for such
*measured contexts*: grades, measured quasi-Borel spaces, and the category of graded
contexts. It is not used by the term semantics above.

*Grades* $sof = [0,oo]$.

#tb(
  columns: (1fr, auto),
  table.header([*operations*], [*unit*]),
  [$p ⊕^* q = (p^(-1) + q^(-1))^(-1)$ #h(0.6em) (harmonic sum)],
  [$oo$],
  [$p and q$ #h(0.6em) (meet, used by thinning and substitution)],
  [$oo$],
)

== Measured quasi-Borel spaces

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
] <lem:marginals>

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

== Graded contexts

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
  Over a measured context, formulas are interpreted over $U Gamma$, exactly as the terms
  of @sec:terms are interpreted over $sem(Gamma)$: the measures and grades of the slots
  are consumed by the sequent, not by the formulas.
]

== Outlook: graded entailment

The judgement of the entailment layer will be a sequent
$
  x_1 attach(tilde, br: p_1) nu_1, space dots, space x_n attach(tilde, br: p_n) nu_n mid(|) Phi tack psi,
$
in which $x_1 : A_1, dots, x_(i-1) : A_(i-1) tack nu_i : Dst A_i$ --- a chain of kernels,
i.e. a probabilistic program generating the context --- refines the plain typing context
$x_1 : A_1, dots, x_n : A_n$ over which $Phi$ and $psi$ are typed, and $p_i in sof$ is the
softness at which $x_i$ is averaged. Its intended semantics is the mixed harmonic mean
$
  integral^(-p_1)_(x_1 tilde nu_1) dots.c integral^(-p_n)_(x_n tilde nu_n) (times.o.big Phi multimap psi),
$
the $P$-entailment of @capucci2026notes[§6] with products of probability spaces replaced
by kernels; a sequent is valid at grade $P$ when this quantity is at least $1$. The
category $"Ctx"$ above is the special case of closed, independent $nu_i$, where the mixed
mean is taken against the product $nu_1 ⊗ dots.c ⊗ nu_n$ of @lem:marginals. The rules will
be those of @capucci2026notes[§7] --- cut by Hölder's inequality at grade $p ⊕^* q$, the
additive rules by Minkowski's inequality --- with two s-finite specifics recorded above. A
soft grade on a slot of infinite mass makes reflexivity fail (@lem:mass), so soft slots
must be sub-probability or normalised, or the masses must be recorded in the grade. And
discarding a slot scales by its mass (@lem:marginals), so weakening is not free: this is
why the equational theory of @sec:eqth has no discard law.


#bibliography("bibliography.bib")
