#import "lib.typ": *

#import "@preview/showybox:2.0.4": showybox
#import "@preview/curryst:0.6.0": prooftree, rule
// Extra room above and below the inference bar, so tall operators (e.g. integrals) do not touch it.
#let prooftree = prooftree.with(vertical-spacing: 0.4em)
#import "@preview/commute:0.3.0": arr, commutative-diagram, node
#import "@preview/equate:0.3.2": equate

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

// Per-line numbering and labels in multi-line equations (used for D1--D7).
#show: equate.with(breakable: true)
// Colour references to equations (equate turns each labelled line into an equation figure).
#show ref: it => {
  let el = it.element
  if el != none and (el.func() == math.equation or (el.func() == figure and el.kind == math.equation)) {
    text(fill: colors.emerald, it)
  } else {
    it
  }
}

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
#let fct = math.op("factor")
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
// Kleisli bind  ν >>= f, as the usual LaTeX \mathbin{>\!\!\!>\mkern-6.7mu=}
#let kbind = math.class("binary", $>#h(-9em / 18)>#h(-6.7em / 18)=$)
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
  inset: 8pt,
  stroke: 0.4pt + rgb("#515151"),
  ..args,
)

// ============================================================

= Multiplicative Extended Reals $RR_times.o$ <sec:omega>

#tb(
  columns: (1fr, auto),
  table.header([*operation*], [*unit*]),
  [$a ⊗ b = a b$ #h(1em) ($0 ⊗ oo = 0$)],
  [$1$],
  [$a ⊕ b = a + b$],
  [$0$],
  [$a^* = 1 slash a$, #h(0.4em) $0^* = oo$],
  [---],
  [$a^p$ #h(1em) ($0^p = 0$, #h(0.3em) $oo^p = oo$, #h(0.3em) $p in (0, oo)$)],
  [---],
  [$a ⊗^* b = a b$ #h(1em) ($0 ⊗^* oo = oo$)],
  [$1$],
  [$a multimap b = sup{c mid(|) a ⊗ c <= b} = a^* ⊗^* b$],
  [---],
  [$a or^p b = (a^p ⊕ b^p)^(1 slash p) quad quad a and^(-p) b = (a^(-p) ⊕ b^(-p))^(-1 slash p)$],
  [$0$ / $oo$],
)

#notations[
  #grid(
    columns: (auto, auto, 1fr),
    column-gutter: 1.2em,
    row-gutter: 0.6em,
    [- $bb(I)$: unit interval $[0, 1]$], [- $overline(RR)$: extended real line $[-oo, oo]$],
    grid.cell(rowspan: 2)[- $overline(RR)_+$: $[0, oo]$.],

    [- $RR$: real line $(-oo, oo)$], [- $RR_+$: non-negative reals $[0, oo)$],
  )
]

= Syntax

We present HQLL in the style of Church's simple theory of types as mechanised in HOL
@church1940 @gordonmelham1993: a simply typed $lambda$-calculus over a signature of typed
constants, in which formulas are the terms of type $Omega$ and every logical operator,
quantifiers included, is a constant applied to its arguments; binder notation is sugar.

== Types

$
  A, B ::= 1 mid(|) RR mid(|) Omega mid(|) A times B mid(|) A -> B mid(|) Dst A
$

The type constants are $1$, $RR$ and the type $Omega$ of truth values; the type operators
are $times$, $->$ and the s-finite measure type $Dst$. The $Omega$ plays the role of $overline(RR)_+$ i.e. Prop,
and $RR$ that of individual: it is standard Borel.
A term of type $Dst A$ denotes an s-finite measure on the space denoted by $A$. The measure
is not required to be normalised: it may be a probability distribution, but also an
unnormalised or infinite measure such as Lebesgue measure on $RR$, or
the unnormalised posterior computed by a program that uses $fct$. The
measure enters the logic only as a term of type $Dst A$.

#definition("Predicate")[The type of predicates on $A$ is defined by $Prd A ≔ A -> Omega$]

== Terms and signature <sec:sig>

$
  M, N ::= x mid(|) c mid(|) M space N mid(|) lambda x : A. space M
  quad quad quad quad (c : A) in Sig
$

Terms are those of the simply typed $lambda$-calculus over the signature $Sig$ of
@tab:sig, whose constants come in families indexed by types $A, B$, by a softness
$p in (0, oo)$, by s-finite measures $mu$ and by Borel functions $f$. Formulas are the
terms of type $Omega$ and predicates on $A$ the terms of type $Prd A$. We abbreviates $lambda a. space lambda b. space M$ as $lambda a space b. space M$.

#figure(
  tb(
    columns: (auto, 1fr),
    align: (left, left),
    table.header([*constant*], [*type*]),
    [$ast$],
    [$1$],
    [$pr$],
    [$A -> B -> A times B$],
    [$pi_1$, #h(0.3em) $pi_2$],
    [$A times B -> A$, #h(0.3em) $A times B -> B$],
    [$0$, #h(0.3em) $1$],
    [$Omega$],
    [$⊗$, #h(0.3em) $⊕$],
    [$Omega -> Omega -> Omega$],
    [$(-)^*$],
    [$Omega -> Omega$],
    [$(-)^p$ #h(0.4em) ($p in [-oo, oo]$)],
    [$Omega -> Omega$],
    [$integral_A$],
    [$Dst A -> (A -> Omega) -> Omega$],
    [$ret$],
    [$A -> Dst A$],
    [$bnd$],
    [$Dst A -> (A -> Dst B) -> Dst B$],
    [$smp_mu$ #h(0.4em) ($mu$ s-finite on $sem(A)$)],
    [$Dst A$],
    [$fct$],
    [$Omega -> Dst 1$],
    [$mss$],
    [$Dst 1 -> Omega$],
    [$nrm$],
    [$Dst A -> Dst A$],
  ),
  caption: [The signature $Sig$ of HQLL],
) <tab:sig>

The computation $smp_mu$ draws from a constant s-finite measure $mu$ on $sem(A)$: a
probability distribution, but also Lebesgue measure $RR$).
The $fct(phi)$ multiplies the weight of the current execution by the truth value of the formula $phi$;
its inverse $mss$ reads a measure on the one-point type back as a truth value.

#remark[
  $Omega$ and $Dst 1$ denote the same space $[0, oo]$ (@lem:omega-t1)
]

HOL builds $top, forall, exists, bot, not, and, or$ from the three primitives $=$,
$arrow$ and $epsilon$ @gordonmelham1993. We do the same approach but without $epsilon$.
We define the new constants in $Sig$ with the displayed type, together with the equation $c ≡ M$ (@sec:eqth).
Throughout, $p in [-oo, oo]$ unless stated otherwise.

#[
  #set math.equation(numbering: n => "D" + str(n), supplement: none)
  #counter(math.equation).update(0)
  $
    oo & ≔ 0^* : Omega #<D1> \
    bot & ≔ 0 : Omega #<D2> \
    top & ≔ oo : Omega #<D3> \
    ⊗^* & ≔ lambda a space b. space (a^* ⊗ b^*)^* : Omega -> Omega -> Omega #<D4> \
    multimap & ≔ lambda a space b. space a^* ⊗^* b : Omega -> Omega -> Omega #<D5> \
    or^p & ≔ lambda a space b. space (a^p ⊕ b^p)^(1 slash p) : Omega -> Omega -> Omega #<D6> \
    and^(p) & ≔ lambda a space b. space (a^* ⊕^(-p) b^*)^* : Omega -> Omega -> Omega #<D7> \
    exists^p_A & ≔ lambda nu space u. space (integral_A space nu space (lambda x. space (u space x)^p))^(1 slash p) : Dst A -> (A -> Omega) -> Omega #<D8> \
    forall^p_A & ≔ lambda nu space u. space (exists^p_A space nu space (lambda x. space (u space x)^*))^* : Dst A -> (A -> Omega) -> Omega #<D9>
  $
]

@D5 is the place where HOL defines $exists P$ as $P (epsilon P)$.
Here the existential is instead computed.
We define the existential quantifier in @D8 as the $L^p (nu)$-norm of $u$, an arithmetic $p$-mean when $nu$ is a probability measure, and @D9 makes $forall^p$ its De
Morgan dual, the harmonic $p$-mean.
Similarly approach done for the universal quantifier $forall^p_nu u$.

#remark[
  At $p = oo$ gives the hard existential $exists^oo$ is the essential supremum, and $forall^oo$ the essential infimum.

  $
    exists^oo = or.big^oo quad quad forall^oo = and.big^oo
  $
]

#notations[
  We use the following abbreviations:
  - $⟨M, N⟩ ≔ pr space M space N$, and, for $M : Dst A$, $"let" x <- M "in" N ≔ bnd space M space (lambda x : A. space N)$, with $M ; N ≔ "let" x <- M "in" N$ for $x$ fresh.
  - For any constant $Q : Dst A -> (A -> Omega) -> Omega$ (quantifiers) we write
    $Q space (x tilde nu). space phi$ read $Q$ over $x$ drawn from $nu : Dst A$ where the type is omitted.
]

== Typing

#definition("Context")[
  Contexts $Gamma ::= diamond.small mid(|) Gamma, x : A$ are finite lists of distinct typed variables.
]

#definition("Judgement")[
  The judgements are
  $
    Gamma tack M : A quad quad Gamma tack M ≡ N : A
  $
  $M$ is a well-typed term of type $A$ in context $Gamma$, and the other denote the equational judgement.
]

No measure and no grade is attached to a context. Measures live in the terms of type $Dst A$, and
grades in the entailment layer (@sec:quasitripos). As in HOL there are exactly four typing rules:

#grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  row-gutter: 14pt,
  prooftree(rule(name: [Var], $Gamma\, x : A\, Gamma' tack x : A$)),
  prooftree(rule(name: [Con], $(c : A) in Sig$, $Gamma tack c : A$)),

  prooftree(rule(name: [Abs], $Gamma\, x : A tack M : B$, $Gamma tack lambda x : A. space M : A -> B$)),
  prooftree(rule(name: [App], $Gamma tack M : A -> B$, $Gamma tack N : A$, $Gamma tack M space N : B$)),
)

#example[
  #align(center, prooftree(rule(
    name: [App],
    rule(
      name: [App],
      rule(
        name: [Con],
        $(integral_A : Dst A -> (A -> Omega) -> Omega) in Sig$,
        $Gamma tack integral_A : Dst A -> (A -> Omega) -> Omega$,
      ),
      $Gamma tack nu : Dst A$,
      $Gamma tack integral_A space nu : (A -> Omega) -> Omega$,
    ),
    rule(
      name: [Abs],
      $Gamma\, x : A tack phi : Omega$,
      $Gamma tack lambda x : A. space phi : A -> Omega$,
    ),
    $Gamma tack integral_A space nu space (lambda x : A. space phi) : Omega$,
  )))

  The term $integral_A space nu space (lambda x : A. space phi)$ sample $x$ from $nu$ and weight the outcome by the
  truth value of $phi$.
]

== Equational theory <sec:eqth>

The judgement $Gamma tack M ≡ N : A$ is the least congruence i.e. reflexive, symmetric, transitive, closed under Abs and App --- containing the definitional equations of logical operators and the axioms below. It plays the role of HOL's axioms and conversion rules.

#block(above: 1.5em, below: 1.5em, grid(
  columns: (1fr, 1fr),
  column-gutter: 16pt,
  row-gutter: 1.5em,
  align: left,
  $(lambda x : A. space M) space N ≡ M[N slash x]$, $pi_i ⟨M_1, M_2⟩ ≡ M_i$,
  $lambda x : A. space (M space x) ≡ M quad (x in.not "FV"(M))$, $⟨pi_1 M, pi_2 M⟩ ≡ M$,
  $M ≡ ast quad (M : 1)$, $s[arrow(phi)] ≡ t[arrow(phi)] quad (s = t "in" [0, oo])$,

  $fct(1) ≡ ret ast$, $fct(phi) seq fct(psi) ≡ fct(phi ⊗ psi)$,
  $mss(fct(phi)) ≡ phi$,
  $fct(mss(m)) ≡ m$,

  $"let" x <- ret M "in" N ≡ N[M slash x]$, $"let" x <- M "in" ret x ≡ M$,
  grid.cell(colspan: 2, $"let" y <- ("let" x <- M "in" N) "in" P ≡ "let" x <- M "in" "let" y <- N "in" P$),
  grid.cell(colspan: 2, $"let" x <- M "in" "let" y <- N "in" P ≡ "let" y <- N "in" "let" x <- M "in" P$),
))

Where HOL has the axiom of choice for $epsilon$, we have three axioms for $integral$:
#[
  #let names = ("∫-prog", "∫-lin", "∫-zero")
  #set math.equation(numbering: n => names.at(n - 1, default: str(n)), supplement: none)
  #counter(math.equation).update(0)
  $
    integral_(x tilde nu) phi ≡ mss("let" x <- nu "in" fct(phi)) #<eq:int-prog> \
    integral_(x tilde nu) (phi ⊕ psi) ≡ integral_(x tilde nu) phi ⊕ integral_(x tilde nu) psi #<eq:int-lin> \
    integral_(x tilde nu) 0 ≡ 0 #<eq:int-zero>
  $
]
The @eq:int-prog says that quantifying is running a program, integrating $phi$ against $nu$ is sampling $x$ from $nu$, scoring by $phi$ and reading off the mass.
The @eq:int-lin and @eq:int-zero are additivity of the integral, which no monad law provides. Everything else follows.

#lemma([Derived integration laws])[
  The following equations are derivable, with $x in.not "FV"(phi)$ in @eq:int-bind and
  $x in.not "FV"(psi)$ in @eq:int-hom:
  #[
    #let names = ("∫-ret", "∫-bind", "∫-factor", "∫-hom", "Fubini")
    #set math.equation(numbering: n => names.at(n - 1, default: str(n)), supplement: none)
    #counter(math.equation).update(0)
    $
      integral_(x tilde ret M) phi ≡ phi[M slash x] #<eq:int-ret> \
      integral_(y tilde ("let" x <- M "in" N)) phi ≡ integral_(x tilde M) integral_(y tilde N) phi #<eq:int-bind> \
      integral_(x tilde fct(psi)) phi ≡ psi ⊗ phi[ast slash x] #<eq:int-factor> \
      integral_(x tilde nu) (psi ⊗ phi) ≡ psi ⊗ integral_(x tilde nu) phi #<eq:int-hom> \
      integral_(x tilde nu) integral_(y tilde rho) phi ≡ integral_(y tilde rho) integral_(x tilde nu) phi #<eq:fubini>
    $
  ]
]

= Semantics

== Preliminaries <sec:prelim>

#definition("QBS")[
  $X = (|X|, M_X)$ is a quasi-Borel space with a underlying set $|X|$ and a set of functions $M_X subset.eq { RR -> |X|}$ closed under precomposition with Borel maps, containing constants, closed under countable Borel gluing. Given $f: X -> Y$ is a QBS morphism if and only if $f compose alpha in M_Y$ for all $alpha in M_X$.
  - QBS is cartesian closed: $M_(Y^X) = { alpha mid(|) "uncurry"(alpha) in "QBS"(RR times X, Y)}$
  - QBS is well pointed
  - $Sigma_(M_X) = { U mid(|) forall alpha in M_X dot alpha^(-1) U in Sigma_RR}$ is the induced 𝜎-algebra.
  - $M_X = Qbs(RR, X)$, and for a standard Borel space $X$ (regarded as a QBS with
    $M_X = Meas(RR, X)$) one has $Qbs(X, Y) = Meas(X, Sigma_(M_Y))$.
]

Measures on a QBS are introduced through the s-finite monad $T$ @scibior2018denotational @vakar2026sfinite.
Recall that a measure $mu$ on a measurable space is s-finite if it is a countable sum of finite measures, and that a kernel $k : X kto Y$ is s-finite if it is a countable sum of kernels $k_i$ with $sup_x k_i (x, Y) < oo$.
S-finite kernels are closed under composition @staton2017commutative and contain the probability kernels,
Lebesgue measure and counting measure on $NN$; counting measure on $RR$ is not s-finite.

#definition([The monad $T$])[
  Let $X in Qbs$ and let $Sbs$ denote the standard Borel spaces.
  A *(randomisable) s-finite measure* on $X$ is a triple $T X := ⟨W, mu, alpha⟩$ with
  $W in Sbs$, $mu$ an s-finite measure on $W$ and $alpha in Qbs(W, X)$.
  It integrates every $f in Qbs(X, Omega)$ by
  $
    integral_X f dif ⟨W, mu, alpha⟩ := integral_W f(alpha(w)) space dif mu(w).
  $
  - $ret_X : X -> T X$ \
    $ret_X (x) := ⟨1, delta_ast, ast |-> x⟩$
  - $(kbind) : T X times Qbs(X, T Y) -> T Y$ \
    $⟨W, mu, alpha⟩ kbind f := ⟨W times V, space A |-> bb(E)_(w tilde mu) [k(w, A_w)], space beta⟩$ \
    with $f(alpha(w)) = ⟨V, k(w, -), beta(w, -)⟩$ \
    and $k : W kto V$, #h(0.5em) $beta in Qbs(W times V, Y)$
] <def:sfinite>

#proposition[
  $T$ is a commutative monad on $Qbs$, embedded in the continuation monad
  $((-) => Omega) => Omega$ by $nu |-> integral_X (-) dif nu$.
] <prop:comm-monad>

#proposition[
  For $X, Y in Sbs$, $|T X|$ is the set of all s-finite measures on $X$, and $Qbs(X, T Y)$
  the set of s-finite kernels $X kto Y$. In particular $T 1 = [0, oo] = Omega$.
] <prop:sbs-measures>

#definition([Probability monad])[
  The probability monad $cal(P)$ is the sub-monad of $T$ where $mu$ is a probability measure.
]

#lemma([One parameter line suffices])[
  Every s-finite measure on $X$ has a representative on $W = RR$, and every random
  element of $T X$ has a representative with a fixed random element of $X$:
  $
      |T X| & = { [alpha, mu] mid(|) alpha in M_X, space mu "s-finite on" RR } slash ~, \
    M_(T X) & = { r |-> [alpha, k(r, -)] mid(|) alpha in M_X, space k : RR kto RR "an s-finite kernel" }.
  $
]

== Types and contexts

We define the semantics of types recursively as follows:

#block(above: 1em, below: 1em)[
  #grid(
    columns: (1fr, 1fr, 1fr),
    align: center,
    row-gutter: 10pt,
    $sem(1) = 1$, $sem(RR) = RR$, $sem(Omega) = overline(RR)_+$,
    $sem(A times B) = sem(A) times sem(B)$, $sem(A -> B) = sem(B)^(sem(A))$, $sem(Dst A) = T sem(A)$,
  ) <eq:types>
]

where $[0, oo]$ is standard Borel with $M_Omega = {"Borel" RR -> [0, oo] }$.

#lemma[
  $sem(Omega) = sem(Dst 1)$, via the isomorphism $T 1 ≅ overline(RR)_+$.
  #proof[
    By @prop:sbs-measures, $|T 1|$ is the set of s-finite measures on $1$, and $M_(T 1)$
    the set of s-finite kernels $RR kto 1$. Define
    $
      f : T 1 -> overline(RR)_+, quad f(mu) := mu({ast}) quad quad quad
      g : overline(RR)_+ -> T 1, quad g(c) := c dot delta_ast
    $
    and $f(g(c)) = c dot delta_ast ({ast}) = c$, and $g(f(mu)) = mu({ast}) dot delta_ast = mu$ inverses
    of each others because $emptyset$ and ${ast}$ are the only measurable subsets of $1$.
  ]
] <lem:omega-t1>

A context is interpreted by the cartesian product in $"QBS"$:
$
  sem(x_1 : A_1\, dots\, x_n : A_n) := sem(A_1) times dots.c times sem(A_n),
$ <eq:ctx>

the terminal object $1$ for the empty context. This is the standard interpretation of a
simply typed $lambda$-calculus in a cartesian closed category @jacobs1999cltt.
The interpretation of $Gamma tack M : A$ is a QBS morphism:
$
  sem(Gamma tack M : A) : sem(Gamma) -> sem(A)
$

== Terms <sec:terms>

A constant $c : A$ is interpreted by a point $sem(c) : 1 -> sem(A)$.
For $c : A_1 -> dots.c -> A_n -> B$ we write $sem(c)(a_1, dots, a_n)$ for its transpose
$sem(A_1) times dots.c times sem(A_n) -> sem(B)$.

#block(above: 2em, below: 1em, grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 10pt,
  $sem(x_i) = pi_i$, $sem(c) = sem(c) compose !_(sem(Gamma))$,
  $sem(lambda x : A. space M) = cur (sem(Gamma\, x : A tack M))$, $sem(M space N) = ev compose ⟨ sem(M), sem(N) ⟩$,
)) <eq:term-sem>


#block(above: 1em, below: 1em, grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(ast) = ast$, $sem(pr)(a, b) = (a, b)$,
  $sem(pi_1)(a, b) = a$, $sem(pi_2)(a, b) = b$,
  $sem(ret)(a) = ⟨1, delta_ast, ast |-> a⟩$, $sem(bnd)(nu, f) = nu kbind f$,
  $sem(smp_mu) = mu$, $sem(fct)(a) = a dot delta_ast$,
  $sem(mss)(m) = m({ast})$,
  $sem(nrm)(nu) = display(cases(nu slash nu(sem(A)) & "if" 0 < nu(sem(A)) < oo, 0 & "otherwise"))$,
))

=== Logic operators

A point $g in sem(Gamma)$ is an environment: a tuple of values for the variables of $Gamma$.
A measure term $Gamma tack nu : Dst A$ denotes a kernel $sem(Gamma) -> T sem(A)$, and we write
$nu_g := sem(Gamma tack nu : Dst A)(g)$ for the s-finite measure on $sem(A)$ it assigns to the
environment $g$. A formula $Gamma\, x : A tack phi : Omega$ with a free $x$ denotes a map
$sem(Gamma) times sem(A) -> [0, oo]$, and we write $sem(phi)(g, x)$ for its value; once $g$ is
fixed, $sem(phi)(g, -) : sem(A) -> [0, oo]$ is the measurable function that gets integrated
against $nu_g$.

$
    sem(Q space (x tilde nu). phi)(g) & = sem(Q)(nu_g, sem(phi)(g, -)), \
    sem(integral_(x tilde nu) phi)(g) & = integral_(sem(A)) sem(phi)(g, x) space nu_g (dif x)
                                        = integral_(x tilde nu_g) sem(phi)(g, x), \
   sem(exists^p (x tilde nu). phi)(g) & = (integral_(sem(A)) sem(phi)(g, x)^(p) space nu_g (dif x))^(1 slash p)
                                        = integral^(p)_(x tilde nu_g) sem(phi)(g, x), \
   sem(forall^p (x tilde nu). phi)(g) & = (integral_(sem(A)) sem(phi)(g, x)^(-p) space nu_g (dif x))^(-1 slash p)
                                        = integral^(-p)_(x tilde nu_g) sem(phi)(g, x), \
  sem(exists^oo (x tilde nu). phi)(g) & = limits(esssup)_(x tilde nu_g) sem(phi)(g, x), \
  sem(forall^oo (x tilde nu). phi)(g) & = limits(essinf)_(x tilde nu_g) sem(phi)(g, x).
$ <eq:unwind>

== Interpretation of the logical constants <sec:consts>


Let $a, b in sem(Omega) = [0, oo]$ and $0 < p < oo$.
We define the semantics of extended reals as follows:

#block(above: 2em, below: 2em, grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(⊗)(a, b) = a b quad (0 dot oo = 0)$, $sem(⊕)(a, b) = a + b$,
  $sem((-)^*)(a) = 1 slash a quad (1 slash 0 = oo, space 1 slash oo = 0)$,
  $sem((-)^p)(a) = a^p quad (0^p = 0, space oo^p = oo)$,

  $sem((-)^(-p))(a) = (1 slash a)^p quad (0^(-p) = oo, space oo^(-p) = 0)$, $sem((-)^0)(a) = 1$,
  $sem((-)^oo)(a) = lim_(p -> oo) a^p in {0, 1, oo}$, $sem((-)^(-oo))(a) = sem((-)^oo)(1 slash a)$,
))

We define the semantics of logical operators (@D1 to @D7) as follows:

#block(above: 2em, below: 2em, grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(bot) = 0$, $sem(top) = oo$,
  $sem(oo) = oo$, $sem(⊗^*)(a, b) = a b quad (0 dot oo = oo)$,
  grid.cell(colspan: 2, $sem(multimap)(a, b) = sup{c in [0, oo] mid(|) a c <= b}$),
  $sem(or^p)(a, b) = (a^p + b^p)^(1 slash p)$, $sem(and^p)(a, b) = (a^(-p) + b^(-p))^(-1 slash p)$,
  $sem(or^oo)(a, b) = max(a, b)$, $sem(and^oo)(a, b) = min(a, b)$,
))

For the quantifier (@D8, @D9), for $nu in |T sem(A)|$ and $u in Qbs(sem(A), [0, oo])$:
$
   sem(integral_A)(nu, u) & = integral_(sem(A)) u space dif nu, \
   sem(exists^p_A)(nu, u) & = (integral_(sem(A)) u^p space dif nu)^(1 slash p) = norm(u)_(L^p (nu)), \
   sem(forall^p_A)(nu, u) & = (integral_(sem(A)) u^(-p) space dif nu)^(-1 slash p) = norm(u^*)_(L^p (nu))^*, \
  sem(exists^oo_A)(nu, u) & = limits(esssup)_nu u, quad quad sem(forall^oo_A)(nu, u) = limits(essinf)_nu u.
$

== Soundness

#theorem([Soundness of the equational theory])[
  $
    "If" Gamma tack M ≡ N : A "then" sem(M) = sem(N) : sem(Gamma) -> sem(A)
  $
]

= Graded entailment <sec:quasitripos>

#bibliography("bibliography.bib")
