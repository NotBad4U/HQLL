#import "common.typ": *

= Syntax

We present HQLL in the style of Church's simple theory of types as mechanised in HOL
@church1940 @gordonmelham1993: a simply typed $lambda$-calculus over a signature of typed
constants, in which formulas are the terms of type $Omega$ and every logical operator,
quantifiers included, is a constant applied to its arguments; binder notation is sugar.

== Types #rocqlink[ty][theories/syntax.v#73]

#let types-syntax = $
  A, B ::= 1 mid(|) RR mid(|) Omega mid(|) A times B mid(|) A -> B mid(|) Dst A
$

#types-syntax

The type constants are $1$, $RR$ and the type $Omega$ of truth values; the type operators
are $times$, $->$ and the s-finite measure type $Dst$. The $Omega$ plays the role of $overline(RR)_+$ i.e. Prop,
and $RR$ that of individual: it is standard Borel.
A term of type $Dst A$ denotes an s-finite measure on the space denoted by $A$. The measure
is not required to be normalised: it may be a probability distribution, but also an
unnormalised or infinite measure such as Lebesgue measure on $RR$, or
the unnormalised posterior computed by a program that uses $fct$. The
measure enters the logic only as a term of type $Dst A$.

#let pred-def = $Prd A ≔ A -> Omega$

#definition("Predicate")[The type of predicates on $A$ is defined by #pred-def~#rocqlink[Pred][theories/syntax.v#92]]

== Terms and signature #rocqlink[tm][theories/syntax.v#215] <sec:sig>

#let terms-syntax = $
  M, N ::= x mid(|) c mid(|) M space N mid(|) lambda x : A. space M
  quad quad quad quad (c : A) in Sig
$

#terms-syntax

#let lam-abbrev = $lambda a space b. space M ≔ lambda a. space lambda b. space M$

Terms are those of the simply typed $lambda$-calculus over the signature $Sig$ of
@tab:sig, whose constants come in families indexed by types $A, B$, by a softness
$p in (0, oo)$, by s-finite measures $mu$ and by Borel functions $f$. Formulas are the
terms of type $Omega$ and predicates on $A$ the terms of type $Prd A$. We abbreviate #lam-abbrev.~#rocqlink[tm][theories/syntax.v#215]

#let sig-table = tb(
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
)

#figure(
  sig-table,
  caption: [The signature $Sig$ of HQLL~#rocqlink[const][theories/syntax.v#176-193]],
) <tab:sig>

The computation $smp_mu$ draws from a constant s-finite measure $mu$ on $sem(A)$: a
probability distribution, but also Lebesgue measure $RR$).
The $fct(phi)$ multiplies the weight of the current execution by the truth value of the formula $phi$;
its inverse $mss$ reads a measure on the one-point type back as a truth value.

#remark[
  $Omega$ and $Dst 1$ denote the same space $[0, oo]$ (@lem:omega-t1)
]

#let grade-range = $p in [-oo, oo]$

HOL builds $top, forall, exists, bot, not, and, or$ from the three primitives $=$,
$arrow$ and $epsilon$ @gordonmelham1993. We do the same approach but without $epsilon$.
We define the new constants in $Sig$ with the displayed type, together with the equation $c ≡ M$ (@sec:eqth)~#rocqlink[Infty … Forall][theories/syntax.v#413-454].
Throughout, #grade-range unless stated otherwise.

#let const-defs = tagged("D", $
  oo & ≔ 0^* : Omega #<D1> \
  bot & ≔ 0 : Omega #<D2> \
  top & ≔ oo : Omega #<D3> \
  ⊗^* & ≔ lambda a space b. space (a^* ⊗ b^*)^* : Omega -> Omega -> Omega #<D4> \
  multimap & ≔ lambda a space b. space a^* ⊗^* b : Omega -> Omega -> Omega #<D5> \
  or^p & ≔ lambda a space b. space (a^p ⊕ b^p)^(1 slash p) : Omega -> Omega -> Omega #<D6> \
  and^(p) & ≔ lambda a space b. space (a^* ⊕^(-p) b^*)^* : Omega -> Omega -> Omega #<D7> \
  exists^p_A & ≔ lambda nu space u. space (integral_A space nu space (lambda x. space (u space x)^p))^(1 slash p) : Dst A -> (A -> Omega) -> Omega #<D8> \
  forall^p_A & ≔ lambda nu space u. space (exists^p_A space nu space (lambda x. space (u space x)^*))^* : Dst A -> (A -> Omega) -> Omega #<D9>
$)

#const-defs

@D5 is the place where HOL defines $exists P$ as $P (epsilon P)$.
Here the existential is instead computed.
We define the existential quantifier in @D8 as the $L^p (nu)$-norm of $u$, an arithmetic $p$-mean when $nu$ is a probability measure, and @D9 makes $forall^p$ its De
Morgan dual, the harmonic $p$-mean.
Similarly approach done for the universal quantifier $forall^p_nu u$.

#let hard-quantifiers = $
  exists^oo = or.big^oo quad quad forall^oo = and.big^oo
$

#remark[
  At $p = oo$ gives the hard existential $exists^oo$ is the essential supremum, and $forall^oo$ the essential infimum.

  #hard-quantifiers
]

#let pair-abbrev = $⟨M, N⟩ ≔ pr space M space N$
#let letin-abbrev = $"let" x <- M "in" N ≔ bnd space M space (lambda x : A. space N)$
#let seq-abbrev = $M ; N ≔ "let" x <- M "in" N$
#let qbind-abbrev = $Q space (x tilde nu). space phi ≔ Q space nu space (lambda x. space phi)$

#notations[
  We use the following abbreviations:
  - #pair-abbrev, and, for $M : Dst A$, #letin-abbrev, with #seq-abbrev for $x$ fresh~#rocqlink[Letin, Seq][theories/syntax.v#481-488].
  - For any constant $Q : Dst A -> (A -> Omega) -> Omega$ (quantifiers) we write
    #qbind-abbrev, read $Q$ over $x$ drawn from $nu : Dst A$ where the type is omitted~#rocqlink[qbind][theories/syntax.v#461].
]

== Typing

#let ctx-syntax = $Gamma ::= diamond.small mid(|) Gamma, x : A$

#definition("Context")[
  Contexts #ctx-syntax are finite lists of distinct typed variables~#rocqlink[ctx][theories/syntax.v#126].
]

#let judgement-forms = $
  Gamma tack M : A quad quad Gamma tack M ≡ N : A
$

#definition("Judgement")[
  The judgements are
  #judgement-forms
  $M$ is a well-typed term of type $A$ in context $Gamma$, and the other denote the equational judgement.
]

No measure and no grade is attached to a context. Measures live in the terms of type $Dst A$, and
grades in the entailment layer (@sec:quasitripos). As in HOL there are exactly four typing rules~#rocqlink[tm][theories/syntax.v#215-219]:

#let typing-rules = grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  row-gutter: 14pt,
  prooftree(rule(name: [Var], $Gamma\, x : A\, Gamma' tack x : A$)),
  prooftree(rule(name: [Con], $(c : A) in Sig$, $Gamma tack c : A$)),

  prooftree(rule(name: [Abs], $Gamma\, x : A tack M : B$, $Gamma tack lambda x : A. space M : A -> B$)),
  prooftree(rule(name: [App], $Gamma tack M : A -> B$, $Gamma tack N : A$, $Gamma tack M space N : B$)),
)

#typing-rules

Weakening, exchange and substitution are admissible: a derivation in $Gamma$ is read in any
context containing $Gamma$ by renaming its variables, and substitution acts on derivations.

#let typing-admissible = grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  row-gutter: 14pt,
  prooftree(rule(name: [#rocqlink[Weaken][theories/syntax.v#235]], $Gamma tack M : A$, $Gamma\, x : B tack M : A$)),
  prooftree(rule(name: [#rocqlink[Exch][theories/syntax.v#226]], $Gamma\, x : A\, y : B\, Gamma' tack M : C$, $Gamma\, y : B\, x : A\, Gamma' tack M : C$)),
  grid.cell(colspan: 2, prooftree(rule(name: [#rocqlink[Subst][theories/syntax.v#280]], $Gamma\, x : A tack M : B$, $Gamma tack N : A$, $Gamma tack M[N slash x] : B$))),
)

#typing-admissible

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

== Conversion rules #rocqlink[conv][theories/equational.v#524-581] <sec:eqth>

The judgement $Gamma tack M ≡ N : A$ is the least
congruence containing the definitional equations of the logical operators and the axioms
below. The congruence is generated by the rules:

#let conv-equivalence = grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 9pt,
  row-gutter: 14pt,
  prooftree(rule(name: [Refl], $Gamma tack M : A$, $Gamma tack M ≡ M : A$)),
  prooftree(rule(name: [Sym], $Gamma tack M ≡ N : A$, $Gamma tack N ≡ M : A$)),
  prooftree(rule(name: [Trans], $Gamma tack M ≡ N : A$, $Gamma tack N ≡ P : A$, $Gamma tack M ≡ P : A$)),
)
#let conv-congruence = grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  prooftree(rule(name: [Abs], $Gamma\, x : A tack M ≡ M' : B$, $Gamma tack lambda x : A. space M ≡ lambda x : A. space M' : A -> B$)),
  prooftree(rule(name: [App], $Gamma tack M ≡ M' : A -> B$, $Gamma tack N ≡ N' : A$, $Gamma tack M space N ≡ M' space N' : B$)),
)

#conv-equivalence
#conv-congruence

It plays the role of HOL's axioms and conversion rules.

#let conv-axioms = grid(
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
  grid.cell(colspan: 2, $"let" y <- ("let" x <- M "in" N) "in" P ≡ "let" x <- M "in" "let" y <- N "in" P quad (x in.not "FV"(P))$),
  grid.cell(colspan: 2, $"let" x <- M "in" "let" y <- N "in" P ≡ "let" y <- N "in" "let" x <- M "in" P quad (x in.not "FV"(N), space y in.not "FV"(M))$),
)

#block(above: 1.5em, below: 1.5em, conv-axioms)

In the arithmetic rules, $s$ and $t$ are _$Omega$-expressions_. The formula $s[arrow(phi)]$
instantiates the variables by formulas~#rocqlink[oexp, conv_omega][theories/equational.v#335-363].

#let conv-admissible = grid(
  columns: (1fr, 1fr),
  gutter: 9pt,
  row-gutter: 14pt,
  prooftree(rule(name: [Weak #rocqlink[conv_weaken][theories/equational.v#723]], $Gamma tack M ≡ N : A$, $Gamma\, x : B tack M ≡ N : A$)),
  prooftree(rule(name: [Exch], $Gamma\, x : A\, y : B\, Gamma' tack M ≡ N : C$, $Gamma\, y : B\, x : A\, Gamma' tack M ≡ N : C$)),
  grid.cell(colspan: 2, prooftree(rule(name: [Subst #rocqlink[conv_subst_cong][theories/equational.v#787]], $Gamma\, x : A tack M ≡ M' : B$, $Gamma tack N ≡ N' : A$, $Gamma tack M[N slash x] ≡ M'[N' slash x] : B$))),
)

#lemma([Admissible rules])[
  Weakening, exchange and substitution are not rules of the judgement but are derivable.
  #conv-admissible
  Every rule is closed under renaming of the context and under substitution, by induction on the
  derivation~#rocqlink[conv_rename, conv_subst][theories/equational.v#685-787].
]

#let int-axioms = tagged(("∫-prog", "∫-lin", "∫-zero"), $
  integral_(x tilde nu) phi ≡ mss("let" x <- nu "in" fct(phi)) #<eq:int-prog> \
  integral_(x tilde nu) (phi ⊕ psi) ≡ integral_(x tilde nu) phi ⊕ integral_(x tilde nu) psi #<eq:int-lin> \
  integral_(x tilde nu) 0 ≡ 0 #<eq:int-zero>
$)

Where HOL has the axiom of choice for $epsilon$, we have three axioms for $integral$:
#int-axioms
The @eq:int-prog says that quantifying is running a program, integrating $phi$ against $nu$ is sampling $x$ from $nu$, scoring by $phi$ and reading off the mass.
The @eq:int-lin and @eq:int-zero are additivity of the integral, which no monad law provides. Everything else follows.

#let int-derived = tagged(("∫-ret", "∫-bind", "∫-factor", "∫-hom", "Fubini"), $
  integral_(x tilde ret M) phi ≡ phi[M slash x] #<eq:int-ret> \
  integral_(y tilde ("let" x <- M "in" N)) phi ≡ integral_(x tilde M) integral_(y tilde N) phi #<eq:int-bind> \
  integral_(x tilde fct(psi)) phi ≡ psi ⊗ phi[ast slash x] #<eq:int-factor> \
  integral_(x tilde nu) (psi ⊗ phi) ≡ psi ⊗ integral_(x tilde nu) phi #<eq:int-hom> \
  integral_(x tilde nu) integral_(y tilde rho) phi ≡ integral_(y tilde rho) integral_(x tilde nu) phi #<eq:fubini>
$)

#let int-bind-fresh = $x in.not "FV"(phi)$
#let int-hom-fresh = $x in.not "FV"(psi)$
#let fubini-fresh-x = $x in.not "FV"(rho)$
#let fubini-fresh-y = $y in.not "FV"(nu)$

#lemma([Derived integration laws])[
  The following equations are derivable, with #int-bind-fresh in @eq:int-bind,
  #int-hom-fresh in @eq:int-hom and #fubini-fresh-x, #fubini-fresh-y in
  @eq:fubini:
  #int-derived
  #proof[
    #rocqlink[conv_int_ret … conv_fubini][theories/equational.v#811-882]
  ]
]
