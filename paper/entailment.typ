#import "common.typ": *

= Graded logical entailment <sec:quasitripos>

The typing context $Gamma$ carries no measure and no grade. Both live in a second, ordered
context that records, for each variable, the measure it is drawn from and the softness at which
it is quantified.

#let gctx-syntax = $
  Theta ::= diamond.small mid(|) Theta seq x tilde^p nu quad quad (p in (0, oo])
$
#let gctx-erase-nil = $Gamma_diamond.small := diamond.small$
#let gctx-erase-cons = $Gamma_(Theta seq x tilde^p nu) := Gamma_Theta, x : A$
#let gctx-wf-measure = $Gamma_Theta tack nu : Dst A$
#let gctx-wf-fresh = $x in.not Gamma_Theta$

#definition("Graded context")[
  A graded context is a list
  #gctx-syntax
  Its underlying typing context $Gamma_Theta$ erases measures and grades:
  #gctx-erase-nil and #gctx-erase-cons.
  It is well formed when every measure is a term over the variables declared before it:
  #gctx-wf-measure and #gctx-wf-fresh.
]

#let seq-erasure = $Pi : Seq(Qbs) -> Qbs$
#let seq-counit = align(center, commutative-diagram(
  node-padding: (120pt, 55pt),
  node((0, 0), $(sem(A_1) times dots.c times sem(A_n))$),
  node((0, 1), $(sem(A_1) seq dots seq sem(A_n))$),
  node((1, 1), $(sem(A_i))$),
  arr((0, 0), (0, 1), $delta_Gamma$),
  arr((0, 0), (1, 1), $(pi_i)$, label-pos: right),
  arr((0, 1), (1, 1), $"pr"_i$),
))

Semantically a typing context is a product in $Qbs$, where variables may be tupled and
permuted, while a graded context is an ordered sequence, where they may not. Writing
$Seq(Qbs)$ for the free ordered-product category on $Qbs$ @capucci2026notes, erasure is the
product functor #seq-erasure, right adjoint to the inclusion of singletons, and
passing from a typing context to a graded one is the counit $delta_Gamma$ of this
coreflection, which fixes the order of the variables. It is the cone of the product, so it
commutes with the projections, the only structural maps of $Seq(Qbs)$:

#seq-counit

A graded context is an ordered chain of kernels: the measure of a variable may depend on the
variables declared before it, and $p$ is the softness of the universal quantifier that binds it.

#let gctx-explicit = $Theta = x_1 tilde^(p_1) nu_1 seq dots seq x_n tilde^(p_n) nu_n$
#let sequent-typing = $Gamma_Theta tack psi_1, dots, psi_k, phi : Omega$
#let sequent-form = $
  Theta thin | thin psi_1, dots, psi_k tack phi
$
#let sequent-sem = $
  forall^(p_1) (x_1 tilde nu_1). space dots.c space forall^(p_n) (x_n tilde nu_n). space
  ((psi_1 ⊗ dots.c ⊗ psi_k) multimap phi) : Omega
$
#let sequent-valid = $1 <= sem(Theta thin | thin psi_1\, dots\, psi_k tack phi)$

#definition("Logical sequent")[
  Let #gctx-explicit be well formed and
  #sequent-typing. The sequent
  #sequent-form
  denotes the closed formula
  #sequent-sem
  where the empty list of assumptions stands for $1$. It is _valid_ when
  #sequent-valid.
]

The sequent reads: in the graded context $Theta$, which declares every variable free in
$psi_1, dots, psi_k$ and $phi$, the formula $phi$ is true under the assumptions
$psi_1, dots, psi_k$.

#let hard-sequent-order = $
  phi aele(Theta) phi' quad "iff" quad "for" nu_1"-a.e." x_1, dots, "for" nu_n (x_1, dots, x_(n-1))"-a.e." x_n : space
  phi(x_1, dots, x_n) <= phi'(x_1, dots, x_n)
$
#let hard-sequent-valid = $
  Theta thin | thin psi_1, dots, psi_k tack phi "is valid" quad <==> quad
  sem(psi_1 ⊗ dots.c ⊗ psi_k) aele(Theta) sem(phi) quad quad (p_1 = dots.c = p_n = oo)
$

#corollary([Hard sequents])[
  Let #gctx-explicit be well formed with every grade $p_i = oo$. Comparing formulas over
  $Gamma_Theta$ almost everywhere along the chain,
  #hard-sequent-order
  validity is almost-everywhere entailment:
  #hard-sequent-valid
  #proof[
    By @lem:esssup, the pointwise form of @thm:adjoint,
    $1 <= sem(forall^oo (x tilde nu). chi)(g)$ iff $1 <= sem(chi)(g, x)$ for $nu_g$-almost
    every $x$. Applied $n$ times from the outermost quantifier inwards, the sequent is valid iff
    $1 <= sem((psi_1 ⊗ dots.c ⊗ psi_k) multimap phi)$ holds $Theta$-almost everywhere. Finally
    $1 <= a multimap b$ iff $a <= b$ by @lem:residuation.
  ]
] <cor:hard-sequent>
