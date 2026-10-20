#import "common.typ": *

= Semantics

== Preliminaries <sec:prelim>

#let qbs-tuple = $X = (|X|, M_X)$
#let qbs-random-set = $M_X subset.eq { RR -> |X|}$
#let qbs-mor = [$f compose alpha in M_Y$ for all $alpha in M_X$]
#let qbs-exp = $M_(Y^X) = { alpha mid(|) "uncurry"(alpha) in "QBS"(RR times X, Y)}$
#let qbs-sigma = $Sigma_(M_X) = { U mid(|) forall alpha in M_X dot alpha^(-1) U in Sigma_RR}$
#let qbs-random = $M_X = Qbs(RR, X)$
#let qbs-sbs-random = $M_X = Meas(RR, X)$
#let qbs-sbs-hom = $Qbs(X, Y) = Meas(X, Sigma_(M_Y))$

#definition("QBS")[
  #qbs-tuple is a quasi-Borel space with a underlying set $|X|$ and a set of functions #qbs-random-set closed under precomposition with Borel maps, containing constants, closed under countable Borel gluing. Given $f: X -> Y$ is a QBS morphism if and only if #qbs-mor.
  - QBS is cartesian closed: #qbs-exp
  - QBS is well pointed
  - #qbs-sigma is the induced 𝜎-algebra.
  - #qbs-random, and for a standard Borel space $X$ (regarded as a QBS with
    #qbs-sbs-random) one has #qbs-sbs-hom.
]

Measures on a QBS are introduced through the s-finite monad $T$ @scibior2018denotational @vakar2026sfinite.
Recall that a measure $mu$ on a measurable space is s-finite if it is a countable sum of finite measures, and that a kernel $k : X kto Y$ is s-finite if it is a countable sum of kernels $k_i$ with $sup_x k_i (x, Y) < oo$.
S-finite kernels are closed under composition @staton2017commutative and contain the probability kernels,
Lebesgue measure and counting measure on $NN$; counting measure on $RR$ is not s-finite.

#let t-triple = $T X := ⟨W, mu, alpha⟩$
#let t-triple-space = $W in Sbs$
#let t-triple-param = $alpha in Qbs(W, X)$
#let t-integral = $
  integral_X f dif ⟨W, mu, alpha⟩ := integral_W f(alpha(w)) space dif mu(w).
$
#let t-ret-type = $ret_X : X -> T X$
#let t-ret = $ret_X (x) := ⟨1, delta_ast, ast |-> x⟩$
#let t-bind-type = $(kbind) : T X times Qbs(X, T Y) -> T Y$
#let t-bind = $⟨W, mu, alpha⟩ kbind f := ⟨W times V, space A |-> bb(E)_(w tilde mu) [k(w, A_w)], space beta⟩$
#let t-bind-cond = $f(alpha(w)) = ⟨V, k(w, -), beta(w, -)⟩$
#let t-bind-kernel = $k : W kto V$
#let t-bind-param = $beta in Qbs(W times V, Y)$

#definition([The monad $T$])[
  Let $X in Qbs$ and let $Sbs$ denote the standard Borel spaces.
  A *(randomisable) s-finite measure* on $X$ is a triple #t-triple with
  #t-triple-space, $mu$ an s-finite measure on $W$ and #t-triple-param.
  It integrates every $f in Qbs(X, Omega)$ by
  #t-integral
  - #t-ret-type \
    #t-ret
  - #t-bind-type \
    #t-bind \
    with #t-bind-cond \
    and #t-bind-kernel, #h(0.5em) #t-bind-param
] <def:sfinite>

#let cont-monad = $((-) => Omega) => Omega$
#let t-cont-embed = $nu |-> integral_X (-) dif nu$

#proposition[
  $T$ is a commutative monad on $Qbs$, embedded in the continuation monad
  #cont-monad by #t-cont-embed.
] <prop:comm-monad>

#let t-one = $T 1 = [0, oo] = Omega$

#proposition[
  For $X, Y in Sbs$, $|T X|$ is the set of all s-finite measures on $X$, and $Qbs(X, T Y)$
  the set of s-finite kernels $X kto Y$. In particular #t-one.
] <prop:sbs-measures>

#definition([Probability monad])[
  The probability monad $cal(P)$ is the sub-monad of $T$ where $mu$ is a probability measure.
]

#let t-rep = $
    |T X| & = { [alpha, mu] mid(|) alpha in M_X, space mu "s-finite on" RR } slash ~, \
  M_(T X) & = { r |-> [alpha, k(r, -)] mid(|) alpha in M_X, space k : RR kto RR "an s-finite kernel" }.
$

#lemma([One parameter line suffices])[
  Every s-finite measure on $X$ has a representative on $W = RR$, and every random
  element of $T X$ has a representative with a fixed random element of $X$:
  #t-rep
]

== Types and contexts

We define the semantics of types recursively as follows:

#let sem-types = grid(
  columns: (1fr, 1fr, 1fr),
  align: center,
  row-gutter: 10pt,
  $sem(1) = 1$, $sem(RR) = RR$, $sem(Omega) = overline(RR)_+$,
  $sem(A times B) = sem(A) times sem(B)$, $sem(A -> B) = sem(B)^(sem(A))$, $sem(Dst A) = T sem(A)$,
)

#block(above: 1em, below: 1em)[
  #sem-types <eq:types>
]

#let omega-random = $M_Omega = {"Borel" RR -> [0, oo] }$

where $[0, oo]$ is standard Borel with #omega-random.

#let omega-t1 = $sem(Omega) = sem(Dst 1)$
#let t1-iso = $T 1 ≅ overline(RR)_+$
#let omega-t1-maps = $
  f : T 1 -> overline(RR)_+, quad f(mu) := mu({ast}) quad quad quad
  g : overline(RR)_+ -> T 1, quad g(c) := c dot delta_ast
$

#lemma[
  #omega-t1, via the isomorphism #t1-iso.
  #proof[
    By @prop:sbs-measures, $|T 1|$ is the set of s-finite measures on $1$, and $M_(T 1)$
    the set of s-finite kernels $RR kto 1$. Define
    #omega-t1-maps
    and $f(g(c)) = c dot delta_ast ({ast}) = c$, and $g(f(mu)) = mu({ast}) dot delta_ast = mu$ inverses
    of each others because $emptyset$ and ${ast}$ are the only measurable subsets of $1$.
  ]
] <lem:omega-t1>

#let sem-ctx = $
  sem(x_1 : A_1\, dots\, x_n : A_n) := sem(A_1) times dots.c times sem(A_n),
$

A context is interpreted by the cartesian product in $"QBS"$:
#sem-ctx <eq:ctx>

#let sem-judgement = $
  sem(Gamma tack M : A) : sem(Gamma) -> sem(A)
$

the terminal object $1$ for the empty context. This is the standard interpretation of a
simply typed $lambda$-calculus in a cartesian closed category @jacobs1999cltt.
The interpretation of $Gamma tack M : A$ is a QBS morphism:
#sem-judgement

== Terms <sec:terms>

#let sem-const-point = $sem(c) : 1 -> sem(A)$

A constant $c : A$ is interpreted by a point #sem-const-point.
For $c : A_1 -> dots.c -> A_n -> B$ we write $sem(c)(a_1, dots, a_n)$ for its transpose
$sem(A_1) times dots.c times sem(A_n) -> sem(B)$.

#let sem-terms = grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 10pt,
  $sem(x_i) = pi_i$, $sem(c) = sem(c) compose !_(sem(Gamma))$,
  $sem(lambda x : A. space M) = cur (sem(Gamma\, x : A tack M))$, $sem(M space N) = ev compose ⟨ sem(M), sem(N) ⟩$,
)

#block(above: 2em, below: 1em, sem-terms) <eq:term-sem>

#let sem-prims = grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(ast) = ast$, $sem(pr)(a, b) = (a, b)$,
  $sem(pi_1)(a, b) = a$, $sem(pi_2)(a, b) = b$,
  $sem(ret)(a) = ⟨1, delta_ast, ast |-> a⟩$, $sem(bnd)(nu, f) = nu kbind f$,
  $sem(smp_mu) = mu$, $sem(fct)(a) = a dot delta_ast$,
  $sem("uniform"_(a, b)) = cal(U)[a, b]$, $sem("normal"_(m, s)) = cal(N)(m, s^2)$,
  $sem(mss)(m) = m({ast})$,
  $sem(nrm)(nu) = display(cases(nu slash nu(sem(A)) & "if" 0 < nu(sem(A)) < oo, 0 & "otherwise"))$,
)

#block(above: 1em, below: 1em, sem-prims)

=== Logic operators

#let sem-env = $g in sem(Gamma)$
#let sem-env-measure = $nu_g := sem(Gamma tack nu : Dst A)(g)$

A point #sem-env is an environment: a tuple of values for the variables of $Gamma$.
A measure term $Gamma tack nu : Dst A$ denotes a kernel $sem(Gamma) -> T sem(A)$, and we write
#sem-env-measure for the s-finite measure on $sem(A)$ it assigns to the
environment $g$. A formula $Gamma\, x : A tack phi : Omega$ with a free $x$ denotes a map
$sem(Gamma) times sem(A) -> [0, oo]$, and we write $sem(phi)(g, x)$ for its value; once $g$ is
fixed, $sem(phi)(g, -) : sem(A) -> [0, oo]$ is the measurable function that gets integrated
against $nu_g$.

#let sem-unwind = $
    sem(Q space (x tilde nu). phi)(g) & = sem(Q)(nu_g, sem(phi)(g, -)), \
    sem(integral_(x tilde nu) phi)(g) & = integral_(sem(A)) sem(phi)(g, x) space nu_g (dif x)
                                        = integral_(x tilde nu_g) sem(phi)(g, x), \
   sem(exists^p (x tilde nu). phi)(g) & = (integral_(sem(A)) sem(phi)(g, x)^(p) space nu_g (dif x))^(1 slash p)
                                        = integral^(p)_(x tilde nu_g) sem(phi)(g, x), \
   sem(forall^p (x tilde nu). phi)(g) & = (integral_(sem(A)) sem(phi)(g, x)^(-p) space nu_g (dif x))^(-1 slash p)
                                        = integral^(-p)_(x tilde nu_g) sem(phi)(g, x), \
  sem(exists^oo (x tilde nu). phi)(g) & = limits(esssup)_(x tilde nu_g) sem(phi)(g, x), \
  sem(forall^oo (x tilde nu). phi)(g) & = limits(essinf)_(x tilde nu_g) sem(phi)(g, x).
$

#sem-unwind <eq:unwind>

== Interpretation of the logical constants <sec:consts>


#let sem-omega-args = $a, b in sem(Omega) = [0, oo]$
#let sem-p-range = $0 < p < oo$

Let #sem-omega-args and #sem-p-range.
We define the semantics of extended reals as follows:

#let sem-arith = grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(⊗)(a, b) = a b quad (0 dot oo = 0)$, $sem(⊕)(a, b) = a + b$,
  $sem((-)^*)(a) = 1 slash a quad (1 slash 0 = oo, space 1 slash oo = 0)$,
  $sem((-)^p)(a) = a^p quad (0^p = 0, space oo^p = oo)$,

  $sem((-)^(-p))(a) = (1 slash a)^p quad (0^(-p) = oo, space oo^(-p) = 0)$, $sem((-)^0)(a) = 1$,
  $sem((-)^oo)(a) = lim_(p -> oo) a^p in {0, 1, oo}$, $sem((-)^(-oo))(a) = sem((-)^oo)(1 slash a)$,
)

#block(above: 2em, below: 2em, sem-arith)

We define the semantics of logical operators (@D1 to @D7) as follows:

#let sem-logic = grid(
  columns: (1fr, 1fr),
  align: left,
  row-gutter: 8pt,
  $sem(bot) = 0$, $sem(top) = oo$,
  $sem(oo) = oo$, $sem(⊗^*)(a, b) = a b quad (0 dot oo = oo)$,
  grid.cell(colspan: 2, $sem(multimap)(a, b) = sup{c in [0, oo] mid(|) a c <= b}$),
  $sem(or^p)(a, b) = (a^p + b^p)^(1 slash p)$, $sem(and^p)(a, b) = (a^(-p) + b^(-p))^(-1 slash p)$,
  $sem(or^oo)(a, b) = max(a, b)$, $sem(and^oo)(a, b) = min(a, b)$,
)

#block(above: 2em, below: 2em, sem-logic)

#let sem-quant = $
   sem(integral_A)(nu, u) & = integral_(sem(A)) u space dif nu, \
   sem(exists^p_A)(nu, u) & = (integral_(sem(A)) u^p space dif nu)^(1 slash p) = norm(u)_(L^p (nu)), \
   sem(forall^p_A)(nu, u) & = (integral_(sem(A)) u^(-p) space dif nu)^(-1 slash p) = norm(u^*)_(L^p (nu))^*, \
  sem(exists^oo_A)(nu, u) & = limits(esssup)_nu u, quad quad sem(forall^oo_A)(nu, u) = limits(essinf)_nu u.
$

#let sem-quant-measure = $nu in |T sem(A)|$
#let sem-quant-fn = $u in Qbs(sem(A), [0, oo])$

For the quantifier (@D8, @D9), for #sem-quant-measure and #sem-quant-fn:
#sem-quant

== Soundness

#let soundness-stmt = $
  "If" Gamma tack M ≡ N : A "then" sem(M) = sem(N) : sem(Gamma) -> sem(A)
$

#theorem([Soundness of the equational theory])[
  #soundness-stmt
]
