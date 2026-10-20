#import "common.typ": *

= Multiplicative Extended Reals $RR_times.o$ <sec:omega>

#let omega-ops = tb(
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

#omega-ops

#let omega-residuation = $
  a ⊗ c <= b quad <==> quad c <= a multimap b quad quad quad (a, b, c in [0, oo])
$

#lemma([Residuation])[
  #omega-residuation
  In particular $1 <= a multimap b$ iff $a <= b$.
  #proof[
    $D := {c mid(|) a ⊗ c <= b}$ is a down-set, as $⊗$ is monotone, and $a multimap b = sup D$
    lies in $D$: if $a = 0$ or $b = oo$ then $D = [0, oo]$ and $a ⊗ oo <= b$; if $a = oo$ and
    $b < oo$ then $D = {0}$; otherwise $D = [0, b slash a]$ and $a ⊗ (b slash a) = b$. Hence
    $c <= sup D$ iff $c in D$.
  ]
] <lem:residuation>

#let reals-notation = grid(
  columns: (auto, auto, 1fr),
  column-gutter: 1.2em,
  row-gutter: 0.6em,
  [- $bb(I)$: unit interval $[0, 1]$], [- $overline(RR)$: extended real line $[-oo, oo]$],
  grid.cell(rowspan: 2)[- $overline(RR)_+$: $[0, oo]$.],

  [- $RR$: real line $(-oo, oo)$], [- $RR_+$: non-negative reals $[0, oo)$],
)

#notations[
  #reals-notation
]
