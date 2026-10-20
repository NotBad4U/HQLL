// Shared imports and definitions, imported by every section with
//   #import "common.typ": *
// Set/show rules live in main.typ, since they only apply where they are written.

#import "lib.typ": *

#import "@preview/showybox:2.0.4": showybox
#import "@preview/curryst:0.6.0": prooftree, rule
// Extra room above and below the inference bar, so tall operators (e.g. integrals) do not touch it.
#let prooftree = prooftree.with(vertical-spacing: 0.4em)
#import "@preview/commute:0.3.0": arr, commutative-diagram, node
#import "@preview/equate:0.3.2": equate

// ---------------- notation ----------------
#let sem(x) = $lr(⟦ #x ⟧)$
#let Prd = math.op("Pred")
// Type of s-finite measures on A (formerly Dist A, the probability type).
#let Dst = math.cal("T")
#let Qbs = math.op("QBS")
#let Meas = math.op("Meas")
#let Sbs = math.op("Sbs")
#let Seq = math.op("Seq")
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

// ---------------- layout ----------------

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

// Colours references to equations (equate turns each labelled line into an equation figure).
// Used as `#show ref: eq-ref`.
#let eq-ref(it) = {
  let el = it.element
  if el != none and (el.func() == math.equation or (el.func() == figure and el.kind == math.equation)) {
    text(fill: colors.emerald, it)
  } else {
    it
  }
}

// Tags each line of a multi-line display, restarting from the first line.
// `tags` is a prefix ("D" gives D1, D2, …) or an array with one name per line.
// Lines are labelled with equate's `#<label>`, so they can be referenced.
#let tagged(tags, body) = {
  let numbering = if type(tags) == array { n => tags.at(n - 1, default: str(n)) } else { n => tags + str(n) }
  set math.equation(numbering: numbering, supplement: none)
  counter(math.equation).update(0)
  body
}
