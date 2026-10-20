// The formulas of the paper, and nothing else.
//
// Each formula is a variable defined next to its prose in a section file and only
// imported here, so editing a section updates this sheet. To add a formula, define
// it with a hyphenated name (a plain one like `sem` or `seq` would shadow the
// math macro in the whole section), then import it and give it an `entry` below.

#import "common.typ": *
#import "omega.typ": omega-ops, omega-residuation, reals-notation
#import "syntax.typ": (
  types-syntax, pred-def,
  terms-syntax, lam-abbrev, sig-table, grade-range, const-defs, hard-quantifiers,
  pair-abbrev, letin-abbrev, seq-abbrev, qbind-abbrev,
  ctx-syntax, judgement-forms, typing-rules, typing-admissible,
  conv-equivalence, conv-congruence, conv-axioms, conv-admissible,
  int-axioms, int-derived, int-bind-fresh, int-hom-fresh, fubini-fresh-x, fubini-fresh-y,
)
#import "semantics.typ": (
  qbs-tuple, qbs-random-set, qbs-mor, qbs-exp, qbs-sigma, qbs-random, qbs-sbs-random, qbs-sbs-hom,
  t-triple, t-triple-space, t-triple-param, t-integral,
  t-ret-type, t-ret, t-bind-type, t-bind, t-bind-cond, t-bind-kernel, t-bind-param,
  cont-monad, t-cont-embed, t-one, t-rep,
  sem-types, omega-random, omega-t1, t1-iso, omega-t1-maps, sem-ctx, sem-judgement,
  sem-const-point, sem-terms, sem-prims,
  sem-env, sem-env-measure, sem-unwind,
  sem-omega-args, sem-p-range, sem-arith, sem-logic, sem-quant-measure, sem-quant-fn, sem-quant,
  adj-mass, adj-esssup-def, adj-esssup-dual, adj-esssup-char, adj-pred, adj-ae-order, adj-fibre,
  adj-weakening, adj-quantifiers, adj-statement, adj-hom, adj-laws, adj-unit, adj-frobenius, adj-bc-square, adj-bc, adj-ex-measure, adj-ex-formula, adj-ex-I, adj-ex-values,
  adj-finite-p-setup, adj-finite-p,
  soundness-stmt,
)
#import "entailment.typ": (
  gctx-syntax, gctx-erase-nil, gctx-erase-cons, gctx-wf-measure, gctx-wf-fresh,
  seq-erasure, seq-counit,
  gctx-explicit, sequent-typing, sequent-form, sequent-sem, sequent-valid,
  hard-sequent-order, hard-sequent-valid,
)

#set document(title: [Higher order QLL with QBS: formula sheet])
#set page(numbering: "1", number-align: center + bottom)
#set text(10pt, font: fonts.serif)
#show math.equation: set text(font: fonts.math)
#show heading: set text(font: fonts.sans)
// Same numbering as the paper, so a sheet section points to the paper's one.
#set heading(numbering: "1.1")
#show: equate.with(breakable: true)
#show ref: eq-ref

#title()

// an inline formula is set as a display one, the rest is shown as it is
#let display(f) = if f.func() == math.equation and not f.block {
  math.equation(block: true, f.body)
} else {
  f
}

// several short formulas on a single display line
#let side(..fs) = math.equation(block: true, fs.pos().map(f => f.body).join(h(3em)))

// one item of the sheet: a rubric, the hypotheses `where` it holds, then its formulas
#let entry(name, where: (), ..formulas) = block(breakable: false, width: 100%, above: 1.6em, {
  text(weight: "bold", fill: colors.emerald, name)
  if where.len() > 0 {
    h(1.5em)
    text(fill: colors.gray, where.map(box).join(h(1.5em)))
  }
  for f in formulas.pos() { display(f) }
})

= Multiplicative Extended Reals $RR_times.o$

#entry([Operations], omega-ops)
#entry([Residuation], omega-residuation)
#entry([Notation], reals-notation)

= Syntax

== Types

#entry([Types], types-syntax)
#entry([Predicates], pred-def)

== Terms and signature

#entry([Terms], terms-syntax, lam-abbrev)
#entry([Signature $Sig$], sig-table)
#entry([Defined constants], where: (grade-range,), const-defs)
#entry([Hard quantifiers], hard-quantifiers)
#entry([Abbreviations], side(pair-abbrev, seq-abbrev), letin-abbrev, qbind-abbrev)

== Typing

#entry([Contexts], ctx-syntax)
#entry([Judgements], judgement-forms)
#entry([Typing rules], typing-rules)
#entry([Admissible rules], typing-admissible)

== Conversion rules

#entry([Equivalence and congruence], conv-equivalence, conv-congruence)
#entry([Axioms], conv-axioms)
#entry([Admissible rules], conv-admissible)
#entry([Integration axioms], int-axioms)
#entry(
  [Derived integration laws],
  where: (
    [#int-bind-fresh (@eq:int-bind)],
    [#int-hom-fresh (@eq:int-hom)],
    [#fubini-fresh-x, #fubini-fresh-y (@eq:fubini)],
  ),
  int-derived,
)

= Semantics

== Preliminaries

#entry([Quasi-Borel space], side(qbs-tuple, qbs-random-set))
#entry([QBS morphism $f : X -> Y$], align(center, qbs-mor))
#entry([Exponential], qbs-exp)
#entry([Induced $sigma$-algebra], qbs-sigma)
#entry([Random elements], qbs-random)
#entry([Standard Borel $X$], side(qbs-sbs-random, qbs-sbs-hom))
#entry([The monad $T$], where: (t-triple-space, t-triple-param), t-triple, t-integral)
#entry([Return], side(t-ret-type, t-ret))
#entry([Bind], where: (t-bind-cond, t-bind-kernel, t-bind-param), t-bind-type, t-bind)
#entry([Embedding into the continuation monad], side(cont-monad, t-cont-embed))
#entry([Measures on the point], t-one)
#entry([One parameter line suffices], t-rep)

== Types and contexts

#entry([Types], sem-types)
#entry([Truth values], omega-random)
#entry([Truth values as measures], side(omega-t1, t1-iso), omega-t1-maps)
#entry([Contexts], sem-ctx)
#entry([Judgements], sem-judgement)

== Terms

#entry([Constants], sem-const-point)
#entry([Terms], sem-terms)
#entry([Primitive constants], sem-prims)

=== Logic operators

#entry([Quantified formulas], where: (sem-env,), sem-env-measure, sem-unwind)

== Interpretation of the logical constants

#entry([Arithmetic], where: (sem-omega-args, sem-p-range), sem-arith)
#entry([Logical operators], sem-logic)
#entry([Quantifiers], where: (sem-quant-measure, sem-quant-fn), sem-quant)

== Quantifiers as adjoints

#entry([Mass of a measurable set], adj-mass)
#entry([Essential supremum and infimum], adj-esssup-def, adj-esssup-dual)
#entry([Essential bounds], adj-esssup-char)
#entry([Orders on predicates], side(adj-pred, adj-fibre), adj-ae-order)
#entry([Weakening and hard quantifiers], adj-weakening, adj-quantifiers)
#entry([Quantifiers as adjoints], adj-statement, adj-hom)
#entry([Laws], adj-laws, adj-unit)
#entry([Frobenius reciprocity], adj-frobenius)
#entry([Beck–Chevalley], adj-bc-square, adj-bc)
#entry([Quantifying over predicates], where: (adj-ex-measure,), adj-ex-formula, adj-ex-I, adj-ex-values)
#entry([Soft quantifiers are not adjoints], where: (adj-finite-p-setup,), adj-finite-p)

== Soundness

#entry([Soundness of the equational theory], soundness-stmt)

= Graded logical entailment

#entry([Graded contexts], gctx-syntax)
#entry([Erasure], side(gctx-erase-nil, gctx-erase-cons))
#entry([Well formed], side(gctx-wf-measure, gctx-wf-fresh))
#entry([Erasure functor], seq-erasure, seq-counit)
#entry([Logical sequent], where: (gctx-explicit, sequent-typing), sequent-form, sequent-sem)
#entry([Validity], sequent-valid)
#entry([Hard sequents], hard-sequent-order, hard-sequent-valid)
