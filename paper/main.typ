#import "common.typ": *

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
// Colour references to equations.
#show ref: eq-ref

#include "omega.typ"
#include "syntax.typ"
#include "semantics.typ"
#include "entailment.typ"

#bibliography("bibliography.bib")
