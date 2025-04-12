#import "./template.typ": *
#import "./theme.typ": *
#import "@preview/dashy-todo:0.0.1": todo

#let title = "Generalised Rewriting for Lean"
#let author = "Florian Würmseer"

#show: official.with(
  title: title,
  author: author,
  thesis-type: "Master Thesis",
  submission_date: datetime.today().display(),
  matriculation: "12760815",
  advisor: "Jannis Limperg",
  supervisor: "Prof. Dr. Jasmin Blanchette"
)
#show heading: set block(below: 1.5em, above: 2em)

#show figure: set block(below: 1.5em, above: 2em)

#set page(numbering : "1")

#counter(page).update(1)
#set cite(style: "the-institution-of-engineering-and-technology")

#include "introduction.typ"

#include "algorithm.typ"

#include "optimisations.typ"

#include "updated-algorithm.typ"

#include "proof.typ"

#include "implementation.typ"

#include "relatedwork.typ"

#include "conclusion.typ"

#pagebreak()

#bibliography("refs.bib", full: true, title: "References", style: "institute-of-electrical-and-electronics-engineers")
