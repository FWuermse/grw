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

#set page(numbering : "1")

#counter(page).update(1)

#let charCounter = counter("charCounter")

#show regex("[a-zA-Z]"): it =>{
  charCounter.step()
  it
}

#include "introduction.typ"

#include "algorithm.typ"

#include "optimisations.typ"

#include "updated-algorithm.typ"

#include "proof.typ"

#include "implementation.typ"

= Related Work



= Conclusion

#pagebreak()

#bibliography("refs.bib", full: true, title: "References")

Characters: #context(charCounter.display())
