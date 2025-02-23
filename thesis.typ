#import "lib/template.typ": template, front-matter, main-matter, back-matter

#show: template.with(
  title: [Use it or Lose it: A Kotlin Static Analysis for Identifying Unused Values],
  author: "Faiz Ilham Muhammad",
  keywords: ("kotlin", "data-flow analysis", "unused value", "utilization")
)

// #set pagebreak(weak: true)
#set page(numbering: none)

#include "head/cover.typ"

#show: front-matter

#include "head/abstract.typ"

#outline(title: "Contents", depth: 3)
// #outline(title: "List of Figures", target: figure.where(kind: image))
// #outline(title: "List of Tables", target: figure.where(kind: table))
// #outline(title: "List of Listings", target: figure.where(kind: raw))

#show: main-matter

#include "main/ch1_introduction.typ"
#include "main/ch2_preliminaries.typ"
#include "main/ch3_related_work.typ"
#include "main/ch4_simple_model.typ"
#include "main/ch5_general_function.typ"
#include "main/ch6_collection_extension.typ"
#include "main/ch7_implementation.typ"
#include "main/ch8_conclusion.typ"

#show: back-matter

#include "tail/ap1_safely_reachable_proof.typ"
#include "tail/ap2_full_description.typ"
#include "tail/references.typ"
