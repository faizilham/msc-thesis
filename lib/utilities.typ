#import "@preview/codelst:2.0.2" as codelst
#import "@preview/fletcher:0.5.4" as fletcher: diagram, node, edge


#let pkg-fletcher = "@preview/fletcher:0.5.4"
#let pkg-curryst = "@preview/curryst:0.4.0"

#let citep(lbl, pageno) = cite(lbl, supplement: [p. #pageno])

#let sourcecode = codelst.sourcecode

#let listing(caption, content) = {
  figure(
    sourcecode(content, frame: none),
    caption: caption,
  )
}
