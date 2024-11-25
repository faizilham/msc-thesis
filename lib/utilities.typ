#import "@preview/codelst:2.0.2" as codelst

#let citep(lbl, pageno) = cite(lbl, supplement: [p. #pageno])

#let sourcecode = codelst.sourcecode

#let listing(caption, content) = {
  figure(
    sourcecode(content, frame: none),
    caption: caption,
  )
}
