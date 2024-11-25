// Math Symbol Shortcuts
#let evalbracket = body => $[| body |]$
#let powerset = body => $cal(P)(body)$

#let leqsq = math.subset.eq.sq
#let geqsq = math.supset.eq.sq

#let join = math.union.sq
#let meet = math.sect.sq

// Analysis specific symbols
#let lbl = e => text(size: 0.85em, sym.dollar) + e

#let evalentry = body => $evalbracket(body)^circle.small$
#let evalexit = body => $evalbracket(body)^(circle.filled.small)$

#let angles = body => $angle.l body angle.r$

#let orpair = $accent(or, arrow.l.r)$

// Terms
#let upar(f, i) = $"par"_(#f)^(#i)$
#let ret = "ret"
#let ucol(e) = $"col"_(#e)$
