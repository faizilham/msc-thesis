// Math Symbol Shortcuts
#let powerset = body => $cal(P)(body)$

#let leqsq = math.subset.eq.sq
#let geqsq = math.supset.eq.sq

#let join = math.union.sq
#let meet = math.sect.sq

// Analysis specific symbols
#let lbl = e => text(size: 0.85em, sym.dollar) + e

#let evalbracket(body, sub:none) = {
  if sub == none {
    $[| body |]$
  } else {
    $[| body |]_#sub$
  }
}

#let evalentry(body, sub:none) = $evalbracket(body, sub:sub)^(circle.small)$
#let evalexit(body, sub:none) = $evalbracket(body, sub:sub)^(circle.filled.small)$

#let spx = $s_p^circle.small.filled$
#let sp = $s_p^circle.small$

#let angles(..body) = {
  let merged = body.pos().join(", ")
  $angle.l merged angle.r$
}

#let orpair = $accent(or, arrow.l.r)$

// Terms
#let upar(f, i) = $"par"_(#f)^(#i)$
#let ret = "ret"
#let ucol(e) = $"col"_(#e)$
