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

// effects
#let ann(body) = $angle.l.double body angle.r.double$

#let eff(x) = math.accent(x, math.hat)

#let ef = math.accent("e", math.hat)
#let Ef = math.accent("E", math.hat)
#let EfU = math.accent("U", math.hat)
#let EfI = math.accent("I", math.hat)
#let EfN = math.accent("N", math.hat)
#let EfX = math.accent("X", math.hat)
#let PiEf = eff(sym.Pi)
#let PhiEf = eff(sym.Phi)
#let phiEf = eff(sym.phi)

#let UT = math.accent("1", math.breve)
#let NU = math.accent("0", math.breve)
#let RT = $accent(R, breve)$

#let utv = math.accent("u", math.breve)
#let Utv = math.accent("U", math.breve)


#let efv = math.epsilon
#let andef = pad(left: 0.01em, right:0.01em, text(size: 0.85em, "&"))
#let plusef = math.plus.circle
#let timesef = math.times.circle

#let plusUt = math.accent(math.plus.circle, math.breve)

// Terms
#let upar(f, i) = $"par"_(#f)^(#i)$
#let ret = "ret"
#let ucol(e) = $"col"_(#e)$
