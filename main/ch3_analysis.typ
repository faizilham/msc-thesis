#import "../lib/symbols.typ": *

= Value Usage and Utilization Analysis


== Definitions

Given $s$ a mapping $X -> Y$, $s[x -> y]$ means replace any mapping $x -> *$ in $s$ with $x -> y$. Formally:

$
  &s[x -> y] &&= (s without {x -> *}) union {x -> y} \
  &s[x_1 -> y_1, x_2 -> y_2]& &= (s[x_1 -> y_1])[x_2 -> y_2] \
  &s[x -> y | "cond"(x) ] &&= cases(
    s[x -> y] & "if cond"(x) "is true",
    s         & "otherwise"
  )
$

Map lattice:

$
  M = "MapLat"(A, L) = (A -> L, attach(leqsq, br: L))\
  "where, for all" m_1, m_2 in powerset(M), "this property holds":\
  m_1 leqsq m_2 <=> forall a in A . m_1(a) leqsq m_2(a)
$



Transfer function:

$
  &evalexit(mono("exit")) = { x -> top | forall x in R without C } union { f -> bot | forall f in C } \
  &evalexit(p) = join.big_(q in "succ"(p)) evalentry(q) \
  &evalentry(mono("p: x :=" lbl(e))) = s[\$e -> s(lbl(e)) meet s(x), x -> top], "where" s = evalexit(p) \
  &evalentry(mono("p:" lbl(e) "= f") | mono(f) in C) = s[f ->s(lbl(e))], "where" s = evalexit(p)\
  &evalentry(mono("p:" lbl(e) "= x")) = s[x -> s(x) meet s(lbl(e)), x -> top], "where" s = evalexit(p)\
  &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl("arg"_1), ..., lbl("arg"_n) )) = (
    "UtilizeFV" compose "UtilizeArgs" compose "UpdateCall"
  )(evalexit(p)) \
    &"  where:" \
    &"    UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
    &"    UtilizeArgs"(s) = s["arg"_i -> "UT" | forall i. 1 <= i <= n and i in "UtilParam"(f)] \
    &"    UtilizeFV"(s) = s[x -> "UT" | forall x in "UtilFV"(f)] \
  &\

  &evalentry(mono("p: return" lbl(e))) = evalexit(p)[lbl(e) -> lbl(e) meet "RT"]\
  &evalentry(p) = evalexit(p)
$


Analysis result

$
  &"Warnings" = {f | forall f in C. evalentry(mono("start"))(f) leqsq.not "RT" } \
  &"If F is a local function:"\
  &"UtilParams(F)" = { "index"(v) | forall v in "Params". evalentry(mono("start"))(f) leqsq "UT" }\
  &"UtilFV(F)" = { v | forall v in "FV". evalentry(mono("start"))(f) leqsq "UT" }\
$


Pairwise or operator:
$
   A orpair B &= union.big_(a in A) union.big_(b in B) {a or b}
$

Term & Prerequisite lattice:

$
  "term" &::= upar(f, i) | "ret" | ucol(e) \
  "prereq" &::= "true" | "false" | "term" (or "term")^* \
  & t or t = t\
  & t_1 or t_2 = t_2 or t_1\
  & (t_1 or t_2) or t_3 = t_1 or (t_2 or t_3)\
  & t or "true" = "true"\
  & t or "false" = t \
  UU &= (powerset("prereq"), subset.eq) \
  &attach(bot, br: UU) = emptyset subset.sq.eq { "true" }, {upar(a, 1)}, {
    ucol(z)
  } subset.sq.eq ... subset.sq.eq attach(top, br: UU) = "prereq" \
  SS &= "MapLat"(VV, UU) \
  evalentry("_"), evalexit("_") &:: "Node" -> SS
$
