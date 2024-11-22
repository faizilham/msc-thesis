#import "../lib/symbols.typ": *

= Value Usage and Utilization Analysis

== Desired properties

== Definitions

Given $s$ a mapping of $X -> Y$, $s[x -> y]$ means replace any mapping $(x -> *)$ in $s$ with $(x -> y)$. Formally:

$
  &s[x -> y] &&= (s without {x -> *}) union {x -> y} \
  &s[x_1 -> y_1, x_2 -> y_2]& &= (s[x_1 -> y_1])[x_2 -> y_2] \
  &s[x -> y | phi(x) ] &&= cases(
    s[x -> y] & "for all" x "that satisfy predicate "phi(x),
    s         & "otherwise"
  )
$

Map lattice:

$
  M = "MapLat"(A, L) = (A -> L, attach(leqsq, br: L))\
  "where, for all" m_1, m_2 in powerset(M), "this property holds":\
  m_1 leqsq m_2 equiv forall a in A . m_1(a) attach(leqsq, br: L) m_2(a)
$

Algorithms

```
Analyze(F, UpperAlias):
  Warnings := EmptySet
  AliasPerNode := AnalyzeFunctionAlias(F) + UpperAlias
  UtilParams := EmptySet
  UtilFVs := EmptySet
  for each local function G in F:
    (W, P, F) := Analyze(G, AliasPerNode)
    Warnings := Warnings + W
    UtilParams[G] := P
    UtilFVs[G] := F

  UtilPerNode := AnalyzeUtilization(AliasPerNode, UtilParams, UtilFVs)
  S := UtilPerNode[start]
  return (Warnings + GenWarning(S), GenUtilParam(S), GenUtilFV(S))
```

Transfer function:

$
  &evalexit(mono("exit")) = { x -> top | x in R without C } union { f -> bot | f in C } \
  &evalexit(p) = join.big_(q in "succ"(p)) evalentry(q) \
  &evalentry(mono("p: x :=" lbl(e))) = s[lbl(e) -> s(lbl(e)) meet s(x), x -> top], "where" s = evalexit(p) \
  &evalentry(mono("p:" lbl(e) "= f") | mono(f) in C) = s[f ->s(lbl(e))], "where" s = evalexit(p)\
  &evalentry(mono("p:" lbl(e) "= x")) = s[x -> s(x) meet s(lbl(e)), x -> top], "where" s = evalexit(p)\
  &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl(a_1), ..., lbl(a_n) )) = (
    "UseFV" compose "UseArgs" compose "UpdateCall"
  )(evalexit(p)) \
    & quad "where:" \
    & quad "UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
    & quad "UseArgs"(s) = s[a_i -> "UT" | i in "UtilParam"(f)] \
    & quad "UseFV"(s) = s[x -> "UT" | x in "UtilFV"(f)] \
  &\

  &evalentry(mono("p: return" lbl(e))) = evalexit(p)[lbl(e) -> lbl(e) meet "RT"]\
  &evalentry(p) = evalexit(p)
$


Analysis result

$
  &"Warnings" = {f | f in C and evalentry(mono("start"))(f) leqsq.not "RT" } \
  &"If F is a local function:"\
  &"UtilParams(F)" = { "index"(v) | v in "Params" and evalentry(mono("start"))(f) leqsq "UT" }\
  &"UtilFV(F)" = { v | v in "FV" and evalentry(mono("start"))(f) leqsq "UT" }\
$

== A more contextual warning

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
  & (t_1 or t_2) or t_3 = t_1 or (t_2 or t_3) \
  & t or "true" = "true"\
  & t or "false" = t \
  UU &= (powerset("prereq"), subset.eq) \
  &attach(bot, br: UU) = emptyset subset.sq.eq { "true" }, {upar(a, 1)}, {
    ucol(z)
  } subset.sq.eq ... subset.sq.eq attach(top, br: UU) = "prereq" \
  SS &= "MapLat"(VV, UU) \
$

$
  cal(U) ::= "true" | "false" | omega_k\
  "UtilParam"(F, i) :: "Func" -> ZZ -> cal(U)\
  "UtilFV"(F) :: "Func" -> powerset("Var" times cal("U"))\

$


Transfer function:

$
  &evalexit(mono("exit")) = { x -> top | x in R without "CS" } union { f -> bot | f in "CS" } \

  &evalexit(p) = join.big_(q in "succ"(p)) evalentry(q) \

  &evalentry(mono("p: x :=" lbl(e))) = s[lbl(e) -> s(lbl(e)) orpair s(x), x -> top], "where" s = evalexit(p) \

  &evalentry(mono("p:" lbl(e) "= f") | mono(f) in C) = s[f ->s(lbl(e))], "where" s = evalexit(p)\

  &evalentry(mono("p:" lbl(e) "= x")) = s[x -> s(x) orpair s(lbl(e)), x -> top], "where" s = evalexit(p)\
$

$
  &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl(a_1), ..., lbl(a_n) )) = (
    "MarkFV" compose "MarkArgs" compose "UpdateCall"
  )(evalexit(p)) \
    & quad "where:" \

    & quad "UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
    & quad "MarkArgs"(s) = s[lbl(a_i) -> "mark"(s, lbl(a_i), "UtilParam"(f', i)) | i in [1..n] and lbl(a_i) :: "UType"]\

    & quad "MarkFV"(s) = s[x -> "mark"(s, x, u) | (x, u) in "UtilFV"(f')] \

    & quad "mark"(s, alpha, u) =  cases(

      { "true" } &"if" u = "true",
      s(alpha) orpair "ConcreteUtil"(omega_k) & "if" u = omega_k,
      s(alpha) orpair upar(f', i) & f' in "Params",
      s(alpha) & "otherwise",
      // s(alpha)  &"otherwise"
    ) \

    & quad "ConcreteUtil" = "Unify"(tau(f'), (a'_1, ..., a'_n))\
    & quad f' = "resolve"(lbl(f))\
    & quad a'_i = "resolve"(lbl(a_i)) "for" i in [1..n] \
    & quad "resolve"(lbl(e)) = evalexit(p)_(Phi)(lbl(e)) \

$

Unification of parameteric utilization

$
  "Unify"(t, (a_1, ..., a_n))
 = union.big_((t_phi, phi) in "FA") "UnifyFuncArg"(t_phi, phi)\
  quad "where" "FA" = { (t (i), a_i) | i in [1..n] and t (i) "is a function type" }\

  "UnifyFuncArg"(t, phi) = union.big_(alpha_i in "args"(phi)) "UnifyArg"(phi, t (i), alpha_i)
  \

  "UnifyArg"(phi, t, alpha_i) = cases(
    "UnifyFuncArg"(t, alpha_i)    & "if" t "is a function type",
    { omega_k -> "ArgUtil"(phi,i) } & "if" t "has a parametric util." omega_k,
    emptyset                      & "otherwise"
  ) \

  "ArgUtil"(phi, i) = cases(
    { "true" }        & "if" "UtilParam"(phi, i) = "true",
    { upar(phi, i) }  & "if" phi in "Params",
    { "false" }       & "otherwise"
  )\
$

$
  &evalentry(mono("p: return" lbl(e))) = evalexit(p)[lbl(e) -> lbl(e) orpair { ret }]\

  &evalentry(p) = evalexit(p)
$

Analysis result

$
  &"Warnings" = {f | f in "CS" and evalentry(mono("start"))(f) leqsq.not { "true", ret } } \
  &"If F is a local function:"\
  &"UtilParams(F)" = { "index"(v) | v in "Params" and evalentry(mono("start"))(f) leqsq {"true"} }\
  &"UtilFV(F)" = { v | v in "FV" and evalentry(mono("start"))(f) leqsq {"true"} }\
$
