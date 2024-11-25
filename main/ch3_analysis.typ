#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

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
  UtilParams := EmptyMap
  UtilFVs := EmptyMap
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
  &evalentry(mono("p:" lbl(e) "= x")) = s[x -> s(x) meet s(lbl(e))], "where" s = evalexit(p)\
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

== Parametric utilization

#let ann(body) = $angle.l.double body angle.r.double$

Given a function with annotated utilization $(p_1:ann(omega_1) t_1, ..., p_n:ann(omega_n)t_n) -> t_r$, argument  $p_i$ is utilized after the function call if $omega_i = 1$. In other words, $"util"(p_i)_"next" := "util"(p_i) + omega_i$.

$
  "await" :: ("Deferred"angles(T)) -> "T" \
  "await" :: (ann(1)"Deferred"angles(T)) -> "T"\
$

$
  "let" :: (D,  (D) -> E ) -> E \
  "let" :: (ann(omega) D,  (ann(omega) D) -> E ) -> E \
  "let"(x, f) = f(x)
$
$
  "applyTupple" :: ((D, D), (D) -> E) -> (E, E) \
  "applyTupple" :: ((ann(omega)D, ann(omega)D), (ann(omega)D) -> E) -> (E, E) \
  "applyTupple"(t, f) = (f(t_1), f(t_2))

$

A + operator might be allowed

$
  "toTuple" :: (D, (D) -> E, (D) -> E) -> (E, E) \
  "toTuple" :: (ann(omega_1 + omega_2)D, (ann(omega_1) D) -> E, (ann(omega_2)D) -> E) -> (E, E)\
  "toTuple"(x, f,g) = (f(x), g(x))
$

Parametric utilization at return position is currently not allowed, but possibly consistent.

$
  "applyId" :: (ann(omega) D, (ann(omega) D) -> ()) -> ann(omega)D\
  "applyId"(x, g) = g(x); x\

  "id" :: (ann(omega)D) -> ann(omega)D\
  "id"(x) = x \

  "choose" :: ("Bool", ann(omega_1) D, ann(omega_2) D) -> ann(omega_1 + omega_2) D\
  "choose"(c,x,y) = x "if" c, "otherwise" y
$

Term & Prerequisite lattice:

$
  "term" &::= upar(f, i) | "ret" \
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


Pairwise or operator:
$
   A orpair B &= { a or b | a in A, b in B }
$

$
  cal(U) ::= 1 | 0 | omega_k\
  "UtilParam"(F, i) :: "Func" -> NN -> cal(U)\
  "UtilFV"(F) :: "Func" -> "Var" -> cal("U")\

$



Transfer function:

$
  &evalexit(mono("exit")) = { x -> { "false" } | x in R without "CS" } union { f -> emptyset | f in "CS" } \

  &evalexit(p) = join.big_(q in "succ"(p)) evalentry(q) \

  &evalentry(mono("p: x :=" lbl(e))) = s[lbl(e) -> s(lbl(e)) orpair s(x), x -> { "false" }], "where" s = evalexit(p) \

  &evalentry(mono("p:" lbl(e) "= f") | mono(f) in C) = s[f ->s(lbl(e))], "where" s = evalexit(p)\

  &evalentry(mono("p:" lbl(e) "= x")) = s[x -> s(x) orpair s(lbl(e))], "where" s = evalexit(p)\
$

$
  &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl(a_1), ..., lbl(a_n) )) = (
    "MarkFV" compose "MarkArgs" compose "UpdateCall"
  )(evalexit(p)) \
    & quad "where:" \

    & quad "UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
    & quad "MarkArgs"(s) = s[lbl(a_i) -> "mark"(s, lbl(a_i), u) | (i -> u) in "UtilParam"(f')]\

    & quad "MarkFV"(s) = s[x -> "mark"(s, x, u) | (x -> u) in "UtilFV"(f')] \

    & quad "mark"(s, alpha, u) =  cases(

      { "true" } &"if" u = 1,
      s(alpha) orpair "ConcreteUtil"(omega_k) & "if" u = omega_k,
      s(alpha) orpair {upar(f', i)} & f' in "Params",
      s(alpha) & "otherwise",
      // s(alpha)  &"otherwise"
    ) \

    & quad "ConcreteUtil" = "Instance"("type"(f'), (a'_1, ..., a'_n))\
    & quad f' = "resolve"(lbl(f))\
    & quad a'_i = "resolve"(lbl(a_i)) "for" i in [1..n] \
    & quad "resolve"(lbl(e)) = evalexit(p)_("FA")(lbl(e)) \

$

Instantiation of parameteric utilization. $"Instance"(t,a_1..a_n)$ returns map of ${omega -> UU}$

$
  "Instance"(t, (a_1, ..., a_n))
 = union.big_((t_phi, phi) in "FA") "InstFuncArg"(t_phi, phi)\
  quad "where" "FA" = { (t (i), a_i) | i in [1..n] and t (i) "is a function type" }\

  "InstFuncArg"(t, phi) = union.big_(alpha_i in "args"(phi)) "InstArg"(phi, t (i), alpha_i)
  \

  "InstArg"(phi, t, alpha_i) = cases(
    "InstFuncArg"(t, alpha_i)    & "if" t "is a function type",
    { omega_k -> "ArgUtil"(phi,i) } & "if" t "has a parametric util." omega_k,
    emptyset                      & "otherwise"
  ) \

  "ArgUtil"(phi, i) = cases(
    { "true" }        & "if" "UtilParam"(phi, i) = 1,
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

  & Upsilon(g, i) = cases(
    "true" &"if" g in "Params" and "arg"(g,i) "has util. ann." ann(1),
    omega_k &"if" g in "Params" and  "arg"(g,i) "has util. ann." ann(omega_k),
    "false" &"otherwise",
  ) \

  &"eval"(u) = and.big_(t in u') t "where" u' = u|_(upar(g,i) = Upsilon(g,i)) forall i, g in "Params" \

  &"Replace"(s, f) = { x -> "eval"(u) | x -> u in s}
  \
  &"If F is a local function (without" ann(omega) "inference):" \
  &"UtilParams(F)" = { "index"(v) -> 1 | v in "Params" and evalentry(mono("start"))(f) leqsq {"true"} }\
  &"UtilFV(F)" = { v -> 1 | v in "FV" and evalentry(mono("start"))(f) leqsq {"true"} }\
$

#pagebreak()


Example:
#listing("Example kotlin")[
```kotlin
fun T, R> (@u1 T).let(f: (@u1 T) -> R): R = f(this)

fun test(g: (Deferred) -> ()) {
  val x = Deferred(...)

  if (...) {
    x.let(g)
  } else {
    val l1 = { it.await() }
    x.let(l1)
  }
}
```]

#listing("With analysis")[
```kotlin
fun T, R> (@u1 T).let(f: (@u1 T) -> R): R = f(this)
  // UtilPar(let) = {0 (this) -> u1}

fun test(g: (Deferred) -> ()) { // UtilPar(g) = {0 -> 0}

  val x = Deferred(...) // callsite d1 -> s(x) = {par(g,0), true}

  // x -> true_branch(x) join false_branch(x) = {par(g,0), true}
  if (...) {
    x.let(g)    // x -> {false} V↔ Concrete(u1) = {par(g, 0)}
                // Concrete(u1) = {par(g,0)},
                //    since UtilPar(g) != 1 & g in Params
                // Instantiate((@u1 T) -> R, g: (T) -> R)

  } else {
    val l1 = { it.await() } // UtilPar(l1) = {0 (it) -> 1}

    x.let(l1)   // x -> {false} V↔ Concrete(u1) = {true}
                // Concrete(u1) = {true}, since UtilPar(l1, 0) = 1
                // Instantiate((@u1 T) -> R, l1: (@1 T) -> R)
  }

  // x -> {false}
}
```]<withAnalysis>



#pagebreak()

/*
== With zero

$
   A union.dot B &= union.big_((a, b) in  A times B) {a union b} \

   A accent(union.dot, arrow.l) t &= {a union {t} | a in A} = A union.dot {{t}}\
$

$
  "term" ::= 0 | 1 | omega_k | upar(f,i)\
  "prereq" = powerset("term")\

  cal(U) = powerset("prereq")

$

$
  &Z = {{0}} \
  &evalexit(mono("exit")) = { x -> Z | x in R without "CS" } union { f -> emptyset | f in "CS" } \

  &evalexit(p) = join.big_(q in "succ"(p)) evalentry(q) \

  &evalentry(mono("p: x :=" lbl(e))) = s[lbl(e) -> s(lbl(e)) union.dot s(x), x -> Z ], "where" s = evalexit(p) \

  &evalentry(mono("p:" lbl(e) "= f") | mono(f) in C) = s[f ->s(lbl(e))], "where" s = evalexit(p)\

  &evalentry(mono("p:" lbl(e) "= x")) = s[x -> s(x) union.dot s(lbl(e))], "where" s = evalexit(p)\
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
*/
