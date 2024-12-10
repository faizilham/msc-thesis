#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Handling Collection Types and Other Extensions
TODO: text

- maintaining invariant: Items in collection are either all utilized or not

== Utilization preconditions

A function signature can also denotated with utilization preconditions in its parameter:

$wide f :: (ann(omega_1) t_1, ..., ann(omega_n) t_n) -> t_ret andef efs(efl(ef_1, ..., ef_n), Theta)$

where $omega_i subset.eq {0, 1}$, 0 = Not Utilized, 1 = Utilized.

This indicates that the call of function $f$ requires $"utilization"(a_i) in omega_i$ for each $a_i$ the value passed as $i$-th argument. If there is an argument that doesn't fulfil its precondition, it should be reported as an error. Any parameters without annotations are the same as annotated with $ann(0|1)$.

=== Analysis with preconditions

// Design limitation: no parametric preconditions for now

- no parametric preconditions
- precondition check in function call rule

== Collection utilization
Collection functions
$
  "utilizeAll" :: (C[a]) -> () andef efl(U)\
  "map" :: (ann(omega)C[a], (ann(omega)a) -> b andef efs(efl(efv), theta)) -> C[b] andef efs(efl(efv, N), theta)\
  "add" :: (C[a], a) -> () andef efl(I, U)\
  "add" :: (ann(omega)C[a], ann(omega) a) -> () andef efl(N, U)\
  "remove" :: (ann(1) C[a], a) -> ()\
  "filter" :: (ann(1) C[a], (a)-> "Bool" andef efs(efl(efv), theta)) -> C[a] andef efs(efl(efv, N), theta)\
$

== A better error reporting
TODO: text
drop?

== Limitations
TODO: text

- Util signature of function-returning function
- Parametric preconditions

== Usage analysis
TODO: text

here? drop?

- Discardable-ness
- Same-use
- Inference of discardable and same-use

#pagebreak()
== Notes (TODO: temporary, will be moved or deleted)

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



A function type can be annotated with utilization effects after the return type,
such as

$f ::(t_1,...,t_n) -> t_r andef (epsilon_1, ..., epsilon_n)$,

Given a function $f(a_1, ..., a_n) :: (t_1,...,t_n) -> r andef (epsilon_1, ..., epsilon_n)$, the utilization of argument $a_i$ after the function call is equal to $"EvalEff"(epsilon_i, s[a_i])$

$
  "EvalEff"(e, u) = cases(
    { "true" } & "if" e = U,
    u & "if" e = N,
    { "false" } & "if" e = I
  )
$

Annotation examples:

$
  "await" :: ("Deferred"angles(T)) ->^U "T" \
  "await" :: ("Deferred"angles(T)) -> "T" andef U\
$

$
  "let" :: (A,  (A) -> B ) -> B \
  "let" :: A ->^epsilon (A ->^epsilon B ) -> B \
  "let" :: (A,  (A) -> B andef epsilon ) -> B andef (epsilon, N) \
  "let"(x, f) = f(x)\
$
$

  "applyTwo" :: (A, A, (A) -> B andef epsilon) -> (B, B) andef (epsilon, epsilon, N) \
  "applyTwo" :: A ->^epsilon A ->^epsilon (A ->^epsilon B) -> (B, B)\
  "applyTwo"(x, y, f) = (f(x), f(y))

$

A + operator might be allowed

$
  "toTuple" :: (A, (A) -> B, (A) -> B) -> (B, C) \
  "toTuple" :: A -->^(epsilon_1 + epsilon_2) (A ->^(epsilon_1) B) -> (A ->^(epsilon_2) C) -> (B, C) \
  "toTuple" :: (A, (A) -> B andef epsilon_1, (A) -> C andef epsilon_2) -> (B, C) andef (epsilon_1 + epsilon_2, N, N) \
  "toTuple" :: (\
  wide quad x: A,\
  wide quad f: (a_f: A) -> B andef epsilon_f,\
  wide quad g: (a_g: A) -> C andef epsilon_g\
  wide ) -> (B, C) andef {x arrow.bar epsilon_f (a_f) + epsilon_g (a_g)} \
$
$
  "toTuple"(x, f, g) = (f(x), g(x))
$

// Parametric utilization at return position is currently not allowed, but possibly consistent.

// $
//   "applyId" :: (ann(omega) D, (ann(omega) D) -> ()) -> ann(omega)D\
//   "applyId"(x, g) = g(x); x\

//   "id" :: (ann(omega)D) -> ann(omega)D\
//   "id"(x) = x \

//   "choose" :: ("Bool", ann(omega_1) D, ann(omega_2) D) -> ann(omega_1 + omega_2) D\
//   "choose"(c,x,y) = x "if" c, "otherwise" y
// $

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
  // "UtilParam"(F, i) :: "Func" -> NN -> cal(U)\
  // "UtilFV"(F) :: "Func" -> "Var" -> cal("U")\
  "FuncEffects" :: "Func" -> NN + "Var" -> E
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
    & quad "MarkArgs"(s) = s[lbl(a_i) -> "mark"(s, lbl(a_i), ef) | (i -> ef) in "FuncEffects"(f')]\

    & quad "MarkFV"(s) = s[x -> "mark"(s, x, ef) | (x -> ef) in "FuncEffects"(f')] \

    & quad "mark"(s, alpha, ef) =  cases(
      "EvalEff"("Instantiate"(epsilon, k), s(alpha)) & "if" ef = epsilon (k),
      "EvalEff"(ef, s(alpha)) & "otherwise",
    ) \

    // & quad "mark"(s, alpha, u) =  cases(

    //   { "true" } &"if" u = 1,
    //   s(alpha) orpair "ConcreteUtil"(omega_k) & "if" u = omega_k,
    //   s(alpha) orpair {upar(f', i)} & f' in "Params",
    //   s(alpha) & "otherwise",
    //   // s(alpha)  &"otherwise"
    // ) \
    //
    & quad "EvalEff"(e, u) = cases(
      { "true" } & "if" e = U,
      u & "if" e = N,
      { "false" } & "if" e = I
    )\

    & quad "Instantiate"(epsilon, k) = "Resolve" epsilon "in" a'_1...a'_n, "apply" epsilon(k)\

    // & quad "ConcreteEff" = "Instance"(p, "type"(f'), (lbl(a_1), ..., lbl(a_n)))\
    & quad f' = "resolve"(p, lbl(f))\
    & quad "resolve"(p, lbl(e)) = evalexit(p)_("FA")(lbl(e))\

$

// Instantiation of parameteric utilization effect.

// $
//   "Instance"(p, t andef epsilon, (a_1, ..., a_n))
//  = union.big_((t_alpha, alpha) in "FA") "InstFuncArg"(t_alpha, "resolve"(p, alpha), "EP")\
//   quad "where" "FA" = { (t (i), a_i) | i in [1..n] and t (i) "is a function type" }\
//   quad "         EP" = {epsilon_k | epsilon_k "appearing in" epsilon}\

//   "InstFuncArg"(t andef epsilon, phi, e) = {} union union.big_(alpha_i in "args"(phi)) "InstArg"(phi, t (i), alpha_i)
//   \

//   "InstArg"(phi, t, alpha_i) = cases(
//     "InstFuncArg"(t, alpha_i)    & "if" t "is a function type",
//     { epsilon_k -> "ArgUtil"(phi,i) } & "if" t "has a parametric eff." epsilon_k,
//     emptyset                      & "otherwise"
//   ) \

//   "ArgUtil"(phi, i) = cases(
//     { "true" }        & "if" "UtilParam"(phi, i) = 1,
//     { upar(phi, i) }  & "if" phi in "Params",
//     { "false" }       & "otherwise"
//   )\
// $


// Instantiation of parameteric utilization. $"Instance"(t,a_1..a_n)$ returns map of ${omega -> UU}$

// $
//   "Instance"(t, (a_1, ..., a_n))
//  = union.big_((t_alpha, alpha) in "FA") "InstFuncArg"(t_alpha, alpha)\
//   quad "where" "FA" = { (t (i), a_i) | i in [1..n] and t (i) "is a function type" }\

//   "InstFuncArg"(t, phi) = union.big_(alpha_i in "args"(phi)) "InstArg"(phi, t (i), alpha_i)
//   \

//   "InstArg"(phi, t, alpha_i) = cases(
//     "InstFuncArg"(t, alpha_i)    & "if" t "is a function type",
//     { omega_k -> "ArgUtil"(phi,i) } & "if" t "has a parametric util." omega_k,
//     emptyset                      & "otherwise"
//   ) \

//   "ArgUtil"(phi, i) = cases(
//     { "true" }        & "if" "UtilParam"(phi, i) = 1,
//     { upar(phi, i) }  & "if" phi in "Params",
//     { "false" }       & "otherwise"
//   )\
// $

$
  &evalentry(mono("p: return" lbl(e))) = evalexit(p)[lbl(e) -> lbl(e) orpair { ret }]\

  &evalentry(p) = evalexit(p)
$

Analysis result

$
  &"Warnings" = {f | f in "CS" and evalentry(mono("start"))(f) leqsq.not { "true", ret } } \

  // & Upsilon(g, i) = cases(
  //   "true" &"if" g in "Params" and "arg"(g,i) "has util. ann." ann(1),
  //   omega_k &"if" g in "Params" and  "arg"(g,i) "has util. ann." ann(omega_k),
  //   "false" &"otherwise",
  // ) \

  // &"eval"(u) = and.big_(t in u') t "where" u' = u|_(upar(g,i) = Upsilon(g,i)) forall i, g in "Params" \

  // &"Replace"(s, f) = { x -> "eval"(u) | x -> u in s}
  \

$
If F is a local function (without inference):
$


  "FuncEffects(F)" =
        & { "index"(v) -> U | v in "Params" and evalentry(mono("start"))(v) leqsq {"true"} }\
        & union { v -> U | v in "FV" and evalentry(mono("start"))(v) leqsq {"true"} }
  \
$

with list

$
  // &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl(a_1), ..., lbl(a_n) )) = (
  //   "MarkFV" compose "MarkArgs" compose "UpdateCall"
  // )(evalexit(p)) \
  //   & quad "where:" \

  //   & quad "UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
  //   & quad "MarkArgs"(s) = s[lbl(a_i) -> "mark"(s, lbl(a_i), u) | (i -> u) in "UtilParam"(f')]\

  //   & quad "MarkFV"(s) = s[x -> "mark"(s, x, u) | (x -> u) in "UtilFV"(f')] \

  //   & quad "mark"(s, alpha, u) =  cases(

  //     { "true" } &"if" u = 1,
  //     { "false" } &"if" u = -1,
  //     s(alpha) orpair "ConcreteUtil"(omega_k) & "if" u = omega_k,
  //     s(alpha) orpair {upar(f', i)} & f' in "Params",
  //     s(alpha) & "otherwise",
  //     // s(alpha)  &"otherwise"
  //   ) \

  &evalentry("p:" lbl(e) ="utilize"(lbl(c))) = s[lbl(c) -> "mark"(s, lbl(c), U) = {"true"}]\
  &evalentry("p:" lbl(e) ="map"(lbl(c), lbl(f))) = s[lbl(c) -> "mark"(s, lbl(c), "FuncEffects"(f', 1))]\
  &evalentry("p:" lbl(e) ="add"(lbl(c), lbl(x))) = s[lbl(x) -> s(c') | lbl(c) "is expression of var" c']\
  &evalentry("p:" lbl(e) ="filter"(lbl(c), lbl(f))) = s[lbl(c) -> {"false"_lbl(e)}]\
$

// $
//   "utilize" :: (ann(1) C angles(U)) -> ()\
//   "map" :: (ann(omega) C angles(U), (ann(omega) U) -> T ) -> C angles(T)\
//   "add" :: (ann(omega) C angles(U), ann(omega) U) -> ()\
//   // "add" :: (C angles(U), ann(1) U) -> ()\
//   "remove" :: (ann(-1) C angles(U), U) -> ()\
//   "filter" :: (ann(-1) C angles(U), (U)-> "Bool") -> C angles(U)\
// $



Example:
#listing("Parametric utilization instantiation")[
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
