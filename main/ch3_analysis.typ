#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Usage and Utilization Tracking with Data Flow Analysis

TODO: polish

As we discuss in the previous chapter, there are several techniques related to utilization tracking. The utilization tracking problem maps almost one-to-one with substructural type systems, especially the relevant type system. However, we choose to use a data-flow analysis approach instead of a substructural type system one. This is because changing the Kotlin type system is complicated and introduces too much change to the compiler for a relatively small quality-of-life feature. In contrast, the compiler provides plugin support for running a data-flow analysis.


== Definitions

TODO: initial paragraph


=== Control flow graph

We first define a model of control flow graph (CFG) that we use in the data flow analysis. This CFG model is a simplified version of the real control flow graph in the Kotlin compiler.

We assume that each expression and sub-expression in the program's AST is labeled with a unique number $e$. @lst:ExprLabel shows an example of expressions labeling, in which each number written in superscript letter is the label number for the corresponding expression.

// ¹²³⁴⁵⁶⁷⁸⁹⁰
#listing("Expression labeling")[
```kotlin
fun test(x: Int, y: Boolean) {
  val a = (2¹ + x²)³

  if ((a⁴ >= 1⁵)⁶) {
    println⁷((a⁸ + 10⁹)¹⁰)¹¹
  }

  val b = (if (y¹²) 1¹³ else 0¹⁴)¹⁵
}
```]<lst:ExprLabel>


#let cfg(body) = text(font: "Consolas", [[#body]])

Given an expression label $e$, the value of the expression is denoted as $lbl(e)$. For example, using the expression labels in @lst:ExprLabel, the value of $lbl(1)$ is equal to 2, and the value of $lbl(3)$ is equal to $(2 + x)$.

TODO: nodes explanation and transformation examples

All AST constructs are transformed into the following CFG nodes.
+ Function start #cfg[start] and exit #cfg[exit]
+ Literal constant. #cfg("$e = <Lit>")
+ Identifier access. #cfg("$e = x")
+ Variable declaration. #cfg("var x := $val")
+ Variable assignment. #cfg("x := $val")
+ When begin #cfg("when_begin($cond)") and end #cfg("when_end")
+ Function call #cfg([\$e = \$f(\$arg#sub("1"), ... ,\$arg#sub("n"))])
+ Return statement. #cfg("return $val")
+ Lambda expression #cfg("$e = <"+ $lambda$ +".subgraph>")

=== Notations

TODO: notation definitions

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


#pagebreak()

== A simplified utilization model

Let us start with an overly simplified version of the problem. In this version, a utilizable value `u` can only be constructed by the function `create()` and utilized by the function `utilize(u)`. Other functions do not affect the utilization of any values. A value constructed by a `create` call is defined as utilized if, for every path the program execution might take, one can always eventually trace it to a `utilize` call. Any `create` calls that are not always traceable to a `utilize` call are not guaranteed to be utilized and should be reported as an error.

#listing("Utilization tracking in the simplified model")[
```kotlin
fun simple() {
  val a = create() /*C1: OK*/
  val a1 = a
  if (/*cond1*/) utilize(a) else utilize(a1)

  val b = if (/*cond2*/) create() /*C2: OK*/ else create() /*C3: OK*/
  utilize(b)

  val d = create() /*C4: Error*/
  val d1 = if (/*cond3*/) create() /*C5: OK*/ else d
  if (/*cond4*/) utilize(d)
  utilize(d1)

  var e = create() /*C6: Error*/
  if (/*cond5*/) e = create() /*C7: OK*/
  utilize(e)
}
```] <lst:SimpleModelExample>

@lst:SimpleModelExample shows an example of utilization tracking in this simplified model, with each `create` call marked with "OK" or "Error". In the example, the `create` call C1 can always be traced to a `utilize` via variable `a` or variable `a1`. Both C2 and C3 are utilized through variable `b`. The call C4 is the first error example. In this case, C4 is not utilized if the conditional expression `cond3` is true and and `cond4` is false. On the other hand, the call C5 is always utilized through variable `d1`, since if `cond3` is false the call C5 never happened and no value is created. The same reasoning also applies to call C6 and C7.

=== Backward analysis
TODO: text

=== Forward analysis
TODO: text

== Generalizing function calls
TODO: text

- function alias analysis

=== Utilization function signature
TODO: text

=== DFA with signature
TODO: text

== Tracking a collection of utilizable values
TODO: text

== A better error reporting
TODO: text

== Usage analysis
TODO: text

== Notes (TODO: temporary)

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

#let ann(body) = $angle.l.double body angle.r.double$

#let ef = math.accent("e", math.hat)

#let andef = pad(left: 0.01em, right:0.01em, text(size: 0.85em, "&"))

$E ::= U | N | I$

where $U$ = Utilized, $N$ = No change, $I$ = Invalidated, with operator $(+, dot)$ defined as:

$
  ef + ef = ef; ef_1 + ef_2 = ef_2 + ef_1\
  ef dot ef = ef; ef_1 dot ef_2 = ef_2 dot ef_1\
  U + N = U; ef + I = I\
  U dot N = N; ef dot I = I\
$

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

#pagebreak()

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


$
  "utilize" :: (C angles(A)) -> () andef U\
  "map" :: (C angles(A), (A) -> B andef epsilon) -> C angles(B) andef (epsilon, N)\
  "add" :: (ann(omega) C angles(A), U) -> () andef (N, Q(omega))\
  "add" :: ann(omega) C angles(A) -> U ->^(Q(omega)) ()\
  // "add" :: (C angles(A), ann(1) U) -> ()\
  "remove" :: (C angles(A), A) -> () andef (I, N)\
  "filter" :: (C angles(A), (A)-> "Bool") -> C angles(A) andef (I, N)\
$

#pagebreak()


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
