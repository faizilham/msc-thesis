#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Usage and Utilization Tracking with Data Flow Analysis

TODO: polish

As we discuss in the previous chapter, there are several techniques related to utilization tracking. The utilization tracking problem maps almost one-to-one with substructural type systems, especially the relevant type system. However, we choose to use a data-flow analysis approach instead of a substructural type system one. This is because changing the Kotlin type system is complicated and introduces too much change to the compiler for a relatively small quality-of-life feature. In contrast, the compiler provides plugin support for running a data-flow analysis.


== Definitions

TODO: initial paragraph


=== Control flow graph

We first define a model of control flow graph (CFG) that we use in the data flow analysis. This CFG model is a simplified version of the real control flow graph in the Kotlin compiler.

We assume that each expression and sub-expression in the program's AST is labeled with a unique label $e$. @lst:ExprLabel shows an example of expressions labeling, in which the numbers written in superscript letter are the labels for the corresponding expression.

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

Given an expression label $e$, the value of the expression is denoted as $lbl(e)$. For example, using the expression labels in @lst:ExprLabel, the value of $lbl(1)$ is equal to 2, and the value of $lbl(3)$ is equal to $(lbl(1) + lbl(2))$, in other words the evaluation result of $(2 + x)$.

TODO: nodes explanation and transformation examples

All AST constructs are transformed into the following CFG nodes.
+ Function start #cfg[start] and exit #cfg[exit]
+ Literal constant. #cfg("$e = <Lit>")
+ Identifier access. #cfg("$e = x")
+ Variable declaration. #cfg("var x")
+ Variable assignment. #cfg("x := $val")
+ When begin #cfg("when_begin($cond)") and end #cfg("when_end")
+ Function call #cfg([\$e = \$f(\$arg#sub("1"), ... ,\$arg#sub("n"))])
+ Return statement. #cfg("return $val")
+ Lambda expression #cfg("$e = "+ $lambda$ +".{subgraph}")

=== Common Notations

TODO: notation definitions

Given $s$ a mapping of $X -> Y$, $s[x |-> y]$ equals to s but with $(x |-> *) in s$ replaced with $(x |-> y)$. Formally:

$
  &s[x |-> y] &&= (s without {x |-> *}) union {x |-> y} \
  &s[x_1 |-> y_1, x_2 |-> y_2]& &= (s[x_1 |-> y_1])[x_2 |-> y_2] \
  &s[x |-> y | phi(x) ] &&= cases(
    s[x |-> y] & "for all" x "that satisfy predicate "phi(x),
    s         & "otherwise"
  )
$

A map lattice $"MapLat"(A -> L)$ is a lattice of the mapping from set A to lattice L, and its ordering is equivalent to the ordering of lattice L.

$
  M = "MapLat"(A -> L) = (A -> L, attach(leqsq, br: L))\
  "where, for all" m_1, m_2 in powerset(M), "this property holds":\
  m_1 leqsq m_2 equiv forall a in A . m_1(a) attach(leqsq, br: L) m_2(a)
$

A powerset lattice $(powerset(A), subset.eq)$ is a lattice of the powerset of $A$, with subset or equal ($subset.eq$) as the ordering operator.

A flat lattice $"FlatLat"(A)$ is a lattice of set $A union {bot, top}$, with the ordering defined as $bot leqsq a leqsq top$, for all $a in A$.

A linearly ordered lattice $"OrderLat"(angles(bot = a_1, ..., a_n = top)) $ is a lattice of set ${a_1, ..., a_n}$ with the ordering defined as $a_i leqsq a_j$ iff. $i <= j$

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
TODO:

Examples


#let transferFuncName(name, body) = {
  let evalbracket = evalbracket.with(sub:name)
  let evalentry = evalentry.with(sub:name)
  let evalexit = evalexit.with(sub:name)

  body
}

#[
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")

$
  "Ref" &= "LocalVars" union "ExprLabel"\
  "CR" &= { f | f in "ExprLabel" and lbl(f) = mono("create") }\
$
Lattices

$
  U &= "OrderLat"(angles(bot, "UT", top)) \
  S &= "MapLat"("Ref" -> U) \
  evalbracket("_") &:: "Node" -> S\
$

Transfer function:
$
  &evalexit(mono("exit")) &&= { x |-> top | x in "Ref" without "CR" } union { f |-> bot | f in "CR" } \
  &evalexit(p) &&= join.big_(q in "succ"(p)) evalentry(q) \
  &evalentry(mono("p: x :=" lbl(e))) &&= spx[e |-> spx(e) meet spx(x)][x |-> top]\
  &evalentry(mono("p:" lbl(e) "= x")) &&= spx[x |-> s(x) meet s(e)]\

  &evalentry(mono("p:" lbl(e) = lbl(f)())) &&= spx[f |-> spx(e) | lbl(f) = mono("create")]\

  &evalentry(mono("p:" lbl(e) = lbl(f)(lbl(a)))) &&= spx[a |-> "UT" | lbl(f) = mono("utilize")]\

  &evalentry(p) &&= evalexit(p)\ \

  &"given" s_p^circle.small.filled = evalexit(p).

  // &evalentry(mono("p: return" lbl(e))) = evalexit(p)[lbl(e) -> lbl(e) meet "RT"]\

    // &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl(a_1), ..., lbl(a_n) )) = (
  //   "UseFV" compose "UseArgs" compose "UpdateCall"
  // )(evalexit(p)) \
  //   & quad "where:" \
  //   & quad "UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
  //   & quad "UseArgs"(s) = s[a_i -> "UT" | i in "UtilParam"(f)] \
  //   & quad "UseFV"(s) = s[x -> "UT" | x in "UtilFV"(f)] \
  // &\
$
]

Analysis result

$
  "Warnings" = {f | f in "CR" and evalentry(mono("start"))(f) leqsq.not "UT" } \
  // &"If F is a local function:"\
  // &"UtilParams(F)" = { "index"(v) | v in "Params" and evalentry(mono("start"))(f) leqsq "UT" }\
  // &"UtilFV(F)" = { v | v in "FV" and evalentry(mono("start"))(f) leqsq "UT" }\
$


=== Forward analysis
TODO:

#[ /* Start of Safely Reachable Value */
#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

Safely reachable value analysis
$
  &"Ref" &&= "LocalVars" union "ExprLabel"\
  &"CR" &&= { f | f in "ExprLabel" and lbl(f) = mono("create") }\
$

Lattices
$
  &"VarAt" &&= {(x, p) | x in "LocalVars", p in "Node"}\
  &R &&= (powerset("VarAt" union "CR"), subset.eq)\
  &O &&= (powerset("CR"), subset.eq)\
  &S &&= "MapLat"("Ref" -> (R, O))\
  &evalbracket("_") &&:: "Node" -> S\
$

Transfer functions, given $sp = evalentry(p)$ and $(rpe(x), ope(x)) = sp(x) $
$
  &evalentry(mono("start")) &&= { e |-> (emptyset, emptyset) | e in "Ref" without "CR" } union {f |-> ({f}, emptyset) | f in "CR"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
$

$
  &evalexit(mono("p:" lbl(e) = lbl(f)())) &&= sp[e |-> ({f}, emptyset) | lbl(f) = mono("create")]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> ({ (x, p) }, emptyset) ]\

  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> (rpe(e), ope(x) union (rpe (e) sect "CR" )) ]\
  &evalexit(p) &&= evalentry(p)\
  \
$ <eq:RVTransferFunc>


Safely reachable references and source calls

// $"SafeRef" :: "Node" times "LocalVars" -> R$,
// $"Source" :: "Node" times "LocalVars" -> {"CR"}$

$
  &"SafeReach"(p, e) &&= cases(
    r_e & "if" abs(r_e) <= 1,
    (r_e sect "CR") without o_e& "otherwise"
  )\
  &&&"where" (r_e, o_e) = evalexit(p)(e)\

  &"Source"(p, e) &&= cases(
    "Source"(p', x) & "if" sigma = {(x, p')},
    sigma & "otherwise"
  )\
  &&&"where" sigma = "SafeReach"(p, e)
$
] /* End of Safely Reachable Value */


TODO: examples



#[
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")

Utilization analysis

Lattice (same as backward)
$
  U = "OrderLat"(angles(bot, "UT", top)) \
  S = "MapLat"("Ref" -> U) \
  evalbracket("_") :: "Node" -> S\
$


Transfer function
$
  &evalentry(mono("start")) &&= { x |-> top | x in "Ref" without "CR" } union { f |-> bot | f in "CR" }\
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \

  &evalexit(mono("p:" lbl(e) = mono("create")^f"()")) &&= sp[f |-> top, e |-> top]\

  &evalexit(mono("p:" lbl(e) = mono("utilize")^f (lbl(a)))) &&= sp[a' |-> "UT" | a' in "Source"(p, a)]\

  &evalexit(p) &&= evalentry(p)\ \

  &"given" sp = evalentry(p).
$
]


Analysis result, warning = ${f | f in "CR" and evalentry(mono("start"))(f) leqsq.not "UT" }$
== Generalizing function calls
TODO: defining behaviors

functions can:
- utilize any of its argument
- returns a new utilizable values
- in case of lambdas, utilize any of its free variable
- invalidates argument or free variable

=== Utilization function signature

#let ann(body) = $angle.l.double body angle.r.double$
#let ef = math.accent("e", math.hat)
#let efv = math.epsilon
#let andef = pad(left: 0.01em, right:0.01em, text(size: 0.85em, "&"))
#let plusef = math.plus.circle
#let timesef = math.times.circle
#let efs(l, r) = $#l parallel #r$
// #let efl(..body) = $bracket #body.pos().join(",") bracket.r$
#let efl(..body) = angles(..body)

TODO: text

$E ::= U | N | I $

where $U$ = Utilized, $N$ = Not changed, $I$ = Invalidated, with operators $(plusef, timesef)$ defined as follows.

$
  // ef + ef = ef; ef_1 + ef_2 = ef_2 + ef_1\
  // ef dot ef = ef; ef_1 dot ef_2 = ef_2 dot ef_1\
  U plusef N = U", and" ef plusef I = I "for all" ef :: E\
  U timesef N = N", and" ef timesef I = I "for all" ef :: E\

$

Both operators obey idempotence ($ef circle ef = ef$) and commutative ($ef_1 circle ef_2 = ef_2 circle ef_1$) properties.

A function type can be annotated with utilization effects after the return type,
such as

// $f :: t_1 -->^angles(ef_1, theta_1) ... -->^angles(ef_(n-1),theta_(n-1)) t_n -->^angles(ef_n,theta_n) t_ret$

$wide f ::(t_1,..., t_n) -> t_ret andef efs(efl(ef_1, ..., ef_n), Theta)$

where $Theta = {v |-> ef_v | v in "FV"(f)}$.

This notation indicates that after the call of $f$, the effect $ef_i$ is applied to the value passed as $i$-th argument, and $ef_v$ is applied to free variable $v$.

A non-annotated function type is equivalent to having no effect to its arguments and free variables.

$wide f ::(t_1,..., t_n) -> t_ret andef efs(efl(N, ..., N), {v |-> N | v in "FV"(f)})$

Because many functions do not have free variables, it is often the case that $Theta = emptyset$. For convenience, we shorten the notation in such cases:

$wide f ::(t_1,..., t_n) -> t_ret andef efl(ef_1, ..., ef_n)$


For example, the function "`await(x: Deferred<t>): t`" can be notated as:

$wide "await" :: ("Deferred"[t]) -> t andef efl(U)$

Effect annotation can also be parametric, especially for higher order function. For example, the function "`let(x: a, f: a -> b): b`" can be notated as:

$wide "let" ::(a, (a) -> b andef efs(efl(efv), theta)) -> b andef efs(efl(efv, N), theta)$

// $f :: ann(omega_1) t_1 ->^(ef_1)_(theta_1) ... ->^(ef_(n-1))_(theta_(n-1)) ann(omega_n) t_n ->^(ef_n)_(theta_n) t_ret$


// $f ::(ann(omega_1)t_1,...,ann(omega_n) t_n) -> t_ret andef angles((ef_1, ..., ef_n), Theta)$

=== Analysis with function signature


- function alias analysis

(in appendix?)

#[ /* Start of Function Alias Analysis */
#let evalbracket = evalbracket.with(sub:"FA")
#let evalentry = evalentry.with(sub:"FA")
#let evalexit = evalexit.with(sub:"FA")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

Function alias analysis
$
  &"Ref" &&= "LocalVars" union "ExprLabel"\
  &"Func" &&= {"Set of function declarations"}\
$

Lattices
$
  &F &&= "FlatLat"("Func")\
  &S &&= "MapLat"("Ref" -> F)\
  &evalbracket("_") &&:: "Node" -> S\
$

Transfer functions, given $sp = evalentry(p)$,
$
  &evalentry(mono("start")) &&= { e |-> bot | e in "Ref"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
$

$

  &evalexit(mono("p:" lbl(e) = "f") | f in "Func") &&= sp[e |-> f ]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> sp(x) ]\
  &evalexit(mono("p:" lbl(e) = lambda.{...})) &&= sp[e |-> lambda ]\
  &evalexit(mono("p:" lbl(e) = lbl(f)(...))) &&= sp[e |-> top ]\

  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> sp(e)]\
  &evalexit(p) &&= evalentry(p)\
  \
$

Resolve function alias: $"Resolve"(p, e) = evalexit(p)(e)$, $"Resolve"::"Node" times "Ref" -> ("Func" + bot + top)$
] /* End of Function Alias Analysis */

We also want the analysis to track utilizable values returned from any function calls, and not only from `create` calls. To allow this, we need to modify the transfer function of the safely-reachable value analysis defined in @eq:RVTransferFunc as follows.

$
  "Replace the equation:"\
  evalexit(sub:"RV", mono("p:" lbl(e) = lbl(f)())) = sp[e |-> ({f}, emptyset) | lbl(f) = mono("create")]\

  "With this equation:"\
  evalexit(sub:"RV", mono("p:" lbl(e) = lbl(f) (...))) = sp[e |-> ({f}, emptyset) | "RetType"(lbl(f)) "is Utilizable"]\
$ <eq:RVModifyCreateFunc>

TODO: The complete modification is provided in Appendix ...

=== Inferencing lambda signature
TODO: text

== Utilizable collection types
TODO: text

- maintaining invariant: Items in collection are either all utilized or not

=== Utilization preconditions

A function signature can also denotated with utilization preconditions in its parameter:

$wide f :: (ann(omega_1) t_1, ..., ann(omega_n) t_n) -> t_ret andef efs(efl(ef_1, ..., ef_n), Theta)$

where $omega_i subset.eq {0, 1}$, 0 = Not Utilized, 1 = Utilized.

This indicates that the call of function $f$ requires $"utilization"(a_i) in omega_i$ for each $a_i$ the value passed as $i$-th argument. If there is an argument that doesn't fulfil its precondition, it should be reported as an error. Any parameters without annotations are the same as annotated with $ann(0|1)$.

=== Collection utilization
Collection functions
$
  "utilizeAll" :: (C[a]) -> () andef efl(U)\
  "map" :: (ann(omega)C[a], (ann(omega)a) -> b andef efs(efl(efv), theta)) -> C[b] andef efs(efl(efv, N), theta)\
  "add" :: (C[a], a) -> () andef efl(I, U)\
  "remove" :: (ann(1) C[a], a) -> ()\
  "filter" :: (ann(1) C[a], (a)-> "Bool" andef efs(efl(efv), theta)) -> C[a] andef efs(efl(efv, N), theta)\
$


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
