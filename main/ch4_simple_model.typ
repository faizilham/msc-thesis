#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= A Simplified Utilization Analysis

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

== Backward analysis
TODO:

Main idea: flow the utilization status backward, starting from each `utilize` calls.

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


== Forward analysis
TODO:

Main idea: track which value is definitely referred by a variable, or set of values that "lives" exclusively from each other: "safely reachable". Set those values to utilize status when passed to `utilize` function.

TODO: examples of safely reachable

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

Transfer functions, given $sp = evalentry(p)$ and $(rpe(x), ope(x)) = sp(x)$
$
  &evalentry(mono("start")) &&= { e |-> (emptyset, emptyset) | e in "Ref" without "CR" } union {f |-> ({f}, emptyset) | f in "CR"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \

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

  &"Sources"(p, e) &&= cases(
    "Sources"(p', x) & "if" sigma = {(x, p')},
    sigma & "otherwise"
  )\
  &&&"where" sigma = "SafeReach"(p, e)
$

TODO: Prove (or rationale): Given $sigma = "Sources"(p, e)$, if $abs(sigma) >=2$ then all $c in sigma$ is alive exclusively from each other

- Lemma: Occluded values must be alive before the current value
- Occlusion only matters if SafeReach has more than one value

] /* End of Safely Reachable Value */





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


Analysis result, warning = ${f | f in "CR" and evalexit(mono("exit"))(f) leqsq.not "UT" }$
