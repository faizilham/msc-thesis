#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= A Simple Utilization Analysis

We start with a simplified version of the problem. In this version of the problem, the utilizable values can only be constructed by the function `create()` and utilized by the function `utilize(u)`. Other functions do not affect the values' utilization status. The goal of the utilization analysis is to find which utilizable values are guaranteed to be utilized and which are not. A value is guaranteed to be utilized if all program execution paths starting from its `create` call always reach a `utilize` call. Any `create` calls may have a path not reaching a `utilize` call should be reported as an error.

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

@lst:SimpleModelExample shows an example of utilization tracking in this simplified model, with each `create` call marked with "OK" or "Error" as the expected result of the analysis. In the example, the value constructed by the `create` call $C_1$ can always reach a `utilize` call via variable `a` or variable `a1`. Both values from calls $C_2$ and $C_3$ are utilized through the variable `b`. The call $C_4$ is the first error example. In this case, the value is not utilized if the conditional expression `cond3` is true and `cond4` is false. On the other hand, the value from call $C_5$ is always utilized through variable `d1`, since if `cond3` is false the call $C_5$ never happened and no value is created. The same case also applies to the call $C_6$ and $C_7$.

There are two ways to approach the problem. The first one is to trace paths backward from a `utilize` call to the `create` calls. The second one is to trace paths forward from a `create` calls to `utilize` calls.

== Backward analysis

The first approach to utilization tracking is through a backward analysis. The main idea of this approach is to propagate back the utilization status starting from each `utilize` call. For example, suppose there is a path reaching a call `utilize(x)`. This means, any values referenced by variable `x` is guaranteed to be utilized in current path. We can mark the variable `x` as utilized, and go back to the previous nodes in the path. When the analysis reaches a past assignment `x := create()`, we can mark the `create` call as utilized. Similarly, if the path never reaches a call `utilize(x)`, the utilization status of `x` is never changed, and all past assignments will also be marked as not utilized. One main advantage of tracing backward is that we do not need to track the possible values or alias of the variables, since the future utilization status is automatically propagated in assignment nodes.

#[
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")

To analyze a function, we assume we have the sets LocalVars, the set of all local variables in the function, and ExprLabel, the set of all expression labels in the function. We define two sets: \Ref and Cons. Ref is the set of references to utilizable values, which are variables and expression labels. Cons is the set of construction call sites, which are expression labels of `create` calls. Notice that since Cons $subset.eq$ ExprLabel, then Cons $subset.eq$ Ref also applies.

$
  &"Ref"  &&= "LocalVars" union "ExprLabel"\
  &"Cons" &&= { f | f in "ExprLabel" and lbl(f) = mono("create") }\
$

We then defined the lattices used in the data flow analysis. We defined the utilization status lattice $U$ and the abstract program state lattice $S$.
$
  U &= "OrderLat"(angles(bot, "UT", top)) \
  S &= "MapLat"("Ref" -> U) \
$

The lattice $S$ is a map from references Ref to a utilization status $U$. Given a state $s$ and a reference $x$, $s(x) = u$ is interpreted as "the utilization status of $x$ is guaranteed to be $u$". The utilization status $u$ is interpreted as follows: $bot$ means "not available", UT means "definitely utilized", and $top$ means "unknown".

We then define the constraint functions $evalbracket("_") :: "Node" -> S$, with $evalexit(p)$ the program state right after execution of node $p$, and $evalentry(p)$ the program state right before node $p$. For ease of reading, we also use the notation $spx = evalexit(p)$. We defined the post-execution constraints as follows.
$
  &evalexit(mono("exit")) &&= { x |-> top | x in "Ref" without "Cons" } union { f |-> bot | f in "Cons" } \
  &evalexit(p) &&= join.big_(q in "succ"(p)) evalentry(q)
$<eq:BackwardPostFunc>

Since the analysis is going backward, we define the initial constraint on the function exit node. All non-construction references are marked with $top$, while construction expressions are marked with $bot$. We mark constructions with $bot$ to accommodate paths where the construction calls never happened, i.e. if the call happened inside a conditional branch. Other nodes' post-execution constraints are simply the joined state of its successor nodes.

We define the pre-execution constraints in @eq:BackwardPreFunc. There are four important cases here. The first two cases are function call expressions `$e = $f(...)`. If it is a `create` call with label $f in "Cons"$, then the utilization of construction call site $f$ is equal to the result's utilization. If it is a `utilize` call, then the argument expression $a$ is marked as utilized.
$
  &evalentry(mono("p:" lbl(e) = lbl(f)())) &&= spx[f |-> spx(e) | lbl(f) = mono("create")]\
  &evalentry(mono("p:" lbl(e) = lbl(f)(lbl(a)))) &&= spx[a |-> "UT" | lbl(f) = mono("utilize")]\
  &evalentry(mono("p:" lbl(e) "= x")) &&= spx[x |-> s(x) meet s(e)]\
  &evalentry(mono("p: (var) x :=" lbl(e))) &&= spx[e |-> spx(e) meet spx(x)][x |-> top]\
  &evalentry(p) &&= evalexit(p)\ \
$ <eq:BackwardPreFunc>

The next case is the variable access expression `$e = x`, where the utilization of expression label $e$ is propagated to variable $x$. We use meet operation to make sure that if $x$ is already utilized in the current path, it should remain so. The last cases are the variable declaration and assignment `(var) x := $e`. It is quite similar with the variable access expression, but with resetting the utilization of $x$ to $top$. This is because any values assigned prior to this node is "hidden" by the current assignment and cannot be traced to any future `utilize`, therefore the utilization status is unknown.
After the constraints reaches a fixpoint, the analysis can return back as a warning the set of call sites that are not guaranteed to be utilized at starting point.

$
  "Warnings" = {f | f in "Cons" and evalentry(mono("start"))(f) leqsq.not "UT" }
$

@eq:BackwardExample shows the example of the resulting states of the backward analysis. In this example, the analysis determines that, based on the abstract program state at the start of the function ($s_10$), the creation call $C_2$ is always utilized (UT) while $C_1$ is sometimes not utilized ($top$). Therefore, it should only gives warning on $C_1$. $C_1$ utilization is $top$ because of variable $a$, which also has $top$ utilization status. Notice that in some states, like $s_3$ and $s_5$, the variable $a$ is marked as utilized. However, it is only marked as utilized on some of the conditional branches but not all of them. As a result, when the branches' states merged as $s_4$ and $s_6$, the utilization of $a$ remains as $top$.

#listing("Example of backward analysis states")[
```kotlin
fun test() {                    //s10 = {C1: ⊤, C2: UT, ...}
  val a = create() /*C1: Err*/  // s9 = s8[C1: s8[a] = ⊤]
  val b =
    if (/*cond3*/) {            // s8 = s6 ⊔ s7 = {a: ⊤, C2: UT, ...}
      create() /*C2: OK*/       // s7 = s5[C2: s4(if) = UT]
    } else {
      a                         // s6 = s5[a: s4(if) = UT]
    } // val b := $if           // s5 = s4[if: s4(b) = UT, b: ⊤]
  if (/*cond4*/) {              // s4 = s3 ⊔ s2 = {b: UT, a: ⊤, ...}
    utilize(a)                  // s3 = s2[a: UT]
  }
  utilize(b)                    // s2 = s1[b: UT]
}                               // s1 = {C1: ⊥, C2: ⊥, * : ⊤}
```] <eq:BackwardExample>


]


== Forward analysis

The backward analysis works quite well in the simplified problem and has the advantage of not requiring variable value tracking. However, we found that later in the generalized version of the problem, there are some aspects of the analysis that are easier to handle if we have information on past utilizations of values. The backward analysis, by its nature, only provide information about future utilizations. We found that while making future utilization guarantee is less straightforward in the forward analysis, it is still easier to reason with than making past utilization guarantee in the backward analysis.

The forward utilization analysis is divided in two parts, which are safely-reachable value analysis and the utilization analysis itself. We divide the analysis into two parts for the ease of definitions, but in practice it is possible and more efficient to combine both of them into a single analysis, since both of them are forward-moving analyses. The main idea of this analysis is to first identify which values constructed by `create` calls are safely-reachable from a variable or an expression, then to mark those values as utilized when it is passed as an argument to a `utilize` call. Any values that may not always be marked as utilized at the end of the function should be reported as an error.

=== Safely-reachable values

A set of safely-reachable values is a subset of reachable values from a variable or an expression, in which at most one of the values is alive at the same time. In other words, for each values in the safely-reachable set, either it is the actual referred value during the runtime or it is never created in the first place. Consider the example shown in @lst:SafelyReachableEx. Right after the execution of line 1, the safely-reachable values of variable $a$ is ${C_1, C_2}$, since both $C_1$ and $C_2$ only exist exclusively from each other. Right after line 4, the safely-reachable values of $a$ is ${C_3}$, since it is the last assigned value. Notice that right after the end of the branching statement at line 7, only the values ${C_3, C_4}$ are safely-reachable from $a$. While it is still possible that $a$ might refers to $C_1$ or $C_2$, which happens when conditions at line 3 and 5 fail, it is not safe to assume so. However, it is safe to assume that $a$ may refer to ${C_3, C_4}$, since both exist exclusively with each other and both are not created if $a$ refers to either $C_1$ or $C_2$.

#listing("Example of safely-reachable values")[
```kotlin
var a = if(...) create() /*C1*/ else create() /*C2*/   // a -> {C1, C2}

if(...) {
  a = create() /*C3*/                                  // a -> {C3}
} else if (...) {
  a = create() /*C4*/                                  // a -> {C4}
}                                                      // a -> {C3, C4}

val b = if(...) create() /*C5*/ else create() /*C6*/   // b -> {C5, C6}
if(...) {
  a = b                                                // a -> {C5, C6}
} else if(...) {
  a = create() /*C7*/                                  // a -> {C7}
}                                                      // a -> {C7}

val c = create() /*C8*/
a = if(...) b else c                                   // a -> {}
```] <lst:SafelyReachableEx>

The safely-reachable values set become less straightforward when the assignment happen through a variable. At line 11 of the code example, variable $a$ can safely reach ${C_5, C_6}$ since both are also safely-reachable from $b$. However, at line 14, while during runtime $a$ may refer to any of the values in the set ${C_1, ..., C_7}$, we can only statically guarantee that $C_7$ is safely reachable from $a$. This is because if $a$ refers to any values other than $C_7$, we can be sure $C_7$ is never created in the first place, while the reverse is not necessarily true.

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
