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

We then define the constraint functions $evalbracket("_") : "Node" -> S$, with $evalexit(p)$ the program state right after execution of node $p$, and $evalentry(p)$ the program state right before node $p$. For ease of reading, we also use the notation $spx = evalexit(p)$. We defined the post-execution constraints as follows.
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
  &evalentry(p) &&= evalexit(p)\
$ <eq:BackwardPreFunc>

The next case is the variable access expression `$e = x`, where the utilization of expression label $e$ is propagated to variable $x$. We use meet operation to make sure that if $x$ is already utilized in the current path, it should remain so. The last cases are the variable declaration and assignment `(var) x := $e`. It is quite similar with the variable access expression, but with resetting the utilization of $x$ to $top$. This is because any values assigned prior to this node is "hidden" by the current assignment and cannot be traced to any future `utilize`, therefore the utilization status is unknown.

The analysis runs for a single pass of constraint evaluations. This means a loop will be analyzed like an if statement, that is either the loop never runs or runs exactly once. For the utilization analysis purpose, this is already close enough to a fixpoint since utilization cases for singular values (i.e. not a list or a collection) inside loops are quite rare and can be regarded as an error. We will discuss handling collections of utilizable values later. Based on the program state at function start, the analysis produces the set of warnings as follows.

$
  "Warnings" = {f | f in "Cons" and evalentry(mono("start"))(f) leqsq.not "UT" }
$

@lst:BackwardExample shows the example of the resulting states of the backward analysis. In this example, the analysis determines that, based on the abstract program state at the start of the function ($s_10$), the creation call $C_2$ is always utilized (UT) while $C_1$ is sometimes not utilized ($top$). Therefore, it should only gives warning on $C_1$. $C_1$ utilization is $top$ because of variable $a$, which also has $top$ utilization status. Notice that in some states, like $s_3$ and $s_5$, the variable $a$ is marked as utilized. However, it is only marked as utilized on some of the conditional branches but not all of them. As a result, when the branches' states merged as $s_4$ and $s_6$, the utilization of $a$ remains as $top$.

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
```] <lst:BackwardExample>


]


== Forward analysis

The backward analysis works quite well in the simplified problem and has the advantage of not requiring variable value tracking. However, we found that later in the generalized version of the problem, there are some aspects of the analysis that are easier to handle if we have information on past utilizations of values. The backward analysis, by its nature, only provide information about future utilizations. We found that while making future utilization guarantee is less straightforward in the forward analysis, it is still easier to reason with than making past utilization guarantee in the backward analysis.

The forward utilization analysis is divided in two parts, which are safely-reachable value analysis and the utilization analysis itself. We divide the analysis into two parts for the ease and clarity of the definitions, but in practice it is possible and more efficient to combine both of them into a single analysis, since both of them are forward-moving analyses. The main idea of this analysis is to first identify which values constructed by `create` calls are safely-reachable from a variable or an expression, then to mark those values as utilized when it is passed as an argument to a `utilize` call. Any values that may not always be marked as utilized at the end of the function should be reported as an error.

=== Safely-reachable values

A set of safely-reachable values is a subset of reachable values from a variable or an expression, in which at most one of the values is alive at the same time. In other words, for each values in the safely-reachable set, either it is the actual referred value during the runtime or it is never created in the first place. Consider the example shown in @lst:SafelyReachableEx. Right after the execution of line 1, the safely-reachable values of variable $a$ is ${C_1, C_2}$, since both $C_1$ and $C_2$ only exist exclusively from each other. Right after line 4, the safely-reachable values of $a$ is ${C_3}$, since it is the last assigned value. Notice that right after the end of the branch statement at line 7, only the values ${C_3, C_4}$ are safely-reachable from $a$. While it is still possible that $a$ might refers to $C_1$ or $C_2$, which happens when conditions at line 3 and 5 fail, it is not safe to assume so. However, it is safe to assume that $a$ may refer to ${C_3, C_4}$, since both exist exclusively with each other and both are not created if $a$ refers to either $C_1$ or $C_2$.

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

The safely-reachable values set become less straightforward when the assignment happen through a variable. At line 11 of the code example, variable $a$ can safely reach ${C_5, C_6}$ since both are also safely-reachable from $b$. However, at line 14, while during runtime $a$ may refer to any of the values in the set ${C_1, ..., C_7}$, we can only statically guarantee that $C_7$ is safely reachable from $a$. This is because we can be sure $C_7$ is never created in the first place if $a$ refers to any values other than $C_7$, while the reverse is not necessarily true. Observe that right after line 17, the safely-reachable values set for $a$ is an empty set, since the values referred by variables $b$ and $c$ do not live exclusively with each other. A pattern then emerge: a variable to variable assignment is only safely reachable if it is the only reachable assignment.


#[ /* Start of Safely Reachable Value */
#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

To define the safely-reachable analysis, we first define three sets Ref, Cons, and VarAt as shown in @eq:ForwardSafeReachSets. The sets Ref and Cons have the same definitions as in the backward analysis. The VarAt set is a set of pairs of a local variable and a node. The pair ($x$, $p$) can be interpreted as "the values referred by local variable $x$ when the program execution reaches node $p$".

$
  &"Ref" &&= "LocalVars" union "ExprLabel"\
  &"Cons" &&= { f | f in "ExprLabel" and lbl(f) = mono("create") }\
  &"VarAt" &&= {(x, p) | x in "LocalVars", p in "Node"}\
$ <eq:ForwardSafeReachSets>

Next we defined the lattices used in the safely-reachable analysis. The first lattice is the reachable values lattice $R$, which is a powerset lattice of the sets VarAt and Cons. This lattice is quite similar to the lattice used in the classic reachable definition analysis. The second lattice is the occluded constructions lattice $O$, which is a powerset lattice of the set Cons. This lattice indicates which construction call sites are "hidden" or "older" than the last assigned values. The last one is the abstract state lattice $S_"RV"$, which is a map lattice from the references to the pair of reachable values $R$ and occluded constructions $O$.

$
  &R &&= (powerset("VarAt" union "Cons"), subset.eq)\
  &O &&= (powerset("Cons"), subset.eq)\
  &S_"RV" &&= "MapLat"("Ref" -> (R, O))
$

We then define the constraint functions $evalbracket("_") &&: "Node" -> S_"RV"$. For convenience, we also use the notations $sp, rpe(x),$ and $ope(x)$, defined as  $sp = evalentry(p)$ and $(rpe(x), ope(x)) = sp(x)$. First we set the pre-execution constraints at function start. For the reachable values, any non-construction expressions and variables are mapped to empty set, while construction calls are mapped to the singleton set of itself. No constructions are occluded at the beginning.
$
  &evalentry(mono("start")) &&= { e |-> (emptyset, emptyset) | e in "Ref" without "Cons" } union {f |-> ({f}, emptyset) | f in "Cons"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
$

As for the post-execution constraints, there are four main cases, which are construction calls, variable access expressions, variable declarations, and assignments.

$
  &evalexit(mono("p:" lbl(e) = lbl(f)())) &&= sp[e |-> ({f}, emptyset) | lbl(f) = mono("create")]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> ({ (x, p) }, emptyset) ]\

  &evalexit(mono("p: var" x := lbl(e))) &&= sp[x |-> (rpe(e), emptyset) ]\
  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> (rpe(e), ope(x) union (rpe (x) sect "Cons" )) ]\
  &evalexit(p) &&= evalentry(p)\
$ <eq:RVTransferFunc>

The construction call case is trivial; the call expression is simply mapped to the singleton set of the construction function. In the variable access expresssion case, instead of mapping $e$ to the reachable values of $x$, which is $rpe(x)$, we instead map it to $(x, p)$. This is quite important since we want to distinguish when assignment from variable to variable happened. The variable declaration case is also trivial; we simply mapped $x$ to the reachable set of the initial expression $e$. The variable assignment case is quite similar to the declaration, but in this case we want to grow the occlusion set with the previous values of $x$. When we grow the occlusion set, only construction sites are included.

When the analysis reaches a fixpoint, we can define the safely reachable references function  $"SafeReach": ("Node", "Ref") -> powerset("VarAt" union "Cons")$ and construction sites resolving function $"Sources" : ("Node","Ref") -> powerset("Cons")$, defined as follows.

$
  &"SafeReach"(p, e) &&= cases(
    r_e & "if" abs(r_e) <= 1,
    (r_e sect "Cons") without o_e& "otherwise"
  )\
  &&&"where" (r_e, o_e) = evalexit(p)(e)\

  &"Sources"(p, e) &&= cases(
    "Sources"(p', x) & "if" sigma = {(x, p')},
    sigma & "otherwise"
  )\
  &&&"where" sigma = "SafeReach"(p, e)
$ <eq:ForwardSafeReachFunc>

The SafeReach function returns the reachable value set if it only contains a single value. Otherwise, it returns non-occluded construction sites. The Sources function simply resolve a singleton set of $(x, p)$ pair into its safely-reachable set.

TODO: Prove: Given $sigma = "Sources"(p, e)$, if $abs(sigma) >=2$ then all $c in sigma$ is alive exclusively from each other

- Lemma: if $abs(sigma) >= 2$, then all of the elements are call sites
- Lemma: Occluded values must be alive before the current value
- Occlusion only matters if SafeReach has more than one value

] /* End of Safely Reachable Value */

#[
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")

=== Utilization analysis with safely-reachable values

A lot of work for utilization analysis is already done by the safely-reachable analysis. The utilization analysis becomes quite simple: resolve the arguments into the set of safely-reachable construction call sites using the Source function, then mark those values as utilized. We use the same lattices as in the backward analysis.

$
  U = "OrderLat"(angles(bot, "UT", top)) \
  S = "MapLat"("Ref" -> U) \
$


The constraint functions $evalbracket("_") :: "Node" -> S$ are defined by @eq:ForwardUtil, given $sp = evalentry(p)$.

$
  &evalentry(mono("start")) &&= { x |-> top | x in "Ref" without "Cons" } union { f |-> bot | f in "Cons" }\
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \

  &evalexit(mono("p:" lbl(e) = lbl(f)"()")) &&= sp[f |-> top, e |-> top | lbl(f) = mono("create")]\

  &evalexit(mono("p:" lbl(e) = lbl(f)(lbl(a)))) &&= sp[c |-> "UT" | lbl(f) = mono("utilize") and c in "Sources"(p, a)]\

  &evalexit(p) &&= evalentry(p)\
$ <eq:ForwardUtil>

There are two main cases of note here. The first is the `create` call case, in which the construction label $f$ is marked with the $top$ utilization. The other case is the `utilize` call, in which we first resolve the arguments into safely-reachable construction call labels, and mapped those labels as utilized. After a single pass of constraints evaluations, the analysis can report the warning based on the utilization status at exit nodes.

$
"Warnings" = {f | f in "Cons" and evalexit(mono("exit"))(f) leqsq.not "UT" }
$

An example of the analysis result can be seen in @lst:ForwardUtilExample. We also show in the example the values of $"Sources"(p, x)$ when $x$ is updated. Similar to the backward analysis, the forward analysis also reports error on call $C_1$ and not $C_2$. However, the utilization state updates only happened on function calls, since the variable related cases are only relevant during safely-reachable values analysis.

#listing("Example of forward analysis states")[
```kotlin
fun test() {                   // s1 = {C1: ⊥, C2: ⊥, * : ⊤}
  val a = create() /*C1: Err*/ // s2 = s1[C1: ⊤, a: ⊤]; SRC(L2,a)={C1}
  val b =
    if (/*cond3*/) {
      create() /*C2: OK*/      // s3 = s2[C2: ⊤]; SRC(L5,b)={C2}
    } else {
      a                        // s4 = s2; SRC(L7,b)={(a,L7)}
    } // val b := $if          // s5 = s3⊔s4 = {C2: ⊤, ...}; SRC(L8,b)={C2}
  if (/*cond4*/) {
    utilize(a)                 // s6 = s5[C1: UT]
  }                            // s7 = s6 ⊔ s5 = {C1: ⊤, ...}
  utilize(b)                   // s8 = s7[C2: UT]
}                              // s9 = s8 = {C1: ⊤, C2: UT, ...}
```] <lst:ForwardUtilExample>


]
