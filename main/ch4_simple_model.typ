#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= A Simple Utilization Analysis

We start with a simplified version of the problem. In this version, the utilizable values can only be constructed by the function `create()` and utilized by the function `utilize(u)`. Other functions do not affect the values' utilization status, and we purposefully ignore any utilization through higher-order functions and collection types.

The goal of the utilization analysis is to find which utilizable values are guaranteed to be utilized and which are not. A value is guaranteed to be utilized if all program execution paths starting from its `create` call always reach a `utilize` call. Any `create` calls may have a path not reaching a `utilize` call should be reported as an error. Using this simplified model, we want to focus first on ensuring the soundness of the analysis in regards to reference alias problem.

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

@lst:SimpleModelExample shows an example of utilization tracking in this simplified model, especially in regards to the reference alias problem. Each `create` is call marked with "OK" or "Error" as the expected result of the analysis. Observe that:
+ The value constructed by the `create` call $C_1$ can always reach a `utilize` call via variable `a` or variable `a1`.
+ Both values from calls $C_2$ and $C_3$ are utilized through the variable `b`.
+ The call $C_4$ is the first error example. In this case, the value is not utilized if the conditional expression `cond3` is true and `cond4` is false.
+ In contrast to $C_4$, the value $C_5$ is always utilized through variable `d1`, since if `cond3` is false the call $C_5$ never happened and no value is created.
+ The same case also applies to the call $C_6$ and $C_7$.

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
  U &= "LinearLat"(bot, "UT", top) \
  S &= "MapLat"("Ref" -> U) \
$

The lattice $S$ is a map from references Ref to a utilization status $U$. Given a state $s$ and a reference $x$, $s(x) = u$ is interpreted as "the utilization status of $x$ is eventually equal to $u$". There are three possible values of utilization status forming a linear lattice: $top$ which means a "maybe not utilized", UT which means "definitely utilized", and $bot$ which means "not created" or "not available".

We then define the transfer functions $evalbracket("_") : "Node" -> S$, with $evalexit(p)$ the program state right after execution of node $p$, and $evalentry(p)$ the program state right before node $p$. For ease of reading, we also use the notation $spx = evalexit(p)$. We define the post-execution transfer functions as follows.
$
  &evalexit(mono("exit")) &&= { x |-> top | x in "Ref" without "Cons" } union { f |-> bot | f in "Cons" } \
  &evalexit(p) &&= join.big_(q in "succ"(p)) evalentry(q)
$<eq:BackwardPostFunc>

Since the analysis is going backward, we define the initial state on the function exit node. All non-construction references are marked with $top$, while construction expressions are marked with $bot$. We mark constructions with $bot$ to accommodate paths where the construction calls never happened, i.e. if the call happened inside a conditional branch. Other nodes' post-execution transfer functions are simply the joined state of its successor nodes.

We define the pre-execution transfer functions in @eq:BackwardPreFunc. There are four important cases here. The first two cases are function call expressions `$e = $f(...)`. If it is a `create` call with label $f in "Cons"$, then the utilization of construction call site $f$ is equal to the result's utilization. If it is a `utilize` call, then the argument expression $a$ is marked as utilized.
$
  &evalentry(mono("p:" lbl(e) = lbl(f)())) &&= spx[f |-> spx(e) | lbl(f) = mono("create")]\
  &evalentry(mono("p:" lbl(e) = lbl(f)(lbl(a)))) &&= spx[a |-> "UT" | lbl(f) = mono("utilize")]\
  &evalentry(mono("p:" lbl(e) "= x")) &&= spx[x |-> s(x) meet s(e)]\
  &evalentry(mono("p: (var) x :=" lbl(e))) &&= spx[e |-> spx(e) meet spx(x)][x |-> top]\
  &evalentry(p) &&= evalexit(p)\
$ <eq:BackwardPreFunc>

The next case is the variable access expression `$e = x`, where the utilization of expression label $e$ is propagated to variable $x$. We use meet operation to make sure that if $x$ is already utilized in the current path, it should remain so. The last cases are the variable declaration and assignment `(var) x := $e`. It is quite similar with the variable access expression, but with resetting the utilization of $x$ to $top$. This is because any values assigned prior to this node is "hidden" by the current assignment and cannot be traced to any future `utilize`, therefore the utilization status is unknown.

The analysis runs for a single pass of transfer functions evaluation. This means a loop will be analyzed like an if statement, that is either the loop never runs or runs exactly once. This is because for utilization analysis, we only need to determine whether a value is utilized at least once. Based on the program state at function start, the analysis produces the set of warnings as follows.

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

The backward analysis works quite well in the simplified problem and has the advantage of not requiring variable value tracking.
However, we find it hard to generalize the backward analysis to meet our goals. This is especially true for utilization status pre-requisites, which is required to handle types like collection and file handler type. The backward analysis provides _future_ guarantees for past executions, while the utilization pre-requisites needs _past_ guarantees. To provide past guarantees, we need a forward-moving analysis instead of a backward one. In this section, we shall define the forward analysis of the simplified problem that will become the base for the generalized analysis.

The forward utilization analysis is divided in two parts, which are safely-reachable value analysis and the utilization analysis itself. We divide the analysis into two parts for the ease and clarity of the definitions, but in practice it is possible and more efficient to combine both of them into a single analysis, since both of them are forward-moving analyses. The main idea of this analysis is to first identify which values constructed by `create` calls are safely-reachable from a variable or an expression, then to mark those values as utilized when it is passed as an argument to a `utilize` call. Any values that may not always be marked as utilized at the end of the function should be reported as an error.

=== Safely-reachable values

The reachable values of a variable or an expression are any values that might be referenced by the variable or an expression. This is quite similar to the reaching definition concept in many classical data-flow analyses. If we mark those reachable values as utilized, for example when there is a utilization call `utilize(x)` to a variable $x$, we cannot be sure if it is correct. This is because during runtime, $x$ can only refer to one of the reachable values, and if the other non-referred reachable values also exist, those values are not actually utilized by `utilize(x)`. However, if we can guarantee that only one of them can exists at the same time (and thus it is the value referenced by $x$), we can safely mark them as utilized. We called this the _safely-reachable_ values.

The set of safely-reachable values is a subset of a variable's or an expression's reachable values, in which at most one of the values exist at the same time. In other words, each value in safely-reachable set is _exist exclusively_ from each other, that is either it is the referred value at runtime or it is never created in the first place. Consider the following code example.

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

\
From the examples in @lst:SafelyReachableEx, we can observe that:
+ Right after the execution of line 1, the safely-reachable values of variable $a$ is ${C_1, C_2}$, since both $C_1$ and $C_2$ only exist exclusively from each other
+ Right after line 4, the safely-reachable values of $a$ is ${C_3}$, since it is the last assigned value.
+ After the end of the branch statement at line 7, only $C_3$ and $C_4$ are safely-reachable from $a$.
+ While it is still possible that $a$ might refers to $C_1$ or $C_2$, which happens when the conditions at line 3 and 5 fail, it is not safely-reachable since one of ${C_1, C_2}$ is still created even when $a$ no longer refers to it.
+ In contrast, it is safe to assume that $a$ may refer to ${C_3, C_4}$, since both are exist exclusively from each other and both are not created if $a$ refers to either $C_1$ or $C_2$.
+ At line 11 of the code example, variable $a$ can safely reach ${C_5, C_6}$ since both are also safely-reachable from $b$.
+ At line 14, however, while $a$ may refer to any of the values $C_1$ to $C_7$, only $C_7$ is safely-reachable. This is because $C_7$ is never created if $a$ refers to any values other than $C_7$, while the reverse is not necessarily true.
+ At line 17, the safely-reachable values set for $a$ is an empty set, since the values referred by variables $b$ and $c$ do not exist exclusively with each other.

Based on these observations, we find a pattern: a variable to variable assignment is only safely reachable if it is the only reachable assignment. In contrast, there can be more than one direct value references that are safely-reachable. From a graph-centric perspective, we can also express that given two creation calls $c_a$ and $c_b$, the values returned by $c_a$ and $c_b$ are exist exclusively of each other if there is no program path in which both $c_a$ and $c_b$ are called. In other words, the CFG node of $c_a$ call is not an ancestor to the node of $c_b$ call and vice versa.


#[ /* Start of Safely Reachable Value */
#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$
#let opx = $o_p^circle.small.filled$
#let rpx = $r_p^circle.small.filled$

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

We then define the transfer functions $evalbracket("_") &&: "Node" -> S_"RV"$. For convenience, we also use the notations $sp, rpe(x),$ and $ope(x)$, defined as $sp = evalentry(p)$ and $(rpe(x), ope(x)) = sp(x)$. First we set the pre-execution state at the function's starting node. For the reachable values, any non-construction expressions and variables are mapped to empty set, while construction calls are mapped to the singleton set of itself. No constructions are occluded at the beginning.
$
  &evalentry(mono("start")) &&= { e |-> (emptyset, emptyset) | e in "Ref" without "Cons" } union {f |-> ({f}, emptyset) | f in "Cons"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
$

As for the post-execution transfer functions, there are four main cases, which are construction calls, variable access expressions, variable declarations, and assignments.

$
  &evalexit(mono("p:" lbl(e) = lbl(f)())) &&= sp[e |-> ({f}, emptyset) | f in "Cons"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> ({ (x, p) }, emptyset) ]\

  &evalexit(mono("p: var" x := lbl(e))) &&= sp[x |-> (rpe(e), emptyset) ]\
  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> (rpe(e), ope(x) union (rpe (x) sect "Cons" )) ]\
  &evalexit(p) &&= evalentry(p)\
$ <eq:RVTransferFunc>

In the construction call case, the call expression is simply mapped to the singleton set of the construction function. In the variable access expression case, instead of mapping $e$ to the reachable values of $x$, which is $rpe(x)$, we instead map it to the current variable reference, denoted by the variable-node pair $(x, p)$. This is quite important since we want to distinguish when assignment from variable to variable happened. In the case of variable declaration, the variable $x$ is mapped to the reachable set of the initial expression $e$. The variable assignment case is quite similar to the declaration, but in this case we want to grow the occlusion set with the previous values of $x$. When we grow the occlusion set, only construction sites are included.

When the analysis reaches a fix-point, we can define the safely reachable references function  $"SafeReach": ("Node", "Ref") -> powerset("VarAt" union "Cons")$ and construction sites resolving function $"Sources" : ("Node","Ref") -> powerset("Cons")$, defined as follows.
#[
#show math.equation.where(block: true): set block(spacing: 1em)
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
]

The SafeReach function returns the reachable value set if it only contains a single value. Otherwise, it returns non-occluded construction sites. The Sources function merely resolve a singleton set of variable reference $(x, p')$ into its safely-reachable set. The soundness of our overall analysis depends on the correctness of safely-reachable property. This is because later in the utilization analysis, the analysis determines which value should be marked as utilized based on the Sources function, which depends on SafeReach function. The set #box($sigma = "SafeReach"(p, e)$) is safely reachable if either there is only at most one reference ($abs(sigma) < 2$) or all references in $sigma$ are construction calls that exist exclusively.

We provide the full proof of this property in @apx:SafeReachProof. In short, we prove that if there are two construction calls that do not exist exclusively, such that one call's node is an ancestor to the other, the ancestor call must be included in the occluded set. Since the result of SafeReach always excludes the occluded set if there are more than one reachable definitions, its member cannot be an ancestor to each other, and thus exist exclusively to each other.

@eq:SafelyReachableAnalysisEx shows an example of the result of the analysis, with `Src(a)` the resolved safely-reachable values of `a` at that point. Notice that at line 9, the references ${C_1, C_3, (b, L_7)}$ are reachable, but since $C_1$ is occluded and reference to $b$ is not the only reference, only $C_3$ is safely-reachable.

#listing("Example of safely-reachable values analysis")[
```kotlin
var a = create() /*C1*/   // a -> ({C1}, {}), Src(a) = {C1}
val b = create() /*C2*/   // b -> ({C2}, {}}

if(...) {
  a = create() /*C3*/     // a -> ({C3}, {C1}), Src(a) = {C3}
} else if (...) {
  a = b                   // a -> ((b,L7), {C1}), Src(a) = Src(b) = {C2}
}
// a -> {{C1, C3, (b,L7)}, {C1}}, Src(a) = {C3}
```] <eq:SafelyReachableAnalysisEx>

] /* End of Safely Reachable Value */

#[
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")
// #show math.equation.where(block: true): set block(spacing: 1em)

=== Utilization analysis with safely-reachable values

A lot of work for utilization analysis is already done by the safely-reachable analysis. The utilization analysis becomes simpler: resolve the arguments into the set of safely-reachable construction call sites using the Source function, then mark those values as utilized.

We use a quite different lattice than the one in the backward analysis, as shown in @eq:ForwardLattice. Instead of an linearly-ordered lattice of $(bot, "UT", top)$, the utilization lattice $U$ is a flat lattice with the partial ordering #box($bot #h(5pt) leqsq NU, UT leqsq top$). The lattice $U$ has four values: $top$ which means "maybe utilized or not" or "unknown", $UT$ which means "definitely utilized" (equivalent to UT), $NU$ which means "definitely not utilized" and $bot$ which means "not created" or "not accessible". Currently, the utilization status $NU$ is not really useful, but this will become useful when we include utilization pre-requisites later. The program state lattice $S$ is a mapping from the construction calls instead of references since any variables and other expressions are resolved with the Sources function.

$
  U = "FlatLat"({NU, UT}) \
  S = "MapLat"("Cons" -> U)
$ <eq:ForwardLattice>

The transfer functions $evalbracket("_") :: "Node" -> S$ are defined by @eq:ForwardUtil, given $sp = evalentry(p)$.

$
  &evalentry(mono("start")) &&= { f |-> bot | f in "Cons" }\
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \

  &evalexit(mono("p:" lbl(e) = lbl(f)"()")) &&= sp[f |-> NU | lbl(f) = mono("create")]\

  &evalexit(mono("p:" lbl(e) = lbl(f)(lbl(a)))) &&= sp[c |-> UT | lbl(f) = mono("utilize") and c in "Sources"(p, a)]\

  &evalexit(p) &&= evalentry(p)\
$ <eq:ForwardUtil>

There are two main cases of note here. The first is the `create` call case, in which the construction label $f$ is marked as not utilization. The other case is the `utilize` call, in which we resolve the arguments into safely-reachable construction call labels and mark them as utilized.

After a single pass of transfer functions evaluations, the analysis can report the warning based on the utilization status at exit nodes.

$
"Warnings" = {f | f in "Cons" and evalexit(mono("exit"))(f) leqsq.not UT }
$

An example of the analysis result can be seen in @lst:ForwardUtilExample. We also show in the example the values of $"Sources"(p, x)$ when $x$ is updated. Similar to the backward analysis, the forward analysis also reports error on call $C_1$ and not $C_2$. Notice that we only update the program state during function calls.
// However, the utilization state updates only happened on function calls, since the variable related cases are only relevant during safely-reachable values analysis.

#listing("Example of forward analysis states")[
```kotlin
fun test() {                   // s1 = {C1: ⊥, C2: ⊥}
  val a = create() /*C1: Err*/ // s2 = s1[C1: 0]; Src(a)={C1}
  val b =
    if (/*cond3*/) {
      create() /*C2: OK*/      // s3 = s2[C2: 0]; Src(b)={C2}
    } else {
      a                        // s4 = s2; Src(b)={C1}
    }                          // s5 = s3⊔s4 = {C1: 0, C2: 0}; Src(b)={C2}
  if (/*cond4*/) {
    utilize(a)                 // s6 = s5[C1: 1]
  }                            // s7 = s6 ⊔ s5 = {C1: ⊤, C2: 0}
  utilize(b)                   // s8 = s7[C2: 1]
}                              // s9 = s8 = {C1: ⊤, C2: 1}
```] <lst:ForwardUtilExample>
]

== Chapter summary

We define a simplified version of the utilization analysis problem by limiting it to only `create` and `utilize` calls. The main goal of formalizing utilization analysis in this simplified version is solving the reference alias problem. We first start with the backward-moving analysis, in which the analysis can simply flow back the utilization status starting from any `utilize` call to a `create` calls. However, this technique is incompatible with our other goal: handling functions that may require certain utilization status.

We then devise the forward-moving analysis that is more compatible with our other goals. The analysis is split into two parts, the safely-reachable value analysis and the utilization analysis. We prove that our safely-reachable value analysis infers sound approximations of safely-reachable values, which are contain values that exist exclusively from each other. The utilization analysis then become simpler. Using the result of the previous analysis, it resolves variables' and expressions' safely-reachable values and mark them as utilized whenever `utilize` calls occur.

This simplified problem, however, is only a small part of the utilization tracking problem. We need to generalize the problem to include any function calls. We shall use the forward-moving analysis as the basis of the general analysis as it is more compatible with the other goals.
