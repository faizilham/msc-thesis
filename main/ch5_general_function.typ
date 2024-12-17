#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Generalized Utilization Analysis

While the simplified model of the problem is useful as a starting point, in practice we require a more sophisticated model. In this chapter we generalize the forward analysis of the simplified model to include all functions other than `create` and `utilize`.

We start by defining what can a function do in relation to utilizable values. A function can utilize any of its utilizable arguments, similiar to the `utilize` function. A function that returns a utilizable types is also regarded as a value-constructing function, just like the `create` function. Accordingly, a utilizable value that escapes a function through the return statement should also be regarded as utilized inside that function. @lst:TopLevelUtilEx shows an example of how some functions may affect utilization. The `utilizeTwo` function utilizes both of its arguments, while the `newUtilizable` function is basically an intermediary for a `create` function and thus its behavior is the same as `create`.

The `passThrough` function behavior is quite unintuitive at the first glance since it only returns an existing value instead of a new one. There are two ways to handle this case. First, we can declare that the function does not use its argument and the return value is an alias to the argument. The second way is to declare that the function uses its argument and then return a new utilizable value. While the first way is the more accurate description of `passThrough` behavior, we choose the second description in this model since it bypasses the aliasing problem, and if we want to add a more accurate alias analysis in the future it can be easily modified by disabling the return-means-utilize behavior for argument values.


#listing("Top level functions utilization examples")[```kt
fun utilizeTwo(a: Utilizable, b: Utilizable) { // Utilize a and b
  utilize(a)
  utilize(b)
}

fun newUtilizable() : Utilizable { // Create a new utilizable
  return create()
}

// Utilize a, and "create" a new utilizable
fun passThrough(a: Utilizable) : Utilizable {
  return a
}
```] <lst:TopLevelUtilEx>

Lambda functions behave in a similar way to top-level functions, but one main difference is that lambda functions may also affect the utilization of its free variables, that is the variables declared on the higher-level scope than the lambda function's body. @lst:LambdaUtilEx shows the example of lambda functions effect on utilization. In the `testLambda` function, the lambda function assigned to variable `lam` uses its first argument and the free variable `b`. Therefore, the values in `a` and `b` are utilized after the `lam(a)` call.

#listing("Lambda functions utilization examples")[```kt
fun testLambda() {
  val a = create() // OK
  val b = create() // OK
  val lam = { it -> utilize(it); utilize(b) } // utilize its arg and FV b
  lam(a)
}

fun invalidateErr() {
  var a = create() // mutable variable
  val f = {
    utilize(a)
    a = create() // Err, even if it should be OK in this case
  }

  f()
  utilize(a)
}
```] <lst:LambdaUtilEx>

A lambda function may also change the values of mutable free variables, as shown in the `invalidateErr` function in the given example. We decide to regard any mutation of free variable by a lambda function as a possible error, and thus the example is reported as an error when it should be alright. This is because tracking the reference changes and values escapes through the free variables complicates the analysis too much, while in practice free-variable mutating lambda functions are rarely used.

To complete our definition, we also allow functions to invalidate previously-utilized values into unutilized values. We define the primitive `unutilize` as a mirror to `utilize`. While invalidating utilization cases are quite rare, it is useful to have a complete definition with only few changes.


== Utilization effects

As we previously discussed, functions may affect the utilization of its arguments and free variables. We define the set of utilization effects $Ef$ in @eq:UtilEffects, where $EfU$ means it utilizes the value, $EfI$ means it invalidates the value's utilization, and $EfN$ means it does not affect the value.

$
  Ef = {EfU, EfI, EfN}
$ <eq:UtilEffects>

We then extend the function type signature after its return type with effect notations for each of its parameter and free variable in cases of lambda functions. @eq:FuncSignWithEffects shows the extended function type signature with $PiEf$ the map of parameter indexes to utilization effects and $PhiEf$ the map of free variables to utilization effects. A function without any effect annotation is equivalent to having no effect to its arguments and free variables.

$
  f : (t_1,..., t_n) -> t_ret andef PiEf union PhiEf\
  "where"
  PiEf = efl(ef_1, ..., ef_n) = {1 |-> ef_1, .., n |-> ef_n},\
  wide quad PhiEf = {v |-> ef_v | v in "FV"(f)}
$ <eq:FuncSignWithEffects>

The functions previously shown in @lst:TopLevelUtilEx and the lambda function `lam` in @lst:LambdaUtilEx can be annotated as follows.

$
  "utilizeTwo" : ("Utilizable", "Utilizable") -> "Unit" andef efl(EfU, EfU)\
  "newUtilizable" : () -> "Utilizable"\
  "passThrough": ("Utilizable") -> "Utilizable" andef efl(EfU)\
  "lam" : ("Utilizable") -> "Unit" andef efl(EfU) union {b |-> EfU}
$

Notice how `newUtilizable` does not have an effect since it only creates a new value, while `utilizeTwo` and `passThrough` only have effects on its parameters. In addition to the parameter effects, the lambda function `lam` also has the free variable effects.

=== Parametric utilization effect

Unlike first-order functions, higher-order functions usually do not affect utilization directly. Instead, its effects depend on the functions it receives as an argument. In order to handle this, functions can also be annotated with the parametric annotation $epsilon$ for a parametric effect, and $phiEf$ for a parametric map of free variable effects. For example the function `apply`, which simply applies its first argument to the function argument at second position, can be annotated as follows.

$
  "apply" : (A, (A) -> B andef efl(epsilon) union phiEf ) -> B andef efl(epsilon) union phiEf\
  "apply"(x, f) = f(x)
$ <eq:ApplySignature>

This example illustrates how the effect of `apply` is parametric to the effects of function `f`. The utilization of parameter `x` depends on the effect of `f` on its first parameter, which is $epsilon$. If function `f` has some effects on free variables annotated as $phiEf$, then `apply` also has the same effects.

// $
//   // ef + ef = ef; ef_1 + ef_2 = ef_2 + ef_1\
//   // ef dot ef = ef; ef_1 dot ef_2 = ef_2 dot ef_1\
//   U plusef N = U", and" ef plusef I = I "for all" ef :: E\
//   U timesef N = N", and" ef timesef I = I "for all" ef :: E\
// $

// Both operators obey idempotence ($ef circle ef = ef$) and commutative ($ef_1 circle ef_2 = ef_2 circle ef_1$) properties.

// Operator $plusef$ indicates serial application of effect (one after another), while $timesef$ indicates choice or possible branching.

== Function alias analysis

Since in the generalized model any function call may create a new utilizable value or has some effects, we first need to determine which function is called and what is its effect signature before we can analyze the values utilizations. We can determine the function by running a function alias analysis, which is a reachable definition analysis modified for function type values.

#[ /* Start of Function Alias Analysis */
#let evalbracket = evalbracket.with(sub:"FA")
#let evalentry = evalentry.with(sub:"FA")
#let evalexit = evalexit.with(sub:"FA")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

We first define the set of references Ref and the set of function declarations Func. Based on these sets, we also define the flat lattice of function declarations $F$ and the abstract state $S$, which is a map lattice of references to function declarations.

$
  &"Ref" &&= "LocalVars" union "ExprLabel"\
  &"Func" &&= {"Set of top-level and lambda function declarations"}\
  &F &&= "FlatLat"("Func")\
  &S &&= "MapLat"("Ref" -> F)\
$

We define the constraint functions $evalbracket("_") : "Node" -> S$ for the data flow analysis in @eq:FuncAliasConstraints, given the previous state notation $sp = evalentry(p)$.
$
  &evalentry(mono("start")) &&= { e |-> bot | e in "Ref"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
  &evalexit(mono("p:" lbl(e) = "f")) &&= sp[e |-> f | f in "Func"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> sp(x) ]\
  &evalexit(mono("p:" lbl(e) = lambda.{...})) &&= sp[e |-> lambda ]\
  &evalexit(mono("p:" lbl(e) = lbl(f)(...))) &&= sp[e |-> top ]\

  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> sp(e)]\
  &evalexit(p) &&= evalentry(p)\
$ <eq:FuncAliasConstraints>

The constraint functions are quite similar to the reachable definitions analysis. The main difference is the function lattice is a flat lattice, meaning if there are more than one reachable definitions then the reference would be mapped to $top$. Other notable difference is for function calls, in which we also defaulted to $top$ since we currently do not handle function-returning functions.

We can then define a function to resolve the function signature from a reference as @eq:ResolveSign. If the reference can be resolved to a single top-level or lambda function declaration, it simply return the signature of the function. Otherwise it returns the function type without utilization effects. The signature of a top-level function definition is given by annotations, while a lambda function one is typically inferred. We will discuss how to infer the effect signature of lambda functions later.

$
  &"ResolveSign"(p, e) &&= cases(
    "signature"(f) & f in "Func",
    tau_f andef emptyset & "otherwise",
  )\
  &&& "where" f = evalexit(p)(e), "type"(lbl(e)) = tau_f\
$ <eq:ResolveSign>

] /* End of Function Alias Analysis */

== Modifying the safely reachable values analysis

#[ /* Start of Reachable Value Analysis Modified */
#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

In the simplified model, we only care about the utilization of values created inside the function, since we assume functions other than `create` and `utilize` do not create new values or have any effects. Since now any functions may have effects on its arguments or free variables, we also need to track the utilization of those values.

In addition to LocalVars and ExprLabel, we now also assume each functions to have the set of parameters Param and the set of free variables FV. We redefine the set of construction calls Cons as the set of function calls which return utilizable types. We also define the set of utilizable values from non-local sources, which are the function parameters and free variables. The set Src is the set of utilizable values sources, which are construction calls and non-local sources.
$
  &"Ref" &&= "LocalVars" union "ExprLabel" union "NonLocal" \
  &"Cons" &&= { f | f in "ExprLabel" and "RetType"(lbl(f)) "is Utilizable" }\
  &"NonLocal" &&= "Params" union "FV"\
  &"Src" &&= "Cons" union "NonLocal"\
  &"VarAt" &&= {(x, p) | x in "LocalVars", p in "Node"}
$

We can then define the lattices used in the analysis as @eq:RVLatticeModified. The main difference is that the reachable values lattice $R$ also includes NonLocal through the Src set, instead of just VarAt and Cons.

$
  &\
  &R &&= (powerset("VarAt" union "Src"), subset.eq)\
  &O &&= (powerset("Cons"), subset.eq)\
  &S &&= "MapLat"("Ref" -> (R, O))\
$ <eq:RVLatticeModified>

We can then update the constraint functions $evalbracket("_") : "Node" -> S$, starting with the pre-execution constraints as defined in @eq:RVPreExecConstraintModified. The main difference here is we set the initial reachable values for non-local sources to the singleton set of itself.

$
  &evalentry(mono("start")) &&=
    && { e |-> (emptyset, emptyset) | e in "Ref" without "Src" } \
    &&&&& union {f |-> ({f}, emptyset) | f in "Cons"} \
    &&&&& union {x |-> ({x}, emptyset) | x in "NonLocal"} \
  &evalentry(p) &&= &&join.big_(q in "pred"(p)) evalexit(q) \
$ <eq:RVPreExecConstraintModified>

We also redefine the post-execution constraints in @eq:RVPostExecConstraintModified, given entrance state $sp = evalentry(p)$ and $(rpe(x), ope(x)) = sp(x)$. The constraints are similar to the one in the simplified model, with the main difference when handling parameter and non-local variables. Since we require parameters and free variables to be immutable references, we report an error when there is a reassignment to them.

$
  &evalexit(mono("p:" lbl(e) = lbl(f) (...))) &&= sp[e |-> ({f}, emptyset) | f in "Cons"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= cases(
    sp[e |-> ({ (x, p) }, emptyset) ] &"if" x in "LocalVars",
    sp[e |-> ({x}, emptyset)] &"otherwise"
  )\

  &evalexit(mono("p: var" x := lbl(e))) &&=
    sp[x |-> (rpe(e), emptyset) ]\

  &evalexit(mono("p:" x := lbl(e))) &&= cases(
    sp[x |-> (rpe(e), ope(x) union (rpe (x) sect "Cons" )) ] &"if" x in "LocalVars",
    "error"& "otherwise"
  )\
  &evalexit(p) &&= evalentry(p)\

$ <eq:RVPostExecConstraintModified>

The definitions of SafeReach and Sources are not changed, but we include it here for convenience sake. Notice that SafeReach still only returns construction calls if there are more than one reachable definitions. This means that references to parameters and free variables behave similarly to references of local variable, in which a reference to a parameter or free variable is safely reachable if it is the only reachable value.
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
$

] // End of Reachable Value Analysis Modified

== Utilization analysis with effects

#[ /* Start of Utilization Analysis with Signature */
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")

Lattice

$
  // &U &&= "OrderLat"(angles(bot, "UT", top)) \
  &U &&= "FlatLat"({0, 1}) \
  &S &&= "MapLat"("Src" -> U) \
  &evalbracket("_") &&:: "Node" -> S\
$

Transfer function, given $sp = evalentry(p)$,

$
  &evalentry(mono("start")) &&= { x |-> top | x in "NonLocal" } union { f |-> bot | f in "Cons" }\
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
$
$
  &evalexit(mono("p:" lbl(e) = lbl(f) (lbl(a_1),..,lbl(a_n)))) &&= ("MarkFV" compose "MarkArgs" compose "MarkCall")(sp)\
  &wide "where:"\
  &wide "MarkCall(s)" &&= sp[e |-> top | "RetType"(phi) "is Utilizable"]\
  &wide "MarkArgs(s)" &&= sp[c |-> "Apply"(s(c), ef_i) | c in a'_i and (i |-> ef_i) in Ef]\
  &wide "MarkFV(s)" &&= sp[v |-> "Apply"(s(v), ef_v) | (v ->ef_v) in Theta]\
  &wide phi andef (Ef union Theta) &&= "Instance"("ResolveSign"(p, f), (a'_1, .., a'_n))\
  &wide a'_i &&= "Sources"(p, a_i) "for each" i in [1..n]\

  &evalexit(mono("p: return" lbl(e))) &&= sp[c |-> "UT" | c in "Sources"(p, e) ]\ \

  &evalexit(p) &&= evalentry(p)\ \
$

// $
//   &evalentry(mono("p: ")lbl(e) = lbl(f)(lbl(a_1), ..., lbl(a_n) )) = (
//     "MarkFV" compose "MarkArgs" compose "UpdateCall"
//   )(evalexit(p)) \
//     & quad "where:" \

//     & quad "UpdateCall"(s) = s[lbl(f) -> s(lbl(e))]\
//     & quad "MarkArgs"(s) = s[lbl(a_i) -> "mark"(s, lbl(a_i), ef) | (i -> ef) in "FuncEffects"(f')]\

//     & quad "MarkFV"(s) = s[x -> "mark"(s, x, ef) | (x -> ef) in "FuncEffects"(f')] \

//     & quad "mark"(s, alpha, ef) =  cases(
//       "EvalEff"("Instantiate"(epsilon, k), s(alpha)) & "if" ef = epsilon (k),
//       "EvalEff"(ef, s(alpha)) & "otherwise",
//     ) \
// $

$
  "Apply"(u, ef) &= cases(
    1 "," &"if" ef = U,
    u "," &"if" ef = N,
    0 "," &"if" ef = I,
  )\
$

Instance($t_f$, $(a_1, .., a_n)$) $:: ("Sign", ("Expr"...)) -> "Sign"$
+ Take all effect variables in $Ef$ and $Theta$ as env $Gamma = {epsilon -> emptyset}$
+ For each $a_i = {g}$ with function type $t_g$, UnifyType($Gamma, t_i,  t_g$), resulting in $Gamma_i$
+ Return: $t_f$ with effect variables replaced using $"combine"(union.big Gamma_i)$

$"combine"(Gamma) = { epsilon -> ef_1 timesef .. timesef ef_n | epsilon in Gamma, {ef_1, .., ef_n} = Gamma(epsilon)}$

UnifyType($Gamma, t andef Ef_t, tau andef Ef_tau$):
+ for all i in [1..n], Unify($Gamma, Ef_t (i), Ef_tau (i)$)
+ return unions of $Gamma$
$
  "Unify"(Gamma, ef, ef) = Gamma\
  "Unify"(Gamma, epsilon, ef) = Gamma[epsilon |-> Gamma(epsilon) union ef]\
  "Unify"(Gamma, "_", "_") = "Error"
$

- Why disallow annotating $Theta$ (esp. in top level functions) with explicit set, but allow for parametric $theta$ from input function: hard to reason with global states, but allows scope function to apply localized effect
- $theta$ instantiation and unification

- This only instantiate up to second order. Design reason:
  + Kotlin does not support currying / partial function application
  + A function returning a function is rare in Kotlin codebase

] /* End of Utilization Analysis with Signature */


Analysis result, utilization warning = ${f | f in "Cons" and evalexit(mono("exit"))(f) leqsq.not "UT" }$


== Inferencing lambda signature
TODO: text

- Given lambda $lambda$, the signature $(t_1, ..., t_n) -> t_ret andef Ef union Theta$ is inferred with:
- $Ef = {i -> "U" | p_i in "Params"(lambda) and evalexit(mono("exit"))(p_i) leqsq "UT" }$
- $Theta = {v -> "U" | v in "FV"(lambda) and evalexit(mono("exit"))(v) leqsq "UT" }$

- limitation: parametric effect inference is not yet possible
