#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *
#import pkg-curryst: rule, proof-tree

= Generalizing the Analysis to All Functions

While the simplified model of the problem is useful as a starting point, in practice we need a more sophisticated model that can handle utilizations through any functions and not just `create` and `utilize`. We start by defining what a function may do in relation to utilizable values. A function may utilize any of its utilizable arguments, similar to the `utilize` function. A function that returns a utilizable type is also regarded as a value-constructing function, just like the `create` function. Accordingly, a utilizable value that escapes a function through the return statement should also be regarded as utilized inside that function. @lst:TopLevelUtilEx shows an example of how some functions may affect utilization. The `utilizeTwo` function utilizes both of its arguments, while the `newUtilizable` function is basically an intermediary for a `create` function and thus its behavior is the same as `create`.

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

The `passThrough` function behavior is quite unintuitive at first glance since it only returns an existing value instead of a new one. There are two ways to handle this case. First, we declare that the function does not use its argument and the return value is an alias to the argument. The second way is to declare that the function uses its argument and then return a new utilizable value. While the first way is the more accurate description of `passThrough` behavior, we choose the second description in this model since it bypasses the aliasing problem, and if we want to add a more accurate alias analysis in the future it can be modified by disabling the return-means-utilize behavior for argument values.

Lambda functions behave in a similar way to top-level functions, but one main difference is that lambda functions may also affect the utilization of its free variables, that is the variables declared on the higher-level scope than the lambda function's body. @lst:LambdaUtilEx shows the example of lambda functions' effect on utilization. In the `testLambda` function, the lambda function assigned to variable `lam` uses its first argument and the free variable `b`. Therefore, the values in `a` and `b` are utilized after the `lam(a)` call.

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

A lambda function may also change the values of mutable free variables, as shown in the `invalidateErr` function in the given example. We decide to regard any mutation of free variable by a lambda function as a possible error, and thus the example is reported as an error when it should be correct. This is because tracking the reference changes and values escapes through the free variables complicates the analysis too much, while in practice free-variable mutating lambda functions are rarely used.

From the given examples, we conclude that a function may utilize its parameters (or free variables) or does not affect them. In other words, given a parameter's utilization status $u$, a function may change it to $UT$ ("definitely utilized") as a side effect or keep it as $u$. The utilization status lattice, however, also consists of the values $NU$ ("definitely not utilized") and $top$ ("maybe utilized or not"). Changing the utilization to $top$ may happen if we do not have any information about the function, and thus the analysis needs to over-approximate. While there are not many examples of functions that need to change the utilization back to $NU$, it is useful to model it for the sake of completion.


== Utilization effects

We define the set of utilization effects $Ef$ in @eq:UtilEffects, where, given $u$ the initial utilization status of a parameter or free variable, $EfU$ means it utilizes the value (changing $u$ to $UT$), $EfI$ means it invalidates the value's utilization (changing $u$ to $NU$), $EfN$ means it does not affect the value (keeping it to $u$), and $EfX$ means unknown effect (changing $u$ to $top$). Effects may also be parametric, with $epsilon$ as an effect variable.

$
  Ef := EfU | EfI | EfN | EfX | epsilon
$ <eq:UtilEffects>

We then extend the function type signature after its return type with effect annotations for each of its parameters and free variables in the case of lambda functions. @eq:FuncSignWithEffects shows the extended function type signature with $PiEf$ the map of parameter indexes to utilization effects and, in the case of lambda functions, with $PhiEf$ the map of free variables to utilization effects. A function without any effect annotation is equivalent to having no effect on its arguments and free variables.

$
  f : (t_1,..., t_n) -> t_ret andef PiEf union PhiEf\
  "where"
  PiEf : "Index" |-> Ef = {1 |-> ef_1, .., n |-> ef_n},\
  wide quad PhiEf : "FV" |-> Ef = {v |-> ef_v | v in "FV"(f)}
$ <eq:FuncSignWithEffects>

 All effects are subeffects to the unknown effect $EfX$, such that $ef <= EfX$ for all $ef : Ef$. If we were to define the utilization effect as a type and effect system, @eq:EffectJudgment shows the required judgment rules.

$
  #proof-tree(rule(name:"[Eff-Id]",$ef <= ef$, $ef : Ef$))
  #h(3em)
  #proof-tree(rule(name:[[$EfX$-SupEff]], $ef <= EfX$, $ef : Ef$))
  \ \
  #proof-tree(rule(name:"[Map-SubEff]", $hat(A) <= hat(A)'$, $hat(A) : X |-> Ef$,$hat(A)' : X' |-> Ef$, $X subset.eq X'$, $forall x in X . hat(A)(x) <= hat(A)'(x)$))
  \ \
  #proof-tree(rule(name: "[SubEff]", $(t_1, ..., t_n) -> t_ret andef PiEf union PhiEf <= (t'_1, ..., t'_n) -> t'_ret andef PiEf' union PhiEf'$, $t'_i <= t_i, i in [1..n]$, $t_ret <= t'_ret$, $PiEf <= PiEf'$, $PhiEf <= PhiEf'$))
$ <eq:EffectJudgment>

// Given effect maps $hat(A) : X -> Ef$ and $hat(B) : Y -> Ef$, the relation $hat(A) <= hat(B)$ holds if $X subset.eq Y$ and for all $x in X$, $hat(A)(x) <= hat(B)(x)$.


For example, the functions previously shown in @lst:TopLevelUtilEx and the lambda function `lam` in @lst:LambdaUtilEx is annotated as follows.

$
  "utilizeTwo" : ("Utilizable", "Utilizable") -> "Unit" andef { 1 |-> EfU, 1 |-> EfU}\
  "newUtilizable" : () -> "Utilizable"\
  "passThrough": ("Utilizable") -> "Utilizable" andef { 1 |-> EfU }\
  "lam" : ("Utilizable") -> "Unit" andef {1 |-> EfU, b |-> EfU}
$

Notice how `newUtilizable` does not have an effect since it only creates a new value, while `utilizeTwo` and `passThrough` only have effects on its parameters. In addition to the parameter effects, the lambda function `lam` also has free variable effects.

=== Parametric utilization effect

Unlike first-order functions, higher-order functions usually do not affect utilization directly. Instead, its effects depend on the functions it receives as an argument. In order to handle this, functions may also be annotated with the parametric annotation $epsilon$ for a parametric effect, and $phiEf$ for a parametric map of free variable effects. For example, the function `apply(f,x) = f(x)`, which applies the function `f` with the value `x`, is annotated as follows.

$
  "apply" : ((A) -> B andef { 1 |-> epsilon } union phiEf, A ) -> B andef { 2 |-> epsilon } union phiEf\
$ <eq:ApplySignature>

This example illustrates how the effect of `apply` is parametric to the effects of function `f`. The utilization of parameter `x`, which is the second parameter of `apply`, depends on the effect of `f` on its first parameter, that is $epsilon$. If function `f` has some effects on free variables annotated as $phiEf$, then `apply` also has the same effects. Currently, we only allow top-level functions' free variable annotation to be either parametric (as variable $phiEf$) or empty ($PhiEf = emptyset$) to prevent notating effects on global variables. This is because we limit the analysis to a local, intra-procedural analysis.

== Function alias analysis

Since any function call may create a new utilizable value or has some effects, we first need to determine which function is called and what is its effect signature before we analyze the values utilizations. We determine the function by running a function alias analysis, which is a reachable definition analysis modified for function type values.

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

We define the transfer functions $evalbracket("_") : "Node" -> S$ for the data flow analysis in @eq:FuncAliasTransfers, given the previous state $sp = evalentry(p)$.
$
  &evalentry(mono("start")) &&= { e |-> bot | e in "Ref"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
  &evalexit(mono("p:" lbl(e) = "f")) &&= sp[e |-> f | f in "Func"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> sp(x) ]\
  &evalexit(mono("p:" lbl(e) = lambda.{...})) &&= sp[e |-> lambda ]\
  &evalexit(mono("p:" lbl(e) = lbl(f)(...))) &&= sp[e |-> top ]\

  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> sp(e)]\
  &evalexit(p) &&= evalentry(p)\
$ <eq:FuncAliasTransfers>

The transfer functions are similar to the reachable definitions analysis. The main difference is the function lattice is a flat lattice, meaning if there is more than one reachable definition then the reference would be mapped to $top$. Another notable difference is for function calls, in which we also set it to $top$ since we currently do not handle function-returning functions.

We then define a function to resolve the function signature from a reference as @eq:ResolveSign. If the reference can be resolved to a single top-level or lambda function declaration, it simply returns the function's signature. Otherwise, it returns the function type with unknown utilization effects since we cannot guarantee what are the effects. The signature of a top-level function definition is given by annotations, while a lambda function's signature is typically inferred. We will discuss how to infer the effect signature of lambda functions later.

$
  &"ResolveSign"(p, e) &&= cases(
    "signature"(f) & f in "Func",
    tau_f andef {i |-> EfX | i "param of" tau_f} & "otherwise",
  )\
  &&& "where" f = evalexit(p)(e), "type"(lbl(e)) = tau_f\
$ <eq:ResolveSign>

] /* End of Function Alias Analysis */

== Modifying the safely-reachable values analysis

#[ /* Start of Reachable Value Analysis Modified */
#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

In the simplified model, we only care about the utilization of values created inside the function, since we assume functions other than `create` and `utilize` do not create new values or have any effects. Since now any functions may have effects on its arguments or free variables, we also need to track the utilization of those values.

In addition to LocalVars and ExprLabel, we now also assume each function to have the set of parameters Param and the set of free variables FV. We redefine the set of construction calls Cons as the set of function calls that return utilizable types. We also define the set of utilizable values from non-local sources, which are the function parameters and free variables. The set Src is the set of utilizable values sources, which are construction calls and non-local sources.
$
  &"Ref" &&= "LocalVars" union "ExprLabel" union "NonLocal" \
  &"Cons" &&= { f | f in "ExprLabel" and "RetType"(lbl(f)) "is Utilizable" }\
  &"NonLocal" &&= "Params" union "FV"\
  &"Src" &&= "Cons" union "NonLocal"\
  &"VarAt" &&= {(x, p) | x in "LocalVars", p in "Node"}
$

We then define the lattices used in the analysis as @eq:RVLatticeModified. The main difference is that the reachable values lattice $R$ also includes NonLocal through the Src set, instead of only VarAt and Cons.

$
  &R &&= (powerset("VarAt" union "Src"), subset.eq)\
  &O &&= (powerset("Cons"), subset.eq)\
  &S &&= "MapLat"("Ref" -> (R, O))\
$ <eq:RVLatticeModified>

We update the transfer functions $evalbracket("_") : "Node" -> S$, starting with the pre-execution transfer functions as defined in @eq:RVPreExecTransferModified. The main difference here is we set the initial reachable values for non-local sources to the singleton set of itself.

$
  &evalentry(mono("start")) &&=
    && { e |-> (emptyset, emptyset) | e in "Ref" without "Src" } \
    &&&&& union {f |-> ({f}, emptyset) | f in "Cons"} \
    &&&&& union {x |-> ({x}, emptyset) | x in "NonLocal"} \
  &evalentry(p) &&= &&join.big_(q in "pred"(p)) evalexit(q) \
$ <eq:RVPreExecTransferModified>

We also redefine the post-execution transfer functions in @eq:RVPostExecTransferModified1 and @eq:RVPostExecTransferModified2, given entrance state $sp = evalentry(p)$ and $(rpe(x), ope(x)) = sp(x)$. The equations are similar to the one in the simplified model, with the main difference when handling parameter and non-local variables. Since we require parameters and free variables to be immutable references, we report an error when there is a reassignment to them.

$
  &evalexit(mono("p:" lbl(e) = lbl(f) (...))) &&= sp[e |-> ({f}, emptyset) | f in "Cons"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= cases(
    sp[e |-> ({ (x, p) }, emptyset) ] &"if" x in "LocalVars",
    sp[e |-> ({x}, emptyset)] &"otherwise"
  )\
$  <eq:RVPostExecTransferModified1>
$
  &evalexit(mono("p: var" x := lbl(e))) &&=
    sp[x |-> (rpe(e), emptyset) ]\

  &evalexit(mono("p:" x := lbl(e))) &&= cases(
    sp[x |-> (rpe(e), ope(x) union (rpe (x) sect "Cons" )) ] &"if" x in "LocalVars",
    "error"& "otherwise"
  )\
  &evalexit(p) &&= evalentry(p)\

$ <eq:RVPostExecTransferModified2>

The definitions of SafeReach and Sources have not changed, but we include them here for convenience's sake. Notice that SafeReach still only returns construction calls if there is more than one reachable definition. This means that references to parameters and free variables behave similarly to references of local variables, in which a reference to a parameter or free variable is safely reachable if it is the only reachable value.
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

== Utilization analysis with function effects

#[ /* Start of Utilization Analysis with Signature */
#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")

We modify the utilization analysis to handle effects. We first define the lattices for the utilization analysis as shown in @eq:UtilAnalysisLattices. The utilization status lattice $U$ is the same as before. The program state lattice $S$ is modified to be a mapping from any value sources Src since we also want to track non-local values such as parameters and free variables.

$
  &U &&= "FlatLat"({NU, UT}) \
  &S &&= "MapLat"("Src" -> U) \
$ <eq:UtilAnalysisLattices>

We then modify the transfer functions $evalbracket("_") : "Node" -> S$. @eq:UtilAnalysisTransferGen1 shows the modified pre-execution transfer function. In the initial state, construction call sites are set to $bot$, while parameters and free variables are set to $top$ since we do not know its initial utilization.

$
  &evalentry(mono("start")) &&= { f |-> bot | f in "Cons" } union { x |-> top | x in "NonLocal" }\
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
$ <eq:UtilAnalysisTransferGen1>

As for the post-execution transfer functions, there are only two main cases. The first case is returning a utilizable type, in which we mark the safely-reachable values of the returned expression as utilized.

$
  &evalexit(mono("p: return" lbl(e))) &&= sp[c |-> {UT} | c in "Sources"(p, e) and "type"(lbl(e)) "is Utilizable"]\
$

The second main case is the function call node, defined as follows.

$
  &evalexit(mono("p:" lbl(e) = lbl(f) (lbl(a_1),..,lbl(a_n)))) &&= ("MarkFV" compose "MarkArgs" compose "MarkCall")(sp),  "where:"\
  &wide "MarkCall(s)" &&= sp[f |-> NU | f in "Cons"]\
  &wide "MarkArgs(s)" &&= sp[c |-> "ApplyEff"(s(c), ef_i) | c in a'_i and (i |-> ef_i) in PiEf]\
  &wide "MarkFV(s)" &&= sp[c |-> "ApplyEff"(s(c), ef_v) | c in v' and (v ->ef_v) in PhiEf]\
  &wide tau_f andef PiEf union PhiEf &&= "Instantiate"("ResolveSign"(p, f), (alpha'_1, .., alpha'_n))\
  &wide alpha_i &&= "ResolveSign"(p, a_i) "for each arg" a_i "that is a function ref" \
  &wide a'_i &&= "Sources"(p, a_i) "for each arg" a_i \
  &wide v' &&= "Sources"(p, v) "given" v "a free variable of" f
$ <eq:UtilAnalysisFuncCall>

The transfer function is essentially a composition of three primary functions: (1) MarkCall for marking a potential creation of utilizable value, that is by setting $f$ to $NU$ if it is a construction call (2) MarkArgs for applying the utilization effects to the safely-reachable values of the arguments, and (3) MarkFV for applying the effects to the safely-reachable values of free variables. The effect-applying function in MarkArgs and MarkFV is defined in @eq:ApplyEff, which simply returns a new utilization status according to the effect. Before the applications of the three marking functions, however, the analysis first resolves safely-reachable values of each argument and free variable, and also checks and instantiates the signature of $f$ based on the arguments it receives.

#[
// Temporarily decrease block spacing here
#show math.equation.where(block: true): set block(spacing: 1em)
$
"ApplyEff"(u, ef) = cases(
    {UT} "," &"if" ef = EfU,
    {NU} "," &"if" ef = EfI,
    top "," &"if" ef = EfX,
    u "," &"if" ef = EfN,
  )\
$ <eq:ApplyEff>
]

This transfer function is much more complicated than the one in the simplified problem for two reasons. First, any function can now create new utilizable values, change the utilization of its parameters and free variables, or both. This is why the transfer function is a composition of the three marking functions. Second, we allow functions to have parametric effects in order to be able to handle higher-order functions; hence, the function signature must be instantiated and checked based on the received arguments.

=== Instantiating function signatures

As we mentioned earlier, the analysis needs to instantiate the signature based on the resolved arguments before applying the effects. The Instantiate function instantiates any parametric effects in the signature with the concrete effect signatures of the arguments and also checks the effect signature of the arguments if the signature has a concrete one instead.

For example, suppose that we have higher-order functions `apply(f,a)` and `applyU(f,a)` that pass the value $a$ to the function $f$. The signatures of these functions are shown in @eq:InstantiateExample1. The function `applyU` is similar to `apply` but with the difference that it requires the passed function to utilize its argument.
#[
// Temporarily decrease block spacing here
// #show math.equation.where(block: true): set block(spacing: 1em)

$
  &"apply"  &&: ((A) -> B andef { 1 |-> epsilon } union phiEf, A) -> B andef { 2 |-> epsilon } union phiEf\
  &"applyU" &&: ((A) -> B andef { 1 |-> EfU } union phiEf, A) -> B andef { 2 |-> EfU } union phiEf\
$ <eq:InstantiateExample1>

Suppose that we also have the functions `f` and `g` that we are going to pass as an argument to `apply` and `applyU`. The function `f` utilizes its first argument, and invalidates the free variable `x`, while function `g` only utilizes the free variable `y`. These functions have the following signatures:
$
  f : (A) -> B andef {1 |-> EfU, x |-> EfI}\
  g : (A) -> B andef {1 |-> EfN, y |-> EfU}
$

The calls `apply(f,a)`, `apply(g,a)`, `applyU(f,a)`, and `applyU(g,a)` are then instantiated as follows, given $sigma_f$ and $sigma_g$ the signatures of `f` and `g`:

$
  &"Inst"("apply", (sigma_f)) &&= (A -> B andef {1 |-> EfU, x |-> EfI}, A) -> B andef {2 |-> EfU, x |-> EfI}\
  &"Inst"("apply", (sigma_g)) &&= (A -> B andef {1 |-> EfN, y |-> EfU}, A) -> B andef {2 |-> EfN, y |-> EfU}\
  &"Inst"("applyU", (sigma_f)) &&= (A -> B andef {1 |-> EfU, x |-> EfI}, A) -> B andef {2 |-> EfU, x |-> EfI}\
  &"Inst"("applyU", (sigma_g)) &&= "Error"
$
]

#let unify = math.cal("U")

As illustrated in the example, the instantiations of `apply(f,a)` and `apply(g,a)` replace the parametric effects $epsilon$ and $phiEf$ with the effects of `f` and `g` accordingly. The instantiation of `applyU(f,a)` only replaces $phiEf$ since it is the only parametric effect in `applyU`. In contrast to the other calls, the instantiation of `applyU(g,a)` results in an error since the required effect signature #box($(A) -> B andef {1 |-> EfU} union phiEf$) is not fulfilled by `g`, which has the effect $EfN$ for its first parameter.

We define  Instantiate : $("Signature", angles("Signature", ...)) -> "Signature"$ as shown in @eq:InstantiateDef. It collects all parametric effect variables in $PiEf$ and $phiEf$ into environment $Gamma$, and then unifies each parameter type $t_i$ that is a function type with the argument signature $alpha_i$ using the unification function $unify$. The results of the unification are combined into $Gamma'$. Finally, it replaces all effect variables in the types and the effect sets based on the combined environment $Gamma'$.
#[
// #show math.equation.where(block: true): set block(spacing: 1em)

$
  "Instantiate"((t_1, ..., t_n) -> t_ret andef PiEf union phiEf, (alpha_1, ..., alpha_n) ) =\
  quad (t'_1, ..., t'_n) -> t'_ret andef PiEf' union PhiEf'\
  wide "where:" \
  wide t'_i = "replace"(Gamma', t_i) "for each" t_i\
  wide PiEf' = "replace"(Gamma', PiEf)\
  wide PhiEf' = "replace"(Gamma', phiEf)\
  wide Gamma' = "combine"(union.big_(t_i "is Function") unify (Gamma, t_i, alpha_i)) \
  wide Gamma = { epsilon_k |-> emptyset | epsilon_k in PiEf} union {phiEf |-> emptyset}
$ <eq:InstantiateDef>

The combine function simply checks if there are more than two possible replacements, it should report an error.

$
  "combine"(Gamma) = cases(
    "Error" & "if" exists epsilon "s.t." abs(Gamma(epsilon)) > 1\
    Gamma & "otherwise"
  )\
$ <eq:CombineDef>

We define the replace function as shown in @eq:ReplaceDef. As the name suggests, it replaces any occurrence of effect variables $epsilon$ and $phiEf$ based on the combined environment.

$
  "replace"(Gamma, PiEf) = {i |-> ef | i |-> epsilon in PiEf, Gamma(epsilon) = {ef}}\
  "replace"(Gamma, PhiEf) = {v |-> ef | v |-> epsilon in PhiEf, Gamma(epsilon) = {ef}}\
  "replace"(Gamma, phiEf) = Gamma(phiEf)\
  "replace"(Gamma, t_"fun" andef PiEf union phiEf) = "replace"(Gamma, t_"fun") andef "replace"(Gamma, PiEf) union "replace"(Gamma, phiEf)\
  "replace"(Gamma, (t_1, ..., t_n) -> t_ret) = ("replace"(Gamma, t_1), ..., "replace"(Gamma, t_n)) -> "replace"(Gamma, t_ret)
$ <eq:ReplaceDef>
]

// Instance($t_f$, $(a_1, .., a_n)$) $:: ("Sign", ("Expr"...)) -> "Sign"$
// + Take all effect variables in $Ef$ and $Theta$ as env $Gamma = {epsilon -> emptyset}$
// + For each $a_i = {g}$ with function type $t_g$, UnifyType($Gamma, t_i,  t_g$), resulting in $Gamma_i$
// + Return: $t_f$ with effect variables replaced using $"combine"(union.big Gamma_i)$

// $"combine"(Gamma) = { epsilon -> ef_1 timesef .. timesef ef_n | epsilon in Gamma, {ef_1, .., ef_n} = Gamma(epsilon)}$

#pagebreak()

We define the unification function $unify$ in @eq:UnifyDef. The unification function adds a possible replacement of effect variables $epsilon$ and $phiEf$ to environment $Gamma$ recursively for each parameter in a function type. If the unification does not match, e.g. $unify (EfN, EfU)$, the function returns an error.

$
  unify (Gamma, ef, ef) = Gamma\
  unify (Gamma, EfX, ef) = Gamma\

  unify (Gamma, epsilon, ef) = Gamma[epsilon |-> Gamma(epsilon) union {ef}]\

  unify (Gamma, phiEf, PhiEf') = Gamma[phiEf |-> Gamma(phiEf) union {PhiEf'}]\
  unify (Gamma, PiEf, PiEf') = "combine"(union.big_(i in PiEf) unify(Gamma, PiEf(i), PiEf'(i))) \

  unify (Gamma, PhiEf, PhiEf') = "combine"(union.big_(v in PhiEf) unify(Gamma, PhiEf(v), PhiEf'(v))) \

  unify (Gamma, t andef PiEf union phiEf, t' andef PiEf' union PhiEf')  = "combine"(unify (t, t') union unify (PiEf,PiEf') union unify (phiEf, PhiEf'))\

  unify (Gamma, (t_1, ..., t_n) -> t_ret, (t'_1, ..., t'_n) -> t'_ret) = "combine"( unify(Gamma, t_ret, t'_ret) union union.big_(i) unify (Gamma, t'_i, t_i)) \

  unify (Gamma, "_", "_") = "Error"
$ <eq:UnifyDef>

] /* End of Utilization Analysis with Signature */


=== Analysis result and effect inference

After a single pass of transfer functions evaluations, the analysis reports any unutilized construction calls in the function as follows.

$ "Warnings" = {f | f in "Cons" and evalexit(mono("exit"))(f) leqsq.not { UT } } $

The analysis also produces warnings for top-level function signature effects that do not match the actual utilization as shown in @eq:ParamWarningNonParametric. For example, if the function is annotated with parameter effect ${ 1 |-> EfU}$ but the first parameter is not guaranteed to be utilized, then it should be reported as an error.

$
"ParamWarnings" = {p_i | p_i in "Params" and PiEf(i) eq.not "GetEff"(evalexit(mono("exit"))(p_i)) }\
"GetEff"(u) = cases(
    EfU &"if" u = {UT},
    EfI &"if" u = {NU},
    EfN &"otherwise"
  )
$ <eq:ParamWarningNonParametric>


If the function is a lambda function, the analysis also infers the effect sets $PiEf union PhiEf$ in its signature as follows.

$
  PiEf = {i -> "GetEff"(evalexit(mono("exit"))(p_i)) | p_i in "Params" }\
  PhiEf = {v -> "GetEff"(evalexit(mono("exit"))(v)) | v in "FV" }\
$

This method of effect checking and inference accommodates the most common cases in utilization analysis. However, it is only limited to non-parametric effect signatures since we only recorded concrete utilization status (i.e. $NU$ or $UT$ or $top$ instead of a variable) in the analysis lattices.


== Chapter summary

We generalize the forward analysis of the simplified problem to be able to handle any functions, including higher-order functions. We first introduce effect annotations to function signatures, indicating how a function affects the utilization status of its parameters and free variables: changing the status to utilized, to not-utilized, to an unknown status, or having no effect. Higher-order functions are annotated with parametric effect, such that they may take the effect of the functions passed to them as input arguments.

We introduce a new phase of the analysis, the function alias analysis, that shall run before the reachable value analysis. The function alias analysis determines which functions are actually called and resolves their signatures since we now must handle any function. We modify the reachable value analysis to include parameters and free variables as value sources aside from the local construction calls. The most significant change is to the utilization analysis, in which a function call may create a new utilizable value, affect the utilization status of its parameters and free variables, or both. Since effect annotations are also parametric, the analysis must also instantiate and check the annotations based on the input arguments. When the analysis is finished, it checks a function's effect annotations for each parameter to make sure that it correctly reflects what happened in the function body. The analysis also infers a concrete effect annotation for lambda functions.

With the addition of the effect annotations and the generalization to all functions, we achieve our goals of handling any user-defined functions, handling higher-order functions, and the goal of checking and inferring functions' utilization effects. The last thing we have not yet handled is the collection and resource-like types, which require utilization status annotations.
