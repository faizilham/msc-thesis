#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Generalized Utilization Analysis

TODO: defining behaviors

functions can:
- utilize any of its argument
- returns a new utilizable values
- in case of lambdas, utilize any of its free variable
- invalidates argument or free variable

Add example

== Utilization function signature

TODO: text

Utilization Effect

$E ::= U | N | I $

where $U$ = Utilized, $N$ = Not changed, $I$ = Invalidated, with operators $(plusef, timesef)$ defined as follows.

$
  // ef + ef = ef; ef_1 + ef_2 = ef_2 + ef_1\
  // ef dot ef = ef; ef_1 dot ef_2 = ef_2 dot ef_1\
  U plusef N = U", and" ef plusef I = I "for all" ef :: E\
  U timesef N = N", and" ef timesef I = I "for all" ef :: E\
$

Both operators obey idempotence ($ef circle ef = ef$) and commutative ($ef_1 circle ef_2 = ef_2 circle ef_1$) properties.

Operator $plusef$ indicates serial application of effect (one after another), while $timesef$ indicates choice or possible branching.

A function type can be annotated with utilization effects after the return type,
such as

// $f :: t_1 -->^angles(ef_1, theta_1) ... -->^angles(ef_(n-1),theta_(n-1)) t_n -->^angles(ef_n,theta_n) t_ret$

$wide f ::(t_1,..., t_n) -> t_ret andef efs(Ef, Theta)$

where $Ef = efl(ef_1, ..., ef_n) = {1 |-> ef_1, .., n |-> ef_n} , "and" Theta = {v |-> ef_v | v in "FV"(f)}$.

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

== Analysis with function signature


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

Resolve function alias: $$, $$
$
  &"Resolve" &&:: "Node" times "Ref" -> ("Func" + bot + top)\
  &"Resolve"(p, e) &&= evalexit(p)(e)
$

$
  &"ResolveSign" &&:: "Node" times "Ref" -> "Sign"\
  &"ResolveSign"(p, e) &&= cases(
    (t_1, .., t_n) -> t_ret "if" f in {top, bot},
    (t_1 sigma_1, .., t_n sigma_n) -> t_ret sigma
  )\
  &&& "where" f = evalexit(p)(e), "type"(lbl(e)) = (t_1, .., t_n) -> t_ret\
$

] /* End of Function Alias Analysis */

We also want the analysis to track utilizable values returned from any function calls, and not only from `create` calls.

$
  &"Cons" &&= { f | f in "ExprLabel" and "RetType"(lbl(f)) "is Utilizable" }\
  &"NonLocal" &&= "Params" union "FV"\
  &"Ref" &&= "LocalVars" union "ExprLabel" union "NonLocal"\
  &"Src" &&= "Cons" union "NonLocal"\
$

#[ /* Start of Function Alias Analysis */
#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

We also need to modify the transfer function of the safely-reachable value analysis defined in @eq:RVTransferFunc as follows.

Lattices
$
  &"VarAt" &&= {(x, p) | x in "LocalVars", p in "Node"}\
  &R &&= (powerset("VarAt" union "Src"), subset.eq)\
  &O &&= (powerset("Cons"), subset.eq)\
  &S &&= "MapLat"("Ref" -> (R, O))\
  &evalbracket("_") &&:: "Node" -> S\
$

$
  &evalentry(mono("start")) &&= { e |-> (emptyset, emptyset) | e in "Ref" without "Cons" } union {f |-> ({f}, emptyset) | f in "Cons"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \

  &evalexit(mono("p:" lbl(e) = lbl(f) (...))) &&= sp[e |-> ({f}, emptyset) | "RetType"(lbl(f)) "is Utilizable"]\
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
  \
$

given $sp = evalentry(p)$, $(rpe(x), ope(x)) = sp(x)$

]

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
