#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *
#import pkg-curryst: rule, proof-tree

= Handling Collection and Resource Types

A common utilization tracking case is tracking the utilization of a collection of utilizable values, such as a list of deferred calls. Individually tracking the items inside the collection is very hard if not downright uncomputable. It is more practical to treat the utilization of the items as a whole collection. To allow this, we need to maintain an invariant: the utilization status of a collection of utilizable values is always the same as all its items' utilization status. This means that the collection type's primitive methods, such as map, filter and add, need to have utilization annotation in their signature to ensure that the invariant is held.

#[
#show math.equation.where(block: true): set block(spacing: 1.1em)

== Utilization status annotation in function signature

We extend the effectful function signature $(t_1, ..., t_n) -> t_ret andef PiEf union PhiEf$ with utilization status annotations $utv_i$ in each of the parameter types and the return type as follows.

$
f : (ann(utv_1) t_1, ..., ann(utv_n) t_n) -> ann(utv_ret) t_ret andef PiEf union PhiEf\
"where" utv_i : Utv, "and" Utv ::= NU | UT | top | omega
$

The utilization annotation $utv$ is either a concrete utilization status ($NU$, $UT$, or $top$) or a parametric utilization variable $omega$. A utilization annotation $utv_i$ at the $i$-th parameter indicates that the function requires the argument to have a utilization status of at least $utv_i$, such that given $u_a$ the utilization status of the argument, the analysis would report an error if $u_a leqsq.not utv_i$. A utilization annotation $utv_ret$ at the return type indicates the utilization status of the returned value. By default, we treat a parameter or return type without annotation as annotated with $top$. We may also define the utilization status annotation as an annotated type, with the typing judgment rules shown in @eq:UtilStatusJudgment.


$
  #proof-tree(rule(name:"[U-Id]",$utv <= utv$, $utv : Utv$))
  #h(5em)
  #proof-tree(rule(name:[[$top$-SupTy]], $utv <= top$, $utv : Utv$))
  \ \
  #proof-tree(rule(name: "[U-SubTy]",
    $(ann(utv_1) t_1, ..., ann(utv_n) t_n) -> ann(utv_ret) t_ret <= (ann(utv'_1) t'_1, ..., ann(utv'_n) t'_n) -> ann(utv'_ret) t'_ret$,
    $i in [1..n]$,
    $t'_i <= t_i$,
    $utv'_i <= utv_i$,
    $t_ret <= t'_ret$,
    $utv_ret <= utv'_ret$)
  )\ \
  #proof-tree(rule(name: "[Fn-Call]", $Gamma tack f(a_1, ..., a_n) : ann(utv_ret) t_ret$, $f : (ann(utv_1) t_1, ...,ann(utv_n) t_n) -> ann(utv_ret) t_ret$, $Gamma tack a_i : ann(u'_i) t'_i$, $t'_i <= t_i$, $u'_i <= utv_i$))
$ <eq:UtilStatusJudgment>

\
For example, we annotate the collection type methods as follows, given $C[a]$ the collection type of a utilizable type $a$.

$
  "utilizeAll" :: (C[a]) -> "Unit" andef {1 |-> EfU}\
  "add" :: (ann(omega)C[a], ann(omega) a) -> "Unit" andef {2 |-> EfU}\
  "map" :: (ann(omega)C[a], (ann(omega)a) -> b andef {1 |-> efv} union phiEf) -> C[b] andef {1 |-> efv} union phiEf\

  "filter" :: (ann(UT) C[a], (a)-> "Bool" andef {1 |-> efv} union phiEf) -> C[a] andef {1 |-> efv} union phiEf
$ <eq:CollectionTypeMethod>

The function `utilizeAll(c)` does not have any utilization status requirement, and utilizes the collection `c` as a side effect. This function is practically the same as `awaitAll` in real cases of deferred call type. The `add(c,a)` function requires the collection `c` to have the same utilization status as the added item `a`, which has a parametric utilization status $omega$. The added item is then marked as utilized since we transfer the utilization responsibility to the collection.

The `map(c,f)` function is quite more complicated. It requires the collection `c` to have the same utilization status requirement to the first argument of `f`, and then applies the effect of `f` to the collection. The `filter` function is quite similar to `map`, but it requires the collection to be already utilized since we may lose the reference to the filtered values.

Other than the collection type, we also employ both utilization annotation and effect in function signature to model resource types that are similar to linear types, such as the file handler type. For example, the primitives of a File type are annotated as follows.
$
  "open"(s) : ("String") -> ann(NU)"File"\
  "read"(f) : (ann(NU)"File") -> "String"\
  "write"(f, s) : (ann(NU)"File", "String") -> "Unit"\
  "close"(s) : (ann(NU)"File") -> "Unit" andef {1 |-> EfU}\
$ <eq:FileHandlerMethods>

We model the file handler status of open or closed by assigning not utilized ($NU$) as unclosed and utilized ($UT$) as closed. The file handler type can only be constructed with  the `open` function, which always returns an unclosed handler. The `read` and `write` functions both require the file handler to be unclosed and have no effect on the file handler's status. The `close` function also requires the file handler to be unclosed, but then utilize, i.e. closing, the handler as a side effect. This way the analysis guarantees that an opened file handler is always closed exactly once, and there are no reads or writes to an already closed file handler.
]

#let unify = math.cal("U")
#[

== Analysis with utilization annotations

#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")


#[
// #show math.equation.where(block: true): set block(spacing: 0.95em)
// #show math.equation.where(block: true): set text(size: 10.5pt)

We need to modify the analysis to handle utilization annotations, starting with the lattices.

$
  &Omega &&= { omega_i | p_i in "Params" and utv_i = {omega_i} } \
  &U &&= (powerset({NU, UT} union Omega), subset.eq) \
  &S &&= "MapLat"("Src" -> U)\
  &Y &&= "MapLat"(Omega -> powerset({NU, UT}))\
  &Sigma &&=  (S, Y)
$
]

Instead of just concrete utilization status {$NU$, $UT$}, we also include the set of utilization variables $Omega$ into the utilization lattice $U$. We include the utilization variables to allow easier inference which we will explain later. The program state lattice $Sigma$ comprises two maps $S$, which is the map of value sources (calls, parameters, and free variables) to its utilization, and $Y$, which is the map of utilization variables to its known utilization status.

#let yp = $gamma_p^circle.small$
#let ypo = $gamma_p^circle.small.filled$

We then redefine the transfer functions $evalbracket(p) : "Node" -> Sigma$. We first start with the `start` node, as shown in @eq:UtilAnnoTransferStart. The program state is initialized with each parameter $p_i$ mapped to its utilization annotation $utv_i$, and any utilization variable $omega_i$ that is used in the annotations is mapped to a bottom value.
#[
$
  &evalentry(mono("start")) &&= (
    { f |-> bot | f in "Cons" } union { p_i |-> utv_i | p_i in "Params" } union
    { v |-> top | v in "FV" },\
    &&& quad space space.sixth { omega_i |-> bot | p_i in "Params" and utv_i = omega_i} )\
$ <eq:UtilAnnoTransferStart>

@eq:UtilAnnoTransferReturn shows the transfer function for the return statement node, given $(sp, yp) = evalentry(p)$. It is only updated to include the lattice changes, meaning that returning a value is still counted as utilizing the value.

$
  &evalexit(mono("p: return" lbl(e))) &&= (sp[c |-> {UT} | c in "Sources"(p, e) and "type"(lbl(e)) "is Utilizable"], yp)\
$ <eq:UtilAnnoTransferReturn>

We choose to keep this behavior since we do not have proper alias tracking. For example, the identity function is annotated as $(ann(omega) x) -> ann(omega) x andef {1 |-> UT}$, implying that the function utilizes the input and creates a new value with the same previous utilization, even if it is not actually the case.

The most important change to the transfer functions is to the function call node case. First, we update the Instantiate function to require the utilization status of each argument and also return the unification environment $Gamma$. Next, we update any utilization variable $omega$ occurring in $yp$ and $Gamma$ to its replacement value; this is used later by the analysis to infer the required utilization status assigned to $omega$.
$
  &evalexit(mono("p:" lbl(e) = lbl(f) (lbl(a_1),..,lbl(a_n)))) &&= (("MarkFV" compose "MarkArgs" compose "MarkCall")(sp), ypo), "where:"\
  &wide "MarkCall(s)" &&= sp[f |-> u_ret | f in "Cons"]\
  &wide u_ret t_ret &&= "ReturnType"(tau_f) \
  &wide ypo &&= yp[omega |-> yp(omega) join Gamma(omega) | omega in yp sect Gamma] \
  &wide (tau_f andef PiEf union PhiEf), Gamma &&= "Instantiate"("ResolveSign"(p, f), (alpha'_1, .., alpha'_n), (u_1, .., u_n))\
  &wide u_i &&= sp(a'_i) "for each argument value source" a'_i\
  &wide ... &&"(rest of the definitions)"
$
]

Instead of always marking the utilization of construction call sites to $NU$, it now depends on instantiated utilization annotation of the function's return value. We also update the function `ApplyEff` called by `MarkArgs` and `MarkFV`, which now also replaces any occurring utilization variable $omega$ to $ypo(omega)$, which is the latest known assignment value of $omega$ after the signature instantiation.

#[
$
  "ApplyEff"(ypo, u, ef) = cases(
    {UT} &"if" ef = EfU,
    {NU} &"if" ef = EfI,
    top &"if" ef = EfX,
    u[ypo(omega) | omega in u ] &"if" ef = EfN,
  )
$

As we mentioned earlier, the Instantiate function now also takes the utilization status of each argument $(v_1, .., v_n)$ and also returns the combined unification environment $Gamma'$.

$
  "Instantiate"((u_1 t_1, .., u_n t_n) -> u_ret t_ret andef PiEf union phiEf, (alpha_1, ..., alpha_n), (v_1, ., v_n)) =\
  quad ((u'_1 t'_1, .., u'_n t'_n) -> u'_ret t'_ret andef PiEf' union PhiEf'), Gamma'\
  wide "where:" \
  wide u'_i = "replace"(Gamma', u_i) "for each" u_i\
  wide Gamma' = "combine"(union.big_(t_i "is Function") unify (Gamma, t_i, alpha_i) union union.big_(t_i) unify(Gamma, u_i, v_i)) \
  wide ... "(rest of the definitions)"
$
]

We also update the unification function $unify$ so that it handles unification between utilization status and variables. The unification between a required utilization status $u$ and a concrete utilization status $u'$ is defined by the relation $u' leqsq u$. Notice that the unification is in the contraposition order when unifying the parameters of a function type.

$
  unify(Gamma, omega, u) = Gamma[omega |-> Gamma(omega) union {u}]\
  unify(Gamma, u, omega) = Gamma[omega |-> Gamma(omega) union {u}]\

  unify(Gamma, u, u') = cases(
    Gamma & "if" u' leqsq u,
    "Error" & "otherwise"
  )\

    unify (Gamma, (u_1 t_1, ..., u_n t_n) -> u_ret t_ret, (u'_1 t'_1, ..., u'_n t'_n) -> u'_ret t'_ret) = \
  wide "combine"(
    unify(Gamma, t_ret, t'_ret) union
    unify(Gamma, u_ret, u'_ret) union
    union.big_(i) unify (Gamma, t'_i, t_i) union unify (Gamma, u'_i, u_i)
    ) \

  ... "(rest of the definitions)"
$

== Analysis result and basic signature inference


The analysis reports errors and warnings based on the abstract program state at the exit point, which is  $(s_"fin", gamma_"fin") = evalexit(mono("exit"))$. The resulting warnings are still the same as before since construction calls are always marked with concrete utilization status.

$
 "Warnings" = {f | f in "Cons" and s_"fin" (f) leqsq.not { UT } }
$

For functions with utilization-annotated return type, the analysis also checks whether the returned values comply with the annotation. From the return statement nodes, the analysis computes the map ReturnUtil, which is the map of returned values to its utilization just before the return statement. The actual utilization of the return value $u_ret$ is simply the joined utilization status in ReturnUtil. The analysis then produces a warning if $u_ret leqsq.not utv_ret$, given $utv_ret$ return utilization annotation.

$
  "ReturnUtil" = union.big_(p in "Node") { c |-> sp(c) | c in "Sources"(p, e), p "is a" mono("return" lbl(e)) "node"}\

 u_ret = join.big_(c in "ReturnUtil") "ReturnUtil"(c)\
$

The warnings for mismatched effects are still quite similar, with the main difference being the no-effect ($EfN$) requires the final utilization of a parameter to be equal to its prerequisite, annotated utilization $utv$. @eq:ParamWarning2 shows how this warning is defined.

$
"ParamWarnings" = {p_i | p_i in "Params" and PiEf(i) eq.not "GetEff"(utv_i, s_"fin" (p_i)) }\
"GetEff"(utv, u) = cases(
    EfN & "if" u = utv != {omega}", or" utv = {omega} and u = {gamma_"fin" (omega)},
    EfU &"if" u = {UT},
    EfI &"if" u = {NU},
    EfX &"otherwise"
  )
$ <eq:ParamWarning2>

The analysis also infers the utilization annotation of a lambda function. At the start node, it assigns each utilizable parameter $p_i$ with a utilization variable $omega_i$. Then, after transfer function evaluations, the utilization annotation of parameters $utv_i$ and utilization annotation of return value $utv_ret$ are inferred as follows.

$
  utv_i = gamma_"fin" (omega_i) "for each" p_i in "Params"\
  utv_ret = u_ret
$
]

== Chapter summary

We extend the function signatures with utilization status annotation. A status annotation is added to a parameter type, indicating the required utilization status for the corresponding argument, or to the return type to indicate the resulting utilization status. Status annotations may also be parametric; this is usually the case for higher-order functions.

To accommodate the status annotations, we only need to change the utilization analysis, since the function alias and safely-reachable values analysis are not directly related to the utilization status requirements. The most significant change is the expansion of the utilization lattice ${bot, NU, UT, top}$ with the utilization variables set, which contains all parametric status annotations in the analyzed function. Because of this expansion, we also need to record what are the instantiated values of the utilization variables, which are added to the program state lattice as the known utilization variable assignment lattice $Y$. The resulting unification environments in the Instantiate function are now recorded in the lattice $Y$ for every function call. This lattice $Y$ is useful for inferring the utilization requirements for lambda functions. Apart from recording the unification environments, the Instantiate function now also checks and instantiates the function signatures according to the arguments' utilization status.

By using the combination of utilization status and effect annotations, we model the utilization of collection types and resource-like types like a file handler. We now only need to implement a prototype of the analysis in Kotlin.
