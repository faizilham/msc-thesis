#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Handling Collection Types and Other Extensions

A common utilization tracking case is tracking the utilization of a collection of utilizable values, such as a list of deferred calls. Individually tracking the items inside the collection is very hard if not downright uncomputable. It is more practical to treat the utilization of the items as a whole collection. To allow this, we need to maintain an invariant: the utilization status of a collection of utilizable values is always the same to all its items' utilization statuses. This means that the collection type's primitive methods, such as map, filter and add, need to have utilization annotation in their signature to ensure that the invariant is held.

#[
#show math.equation.where(block: true): set block(spacing: 1em)

== Utilization annotation in function signature

We extend the effectful function signature $(t_1, ..., t_n) -> t_ret andef PiEf union PhiEf$ with utilization annotations $utv_i$ in each of the parameter types and the return type as follows.

$
f : (ann(utv_1) t_1, ..., ann(utv_n) t_n) -> ann(utv_ret) t_ret andef PiEf union PhiEf\
"where" utv_i ::= NU | UT | top | omega
$

The utilization annotation $utv$ is either a utilization status from the set ${NU, UT, top}$ or a parametric utilization variable $omega$. A utilization annotation $utv_i$ at the $i$-th parameter indicates that the function requires the argument to have a utilization status of at least $utv_i$, such that given $u_a$ the utilization status of the argument, the analysis would report an error if $u_a leqsq.not utv_i$. A utilization annotation $utv_ret$ at the return type indicates the utilization status of the returned value. This way, we can also model functions that return an already-utilized value. As a matter of convenience, we treat a parameter or return type without annotation as annotated with $top$. For example, we can annotate the collection type methods as follows, given $C[a]$ the collection type of a utilizable type $a$.

$
  "utilizeAll" :: (C[a]) -> "Unit" andef {1 |-> EfU}\
  "add" :: (ann(omega)C[a], ann(omega) a) -> "Unit" andef {2 |-> EfU}\
  "map" :: (ann(omega)C[a], (ann(omega)a) -> b andef {1 |-> efv} union phiEf) -> C[b] andef {1 |-> efv} union phiEf\

  "filter" :: (ann(UT) C[a], (a)-> "Bool" andef {1 |-> efv} union phiEf) -> C[a] andef {1 |-> efv} union phiEf
$ <eq:CollectionTypeMethod>

The function `utilizeAll(c)` does not have any utilization status requirement, and utilizes the collection `c` as a side effect. This function is practically the same to `awaitAll` in real cases of deferred call type. The `add(c,a)` function requires the collection `c` to have the same utilization status with the added item `a`, which has a parametric utilization status $omega$. The added item is then marked as utilized, since we transfer the utilization responsibility to the collection.

The `map(c,f)` function is quite more complicated. It requires the collection `c` to have the same utilization status requirement to the first argument of `f`, and then applies the effect of `f` to the collection. The `filter` function is quite similar to `map`, but it requires the collection to be already utilized since we may lose the reference to the filtered values.

Other than the collection type, we can also employ both utilization annotation and effect in function signature to model linear-type like resources, such as a file handler type. For example, the primitives of a File type can be annotated as follows.
$
  "open"(s) : ("String") -> ann(NU)"File"\
  "read"(f) : (ann(NU)"File") -> "String"\
  "write"(f, s) : (ann(NU)"File", "String") -> "Unit"\
  "close"(s) : (ann(NU)"File") -> "Unit" andef {1 |-> EfU}\
$ <eq:FileHandlerMethods>

We can model the file handler status of open or closed by assigning not utilized ($NU$) as unclosed, and utilized ($UT$) as closed. The file handler type can only be constructed with  the `open` function, which always returns an unclosed handler. The `read` and `write` functions both require the file handler to be unclosed, and have no effect to the file handler's status. The `close` function also requires the file handler to be unclosed, but then utilize, i.e. closing, the handler as a side effect. This way the analysis can guarantee that an opened file handler is always closed exactly once, and there are no reads or writes to an already closed file handler.
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

We need to modify the analysis in order to handle utilization annotations, starting with the lattices.

$
  &Omega &&= { omega_i | p_i in "Params" and utv_i = {omega_i} } \
  &U &&= (powerset({NU, UT} union Omega), subset.eq) \
  &S &&= "MapLat"("Src" -> U)\
  &Y &&= "MapLat"(Omega -> powerset({NU, UT}))\
  &Sigma &&=  (S, Y)
$
]

Instead of just concrete utilization statuses {$NU$, $UT$}, we also include the set of utilization variables $Omega$ into the utilization lattice $U$. We include the utilization variables to allow easier inference that we will explain later. The program state lattice $Sigma$ comprises of two maps $S$, which is the map of value sources (calls, parameters, and free variables) to its utilization, and $Y$, which is the map of utilization variables to its known utilization statuses.

#let yp = $gamma_p^circle.small$
#let ypo = $gamma_p^circle.small.filled$

We then redefine the transfer functions $evalbracket(p) : "Node" -> Sigma$. We first start with the `start` node, as shown in @eq:UtilAnnoTransferStart. The program state is initialized with each parameter $p_i$ mapped to its utilization annotation $utv_i$, and any utilization variable $omega_i$ that is used in the annotations is mapped to a bottom value.
#[
#show math.equation.where(block: true): set block(spacing: 1.1em)
$
  &evalentry(mono("start")) &&= (
    { f |-> bot | f in "Cons" } union { p_i |-> utv_i | p_i in "Params" } union
    { v |-> top | v in "FV" },\
    &&& quad space space.sixth { omega_i |-> bot | p_i in "Params" and utv_i = omega_i} )\
$ <eq:UtilAnnoTransferStart>

@eq:UtilAnnoTransferReturn shows the transfer function for return statement node, given $(sp, yp) = evalentry(p)$. It is only updated to include the lattice changes, meaning that returning a value is still counted as utilizing the value.

$
  &evalexit(mono("p: return" lbl(e))) &&= (sp[c |-> {UT} | c in "Sources"(p, e) and "type"(lbl(e)) "is Utilizable"], yp)\
$ <eq:UtilAnnoTransferReturn>

We choose to keep this behavior since we do not have a proper alias tracking. For example, the identity function is annotated as $(ann(omega) x) -> ann(omega) x andef {1 |-> UT}$, implying that the function utilizes the input and creates a new value with the same previous utilization, even if it is not actually the case.

The most important change to the transfer functions is to the function call node case. First, we update the Instantiate function to requires the utilization statuses of each arguments, and also returns back the unification environment $Gamma$. Next, we update all utilization variable $omega$ occuring in $yp$ and $Gamma$ to its replacement value, so that later we can infer the required utilization statuses assigned to $omega$.
$
  &evalexit(mono("p:" lbl(e) = lbl(f) (lbl(a_1),..,lbl(a_n)))) &&= (("MarkFV" compose "MarkArgs" compose "MarkCall")(sp), ypo), "where:"\
  &wide "MarkCall(s)" &&= sp[e |-> u_ret | f in "Cons"]\
  &wide u_ret t_ret &&= "ReturnType"(tau_f) \
  &wide ypo &&= yp[omega |-> yp(omega) join Gamma(omega) | omega in yp sect Gamma] \
  &wide (tau_f andef PiEf union PhiEf), Gamma &&= "Instantiate"("ResolveSign"(p, f), (alpha'_1, .., alpha'_n), (u_1, .., u_n))\
  &wide u_i &&= sp(a'_i) "for each argument value source" a'_i\
  &wide ... &&"(rest of the definitions)"
$
]

Instead of always marking the utilization of construction call sites to $top$, it now depends on instantiated utilization annotation of the function's return value. We also update the function `ApplyEff` called by `MarkArgs` and `MarkFV`, which now also replaces any occuring utilization variable $omega$ to $ypo(omega)$, that is the latest known assignment value of $omega$ after the signature instantiation.

#[
// #show math.equation.where(block: true): set block(spacing: 1.2em)
$
  "ApplyEff"(ypo, u, ef) = cases(
    {UT} &"if" ef = EfU,
    {NU} &"if" ef = EfI,
    top &"if" ef = EfX,
    u[ypo(omega) | omega in u ] &"if" ef = EfN,
  )
$

As we mentioned earlier, the Instantiate function now also takes the utilization statuses of each arguments $(v_1, .., v_n)$ and also returns the combined unification environment $Gamma'$.

$
  "Instantiate"((u_1 t_1, .., u_n t_n) -> u_ret t_ret andef PiEf union phiEf, (alpha_1, ..., alpha_n), (v_1, ., v_n)) =\
  quad ((u'_1 t'_1, .., u'_n t'_n) -> u'_ret t'_ret andef PiEf' union PhiEf'), Gamma'\
  wide "where:" \
  wide u'_i = "replace"(Gamma', u_i) "for each" u_i\
  wide Gamma' = "combine"(union.big_(t_i "is Function") unify (Gamma, t_i, alpha_i) union union.big_(t_i) unify(Gamma, u_i, v_i)) \
  wide ... "(rest of the definitions)"
$
]

We also update the unification function $unify$ so that it can handle unification between utilization statuses and variables. The unification between a required utilization status $u$ and a concrete utilization status $u'$ is defined by the relation $u' leqsq u$. Notice that the unification is in the contraposition order when unifying the parameters of a function type.

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


The analysis reports errors and warnings based on the abstract program state at exit point, which is  $(s_"fin", gamma_"fin") = evalexit(mono("exit"))$. The resulting warnings are still the same as before, since construction calls are always marked with concrete utilization status.

$
 "Warnings" = {f | f in "Cons" and s_"fin" (f) leqsq.not { UT } }
$

For functions with utilization-annotated return type, the analysis may also check whether the returned values comply with the annotation. From the return statement nodes, we can extract the map ReturnUtil, which is the map of returned values to its utilization just before the return statement. The actual utilization of the return value $u_ret$ is simply the joined utilization statuses in ReturnUtil. The analysis can then produce a warning if $u_ret leqsq.not utv_ret$, given $utv_ret$ return utilization annotation.

$
  "ReturnUtil" = union.big_(p in "Node") { c |-> sp(c) | c in "Sources"(p, e), p "is a" mono("return" lbl(e)) "node"}\

 u_ret = join.big_(c in "ReturnUtil") "ReturnUtil"(c)\
$

The warnings for mismatched effects are still quite similar, with the main difference being the no-effect ($EfN$) requires the final utilization of a parameter to be equal to its prerequisite, annotated utilization $utv$.
$
"ParamWarnings" = {p_i | p_i in "Params" and PiEf(i) eq.not "GetEff"(utv_i, s_"fin" (p_i)) }\
"GetEff"(utv, u) = cases(
    EfN & "if" u = utv and utv != {omega},
    EfN & "if" u = {gamma_"fin" (omega)} and utv = {omega},
    EfU &"if" u = {UT},
    EfI &"if" u = {NU},
    EfX &"otherwise"
  )
$

The analysis may also infers the utilization annotation of a lambda function. At start, it assign each utilizable parameter $p_i$ with a utilization variable $omega_i$. Then, after transfer function evaluations, the utilization annotation of parameters $utv_i$ and utilization annotation of return value $utv_ret$ are inferred as follows.

$
  utv_i = gamma_"fin" (omega_i) "for each" p_i in "Params"\
  utv_ret = u_ret
$
]

/*
TODO: concrete example

== Parametric inference
TODO: text

$
  (A -> B andef {1 |-> epsilon} union phiEf, A) -> B andef {2 |-> epsilon} union phiEf \

  E = "Set of effect variables" = {epsilon_1, ..., epsilon_n}\

  Omega = { omega_i | p_i in "Params" } union{ omega_epsilon | epsilon in E } \

  U = powerset({NU, UT} union Omega) \


  "replace"(Gamma, PiEf) = {i |-> ef | i |-> epsilon in PiEf, Gamma(epsilon) = {ef}} union {i |-> omega_epsilon | i |-> epsilon in PiEf, Gamma(epsilon) = emptyset}\


  "ApplyEff"(u, ef) = cases(
    {UT} "," &"if" ef = EfU,
    {NU} "," &"if" ef = EfI,
    {omega_epsilon} "," &"if" ef = epsilon,
    u "," &"if" ef = EfN,
  )\

  "GetEff"(utv, u) = cases(
    EfN & "if" u = utv,
    EfU &"if" u = {UT},
    EfI &"if" u = {NU},
    epsilon &"if" u = {omega_epsilon},
    EfX &"otherwise"
  )\

  PiEf = {i -> "GetEff"(evalexit(mono("exit"))(p_i)) | p_i in "Params" }\
  PhiEf = {v -> "GetEff"(evalexit(mono("exit"))(v)) | v in "FV" }\

$

```
call(f : ... & 1->ef, g: ...& 1->eg, x) = f(x); g(x) --- x = {ef, eg}
```
*/

/*

== Usage analysis
TODO: text

here? drop?

- Discardable-ness
- Same-use
- Inference of discardable and same-use
*/
