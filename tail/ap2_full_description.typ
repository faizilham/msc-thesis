#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Utilization Analysis Formalization Summary

#set math.equation(numbering: none)
#show math.equation.where(block: true): set block(spacing: 1em)

#show heading.where(level: 2): set heading(numbering: "A.1")

#let Fcal = math.cal("F")

(TODO: formatting) Given a function $Fcal$, we define:

$
&"Node" &&= "The CFG nodes of" Fcal\
&"Func" &&= {"Top-level functions and lambda functions accessible from" Fcal}\

&"Param" &&= { "Parameters of" Fcal}\
&"FV" &&= { "Free variables referenced in" Fcal}\
&"ExprLabel" &&= { "Expression labels in" Fcal}\
&"LocalVars" &&= { "Local variables declared in" Fcal}\
  &"Ref" &&= "LocalVars" union "ExprLabel" union "NonLocal" \
  &"Cons" &&= { f | f in "ExprLabel" and "RetType"(lbl(f)) "is Utilizable" }\
  &"NonLocal" &&= "Params" union "FV"\
  &"Src" &&= "Cons" union "NonLocal"\
  &"VarAt" &&= {(x, p) | x in "LocalVars", p in "Node"}
$

#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$

== Function alias analysis

#[ /* Start of Function Alias Analysis */
#let evalbracket = evalbracket.with(sub:"FA")
#let evalentry = evalentry.with(sub:"FA")
#let evalexit = evalexit.with(sub:"FA")

Lattice:
$
  &F &&= "FlatLat"("Func")\
  &S &&= "MapLat"("Ref" -> F)
$

Transfer functions $evalbracket("_") : "Node" -> S$.
$
  &evalentry(mono("start")) &&= { e |-> bot | e in "Ref"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q)\
  &evalexit(mono("p:" lbl(e) = "f")) &&= sp[e |-> f | f in "Func"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> sp(x) ]
$
$
  &evalexit(mono("p:" lbl(e) = lambda.{...})) &&= sp[e |-> lambda ]\
  &evalexit(mono("p:" lbl(e) = lbl(f)(...))) &&= sp[e |-> top ]\
  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> sp(e)]\
  &evalexit(p) &&= evalentry(p)\
$

Resolve signature function
$
  &"ResolveSign"(p, e) &&= cases(
    "signature"(f) & f in "Func",
    tau_f andef emptyset & "otherwise",
  )\
  &&& "where" f = evalexit(p)(e), "type"(lbl(e)) = tau_f\
$

] /* End of Function Alias Analysis */

== Safely reachable values analysis

#[ /* Start of Reachable Value Analysis Modified */
Lattice:

$
  &R &&= (powerset("VarAt" union "Src"), subset.eq)\
  &O &&= (powerset("Cons"), subset.eq)\
  &S &&= "MapLat"("Ref" -> (R, O))\
$

Transfer functions $evalbracket("_") : "Node" -> S$

$
  &evalentry(mono("start")) &&=
    && { e |-> (emptyset, emptyset) | e in "Ref" without "Src" } \
    &&&&& union {f |-> ({f}, emptyset) | f in "Cons"} \
    &&&&& union {x |-> ({x}, emptyset) | x in "NonLocal"} \
  &evalentry(p) &&= &&join.big_(q in "pred"(p)) evalexit(q) \
$

$
  &evalexit(mono("p:" lbl(e) = lbl(f) (...))) &&= sp[e |-> ({f}, emptyset) | f in "Cons"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= cases(
    sp[e |-> ({ (x, p) }, emptyset) ] &"if" x in "LocalVars",
    sp[e |-> ({x}, emptyset)] &"otherwise"
  )\
$
$
  &evalexit(mono("p: var" x := lbl(e))) &&=
    sp[x |-> (rpe(e), emptyset) ]\

  &evalexit(mono("p:" x := lbl(e))) &&= cases(
    sp[x |-> (rpe(e), ope(x) union (rpe (x) sect "Cons" )) ] &"if" x in "LocalVars",
    "error"& "otherwise"
  )\
  &evalexit(p) &&= evalentry(p)\

$

Safely reachable value sources

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

== Utilization Analysis

#let unify = math.cal("U")
#[

#let evalbracket = evalbracket.with(sub:"UA")
#let evalentry = evalentry.with(sub:"UA")
#let evalexit = evalexit.with(sub:"UA")


Lattice
$
  &Omega &&= { omega_i | p_i in "Params" and utv_i = {omega_i} } \
  &U &&= (powerset({NU, UT} union Omega), subset.eq) \
  &S &&= "MapLat"("Src" -> U)\
  &Y &&= "MapLat"(Omega -> powerset({NU, UT}))\
  &Sigma &&=  (S, Y)
$

#let yp = $gamma_p^circle.small$
#let ypo = $gamma_p^circle.small.filled$

Transfer Functions $evalbracket("_") : "Node" -> Sigma$
$
  &evalentry(mono("start")) &&= (
    { f |-> bot | f in "Cons" } union { p_i |-> utv_i | p_i in "Params" } union
    { v |-> top | v in "FV" },\
    &&& quad space space.sixth { omega_i |-> bot | p_i in "Params" and utv_i = omega_i} )\

  &evalentry(mono("p")) &&= join.big_(q in "pred"(p)) evalexit(q)\
$

$
  &evalexit(mono("p: return" lbl(e))) &&= (sp[c |-> {UT} | c in "Sources"(p, e) and "type"(lbl(e)) "is Utilizable"], yp)\
$
$
  &evalexit(mono("p:" lbl(e) = lbl(f) (lbl(a_1),..,lbl(a_n)))) &&= (("MarkFV" compose "MarkArgs" compose "MarkCall")(sp), ypo), "where:"\

  &wide "MarkArgs(s)" &&= sp[c |-> "ApplyEff"(ypo, s(c), ef_i) | c in a'_i and (i |-> ef_i) in PiEf]\
  &wide "MarkFV(s)" &&= sp[c |-> "ApplyEff"(ypo, s(c), ef_v) | c in v' and (v ->ef_v) in PhiEf]\


  &wide "MarkCall(s)" &&= sp[e |-> u_ret | f in "Cons"]\
  &wide u_ret t_ret &&= "ReturnType"(tau_f) \
  &wide ypo &&= yp[omega |-> yp(omega) join Gamma(omega) | omega in yp sect Gamma] \
  &wide (tau_f andef PiEf union PhiEf), Gamma &&= "Instantiate"("ResolveSign"(p, f), (alpha'_1, .., alpha'_n), (u_1, .., u_n))\
  &wide u_i &&= sp(a'_i) "for each argument value source" a'_i\
  &wide alpha_i &&= "ResolveSign"(p, a_i) "for each" a_i "that is a function" \
  &wide a'_i &&= "Sources"(p, a_i) "for each argument" a_i \
  &wide v' &&= "Sources"(p, v) "given" v "a free variable of" f
$

$
  &evalexit(p) &&= evalentry(p)
$

Helper functions for function call constraints

$
  "ApplyEff"(ypo, u, ef) = cases(
    {UT} &"if" ef = EfU,
    {NU} &"if" ef = EfI,
    top &"if" ef = EfX,
    u[ypo(omega) | omega in u ] &"if" ef = EfN,
  )
$
Instantiate signature function
$
  "Instantiate"((u_1 t_1, .., u_n t_n) -> u_ret t_ret andef PiEf union phiEf, (alpha_1, ..., alpha_n), (v_1, ., v_n)) =\
  quad ((u'_1 t'_1, .., u'_n t'_n) -> u'_ret t'_ret andef PiEf' union PhiEf'), Gamma'\
  wide "where:" \
  wide u'_i = "replace"(Gamma', u_i) "for each" u_i\
  wide t'_i = "replace"(Gamma', t_i) "for each" t_i\
  wide PiEf' = "replace"(Gamma', PiEf)\
  wide PhiEf' = "replace"(Gamma', phiEf)\
  wide Gamma' = "combine"(union.big_(t_i "is Function") unify (Gamma, t_i, alpha_i) union union.big_(t_i) unify(Gamma, u_i, v_i)) \
  wide Gamma = { epsilon_k |-> emptyset | epsilon_k in PiEf} union {phiEf |-> emptyset} union {omega_k |-> emptyset | omega_k "in the inputs" }
$
Combine unification environment function
$
  "combine"(Gamma) = cases(
    "Error" & "if" exists x "s.t." abs(Gamma(x)) > 1\
    Gamma & "otherwise"
  )
$
Replace signature variable function
$
  "replace"(Gamma, PiEf) = {i |-> ef | i |-> epsilon in PiEf, Gamma(epsilon) = {ef}}\
  "replace"(Gamma, PhiEf) = {v |-> ef | v |-> epsilon in PhiEf, Gamma(epsilon) = {ef}}\
  "replace"(Gamma, omega) = Gamma(omega)\
  "replace"(Gamma, phiEf) = Gamma(phiEf)\
  "replace"(Gamma, t_"fun" andef PiEf union phiEf) = "replace"(Gamma, t_"fun") andef "replace"(Gamma, PiEf) union "replace"(Gamma, phiEf)\
  "replace"(Gamma, (t_1, ..., t_n) -> t_ret) = ("replace"(Gamma, t_1), ..., "replace"(Gamma, t_n)) -> "replace"(Gamma, t_ret)
$
Unification function
$
  unify (Gamma, ef, ef) = Gamma\
  unify (Gamma, EfX, ef) = Gamma\

  unify (Gamma, epsilon, ef) = Gamma[epsilon |-> Gamma(epsilon) union {ef}]\

  unify (Gamma, phiEf, PhiEf') = Gamma[phiEf |-> Gamma(phiEf) union {PhiEf'}]\

  unify(Gamma, omega, u) = Gamma[omega |-> Gamma(omega) union {u}]\
  unify(Gamma, u, omega) = Gamma[omega |-> Gamma(omega) union {u}]\
$
$
  unify(Gamma, u, u') = cases(
    Gamma & "if" u' leqsq u,
    "Error" & "otherwise"
  )\

  unify (Gamma, PiEf, PiEf') = "combine"(union.big_(i in PiEf) unify(Gamma, PiEf(i), PiEf'(i))) \

  unify (Gamma, PhiEf, PhiEf') = "combine"(union.big_(v in PhiEf) unify(Gamma, PhiEf(v), PhiEf'(v))) \


  unify (Gamma, t andef PiEf union phiEf, t' andef PiEf' union PhiEf')  = "combine"(unify (t, t') union unify (PiEf,PiEf') union unify (phiEf, PhiEf'))\

  unify (Gamma, (u_1 t_1, ..., u_n t_n) -> u_ret t_ret, (u'_1 t'_1, ..., u'_n t'_n) -> u'_ret t'_ret) = \
  wide "combine"(
    unify(Gamma, t_ret, t'_ret) union
    unify(Gamma, u_ret, u'_ret) union
    union.big_(i) unify (Gamma, t'_i, t_i) union unify (Gamma, u'_i, u_i)
    ) \

  unify (Gamma, "_", "_") = "Error"
$

Analysis result
$ "Warnings" = {f | f in "Cons" and evalexit(mono("exit"))(f) leqsq.not { UT } } $

$
  "ReturnUtil" = union.big_(p in "Node") { c |-> sp(c) | c in "Sources"(p, e), p "is a" mono("return" lbl(e)) "node"}\

 u_ret = join.big_(c in "ReturnUtil") "ReturnUtil"(c)\
$

Warning on return value if $u_ret leqsq.not utv_ret$

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

Inference on lambda functions

$
  utv_i = gamma_"fin" (omega_i) "for each" p_i in "Params"\
  utv_ret = u_ret
$
]
