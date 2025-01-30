#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Proof of Safely-Reachable Property <apx:SafeReachProof>

#[ /* Start of Safely Reachable Value */
#set math.equation(numbering: none)
#show math.equation.where(block: true): set block(spacing: 1em)

#let evalbracket = evalbracket.with(sub:"RV")
#let evalentry = evalentry.with(sub:"RV")
#let evalexit = evalexit.with(sub:"RV")
#let ope = $o_p^circle.small$
#let rpe = $r_p^circle.small$
#let opx = $o_p^circle.small.filled$
#let rpx = $r_p^circle.small.filled$

Given the transfer functions,

$
  &evalentry(mono("start")) &&= { e |-> (emptyset, emptyset) | e in "Ref" without "Cons" } union {f |-> ({f}, emptyset) | f in "Cons"} \
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q) \
  &evalexit(mono("p:" lbl(e) = lbl(f)())) &&= sp[e |-> ({f}, emptyset) | f in "Cons"]\
  &evalexit(mono("p:" lbl(e) = x)) &&= sp[e |-> ({ (x, p) }, emptyset) ]\
  &evalexit(mono("p: var" x := lbl(e))) &&= sp[x |-> (rpe(e), emptyset) ]\
  &evalexit(mono("p:" x := lbl(e))) &&= sp[x |-> (rpe(e), ope(x) union (rpe (x) sect "Cons" )) ]\
  &evalexit(p) &&= evalentry(p)
$

and the safely-reachable references function,

$
  &"SafeReach"(p, e) &&= cases(
    r_e & "if" abs(r_e) <= 1,
    (r_e sect "Cons") without o_e& "otherwise"
  )\
  &&&"where" (r_e, o_e) = evalexit(p)(e)
$

we shall prove that the set $sigma = "SafeReach"(p, e)$ is safely reachable for any $p$ and $e$, that is if $abs(sigma) >=2$, all values in $sigma$ are construction calls that exist exclusively from each other. Construction calls $f$ and $g$ exist exclusively if their CFG nodes $mono(p_f: lbl(e_f) = f(...))$ and $mono(p_g: lbl(e_g) = g(...))$ are not the ancestor of each other. The set of ancestors of a node is defined as follows, given $"pred"(p)$ the direct predecessor of node $p$.

$
  "ancestor(p)" = "pred"(p) union union.big_(q in "pred"(p)) "ancestor"(q)
$

We first prove three sub-properties of the safely-reachable property.

*Lemma 1*. If $abs(sigma) >= 2$, each value in $sigma$ must be a non-occluded construction call and not a variable reference, that is for any $c in sigma$, $c in.not o_e$, $c in "Cons"$ and $c != (x, p')$ for some $x$ and $p$.\
*Proof.* A set $sigma$ with more than one element only exists if $|r_e| > 1$, for $r_e$ the reachable definitions of expression $e$. Per the definition of SafeReach, the set $r_e$ is intersected with Cons, which contains no variable reference $(x,p)$, and then subtracted by occluded set $o_e$. Therefore, for any $c in sigma$, $c in.not o_e$, $c in "Cons"$ and $c != (x, p')$. $qed$

*Lemma 2*. For any expression label $e$, node $p$, and $(r_e, o_e) = evalexit(p)(e)$, if the reachable definitions set $r_e$ has more than one construction calls, all of them must exist exclusively to each other.\
*Proof.* Let $f$ and $g$ be construction calls in $r_e$. Construction calls are only added to the reachable definition set of an expression label in the case of function calls. Hence, there must be some nodes $q_f: e = f(...)$ and $q_g: e = g(...)$ which are ancestors of $p$. By the definition of the control flow graph, the value expression nodes must have an expression label that is unique to the program path. Since both $q_f$ and $q_g$ have the expression label $e$, the nodes $q_f$ and $q_g$ must appear in different program paths. This means that $q_f$ and $q_g$ cannot be the ancestor of each other. Therefore, $f$ and $g$ must exist exclusively from each other. $qed$

*Lemma 3*. For any variable $x$, node $p$, and $(r_x, o_x) = evalexit(p)(x)$, if there are construction calls $f, g in r_x$ in which node $q_f$ is an ancestor to node $q_g$, $f$ must be included in occluded set $o_x$.\
*Proof.* Let the node $q_f$ and $q_g$ be respectively $q_f: lbl(e_f) = f(...)$ and $q_g : lbl(e_g) = g(...)$. The reachable set $r_x$ is set in the case of variable declaration and assignment, while the  occluded set $o_x$ is only updated in the latter case. Since $f, g in r_x$ and $q_f$ is ancestor to $q_g$, there must be a variable declaration or assignment node to $x$ in the form of $p_f:(mono("var"))x:=lbl(e_f)$, which is an ancestor to an assignment node $p_g: x := lbl(e_g)$. The node $p_g$ must be an assignment node because a variable declaration node must not have ancestors that are declaration or assignment nodes of the same variable. Both $p_f$ and $p_g$ are ancestors of $p$, and since $f in r_x$, there must also be a program path from $p_f$ to $p$ that does not include $p_g$, otherwise the assignment of $x$ to $f$ is always overwritten to $g$. Node $p$ is also neither a declaration nor an assignment to $x$ for the same reason.

#[
  #let of = $o_f^circle.small.filled$
  #let rf = $r_f^circle.small.filled$
  #let og = $o_g^circle.small$
  #let rg = $r_g^circle.small$
  #let ogx = $o_g^circle.small.filled$
  #let rgx = $r_g^circle.small.filled$
  #let oh = $o_h^circle.small.filled$
  #let rh = $r_h^circle.small.filled$


  Let the reachable and occluded sets after $f$ assignment be $(rf, of) = evalexit(p_f)(x)$, before $g$ assignment be $(rg, og) = evalentry(p_g)(x)$, and after $g$ assignment be $(rgx, ogx) = evalexit(p_g)(x)$. Since $p$ is not an assignment node for variable $x$, $evalentry(p)(x) = evalexit(p)(x) = (r_x, o_x)$.

  If between node $p_f$ and $p_g$ there are no assignment nodes of variable $x$, then $rg supset.eq rf supset.eq {f}$. If there is an assignment node $p_h$ such that $(rh, oh) = evalexit(p_h)(x)$, then $og supset.eq oh supset.eq rf supset.eq {f}$. This also inductively applies if there are more assignment nodes between them. because an assignment to $x$. Since either $f in rg$ or $f in og$ applies, then $f in ogx$. The node $p_g$ is an ancestor to $p$, therefore $ogx supset.eq o_x$ and $f in o_x$. $qed$
]

Finally, we prove the safely-reachable property.

*Theorem*. Given $sigma = "SafeReach"(p, e)$, all values in $sigma$ exist exclusively if $abs(sigma) >=2$.\
*Proof.* Based on Lemma 1, if $abs(sigma) >= 2$, all values in $sigma$ must be non-occluded construction calls. There are two cases of $e$. The first case is that $e$ is an expression label. Using Lemma 2 and the fact that $sigma subset.eq r_e$ we can conclude that all values in $sigma$ exist exclusively. The second case is that if $e$ is a variable. We restate the Lemma 3 in its contraposition form, that is if a construction call $f$ is not included in occluded set $o_e$, there is no $f, g in r_e$ such that node $q_f$ is an ancestor to node $q_g$. Since any value in $sigma$ is not occluded and $sigma subset.eq r_e$, each value in $sigma$ is not an ancestor to the others and thus exists exclusively. $qed$
]
