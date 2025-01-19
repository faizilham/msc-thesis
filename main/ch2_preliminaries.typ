#import "../lib/utilities.typ": *
#import "../lib/symbols.typ": *
#import pkg-fletcher as fletcher: diagram, node, edge
#import pkg-curryst: rule, proof-tree

= Preliminaries

In this chapter, we discuss the background knowledge needed and the common mathematical notations we used in this research.

== Data flow analysis with monotone framework

A classical technique for statically analyzing programs is the data-flow analysis #citep(<MollersSPA>, 51) . To define a data-flow analysis, we first start with the control-flow graph (CFG) of the analyzed program and a complete lattice of finite height, representing the abstract information that we want to analyze from the program. For each node in the graph, we define equations (or sometimes inequalities) of the abstract information lattice in relation to the other nodes, usually the predecessor or successor nodes. These equations or inequalities are called transfer functions or constraint functions.

If the transfer functions are monotonic, there is a unique least solution that can be computed by a fix-point algorithm. The combination of a complete lattice and a set of monotonic transfer functions is called the monotone framework, first described by Kam and Ullman (1977) @KamUllmanMonotoneDFA. We shall discuss the main parts of a data-flow analysis, the lattice and monotonic transfer functions, in more detail.

=== Lattice

A lattice $(S, leqsq)$ is the partial order of set $S$ defined by a binary relation $leqsq$, where for each pair of elements $x, y in S$, there is a least upper bound and a greatest lower bound of the set ${x, y}$ #citep(<MollersSPA>, [39]). A complete lattice is a lattice $(S, leqsq)$ in which for any $X subset.eq S$, there is a least upper bound and greatest lower bound of $X$.

The least upper bound of a set $X subset.eq S$, usually denoted by $join.big X$, is an element $y in S$ such that every $x in X$ is $x leqsq y$. On the other hand, the greatest lower bound of a set $X subset.eq S$, denoted by $meet.big X$, is an element $y in S$ such that every $x in X$ is $y leqsq x$. The binary operations $x join y$ (join) and $x meet y$ (meet) are also used for denoting $join.big {x, y}$ and $meet.big {x, y}$ respectively #citep(<MollersSPA>, [39]). In a complete lattice, the least upper bound element and the greatest lower bound element to $S$ itself are usually notated as $top$ (top) and $bot$ (bottom) elements respectively.

In a data-flow analysis, lattices are used to represent abstract states of a program. For example, suppose that we want to analyze whether a floating point number is a real number ($R$), an infinity ($infinity$), a "not a number" value (NaN), or an unknown value. We can represent the sign information with the set #box($F = {bot, R, infinity, "NaN", top}$) and the lattice $(F, leqsq)$, with the binary relation $leqsq$ defined as $bot leqsq x$ and $x leqsq top$ for all $x in F$. We can also illustrate the lattice as a graph shown in @fig:FloatLattice.

#figure(caption: "Floating point number lattice")[
#diagram(
    node-defocus: 0,
		node((0,0), [$top$]),
		node((-1,1), [$R$]),
		node((0,1), [$infinity$]),
		node((1,1), [NaN]),
		node((0,2), [$bot$]),
    {
      edge((0,0), (-1, 1))
      edge((0,0), (0, 1))
      edge((0,0), (1, 1))

      edge((-1, 1), (0,2))
      edge((0, 1), (0,2))
      edge((1, 1), (0,2))
    }
)] <fig:FloatLattice>

=== Transfer functions and monotonicity

The transfer or constraint functions in a data-flow analysis are equations (or inequalities) of the program state lattice, defined for each nodes in the programs' CFG. These equations are defined for the entry point and exit point of the nodes #citep(<NielsonPPA>, 63), which describe the state right before and after the execution of the nodes. We use the notation $evalentry(p)$ and $evalexit(p)$ to denote the equation for the nodes' entry and exit points respectively.

The way the equations are defined reflects the direction of the analysis, which either forward or backward. A forward analysis is an analysis that computes information about past behavior, while a backward one computes future behavior #citep(<MollersSPA>, 72). In forward analysis, the entry equations $evalentry(p)$ are usually defined as a combination of the predecessors' exit equation $evalexit(q)$ for each $q$ a predecessor of $p$, while the exit equations $evalexit(p)$ are defined by the nodes' entry equation $evalentry(p)$. The reverse is true for backward analysis, with the exit equations defined by the successors' entry equation.

When the information flow from the predecessor nodes (or successor nodes in case of backward analysis), the lattice can be combined using either the least upper bound operation $join.big$ or greatest lower bound operation $meet.big$. These way of combining the lattice respectively reflects whether the analysis is a may or a must analysis #citep(<MollersSPA>, 73). A may analysis computes information that may be true, in other words an over-approximation of the real state. A must analysis, meanwhile, computes information that must be true, that is the under-approximation.

In order for the equations to converge, the transfer functions should be monotonic. A monotonic function $f : S_1 -> S_2$, given lattices $S_1$ and $S_2$, is a function that preserves the order of the input, that is for all $x, y: S_1$ if $x leqsq y$, it is also the case that $f(x) leqsq f(y)$  #citep(<MollersSPA>, 44).

=== Reaching definitions analysis

A classical example of a data-flow analysis is the reaching definitions analysis. We use a similar analysis to the reaching definition analysis, and thus we shall discuss the original version.

The reaching definitions analysis computes which variable assignments might define the values of variables at any points in the program #citep(<MollersSPA>, 71). The lattice used in this analysis is the map of variables to the powerset of assignment statements. For example, given the following program:
#listing("Program example for reaching definition analysis")[
  ```
var a, b, c;
a = 1;
b = a + 1;
if (a < 2) {
  a = 2;
} else {
  a = a + 1;
  b = a - 3;
}
c = a - b;
```
]

the program state lattice is the map from variable set ${a, b, c}$ to the powerset of assignment set ${#[`a=1`, `b=a+1`, `a=2`, `a=a+1`, `b=a-3`, `c=a-b`]}$. After the end of the if-else at line 9, we would expect that the program state lattice to be ${a |-> {mono("a=2"), mono("a=a+1")}, b |-> {mono("b=a+1")}, c |-> emptyset}$. The transfer functions equations are then defined by @eq:ReachingDefAnalysis.

$
  &evalentry(mono("start")) &&= {* |-> emptyset}\
  &evalentry(p) &&= join.big_(q in "pred"(p)) evalexit(q)\
  &evalexit(mono(p": x=expr")) &&= (evalentry("p") without { x |-> * }) union { x |-> {mono("x=expr")} }\
  &evalexit(p) &&= evalentry("p")\
$ <eq:ReachingDefAnalysis>


The reaching definition analysis computes information of past assignments that might affect the variable values, and thus it is a forward, may-analysis. At program start, all variables are mapped to empty sets. The entry equations are the least upper bound of the predecessors' state, since it's a forward, may-analysis. When there is an assignment node $p$ in the form of `x=expr`, we replace the mapping of the variable $x$ in the program state to the singleton set of the assignment. Since other type of statements do not change variable values, their equations simply flow the entry points' program state.

== Effect system
An effect is an abstract information about what happened when a part of a program is executed #citep(<NielsonPPA>, 17), such as whether an exception might be raised or which system calls are called by the program. To analyze effects, the type system of a programming language is extended with an effect system, in which annotations are typically added to the function type representing informations related to its internal computation. This is quite different to an annotated type system, since the effect annotation is inherent to the function itself, and not the input or the output of the function #citep(<NielsonPPA>, 323).

We can extend the function type notation $(t_1, .., t_n) -> t_ret$ with the effect annotation $phi$ as #box($(t_1, .., t_n) ->^phi t_ret$), or sometimes written as $(t_1, .., t_n) -> t_ret andef phi$. The definition of the effect annotation depends on what kind of effects we want to analyze, but it usually is a set. For example, in exception analysis, the effect annotation $phi$ is defined as a set of exceptions, while in side-effect analysis the effect annotation can be a set of system calls such as console operations, file handling operations, memory allocations, etc.

Since the effect system is an extension of type system, we may also include polymorphic effect and sub-effecting rules in the typing judgment. @eq:SubeffectingRule shows a typical sub-effecting rule added to the typing judgment. Notice that the sub-effecting is covariant to the function subtyping.

$
  #let th = $hat(tau)$
  #proof-tree(rule($th_1 -> th_2 andef phi <= th'_1 -> th'_2 andef phi'$, $th'_1 <= th_1$, $th_2 <= th'_2$, $phi subset.eq phi'$))
$ <eq:SubeffectingRule>

== The Kotlin programming language

Kotlin is a statistically typed, general-purpose, object-oriented programming language developed by JetBrains #citep(<KotlinSpec2020>, 3). While mainly object-oriented, Kotlin also supports some aspects of the functional programming paradigm such as higher-order functions and lambda literals. We shall delve into some features of the Kotlin language that are connected to this research.

=== Type system

Kotlin type system has various features and properties #citep(<KotlinSpec2020>, 44). A main feature of the type system is null safety, which is achieved by splitting the types into two different lattice universes, nullable and non-nullable. The type system also has a
unified top (`kotlin.Any`) and bottom (`kotlin.Nothing`) types in the lattices, and a proper upper and lower bound operation using the intersection and union types. Both intersection and union types are non-denotable, meaning they can not be used directly in the codes by users and only exist when performing analyses and compiling the code.

Another notable feature of the Kotlin type system is the flow-based type inference, meaning the type of an expression can be inferred based on where it appears in the control flow. For example, when a variable x of type `kotlin.Any` is checked as an integer using a construct such as `if (x is Int)`, the compiler can be sure that x can be statically cast as an integer in the true branch. Otherwise, the control flow would never reach that branch in the first place. This flow-based type inference is performed on control flow graphs.

=== Control flow graph in Kotlin


We first define a model of control flow graph (CFG) that we use in the data flow analysis. This CFG model is a simplified version of the real control flow graph in the Kotlin compiler.

We assume that each expression and sub-expression in the program's AST is labeled with a unique label $e$. @lst:ExprLabel shows an example of expressions labeling, in which the numbers written in superscript letter are the labels for the corresponding expression.
#let cfg(body) = text(font: "Consolas", [[#body]])

#listing("Expression labeling")[
```kotlin
fun test(x: Int, y: Boolean) {
  val a = (2¹ + x²)³

  if ((a⁴ >= 1⁵)⁶) {
    println⁷((a⁸ + 10⁹)¹⁰)¹¹
  }

  val b = if (y¹²) 1¹³ else 0¹⁴
}
```]<lst:ExprLabel>

Given an expression label $e$, the value of the expression is denoted as $lbl(e)$. For example, using the expression labels in @lst:ExprLabel, the value of $lbl(1)$ is equal to 2, and the value of $lbl(3)$ is equal to $(lbl(1) + lbl(2))$, in other words the evaluation result of $(2 + x)$.

The CFG is built from the AST of the program after type checking and identifier resolving steps are finished. Therefore it is safe to assume that there will no out-of-scope variable accesses or incorrect type assignment when analyzing the CFG. The followings are the types of CFG nodes based on what AST constructs they represent.

+ Function start node #cfg[start] and exit node #cfg[exit]. These nodes appear only once at the start and the end of a function body.
+ Literal constant #cfg("$e = <Lit>"), representing constant values such as number or null value.
+ Identifier access #cfg("$e = x"), representing accesses to variable or other named references.
+ Variable declaration #cfg("var x (:= $e)") or #cfg("val x (:= $e)"). These nodes are variable declaration nodes with an optional initializer expression. In Kotlin a variable can be declared as mutable with `var` or immutable with `val`. For the ease of formalization, we assume a variable is always mutable. This is safe to do  because if an analysis can handle mutable variables, it is also able to handle immutable variables. \ A variable can only be declared once and must be declared before any assignment. This means that for a variable `x`, there is only one variable declaration node of `x` per program path and there are no assignment node to `x` appearing before the declaration.
+ Variable assignment #cfg("x := $e"), representing an assignment of the value of expression `e` to a variable `x`. As we mentioned earlier, a variable assignment node must be preceded, directly or indirectly, by a variable declaration node of the same variable.
+ When begin #cfg("when_begin($cond)") and end #cfg("when_end"), representing branching statements such as if-else and loops. The `when_begin` node always have two successor nodes, representing the paths if the condition is true or false. In case of a loop, the `when_end` node's next edge points back to the beginning of the conditional expression's node.
+ Function call #cfg([\$e = \$f(\$arg#sub("1"), ..., \$arg#sub("n"))]), representing a call to the function `f`. Notice that `f` is an expression label instead of direct a function identifier. In case of a member an extension function call `x.f()`, we assume that it is transformed to `f(x)` for the ease of formalization.
+ Return statement #cfg("return ($e)"), representing a return statement with an optional expression `e`.
+ Lambda expression #cfg("$e = "+ $lambda$ +".{subgraph}"), representing a lambda expression. The lambda expression has a subgraph, representing the CFG of the lambda function's body.

@fig:CFGTransformExample shows an example of how parts of the program in @lst:ExprLabel are transformed to control flow graph. The CFG part in (a) represents the declaration `val a = 2 + x`, while  the one in (b) represents the declaration `val b = if (y) 1 else 0`.

#[
  #let d = 0.7
  #let hd = 0.4
  #figure(caption: [Parts of control flow graph of the program in @lst:ExprLabel], kind: image)[
  #grid(
    columns: (50%, 50%),
    rows: (auto, auto),
    row-gutter:2em,
    align: center,
    [
      #v(1.5em)
      #diagram(
        node-inset: 3pt,
        node((0, d), cfg("$1 = 2")),
        node((0, 2*d), cfg("$2 = x")),
        node((0, 3*d), cfg("$3 = $1 + $2")),
        node((0, 4*d), cfg("val a = $3")),
        {
          let lineTo(p1, p2) = edge(p1, p2, "-|>")
          lineTo((0,d), (0, 2*d))
          lineTo((0,2*d), (0, 3*d))
          lineTo((0,3*d), (0, 4*d))
        }
      )
    ],
    [
      #diagram(
        node-defocus: 0,
        node-inset: 3pt,
        node((0, d), cfg("$12 = y")),
        node((0, 2*d), cfg("when_begin($12)")),
        node((-hd, 3*d), cfg("$13 = 1")),
        node((hd, 3*d), cfg("$14 = 0")),
        node((-hd, 4*d), cfg("val b = $13")),
        node((hd, 4*d), cfg("val b = $14")),
        node((0, 5*d), cfg("when_end")),
        {
          let lineTo(p1, p2, ..args) = edge(p1, p2, "-|>", ..args)
          lineTo((0,d), (0, 2*d))
          lineTo((0,2*d), (-hd, 3*d), label: [*T*], label-size: 9pt, label-pos: 0.6, label-anchor: "center", label-sep: 6pt)
          lineTo((0,2*d), (hd, 3*d), label: [*F*], label-size: 9pt, label-pos: 0.6, label-anchor: "center", label-sep: 6pt)
          lineTo((-hd, 3*d),(-hd, 4*d))
          lineTo((hd, 3*d),(hd, 4*d))

          lineTo((-hd, 4*d),(0, 5*d))
          lineTo((hd, 4*d),(0, 5*d))
        }
      )
    ],
    [(a) Declaration of `a` at line 2],
    [(b) Declaration of `b` at line 8]
    )] <fig:CFGTransformExample>
]


=== Annotation

Annotation is a feature in Kotlin for attaching metadata to various entities in a program, such as class declaration, function declaration, and function parameter #citep(<KotlinSpec2020>, 281). An annotation class may receive values of types integers, enumerations, strings, other annotation types, and arrays of the previously mentioned types. Each annotation class has a retention level indicating its lifetime, which can be source-only, retained in compiled binary, or accessible during runtime. Annotation can be declared in-program by users using annotation class syntax. @lst:KotlinAnnotation shows an example of a user-defined annotation and its usage.

#listing("Annotation usage in Kotlin")[
```kt
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION,
    AnnotationTarget.TYPE_PARAMETER, AnnotationTarget.VALUE_PARAMETER,
    AnnotationTarget.EXPRESSION, AnnotationTarget.TYPE)
@Retention(AnnotationRetention.SOURCE)
annotation class Ann(val message: String = "")

@Ann class Foo {
    @Ann fun bar(@Ann("test") baz: @Ann Int): @Ann Int {
        return (@Ann("zero") 0)
    }
}
```] <lst:KotlinAnnotation>

Annotation can be used as a simple way to extend Kotlin without changing too much of the syntax. For example, if we want to add an effect system to the function type, we can use annotations in the function signature to represent the effects.

== Common notations and definitions

In this section, we define some common notations and definitions that we used in this research.

A mapping $s: X -> Y$ is a set of mapping pairs $(x |-> y)$, in which for all $x in X$, there is a $y in Y$ such that $s(x) = y$. The notation $s[x |-> y]$ denotes the replacement of $x$ mapping in $s$ to $y$, such that $s[x |-> y]$ equals to s but with $(x |-> *) in s$ replaced with $(x |-> y)$.

$
  &s[x |-> y] &&= (s without {x |-> *}) union {x |-> y} \
  &s[x_1 |-> y_1, x_2 |-> y_2]& &= (s[x_1 |-> y_1])[x_2 |-> y_2] \
  &s[x |-> y | phi(x) ] &&= cases(
    s[x |-> y] & "for all" x "that satisfy predicate "phi(x),
    s         & "otherwise"
  )
$

A map lattice $"MapLat"(X -> Y)$ is a lattice $(X -> Y, attach(leqsq, br: Y))$, which is the mapping from set $X$ to lattice $(Y, attach(leqsq, br: Y))$, and its ordering ($leqsq$) is equivalent to the ordering of lattice $Y$ ($attach(leqsq, br: Y)$). This means that given the map lattices $m_1, m_2 : X -> Y$, the property $m_1 leqsq m_2$ holds if and only if $y_1 attach(leqsq, br: Y) y_2$ for all $a in X$, $(a |-> y_1) in m_1$ and $(a |-> y_2) in m_2$.

A powerset lattice $(powerset(A), subset.eq)$ is a lattice of the powerset of $A$, with the partial order relation $leqsq$ defined as the  subset or equal relation ($subset.eq$). The top element ($top$) for a powerset lattice is the set $A$, while the bottom element ($bot$) is the empty set. For example, the powerset lattice $(powerset({a, b, c}), subset.eq)$ can be illustrated as @fig:PowsetLattice.

#figure(caption: "Example of a powerset lattice")[
#diagram(
    node-defocus: -1,
		node((0,0), [${a, b, c}$]),
		node((-1,1), [${a, b}$]),
		node((0,1), [${a, c}$]),
		node((1,1), [${b, c}$]),
    node((-1,2), [${a}$]),
		node((0,2), [${b}$]),
		node((1,2), [${c}$]),
		node((0,3), [$emptyset$]),
    {
      edge((0,0), (-1, 1))
      edge((0,0), (0, 1))
      edge((0,0), (1, 1))

      edge((-1, 1), (-1, 2))
      edge((-1, 1), (0, 2))

      edge((0, 1), (-1, 2))
      edge((0, 1), (1, 2))

      edge((1, 1), (0, 2))
      edge((1, 1), (1, 2))


      edge((-1, 2), (0,3))
      edge((0, 2), (0,3))
      edge((1, 2), (0,3))
    }
)] <fig:PowsetLattice>

A flat lattice $"FlatLat"(A)$ is a lattice $(A union {bot, top}, leqsq)$, with the partial ordering defined as $bot leqsq a leqsq top$, for all $a in A$. @fig:FlatLattice illustrates the flat lattice of set ${a, b, c}$.

#figure(caption: "Example of a flat lattice")[
#diagram(
    node-defocus: 0,
    node-inset: 5pt,
		node((0,0), [$top$]),
		node((-1,1), [$a$]),
		node((0,1), [$b$]),
		node((1,1), [$c$]),
		node((0,2), [$bot$]),
    {
      edge((0,0), (-1, 1))
      edge((0,0), (0, 1))
      edge((0,0), (1, 1))

      edge((-1, 1), (0,2))
      edge((0, 1), (0,2))
      edge((1, 1), (0,2))
    }
)] <fig:FlatLattice>

A linearly ordered lattice $"OrderLat"(angles(bot = a_1, ..., a_n = top)) $ is a lattice of set ${a_1, ..., a_n}$ with the ordering defined as $a_i leqsq a_j$ iff. $i <= j$

The transfer functions, or constraint functions, equations in a data-flow analysis are denoted with the notation $evalentry(p)$ and $evalexit(p)$, which respectively represents the program state equation at the entry point of a node $p$ and the exit point of $p$. We use the notation $evalbracket(p":" mono("<pattern>"))$ to indicate that the node $p$ matches with the CFG node `<pattern>`. For example, the notation $evalexit(mono(p : "return" lbl(e)))$ denotes the equation for a return statement node $p$.
