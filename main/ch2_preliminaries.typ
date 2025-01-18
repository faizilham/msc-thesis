#import "../lib/utilities.typ": *
#import "../lib/symbols.typ": *
#import "@preview/fletcher:0.5.4" as fletcher: diagram, node, edge

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
    node-inset: 5pt,
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

=== Reachable definitions analysis

== Types and effects system
TODO: types and effect system from @NielsonPPA


== The Kotlin programming language

Kotlin is a statistically typed, general-purpose, object-oriented programming language developed by JetBrains #citep(<KotlinSpec2020>, 3). While mainly object-oriented, Kotlin also supports some aspects of the functional programming paradigm such as higher-order functions and lambda literals. We shall delve into some features of the Kotlin language that are connected to this research.

=== Type system

Kotlin type system has various features and properties #citep(<KotlinSpec2020>, 44). A main feature of the type system is null safety, which is achieved by splitting the types into two different lattice universes, nullable and non-nullable. The type system also has a
unified top (`kotlin.Any`) and bottom (`kotlin.Nothing`) types in the lattices, and a proper upper and lower bound operation using the intersection and union types. Both intersection and union types are non-denotable, meaning they can not be used directly in the codes by users and only exist when performing analyses and compiling the code.

Another notable feature of the Kotlin type system is the flow-based type inference, meaning the type of an expression can be inferred based on where it appears in the control flow. For example, when a variable x of type `kotlin.Any` is checked as an integer using a construct such as `if (x is Int)`, the compiler can be sure that x can be statically cast as an integer in the true branch. Otherwise, the control flow would never reach that branch in the first place. This flow-based type inference is performed on control flow graphs.

=== Control flow graph in Kotlin


We first define a model of control flow graph (CFG) that we use in the data flow analysis. This CFG model is a simplified version of the real control flow graph in the Kotlin compiler.

We assume that each expression and sub-expression in the program's AST is labeled with a unique label $e$. @lst:ExprLabel shows an example of expressions labeling, in which the numbers written in superscript letter are the labels for the corresponding expression.

// ¹²³⁴⁵⁶⁷⁸⁹⁰
#listing("Expression labeling")[
```kotlin
fun test(x: Int, y: Boolean) {
  val a = (2¹ + x²)³

  if ((a⁴ >= 1⁵)⁶) {
    println⁷((a⁸ + 10⁹)¹⁰)¹¹
  }

  val b = (if (y¹²) 1¹³ else 0¹⁴)¹⁵
}
```]<lst:ExprLabel>


#let cfg(body) = text(font: "Consolas", [[#body]])

Given an expression label $e$, the value of the expression is denoted as $lbl(e)$. For example, using the expression labels in @lst:ExprLabel, the value of $lbl(1)$ is equal to 2, and the value of $lbl(3)$ is equal to $(lbl(1) + lbl(2))$, in other words the evaluation result of $(2 + x)$.

TODO: nodes explanation and transformation examples

important explanations:
- variable declaration can only be once per path & variable, i.e. no ancestor declaration / assignment
- assignment always have at least 1 declaration ancestor
- etc

All AST constructs are transformed into the following CFG nodes.
+ Function start #cfg[start] and exit #cfg[exit]
+ Literal constant. #cfg("$e = <Lit>")
+ Identifier access. #cfg("$e = x")
+ Variable declaration. #cfg("var x")
+ Variable assignment. #cfg("x := $val")
+ When begin #cfg("when_begin($cond)") and end #cfg("when_end")
+ Function call #cfg([\$e = \$f(\$arg#sub("1"), ... ,\$arg#sub("n"))])
+ Return statement. #cfg("return $val")
+ Lambda expression #cfg("$e = "+ $lambda$ +".{subgraph}")


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

Annotation can be used as a simple way to extend Kotlin without changing too much of the syntax. In this research, for example, we can use annotation to mark usage obligations.


== Common notations and definitions

We shall define some common notations and definitions that we used in this document.

Given $s$ a mapping of $X -> Y$, $s[x |-> y]$ equals to s but with $(x |-> *) in s$ replaced with $(x |-> y)$. Formally:

$
  &s[x |-> y] &&= (s without {x |-> *}) union {x |-> y} \
  &s[x_1 |-> y_1, x_2 |-> y_2]& &= (s[x_1 |-> y_1])[x_2 |-> y_2] \
  &s[x |-> y | phi(x) ] &&= cases(
    s[x |-> y] & "for all" x "that satisfy predicate "phi(x),
    s         & "otherwise"
  )
$

A map lattice $"MapLat"(A -> L)$ is a lattice of the mapping from set A to lattice L, and its ordering is equivalent to the ordering of lattice L.

$
  M = "MapLat"(A -> L) = (A -> L, attach(leqsq, br: L))\
  "where, for all" m_1, m_2 in powerset(M), "this property holds":\
  m_1 leqsq m_2 equiv forall a in A . m_1(a) attach(leqsq, br: L) m_2(a)
$

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

The transfer functions, or constraint functions, equations in a data-flow analysis are denoted with the notation $evalentry(p)$ and $evalexit(p)$, which respectively represents the program state equation at the entry point of a node $p$ and the exit point of $p$. We use the notation $evalbracket(p":" mono("<pattern>"))$ to indicate that the node $p$ matches with the CFG node `<pattern>`. For example, the notation $evalexit(mono(p : "return" lbl(e))) = ...$ denotes the equation for a return statement node $p$.
