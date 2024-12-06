#import "../lib/utilities.typ": *
#import "../lib/symbols.typ": *

= Preliminaries

TODO: modify

In this chapter, we discuss the background knowledge needed for the research and review research literature related to the unused return value analysis problem.

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


Annotation is a feature in Kotlin for attaching metadata to various entities in a program, such as class declaration, function declaration, and function parameter #citep(<KotlinSpec2020>, 281). An annotation class may receive values of types integers, enumerations, strings, other annotation types, and arrays of the previously mentioned types. Each annotation class has a retention level indicating its lifetime, which can be source-only, retained in compiled binary, or accessible during runtime. Annotation can be declared in-program by users using annotation class syntax. \Cref{lst:2_annotation} shows an example of a user-defined annotation and its usage.

/*
\begin{listing}[h!]
    \caption{Annotation usage in Kotlin}
    \label{lst:2_annotation}
    \begin{kotlin}
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
    \end{kotlin}
\end{listing}
*/

Annotation can be used as a simple way to extend Kotlin without changing too much of the syntax. In this research, for example, we can use annotation to mark usage obligations.

== Data flow analysis with monotonic framework

TODO:

- lattice
- DFA
- monotone fixpoint

== Common notations and definitions

TODO: notation definitions

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

A powerset lattice $(powerset(A), subset.eq)$ is a lattice of the powerset of $A$, with subset or equal ($subset.eq$) as the ordering operator.

A flat lattice $"FlatLat"(A)$ is a lattice of set $A union {bot, top}$, with the ordering defined as $bot leqsq a leqsq top$, for all $a in A$.

A linearly ordered lattice $"OrderLat"(angles(bot = a_1, ..., a_n = top)) $ is a lattice of set ${a_1, ..., a_n}$ with the ordering defined as $a_i leqsq a_j$ iff. $i <= j$
