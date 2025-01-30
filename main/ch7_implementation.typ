#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Implementation in Kotlin

In this chapter, we discuss our implementation of the utilization analysis in Kotlin. We implement#footnote([source code in https://github.com/faizilham/kotlin-retval-analysis/]) the analysis as a compiler plugin, using the work of Novozhilov (2024) @DemiurgKotlinPlugin as a base template for connecting the plugin to the compiler. While in theory implementing the analysis should be relatively straightforward, in practice our model of the control flow graph is not identical to the control flow graph implementation in the Kotlin compiler.

// Overall architecture?

== Annotating utilizable types, utilization status, and effects

We use the annotation class feature for annotating utilization status and effects in the function signature. A type is declared as utilizable by annotating it with a `@MustUtilize` annotation. Utilization status is annotated with `@Util(u)` annotation, which shall be placed at parameters, return type, or the function itself to annotate the utilization of the function's context object. Utilization effects are annotated with `@Eff(e)`, which shall be placed at the affected parameters or the function itself in the case of the context object's effect. @lst:AnnoFileType shows the example of annotation for File type and its methods.

#listing("Annotation for File class")[
```kt
@MustUtilize
class MyFile private constructor () {
  companion object {
    // open : (String) -> <0> File
    fun open(path: String) : @Util("0") MyFile { ... }
  }

  // read : (<0>File).() -> String
  @Util("0") fun read() : String { ... }

  // write : (<0>File).(String) -> Unit
  @Util("0") fun write(text: String) { ... }

  // close : (<0>File).() -> Unit & {This: U}
  @Eff("U") @Util("0") fun close() { ... }
}
```] <lst:AnnoFileType>


Collection types, or any generic type that should be covariant to its parameter in regards to utilization, are annotated with `@UtilizeLike` at the type parameter positions, as shown in @lst:CollectionTypeAnno. This means that for `C<A>` an instantiation of a generic type `C<T>`, which has annotation `@UtilizeLike` at the parameter `T`, `C<A>` is also a utilizable type if and only if `A` is also a utilizable type.

#listing("Annotation for collection type")[
```kt
class MyList<@UtilizeLike T> constructor() {
  ...
}
```] <lst:CollectionTypeAnno>

For more complex effects, we annotate the function and its higher-order function type parameters with the `@Effects([...])` annotation for listing the effects, and `UE(target, eff)` for the effect to each target, which are parameters (the parameter's index starting from 0), context objects (-1) and parametric free variable (-2). For example, the `let` scope function in @eq:LetScopeFunc is annotated as shown in @lst:LetAnno.

$
"let" : A.((A) -> B) -> B \
"let" : ann(u_a)A.((ann(u_a) A) -> ann(u_b)B andef {1 |-> e} union phi ) -> ann(u_b) B andef {"This" |-> e} union phi
$ <eq:LetScopeFunc>
\

#listing("Annotation for let function")[
```kt
val THIS = -1; val FV = -2

fun<A, B> (A).let(f: (A) -> B): B { // without annotation
  return f(this)
}

@Effects([UE(THIS, "e"), UE(FV, "φ")]) // with annotation
fun<A, B> (@Util("ua") A).let(
  f: @Effects([UE(0, "e"), UE(FV, "φ")]) (@Util("ua") A) -> @Util("ub") B
): @Util("ub") B {
  return f(this)
}
```] <lst:LetAnno>
/*
// with annotation
@Effects([UE(THIS, "e"), UE(FV, "φ")])
fun<A, B> (@Util("ua") A).let1(
  @Effects([UE(0, "e"), UE(FV, "φ")]) f: (@Util("ua") A) -> @Util("ub") B
): @Util("ub") B {
  return f(this)
}*/

#pagebreak()

== Lattice data structure

While in Chapter 6 we extend the utilization lattice to include utilization variables $omega$, in practice the utilization variables are currently only useful for inferencing the parameters' initial utilization. In the inference case, each parameter is always assigned a unique utilization variable. Rather than using a set object to represent the lattice, we model the utilization lattice as an enumeration of `Bot` ($bot$), `UT` ($UT$), `NU` ($NU$), and `Top` ($top$), as shown in @lst:UtilLatClass. Parameters are assigned with a bottom value at the start node, and the implementation simply tracks the latest known utilization variable value for each function parameter. This is because it is much more efficient to represent the lattice value as a plain enumeration than a set object.


#listing([Utilization lattice class and the $leqsq$ implementation])[
```kt
sealed class UtilLattice(private val value: Int): Lattice<UtilLattice> {
  data object Top: UtilLattice(2)
  data object NU: UtilLattice(1)
  data object UT: UtilLattice(1)
  data object Bot: UtilLattice(0)

  fun leq(other: UtilLattice) = value < other.value || this == other
}
```] <lst:UtilLatClass>

Another common lattice we use in the analysis is the map lattice. We extend the built-in `Map<K,V>` data structure in Kotlin as `DefaultMapLat<K,V>` class, in which any key of type `K` not found in the map lattice is presumed to have a default lattice value, usually either a $bot$ or $top$. This is useful since we do not have to initialize the lattice at the start node, especially in the case of free variables. If we instead must initialize free variable mappings in the lattice, we have to traverse the CFG at least once to collect all the free variables _before_ the analysis can start. By setting a default lattice value, we minimize unnecessary CFG traversals.

== Handling context object and invoke function

A context object or a receiver is the object `x` in the calling syntax `x.f()`, where `f` is a class method or an extension function to `x`. In our model for analysis, calling `x.f()` is identical to calling `f(x)`. We chose to simplify this in the analysis since in principle a context object is similar to a parameter. However, this is not how it is implemented in the Kotlin compiler. In the case of calling `x.f()`, the function `f` has the type #box($X.() ->Y$), while in the other case, the function has the type #box($(X) ->Y$). To reflect this, we separate the effect and utilization annotation for parameters and the context object into different fields in our data structure.

A common case when a context object matters is when a function is assigned to a variable, and then later called. Kotlin has a special primitive called `invoke` for calling a function variable. Consider the example in @lst:ExtensionInvoke.

#listing("Calling extension function through invoke")[
```kt
fun X.f(i: Int) { ... }

val g = X::f
val x : X = ...
x.g(1)             // identical to g.invoke(x, 1) in CFG
```] <lst:ExtensionInvoke>

In the example, we assigned the extension function `f` to variable `g`, and then called `x.g()`. When the compiler transforms the AST to a CFG, the call `x.g()` is translated to `g.invoke(x)`. This means that the context object `x` should be treated as a parameter, and thus the analysis changes the signature data type of `g` by moving the effect and utilization annotation of the context object into the first parameter, and shifting the other parameter indexes by one.
