#import "../lib/utilities.typ":*

= Introduction

Programmers sometimes ignore the return value of a function call when writing a piece of code. While sometimes this might be a deliberate choice, it is often an oversight that can lead to bugs. In most cases, using a value means passing it as an argument to a function or using it as a return value of the enclosing function. However, for some types of values, it is more useful to define its usage as passing the value to a certain set of functions, and not necessarily any functions. We call this kind of usage a utilization, and the types of values are utilizable types.

For example, asynchronous calls in Kotlin are represented by the `Deferred` type. In most cases, `Deferred` values should be eventually awaited using the `.await()` method or canceled using the `cancel()` method. Otherwise, it is potentially a source of bug that should be warned to users. Therefore, we may define that a `Deferred` value is utilized if the methods `await` or `cancel` are called upon it. @lst:UtilOfDeferred shows an example of tracking the utilization of `Deferred` values. The `Deferred` value in the variable `three` is not fully utilized since there is an execution branch where it is never awaited or canceled, and thus the compiler or static analysis tool should warn users about it.

#listing([Utilization of `Deferred`-type values])[
```kt
suspend fun sums(): Int = coroutineScope {
    val one = async { 1 }    // no warning
    val two = async { 2 }    // no warning
    val three = async { 3 }  // warning, incomplete utilization
    var sum = one.await()

    if (sum > 1) {
        sum += two.await() + three.await()
    } else {
        two.cancel() // we forget to cancel or await "three" here
    }

    sum
}

fun asyncFour(scope: CoroutineScope) : Deferred<Int> {
    val four = scope.async { 4 } // no warning because it is returned
    return four
}
```] <lst:UtilOfDeferred>

Another type in Kotlin that benefits from this definition of usage is the `Sequence` type, which represents lazy computations over collections of values, such as list or set. The `Sequence` type is commonly in Kotlin programs for efficiently chaining collection computations, such as maps and filters, and executing it all at once. However, sometimes users forget to collect the result of the sequence, and as a result the computations are never executed. A `Sequence` value is utilized if its computations are eventually executed and collected as a new collection, for example using the `toList` function.

In this research, we extend the Kotlin compiler with a static analysis method for tracking utilization. The main contributions of our research are:

+ A formal definition of a static analysis method for tracking utilization of values.
+ A prototype implementation of the static analysis as a Kotlin compiler plugin.

Since we focus on the Kotlin language, there are a few constraints that shall be fulfilled by the analysis method. First, the analysis is based on the intra-procedural data-flow analysis since it is the main technique used in the Kotlin compiler framework. This also means that we would require some information embedded at the function signature level to allow analyzing function calls and interactions without requiring inter-procedural analysis techniques.

As for the second constraint, we shall use existing features of Kotlin, such as annotations, instead of developing new syntax. This is because we want the analysis to be compatible with common Kotlin programs as much as possible. Lastly, if some annotations are required on the function signatures, we want the analysis to be able to infer the annotations as much as possible, especially in the case of lambda functions. This is because a lot of Kotlin programs extensively use lambda functions, and it would be unwieldy if each of those lambda functions require annotations.
