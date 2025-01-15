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

/*
== Basic intuitions and desirable properties

We first describe the basic intuitions about the problem and the properties we desire from the analysis. In most cases, the return values of function calls should be used in an expression or assigned to a variable. We shall call these functions having a must-use obligation. This is the default usage obligation because ignoring the return value is usually a mistake. A major exception to the must-use obligation is if the returned value is a unit-type value, as it is cumbersome if the compiler requires users to use unit values.

Another exception is when ignoring the return value of certain functions is usually safe. For example, the function `MutableSet.add` in the standard library returns a Boolean value indicating whether the element is added to the set if it does not exist previously. In most cases, this Boolean value is safe to ignore. If the compiler keeps warning about this, it will only frustrate users, resulting in users disregarding future warnings and missing other more important unused value warnings. Therefore, there has to be a way to indicate that the return values of certain functions are safe to discard. We shall call these functions as discardable or having a may-use obligation.


One potential way to mark such discardable functions is by using Kotlin's annotation #cite(<KotlinSpec2020>) feature. \Cref{lst:1_basic} shows an example of how the analysis would potentially look like. In this example, the return value of `ignored` can be safely discarded since it has the `Discardable` annotation.

/*
\begin{listing}[H]
    \caption{Basic unused value analysis}
    \label{lst:1_basic}
    \begin{kotlin}
        fun normal() : Int = 1
        \@Discardable fun ignored() : Int = 1

        val x = normal() // no warning
        print(x)         // no warning because it returns Unit type
        ignored()        // no warning because of @Discardable annotation
        normal()         // triggers warning
    \end{kotlin}
\end{listing}
*/


=== Propagation through higher-order functions

Many Kotlin code bases extensively use lambda functions since it is the idiomatic style in Kotlin. This is especially true because of the scope functions provided in Kotlin's standard library, in which a lambda function is executed within the context or scope of an object. Some scope functions, such as `run` and `with`, also return the resulting value of the lambda function. It would be useful if the analysis could propagate the usage obligation of the resulting values to the scope functions or other higher-order functions.

\Cref{lst:1_lambda} shows the example of the analysis with higher-order functions. This example is similar to the previous one shown in \Cref{lst:1_basic}, but each function is called indirectly using `run` scope function. The analysis gives the same warning as the previous one due to usage obligation propagation.

// \begin{listing}[H]
//     \caption{Unused value analysis with higher-order function}
//     \label{lst:1_lambda}
//     \begin{kotlin}
//         inline fun <R> run(block: () -> R): R  // scope function from the standard library

//         fun normal() : Int = 1
//         \@Discardable fun ignored() : Int = 1

//         val x = run { normal() } // no warning
//         run { print(x) }         // no warning because of unit type
//         run { ignored() }        // no warning because @Discardable is propagated
//         run { normal() }         // triggers warning
//     \end{kotlin}
// \end{listing}


=== Notion of usage and utilizable types

For most types, using a value means assigning it to a variable, passing it to a function, or calling a method upon it. However, for certain types, it is more useful to define when precisely a value is used. For example, a `Deferred` value in Kotlin represents an asynchronous non-blocking computation, with `.await()` method to wait for it to finish and `.cancel()` method to cancel it.  While we can certainly handle it with the usual notion of usage, it is more useful to argue that a `Deferred` should be considered unused until we call `.await()` or `.cancel()` at least once. This way the analysis may guarantee to a certain degree that any asynchronous computation will eventually be awaited or canceled. Other types in Kotlin that may benefit from a more precise usage definition are `Sequence` and `Flow`.
/*
\begin{listing}[H]
    \caption{Unused value analysis with utilizable type Deferred}
    \label{lst:1_utilize}
    \begin{kotlin}
        suspend fun sums(): Int = coroutineScope {
            val one = async { 1 }    // no warning
            val two = async { 2 }    // no warning
            val three = async { 3 }  // warning, incomplete utilization
            var sum = one.await()

            if (sum > 1) {
                sum += two.await() + three.await()
            } else {
                two.cancel()
                // we forget to cancel or await three here
            }

            sum
        }

        fun asyncFour(scope: CoroutineScope) : Deferred<Int> {
            val four = scope.async { 4 } // no warning because it escapes the function
            return four
        }
    \end{kotlin}
\end{listing}
*/

We shall call these types of values the utilizable types, and the associated set of functions that use them the utilizer functions. A utilizable value is considered to be used if and only if it is passed to any of the utilizer functions at least once. Otherwise, it remains unutilized. The analysis should then warn about any non-escaping unutilized values. \Cref{lst:1_utilize} illustrates an example with Deferred type. In function `sums`, the analysis warns about incomplete utilization of variable `three` because there is a path in which it is not utilized and not escaping, that is through the else branch. In contrast, while we never directly utilize the value of variable `four` in function `asyncFour`, the analysis should not produce any warning because the value escapes the function.


== Research challenges

A few challenges arise due to the design and desired properties of the analysis. We currently have identified three main challenges that should be addressed in our research: propagation rules, alias tracking, and adoption into Kotlin.

=== Usage obligation propagation rules

While the basic intuition for the usage obligation propagation is quite straightforward in the case of simple higher-order functions like `run`, it is still unclear how exactly the propagation would work with other control flow structures.

Consider the example illustrated in \cref{lst:1_propagation_rule}.
Based only on our simplistic intuition, it is unclear which of the four `run` calls may trigger the warning. For calls 1 and 2, it can be argued that the analysis should produce a warning for the first call but not the second one. For calls 3 and 4 that use functions `singleIgnored` and `doubleIgnored`, however, several design choices can be made. The first choice is to always propagate may-use obligations even if the functions are not annotated with `Discardable`. The second choice is to not automatically propagate it in named functions, but the analysis will produce warnings to remind users to add `Discardable` annotations if all execution paths of the functions produce discardable values. Another choice is to only propagate in specially annotated functions, that is to update the `run` function in the standard library with a new special annotation. Design choices like these have advantages and disadvantages that will be explored in our research.

/*
\begin{listing}[H]
    \caption{A more complex propagation case}
    \label{lst:1_propagation_rule}
    \begin{kotlin}
        fun normal() : Int = 1
        \@Discardable fun ignored() : Int = 1
        \@Discardable fun ignored2() : Int = 2

        fun singeIgnored() : Int = ignored()
        fun doubleIgnored(b : Boolean): Int = if (b) ignored() else ignored2()

        fun testPropagate(b: Boolean) {
            run { if (b) normal() else ignored() }    // 1
            run { if (b) ignored() else ignored2() }  // 2
            run { singeIgnored() }                    // 3
            run { doubleIgnored(b) }                  // 4
        }
    \end{kotlin}
\end{listing}
*/

=== Alias tracking

Alias tracking is the second challenge that we need to address in our research, especially in the case of utilizable types. Alias tracking is an analysis technique for determining which variables or references refer to the same object. Consider a basic aliasing problem shown in \Cref{lst:1_aliasing_basic}. In this example, variables `two` and `three` refer to the same Deferred object. Because all Deferred objects in function `sums` are awaited, the analysis should produce no warning.

/*
\begin{listing}[H]
    \caption{A basic aliasing problem}
    \label{lst:1_aliasing_basic}
    \begin{kotlin}
        suspend fun sums(): Int = coroutineScope {
            val one = async { id(1) }
            val two = async { id(2) }

            val three = two  // three is alias to two

            one.await() + three.await() // ideally no warning at all
        }
    \end{kotlin}
\end{listing}
*/

A more complex aliasing problem example is illustrated in \Cref{lst:1_aliasing_complex}. In this example, the aliasing happens when Deferred objects are passed as arguments to other functions. In an ideal, exact analysis no warning should be produced, because the variables `one` and `two` are eventually awaited. However, this might be unrealistic or too complex to achieve without a more sophisticated system such as borrowing. Therefore, some levels of under or overapproximations are expected.

/*
\begin{listing}[H]
    \caption{A complex aliasing problem}
    \label{lst:1_aliasing_complex}
    \begin{kotlin}
        fun <T> addFinishLog(deferred: Deferred<T>) {
            deferred.invokeOnCompletion { print("finished!") }
        }

        suspend fun <T> awaitAndLog(deferred: Deferred<T>) : T {
            val result = deferred.await()
            println("finished!")
            return result
        }

        suspend fun sums2() : Int = coroutineScope {
            val one = async { 1 }
            val two = async { 2 }

            addFinishLog(one)
            one.await() + awaitAndLog(two) // ideally no warning at all
        }
    \end{kotlin}
\end{listing}
*/

Other cases of aliasing problems we might encounter in our research are when the utilizable values are assigned to an object property or a collection data structure like `List`. Since aliasing analysis is an extensive topic, we shall limit alias handling in this research to only a small set of cases and focus on ensuring that the analysis is flexible enough to be extended with a separate alias tracking analysis.

=== Adoption into Kotlin

The last challenge that should be considered in our research is adopting and implementing the analysis into the Kotlin compiler. The Kotlin compiler is a complex program with millions of developers as its users. While unused value analysis can be quite an important tool for detecting possible bugs, it should also be conservative in producing warnings. Too many false positive warnings can hinder the users' productivity and trust in the tools. While we still attempt to reduce false negatives, in our particular case it is less important than false positives. Our research should also look into patterns that the users employ in their codes so that we may understand which cases are more important to handle in the analysis.

The analysis implementation should also use the existing Kotlin compiler framework and infrastructures and does not require tremendous changes to the Kotlin compiler and the language specification. This means that a less accurate implementation with small changes should be prioritized instead of an accurate implementation with drastic changes.


== Research questions

Based on the challenges we have identified, we formulate three research questions.

    + How does the unused return value analysis be defined, especially concerning usage obligation propagation rules and alias tracking?
    + How does the unused return value analysis be implemented in the existing Kotlin compiler infrastructure?
    + How accurate is the unused return value analysis in terms of false positives and negatives when applied to existing Kotlin code bases?


*
*/
