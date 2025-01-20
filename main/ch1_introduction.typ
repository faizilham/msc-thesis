#import "../lib/utilities.typ":*

= Introduction

Programmers sometimes ignore the return value of a function call when writing a piece of code. While sometimes this might be a deliberate choice, it is often an oversight that can lead to bugs. In most cases, using a value means passing it as an argument to a function or as a return value of the enclosing function. However, for some types of values, it is more useful to define its usage as passing the value to a certain set of functions, and not necessarily any functions. We call this kind of usage a utilization, and the types of values are utilizable types.

For example, the `Deferred` type in Kotlin represents asynchronous calls, which can be awaited using the `.await()` method, suspending the computation until the call is finished, or cancelled by using the `.cancel()` method.
In most cases, `Deferred` values should be eventually awaited or canceled. Otherwise, it is potentially a source of bug that should be warned to users. Therefore, the `Deferred` type is a utilizable type, which must be utilized by the methods `await` or `cancel`, or any user-defined functions that call those methods upon its `Deferred` parameters.

@lst:UtilOfDeferred shows an example of tracking the utilization of `Deferred` values.  The `Deferred` values in the variable `one` and `two` are always awaited or canceled, thus no warning is produced. However, the `Deferred` value in the variable `three` is not fully utilized since there is an execution branch where it is never awaited or canceled, thus a warning should be given about it.

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
```] <lst:UtilOfDeferred>

Another example in Kotlin is the `Sequence` type, which represents lazy computations over collections of values, such as list or set. The `Sequence` type is commonly used in Kotlin programs for efficiently chaining collection computations, such as maps and filters, and executing it all at once. However, sometimes users forget to collect the result of the sequence, and as a result the computations are never executed. A `Sequence` value is utilized if its computations are eventually executed and collected as a new collection, for example using the `toList` function.

Using the utilization model, we can also model safe usage of types that represent linear resources, such as file handler. Suppose that a file handler type `File` has four built-in functions: `open()` for opening a new file, `read(f)` for reading the content of file `f`, `write(f,s)` for writing the value `s` to the file `f`, and `close(f)` for closing the file `f`. We can define that an opened file handler as having the unutilized status, while a closed one as having utilized status. The `open()` function always create a new unutilized file handler. The `read(f)` and `write(f,s)` functions require the parameter `f` to be unutilized, i.e. opened, without changing its utilization status. The `close(f)` function also requires `f` to be unutilized, but then as a side effect it would close the file and utilize the file handler value.

== Problem definition

We define the challenges in utilization tracking by looking at common value utilization patterns found in Kotlin codes. As we explained earlier, a value of utilizable type must be utilized by passing it as an argument to a set of utilizing functions, or returning it as the result of the enclosing function. These utilizing functions consist of some built-in utilizing functions or methods, such as `await` and `cancel` in the case of `Deferred` type, and any user-defined functions that passed its parameter to the built-in functions or other utilizing functions. Therefore, we shall provide a way to *annotate a user-defined function as a utilizing function* and *check if it correctly utilizes its argument(s)*.

Many Kotlin code bases we found use `Deferred` type through a combination of higher-order functions, lambda expressions, and collections or lists of `Deferred` type. @lst:DeferredLambdaCollection illustrates the common patterns we found.

#listing("Utilization with higher-order functions and collections")[
```kt
fun getDeferred() : Deferred? = ...

val d : Deferred? = getDeferred()
d?.let { it.await() }

val calls: MutableList<Deferred> = ...
getDeferred()?.let { calls.add(it) }
val results = calls.map { it.await() }
```] <lst:DeferredLambdaCollection>

In this example, the `Deferred` value in `d` might be null, so users usually employ the `?.let { ... }` pattern. The `let(f)` function is a type-parametric higher-order function, which applies its context object (`d` in this example) as an argument to `f`, in this example the lambda expression `{ it.await() }`. This means that our analysis should also *handle utilization through type-parametric and higher-order functions*. Furthermore, lambda expressions in Kotlin are usually written without any type annotations since it usually results in a harder-to-read source code. Therefore, our analysis shall also *infer any utilization effect of lambda functions* as much as possible.

The other pattern in @lst:DeferredLambdaCollection is the list of deferred calls. In many code bases, the program first creates a list of deferred calls by mapping another list or adding deferred calls to it one by one with `.add`. These calls are then awaited using `awaitAll()` or `map { it.await() }` in some older code bases. This means that our analysis shall also *track the utilization of utilizable values in a list or collection type*.

Another common problem is the *reference alias problem*, that is the problem of determining which values are referenced by which variables. In @lst:DeferredAlias, the only deferred call that might not be fully utilized is the deferred call $D_1$. This is because $D_1$ is only utilized if it is indeed the assigned value to `task2`, but `task2` might be assigned with $D_2$. On the other hand, $D_2$ is fully utilized since if `task2` is assigned with $D_1$, then $D_2$ never exists in the first place. Both $D_3$ and $D_4$ are utilized at line 7 through the variable `task3`, since one can only exist if the other does not. The deferred call $D_5$ is referenced by `task5` through the assignment at line 10, which is then utilized at line 11.

From these examples, only the assignment pattern of `task3` is quite commonly used in Kotlin code bases. While the other patterns are rare, we still need to handle them in order to ensure the soundness of our analysis.


#listing("Reference alias problem")[
```kt
    val task1 = async { /* D1 */ } // the only warning, others are OK

    val task2 = if (...) task1 else async { /* D2 */ }
    task2.await()

    val task3 = if (...) async { /* D3 */ } else async { /* D4 */}
    task3.await()

    val task4 = async { /* D5 */ }
    val task5 = task4
    task5.await()
```] <lst:DeferredAlias>


We mentioned earlier that the utilization model can be used to describe linear resources types such as file handler. Most built-in methods of the file handler type require some prerequisites for the utilization status of the input parameter. Therefore, we shall also provide *utilization status annotation at the function signature* to indicate the required and resulting utilization statuses.

Since we focus on the Kotlin language, there are two constraints that shall be fulfilled by the analysis method. First, the analysis shall be *based on the intra-procedural data-flow analysis* since it is the main technique used in the Kotlin compiler framework. The second constraint is that we shall *use existing features of Kotlin instead of developing new syntax*, such as using Kotlin's annotation feature. This is because we want the analysis to be compatible with common Kotlin programs as much as possible.

In summary, these are the challenges that shall be addressed in the formalization and implementation of the utilization analysis:
+ User-defined functions can be annotated with utilization status requirements and effects, and the analysis can check the annotations' correctness.
+ The analysis can infer the utilization status and effects of lambda functions.
+ The analysis can track utilization through type-parametric higher-order functions and collection types.
+ The analysis can soundly handle the reference alias problem.
+ The analysis is compatible with the Kotlin compiler framework, which means that it is based on intra-procedural data-flow analysis and does not introduce new syntaxes.
