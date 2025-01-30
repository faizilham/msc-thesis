#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Summary

In summary, we present a data-flow analysis for tracking the utilization of values, and implement it as a Kotlin compiler plugin. Our utilization analysis technique:
+ infers a safe, over-approximation of utilization status of each utilizable values, and produces warnings for any values with incomplete utilization,
+ allows for annotating utilization effects and status requirements in user-defined functions, higher-order functions, collection types, and resource-like types,
+ checks for incorrect value assignments in regard to the required utilization status and effects,
+ infers the utilization effect and status annotations for lambda functions.

== Limitations and future works

There are some limitations to our analysis technique that can be improved in the future. First, our analysis *cannot infer parametric effects in lambda function signatures*. While it is possible to extend the analysis to allow this, we chose not to do it since it is quite rare for a Kotlin lambda function to be a higher-order function. Allowing parametric effects would also disallow our heuristic for implementing the fast, enumeration-only utilization lattice.

The second limitation is that the analysis *cannot accurately track utilizable values that escape the function through means other than a direct return statement*, for example through a free variable or through a closure environment. Our analysis is still sound since it would mark such values as unutilized and produce warnings about it, but there might be a way to handle some of those cases more accurately.

Next, the analysis *cannot guarantee the utilization status of a value that depends on other values' utilization*. An example of utilization dependency is utilizing the iterator of a utilizable collection in a for-each loop. Currently, the analysis is able to guarantee the utilization of a collection when it is utilized through iterating functions like `forEach` or `map` by relying on function annotations. This is not the case with for-each loop, since it does not have any annotation that can guide the analysis. To handle for-each cases, either the analysis handles it as a special case, or more generally the analysis' lattice must accommodate utilization dependency, such that it can express that the collection's utilization status depends on the iterator's status.

Another limitation is that the analysis also *does not properly identify value aliases*, and as a result *some functions may be annotated unintuitively*. For example, in our analysis the identity function is annotated with a non-neutral, utilizing effect for its parameter, since the analysis need to assume that a function that returns a utilizable value always creates a new value. With a proper alias analysis, the identity function can be annotated with neutral effect.

Our analysis also *does not track the utilization of an object's fields*. Currently, a class containing fields of utilizable types must also be marked as a utilizable type, and the utilizable fields must be declared to be private in order to prevent escaping values. Tracking the utilization of utilizable fields without the aforementioned workaround requires a more sophisticated alias analysis.

The utilization and effect *annotation for the function signature are also quite complex*, especially for the parametric ones. This is because we implement the notation using Kotlin's annotation feature, and thus we are limited by its syntax. This may be improved by either developing a more concise annotation syntax, or improving the inference technique to allow functions to be fully inferred without user-provided annotations.

Lastly, while our analysis mainly handles utilization tracking, it is also possible to model a simple linear resources such as a file handler. With more works, the utilization status and effect annotation could potentially be *generalized to include the other substructural type system*, such as the linear and affine types. An algebra of the utilization status and effects may also be defined to notate more specific cases.
