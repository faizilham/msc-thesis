#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Summary and Conclusion

In summary, we present a data flow analysis for tracking the utilization of values, and implement it as a Kotlin compiler plugin. Using Kotlin's annotation feature, we extend the function signature with utilization status and effect notation. Our analysis can produce warnings on unutilized values, check the correct utilization status and effect for each function call, and perform a basic utilization and effect annotation inference for lambda functions.

There are some limitations to our work that can be extended in the future. First, our analysis cannot infer parametric effects in lambda function signatures. While it is possible to extend the analysis to allow this, we chose not to do it since it is quite rare for a Kotlin lambda function to be a higher-order function. Allowing parametric effects would also disallow our heuristic for implementing the fast, enumeration-only utilization lattice. Another limitation is tracking utilizable values that escape the function through means other than return statements, for example through a free variable or through a closure environment. Our analysis is still sound since it would simply mark such values as unutilized and produce warnings about it, but we believe it is possible to handle such cases more accurately.

Our analysis also does not properly identify value aliases, and as a result some functions may be annotated with unintuitive utilization and effect annotations. For example, in our analysis the identity function is annotated with a non-neutral, utilizing effect for its parameter, since the analysis need to assume that a function that returns a utilizable value always creates a new value. With a proper alias analysis, it may be possible to annotate the identity function to have neutral effect.

The utilization and effect annotation for the function signature are also quite complex to read and write, especially for the parametric ones. This is because we implement the notation using Kotlin's annotation feature, and thus we are limited by its syntax. This may be improved by either developing a more concise syntax, or improving the inference algorithm to allow functions to be fully inferred without user-provided annotations.

Lastly, while our analysis mainly handles utilization tracking, it is also possible to model a simple linear resources such as a file handler. With more works, the utilization status and effect annotation could potentially be generalized to include the other substructural type system, such as the linear and affine types. An algebra of the utilization statuses and effects may also be defined to notate more specific cases.
