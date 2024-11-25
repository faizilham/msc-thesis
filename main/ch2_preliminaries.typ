#import "../lib/utilities.typ": *

= Preliminaries and Related Works

TODO: modify

In this chapter, we discuss the background knowledge needed for the research and review research literature related to the unused return value analysis problem.

== The Kotlin programming language

Kotlin is a statistically typed, general-purpose, object-oriented programming language developed by JetBrains #citep(<KotlinSpec2020>, 3). While mainly object-oriented, Kotlin also supports some aspects of the functional programming paradigm such as higher-order functions and lambda literals. We shall delve into some features of the Kotlin language that are connected to this research.

=== Type system

Kotlin type system has various features and properties #citep(<KotlinSpec2020>, 44). A main feature of the type system is null safety, which is achieved by splitting the types into two different lattice universes, nullable and non-nullable. The type system also has a
unified top (`kotlin.Any`) and bottom (`kotlin.Nothing`) types in the lattices, and a proper upper and lower bound operation using the intersection and union types. Both intersection and union types are non-denotable, meaning they can not be used directly in the codes by users and only exist when performing analyses and compiling the code.

Another notable feature of the Kotlin type system is the flow-based type inference, meaning the type of an expression can be inferred based on where it appears in the control flow. For example, when a variable x of type `kotlin.Any` is checked as an integer using a construct such as `if (x is Int)`, the compiler can be sure that x can be statically cast as an integer in the true branch. Otherwise, the control flow would never reach that branch in the first place. This flow-based type inference is performed using a control flow analysis.

=== Data flow analysis in Kotlin

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

== Substructural type system


Requiring values to be used at least once, which is the heart of unused return values analysis, is similar to requiring values or resources to be used at most or exactly once. These kinds of resource usage restrictions are often defined using a substructural type system. A substructural type system is a type system where at least one of the structural properties does not hold #cite(<walkerST>). The structural properties are the properties of the simply typed lambda calculus concerning the use of variables, which are:
  + Exchange: the variables ordering in the context do not matter in regards to their usage,
  + Weakening: any extra, irrelevant variable in the context does not prevent the type checking to fail,
  + Contraction: two identical variables in the context are equivalent to a single variable.

Depending on which structural properties are held or broken, one may get a different variant of type systems.
  + Unrestricted type systems are the "normal" type systems, where all structural properties hold.
  + Affine type systems are type systems where only the contraction property is broken, resulting in type systems that require variables to be used at most once.
  + Relevant type systems are type systems where only the weakening property is broken, resulting in type systems that require variables to be used at least once.
  + Linear type systems are type systems where both the contraction and weakening properties are broken and the exchange property is held, resulting in type systems that require variables to be used exactly once. This type system is first developed from linear logic #cite(<WadlerLinearTC>), and is among the earliest substructural type systems to be described.
  + Ordered type systems are type systems where all structural properties are broken, resulting in type systems that require variables to be used exactly once and in the same order in which they are declared.

Our unused return value analysis requires some types to be used at least once, thus it can be modeled as a variant of relevant type systems.

Another type system related to the standard substructural type systems is the uniqueness type. Uniqueness type, first introduced by Smetsers et al. in the Clean language #cite(<uniquenessClean>), guarantees the uniqueness of a variable reference, i.e. there is exactly one reference to the variable value. This way, reference aliasing is much easier to handle since there should only be one reference for a unique variable.

Uniqueness type is the dual of the linear type, as formally shown as a unified calculus by Marshall, Vollmer, and Orchard #cite(<LinearUniqMarshall>). In an informal sense, linear type is a future guarantee while uniqueness type is a past guarantee. Linear type guarantees that in the future a linear variable will be consumed exactly once, whereas uniqueness type guarantees that since its creation, there was and is exactly one reference to the unique variable.

== Other related works

Many languages include unused value warning analyses in their compilers or development tools. However, these analyses tend to be minimal and lack many of the properties we proposed in this research. For example, in Swift #cite(<SwiftWarn>), unused values from non-void returning functions may produce warnings unless the functions are annotated as discardable. However, a function's discardable attribute is not preserved or propagated when the function is assigned to a function-type variable or passed to a higher-order function. In C++17 and above #cite(<CppNoDiscard>), compilers are encouraged to report a warning if there is an unused value from a function with `[[nodiscard]]` attribute. The default behavior, however, is not reporting any unused value.

A more fine-grained approach than the standard substructural type system is the graded modal type system based on bounded linear logic presented by Orchard, Liepelt, and Eades #cite(<Granule19>). This type system, which is implemented for the Granule language, allows quantitative reasoning of variable usages. Instead of rougher guarantees like "exactly once", "at most once" or "at least once", the type system allows usage guarantee of a specific range of natural numbers or any semiring structures. A graded type `Int [1..3]` in Granule means that the integer value must be used at least once and at most three times. While we are unlikely to adopt graded modal types in our work, it might be useful to use Granule for modeling our analysis.

Zimmerman et al. #cite(<latte2023>) presented Latte, a lightweight aliasing tracking for Java with minimal annotations of unique, shared, or borrowed. Only function parameters and object fields require annotations, whereas local variable uniqueness can be automatically inferred.

Pavlinovic, Su, and Wies #cite(<DFRefinement21>) presented a refinement type inference framework that is sensitive to data flow contexts. They formalized type inference as an abstract interpretation problem. Through that perspective, they derived an inference algorithm and proved that the type system is sound and complete in regard to the abstract interpretation semantics.


Foster, Terauchi, and Aiken #cite(<FlowTypeQualifier02>) presented a flow-sensitive type qualifiers system. In their system, programs can be annotated with type qualifiers and checked by a control-flow sensitive inference. Furthermore, they presented an example of alias analysis and effect inference using the system.
