#import "../lib/utilities.typ": *

= Related Work

In this chapter, we review literature and other research related to the utilization analysis problem. We first look into static analyses in some programming languages that are similar to the utilization analysis.

== Static analyses similar to the utilization analysis

Many languages include unused variable and unused return value analyses in their compilers or development tools. However, these analyses tend to be minimal and lack the properties we want to ensure utilization. For example, the Kotlin compiler reports any unused variables or parameters, it does not report any unused return values. In Swift #cite(<SwiftWarn>), unused values from non-void returning functions may produce warnings unless the functions are annotated as discardable. However, a value is always deemed to be used if it is passed as a parameter to any kind of function, unlike the criteria for value utilization. In C++17 and above #cite(<CppNoDiscard>), compilers are encouraged to report a warning if there is an unused value from a function with `[[nodiscard]]` attribute. The default behavior, however, is not reporting any unused value.

Requiring values to be used at least once, which is the heart of utilization analysis, is similar to requiring values or resources to be used at most or exactly once. One popular language that is built upon this principle is Rust @klabnik2023rust, in which non-copyable values can only be used at most once to guarantee memory safety without needing a garbage collector. These kinds of resource usage restrictions are often defined using a substructural type system.

== Substructural type system

A substructural type system is a type system where at least one of the structural properties does not hold #cite(<walkerST>). The structural properties are the properties of the simply typed lambda calculus concerning the use of variables, which are:
  + Exchange: the variables' ordering in the context does not matter in regard to their usage,
  + Weakening: any extra, irrelevant variable in the context does not prevent the type checking to fail,
  + Contraction: two identical variables in the context are equivalent to a single variable.

Depending on which structural properties are held or broken, one may get a different variant of type systems.
  + Unrestricted type systems are the "normal" type systems, where all structural properties hold.
  + Affine type systems are type systems where only the contraction property is broken, resulting in type systems that require variables to be used at most once. For example, the move semantics of non-copyable values in Rust can be defined with an affine type system @Reed2015PatinaA.
  + Relevant type systems are type systems where only the weakening property is broken, resulting in type systems that require variables to be used at least once. Our utilization analysis requires values to be utilized at least once, thus it may also be modeled as a variant of relevant type systems.
  + Linear type systems are type systems where both the contraction and weakening properties are broken and the exchange property is held, resulting in type systems that require variables to be used exactly once. This type system is developed from linear logic #cite(<WadlerLinearTC>) and is among the earliest substructural type systems to be described.
  + Ordered type systems are type systems where all structural properties are broken, resulting in type systems that require variables to be used exactly once and in the same order in which they are declared.

Other type systems related to the standard substructural type systems are uniqueness type systems. Uniqueness types, first introduced by Smetsers et al. in the Clean language #cite(<uniquenessClean>), guarantee the uniqueness of a variable reference, i.e. there is exactly one reference to the variable value. This way, reference aliasing is much easier to handle since there should only be one reference for a unique variable.

Uniqueness type is the dual of the linear type, as formally shown as a unified calculus by Marshall, Vollmer, and Orchard #cite(<LinearUniqMarshall>). In an informal sense, linear types are future guaranteed while uniqueness types are past guarantees. Linear type guarantees that in the future a linear variable will be consumed exactly once, whereas uniqueness type guarantees that since its creation, there was and is exactly one reference to the unique variable.

== Other related work

A more fine-grained approach than the standard substructural type system is the graded modal type system based on bounded linear logic presented by Orchard, Liepelt, and Eades #cite(<Granule19>). This type system, which is implemented for the Granule language, allows quantitative reasoning of variable usages. Instead of rougher guarantees like "exactly once", "at most once" or "at least once", the type system allows usage guarantee of a specific range of natural numbers or any semiring structures. A graded type `Int [1..3]` in Granule means that the integer value must be used at least once and at most three times.

Zimmerman et al. #cite(<latte2023>) presented Latte, a lightweight aliasing tracking for Java with minimal annotations of unique, shared, or borrowed. Only function parameters and object fields require annotations, whereas local variable uniqueness is automatically inferred.

Pavlinovic, Su, and Wies #cite(<DFRefinement21>) presented a refinement type inference framework that is sensitive to data flow contexts. They formalized type inference as an abstract interpretation problem. Through that perspective, they derived an inference algorithm and proved that the type system is sound and complete in regard to the abstract interpretation semantics.


Foster, Terauchi, and Aiken #cite(<FlowTypeQualifier02>) presented a flow-sensitive type qualifiers system. In their system, programs are annotated with type qualifiers and checked by a control-flow sensitive inference. Furthermore, they presented an example of alias analysis and effect inference using the system.
