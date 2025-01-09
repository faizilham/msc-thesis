#import "../lib/symbols.typ": *
#import "../lib/utilities.typ": *

= Summary and Conclusion

- conclusion

- limitations and future works:
  - No parametric inference for effects, rarely used while disallowing the more efficient non-set, enum only implementation of the lattice.
  - Escaping value cases
  - Proper aliasing analysis, s.t. parameter-returning function like identity function can be effect-less
  - Algebraic utilization annotation and effect
  - Generalization to linear & affine type system, currently only limited like the File type.
