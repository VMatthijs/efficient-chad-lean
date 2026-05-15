# Efficient CHAD in Lean

A Lean 4 translation (from Agda) of Tom Smeding's the efficient CHAD development (https://github.com/tomsmeding/efficient-chad-agda): typed source and target languages, evaluation, the CHAD transformation, linear cotangents, amortized cost bounds, and the main correctness and cost theorems.

## Structure

```text
EfficientChad/Spec/LinearTypes.lean   linear cotangent types and operations
EfficientChad/Spec/LACM.lean          local accumulation monad
EfficientChad/Spec.lean               object language, semantics, CHAD, theorem statements
EfficientChad/Setup.lean              supporting lemmas
EfficientChad/EvalSinkCommute.lean    evaluation and weakening/sinking
EfficientChad/ChadPreservesPrimal.lean
EfficientChad/Lemmas.lean             integer arithmetic lemmas
EfficientChad/ChadCost.lean           main cost theorems
```

## Build

```bash
lake build
```

The project uses the Lean version named in `lean-toolchain`.
