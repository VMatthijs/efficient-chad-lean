# Efficient CHAD in Lean

Lean 4 formalization of efficient CHAD: typed source and target languages, evaluation, the CHAD transformation, linear cotangents, primal preservation, and amortized cost bounds.

## Build

```bash
lake build
```

The Lean version is fixed by `lean-toolchain`.

## Files

```text
EfficientChad.lean                   top-level module
EfficientChad/Spec.lean              object languages, semantics, CHAD, theorem statements
EfficientChad/Spec/LinearTypes.lean  linear cotangent types
EfficientChad/Spec/LACM.lean         local accumulation monad
EfficientChad/Setup.lean             weakening, contexts, and auxiliary lemmas
EfficientChad/EvalSinkCommute.lean   evaluation and weakening/sinking commutation
EfficientChad/ChadPreservesPrimal.lean
EfficientChad/Lemmas.lean            arithmetic lemmas
EfficientChad/ChadCost.lean          main amortized cost proof
EfficientChad/Arrays.lean            optional array helper lemmas and paper notation
```

## Main statements

The main theorems are in `EfficientChad.ChadCost`:

```lean
th1 : TH1_STATEMENT
th2 : TH2_STATEMENT
```

`th1` is the main amortized cost theorem. `th2` is the executable reverse-mode bound.

## Arrays

Arrays are part of the core language:

```lean
Typ.array
Term.arrayBuild
Term.arrayIndex
Term.arrayFold
```

The representation follows the paper:

```lean
Rep (.array τ) = List (Rep τ)
D₁(Array τ)   = Array(D₁ τ)
D₂(Array τ)   = Bag (Int × D₂ τ)
```

Sparse array cotangents use `Bag`, with constructors corresponding to `BagEmpty`, `BagOne`, `BagPlus`, and `BagArray`.

The array CHAD clauses are implemented in `chad`:

- `arrayBuild` differentiates the body elementwise, unzips primal values and backpropagators, collects the sparse cotangent bag, scatters it into a dense cotangent array, zips cotangents with element backpropagators, and sequences the resulting effects.
- `arrayIndex` sends a one-hot sparse cotangent, `BagOne (i, d)`, to the array backpropagator.
- `arrayFold` uses the target-level recorded-reduction primitive `arrayFoldAD`, whose evaluator builds a `FoldTree` in the forward pass and replays it in reverse.

The executable evaluator uses lists as a reference representation. The cost theorem is stated for the paper's primitive array cost model: constant-time indexing and linear-time build, collect, scatter, unzip, zip, sequence, and recorded fold operations.

The primitive array assumptions are isolated in three classes:

```lean
CoreArrayEvalRecursorLaws
CoreArrayPrimalLaws
CoreArrayCostLaws
```

These classes cover the array-specific evaluator recursion, primal-preservation obligations, and cost obligations. The scalar proof structure is otherwise unchanged.

## Optional array helper module

`EfficientChad.Arrays` is not imported by `EfficientChad.lean`. It provides paper-style names, well-formedness predicates, and elementary list/size lemmas for the array fragment, including:

```lean
arrayBuildLengthOk
arrayIndexInBounds
arrayFoldNonempty
```
