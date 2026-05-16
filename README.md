# Efficient CHAD in Lean

A Lean 4 library formalizing the efficient CHAD development: typed source and target languages, evaluation, the CHAD transformation, linear cotangents, amortized cost bounds, and the main correctness and cost theorems.

## Structure

```text
EfficientChad/Spec/LinearTypes.lean   linear cotangent types, including sparse array bags
EfficientChad/Spec/LACM.lean          local accumulation monad
EfficientChad/Spec.lean               core object language, arrays, semantics, CHAD, theorem statements
EfficientChad/Setup.lean              supporting lemmas
EfficientChad/EvalSinkCommute.lean    evaluation and weakening/sinking laws
EfficientChad/ChadPreservesPrimal.lean
EfficientChad/Lemmas.lean             integer arithmetic lemmas
EfficientChad/ChadCost.lean           scalar and core-array cost theorem structure
EfficientChad/Arrays.lean             paper spellings and aliases for the core array fragment
```

## Build

```bash
lake build
```

The project uses the Lean version named in `lean-toolchain`.

## Core array extension

Arrays are now part of the core language rather than a detached semantic add-on.
The core definitions contain the three source array forms from the paper:

```lean
Typ.array
Term.arrayBuild
Term.arrayIndex
Term.arrayFold
```

and the target-language array helpers used by the displayed derivative rules:

```lean
Term.larraycollect
Term.arrayUnzipD
Term.arrayScatterD
Term.arrayZipWithScopeD
Term.arraySequenceUnitD
Term.arrayFoldAD
```

`arrayFoldAD` is still a primitive target-level recorded-reduction combinator,
because the paper also treats the recorded tree and `unTree` machinery as an
implementation detail normally hidden from source users.

The semantic representation follows the paper's layout:

```lean
Rep (.array τ) = List (Rep τ)
D₁(Array τ)   = Array(D₁ τ)
D₂(Array τ)   = Bag (Int × D₂ τ)
```

Sparse array cotangents are represented by `Bag`, with constructors matching the
paper's `BagEmpty`, `BagOne`, `BagPlus`, and `BagArray` forms.  The core evaluator
contains list-backed reference implementations of build, indexing, scatter,
zip-with, dense-to-sparse enumeration, and recorded left-associated fold trees.
The reference `build` path constructs lists by forward cons recursion rather than
repeated append; the theorem-level cost model still treats arrays as primitive
random-access arrays, matching the paper rather than literal linked-list update
costs.

The CHAD transform now has paper-shaped source-language array cases.  The
`build` branch is expanded into the same structure as the paper:

```text
let (n, _)    = D[n]
let a         = build n (i. D[body])
let (a₁, a₂)  = unzip a
(a₁, λd. collect d; scatter; zipWith; sequence)
```

The indexing branch is likewise expanded as:

```text
let (xs₁, xs₂) = D[xs]
let (i, _)     = D[i]
(xs₁ ! i, λd. xs₂ (BagOne (i, d)))
```

The fold branch uses the recorded-tree target primitive `arrayFoldAD`, whose
evaluator explicitly builds a `FoldTree` in the primal pass and runs
`FoldTree.unTree` in the reverse pass.  This is the one remaining packaged array
translation form; it packages the tree type hidden in the paper, not the whole
array theory.

The global TH1 proof is also an induction over the extended `Term` syntax.  The
scalar branches remain constructive.  The array branches dispatch through an
explicit primitive cost model class:

```lean
CoreArrayCostLaws
```

The improved version does not assume the whole array theorem as a black box.  The
array cost methods receive the recursive TH1 hypotheses for their subterms, just
like the scalar `pair`, `case`, and `let` lemmas.  Similarly, primal preservation
uses per-array-rule obligations with recursive preservation hypotheses:

```lean
CoreArrayPrimalLaws
```

Weakening/evaluation commutation is constructive for the scalar language, simple
array constructors, one-hot/bag cotangents, array indexing, and the non-recursive
target helpers `collect`, `unzip`, `scatter`, `zipWithScope`, and `sequenceUnit`.
Only the recursive array evaluators are abstracted as primitive recursor laws:

```lean
CoreArrayEvalRecursorLaws
```

Thus `th1`, `th2`, `array_complexity`, and `array_th1` are core-language theorems
for any primitive array implementation satisfying these local array laws.  This is
intentional: the executable reference definitions use lists, but the paper's
complexity model charges random-access array operations and recorded reductions
as primitives.

`EfficientChad.Arrays` also records the paper-side well-formedness conditions
that the total reference evaluator erases:

```lean
arrayBuildLengthOk
arrayIndexInBounds
arrayFoldNonempty
```

and basic checked size/cost facts for build, enumeration, scatter, zip-with, and
bag collection.


## v10 build-log fixes

This package consolidates the fixes for the logs that referenced the older `efficient-chad-lean-core-arrays-v4` directory:

- `EvalSinkCommute.lean` uses ordinary constructor patterns for `arrayFold`/`arrayFoldAD` and passes the pushed integer type explicitly in the `arrayBuild` weakening case.
- `ChadCost.lean` removes the stale `omega` after the `Bag.array` `simp` branch, which Lean 4.12 reports as `no goals to be solved`.
- `ChadCost.lean` disables the unused-section-variable linter for the top-level primitive array cost law variable to keep builds focused on errors rather than harmless warnings.
