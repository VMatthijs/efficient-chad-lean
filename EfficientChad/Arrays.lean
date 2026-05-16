import EfficientChad.ChadCost

namespace EfficientChad

universe u v

/-- Compatibility spelling for the paper's dense arrays.  The core language uses
`Typ.array` and represents arrays as lists while charging primitive-array costs. -/
abbrev ArrayRep (α : Type u) : Type u := List α

/-- Paper spelling: `BagEmpty`. -/
def BagEmpty {α : Type u} : Bag α := Bag.empty

/-- Paper spelling: `BagOne`. -/
def BagOne {α : Type u} (x : α) : Bag α := Bag.one x

/-- Paper spelling: `BagPlus`. -/
def BagPlus {α : Type u} (xs ys : Bag α) : Bag α := Bag.plus xs ys

/-- Paper spelling: `BagArray`. -/
def BagArray {α : Type u} (xs : ArrayRep α) : Bag α := Bag.array xs

/-- Paper spelling for bag collection. -/
def collect {α : Type u} (xs : Bag α) : ArrayRep α := Bag.collect xs

/-- Paper spelling for dense array construction. -/
def build {α : Type u} (n : Int) (f : Int → α) : ArrayRep α :=
  arrayBuildCore n f

/-- Paper spelling for dense array indexing. -/
def index {α : Type u} (xs : ArrayRep α) (i : Int) (default : α) : α :=
  arrayIndexCore xs i default

/-- Paper spelling for scatter/accumulation into a dense array. -/
def scatter {α : Type u} (plus : α → α → α)
    (base : ArrayRep α) (pairs : ArrayRep (Int × α)) : ArrayRep α :=
  arrayScatterCore plus base pairs

/-- Paper spelling for pointwise array zipping. -/
def zipWith {α : Type u} {β : Type v} {γ : Type u}
    (f : α → β → γ) : ArrayRep α → ArrayRep β → ArrayRep γ :=
  arrayZipWithCore f

/-- Paper spelling for unzipping an array of pairs. -/
def unzip {α : Type u} {β : Type v} (xs : ArrayRep (α × β)) : ArrayRep α × ArrayRep β :=
  arrayUnzipCore xs

/-- Core target-language paper spelling for `collect : Bag α → Array α`. -/
def collectTerm {Γ : Env .Du} {τ : LTyp}
    (d : Term .Du Γ (.Lin (.array τ))) : Term .Du Γ (.array (.prod .Inte (.Lin τ))) :=
  Term.larraycollect d

/-- Core target-language paper spelling for `unzip`. -/
def unzipTerm {Γ : Env .Du} {α β : Typ .Du}
    (xs : Term .Du Γ (.array (.prod α β))) : Term .Du Γ (.prod (.array α) (.array β)) :=
  Term.arrayUnzipD xs

/-- Core target-language paper spelling for `scatter`. -/
def scatterTerm {Γ : Env .Du} {τ : LTyp}
    (base : Term .Du Γ (.array (.Lin τ)))
    (pairs : Term .Du Γ (.array (.prod .Inte (.Lin τ)))) :
    Term .Du Γ (.array (.Lin τ)) :=
  Term.arrayScatterD base pairs

/-- The target-language `zipWith` specialised to the paper's build backpropagator. -/
def zipWithScopeTerm {Γ : Env .Du} {Γl : LEnv} {τ : LTyp}
    (fs : Term .Du Γ (.array (.arr (.Lin τ) (.EVM (.LUn :: Γl) .Un))))
    (ds : Term .Du Γ (.array (.Lin τ))) : Term .Du Γ (.array (.EVM Γl .Un)) :=
  Term.arrayZipWithScopeD fs ds

/-- Core target-language paper spelling for sequencing the build backpropagator actions. -/
def sequenceUnitTerm {Γ : Env .Du} {Γl : LEnv}
    (acts : Term .Du Γ (.array (.EVM Γl .Un))) : Term .Du Γ (.EVM Γl .Un) :=
  Term.arraySequenceUnitD acts

/-- Sequence an array of local-accumulation computations. -/
def sequence {Γ : LEnv} {α : Type u} : ArrayRep (LACM Γ α) → LACM Γ (ArrayRep α)
  | [] => LACM.pure []
  | m :: ms =>
      LACM.bind m (fun x =>
        (LACM.bind (sequence ms) (fun xs => (LACM.pure (x :: xs), one)), one))

/-- Paper spelling for constructing an array from a list. -/
def fromList {α : Type u} (xs : List α) : ArrayRep α := xs

/-- Paper spelling for enumerating dense array positions. -/
def enumerate {α : Type u} (xs : ArrayRep α) : ArrayRep (Int × α) :=
  arrayEnumerateCore xs

/-- Semantic form of the paper's `D₁(Array τ) = Array(D₁ τ)`. -/
abbrev ArrayD1 (τ : Typ .Pr) : Type := ArrayRep (Rep (D1τ τ))

/-- Semantic form of the paper's `D₂(Array τ) = Bag(Int × D₂ τ)`. -/
abbrev ArrayD2Prime (τ : Typ .Pr) : Type := Bag (Int × LinRep (D2τPrime τ))

/-- An index is semantically well formed for the list-backed reference evaluator. -/
def arrayIndexInBounds {α : Type u} (xs : ArrayRep α) (i : Int) : Prop :=
  0 ≤ i ∧ i.toNat < xs.length

/-- The paper assumes non-negative build lengths; the reference evaluator
truncates negative lengths with `Int.toNat`. -/
def arrayBuildLengthOk (n : Int) : Prop :=
  0 ≤ n

/-- The paper's fold primitive is a non-empty reduction.  The reference evaluator
is total and uses a default value on `[]`; this predicate records the paper-side
well-formedness condition. -/
def arrayFoldNonempty {α : Type u} (xs : ArrayRep α) : Prop :=
  xs ≠ []

@[simp] theorem arrayBuildCoreFrom_length {α : Type u}
    (start n : Nat) (f : Int → α) :
    (arrayBuildCoreFrom start n f).length = n := by
  induction n generalizing start with
  | zero => simp [arrayBuildCoreFrom]
  | succ n ih => simp [arrayBuildCoreFrom, ih]

@[simp] theorem arrayBuildCoreAux_length {α : Type u} (n : Nat) (f : Int → α) :
    (arrayBuildCoreAux n f).length = n := by
  simp [arrayBuildCoreAux]

@[simp] theorem arrayBuildCore_length {α : Type u} (n : Int) (f : Int → α) :
    (arrayBuildCore n f).length = n.toNat := by
  simp [arrayBuildCore]

@[simp] theorem arrayEnumerateFromCore_length {α : Type u}
    (start : Nat) (xs : ArrayRep α) :
    (arrayEnumerateFromCore start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => simp [arrayEnumerateFromCore]
  | cons x xs ih => simp [arrayEnumerateFromCore, ih]

@[simp] theorem arrayEnumerateCore_length {α : Type u} (xs : ArrayRep α) :
    (arrayEnumerateCore xs).length = xs.length := by
  simp [arrayEnumerateCore]

theorem arrayUpdatePlus_length {α : Type u} (plus : α → α → α)
    (xs : ArrayRep α) (idx : Nat) (v : α) :
    (arrayUpdatePlus plus xs idx v).length = xs.length := by
  induction xs generalizing idx with
  | nil => cases idx <;> simp [arrayUpdatePlus]
  | cons x xs ih => cases idx <;> simp [arrayUpdatePlus, ih]

@[simp] theorem arrayScatterCore_length {α : Type u} (plus : α → α → α)
    (base : ArrayRep α) (pairs : ArrayRep (Int × α)) :
    (arrayScatterCore plus base pairs).length = base.length := by
  induction pairs generalizing base with
  | nil => simp [arrayScatterCore]
  | cons p ps ih =>
      calc
        (arrayScatterCore plus base (p :: ps)).length
            = (arrayScatterCore plus
                (arrayUpdatePlus plus base p.1.toNat p.2) ps).length := by
                simp [arrayScatterCore]
        _ = (arrayUpdatePlus plus base p.1.toNat p.2).length := ih _
        _ = base.length := arrayUpdatePlus_length plus base p.1.toNat p.2

theorem arrayZipWithCore_length_le_left {α : Type u} {β : Type v} {γ : Type u}
    (f : α → β → γ) (xs : ArrayRep α) (ys : ArrayRep β) :
    (arrayZipWithCore f xs ys).length ≤ xs.length := by
  induction xs generalizing ys with
  | nil => simp [arrayZipWithCore]
  | cons x xs ih =>
      cases ys with
      | nil => simp [arrayZipWithCore]
      | cons y ys =>
          simp [arrayZipWithCore]
          exact ih ys

theorem arrayZipWithCore_length_le_right {α : Type u} {β : Type v} {γ : Type u}
    (f : α → β → γ) (xs : ArrayRep α) (ys : ArrayRep β) :
    (arrayZipWithCore f xs ys).length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp [arrayZipWithCore]
  | cons x xs ih =>
      cases ys with
      | nil => simp [arrayZipWithCore]
      | cons y ys =>
          simp [arrayZipWithCore]
          exact ih ys

@[simp] theorem arrayUnzipCore_fst_length {α : Type u} {β : Type v}
    (xs : ArrayRep (α × β)) :
    (arrayUnzipCore xs).1.length = xs.length := by
  induction xs with
  | nil => simp [arrayUnzipCore]
  | cons p xs ih =>
      cases p
      simp [arrayUnzipCore, ih]

@[simp] theorem arrayUnzipCore_snd_length {α : Type u} {β : Type v}
    (xs : ArrayRep (α × β)) :
    (arrayUnzipCore xs).2.length = xs.length := by
  induction xs with
  | nil => simp [arrayUnzipCore]
  | cons p xs ih =>
      cases p
      simp [arrayUnzipCore, ih]

theorem Bag_collect_length_le_size {α : Type u} (b : Bag α) :
    (Bag.collect b).length ≤ Bag.size b := by
  induction b with
  | empty => simp [Bag.collect, Bag.size]
  | one x => simp [Bag.collect, Bag.size]
  | plus xs ys ihx ihy =>
      simp [Bag.collect, Bag.size] at ihx ihy ⊢
      omega
  | array xs => simp [Bag.collect, Bag.size]

theorem Bag_collectCost_le_constructCost {α : Type u} (b : Bag α) :
    Bag.collectCost b ≤ Bag.constructCost b := by
  induction b with
  | empty => simp [Bag.collectCost, Bag.constructCost]
  | one x => simp [Bag.collectCost, Bag.constructCost]
  | plus xs ys ihx ihy =>
      simp [Bag.collectCost, Bag.constructCost] at ihx ihy ⊢
      omega
  | array xs => simp [Bag.collectCost, Bag.constructCost]

/-- Sequential primitive cost assigned to dense array indexing in the abstract
paper model.  The reference evaluator is list backed; this constant records the
intended primitive-array cost rather than Lean list traversal cost. -/
def arrayIndexPrimitiveCost : Int := one

/-- Sequential primitive work of build/unzip/zip-style dense operations. -/
def arrayLinearPrimitiveCost (n : Nat) : Int := one + Int.ofNat n

/-- Sequential primitive work of scatter is linear in the dense base plus the
collected sparse update list. -/
def arrayScatterPrimitiveCost {α : Type u} {β : Type v}
    (base : ArrayRep α) (pairs : ArrayRep β) : Int :=
  one + intLength base + intLength pairs

variable [CoreArrayCostLaws]

/-- The core language now has arrays directly in `Typ`, `Term`, `eval`, `chad`,
and the global TH1 statement.  This alias keeps the previous array-module theorem
name available. -/
theorem array_complexity : TH1_STATEMENT := th1

/-- Alias exposing the global theorem under the array-specific name used by the
standalone array development. -/
theorem array_th1 : TH1_STATEMENT := th1

/-- The executable reverse-mode bound also ranges over array terms. -/
theorem array_th2 : TH2_STATEMENT := th2

end EfficientChad
