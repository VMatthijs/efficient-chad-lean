namespace EfficientChad

universe u

/-- Sparse bags used for array cotangents.  This is the paper's
`Bag` datatype, extended with `array`/`BagArray` for dense batches of
contributions. -/
inductive Bag (α : Type u) : Type u where
  | empty : Bag α
  | one : α → Bag α
  | plus : Bag α → Bag α → Bag α
  | array : List α → Bag α
  deriving Repr

namespace Bag

/-- Collect a sparse bag to a dense list. -/
def collect {α : Type u} : Bag α → List α
  | .empty => []
  | .one x => [x]
  | .plus xs ys => collect xs ++ collect ys
  | .array xs => xs

/-- Amortised collection cost. -/
def collectCost {α : Type u} : Bag α → Int
  | .empty => 1
  | .one _ => 1
  | .plus xs ys => collectCost xs + collectCost ys - 1
  | .array xs => 1 + Int.ofNat xs.length

/-- Construction cost stored in a bag. -/
def constructCost {α : Type u} : Bag α → Int
  | .empty => 1
  | .one _ => 1
  | .plus xs ys => 1 + constructCost xs + constructCost ys
  | .array xs => 1 + Int.ofNat xs.length

/-- A structural size for sparse bags. -/
def size {α : Type u} : Bag α → Nat
  | .empty => 1
  | .one _ => 1
  | .plus xs ys => 1 + size xs + size ys
  | .array xs => 1 + xs.length

end Bag

/-- Linear target types.  `Dyn` is the abstract universal cotangent carrier
used for source function types.  Its concrete representation and encode/decode
laws are supplied below as explicit assumptions. -/
inductive LTyp : Type where
  | LUn : LTyp
  | LR : LTyp
  | Dyn : LTyp
  | prod : LTyp → LTyp → LTyp
  | sum : LTyp → LTyp → LTyp
  | array : LTyp → LTyp
  deriving Repr

abbrev LEnv : Type := List LTyp

def «_:*!_» (σ τ : LTyp) : LTyp :=
  LTyp.prod σ τ

def «_:+!_» (σ τ : LTyp) : LTyp :=
  LTyp.sum σ τ

inductive Idx {α : Type u} : List α → α → Type u where
  | Z {Γ : List α} {τ : α} : Idx (τ :: Γ) τ
  | S {Γ : List α} {τ τ' : α} : Idx Γ τ → Idx (τ' :: Γ) τ

/-- Runtime representation of `Dyn`.

`Dyn` is intentionally untyped: it is the carrier used to stash compact closure
cotangent environments for higher-order values.  The concrete tree below is only
an executable placeholder for the semantic model.  The CHAD correctness and cost
theorems still require the explicit Dyn assumptions in `Spec.lean`, namely
`dynEncode`, `dynDecode`, their retraction law, and the stated amortised cost
bounds. -/
inductive DynRep : Type where
  | unit : DynRep
  | int : Int → DynRep
  | real : Float → DynRep
  | pair : DynRep → DynRep → DynRep
  | inl : DynRep → DynRep
  | inr : DynRep → DynRep
  | array : List (Int × DynRep) → DynRep
  deriving Repr, Inhabited

/-- Zero and addition on `Dyn` used by the linear-combination operations.
The size/cost potential for `Dyn` is deliberately constant in this development;
the representation-specific encode/decode cost is accounted for separately by
the Dyn encode/decode cost assumptions in `Spec.lean`. -/
def dynZero : DynRep := DynRep.unit

def dynPlus (x y : DynRep) : DynRep := DynRep.pair x y

def LinRep : LTyp → Type
  | .LUn => Unit
  | .LR => Float
  | .Dyn => DynRep
  | .prod σ τ => Option (LinRep σ × LinRep τ)
  | .sum σ τ => Option (Sum (LinRep σ) (LinRep τ))
  | .array τ => Bag (Int × LinRep τ)

def LEtup : LEnv → Type
  | [] => Unit
  | τ :: Γ => LinRep τ × LEtup Γ

abbrev one : Int := 1

abbrev intOfNat (n : Nat) : Int := Int.ofNat n

abbrev intLength {α : Type u} (xs : List α) : Int := Int.ofNat xs.length

@[simp] theorem intLength_nil {α : Type u} : intLength ([] : List α) = 0 := by
  simp [intLength]

@[simp] theorem intLength_cons {α : Type u} (x : α) (xs : List α) :
    intLength (x :: xs) = intLength xs + 1 := by
  simp [intLength]

def zerov : (τ : LTyp) → LinRep τ × Int
  | .LUn => ((), one)
  | .LR => ((0.0 : Float), one)
  | .Dyn => (dynZero, one)
  | .prod _ _ => (none, one)
  | .sum _ _ => (none, one)
  | .array _ => (Bag.empty, one)

def plusv : (τ : LTyp) → LinRep τ → LinRep τ → LinRep τ × Int
  | .LUn, (), () => ((), one)
  | .LR, x, y => (((show Float from x) + (show Float from y)), one)
  | .Dyn, x, y => (dynPlus x y, one)
  | .prod _ _, none, y => (y, one)
  | .prod _ _, x, none => (x, one)
  | .prod σ τ, some (x, y), some (x', y') =>
      let xr := plusv σ x x'
      let yr := plusv τ y y'
      (some (xr.1, yr.1), one + xr.2 + yr.2)
  | .sum _ _, x, none => (x, one)
  | .sum _ _, none, y => (y, one)
  | .sum σ _, some (Sum.inl x), some (Sum.inl y) =>
      let z := plusv σ x y
      (some (Sum.inl z.1), one + z.2)
  | .sum _ τ, some (Sum.inr x), some (Sum.inr y) =>
      let z := plusv τ x y
      (some (Sum.inr z.1), one + z.2)
  | .sum _ _, _, _ => (none, one)
  | .array _, x, y => (Bag.plus x y, one)

def addLET {Γ : LEnv} {τ : LTyp} (idx : Idx Γ τ) (val : LinRep τ) : LEtup Γ → LEtup Γ :=
  match idx with
  | .Z => fun env => ((plusv τ val env.1).1, env.2)
  | .S i => fun env => (env.1, addLET i val env.2)

def getLET {Γ : LEnv} {τ : LTyp} (env : LEtup Γ) (idx : Idx Γ τ) : LinRep τ :=
  match idx with
  | .Z => env.1
  | .S i => getLET env.2 i

def «addLEτ» {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) : LEtup Γ → LEtup Γ :=
  addLET idx val

def «_Eτ!!_» {Γ : LEnv} {τ : LTyp}
    (env : LEtup Γ) (idx : Idx Γ τ) : LinRep τ :=
  getLET env idx

/-- Pointwise zero for a linear environment. -/
def zeroLEtup : (Γ : LEnv) → LEtup Γ
  | [] => ()
  | τ :: Γ => ((zerov τ).1, zeroLEtup Γ)

/-- Pointwise addition for linear-environment tuples. -/
def addLEtup : (Γ : LEnv) → LEtup Γ → LEtup Γ → LEtup Γ
  | [], (), () => ()
  | τ :: Γ, x, y => ((plusv τ x.1 y.1).1, addLEtup Γ x.2 y.2)

/-- A typed injection between linear environments. -/
abbrev LEnvInj (Γsrc Γdst : LEnv) : Type :=
  ∀ {δ : LTyp}, Idx Γsrc δ → Idx Γdst δ

/-- A single nonzero contribution in a linear environment. -/
def singletonLEtup : {Γ : LEnv} → {τ : LTyp} → Idx Γ τ → LinRep τ → LEtup Γ
  | _τ :: Γ, _, .Z, d => (d, zeroLEtup Γ)
  | σ :: Γ, τ, .S i, d => ((zerov σ).1, singletonLEtup i d)

/-- Scatter a compact linear-environment tuple into a larger environment. -/
def scatterLEtup : {Γsrc Γdst : LEnv} → LEnvInj Γsrc Γdst → LEtup Γsrc → LEtup Γdst
  | [], Γdst, _inj, _d => zeroLEtup Γdst
  | σ :: Γsrc, Γdst, inj, d =>
      addLEtup Γdst
        (singletonLEtup (inj (Idx.Z : Idx (σ :: Γsrc) σ)) d.1)
        (scatterLEtup (fun {δ} (i : Idx Γsrc δ) => inj (.S i)) d.2)

end EfficientChad
