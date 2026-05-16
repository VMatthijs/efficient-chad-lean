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

inductive LTyp : Type where
  | LUn : LTyp
  | LR : LTyp
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

def LinRep : LTyp → Type
  | .LUn => Unit
  | .LR => Float
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
  | .prod _ _ => (none, one)
  | .sum _ _ => (none, one)
  | .array _ => (Bag.empty, one)

def plusv : (τ : LTyp) → LinRep τ → LinRep τ → LinRep τ × Int
  | .LUn, (), () => ((), one)
  | .LR, x, y => (((show Float from x) + (show Float from y)), one)
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

end EfficientChad
