import Lean.Elab.Tactic.Omega
import EfficientChad.Spec.LinearTypes

namespace EfficientChad

universe u v

abbrev LACM (Γ : LEnv) (α : Type u) : Type u := LEtup Γ → α × LEtup Γ × Int

namespace LACM

def pure {Γ : LEnv} {α : Type u} (x : α) : LACM Γ α :=
  fun e => (x, e, one)

def bind {Γ : LEnv} {α : Type u} {β : Type v}
    (m : LACM Γ α) (k : α → LACM Γ β × Int) : LACM Γ β :=
  fun e =>
    let r1 := m e
    let x := r1.1
    let e1 := r1.2.1
    let c1 := r1.2.2
    let kx := k x
    let m2 := kx.1
    let ccall := kx.2
    let r2 := m2 e1
    (r2.1, r2.2.1, one + c1 + ccall + r2.2.2)

def run {Γ : LEnv} {α : Type u} (m : LACM Γ α) (e : LEtup Γ) : α × LEtup Γ × Int :=
  let r := m e
  (r.1, r.2.1, one + intLength Γ + r.2.2)

def add {Γ : LEnv} {τ : LTyp} (idx : Idx Γ τ) (val : LinRep τ) : LACM Γ Unit :=
  match idx with
  | .Z => fun e =>
      let z := plusv τ val e.1
      ((), (z.1, e.2), one + z.2)
  | .S i => fun e =>
      let r := add i val e.2
      (r.1, (e.1, r.2.1), r.2.2)

def scope {Γ : LEnv} {τ : LTyp} {α : Type u}
    (x : LinRep τ) (m : LACM (τ :: Γ) α) : LACM Γ (LinRep τ × α) :=
  fun e =>
    let r := m (x, e)
    let outval := r.2.1.1
    let e' := r.2.1.2
    ((outval, r.1), e', one + r.2.2)

theorem run_pure {Γ : LEnv} {α : Type u} (x : α) (env : LEtup Γ) :
  let r := run (Γ := Γ) (pure x) env
  r.2.1 = env ∧ r.2.2 = one + intLength Γ + one := by
  simp [run, pure, one]

theorem run_bind {Γ : LEnv} {α : Type u} {β : Type v}
    (m1 : LACM Γ α) (k : α → LACM Γ β × Int) (env : LEtup Γ) :
  let r := run (bind m1 k) env
  let r1 := run m1 env
  let m2 := (k r1.1).1
  let ccall := (k r1.1).2
  let r2 := run m2 r1.2.1
  r.2.1 = r2.2.1 ∧ r.2.2 = r1.2.2 + ccall + r2.2.2 - intLength Γ := by
  simp [run, bind, one] <;> omega

theorem run_add {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ) :
  let r := run (add idx val) env
  r.2.1 = addLET idx val env ∧
    r.2.2 = (2 : Int) + (plusv τ val (getLET env idx)).2 + intLength Γ := by
  induction idx with
  | Z =>
      simp [run, add, addLET, getLET, one] <;> omega
  | S i ih =>
      cases env with
      | mk head tail =>
          have h := ih val tail
          simp [run, add, addLET, getLET, one] at h ⊢
          cases h with
          | intro henv hcost =>
              constructor
              · exact Prod.ext rfl henv
              · omega

theorem run_scope {Γ : LEnv} {τ : LTyp} {α : Type u}
    (m : LACM (τ :: Γ) α) (inval : LinRep τ) (env : LEtup Γ) :
  let r1 := run (scope inval m) env
  let r2 := run m (inval, env)
  r1.1.2 = r2.1 ∧ r1.1.1 = r2.2.1.1 ∧ r1.2.1 = r2.2.1.2 ∧ r1.2.2 = r2.2.2 := by
  simp [run, scope, one] <;> omega

theorem «run-pure» {Γ : LEnv} {α : Type u} (x : α) (env : LEtup Γ) :
  let r := run (Γ := Γ) (pure x) env
  r.2.1 = env ∧ r.2.2 = one + intLength Γ + one :=
  run_pure x env

theorem «run-bind» {Γ : LEnv} {α : Type u} {β : Type v}
    (m1 : LACM Γ α) (k : α → LACM Γ β × Int) (env : LEtup Γ) :
  let r := run (bind m1 k) env
  let r1 := run m1 env
  let m2 := (k r1.1).1
  let ccall := (k r1.1).2
  let r2 := run m2 r1.2.1
  r.2.1 = r2.2.1 ∧ r.2.2 = r1.2.2 + ccall + r2.2.2 - intLength Γ :=
  run_bind m1 k env

theorem «run-add» {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ) :
  let r := run (add idx val) env
  r.2.1 = addLET idx val env ∧
    r.2.2 = (2 : Int) + (plusv τ val (getLET env idx)).2 + intLength Γ :=
  run_add idx val env

theorem «run-scope» {Γ : LEnv} {τ : LTyp} {α : Type u}
    (m : LACM (τ :: Γ) α) (inval : LinRep τ) (env : LEtup Γ) :
  let r1 := run (scope inval m) env
  let r2 := run m (inval, env)
  r1.1.2 = r2.1 ∧ r1.1.1 = r2.2.1.1 ∧ r1.2.1 = r2.2.1.2 ∧ r1.2.2 = r2.2.2 :=
  run_scope m inval env

end LACM
end EfficientChad
