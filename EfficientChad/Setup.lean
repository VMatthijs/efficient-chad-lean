import Lean.Elab.Tactic.Omega
import EfficientChad.Spec

namespace EfficientChad

universe u v

noncomputable section

def finRaise {n : Nat} (i : Fin n) : Fin (Nat.succ n) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

def «fin-raise» {n : Nat} (i : Fin n) : Fin (Nat.succ n) :=
  finRaise i

def dropAt {α : Type u} (l : List α) (i : Fin (Nat.succ l.length)) : List α :=
  List.drop i.1 l

def drop {α : Type u} (l : List α) (i : Fin (Nat.succ l.length)) : List α :=
  dropAt l i

def weakenSim {tag : PDTag} {Γ Γ' : Env tag} {σ : Typ tag}
    (f : ∀ {τ : Typ tag}, Idx Γ τ → Idx Γ' τ)
    {τ : Typ tag} (idx : Idx (σ :: Γ) τ) : Idx (σ :: Γ') τ :=
  match idx with
  | .Z => .Z
  | .S i => .S (f i)

def weakenTrans {tag : PDTag} {Γ Γ' : Env tag} {σ : Typ tag}
    (f : ∀ {τ : Typ tag}, Idx Γ τ → Term tag Γ' τ)
    {τ : Typ tag} (idx : Idx (σ :: Γ) τ) : Term tag (σ :: Γ') τ :=
  match idx with
  | .Z => .var .Z
  | .S i => sink1 (f i)

theorem phi_ge_one (τ : LTyp) (x : LinRep τ) : (1 : Int) ≤ phi τ x := by
  induction τ with
  | LUn =>
      cases x
      simp [phi, one] <;> omega
  | LR =>
      simp [phi, one] <;> omega
  | prod σ τ ihσ ihτ =>
      cases x with
      | none =>
          simp [phi, one] <;> omega
      | some xy =>
          cases xy with
          | mk xσ xτ =>
              have hσ := ihσ xσ
              have hτ := ihτ xτ
              simp [phi, one] <;> omega
  | sum σ τ ihσ ihτ =>
      cases x with
      | none =>
          simp [phi, one] <;> omega
      | some s =>
          cases s with
          | inl xσ =>
              have hσ := ihσ xσ
              simp [phi, one] <;> omega
          | inr xτ =>
              have hτ := ihτ xτ
              simp [phi, one] <;> omega

theorem phi_positive (τ : LTyp) (x : LinRep τ) : (0 : Int) ≤ phi τ x := by
  have h := phi_ge_one τ x
  omega

theorem size_positive (τ : LTyp) (x : LinRep τ) : (0 : Int) ≤ Int.ofNat (size τ x) := by
  exact Int.ofNat_nonneg (size τ x)

theorem dprim_cheap {σ τ : Typ .Pr}
    (op : Primop .Pr σ τ) (x : Rep (D1τ σ)) (dy : LinRep (D2τPrime τ)) :
  let y := eval (Val.push x Val.empty) (Term.prim (d1Prim op) (Term.var Idx.Z))
  let dx := eval (Val.push dy (Val.push x Val.empty)) (dprimPrime op)
  dx.2 - phi (D2τPrime τ) dy + phi (D2τPrime σ) dx.1 ≤ (7 : Int) * y.2 := by
  have hdy := phi_ge_one (D2τPrime τ) dy
  cases op <;>
    simp [d1Prim, dprimPrime, eval, evalprim, D1τ, D2τPrime, phi, one] at hdy ⊢ <;>
    omega

theorem eval_d1prim {σ τ : Typ .Pr} (op : Primop .Pr σ τ) (x : Rep σ) :
  evalprim (d1Prim op) (primal σ x) = primal τ (evalprim op x) := by
  cases op with
  | ADD =>
      simp [d1Prim, evalprim, primal]
  | MUL =>
      simp [d1Prim, evalprim, primal]
  | NEG =>
      simp [d1Prim, evalprim, primal]
  | LIT lit =>
      simp [d1Prim, evalprim, primal]
  | IADD =>
      simp [d1Prim, evalprim, primal]
  | IMUL =>
      simp [d1Prim, evalprim, primal]
  | INEG =>
      simp [d1Prim, evalprim, primal]
  | SIGN =>
      dsimp [d1Prim, evalprim]
      by_cases hneg : x < 0.0
      · simp [hneg, primal, D1τ, dut, dutAll, Rep]
        rfl
      · simp [hneg, primal, D1τ, dut, dutAll, Rep]
        by_cases hpos : 0.0 < x
        · simp [hpos, primal, D1τ, dut, dutAll, Rep]
          rfl
        · simp [hpos, primal, D1τ, dut, dutAll, Rep]
          rfl

theorem zero_small_phi {Γ : Env .Du} (env : Val .Du Γ) (τ : Typ .Pr) :
  phi (D2τPrime τ) (eval env (zerot τ)).1 = 1 := by
  cases τ <;> simp [zerot, eval, evalprim, D2τPrime, D2τPrimeAll, phi, one]

theorem zero_small_cost {Γ : Env .Du} (env : Val .Du Γ) (τ : Typ .Pr) :
  (eval env (zerot τ)).2 ≤ 2 := by
  cases τ <;> simp [zerot, eval, evalprim, D2τPrime, D2τPrimeAll, one] <;> omega

def «zerov'» {Γ : Env .Du} (τ : Typ .Pr) (env : Val .Du Γ) :
    {r : Rep (D2τ τ) × Int // r.2 ≤ (2 : Int)} :=
  ⟨eval env (zerot τ), zero_small_cost env τ⟩

theorem zero_small_phi_v (τ : Typ .Pr) :
  phi (D2τPrime τ) (zerov (D2τPrime τ)).1 = 1 := by
  cases τ <;> simp [zerov, D2τPrime, D2τPrimeAll, phi, one]

theorem zero_small_cost_v (τ : Typ .Pr) :
  (zerov (D2τPrime τ)).2 ≤ 2 := by
  cases τ <;> simp [zerov, D2τPrime, D2τPrimeAll, one] <;> omega

theorem run_bind2 {Γ : Env .Pr} {α : Type u} {β : Type v}
    (m1 : LACM (List.map D2τPrime Γ) α)
    (k : α → LACM (List.map D2τPrime Γ) β × Int)
    (env : LEtup (List.map D2τPrime Γ)) :
  let r := LACM.run (LACM.bind m1 k) env
  let r1 := LACM.run m1 env
  let m2 := (k r1.1).1
  let ccall := (k r1.1).2
  let r2 := LACM.run m2 r1.2.1
  r.2.1 = r2.2.1 ∧ r.2.2 = r1.2.2 + ccall + r2.2.2 - intLength Γ := by
  simpa [intLength] using (LACM.run_bind m1 k env)

theorem run_scope2 {Γ : LEnv} {α : Type u} {τ : LTyp}
    (m1 m2 : LACM (τ :: Γ) α) :
  m1 = m2 → (inval : LinRep τ) → (env : LEtup Γ) →
  let r1 := LACM.run (LACM.scope inval m1) env
  let r2 := LACM.run m2 (inval, env)
  r1.1.2 = r2.1 ∧ r1.1.1 = r2.2.1.1 ∧ r1.2.1 = r2.2.1.2 ∧ r1.2.2 = r2.2.2 := by
  intro h inval env
  cases h
  exact LACM.run_scope m1 inval env

theorem phi_of_addLET {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ) :
  phiPrime Γ (addLET idx val env) =
    phiPrime Γ env - phi τ (getLET env idx) + phi τ (getLET (addLET idx val env) idx) := by
  induction idx with
  | Z =>
      simp [addLET, getLET, phiPrime] <;> omega
  | S i ih =>
      cases env with
      | mk head tail =>
          have h := ih val tail
          simp [addLET, getLET, phiPrime] at h ⊢
          omega

theorem plusv_amortises {τ : LTyp} (a b : LinRep τ) :
  (plusv τ a b).2 - phi τ a - phi τ b + phi τ (plusv τ a b).1 ≤ 0 := by
  induction τ with
  | LUn =>
      cases a
      cases b
      simp [plusv, phi, one] <;> omega
  | LR =>
      simp [plusv, phi, one] <;> omega
  | prod σ τ ihσ ihτ =>
      cases a with
      | none =>
          simp [plusv, phi, one] <;> omega
      | some av =>
          cases b with
          | none =>
              simp [plusv, phi, one] <;> omega
          | some bv =>
              cases av with
              | mk aσ aτ =>
                  cases bv with
                  | mk bσ bτ =>
                      have hσ := ihσ aσ bσ
                      have hτ := ihτ aτ bτ
                      simp [plusv, phi, one] at hσ hτ ⊢
                      omega
  | sum σ τ ihσ ihτ =>
      cases a with
      | none =>
          cases b with
          | none =>
              simp [plusv, phi, one] <;> omega
          | some bv =>
              cases bv with
              | inl bσ =>
                  simp [plusv, phi, one] <;> omega
              | inr bτ =>
                  simp [plusv, phi, one] <;> omega
      | some av =>
          cases b with
          | none =>
              cases av with
              | inl aσ =>
                  simp [plusv, phi, one] <;> omega
              | inr aτ =>
                  simp [plusv, phi, one] <;> omega
          | some bv =>
              cases av with
              | inl aσ =>
                  cases bv with
                  | inl bσ =>
                      have hσ := ihσ aσ bσ
                      simp [plusv, phi, one] at hσ ⊢
                      omega
                  | inr bτ =>
                      have ha := phi_ge_one σ aσ
                      have hb := phi_ge_one τ bτ
                      simp [plusv, phi, one] at ha hb ⊢
                      omega
              | inr aτ =>
                  cases bv with
                  | inl bσ =>
                      have ha := phi_ge_one τ aτ
                      have hb := phi_ge_one σ bσ
                      simp [plusv, phi, one] at ha hb ⊢
                      omega
                  | inr bτ =>
                      have hτ := ihτ aτ bτ
                      simp [plusv, phi, one] at hτ ⊢
                      omega

theorem lemma_addLET_plusv {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ) :
  getLET (addLET idx val env) idx = (plusv τ val (getLET env idx)).1 := by
  induction idx with
  | Z =>
      simp [addLET, getLET]
  | S i ih =>
      cases env with
      | mk head tail =>
          simpa [addLET, getLET] using ih val tail

theorem zero_env_small_cost {Γ' : Env .Du}
    (env : Val .Du Γ') (Γ : Env .Pr) :
  (eval env (zeroEnvTerm Γ)).2 ≤ (1 : Int) + (3 : Int) * intLength Γ := by
  induction Γ with
  | nil =>
      simp [zeroEnvTerm, eval, one, intLength] <;> omega
  | cons τ Γ ih =>
      have hz := zero_small_cost env τ
      have hrest := ih
      simp [zeroEnvTerm, eval, one, intLength] at hz hrest ⊢
      omega

theorem «φ-positive» (τ : LTyp) (x : LinRep τ) : (0 : Int) ≤ phi τ x :=
  phi_positive τ x

theorem «size-positive» (τ : LTyp) (x : LinRep τ) : (0 : Int) ≤ Int.ofNat (size τ x) :=
  size_positive τ x

theorem «dprim-cheap» {σ τ : Typ .Pr}
    (op : Primop .Pr σ τ) (x : Rep (D1τ σ)) (dy : LinRep (D2τPrime τ)) :
  let y := eval (Val.push x Val.empty) (Term.prim (d1Prim op) (Term.var Idx.Z))
  let dx := eval (Val.push dy (Val.push x Val.empty)) (dprimPrime op)
  dx.2 - phi (D2τPrime τ) dy + phi (D2τPrime σ) dx.1 ≤ (7 : Int) * y.2 :=
  dprim_cheap op x dy

theorem «eval-d1prim» {σ τ : Typ .Pr} (op : Primop .Pr σ τ) (x : Rep σ) :
  evalprim (d1Prim op) (primal σ x) = primal τ (evalprim op x) :=
  eval_d1prim op x

theorem «zero-small-φ» {Γ : Env .Du} (env : Val .Du Γ) (τ : Typ .Pr) :
  phi (D2τPrime τ) (eval env (zerot τ)).1 = 1 :=
  zero_small_phi env τ

theorem «zero-small-cost» {Γ : Env .Du} (env : Val .Du Γ) (τ : Typ .Pr) :
  (eval env (zerot τ)).2 ≤ 2 :=
  zero_small_cost env τ

theorem «zero-small-φ-v» (τ : Typ .Pr) :
  phi (D2τPrime τ) (zerov (D2τPrime τ)).1 = 1 :=
  zero_small_phi_v τ

theorem «zero-small-cost-v» (τ : Typ .Pr) :
  (zerov (D2τPrime τ)).2 ≤ 2 :=
  zero_small_cost_v τ

theorem «run-bind2» {Γ : Env .Pr} {α : Type u} {β : Type v}
    (m1 : LACM (List.map D2τPrime Γ) α)
    (k : α → LACM (List.map D2τPrime Γ) β × Int)
    (env : LEtup (List.map D2τPrime Γ)) :
  let r := LACM.run (LACM.bind m1 k) env
  let r1 := LACM.run m1 env
  let m2 := (k r1.1).1
  let ccall := (k r1.1).2
  let r2 := LACM.run m2 r1.2.1
  r.2.1 = r2.2.1 ∧ r.2.2 = r1.2.2 + ccall + r2.2.2 - intLength Γ :=
  run_bind2 m1 k env

theorem «run-scope2» {Γ : LEnv} {α : Type u} {τ : LTyp}
    (m1 m2 : LACM (τ :: Γ) α) :
  m1 = m2 → (inval : LinRep τ) → (env : LEtup Γ) →
  let r1 := LACM.run (LACM.scope inval m1) env
  let r2 := LACM.run m2 (inval, env)
  r1.1.2 = r2.1 ∧ r1.1.1 = r2.2.1.1 ∧ r1.2.1 = r2.2.1.2 ∧ r1.2.2 = r2.2.2 :=
  run_scope2 m1 m2

theorem «φ-of-addLEτ» {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ) :
  phiPrime Γ (addLET idx val env) =
    phiPrime Γ env - phi τ (getLET env idx) + phi τ (getLET (addLET idx val env) idx) :=
  phi_of_addLET idx val env

theorem «plusv-amortises» {τ : LTyp} (a b : LinRep τ) :
  (plusv τ a b).2 - phi τ a - phi τ b + phi τ (plusv τ a b).1 ≤ 0 :=
  plusv_amortises a b

theorem «lemma-addLEτ-plusv» {Γ : LEnv} {τ : LTyp}
    (idx : Idx Γ τ) (val : LinRep τ) (env : LEtup Γ) :
  getLET (addLET idx val env) idx = (plusv τ val (getLET env idx)).1 :=
  lemma_addLET_plusv idx val env

theorem «zero-env-small-cost» {Γ' : Env .Du}
    (env : Val .Du Γ') (Γ : Env .Pr) :
  (eval env (zeroEnvTerm Γ)).2 ≤ (1 : Int) + (3 : Int) * intLength Γ :=
  zero_env_small_cost env Γ

end

end EfficientChad
