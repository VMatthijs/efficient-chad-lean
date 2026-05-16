import Lean.Elab.Tactic.Omega
import EfficientChad.Setup
import EfficientChad.Lemmas
import EfficientChad.ChadPreservesPrimal

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace EfficientChad

universe u v

@[irreducible] def th1Bound {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ))
    (t : Term .Pr Γ τ) : Prop :=
  let ch := eval (primalVal env) (chad t)
  let bp := ch.1.2
  let crun := ch.2
  let bpCall := bp ctg
  let envf := bpCall.1
  let ccall := bpCall.2
  let mon := LACM.run envf denvin
  let denvout := mon.2.1
  let cmonad := mon.2.2
  crun + ccall + cmonad
    - phi (D2τPrime τ) ctg
    - phiPrime (List.map D2τPrime Γ) denvin
    + phiPrime (List.map D2τPrime Γ) denvout
    - intLength Γ
    ≤ (34 : Int) * cost env t

theorem th1Bound_of_TH1 (H : TH1_STATEMENT) {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ))
    (t : Term .Pr Γ τ) : th1Bound env ctg denvin t := by
  unfold th1Bound
  exact H env ctg denvin t

theorem TH1_of_th1Bound
    (H : ∀ {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (ctg : Rep (D2τ τ))
      (denvin : LEtup (List.map D2τPrime Γ))
      (t : Term .Pr Γ τ), th1Bound env ctg denvin t) :
    TH1_STATEMENT := by
  unfold TH1_STATEMENT
  intro Γ τ env ctg denvin t
  have h := H env ctg denvin t
  unfold th1Bound at h
  exact h

/-- Primitive cost laws for the array cases of the *core* TH1 proof.

The scalar branches are proved constructively below.  The array branches are
kept as the primitive random-access-array/recorded-fold cost model, but the laws
are no longer whole-program array TH1 assumptions: every method receives the
recursive TH1 hypotheses for its immediate subterms.  This is the same shape as
the scalar cases such as `th1_pair_case` and `th1_case_case`, and makes explicit
that the remaining assumptions are the direct array-work bounds plus affine use
of the subterm backpropagators. -/
class CoreArrayCostLaws extends CoreArrayPrimalLaws : Prop where
  th1_arrayBuild_case {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (n : Term .Pr Γ .Inte)
      (body : Term .Pr (.Inte :: Γ) τ)
      (ih_n : ∀ (ctgN : Rep (D2τ (.Inte : Typ .Pr)))
          (denvinN : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgN denvinN n)
      (ih_body : ∀ (envI : Val .Pr (.Inte :: Γ))
          (ctgBody : Rep (D2τ τ))
          (denvinBody : LEtup (List.map D2τPrime (.Inte :: Γ))),
        th1Bound envI ctgBody denvinBody body)
      (ctg : Rep (D2τ (.array τ)))
      (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.arrayBuild n body)

  th1_arrayIndex_case {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (xs : Term .Pr Γ (.array τ))
      (i : Term .Pr Γ .Inte)
      (ih_xs : ∀ (ctgXs : Rep (D2τ (.array τ)))
          (denvinXs : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgXs denvinXs xs)
      (ih_i : ∀ (ctgI : Rep (D2τ (.Inte : Typ .Pr)))
          (denvinI : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgI denvinI i)
      (ctg : Rep (D2τ τ))
      (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.arrayIndex xs i)

  th1_arrayFold_case {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (body : Term .Pr (.prod τ τ :: Γ) τ)
      (xs : Term .Pr Γ (.array τ))
      (ih_body : ∀ (envP : Val .Pr (.prod τ τ :: Γ))
          (ctgBody : Rep (D2τ τ))
          (denvinBody : LEtup (List.map D2τPrime (.prod τ τ :: Γ))),
        th1Bound envP ctgBody denvinBody body)
      (ih_xs : ∀ (ctgXs : Rep (D2τ (.array τ)))
          (denvinXs : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgXs denvinXs xs)
      (ctg : Rep (D2τ τ))
      (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.arrayFold body xs)

variable [CoreArrayCostLaws]

theorem zerov_phi_eq_one (τ : LTyp) : phi τ (zerov τ).1 = (1 : Int) := by
  cases τ <;> simp [zerov, phi, Bag.collectCost, one]

theorem bag_collectCost_le_size {α : Type u} (b : Bag α) :
    Bag.collectCost b ≤ Int.ofNat (Bag.size b) := by
  induction b with
  | empty =>
      simp [Bag.collectCost, Bag.size, one]
  | one x =>
      simp [Bag.collectCost, Bag.size, one]
  | plus xs ys ihx ihy =>
      simp [Bag.collectCost, Bag.size, one] at ihx ihy ⊢
      omega
  | array xs =>
      simp [Bag.collectCost, Bag.size, intLength, one]

theorem phi_less_size : (τ : Typ .Pr) → (x : LinRep (D2τPrime τ)) →
    phi (D2τPrime τ) x ≤ Int.ofNat (size (D2τPrime τ) x)
  | .Un, x => by
      cases x
      simp [D2τPrime, D2τPrimeAll, phi, size, one]
  | .Inte, x => by
      cases x
      simp [D2τPrime, D2τPrimeAll, phi, size, one]
  | .R, x => by
      simp [D2τPrime, D2τPrimeAll, phi, size, one]
  | .prod σ τ, x => by
      cases x with
      | none =>
          simp [D2τPrime, D2τPrimeAll, phi, size, one]
      | some xy =>
          cases xy with
          | mk xσ xτ =>
              have hσ := phi_less_size σ xσ
              have hτ := phi_less_size τ xτ
              have h := «lemma-φ-less-size»
                (phi (D2τPrime σ) xσ)
                (phi (D2τPrime τ) xτ)
                (Int.ofNat (size (D2τPrime σ) xσ)) hσ
                (Int.ofNat (size (D2τPrime τ) xτ)) hτ
              simp [D2τPrime, D2τPrimeAll, phi, size, one] at h ⊢
              omega
  | .sum σ τ, x => by
      cases x with
      | none =>
          simp [D2τPrime, D2τPrimeAll, phi, size, one]
      | some s =>
          cases s with
          | inl xσ =>
              have hσ := phi_less_size σ xσ
              simp [D2τPrime, D2τPrimeAll, phi, size, one] at hσ ⊢
              omega
          | inr xτ =>
              have hτ := phi_less_size τ xτ
              simp [D2τPrime, D2τPrimeAll, phi, size, one] at hτ ⊢
              omega
  | .array τ, x => by
      simpa [D2τPrime, D2τPrimeAll, phi, size] using bag_collectCost_le_size x

theorem phi_zero_bound (τ : LTyp) (x : LinRep τ) :
    phi τ (zerov τ).1 ≤ phi τ x := by
  have hzero := zerov_phi_eq_one τ
  have hx := phi_ge_one τ x
  omega

theorem phi_zerot_bound {Γ : Env .Du} {env : Val .Du Γ}
    (τ : Typ .Pr) (x : LinRep (D2τPrime τ)) :
    phi (D2τPrime τ) (eval env (zerot τ)).1 ≤ phi (D2τPrime τ) x := by
  have hzero := zero_small_phi env τ
  have hx := phi_ge_one (D2τPrime τ) x
  omega

theorem phi_zero_env_bound {Γ' : Env .Du} (env : Val .Du Γ')
    (Γ : Env .Pr) (tup : LEtup (List.map D2τPrime Γ)) :
    phiPrime (List.map D2τPrime Γ)
        (repLEτToLEtup (List.map D2τPrime Γ) (eval env (zeroEnvTerm Γ)).1)
      ≤ phiPrime (List.map D2τPrime Γ) tup := by
  revert tup
  induction Γ with
  | nil =>
      intro tup
      cases tup
      simp [zeroEnvTerm, eval, repLEτToLEtup, phiPrime]
  | cons τ Γ ih =>
      intro tup
      cases tup with
      | mk head tail =>
          have hhead := phi_zerot_bound (env := env) τ head
          have htail := ih tail
          simp [zeroEnvTerm, eval, repLEτToLEtup, phiPrime] at hhead htail ⊢
          omega

theorem «φ-less-size» (τ : Typ .Pr) (x : LinRep (D2τPrime τ)) :
    phi (D2τPrime τ) x ≤ Int.ofNat (size (D2τPrime τ) x) :=
  phi_less_size τ x

theorem «φ-zero-bound» (τ : LTyp) (x : LinRep τ) :
    phi τ (zerov τ).1 ≤ phi τ x :=
  phi_zero_bound τ x

theorem «φ-zerot-bound» {Γ : Env .Du} {env : Val .Du Γ}
    (τ : Typ .Pr) (x : LinRep (D2τPrime τ)) :
    phi (D2τPrime τ) (eval env (zerot τ)).1 ≤ phi (D2τPrime τ) x :=
  phi_zerot_bound (env := env) τ x

theorem «φ-zero-env-bound» {Γ' : Env .Du} (env : Val .Du Γ')
    (Γ : Env .Pr) (tup : LEtup (List.map D2τPrime Γ)) :
    phiPrime (List.map D2τPrime Γ)
        (repLEτToLEtup (List.map D2τPrime Γ) (eval env (zeroEnvTerm Γ)).1)
      ≤ phiPrime (List.map D2τPrime Γ) tup :=
  phi_zero_env_bound env Γ tup

theorem th1_unit_case {Γ : Env .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ (.Un : Typ .Pr)))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    let ch := eval (primalVal env) (chad (Term.unit : Term .Pr Γ (.Un)))
    let bp := ch.1.2
    let crun := ch.2
    let bpCall := bp ctg
    let envf := bpCall.1
    let ccall := bpCall.2
    let mon := LACM.run envf denvin
    let denvout := mon.2.1
    let cmonad := mon.2.2
    crun + ccall + cmonad
      - phi (D2τPrime (.Un : Typ .Pr)) ctg
      - phiPrime (List.map D2τPrime Γ) denvin
      + phiPrime (List.map D2τPrime Γ) denvout
      - intLength Γ
      ≤ (34 : Int) * cost env (Term.unit : Term .Pr Γ (.Un)) := by
  cases ctg
  simp [chad, eval, lamwith, buildInj, buildIdx, LACM.run, LACM.pure,
    D2τ, D2τPrime, phi, phiPrime, cost, intLength, one, Int.add_comm, Int.add_left_comm, Int.add_assoc]
  omega

theorem th1_var_case {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (idx : Idx Γ τ)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    let ch := eval (primalVal env) (chad (Term.var idx : Term .Pr Γ τ))
    let bp := ch.1.2
    let crun := ch.2
    let bpCall := bp ctg
    let envf := bpCall.1
    let ccall := bpCall.2
    let mon := LACM.run envf denvin
    let denvout := mon.2.1
    let cmonad := mon.2.2
    crun + ccall + cmonad
      - phi (D2τPrime τ) ctg
      - phiPrime (List.map D2τPrime Γ) denvin
      + phiPrime (List.map D2τPrime Γ) denvout
      - intLength Γ
      ≤ (34 : Int) * cost env (Term.var idx : Term .Pr Γ τ) := by
  let lidx : Idx (List.map D2τPrime Γ) (D2τPrime τ) := convIdx D2τPrime idx
  let run := LACM.run (LACM.add lidx ctg) denvin
  let cmonad : Int := run.2.2
  let φd : Int := phi (D2τPrime τ) ctg
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) (addLET lidx ctg denvin)
  let φeout : Int := phiPrime (List.map D2τPrime Γ) run.2.1
  let envlen : Int := intLength Γ
  let cplus : Int := (plusv (D2τPrime τ) ctg (getLET denvin lidx)).2
  let envlen' : Int := intLength (List.map D2τPrime Γ)

  have hrun_env : run.2.1 = addLET lidx ctg denvin := by
    dsimp [run]
    exact (LACM.run_add lidx ctg denvin).1
  have hrun_cost : cmonad = (2 : Int) + cplus + envlen' := by
    dsimp [cmonad, run, cplus, envlen']
    exact (LACM.run_add lidx ctg denvin).2
  have plenmap : envlen = envlen' := by
    dsimp [envlen, envlen', intLength]
    simp
  have p1 : φeout = φe2 := by
    dsimp [φeout, φe2]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) hrun_env
  have pφaddlet :
      φe2 = φe1
        - phi (D2τPrime τ) (getLET denvin lidx)
        + phi (D2τPrime τ) (getLET (addLET lidx ctg denvin) lidx) := by
    dsimp [φe2, φe1]
    exact phi_of_addLET lidx ctg denvin
  have pplus :
      cplus - φd
        - phi (D2τPrime τ) (getLET denvin lidx)
        + phi (D2τPrime τ)
            (plusv (D2τPrime τ) ctg (getLET denvin lidx)).1
        ≤ 0 := by
    dsimp [cplus, φd]
    exact plusv_amortises ctg (getLET denvin lidx)
  have paddlet :
      phi (D2τPrime τ) (getLET (addLET lidx ctg denvin) lidx)
        = phi (D2τPrime τ)
            (plusv (D2τPrime τ) ctg (getLET denvin lidx)).1 := by
    exact congrArg (phi (D2τPrime τ)) (lemma_addLET_plusv lidx ctg denvin)

  have leaf :
      (5 : Int) + cmonad - φd - φe1 + φeout - envlen ≤ 34 :=
    «lemma-var» cmonad φd φe1 φe2 φeout p1 envlen cplus envlen'
      hrun_cost plenmap
      (phi (D2τPrime τ) (getLET denvin lidx))
      (phi (D2τPrime τ) (getLET (addLET lidx ctg denvin) lidx))
      pφaddlet
      (phi (D2τPrime τ)
        (plusv (D2τPrime τ) ctg (getLET denvin lidx)).1)
      pplus paddlet

  simpa only [chad, eval, lamwith, buildInj, buildValFromInj, valprj, cost,
    D2τ, run, cmonad, φd, φe1, φeout, envlen, one]
    using leaf

theorem th1_unit_case_bound {Γ : Env .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ (.Un : Typ .Pr)))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.unit : Term .Pr Γ (.Un)) := by
  unfold th1Bound
  exact th1_unit_case env ctg denvin

theorem th1_var_case_bound {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (idx : Idx Γ τ)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.var idx : Term .Pr Γ τ) := by
  unfold th1Bound
  exact th1_var_case env idx ctg denvin

theorem th1_prim_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (op : Primop .Pr σ τ)
    (e : Term .Pr Γ σ)
    (ih_e : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.prim op e) := by
  let out1 := eval (primalVal env) (chad e)
  let primal1 : Rep (D1τ σ) := out1.1.1
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let tailEnv : Env .Du :=
    D2τ τ :: (.prod (D1τ σ) (.arr (D2τ σ) (D2Γ Γ))) :: []
  let w : Weakening (D2τ τ :: D1τ σ :: []) (D2τ τ :: D1τ σ :: tailEnv) :=
    Weakening.WCopy (Weakening.WCopy (Weakening.WCut (Γ' := tailEnv)))
  let smallEnv : Val .Du (D2τ τ :: D1τ σ :: []) :=
    Val.push ctg (Val.push primal1 Val.empty)
  let subenv1 : Val .Du (D2τ τ :: D1τ σ :: tailEnv) :=
    Val.push ctg (Val.push primal1 (Val.push ctg (Val.push out1.1 Val.empty)))
  let dprimSmall := eval smallEnv (dprimPrime op)
  let dprimLarge := eval subenv1 (sink w (dprimPrime op))
  let dx : Rep (D2τ σ) := dprimLarge.1
  let cdprim : Int := dprimLarge.2
  let mf1 := bp1 dx
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φdx : Int := phi (D2τPrime σ) dx
  let φd : Int := phi (D2τPrime τ) ctg
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have hsink_dprim : sinksTo w smallEnv subenv1 := by
    dsimp [w, smallEnv, subenv1, tailEnv]
    intro ρ idx
    cases idx with
    | Z => rfl
    | S i =>
        cases i with
        | Z => rfl
        | S j => cases j

  have hcheap0 := dprim_cheap op primal1 ctg
  have lem1_pre :
      dprimSmall.2 - φd + phi (D2τPrime σ) dprimSmall.1 ≤ (7 : Int) * (2 : Int) := by
    dsimp [dprimSmall, smallEnv, φd, primal1]
    simpa only [eval, one] using hcheap0
  have lem1 :
      dprimSmall.2 - φd + phi (D2τPrime σ) dprimSmall.1 ≤ 14 := by
    omega

  have hsmall_large : dprimSmall = dprimLarge := by
    dsimp [dprimSmall, dprimLarge]
    exact eval_sink_commute smallEnv subenv1 w hsink_dprim (dprimPrime op)

  have lem3 : cdprim - φd + φdx ≤ 14 := by
    dsimp [cdprim, φdx, dx]
    rw [← hsmall_large]
    exact lem1

  have k1 :
      crun1 + ccall1 + cmonad1 - φdx - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e dx denvin
    unfold th1Bound at hih
    simpa only [out1, crun1, bp1, mf1, ccall1, run1, cmonad1, denv2,
      φdx, φe1, φe2, envlen, evc1, cost] using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + (3 + (2 + cdprim)) + ccall1)
        + cmonad1 - φd - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-prim» crun1 cdprim ccall1 cmonad1 φdx φd φe1 φe2 evc1
      lem3 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, primal1, bp1, crun1, dprim, lamwith,
    buildInj, buildIdx, listGet, finZero, sink1, sink, sinkPr, sinkDu, weakenVar,
    buildValFromInj, valprj, tailEnv, w, smallEnv,
    subenv1, dprimLarge, dx, cdprim, mf1, ccall1, run1, denv2, cmonad1,
    φdx, φd, φe1, φe2, evc1, envlen, D2τ, one]
    using leaf

theorem th1_pair_nothing_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr Γ τ)
    (ih1 : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e1)
    (ih2 : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e2)
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (none : Rep (D2τ (.prod σ τ))) denvin
      (Term.pair e1 e2 : Term .Pr Γ (.prod σ τ)) := by
  let out1 := eval (primalVal env) (chad e1)
  let out2 := eval (primalVal env) (chad e2)
  let bp1 := out1.1.2
  let bp2 := out2.1.2
  let crun1 : Int := out1.2
  let crun2 : Int := out2.2
  let z1 := zerov (D2τPrime σ)
  let z2 := zerov (D2τPrime τ)
  let ctg1 : Rep (D2τ σ) := z1.1
  let ctg2 : Rep (D2τ τ) := z2.1
  let czero1 : Int := z1.2
  let czero2 : Int := z2.2
  let mf1 := bp1 ctg1
  let mf2 := bp2 ctg2
  let ccall1 : Int := mf1.2
  let ccall2 : Int := mf2.2
  let mf := LACM.bind mf1.1 (fun _ => (mf2.1, one))
  let runOut := LACM.run mf denvin
  let denvout := runOut.2.1
  let cmonad : Int := runOut.2.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let run2 := LACM.run mf2.1 denv2
  let denv3 := run2.2.1
  let cmonad2 : Int := run2.2.2
  let φd1 : Int := phi (D2τPrime σ) ctg1
  let φd2 : Int := phi (D2τPrime τ) ctg2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φe3 : Int := phiPrime (List.map D2τPrime Γ) denv3
  let φeout : Int := phiPrime (List.map D2τPrime Γ) denvout
  let evc1 : Int := cost env e1
  let evc2 : Int := cost env e2
  let envlen : Int := intLength Γ

  have pzero1 : czero1 ≤ 2 := by
    dsimp [czero1, z1]
    exact zero_small_cost_v σ
  have pzero2 : czero2 ≤ 2 := by
    dsimp [czero2, z2]
    exact zero_small_cost_v τ
  have pφd1 : φd1 = 1 := by
    dsimp [φd1, ctg1, z1]
    exact zero_small_phi_v σ
  have pφd2 : φd2 = 1 := by
    dsimp [φd2, ctg2, z2]
    exact zero_small_phi_v τ

  have runbindres := run_bind2 (Γ := Γ) mf1.1 (fun _ => (mf2.1, one)) denvin
  have prunbind1 : denvout = denv3 := by
    dsimp [denvout, denv3, runOut, run2, denv2, mf] at runbindres ⊢
    exact runbindres.1
  have prunbind2 : cmonad = cmonad1 + 1 + cmonad2 - envlen := by
    dsimp [cmonad, cmonad1, cmonad2, runOut, run1, run2, denv2, mf, envlen]
    simpa only [one] using runbindres.2
  have pφdenvout : φeout = φe3 := by
    dsimp [φeout, φe3]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) prunbind1

  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih1 ctg1 denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, mf1, ccall1, run1, denv2, cmonad1,
      φd1, φe1, φe2, evc1, envlen, cost, D2τ, D2τPrime, phi, one]
      using hih
  have k2 :
      crun2 + ccall2 + cmonad2 - φd2 - φe2 + φe3 - envlen
        ≤ (34 : Int) * evc2 := by
    have hih := ih2 ctg2 denv2
    unfold th1Bound at hih
    simpa only [out2, bp2, crun2, mf2, ccall2, run2, denv3, cmonad2,
      φd2, φe2, φe3, evc2, envlen, cost, D2τ, D2τPrime, phi, one]
      using hih

  have leaf :
      (1 : Int) + (1 + crun1 + crun2) + 10
        + (1 + (4 + (2 + czero2) + ccall2)
          + (1 + (4 + (2 + czero1) + ccall1) + 2))
        + cmonad - (1 + 0) - φe1 + φeout - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1 + evc2) :=
    «lemma-pair-nothing» crun1 crun2 czero1 czero2 ccall1 ccall2
      cmonad cmonad1 cmonad2 φd1 φd2 φe1 φe2 φe3 φeout evc1 evc2
      pzero1 pzero2 pφd1 pφd2 pφdenvout envlen prunbind2 k1 k2

  unfold th1Bound
  simpa only [chad, eval, cost, out1, out2, bp1, bp2, crun1, crun2, z1, z2,
    ctg1, ctg2, czero1, czero2, mf1, mf2, ccall1, ccall2, mf,
    runOut, denvout, cmonad, run1, denv2, cmonad1, run2, denv3,
    cmonad2, φd1, φd2, φe1, φe2, φe3, φeout, evc1, evc2, envlen,
    thenevm, lamwith, buildInj, buildIdx, buildValFromInj, valprj,
    listGet, finZero, sink, sink1, sinkDu, sinkPr, weakenVar, d2lfstTerm, d2lsndTerm, d2lpairTerm, D2τ, D2τPrime, D2τPrimeAll, phi, one]
    using leaf

theorem th1_pair_nothing_case_bound {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr Γ τ)
    (ih1 : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e1)
    (ih2 : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e2)
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (none : Rep (D2τ (.prod σ τ))) denvin
      (Term.pair e1 e2 : Term .Pr Γ (.prod σ τ)) :=
  th1_pair_nothing_case env e1 e2 ih1 ih2 denvin

theorem th1_pair_just_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr Γ τ)
    (ih1 : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e1)
    (ih2 : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e2)
    (ctg1 : Rep (D2τ σ))
    (ctg2 : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (some (ctg1, ctg2) : Rep (D2τ (.prod σ τ))) denvin
      (Term.pair e1 e2 : Term .Pr Γ (.prod σ τ)) := by
  let out1 := eval (primalVal env) (chad e1)
  let out2 := eval (primalVal env) (chad e2)
  let bp1 := out1.1.2
  let bp2 := out2.1.2
  let crun1 : Int := out1.2
  let crun2 : Int := out2.2
  let mf1 := bp1 ctg1
  let mf2 := bp2 ctg2
  let ccall1 : Int := mf1.2
  let ccall2 : Int := mf2.2
  let mf := LACM.bind mf1.1 (fun _ => (mf2.1, one))
  let runOut := LACM.run mf denvin
  let denvout := runOut.2.1
  let cmonad : Int := runOut.2.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let run2 := LACM.run mf2.1 denv2
  let denv3 := run2.2.1
  let cmonad2 : Int := run2.2.2
  let φd1 : Int := phi (D2τPrime σ) ctg1
  let φd2 : Int := phi (D2τPrime τ) ctg2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φe3 : Int := phiPrime (List.map D2τPrime Γ) denv3
  let φeout : Int := phiPrime (List.map D2τPrime Γ) denvout
  let evc1 : Int := cost env e1
  let evc2 : Int := cost env e2
  let envlen : Int := intLength Γ

  have runbindres := run_bind2 (Γ := Γ) mf1.1 (fun _ => (mf2.1, one)) denvin
  have prunbind1 : denvout = denv3 := by
    dsimp [denvout, denv3, runOut, run2, denv2, mf] at runbindres ⊢
    exact runbindres.1
  have prunbind2 : cmonad = cmonad1 + 1 + cmonad2 - envlen := by
    dsimp [cmonad, cmonad1, cmonad2, runOut, run1, run2, denv2, mf, envlen]
    simpa only [one] using runbindres.2
  have pφdenvout : φeout = φe3 := by
    dsimp [φeout, φe3]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) prunbind1

  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih1 ctg1 denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, mf1, ccall1, run1, denv2, cmonad1,
      φd1, φe1, φe2, evc1, envlen, cost, D2τ, D2τPrime, phi, one]
      using hih
  have k2 :
      crun2 + ccall2 + cmonad2 - φd2 - φe2 + φe3 - envlen
        ≤ (34 : Int) * evc2 := by
    have hih := ih2 ctg2 denv2
    unfold th1Bound at hih
    simpa only [out2, bp2, crun2, mf2, ccall2, run2, denv3, cmonad2,
      φd2, φe2, φe3, evc2, envlen, cost, D2τ, D2τPrime, phi, one]
      using hih

  have leaf :
      (1 : Int) + (1 + crun1 + crun2) + 10
        + (1 + (6 + ccall2) + (1 + (6 + ccall1) + 2))
        + cmonad - (1 + φd1 + φd2) - φe1 + φeout - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1 + evc2) :=
    «lemma-pair-just» crun1 crun2 ccall1 ccall2 cmonad cmonad1 cmonad2
      φd1 φd2 φe1 φe2 φe3 φeout evc1 evc2 pφdenvout envlen
      prunbind2 k1 k2

  unfold th1Bound
  simpa only [chad, eval, cost, out1, out2, bp1, bp2, crun1, crun2,
    mf1, mf2, ccall1, ccall2, mf, runOut, denvout, cmonad,
    run1, denv2, cmonad1, run2, denv3, cmonad2, φd1, φd2,
    φe1, φe2, φe3, φeout, evc1, evc2, envlen, thenevm,
    lamwith, buildInj, buildIdx, buildValFromInj, valprj, listGet,
    finZero, sink, sink1, sinkDu, sinkPr, weakenVar, d2lfstTerm, d2lsndTerm, d2lpairTerm, D2τ, D2τPrime, D2τPrimeAll, phi, one]
    using leaf

theorem th1_pair_just_case_bound {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr Γ τ)
    (ih1 : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e1)
    (ih2 : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e2)
    (ctg1 : Rep (D2τ σ))
    (ctg2 : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (some (ctg1, ctg2) : Rep (D2τ (.prod σ τ))) denvin
      (Term.pair e1 e2 : Term .Pr Γ (.prod σ τ)) :=
  th1_pair_just_case env e1 e2 ih1 ih2 ctg1 ctg2 denvin

theorem th1_fst_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ (.prod σ τ))
    (ih_e : ∀ (ctgστ : Rep (D2τ (.prod σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e)
    (ctg : Rep (D2τ σ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.fstE e) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let subenv1 : Val .Du
      (D2τ σ :: (.prod (D1τ (.prod σ τ)) (.arr (D2τ (.prod σ τ)) (D2Γ Γ))) :: []) :=
    Val.push ctg (Val.push out1.1 Val.empty)
  let zeroEval := eval subenv1 (zerot τ)
  let zerores : Rep (D2τ τ) := zeroEval.1
  let czero : Int := zeroEval.2
  let ctg1 : Rep (D2τ (.prod σ τ)) := some (ctg, zerores)
  let mf1 := bp1 ctg1
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φd : Int := phi (D2τPrime σ) ctg
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime τ) zerores
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have pzero : czero ≤ (2 : Int) := by
    dsimp [czero, zeroEval]
    exact zero_small_cost subenv1 τ
  have pφd1 : φd1 = (1 : Int) := by
    dsimp [φd1, zerores, zeroEval]
    exact zero_small_phi subenv1 τ
  have k1 :
      crun1 + ccall1 + cmonad1 - ((1 : Int) + φd + φd1) - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e ctg1 denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, ctg1, mf1, ccall1, run1, denv2, cmonad1,
      φd, φe1, φe2, φd1, envlen, evc1, cost, D2τ, D2τPrime, phi, one]
      using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + (2 + czero) + ccall1)
        + cmonad1 - φd - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-fst» crun1 czero ccall1 cmonad1 φd φe1 φe2 φd1 evc1
      pzero pφd1 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, subenv1, zeroEval, zerores,
    czero, ctg1, mf1, ccall1, run1, denv2, cmonad1, φd, φe1, φe2,
    φd1, evc1, envlen, D2τ, D2τPrime, phi, lamwith, buildInj,
    buildIdx, listGet, finZero, valprj, buildValFromInj, one]
    using leaf

theorem th1_fst_case_bound {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ (.prod σ τ))
    (ih_e : ∀ (ctgστ : Rep (D2τ (.prod σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e)
    (ctg : Rep (D2τ σ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.fstE e) :=
  th1_fst_case env e ih_e ctg denvin

theorem th1_snd_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ (.prod σ τ))
    (ih_e : ∀ (ctgστ : Rep (D2τ (.prod σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.sndE e) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let subenv1 : Val .Du
      (D2τ τ :: (.prod (D1τ (.prod σ τ)) (.arr (D2τ (.prod σ τ)) (D2Γ Γ))) :: []) :=
    Val.push ctg (Val.push out1.1 Val.empty)
  let zeroEval := eval subenv1 (zerot σ)
  let zerores : Rep (D2τ σ) := zeroEval.1
  let czero : Int := zeroEval.2
  let ctg1 : Rep (D2τ (.prod σ τ)) := some (zerores, ctg)
  let mf1 := bp1 ctg1
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φd : Int := phi (D2τPrime τ) ctg
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime σ) zerores
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have pzero : czero ≤ (2 : Int) := by
    dsimp [czero, zeroEval]
    exact zero_small_cost subenv1 σ
  have pφd1 : φd1 = (1 : Int) := by
    dsimp [φd1, zerores, zeroEval]
    exact zero_small_phi subenv1 σ
  have k1 :
      crun1 + ccall1 + cmonad1 - ((1 : Int) + φd1 + φd) - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e ctg1 denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, ctg1, mf1, ccall1, run1, denv2, cmonad1,
      φd, φe1, φe2, φd1, envlen, evc1, cost, D2τ, D2τPrime, phi, one]
      using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + ((1 : Int) + czero + 1) + ccall1)
        + cmonad1 - φd - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-snd» crun1 czero ccall1 cmonad1 φd φe1 φe2 φd1 evc1
      pzero pφd1 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, subenv1, zeroEval, zerores,
    czero, ctg1, mf1, ccall1, run1, denv2, cmonad1, φd, φe1, φe2,
    φd1, evc1, envlen, D2τ, D2τPrime, phi, lamwith, buildInj,
    buildIdx, listGet, finZero, valprj, buildValFromInj, one]
    using leaf

theorem th1_snd_case_bound {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ (.prod σ τ))
    (ih_e : ∀ (ctgστ : Rep (D2τ (.prod σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.sndE e) :=
  th1_snd_case env e ih_e ctg denvin

theorem th1_inl_nothing_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ σ)
    (ih_e : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e)
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (none : Rep (D2τ (.sum σ τ))) denvin
      (Term.inl (τ := τ) e : Term .Pr Γ (.sum σ τ)) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let z := zerov (D2τPrime σ)
  let zerores : Rep (D2τ σ) := z.1
  let czero : Int := z.2
  let mf1 := bp1 zerores
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime σ) zerores
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have pzero : φd1 = 1 := by
    dsimp [φd1, zerores, z]
    exact zero_small_phi_v σ
  have pφd1 : czero ≤ 2 := by
    dsimp [czero, z]
    exact zero_small_cost_v σ
  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e zerores denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, zerores, mf1, ccall1, run1, denv2,
      cmonad1, φe1, φe2, φd1, evc1, envlen, cost, D2τ, D2τPrime,
      phi, one] using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + (2 + czero) + ccall1)
        + cmonad1 - (1 + 0) - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-inl-nothing» crun1 czero ccall1 cmonad1 φe1 φe2 φd1 evc1
      pzero pφd1 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, z, zerores, czero, mf1,
    ccall1, run1, denv2, cmonad1, φe1, φe2, φd1, evc1, envlen,
    lamwith, buildInj, buildIdx, buildValFromInj, valprj, listGet,
    finZero, D2τ, D2τPrime, phi, one]
    using leaf

theorem th1_inl_inj1_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ σ)
    (ih_e : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e)
    (ctg : Rep (D2τ σ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (some (Sum.inl ctg) : Rep (D2τ (.sum σ τ))) denvin
      (Term.inl (τ := τ) e : Term .Pr Γ (.sum σ τ)) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let mf1 := bp1 ctg
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime σ) ctg
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e ctg denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, mf1, ccall1, run1, denv2, cmonad1,
      φe1, φe2, φd1, evc1, envlen, cost, D2τ, D2τPrime, phi, one]
      using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (5 + ccall1)
        + cmonad1 - (1 + φd1) - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-inl-inj1» crun1 ccall1 cmonad1 φe1 φe2 φd1 evc1 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, mf1, ccall1, run1,
    denv2, cmonad1, φe1, φe2, φd1, evc1, envlen, lamwith,
    buildInj, buildIdx, buildValFromInj, valprj, listGet, finZero,
    D2τ, D2τPrime, phi, one]
    using leaf

theorem th1_inl_inj2_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ σ)
    (ih_e : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e)
    (ctg2 : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (some (Sum.inr ctg2) : Rep (D2τ (.sum σ τ))) denvin
      (Term.inl (τ := τ) e : Term .Pr Γ (.sum σ τ)) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let z := zerov (D2τPrime σ)
  let zerores : Rep (D2τ σ) := z.1
  let czero : Int := z.2
  let mf1 := bp1 zerores
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime σ) zerores
  let φd2 : Int := phi (D2τPrime τ) ctg2
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have pzero : φd1 = 1 := by
    dsimp [φd1, zerores, z]
    exact zero_small_phi_v σ
  have pφd1 : czero ≤ 2 := by
    dsimp [czero, z]
    exact zero_small_cost_v σ
  have pφd2 : 0 ≤ φd2 := by
    dsimp [φd2]
    exact phi_positive (D2τPrime τ) ctg2
  have sym_φd2 : -φd2 ≤ -φd2 := by
    omega
  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e zerores denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, zerores, mf1, ccall1, run1, denv2,
      cmonad1, φe1, φe2, φd1, evc1, envlen, cost, D2τ, D2τPrime,
      phi, one] using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + (2 + czero) + ccall1)
        + cmonad1 - (1 + φd2) - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-inl-inj2» crun1 czero ccall1 cmonad1 φe1 φe2 φd1 φd2 evc1
      pzero pφd1 pφd2 sym_φd2 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, z, zerores, czero, mf1,
    ccall1, run1, denv2, cmonad1, φe1, φe2, φd1, φd2, evc1,
    envlen, lamwith, buildInj, buildIdx, buildValFromInj, valprj,
    listGet, finZero, D2τ, D2τPrime, phi, one]
    using leaf

theorem th1_inr_nothing_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ τ)
    (ih_e : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e)
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (none : Rep (D2τ (.sum σ τ))) denvin
      (Term.inr (σ := σ) e : Term .Pr Γ (.sum σ τ)) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let z := zerov (D2τPrime τ)
  let zerores : Rep (D2τ τ) := z.1
  let czero : Int := z.2
  let mf1 := bp1 zerores
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime τ) zerores
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have pzero : φd1 = 1 := by
    dsimp [φd1, zerores, z]
    exact zero_small_phi_v τ
  have pφd1 : czero ≤ 2 := by
    dsimp [czero, z]
    exact zero_small_cost_v τ
  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e zerores denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, zerores, mf1, ccall1, run1, denv2,
      cmonad1, φe1, φe2, φd1, evc1, envlen, cost, D2τ, D2τPrime,
      phi, one] using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + (2 + czero) + ccall1)
        + cmonad1 - (1 + 0) - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-inl-nothing» crun1 czero ccall1 cmonad1 φe1 φe2 φd1 evc1
      pzero pφd1 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, z, zerores, czero, mf1,
    ccall1, run1, denv2, cmonad1, φe1, φe2, φd1, evc1, envlen,
    lamwith, buildInj, buildIdx, buildValFromInj, valprj, listGet,
    finZero, D2τ, D2τPrime, phi, one]
    using leaf

theorem th1_inr_inj2_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ τ)
    (ih_e : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (some (Sum.inr ctg) : Rep (D2τ (.sum σ τ))) denvin
      (Term.inr (σ := σ) e : Term .Pr Γ (.sum σ τ)) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let mf1 := bp1 ctg
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime τ) ctg
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e ctg denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, mf1, ccall1, run1, denv2, cmonad1,
      φe1, φe2, φd1, evc1, envlen, cost, D2τ, D2τPrime, phi, one]
      using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (5 + ccall1)
        + cmonad1 - (1 + φd1) - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-inl-inj1» crun1 ccall1 cmonad1 φe1 φe2 φd1 evc1 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, mf1, ccall1, run1,
    denv2, cmonad1, φe1, φe2, φd1, evc1, envlen, lamwith,
    buildInj, buildIdx, buildValFromInj, valprj, listGet, finZero,
    D2τ, D2τPrime, phi, one]
    using leaf

theorem th1_inr_inj1_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ τ)
    (ih_e : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e)
    (ctg2 : Rep (D2τ σ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env (some (Sum.inl ctg2) : Rep (D2τ (.sum σ τ))) denvin
      (Term.inr (σ := σ) e : Term .Pr Γ (.sum σ τ)) := by
  let out1 := eval (primalVal env) (chad e)
  let bp1 := out1.1.2
  let crun1 : Int := out1.2
  let z := zerov (D2τPrime τ)
  let zerores : Rep (D2τ τ) := z.1
  let czero : Int := z.2
  let mf1 := bp1 zerores
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denvin
  let denv2 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φe2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φd1 : Int := phi (D2τPrime τ) zerores
  let φd2 : Int := phi (D2τPrime σ) ctg2
  let evc1 : Int := cost env e
  let envlen : Int := intLength Γ

  have pzero : φd1 = 1 := by
    dsimp [φd1, zerores, z]
    exact zero_small_phi_v τ
  have pφd1 : czero ≤ 2 := by
    dsimp [czero, z]
    exact zero_small_cost_v τ
  have pφd2 : 0 ≤ φd2 := by
    dsimp [φd2]
    exact phi_positive (D2τPrime σ) ctg2
  have sym_φd2 : -φd2 ≤ -φd2 := by
    omega
  have k1 :
      crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih_e zerores denvin
    unfold th1Bound at hih
    simpa only [out1, bp1, crun1, zerores, mf1, ccall1, run1, denv2,
      cmonad1, φe1, φe2, φd1, evc1, envlen, cost, D2τ, D2τPrime,
      phi, one] using hih

  have leaf :
      (1 : Int) + crun1 + 6 + (3 + (2 + czero) + ccall1)
        + cmonad1 - (1 + φd2) - φe1 + φe2 - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1) :=
    «lemma-inl-inj2» crun1 czero ccall1 cmonad1 φe1 φe2 φd1 φd2 evc1
      pzero pφd1 pφd2 sym_φd2 envlen k1

  unfold th1Bound
  simpa only [chad, eval, cost, out1, bp1, crun1, z, zerores, czero, mf1,
    ccall1, run1, denv2, cmonad1, φe1, φe2, φd1, φd2, evc1,
    envlen, lamwith, buildInj, buildIdx, buildValFromInj, valprj,
    listGet, finZero, D2τ, D2τPrime, phi, one]
    using leaf

theorem th1_pair_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr Γ τ)
    (ih1 : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e1)
    (ih2 : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e2)
    (ctg : Rep (D2τ (.prod σ τ)))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin
      (Term.pair e1 e2 : Term .Pr Γ (.prod σ τ)) := by
  cases ctg with
  | none =>
      exact th1_pair_nothing_case env e1 e2 ih1 ih2 denvin
  | some xy =>
      cases xy with
      | mk ctg1 ctg2 =>
          exact th1_pair_just_case env e1 e2 ih1 ih2 ctg1 ctg2 denvin

theorem th1_inl_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ σ)
    (ih_e : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e)
    (ctg : Rep (D2τ (.sum σ τ)))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin
      (Term.inl (τ := τ) e : Term .Pr Γ (.sum σ τ)) := by
  cases ctg with
  | none =>
      exact th1_inl_nothing_case (Γ := Γ) (σ := σ) (τ := τ) env e ih_e denvin
  | some s =>
      cases s with
      | inl ctgσ =>
          exact th1_inl_inj1_case (Γ := Γ) (σ := σ) (τ := τ) env e ih_e ctgσ denvin
      | inr ctgτ =>
          exact th1_inl_inj2_case (Γ := Γ) (σ := σ) (τ := τ) env e ih_e ctgτ denvin

theorem th1_inr_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e : Term .Pr Γ τ)
    (ih_e : ∀ (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgτ denvinτ e)
    (ctg : Rep (D2τ (.sum σ τ)))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin
      (Term.inr (σ := σ) e : Term .Pr Γ (.sum σ τ)) := by
  cases ctg with
  | none =>
      exact th1_inr_nothing_case (Γ := Γ) (σ := σ) (τ := τ) env e ih_e denvin
  | some s =>
      cases s with
      | inl ctgσ =>
          exact th1_inr_inj1_case (Γ := Γ) (σ := σ) (τ := τ) env e ih_e ctgσ denvin
      | inr ctgτ =>
          exact th1_inr_inj2_case (Γ := Γ) (σ := σ) (τ := τ) env e ih_e ctgτ denvin

theorem th1_let_body_sink_eval_eq {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr (σ :: Γ) τ) :
    eval
        (Val.push (eval (primalVal env) (chad e1)).1.1
          (Val.push (eval (primalVal env) (chad e1)).1 (primalVal env)))
        (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad e2))
      = eval (primalVal (Val.push (eval env e1).1 env)) (chad e2) := by
  have hpres := chad_preserves_primal env e1
  have h :=
    eval_copy_skip_wend (primalVal env)
      (primal σ (eval env e1).1)
      (eval (primalVal env) (chad e1)).1
      (chad e2)
  simpa only [primalVal, hpres] using h

theorem th1_case_left_body_sink_eval_eq {Γ : Env .Pr} {σ τ ρ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ (.sum σ τ))
    (e2 : Term .Pr (σ :: Γ) ρ)
    (x : Rep σ) :
    eval
        (Val.push (primal σ x)
          (Val.push (eval (primalVal env) (chad e1)).1 (primalVal env)))
        (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad e2))
      = eval (primalVal (Val.push x env)) (chad e2) := by
  have h :=
    eval_copy_skip_wend (primalVal env)
      (primal σ x)
      (eval (primalVal env) (chad e1)).1
      (chad e2)
  simpa only [primalVal] using h

theorem th1_case_right_body_sink_eval_eq {Γ : Env .Pr} {σ τ ρ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ (.sum σ τ))
    (e3 : Term .Pr (τ :: Γ) ρ)
    (y : Rep τ) :
    eval
        (Val.push (primal τ y)
          (Val.push (eval (primalVal env) (chad e1)).1 (primalVal env)))
        (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad e3))
      = eval (primalVal (Val.push y env)) (chad e3) := by
  have h :=
    eval_copy_skip_wend (primalVal env)
      (primal τ y)
      (eval (primalVal env) (chad e1)).1
      (chad e3)
  simpa only [primalVal] using h

theorem th1_let_case {Γ : Env .Pr} {σ τ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ σ)
    (e2 : Term .Pr (σ :: Γ) τ)
    (ih1 : ∀ (ctgσ : Rep (D2τ σ))
        (denvinσ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgσ denvinσ e1)
    (ih2 : ∀ (env2 : Val .Pr (σ :: Γ))
        (ctgτ : Rep (D2τ τ))
        (denvinτ : LEtup (List.map D2τPrime (σ :: Γ))),
        th1Bound env2 ctgτ denvinτ e2)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.letE e1 e2) := by
  let orig1 := eval env e1
  let origx1 : Rep σ := orig1.1
  let evc1 : Int := orig1.2
  let orig2 := eval (Val.push origx1 env) e2
  let evc2 : Int := orig2.2
  let out1Eval := eval (primalVal env) (chad e1)
  let out1 := out1Eval.1
  let crun1 : Int := out1Eval.2
  let primal1 : Rep (D1τ σ) := out1.1
  let bp1 := out1.2
  let evalA :=
    eval (Val.push primal1 (Val.push out1 (primalVal env)))
      (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad e2))
  let out2 := evalA.1
  let crun2 : Int := evalA.2
  let evalB := eval (primalVal (Val.push origx1 env)) (chad e2)
  let out2p := evalB.1
  let crun2p : Int := evalB.2
  let bp2 := out2.2
  let bp2p := out2p.2
  let env4 : Val .Du
      (D2τ τ :: (.prod (D1τ τ) (.arr (D2τ τ) (D2Γ (σ :: Γ)))) ::
        (.prod (D1τ σ) (.arr (D2τ σ) (D2Γ Γ))) :: []) :=
    Val.push ctg (Val.push out2 (Val.push out1 Val.empty))
  let zeroEval := eval env4 (zerot σ)
  let zerores : Rep (D2τ σ) := zeroEval.1
  let czero : Int := zeroEval.2
  let mf2 := bp2 ctg
  let ccall2 : Int := mf2.2
  let mf := LACM.bind (LACM.scope zerores mf2.1)
    (fun x => ((bp1 x.1).1, (5 : Int) + (bp1 x.1).2))
  let runOut := LACM.run mf denvin
  let denvout := runOut.2.1
  let cmonad : Int := runOut.2.2
  let runScope := LACM.run (LACM.scope zerores mf2.1) denvin
  let dx : Rep (D2τ σ) := runScope.1.1
  let denv2 := runScope.2.1
  let cmonad2 : Int := runScope.2.2
  let mf1 := bp1 dx
  let cbp1 : Int := mf1.2
  let mf2p := bp2p ctg
  let cbp2 : Int := mf2p.2
  let run1 := LACM.run mf1.1 denv2
  let denv3 := run1.2.1
  let cmonad1 : Int := run1.2.2
  let run2p := LACM.run mf2p.1 (zerores, denvin)
  let dxp : Rep (D2τ σ) := run2p.2.1.1
  let denv2p : LEtup (List.map D2τPrime Γ) := run2p.2.1.2
  let cmonad2p : Int := run2p.2.2
  let envlen : Int := intLength Γ

  have eval_e2_equal : evalA = evalB := by
    dsimp [evalA, evalB, primal1, out1, out1Eval, origx1, orig1]
    exact th1_let_body_sink_eval_eq env e1 e2
  have equals_crun2 : crun2 = crun2p := by
    dsimp [crun2, crun2p, evalA, evalB]
    exact congrArg (fun r => r.2) eval_e2_equal
  have equals_mf2 : mf2.1 = mf2p.1 := by
    dsimp [mf2, mf2p, bp2, bp2p, out2, out2p, evalA, evalB]
    exact congrArg (fun r => (r.1.2 ctg).1) eval_e2_equal
  have equals_ccall2 : ccall2 = cbp2 := by
    dsimp [ccall2, cbp2, mf2, mf2p, bp2, bp2p, out2, out2p, evalA, evalB]
    exact congrArg (fun r => (r.1.2 ctg).2) eval_e2_equal

  have pScope := run_scope2 mf2.1 mf2p.1 equals_mf2 zerores denvin
  have equal_dx : dx = dxp := by
    dsimp [dx, dxp, runScope, run2p] at pScope ⊢
    exact pScope.2.1
  have equal_denv2 : denv2 = denv2p := by
    dsimp [denv2, denv2p, runScope, run2p] at pScope ⊢
    exact pScope.2.2.1
  have equal_cmonad2 : cmonad2 = cmonad2p := by
    dsimp [cmonad2, cmonad2p, runScope, run2p] at pScope ⊢
    exact pScope.2.2.2

  have runbindres :=
    run_bind2 (Γ := Γ) (LACM.scope zerores mf2.1)
      (fun x => ((bp1 x.1).1, (5 : Int) + (bp1 x.1).2)) denvin
  have prunbind1 : denvout = denv3 := by
    dsimp [denvout, denv3, runOut, run1, runScope, denv2, mf, mf1] at runbindres ⊢
    exact runbindres.1
  have prunbind2 : cmonad = cmonad2 + ((5 : Int) + cbp1) + cmonad1 - envlen := by
    dsimp [cmonad, cmonad2, cbp1, cmonad1, runOut, runScope, run1, mf, mf1, envlen]
    simpa only [one] using runbindres.2

  let φd : Int := phi (D2τPrime τ) ctg
  let φe1 : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φeout : Int := phiPrime (List.map D2τPrime Γ) denvout
  let φzerores : Int := phi (D2τPrime σ) zerores
  let φdx : Int := phi (D2τPrime σ) dx
  let φdxp : Int := phi (D2τPrime σ) dxp
  let φdenv2 : Int := phiPrime (List.map D2τPrime Γ) denv2
  let φdenv2p : Int := phiPrime (List.map D2τPrime Γ) denv2p
  let φdenv3 : Int := phiPrime (List.map D2τPrime Γ) denv3

  have equal_φdx : φdx = φdxp := by
    dsimp [φdx, φdxp]
    exact congrArg (phi (D2τPrime σ)) equal_dx
  have equal_φdenv2 : φdenv2 = φdenv2p := by
    dsimp [φdenv2, φdenv2p]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) equal_denv2
  have prunbind1φ : φeout = φdenv3 := by
    dsimp [φeout, φdenv3]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) prunbind1
  have pczerosmall : czero ≤ (2 : Int) := by
    dsimp [czero, zeroEval]
    exact zero_small_cost env4 σ
  have pφzeroressmall : φzerores = (1 : Int) := by
    dsimp [φzerores, zerores, zeroEval]
    exact zero_small_phi env4 σ

  have k2_raw :
      crun2p + cbp2 + cmonad2p - φd
        - phiPrime (List.map D2τPrime (σ :: Γ)) (zerores, denvin)
        + phiPrime (List.map D2τPrime (σ :: Γ)) (dxp, denv2p)
        - intLength (σ :: Γ) ≤ (34 : Int) * evc2 := by
    have hih := ih2 (Val.push origx1 env) ctg (zerores, denvin)
    unfold th1Bound at hih
    simp only [evalB, out2p, bp2p, crun2p, mf2p, cbp2, run2p,
      dxp, denv2p, cmonad2p, evc2, orig2, origx1, orig1, cost] at hih ⊢
    exact hih
  have k2 :
      crun2p + cbp2 + cmonad2p - φd - (φzerores + φe1)
        + (φdxp + φdenv2p) - ((1 : Int) + envlen)
        ≤ (34 : Int) * evc2 := by
    simp [φzerores, φe1, φdxp, φdenv2p, envlen, intLength, phiPrime, one] at k2_raw ⊢
    omega

  have k1 :
      crun1 + cbp1 + cmonad1 - φdx - φdenv2 + φdenv3 - envlen
        ≤ (34 : Int) * evc1 := by
    have hih := ih1 dx denv2
    unfold th1Bound at hih
    simp only [out1Eval, out1, bp1, crun1, mf1, cbp1, run1, denv3,
      cmonad1, φdx, φdenv2, φdenv3, evc1, orig1, envlen, cost,
      phiPrime, one] at hih ⊢
    omega



  have leaf :
      (1 : Int) + crun1 + (3 + (1 + crun2 + 6))
        + (1 + (1 + czero + (4 + ccall2)) + 2)
        + cmonad - φd - φe1 + φeout - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1 + evc2) :=
    «lemma-let» evc1 evc2 crun1 crun2 crun2p equals_crun2
      czero ccall2 cmonad cmonad2 cbp1 cbp2 equals_ccall2
      cmonad1 cmonad2p equal_cmonad2 envlen prunbind2
      φd φe1 φeout φzerores φdx φdxp equal_φdx
      φdenv2 φdenv2p equal_φdenv2 φdenv3 prunbind1φ
      pczerosmall pφzeroressmall k2 k1

  unfold th1Bound
  simpa only [chad, eval, cost, orig1, origx1, evc1, orig2, evc2,
    out1Eval, out1, crun1, primal1, bp1, evalA, out2, crun2,
    evalB, out2p, crun2p, bp2, bp2p, env4, zeroEval, zerores,
    czero, mf2, ccall2, mf, runOut, denvout, cmonad, runScope,
    dx, denv2, cmonad2, mf1, cbp1, mf2p, cbp2, run1, denv3,
    cmonad1, run2p, dxp, denv2p, cmonad2p, envlen, φd, φe1,
    φeout, φzerores, φdx, φdxp, φdenv2, φdenv2p, φdenv3,
    lamwith, buildInj, buildIdx, buildValFromInj, valprj, listGet,
    finZero, finTwo, sink, primalVal, one] using leaf



theorem th1_case_inl_case {Γ : Env .Pr} {σ τ ρ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ (.sum σ τ))
    (e2 : Term .Pr (σ :: Γ) ρ)
    (e3 : Term .Pr (τ :: Γ) ρ)
    (ih1 : ∀ (ctgστ : Rep (D2τ (.sum σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e1)
    (ih2 : ∀ (env2 : Val .Pr (σ :: Γ))
        (ctgρ : Rep (D2τ ρ))
        (denvinρ : LEtup (List.map D2τPrime (σ :: Γ))),
        th1Bound env2 ctgρ denvinρ e2)
    (_ih3 : ∀ (env3 : Val .Pr (τ :: Γ))
        (ctgρ : Rep (D2τ ρ))
        (denvinρ : LEtup (List.map D2τPrime (τ :: Γ))),
        th1Bound env3 ctgρ denvinρ e3)
    (x : Rep σ)
    (hscrut : (eval env e1).1 = Sum.inl x)
    (ctg : Rep (D2τ ρ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.caseE e1 e2 e3) := by
  let orig1 := eval env e1
  let evc1 : Int := orig1.2
  let out1Eval := eval (primalVal env) (chad e1)
  let out1 := out1Eval.1
  let crun1 : Int := out1Eval.2
  let primal1 : Rep (D1τ (.sum σ τ)) := out1.1
  let bp1 := out1.2
  let primal1' : Rep (D1τ σ) := primal σ x
  let subenv1 : Val .Du
      (D1τ σ :: (.prod (D1τ (.sum σ τ)) (.arr (D2τ (.sum σ τ)) (D2Γ Γ))) :: D1Γ Γ) :=
    Val.push primal1' (Val.push out1 (primalVal env))
  let chade2res := eval subenv1 (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad e2))
  let out2 := chade2res.1
  let crun2 : Int := chade2res.2
  let subenv2 : Val .Du
      (D2τ ρ :: (.prod (D1τ ρ) (.arr (D2τ ρ) (D2Γ (σ :: Γ)))) ::
        (.prod (D1τ (.sum σ τ)) (.arr (D2τ (.sum σ τ)) (D2Γ Γ))) :: []) :=
    Val.push ctg (Val.push out2 (Val.push out1 Val.empty))
  let zeroEval := eval subenv2 (zerot σ)
  let zerores : Rep (D2τ σ) := zeroEval.1
  let czero : Int := zeroEval.2
  let bp2 := out2.2
  let mf2 := bp2 ctg
  let ccall2 : Int := mf2.2
  let runScope := LACM.run (LACM.scope zerores mf2.1) denvin
  let dx : Rep (D2τ σ) := runScope.1.1
  let denv2_B := runScope.2.1
  let cmonad2_B : Int := runScope.2.2
  let mf1 := bp1 (some (Sum.inl dx))
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denv2_B
  let denvout_B := run1.2.1
  let cmonad1_B : Int := run1.2.2
  let runBind := LACM.run
    (LACM.bind (LACM.scope zerores mf2.1)
      (fun dx' => ((bp1 (some (Sum.inl dx'.1))).1,
        (6 : Int) + (bp1 (some (Sum.inl dx'.1))).2))) denvin
  let denv2_A := runBind.2.1
  let cmonad_A : Int := runBind.2.2
  let orig2 := eval (Val.push x env) e2
  let evc2 : Int := orig2.2
  let envlen : Int := intLength Γ
  let φd : Int := phi (D2τPrime ρ) ctg
  let φdx : Int := phi (D2τPrime σ) dx
  let φenvin : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φdenv2_A : Int := phiPrime (List.map D2τPrime Γ) denv2_A
  let φdenv2_B : Int := phiPrime (List.map D2τPrime Γ) denv2_B
  let φdenvout_B : Int := phiPrime (List.map D2τPrime Γ) denvout_B
  let φzero : Int := phi (D2τPrime σ) zerores

  let chade2res_X := eval (Val.push primal1' (primalVal env)) (chad e2)
  let out2_X := chade2res_X.1
  let crun2_X : Int := chade2res_X.2
  let bp2_X := out2_X.2
  let mf2_X := bp2_X ctg
  let ccall2_X : Int := mf2_X.2
  let run2_X := LACM.run mf2_X.1 (zerores, denvin)
  let dx_X : Rep (D2τ σ) := run2_X.2.1.1
  let denv2_X : LEtup (List.map D2τPrime Γ) := run2_X.2.1.2
  let cmonad2_X : Int := run2_X.2.2
  let φdx_X : Int := phi (D2τPrime σ) dx_X
  let φdenv2_X : Int := phiPrime (List.map D2τPrime Γ) denv2_X

  have hpres := chad_preserves_primal env e1
  have hprimal1 : primal1 = Sum.inl primal1' := by
    dsimp [primal1, primal1', out1, out1Eval, orig1]
    simpa only [primal, hscrut] using hpres
  have pX : chade2res = chade2res_X := by
    dsimp [chade2res, chade2res_X, subenv1, primal1']
    exact th1_case_left_body_sink_eval_eq env e1 e2 x
  have eq_crun2 : crun2 = crun2_X := by
    dsimp [crun2, crun2_X, chade2res, chade2res_X]
    exact congrArg (fun r => r.2) pX
  have eq_ccall2 : ccall2 = ccall2_X := by
    dsimp [ccall2, ccall2_X, mf2, mf2_X, bp2, bp2_X, out2, out2_X, chade2res, chade2res_X]
    exact congrArg (fun r => (r.1.2 ctg).2) pX
  have eq_mf2 : mf2.1 = mf2_X.1 := by
    dsimp [mf2, mf2_X, bp2, bp2_X, out2, out2_X, chade2res, chade2res_X]
    exact congrArg (fun r => (r.1.2 ctg).1) pX

  have pScope := run_scope2 mf2.1 mf2_X.1 eq_mf2 zerores denvin
  have eq_cmonad2 : cmonad2_B = cmonad2_X := by
    dsimp [cmonad2_B, cmonad2_X, runScope, run2_X] at pScope ⊢
    exact pScope.2.2.2
  have eq_dx : dx = dx_X := by
    dsimp [dx, dx_X, runScope, run2_X] at pScope ⊢
    exact pScope.2.1
  have eq_φdx : φdx = φdx_X := by
    dsimp [φdx, φdx_X]
    exact congrArg (phi (D2τPrime σ)) eq_dx
  have eq_denv2 : denv2_B = denv2_X := by
    dsimp [denv2_B, denv2_X, runScope, run2_X] at pScope ⊢
    exact pScope.2.2.1
  have eq_φdenv2 : φdenv2_B = φdenv2_X := by
    dsimp [φdenv2_B, φdenv2_X]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) eq_denv2

  have runbindres :=
    run_bind2 (Γ := Γ) (LACM.scope zerores mf2.1)
      (fun dx' => ((bp1 (some (Sum.inl dx'.1))).1,
        (6 : Int) + (bp1 (some (Sum.inl dx'.1))).2)) denvin
  have runbindres1 : denv2_A = denvout_B := by
    dsimp [denv2_A, denvout_B, runBind, run1, runScope, mf1] at runbindres ⊢
    exact runbindres.1
  have runbindres2 : cmonad_A = cmonad2_B + ((6 : Int) + ccall1) + cmonad1_B - envlen := by
    dsimp [cmonad_A, cmonad2_B, ccall1, cmonad1_B, runBind, runScope, run1, mf1, envlen]
    simpa only [one] using runbindres.2
  have eq_φdenv2out : φdenv2_A = φdenvout_B := by
    dsimp [φdenv2_A, φdenvout_B]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) runbindres1

  have pczero : czero ≤ (2 : Int) := by
    dsimp [czero, zeroEval]
    exact zero_small_cost subenv2 σ
  have pφzero : φzero = (1 : Int) := by
    dsimp [φzero, zerores, zeroEval]
    exact zero_small_phi subenv2 σ

  have k1_raw :
      crun1 + ccall1 + cmonad1_B
        - phi (D2τPrime (.sum σ τ)) (some (Sum.inl dx))
        - φdenv2_B + φdenvout_B - envlen ≤ (34 : Int) * evc1 := by
    have hih := ih1 (some (Sum.inl dx)) denv2_B
    unfold th1Bound at hih
    simp only [out1Eval, out1, bp1, crun1, mf1, ccall1, run1,
      denvout_B, cmonad1_B, φdenv2_B, φdenvout_B,
      evc1, orig1, envlen, cost] at hih ⊢
    exact hih
  have k1 :
      crun1 + ccall1 + cmonad1_B - ((1 : Int) + φdx)
        - φdenv2_B + φdenvout_B - envlen ≤ (34 : Int) * evc1 := by
    simp [φdx, D2τPrime, D2τPrimeAll, phi, one] at k1_raw ⊢
    omega

  have k2_raw :
      crun2_X + ccall2_X + cmonad2_X - φd
        - phiPrime (List.map D2τPrime (σ :: Γ)) (zerores, denvin)
        + phiPrime (List.map D2τPrime (σ :: Γ)) (dx_X, denv2_X)
        - intLength (σ :: Γ) ≤ (34 : Int) * evc2 := by
    have hih := ih2 (Val.push x env) ctg (zerores, denvin)
    unfold th1Bound at hih
    simp only [chade2res_X, out2_X, bp2_X, crun2_X, mf2_X, ccall2_X,
      run2_X, dx_X, denv2_X, cmonad2_X, evc2, orig2, cost] at hih ⊢
    exact hih
  have k2 :
      crun2_X + ccall2_X + cmonad2_X - φd - (φzero + φenvin)
        + (φdx_X + φdenv2_X) - ((1 : Int) + envlen) ≤ (34 : Int) * evc2 := by
    simp [φzero, φenvin, φdx_X, φdenv2_X, envlen, intLength, phiPrime, one] at k2_raw ⊢
    omega



  have leaf :
      (1 : Int) + crun1 + (3 + (1 + crun2 + 6))
        + (1 + (1 + czero + (4 + ccall2)) + 2)
        + cmonad_A - φd - φenvin + φdenv2_A - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1 + evc2) :=
    «lemma-case-1» evc1 crun1 crun2 czero ccall2 cmonad2_B
      ccall1 cmonad1_B cmonad_A evc2 envlen φd φdx φenvin
      φdenv2_A φdenv2_B φdenvout_B φzero crun2_X ccall2_X
      cmonad2_X φdx_X φdenv2_X eq_crun2 eq_ccall2 eq_cmonad2
      eq_φdx eq_φdenv2 runbindres2 eq_φdenv2out pczero pφzero k1 k2

  have hscrutChad : (eval (primalVal env) (chad e1)).fst.fst = Sum.inl primal1' := by
    dsimp [primal1, out1, out1Eval] at hprimal1
    exact hprimal1
  unfold th1Bound
  simpa only [chad, eval, cost, hscrut, hscrutChad, orig1, evc1, out1Eval,
    out1, crun1, primal1, bp1, primal1', subenv1, chade2res, out2,
    crun2, subenv2, zeroEval, zerores, czero, bp2, mf2, ccall2,
    runScope, dx, denv2_B, cmonad2_B, mf1, ccall1, run1, denvout_B,
    cmonad1_B, runBind, denv2_A, cmonad_A, orig2, evc2, envlen,
    φd, φdx, φenvin, φdenv2_A, φdenv2_B, φdenvout_B, φzero,
    chade2res_X, out2_X, crun2_X, bp2_X, mf2_X, ccall2_X,
    run2_X, dx_X, denv2_X, cmonad2_X, φdx_X, φdenv2_X,
    lamwith, buildInj, buildIdx, buildValFromInj, valprj, listGet,
    finZero, finTwo, sink,
    primalVal, one] using leaf



theorem th1_case_inr_case {Γ : Env .Pr} {σ τ ρ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ (.sum σ τ))
    (e2 : Term .Pr (σ :: Γ) ρ)
    (e3 : Term .Pr (τ :: Γ) ρ)
    (ih1 : ∀ (ctgστ : Rep (D2τ (.sum σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e1)
    (_ih2 : ∀ (env2 : Val .Pr (σ :: Γ))
        (ctgρ : Rep (D2τ ρ))
        (denvinρ : LEtup (List.map D2τPrime (σ :: Γ))),
        th1Bound env2 ctgρ denvinρ e2)
    (ih3 : ∀ (env3 : Val .Pr (τ :: Γ))
        (ctgρ : Rep (D2τ ρ))
        (denvinρ : LEtup (List.map D2τPrime (τ :: Γ))),
        th1Bound env3 ctgρ denvinρ e3)
    (y : Rep τ)
    (hscrut : (eval env e1).1 = Sum.inr y)
    (ctg : Rep (D2τ ρ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.caseE e1 e2 e3) := by
  let orig1 := eval env e1
  let evc1 : Int := orig1.2
  let out1Eval := eval (primalVal env) (chad e1)
  let out1 := out1Eval.1
  let crun1 : Int := out1Eval.2
  let primal1 : Rep (D1τ (.sum σ τ)) := out1.1
  let bp1 := out1.2
  let primal1' : Rep (D1τ τ) := primal τ y
  let subenv1 : Val .Du
      (D1τ τ :: (.prod (D1τ (.sum σ τ)) (.arr (D2τ (.sum σ τ)) (D2Γ Γ))) :: D1Γ Γ) :=
    Val.push primal1' (Val.push out1 (primalVal env))
  let chade3res := eval subenv1 (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad e3))
  let out3 := chade3res.1
  let crun3 : Int := chade3res.2
  let subenv2 : Val .Du
      (D2τ ρ :: (.prod (D1τ ρ) (.arr (D2τ ρ) (D2Γ (τ :: Γ)))) ::
        (.prod (D1τ (.sum σ τ)) (.arr (D2τ (.sum σ τ)) (D2Γ Γ))) :: []) :=
    Val.push ctg (Val.push out3 (Val.push out1 Val.empty))
  let zeroEval := eval subenv2 (zerot τ)
  let zerores : Rep (D2τ τ) := zeroEval.1
  let czero : Int := zeroEval.2
  let bp3 := out3.2
  let mf3 := bp3 ctg
  let ccall3 : Int := mf3.2
  let runScope := LACM.run (LACM.scope zerores mf3.1) denvin
  let dy : Rep (D2τ τ) := runScope.1.1
  let denv3_B := runScope.2.1
  let cmonad3_B : Int := runScope.2.2
  let mf1 := bp1 (some (Sum.inr dy))
  let ccall1 : Int := mf1.2
  let run1 := LACM.run mf1.1 denv3_B
  let denvout_B := run1.2.1
  let cmonad1_B : Int := run1.2.2
  let runBind := LACM.run
    (LACM.bind (LACM.scope zerores mf3.1)
      (fun dy' => ((bp1 (some (Sum.inr dy'.1))).1,
        (6 : Int) + (bp1 (some (Sum.inr dy'.1))).2))) denvin
  let denv3_A := runBind.2.1
  let cmonad_A : Int := runBind.2.2
  let orig3 := eval (Val.push y env) e3
  let evc3 : Int := orig3.2
  let envlen : Int := intLength Γ
  let φd : Int := phi (D2τPrime ρ) ctg
  let φdy : Int := phi (D2τPrime τ) dy
  let φenvin : Int := phiPrime (List.map D2τPrime Γ) denvin
  let φdenv3_A : Int := phiPrime (List.map D2τPrime Γ) denv3_A
  let φdenv3_B : Int := phiPrime (List.map D2τPrime Γ) denv3_B
  let φdenvout_B : Int := phiPrime (List.map D2τPrime Γ) denvout_B
  let φzero : Int := phi (D2τPrime τ) zerores

  let chade3res_X := eval (Val.push primal1' (primalVal env)) (chad e3)
  let out3_X := chade3res_X.1
  let crun3_X : Int := chade3res_X.2
  let bp3_X := out3_X.2
  let mf3_X := bp3_X ctg
  let ccall3_X : Int := mf3_X.2
  let run3_X := LACM.run mf3_X.1 (zerores, denvin)
  let dy_X : Rep (D2τ τ) := run3_X.2.1.1
  let denv3_X : LEtup (List.map D2τPrime Γ) := run3_X.2.1.2
  let cmonad3_X : Int := run3_X.2.2
  let φdy_X : Int := phi (D2τPrime τ) dy_X
  let φdenv3_X : Int := phiPrime (List.map D2τPrime Γ) denv3_X

  have hpres := chad_preserves_primal env e1
  have hprimal1 : primal1 = Sum.inr primal1' := by
    dsimp [primal1, primal1', out1, out1Eval, orig1]
    simpa only [primal, hscrut] using hpres
  have pX : chade3res = chade3res_X := by
    dsimp [chade3res, chade3res_X, subenv1, primal1']
    exact th1_case_right_body_sink_eval_eq env e1 e3 y
  have eq_crun3 : crun3 = crun3_X := by
    dsimp [crun3, crun3_X, chade3res, chade3res_X]
    exact congrArg (fun r => r.2) pX
  have eq_ccall3 : ccall3 = ccall3_X := by
    dsimp [ccall3, ccall3_X, mf3, mf3_X, bp3, bp3_X, out3, out3_X, chade3res, chade3res_X]
    exact congrArg (fun r => (r.1.2 ctg).2) pX
  have eq_mf3 : mf3.1 = mf3_X.1 := by
    dsimp [mf3, mf3_X, bp3, bp3_X, out3, out3_X, chade3res, chade3res_X]
    exact congrArg (fun r => (r.1.2 ctg).1) pX

  have pScope := run_scope2 mf3.1 mf3_X.1 eq_mf3 zerores denvin
  have eq_cmonad3 : cmonad3_B = cmonad3_X := by
    dsimp [cmonad3_B, cmonad3_X, runScope, run3_X] at pScope ⊢
    exact pScope.2.2.2
  have eq_dy : dy = dy_X := by
    dsimp [dy, dy_X, runScope, run3_X] at pScope ⊢
    exact pScope.2.1
  have eq_φdy : φdy = φdy_X := by
    dsimp [φdy, φdy_X]
    exact congrArg (phi (D2τPrime τ)) eq_dy
  have eq_denv3 : denv3_B = denv3_X := by
    dsimp [denv3_B, denv3_X, runScope, run3_X] at pScope ⊢
    exact pScope.2.2.1
  have eq_φdenv3 : φdenv3_B = φdenv3_X := by
    dsimp [φdenv3_B, φdenv3_X]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) eq_denv3

  have runbindres :=
    run_bind2 (Γ := Γ) (LACM.scope zerores mf3.1)
      (fun dy' => ((bp1 (some (Sum.inr dy'.1))).1,
        (6 : Int) + (bp1 (some (Sum.inr dy'.1))).2)) denvin
  have runbindres1 : denv3_A = denvout_B := by
    dsimp [denv3_A, denvout_B, runBind, run1, runScope, mf1] at runbindres ⊢
    exact runbindres.1
  have runbindres2 : cmonad_A = cmonad3_B + ((6 : Int) + ccall1) + cmonad1_B - envlen := by
    dsimp [cmonad_A, cmonad3_B, ccall1, cmonad1_B, runBind, runScope, run1, mf1, envlen]
    simpa only [one] using runbindres.2
  have eq_φdenv3out : φdenv3_A = φdenvout_B := by
    dsimp [φdenv3_A, φdenvout_B]
    exact congrArg (phiPrime (List.map D2τPrime Γ)) runbindres1

  have pczero : czero ≤ (2 : Int) := by
    dsimp [czero, zeroEval]
    exact zero_small_cost subenv2 τ
  have pφzero : φzero = (1 : Int) := by
    dsimp [φzero, zerores, zeroEval]
    exact zero_small_phi subenv2 τ

  have k1_raw :
      crun1 + ccall1 + cmonad1_B
        - phi (D2τPrime (.sum σ τ)) (some (Sum.inr dy))
        - φdenv3_B + φdenvout_B - envlen ≤ (34 : Int) * evc1 := by
    have hih := ih1 (some (Sum.inr dy)) denv3_B
    unfold th1Bound at hih
    simp only [out1Eval, out1, bp1, crun1, mf1, ccall1, run1,
      denvout_B, cmonad1_B, φdenv3_B, φdenvout_B,
      evc1, orig1, envlen, cost] at hih ⊢
    exact hih
  have k1 :
      crun1 + ccall1 + cmonad1_B - ((1 : Int) + φdy)
        - φdenv3_B + φdenvout_B - envlen ≤ (34 : Int) * evc1 := by
    simp [φdy, D2τPrime, D2τPrimeAll, phi, one] at k1_raw ⊢
    omega

  have k2_raw :
      crun3_X + ccall3_X + cmonad3_X - φd
        - phiPrime (List.map D2τPrime (τ :: Γ)) (zerores, denvin)
        + phiPrime (List.map D2τPrime (τ :: Γ)) (dy_X, denv3_X)
        - intLength (τ :: Γ) ≤ (34 : Int) * evc3 := by
    have hih := ih3 (Val.push y env) ctg (zerores, denvin)
    unfold th1Bound at hih
    simp only [chade3res_X, out3_X, bp3_X, crun3_X, mf3_X, ccall3_X,
      run3_X, dy_X, denv3_X, cmonad3_X, evc3, orig3, cost] at hih ⊢
    exact hih
  have k2 :
      crun3_X + ccall3_X + cmonad3_X - φd - (φzero + φenvin)
        + (φdy_X + φdenv3_X) - ((1 : Int) + envlen) ≤ (34 : Int) * evc3 := by
    simp [φzero, φenvin, φdy_X, φdenv3_X, envlen, intLength, phiPrime, one] at k2_raw ⊢
    omega



  have leaf :
      (1 : Int) + crun1 + (3 + (1 + crun3 + 6))
        + (1 + (1 + czero + (4 + ccall3)) + 2)
        + cmonad_A - φd - φenvin + φdenv3_A - envlen
        ≤ (34 : Int) * ((1 : Int) + evc1 + evc3) :=
    «lemma-case-1» evc1 crun1 crun3 czero ccall3 cmonad3_B
      ccall1 cmonad1_B cmonad_A evc3 envlen φd φdy φenvin
      φdenv3_A φdenv3_B φdenvout_B φzero crun3_X ccall3_X
      cmonad3_X φdy_X φdenv3_X eq_crun3 eq_ccall3 eq_cmonad3
      eq_φdy eq_φdenv3 runbindres2 eq_φdenv3out pczero pφzero k1 k2

  have hscrutChad : (eval (primalVal env) (chad e1)).fst.fst = Sum.inr primal1' := by
    dsimp [primal1, out1, out1Eval] at hprimal1
    exact hprimal1
  unfold th1Bound
  simpa only [chad, eval, cost, hscrut, hscrutChad, orig1, evc1, out1Eval,
    out1, crun1, primal1, bp1, primal1', subenv1, chade3res, out3,
    crun3, subenv2, zeroEval, zerores, czero, bp3, mf3, ccall3,
    runScope, dy, denv3_B, cmonad3_B, mf1, ccall1, run1, denvout_B,
    cmonad1_B, runBind, denv3_A, cmonad_A, orig3, evc3, envlen,
    φd, φdy, φenvin, φdenv3_A, φdenv3_B, φdenvout_B, φzero,
    chade3res_X, out3_X, crun3_X, bp3_X, mf3_X, ccall3_X,
    run3_X, dy_X, denv3_X, cmonad3_X, φdy_X, φdenv3_X,
    lamwith, buildInj, buildIdx, buildValFromInj, valprj, listGet,
    finZero, finTwo, sink,
    primalVal, one] using leaf



theorem th1_case_case {Γ : Env .Pr} {σ τ ρ : Typ .Pr}
    (env : Val .Pr Γ)
    (e1 : Term .Pr Γ (.sum σ τ))
    (e2 : Term .Pr (σ :: Γ) ρ)
    (e3 : Term .Pr (τ :: Γ) ρ)
    (ih1 : ∀ (ctgστ : Rep (D2τ (.sum σ τ)))
        (denvinστ : LEtup (List.map D2τPrime Γ)),
        th1Bound env ctgστ denvinστ e1)
    (ih2 : ∀ (env2 : Val .Pr (σ :: Γ))
        (ctgρ : Rep (D2τ ρ))
        (denvinρ : LEtup (List.map D2τPrime (σ :: Γ))),
        th1Bound env2 ctgρ denvinρ e2)
    (ih3 : ∀ (env3 : Val .Pr (τ :: Γ))
        (ctgρ : Rep (D2τ ρ))
        (denvinρ : LEtup (List.map D2τPrime (τ :: Γ))),
        th1Bound env3 ctgρ denvinρ e3)
    (ctg : Rep (D2τ ρ))
    (denvin : LEtup (List.map D2τPrime Γ)) :
    th1Bound env ctg denvin (Term.caseE e1 e2 e3) := by
  cases hscrut : (eval env e1).1 with
  | inl x =>
      exact th1_case_inl_case (Γ := Γ) (σ := σ) (τ := τ) (ρ := ρ) env e1 e2 e3 ih1 ih2 ih3 x hscrut ctg denvin
  | inr y =>
      exact th1_case_inr_case (Γ := Γ) (σ := σ) (τ := τ) (ρ := ρ) env e1 e2 e3 ih1 ih2 ih3 y hscrut ctg denvin

theorem th1_bound_proof {Γ : Env .Pr}
    (env : Val .Pr Γ) : {τ : Typ .Pr} →
    (ctg : Rep (D2τ τ)) →
    (denvin : LEtup (List.map D2τPrime Γ)) →
    (t : Term .Pr Γ τ) → th1Bound env ctg denvin t
  | _, ctg, denvin, .var idx =>
      th1_var_case_bound env idx ctg denvin
  | _, ctg, denvin, .letE rhs body =>
      th1_let_case env rhs body
        (fun ctgσ denvinσ => th1_bound_proof env ctgσ denvinσ rhs)
        (fun env2 ctgτ denvinτ => th1_bound_proof env2 ctgτ denvinτ body)
        ctg denvin
  | _, ctg, denvin, .prim op arg =>
      th1_prim_case env op arg
        (fun ctgσ denvinσ => th1_bound_proof env ctgσ denvinσ arg)
        ctg denvin
  | _, ctg, denvin, .unit =>
      th1_unit_case_bound env ctg denvin
  | _, ctg, denvin, .pair left right =>
      th1_pair_case env left right
        (fun ctgσ denvinσ => th1_bound_proof env ctgσ denvinσ left)
        (fun ctgτ denvinτ => th1_bound_proof env ctgτ denvinτ right)
        ctg denvin
  | _, ctg, denvin, .fstE pairTerm =>
      th1_fst_case env pairTerm
        (fun ctgστ denvinστ => th1_bound_proof env ctgστ denvinστ pairTerm)
        ctg denvin
  | _, ctg, denvin, .sndE pairTerm =>
      th1_snd_case env pairTerm
        (fun ctgστ denvinστ => th1_bound_proof env ctgστ denvinστ pairTerm)
        ctg denvin
  | _, ctg, denvin, .inl arg =>
      th1_inl_case env arg
        (fun ctgσ denvinσ => th1_bound_proof env ctgσ denvinσ arg)
        ctg denvin
  | _, ctg, denvin, .inr arg =>
      th1_inr_case env arg
        (fun ctgτ denvinτ => th1_bound_proof env ctgτ denvinτ arg)
        ctg denvin
  | _, ctg, denvin, .caseE scrut left right =>
      th1_case_case env scrut left right
        (fun ctgστ denvinστ => th1_bound_proof env ctgστ denvinστ scrut)
        (fun env2 ctgρ denvinρ => th1_bound_proof env2 ctgρ denvinρ left)
        (fun env3 ctgρ denvinρ => th1_bound_proof env3 ctgρ denvinρ right)
        ctg denvin
  | _, ctg, denvin, .arrayBuild n body =>
      CoreArrayCostLaws.th1_arrayBuild_case env n body
        (fun ctgN denvinN => th1_bound_proof env ctgN denvinN n)
        (fun envI ctgBody denvinBody => th1_bound_proof envI ctgBody denvinBody body)
        ctg denvin
  | _, ctg, denvin, .arrayIndex xs i =>
      CoreArrayCostLaws.th1_arrayIndex_case env xs i
        (fun ctgXs denvinXs => th1_bound_proof env ctgXs denvinXs xs)
        (fun ctgI denvinI => th1_bound_proof env ctgI denvinI i)
        ctg denvin
  | _, ctg, denvin, .arrayFold body xs =>
      CoreArrayCostLaws.th1_arrayFold_case env body xs
        (fun envP ctgBody denvinBody => th1_bound_proof envP ctgBody denvinBody body)
        (fun ctgXs denvinXs => th1_bound_proof env ctgXs denvinXs xs)
        ctg denvin

theorem th1 : TH1_STATEMENT :=
  TH1_of_th1Bound (fun {Γ τ} env ctg denvin t => th1_bound_proof env ctg denvin t)

theorem th2 : TH2_STATEMENT := by
  unfold TH2_STATEMENT
  intro Γ τ env ctg t
  let env1 : Val .Du (D2τ τ :: D1Γ Γ) := Val.push ctg (primalVal env)
  let zeroEval := eval env1 (zeroEnvTerm Γ)
  let denvin : LEtup (List.map D2τPrime Γ) :=
    repLEτToLEtup (List.map D2τPrime Γ) zeroEval.1

  
  let evalres1 := eval env1 (sink1 (chad t))
  let crun1 : Int := evalres1.2
  let bp1 := evalres1.1.2
  let call1 := bp1 ctg
  let ccall1 : Int := call1.2
  let run1 := LACM.run call1.1 denvin
  let cmonad1 : Int := run1.2.2

  
  let evalres2 := eval (primalVal env) (chad t)
  let crun2 : Int := evalres2.2
  let bp2 := evalres2.1.2
  let call2 := bp2 ctg
  let ccall2 : Int := call2.2
  let run2 := LACM.run call2.1 denvin
  let cmonad2 : Int := run2.2.2
  let φdenvout2 : Int := phiPrime (List.map D2τPrime Γ) run2.2.1

  have hsink :
      sinksTo (Weakening.WSkip Weakening.WEnd) (primalVal env) env1 := by
    intro ρ idx
    rfl

  have eq_evalres : evalres1 = evalres2 := by
    dsimp [evalres1, env1, sink1]
    exact (eval_sink_commute (primalVal env) env1
        (Weakening.WSkip Weakening.WEnd) hsink (chad t)).symm

  have eq_crun : crun1 = crun2 := by
    dsimp [crun1, crun2]
    exact congrArg (fun r => r.2) eq_evalres

  have eq_ccall : ccall1 = ccall2 := by
    dsimp [ccall1, ccall2, call1, call2, bp1, bp2]
    exact congrArg (fun r => (r.1.2 ctg).2) eq_evalres

  have eq_cmonad : cmonad1 = cmonad2 := by
    dsimp [cmonad1, cmonad2, run1, run2, call1, call2, bp1, bp2]
    exact congrArg
      (fun r => (LACM.run (r.1.2 ctg).1 denvin).2.2) eq_evalres

  have bound_φd :
      phi (D2τPrime τ) ctg ≤ Int.ofNat (size (D2τPrime τ) ctg) :=
    phi_less_size τ ctg

  have bound_φenv :
      phiPrime (List.map D2τPrime Γ) denvin ≤ φdenvout2 := by
    dsimp [denvin, zeroEval, φdenvout2, run2]
    exact phi_zero_env_bound env1 Γ (LACM.run call2.1 denvin).2.1

  have bound_czeroenv :
      zeroEval.2 ≤ (1 : Int) + (3 : Int) * intLength Γ := by
    dsimp [zeroEval]
    exact zero_env_small_cost env1 Γ

  have sym_φdenvout2 : -φdenvout2 ≤ -φdenvout2 := by
    omega

  have sym_result :
      (1 : Int) + (1 + (1 + (1 + intLength Γ)))
        ≤ (1 : Int) + (1 + (1 + (1 + intLength Γ))) := by
    omega

  have k1 :
      crun2 + ccall2 + cmonad2
        - phi (D2τPrime τ) ctg
        - phiPrime (List.map D2τPrime Γ) denvin
        + φdenvout2
        - intLength Γ
        ≤ (34 : Int) * cost env t := by
    dsimp [crun2, ccall2, cmonad2, call2, bp2, run2, φdenvout2]
    exact th1 env ctg denvin t

  have main :
      (1 : Int) + ((1 : Int) + ((1 : Int) + crun1) + (1 : Int) + ccall1)
        + zeroEval.2 + cmonad1
        ≤ (5 : Int) + (34 : Int) * cost env t
          + Int.ofNat (size (D2τPrime τ) ctg)
          + (4 : Int) * intLength Γ :=
    «lemma-th2»
      (phi (D2τPrime τ) ctg)
      (intLength Γ)
      zeroEval.2
      (phiPrime (List.map D2τPrime Γ) denvin)
      crun1 ccall1 cmonad1
      crun2 ccall2 cmonad2
      φdenvout2
      eq_crun eq_ccall eq_cmonad
      bound_φenv bound_czeroenv
      sym_φdenvout2 sym_result
      (cost env t)
      (Int.ofNat (size (D2τPrime τ) ctg))
      bound_φd
      k1

  simpa only [cost, eval, sink1, env1, zeroEval, denvin, evalres1, crun1, bp1,
    call1, ccall1, run1, cmonad1, one] using main


end EfficientChad
