import EfficientChad.Setup

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace EfficientChad

universe u

def ForallFin : {n : Nat} → (Fin n → Prop) → Prop
  | 0, _ => True
  | Nat.succ n, f =>
      f ⟨0, Nat.zero_lt_succ n⟩ ∧
        ForallFin (n := n)
          (fun i => f ⟨Nat.succ i.1, Nat.succ_lt_succ i.2⟩)

theorem forall_fin_trivial {n : Nat} {f : Fin n → Prop}
    (h : ∀ x, f x) : ForallFin f := by
  induction n with
  | zero =>
      simp [ForallFin]
  | succ n ih =>
      constructor
      · exact h ⟨0, Nat.zero_lt_succ n⟩
      · exact ih
          (f := fun i => f ⟨Nat.succ i.1, Nat.succ_lt_succ i.2⟩)
          (fun i => h ⟨Nat.succ i.1, Nat.succ_lt_succ i.2⟩)

def «forall-fin» {n : Nat} (f : Fin n → Prop) : Prop :=
  ForallFin f

theorem «forall-fin-trivial» {n : Nat} {f : Fin n → Prop}
    (h : ∀ x, f x) : ForallFin f :=
  forall_fin_trivial h

def makeIndex {tag : PDTag} {Γ : Env tag} (idx : Fin Γ.length) :
    Idx Γ (listGet Γ idx) :=
  buildIdx idx

def «make-index» {tag : PDTag} {Γ : Env tag} (idx : Fin Γ.length) :
    Idx Γ (listGet Γ idx) :=
  makeIndex idx

def sinksTo {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ') : Prop :=
  ∀ {τ : Typ tag} (idx : Idx Γ τ), valprj env idx = valprj env2 (weakenVar w idx)

def sinksToFin {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ') : Prop :=
  ForallFin (fun i : Fin Γ.length =>
    let idx := makeIndex (tag := tag) (Γ := Γ) i
    valprj env idx = valprj env2 (weakenVar w idx))

def «sinks-to» {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ') : Prop :=
  sinksToFin w env env2

theorem forallFin_makeIndex_elim {tag : PDTag} {Γ : Env tag}
    {P : ∀ {τ : Typ tag}, Idx Γ τ → Prop}
    (h : ForallFin (fun i : Fin Γ.length =>
      P (makeIndex (tag := tag) (Γ := Γ) i))) :
    ∀ {τ : Typ tag} (idx : Idx Γ τ), P idx := by
  induction Γ with
  | nil =>
      intro τ idx
      cases idx
  | cons σ Γ ih =>
      intro τ idx
      cases idx with
      | Z =>
          dsimp [ForallFin, makeIndex, buildIdx, listGet] at h
          exact h.1
      | S i =>
          dsimp [ForallFin, makeIndex, buildIdx, listGet] at h
          exact ih (P := fun {ρ : Typ tag} (j : Idx Γ ρ) => P (Idx.S j)) h.2 i

theorem sinksTo_of_sinksToFin {tag : PDTag} {Γ Γ' : Env tag}
    {w : Weakening Γ Γ'} {env : Val tag Γ} {env2 : Val tag Γ'} :
    sinksToFin w env env2 → sinksTo w env env2 := by
  intro h τ idx
  exact forallFin_makeIndex_elim
    (tag := tag)
    (Γ := Γ)
    (P := fun {ρ : Typ tag} (j : Idx Γ ρ) =>
      valprj env j = valprj env2 (weakenVar w j))
    h idx

theorem sinksToFin_of_sinksTo {tag : PDTag} {Γ Γ' : Env tag}
    {w : Weakening Γ Γ'} {env : Val tag Γ} {env2 : Val tag Γ'} :
    sinksTo w env env2 → sinksToFin w env env2 := by
  intro h
  exact forall_fin_trivial (fun i => h (makeIndex (tag := tag) (Γ := Γ) i))

theorem sinks_to_idx {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ') :
    sinksTo w env env2 → ∀ {τ : Typ tag} (idx : Idx Γ τ),
      valprj env idx = valprj env2 (weakenVar w idx) :=
  fun h {_} idx => h idx

theorem sinks_to_copy {tag : PDTag} {Γ Γ' : Env tag} {σ : Typ tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ')
    (x : Rep σ) :
    sinksTo w env env2 →
      sinksTo (Weakening.WCopy w) (Val.push x env) (Val.push x env2) := by
  intro h
  intro ρ idx
  cases idx with
  | Z => rfl
  | S i => exact h i

theorem sinks_to_skip {tag : PDTag} {Γ Γ' : Env tag} {σ : Typ tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ')
    (x : Rep σ) :
    sinksTo w env env2 →
      sinksTo (Weakening.WSkip w) env (Val.push x env2) := by
  intro h
  intro ρ idx
  simpa [weakenVar, valprj] using h idx

theorem sinks_to_refl {tag : PDTag} {Γ : Env tag}
    (env : Val tag Γ) : sinksTo Weakening.WEnd env env := by
  intro τ idx
  rfl

theorem sinksTo_WEnd_self {tag : PDTag} {Γ : Env tag}
    (env : Val tag Γ) : sinksTo Weakening.WEnd env env :=
  sinks_to_refl env

theorem sinksTo_WCopy_push {tag : PDTag} {Γ Γ' : Env tag} {σ : Typ tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ')
    (x : Rep σ) :
    sinksTo w env env2 →
      sinksTo (Weakening.WCopy w) (Val.push x env) (Val.push x env2) :=
  sinks_to_copy w env env2 x

theorem sinksTo_WSkip_push {tag : PDTag} {Γ Γ' : Env tag} {σ : Typ tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ')
    (x : Rep σ) :
    sinksTo w env env2 →
      sinksTo (Weakening.WSkip w) env (Val.push x env2) :=
  sinks_to_skip w env env2 x

theorem sinksTo_WCut_empty {tag : PDTag} {Γ' : Env tag}
    (env2 : Val tag Γ') :
    sinksTo (Weakening.WCut (Γ' := Γ')) (Val.empty : Val tag []) env2 := by
  intro τ idx
  cases idx

theorem sinks_to_copy_skip_wend {tag : PDTag} {Γ : Env tag} {σ κ : Typ tag}
    (env : Val tag Γ) (x : Rep σ) (saved : Rep κ) :
    sinksTo (Weakening.WCopy (Weakening.WSkip Weakening.WEnd))
      (Val.push x env) (Val.push x (Val.push saved env)) := by
  intro ρ idx
  cases idx with
  | Z => rfl
  | S i => rfl


@[simp] theorem sink_var {tag : PDTag} {Γ Γ' : Env tag} {τ : Typ tag}
    (w : Weakening Γ Γ') (idx : Idx Γ τ) :
    sink w (Term.var idx) = Term.var (weakenVar w idx) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_letE {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (rhs : Term tag Γ σ) (body : Term tag (σ :: Γ) τ) :
    sink w (Term.letE rhs body) = Term.letE (sink w rhs) (sink (Weakening.WCopy w) body) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_prim {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (op : Primop tag σ τ) (e : Term tag Γ σ) :
    sink w (Term.prim op e) = Term.prim op (sink w e) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_unit {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') :
    sink w (Term.unit : Term tag Γ Typ.Un) = (Term.unit : Term tag Γ' Typ.Un) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_pair {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (e1 : Term tag Γ σ) (e2 : Term tag Γ τ) :
    sink w (Term.pair e1 e2) = Term.pair (sink w e1) (sink w e2) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_fstE {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (e : Term tag Γ (Typ.prod σ τ)) :
    sink w (Term.fstE e) = Term.fstE (sink w e) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_sndE {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (e : Term tag Γ (Typ.prod σ τ)) :
    sink w (Term.sndE e) = Term.sndE (sink w e) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_inl {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (e : Term tag Γ σ) :
    sink w (Term.inl (τ := τ) e) = Term.inl (τ := τ) (sink w e) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_inr {tag : PDTag} {Γ Γ' : Env tag} {σ τ : Typ tag}
    (w : Weakening Γ Γ') (e : Term tag Γ τ) :
    sink w (Term.inr (σ := σ) e) = Term.inr (σ := σ) (sink w e) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_caseE {tag : PDTag} {Γ Γ' : Env tag} {σ τ ρ : Typ tag}
    (w : Weakening Γ Γ') (scrut : Term tag Γ (Typ.sum σ τ))
    (left : Term tag (σ :: Γ) ρ) (right : Term tag (τ :: Γ) ρ) :
    sink w (Term.caseE scrut left right) =
      Term.caseE (sink w scrut) (sink (Weakening.WCopy w) left) (sink (Weakening.WCopy w) right) := by
  cases tag <;> simp [sink, sinkPr, sinkDu]

@[simp] theorem sink_lam {Γ Γ' Γclo : Env .Du} {σ τ : Typ .Du}
    (w : Weakening Γ Γ')
    (inj : ∀ {ρ : Typ .Du}, Idx Γclo ρ → Idx Γ ρ)
    (body : Term .Du (σ :: Γclo) τ) :
    sink w (Term.lam Γclo inj body) =
      Term.lam Γclo (fun {ρ : Typ .Du} (i : Idx Γclo ρ) => weakenVar w (inj i)) body := by
  simp [sink, sinkDu]

@[simp] theorem sink_app {Γ Γ' : Env .Du} {σ τ : Typ .Du}
    (w : Weakening Γ Γ') (e1 : Term .Du Γ (Typ.arr σ τ)) (e2 : Term .Du Γ σ) :
    sink w (Term.app e1 e2) = Term.app (sink w e1) (sink w e2) := by
  simp [sink, sinkDu]

@[simp] theorem sink_pureevm {Γ Γ' : Env .Du} {Γl : LEnv}
    (w : Weakening Γ Γ') {τ : Typ .Du}
    (e : Term .Du Γ τ) :
    sink w (Term.pureevm (Γl := Γl) e) = Term.pureevm (Γl := Γl) (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_bindevm {Γ Γ' : Env .Du} {Γl : LEnv} {σ τ : Typ .Du}
    (w : Weakening Γ Γ')
    (e1 : Term .Du Γ (Typ.EVM Γl σ)) (e2 : Term .Du Γ (Typ.arr σ (Typ.EVM Γl τ))) :
    sink w (Term.bindevm e1 e2) = Term.bindevm (sink w e1) (sink w e2) := by
  simp [sink, sinkDu]

@[simp] theorem sink_runevm {Γ Γ' : Env .Du} {Γl : LEnv} {τ : Typ .Du}
    (w : Weakening Γ Γ')
    (e1 : Term .Du Γ (Typ.EVM Γl τ)) (e2 : Term .Du Γ (LEτ Γl)) :
    sink w (Term.runevm e1 e2) = Term.runevm (sink w e1) (sink w e2) := by
  simp [sink, sinkDu]

@[simp] theorem sink_addevm {Γ Γ' : Env .Du} {Γl : LEnv} {τ : LTyp}
    (w : Weakening Γ Γ')
    (idx : Idx Γl τ) (e : Term .Du Γ (Typ.Lin τ)) :
    sink w (Term.addevm idx e) = Term.addevm idx (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_scopeevm {Γ Γ' : Env .Du} {Γl : LEnv} {τ : LTyp} {σ : Typ .Du}
    (w : Weakening Γ Γ')
    (e1 : Term .Du Γ (Typ.Lin τ)) (e2 : Term .Du Γ (Typ.EVM (τ :: Γl) σ)) :
    sink w (Term.scopeevm e1 e2) = Term.scopeevm (sink w e1) (sink w e2) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lunit {Γ Γ' : Env .Du}
    (w : Weakening Γ Γ') :
    sink w (Term.lunit : Term .Du Γ (Typ.Lin LTyp.LUn)) =
      (Term.lunit : Term .Du Γ' (Typ.Lin LTyp.LUn)) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lpair {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e1 : Term .Du Γ (Typ.Lin σ)) (e2 : Term .Du Γ (Typ.Lin τ)) :
    sink w (Term.lpair e1 e2) = Term.lpair (sink w e1) (sink w e2) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lfstE {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e : Term .Du Γ (Typ.Lin (LTyp.prod σ τ))) :
    sink w (Term.lfstE e) = Term.lfstE (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lsndE {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e : Term .Du Γ (Typ.Lin (LTyp.prod σ τ))) :
    sink w (Term.lsndE e) = Term.lsndE (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lpairzero {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') :
    sink w (Term.lpairzero : Term .Du Γ (Typ.Lin (LTyp.prod σ τ))) =
      (Term.lpairzero : Term .Du Γ' (Typ.Lin (LTyp.prod σ τ))) := by
  simp [sink, sinkDu]

@[simp] theorem sink_linl {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e : Term .Du Γ (Typ.Lin σ)) :
    sink w (Term.linl (τ := τ) e) = Term.linl (τ := τ) (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_linr {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e : Term .Du Γ (Typ.Lin τ)) :
    sink w (Term.linr (σ := σ) e) = Term.linr (σ := σ) (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lcastl {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e : Term .Du Γ (Typ.Lin (LTyp.sum σ τ))) :
    sink w (Term.lcastl e) = Term.lcastl (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lcastr {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') (e : Term .Du Γ (Typ.Lin (LTyp.sum σ τ))) :
    sink w (Term.lcastr e) = Term.lcastr (sink w e) := by
  simp [sink, sinkDu]

@[simp] theorem sink_lsumzero {Γ Γ' : Env .Du} {σ τ : LTyp}
    (w : Weakening Γ Γ') :
    sink w (Term.lsumzero : Term .Du Γ (Typ.Lin (LTyp.sum σ τ))) =
      (Term.lsumzero : Term .Du Γ' (Typ.Lin (LTyp.sum σ τ))) := by
  simp [sink, sinkDu]

theorem eval_sink_commute_var {tag : PDTag} {Γ Γ' : Env tag} {τ : Typ tag}
    (env : Val tag Γ) (env2 : Val tag Γ') (w : Weakening Γ Γ')
    (h : sinksTo w env env2) (idx : Idx Γ τ) :
    eval env (Term.var idx) = eval env2 (sink w (Term.var idx)) := by
  cases tag <;> simp [eval, sink, sinkPr, sinkDu, h idx]

theorem eval_sink_commute_unit {tag : PDTag} {Γ Γ' : Env tag}
    (env : Val tag Γ) (env2 : Val tag Γ') (w : Weakening Γ Γ')
    (_h : sinksTo w env env2) :
    eval env (Term.unit : Term tag Γ (.Un)) =
      eval env2 (sink w (Term.unit : Term tag Γ (.Un))) := by
  cases tag <;> simp [eval, sink, sinkPr, sinkDu]

theorem eval_sink_commute_lunit {Γ Γ' : Env .Du}
    (env : Val .Du Γ) (env2 : Val .Du Γ') (w : Weakening Γ Γ')
    (_h : sinksTo w env env2) :
    eval env (Term.lunit : Term .Du Γ (.Lin .LUn)) =
      eval env2 (sink w (Term.lunit : Term .Du Γ (.Lin .LUn))) := by
  simp [eval, sink, sinkDu]

theorem sinks_to_idx_fin {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ') :
    sinksToFin w env env2 → ∀ {τ : Typ tag} (idx : Idx Γ τ),
      valprj env idx = valprj env2 (weakenVar w idx) :=
  fun h => sinks_to_idx w env env2 (sinksTo_of_sinksToFin h)

theorem «sinks-to-idx» {tag : PDTag} {Γ Γ' : Env tag}
    (w : Weakening Γ Γ') (env : Val tag Γ) (env2 : Val tag Γ') :
    sinksToFin w env env2 → ∀ {τ : Typ tag} (idx : Idx Γ τ),
      valprj env idx = valprj env2 (weakenVar w idx) :=
  sinks_to_idx_fin w env env2

theorem wend_is_id {tag : PDTag} {Γ : Env tag}
    (env env2 : Val tag Γ) : sinksTo Weakening.WEnd env env2 → env = env2 := by
  intro h
  revert env env2
  induction Γ with
  | nil =>
      intro env env2 _
      cases env
      cases env2
      rfl
  | cons τ Γ ih =>
      intro env env2 h
      cases env with
      | push x rest =>
          cases env2 with
          | push y rest2 =>
              have hhead : x = y := h (Idx.Z)
              have htail : rest = rest2 :=
                ih rest rest2 (fun {ρ : Typ tag} (idx : Idx Γ ρ) => h (Idx.S idx))
              cases hhead
              cases htail
              rfl

theorem «wend-is-id» {tag : PDTag} {Γ : Env tag}
    (env env2 : Val tag Γ) : sinksToFin Weakening.WEnd env env2 → env = env2 :=
  fun h => wend_is_id env env2 (sinksTo_of_sinksToFin h)

theorem inj_weaken_commute {Γ Γ' Γclo : Env .Du}
    (f : ∀ {σ : Typ .Du}, Idx Γclo σ → Idx Γ σ)
    (w : Weakening Γ Γ')
    (env : Val .Du Γ) (env2 : Val .Du Γ') :
  sinksTo w env env2 →
    buildValFromInj f env = buildValFromInj (fun {σ : Typ .Du} (i : Idx Γclo σ) => weakenVar w (f i)) env2 := by
  intro h
  revert f
  induction Γclo with
  | nil =>
      intro _
      simp [buildValFromInj]
  | cons τ Γrest ih =>
      intro f
      have hhead : valprj env (f (Idx.Z)) = valprj env2 (weakenVar w (f (Idx.Z))) := h (f (Idx.Z))
      have htail :
          buildValFromInj (fun {ρ : Typ .Du} (i : Idx Γrest ρ) => f (Idx.S i)) env =
          buildValFromInj (fun {ρ : Typ .Du} (i : Idx Γrest ρ) => weakenVar w (f (Idx.S i))) env2 :=
        ih (fun {ρ : Typ .Du} (i : Idx Γrest ρ) => f (Idx.S i))
      change
        Val.push (valprj env (f (Idx.Z)))
            (buildValFromInj (fun {ρ : Typ .Du} (i : Idx Γrest ρ) => f (Idx.S i)) env) =
          Val.push (valprj env2 (weakenVar w (f (Idx.Z))))
            (buildValFromInj (fun {ρ : Typ .Du} (i : Idx Γrest ρ) => weakenVar w (f (Idx.S i))) env2)
      simp [hhead, htail]

theorem «inj-weaken-commute» {Γ Γ' Γclo : Env .Du}
    (f : ∀ {σ : Typ .Du}, Idx Γclo σ → Idx Γ σ)
    (w : Weakening Γ Γ')
    (env : Val .Du Γ) (env2 : Val .Du Γ') :
  sinksToFin w env env2 →
    buildValFromInj f env = buildValFromInj (fun {σ : Typ .Du} (i : Idx Γclo σ) => weakenVar w (f i)) env2 :=
  fun h => inj_weaken_commute f w env env2 (sinksTo_of_sinksToFin h)

theorem eval_sink_commute_core {tag : PDTag} {Γ Γ' : Env tag} {τ : Typ tag}
    (env : Val tag Γ) (env2 : Val tag Γ')
    (w : Weakening Γ Γ') :
  sinksTo w env env2 → (e : Term tag Γ τ) → eval env e = eval env2 (sink w e) := by
  intro h e
  induction e with
  | var idx =>
      simpa [eval, h idx]
  | letE rhs body ih_rhs ih_body =>
      have hrhs : eval env rhs = eval env2 (sink w rhs) := ih_rhs env env2 w h
      have hbody :
          eval (Val.push (eval env2 (sink w rhs)).1 env) body =
            eval (Val.push (eval env2 (sink w rhs)).1 env2) (sink (Weakening.WCopy w) body) :=
        ih_body
          (Val.push (eval env2 (sink w rhs)).1 env)
          (Val.push (eval env2 (sink w rhs)).1 env2)
          (Weakening.WCopy w)
          (sinks_to_copy w env env2 (eval env2 (sink w rhs)).1 h)
      simpa [eval, hrhs, hbody]
  | prim op e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | unit =>
      simp [eval]
  | pair e1 e2 ih1 ih2 =>
      have h1 : eval env e1 = eval env2 (sink w e1) := ih1 env env2 w h
      have h2 : eval env e2 = eval env2 (sink w e2) := ih2 env env2 w h
      simpa [eval, h1, h2]
  | fstE e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | sndE e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | inl e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | inr e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | caseE scrut left right ih_scrut ih_left ih_right =>
      have hs : eval env scrut = eval env2 (sink w scrut) := ih_scrut env env2 w h
      cases hscrut : (eval env2 (sink w scrut)).1 with
      | inl x =>
          have hleft :
              eval (Val.push x env) left =
                eval (Val.push x env2) (sink (Weakening.WCopy w) left) :=
            ih_left
              (Val.push x env)
              (Val.push x env2)
              (Weakening.WCopy w)
              (sinks_to_copy w env env2 x h)
          simpa [eval, hs, hscrut, hleft]
      | inr y =>
          have hright :
              eval (Val.push y env) right =
                eval (Val.push y env2) (sink (Weakening.WCopy w) right) :=
            ih_right
              (Val.push y env)
              (Val.push y env2)
              (Weakening.WCopy w)
              (sinks_to_copy w env env2 y h)
          simpa [eval, hs, hscrut, hright]
  | lam Γclo inj body ih_body =>
      have hbuild := inj_weaken_commute inj w env env2 h
      simpa [eval, hbuild]
  | app e1 e2 ih1 ih2 =>
      have h1 : eval env e1 = eval env2 (sink w e1) := ih1 env env2 w h
      have h2 : eval env e2 = eval env2 (sink w e2) := ih2 env env2 w h
      simpa [eval, h1, h2]
  | pureevm e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | bindevm e1 e2 ih1 ih2 =>
      have h1 : eval env e1 = eval env2 (sink w e1) := ih1 env env2 w h
      have h2 : eval env e2 = eval env2 (sink w e2) := ih2 env env2 w h
      simpa [eval, h1, h2]
  | runevm e1 e2 ih1 ih2 =>
      have h1 : eval env e1 = eval env2 (sink w e1) := ih1 env env2 w h
      have h2 : eval env e2 = eval env2 (sink w e2) := ih2 env env2 w h
      simpa [eval, h1, h2]
  | addevm idx e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | scopeevm e1 e2 ih1 ih2 =>
      have h1 : eval env e1 = eval env2 (sink w e1) := ih1 env env2 w h
      have h2 : eval env e2 = eval env2 (sink w e2) := ih2 env env2 w h
      simpa [eval, h1, h2]
  | lunit =>
      simp [eval]
  | lpair e1 e2 ih1 ih2 =>
      have h1 : eval env e1 = eval env2 (sink w e1) := ih1 env env2 w h
      have h2 : eval env e2 = eval env2 (sink w e2) := ih2 env env2 w h
      simpa [eval, h1, h2]
  | lfstE e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      cases hval : (eval env2 (sink w e)).1 with
      | none => simpa [eval, he, hval]
      | some xy =>
          cases xy with
          | mk x y => simpa [eval, he, hval]
  | lsndE e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      cases hval : (eval env2 (sink w e)).1 with
      | none => simpa [eval, he, hval]
      | some xy =>
          cases xy with
          | mk x y => simpa [eval, he, hval]
  | lpairzero =>
      simp [eval]
  | linl e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | linr e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      simpa [eval, he]
  | lcastl e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      cases hval : (eval env2 (sink w e)).1 with
      | none => simpa [eval, he, hval]
      | some s =>
          cases s with
          | inl x => simpa [eval, he, hval]
          | inr y => simpa [eval, he, hval]
  | lcastr e ih =>
      have he : eval env e = eval env2 (sink w e) := ih env env2 w h
      cases hval : (eval env2 (sink w e)).1 with
      | none => simpa [eval, he, hval]
      | some s =>
          cases s with
          | inl x => simpa [eval, he, hval]
          | inr y => simpa [eval, he, hval]
  | lsumzero =>
      simp [eval]

theorem eval_sink_commute_pr {Γ Γ' : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) (env2 : Val .Pr Γ')
    (w : Weakening Γ Γ') :
  sinksTo w env env2 → (e : Term .Pr Γ τ) → eval env e = eval env2 (sinkPr w e) := by
  intro h e
  simpa [sink] using eval_sink_commute_core env env2 w h e

theorem eval_sink_commute_du {Γ Γ' : Env .Du} {τ : Typ .Du}
    (env : Val .Du Γ) (env2 : Val .Du Γ')
    (w : Weakening Γ Γ') :
  sinksTo w env env2 → (e : Term .Du Γ τ) → eval env e = eval env2 (sinkDu w e) := by
  intro h e
  simpa [sink] using eval_sink_commute_core env env2 w h e

theorem eval_sink_commute {tag : PDTag} {Γ Γ' : Env tag} {τ : Typ tag}
    (env : Val tag Γ) (env2 : Val tag Γ')
    (w : Weakening Γ Γ') :
  sinksTo w env env2 → (e : Term tag Γ τ) → eval env e = eval env2 (sink w e) :=
  eval_sink_commute_core env env2 w


theorem eval_copy_skip_wend {Γ : Env .Du} {σ κ τ : Typ .Du}
    (env : Val .Du Γ) (x : Rep σ) (saved : Rep κ)
    (e : Term .Du (σ :: Γ) τ) :
    eval (Val.push x (Val.push saved env))
        (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) e) =
      eval (Val.push x env) e :=
  (eval_sink_commute
    (Val.push x env)
    (Val.push x (Val.push saved env))
    (Weakening.WCopy (Weakening.WSkip Weakening.WEnd))
    (sinks_to_copy_skip_wend env x saved)
    e).symm

theorem «eval-sink-commute» {tag : PDTag} {Γ Γ' : Env tag} {τ : Typ tag}
    (env : Val tag Γ) (env2 : Val tag Γ')
    (w : Weakening Γ Γ') :
  sinksToFin w env env2 → (e : Term tag Γ τ) → eval env e = eval env2 (sink w e) :=
  fun h e => eval_sink_commute env env2 w (sinksTo_of_sinksToFin h) e

end EfficientChad
