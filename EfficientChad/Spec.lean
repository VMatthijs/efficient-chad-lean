import EfficientChad.Spec.LACM

namespace EfficientChad

noncomputable section

universe u v

inductive PDTag : Type where
  | Pr : PDTag
  | Du : PDTag
  deriving Repr

inductive Typ : PDTag → Type where
  | Un {tag : PDTag} : Typ tag
  | Inte {tag : PDTag} : Typ tag
  | R {tag : PDTag} : Typ tag
  | prod {tag : PDTag} : Typ tag → Typ tag → Typ tag
  | sum {tag : PDTag} : Typ tag → Typ tag → Typ tag
  | array {tag : PDTag} : Typ tag → Typ tag
  | arr {tag : PDTag} : Typ tag → Typ tag → Typ tag
  | EVM : LEnv → Typ .Du → Typ .Du
  | Lin : LTyp → Typ .Du

abbrev «_:*_» {tag : PDTag} (σ τ : Typ tag) : Typ tag :=
  Typ.prod σ τ

abbrev «_:+_» {tag : PDTag} (σ τ : Typ tag) : Typ tag :=
  Typ.sum σ τ

abbrev ArrayT {tag : PDTag} (τ : Typ tag) : Typ tag :=
  Typ.array τ

abbrev «_:->_» {tag : PDTag} (σ τ : Typ tag) : Typ tag :=
  Typ.arr σ τ

abbrev Env (tag : PDTag) : Type := List (Typ tag)

/-- A typed injection between same-tag environments.  For source lambdas this is
the inclusion of the compact closure context into the ambient context; for target
lambdas it is the ordinary closure-capture map used by `lamwith`. -/
abbrev EnvInj {tag : PDTag} (Γsrc Γdst : Env tag) : Type :=
  ∀ {ρ : Typ tag}, Idx Γsrc ρ → Idx Γdst ρ

abbrev Rep : {tag : PDTag} → Typ tag → Type
  | _, .Un => Unit
  | _, .Inte => Int
  | _, .R => Float
  | _, .prod σ τ => Rep σ × Rep τ
  | _, .sum σ τ => Sum (Rep σ) (Rep τ)
  | _, .array τ => List (Rep τ)
  | _, .arr σ τ => Rep σ → Rep τ × Int
  | _, .EVM Γ τ => LACM Γ (Rep τ)
  | _, .Lin τ => LinRep τ

def dutAll : {tag : PDTag} → Typ tag → Typ .Du
  | _, .Un => .Un
  | _, .Inte => .Inte
  | _, .R => .R
  | _, .prod σ τ => .prod (dutAll σ) (dutAll τ)
  | _, .sum σ τ => .sum (dutAll σ) (dutAll τ)
  | _, .array τ => .array (dutAll τ)
  | .Pr, .arr σ τ => .arr (dutAll σ) (dutAll τ)
  | .Du, .arr σ τ => .arr σ τ
  | .Du, .EVM Γ τ => .EVM Γ τ
  | .Du, .Lin τ => .Lin τ

abbrev dut (τ : Typ .Pr) : Typ .Du :=
  dutAll τ


abbrev LEτ : LEnv → Typ .Du
  | [] => .Un
  | τ :: Γ => .prod (.Lin τ) (LEτ Γ)

def repLEτToLEtup (Γ : LEnv) : Rep (LEτ Γ) → LEtup Γ :=
  match Γ with
  | [] => fun x => x
  | _τ :: Γ' => fun x => (x.1, repLEτToLEtup Γ' x.2)

def LEtupToRepLEτ (Γ : LEnv) : LEtup Γ → Rep (LEτ Γ) :=
  match Γ with
  | [] => fun x => x
  | _τ :: Γ' => fun x => (x.1, LEtupToRepLEτ Γ' x.2)

theorem Rep_LEτ_eq_LEtup (Γ : LEnv) : Rep (LEτ Γ) = LEtup Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      simpa [LEτ, LEtup, Rep] using congrArg (fun X : Type => LinRep τ × X) ih

theorem LEtup_eq_Rep_LEτ (Γ : LEnv) : LEtup Γ = Rep (LEτ Γ) := by
  exact (Rep_LEτ_eq_LEtup Γ).symm

theorem «LEtup-eq-LEτ» (Γ : LEnv) : Rep (LEτ Γ) = LEtup Γ :=
  Rep_LEτ_eq_LEtup Γ

def «LEtup-to-LEτ» (Γ : LEnv) : Rep (LEτ Γ) → LEtup Γ :=
  repLEτToLEtup Γ

def «LEτ-to-LEtup» (Γ : LEnv) : LEtup Γ → Rep (LEτ Γ) :=
  LEtupToRepLEτ Γ

inductive Primop : (tag : PDTag) → Typ tag → Typ tag → Type where
  | ADD {tag : PDTag} : Primop tag (.prod .R .R) .R
  | MUL {tag : PDTag} : Primop tag (.prod .R .R) .R
  | NEG {tag : PDTag} : Primop tag .R .R
  | LIT {tag : PDTag} (x : Float) : Primop tag .Un .R
  | IADD {tag : PDTag} : Primop tag (.prod .Inte .Inte) .Inte
  | IMUL {tag : PDTag} : Primop tag (.prod .Inte .Inte) .Inte
  | INEG {tag : PDTag} : Primop tag .Inte .Inte
  | SIGN {tag : PDTag} : Primop tag .R (.sum (.sum .Un .Un) .Un)
  | LZERO : Primop .Du (.Lin .LUn) (.Lin .LR)
  | LADD : Primop .Du (.prod (.Lin .LR) (.Lin .LR)) (.Lin .LR)
  | LSCALE : Primop .Du (.prod (.Lin .LR) .R) (.Lin .LR)
  | LNEG : Primop .Du (.Lin .LR) (.Lin .LR)

def evalprim {tag : PDTag} {σ τ : Typ tag} (op : Primop tag σ τ) : Rep σ → Rep τ :=
  match op with
  | .ADD => fun xy => ((show Float from xy.1) + (show Float from xy.2))
  | .MUL => fun xy => ((show Float from xy.1) * (show Float from xy.2))
  | .NEG => fun x => - (show Float from x)
  | .LIT x => fun _ => x
  | .IADD => fun xy => ((show Int from xy.1) + (show Int from xy.2))
  | .IMUL => fun xy => ((show Int from xy.1) * (show Int from xy.2))
  | .INEG => fun x => - (show Int from x)
  | .SIGN => fun x =>
      if (show Float from x) < (0.0 : Float) then Sum.inl (Sum.inl ())
      else if (0.0 : Float) < (show Float from x) then Sum.inl (Sum.inr ())
      else Sum.inr ()
  | .LZERO => fun _ => (0.0 : Float)
  | .LADD => fun xy => ((show Float from xy.1) + (show Float from xy.2))
  | .LSCALE => fun xy => ((show Float from xy.1) * (show Float from xy.2))
  | .LNEG => fun x => - (show Float from x)

inductive Term : (tag : PDTag) → Env tag → Typ tag → Type where
  | var {tag : PDTag} {Γ : Env tag} {τ : Typ tag} :
      Idx Γ τ → Term tag Γ τ
  | letE {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ σ → Term tag (σ :: Γ) τ → Term tag Γ τ
  | prim {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Primop tag σ τ → Term tag Γ σ → Term tag Γ τ
  | unit {tag : PDTag} {Γ : Env tag} :
      Term tag Γ .Un
  | pair {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ σ → Term tag Γ τ → Term tag Γ (.prod σ τ)
  | fstE {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ (.prod σ τ) → Term tag Γ σ
  | sndE {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ (.prod σ τ) → Term tag Γ τ
  | inl {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ σ → Term tag Γ (.sum σ τ)
  | inr {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ τ → Term tag Γ (.sum σ τ)
  | caseE {tag : PDTag} {Γ : Env tag} {σ τ ρ : Typ tag} :
      Term tag Γ (.sum σ τ) → Term tag (σ :: Γ) ρ → Term tag (τ :: Γ) ρ → Term tag Γ ρ
  | arrayBuild {tag : PDTag} {Γ : Env tag} {τ : Typ tag} :
      Term tag Γ .Inte → Term tag (.Inte :: Γ) τ → Term tag Γ (.array τ)
  | arrayIndex {tag : PDTag} {Γ : Env tag} {τ : Typ tag} :
      Term tag Γ (.array τ) → Term tag Γ .Inte → Term tag Γ τ
  | arrayFold {tag : PDTag} {Γ : Env tag} {τ : Typ tag} :
      Term tag (.prod τ τ :: Γ) τ → Term tag Γ (.array τ) → Term tag Γ τ
  | lam {tag : PDTag} {Γ Γclo : Env tag} {σ τ : Typ tag} :
      EnvInj Γclo Γ →
      Term tag (σ :: Γclo) τ → Term tag Γ (.arr σ τ)
  | app {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} :
      Term tag Γ (.arr σ τ) → Term tag Γ σ → Term tag Γ τ
  | pureevm {Γ : Env .Du} {Γl : LEnv} {τ : Typ .Du} :
      Term .Du Γ τ → Term .Du Γ (.EVM Γl τ)
  | bindevm {Γ : Env .Du} {Γl : LEnv} {σ τ : Typ .Du} :
      Term .Du Γ (.EVM Γl σ) → Term .Du Γ (.arr σ (.EVM Γl τ)) → Term .Du Γ (.EVM Γl τ)
  | runevm {Γ : Env .Du} {Γl : LEnv} {τ : Typ .Du} :
      Term .Du Γ (.EVM Γl τ) → Term .Du Γ (LEτ Γl) → Term .Du Γ (.prod τ (LEτ Γl))
  | addevm {Γ : Env .Du} {Γl : LEnv} {τ : LTyp} :
      Idx Γl τ → Term .Du Γ (.Lin τ) → Term .Du Γ (.EVM Γl .Un)
  | scopeevm {Γ : Env .Du} {Γl : LEnv} {τ : LTyp} {σ : Typ .Du} :
      Term .Du Γ (.Lin τ) → Term .Du Γ (.EVM (τ :: Γl) σ) → Term .Du Γ (.EVM Γl (.prod (.Lin τ) σ))
  | toDyn {Γ : Env .Du} {Γl : LEnv} :
      Term .Du Γ (LEτ Γl) → Term .Du Γ (.Lin .Dyn)
  | fromDyn {Γ : Env .Du} {Γl : LEnv} :
      Term .Du Γ (.Lin .Dyn) → Term .Du Γ (.EVM Γl .Un)
  | scatterevm {Γ : Env .Du} {Γsrc Γdst : LEnv} :
      LEnvInj Γsrc Γdst → Term .Du Γ (.EVM Γsrc .Un) → Term .Du Γ (.EVM Γdst .Un)
  | ldyntzero {Γ : Env .Du} : Term .Du Γ (.Lin .Dyn)
  | larrayzero {Γ : Env .Du} {τ : LTyp} :
      Term .Du Γ (.Lin (.array τ))
  | larrayone {Γ : Env .Du} {τ : LTyp} :
      Term .Du Γ .Inte → Term .Du Γ (.Lin τ) → Term .Du Γ (.Lin (.array τ))
  | larraybag {Γ : Env .Du} {τ : LTyp} :
      Term .Du Γ (.array (.prod .Inte (.Lin τ))) → Term .Du Γ (.Lin (.array τ))
  | larraycollect {Γ : Env .Du} {τ : LTyp} :
      Term .Du Γ (.Lin (.array τ)) → Term .Du Γ (.array (.prod .Inte (.Lin τ)))
  | arrayUnzipD {Γ : Env .Du} {α β : Typ .Du} :
      Term .Du Γ (.array (.prod α β)) → Term .Du Γ (.prod (.array α) (.array β))
  | arrayScatterD {Γ : Env .Du} {τ : LTyp} :
      Term .Du Γ (.array (.Lin τ)) →
      Term .Du Γ (.array (.prod .Inte (.Lin τ))) →
      Term .Du Γ (.array (.Lin τ))
  | arrayZipWithScopeD {Γ : Env .Du} {Γl : LEnv} {τ : LTyp} :
      Term .Du Γ (.array (.arr (.Lin τ) (.EVM (.LUn :: Γl) .Un))) →
      Term .Du Γ (.array (.Lin τ)) →
      Term .Du Γ (.array (.EVM Γl .Un))
  | arraySequenceUnitD {Γ : Env .Du} {Γl : LEnv} :
      Term .Du Γ (.array (.EVM Γl .Un)) → Term .Du Γ (.EVM Γl .Un)
  | arrayFoldAD {Γ : Env .Du} {Γl : LEnv} {α : Typ .Du} {δ : LTyp} :
      Term .Du Γ (.prod (.array α) (.arr (.Lin (.array δ)) (.EVM Γl .Un))) →
      Term .Du (.prod α α :: Γ) (.prod α (.arr (.Lin δ) (.EVM (.prod δ δ :: Γl) .Un))) →
      Term .Du Γ (.prod α (.arr (.Lin δ) (.EVM Γl .Un)))
  | lunit {Γ : Env .Du} : Term .Du Γ (.Lin .LUn)
  | lpair {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin σ) → Term .Du Γ (.Lin τ) → Term .Du Γ (.Lin (.prod σ τ))
  | lfstE {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin (.prod σ τ)) → Term .Du Γ (.Lin σ)
  | lsndE {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin (.prod σ τ)) → Term .Du Γ (.Lin τ)
  | lpairzero {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin (.prod σ τ))
  | linl {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin σ) → Term .Du Γ (.Lin (.sum σ τ))
  | linr {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin τ) → Term .Du Γ (.Lin (.sum σ τ))
  | lcastl {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin (.sum σ τ)) → Term .Du Γ (.Lin σ)
  | lcastr {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin (.sum σ τ)) → Term .Du Γ (.Lin τ)
  | lsumzero {Γ : Env .Du} {σ τ : LTyp} :
      Term .Du Γ (.Lin (.sum σ τ))

def «let'» {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag}
    (e₁ : Term tag Γ σ) (e₂ : Term tag (σ :: Γ) τ) : Term tag Γ τ :=
  Term.letE e₁ e₂

def «fst'» {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag}
    (e : Term tag Γ (.prod σ τ)) : Term tag Γ σ :=
  Term.fstE e

def «snd'» {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag}
    (e : Term tag Γ (.prod σ τ)) : Term tag Γ τ :=
  Term.sndE e

def «case'» {tag : PDTag} {Γ : Env tag} {σ τ ρ : Typ tag}
    (scrut : Term tag Γ (.sum σ τ))
    (left : Term tag (σ :: Γ) ρ)
    (right : Term tag (τ :: Γ) ρ) : Term tag Γ ρ :=
  Term.caseE scrut left right

def arrayBuildTerm {tag : PDTag} {Γ : Env tag} {τ : Typ tag}
    (n : Term tag Γ .Inte) (body : Term tag (.Inte :: Γ) τ) : Term tag Γ (.array τ) :=
  Term.arrayBuild n body

def arrayIndexTerm {tag : PDTag} {Γ : Env tag} {τ : Typ tag}
    (xs : Term tag Γ (.array τ)) (i : Term tag Γ .Inte) : Term tag Γ τ :=
  Term.arrayIndex xs i

def arrayFoldTerm {tag : PDTag} {Γ : Env tag} {τ : Typ tag}
    (body : Term tag (.prod τ τ :: Γ) τ) (xs : Term tag Γ (.array τ)) : Term tag Γ τ :=
  Term.arrayFold body xs

def «lfst'» {Γ : Env .Du} {σ τ : LTyp}
    (e : Term .Du Γ (.Lin (.prod σ τ))) : Term .Du Γ (.Lin σ) :=
  Term.lfstE e

def «lsnd'» {Γ : Env .Du} {σ τ : LTyp}
    (e : Term .Du Γ (.Lin (.prod σ τ))) : Term .Du Γ (.Lin τ) :=
  Term.lsndE e

inductive Weakening {tag : PDTag} : Env tag → Env tag → Type where
  | WEnd {Γ : Env tag} : Weakening Γ Γ
  | WCut {Γ' : Env tag} : Weakening [] Γ'
  | WCopy {Γ Γ' : Env tag} {τ : Typ tag} :
      Weakening Γ Γ' → Weakening (τ :: Γ) (τ :: Γ')
  | WSkip {Γ Γ' : Env tag} {τ : Typ tag} :
      Weakening Γ Γ' → Weakening Γ (τ :: Γ')

def weakenVar {tag : PDTag} {Γ Γ' : Env tag} (w : Weakening Γ Γ')
    {τ : Typ tag} (idx : Idx Γ τ) : Idx Γ' τ :=
  match w with
  | .WEnd => idx
  | .WCut => nomatch idx
  | .WCopy w' =>
      match idx with
      | .Z => .Z
      | .S i => .S (weakenVar w' i)
  | .WSkip w' => .S (weakenVar w' idx)

def «weaken-var» {tag : PDTag} {Γ Γ' : Env tag} (w : Weakening Γ Γ')
    {τ : Typ tag} (idx : Idx Γ τ) : Idx Γ' τ :=
  weakenVar w idx

def sinkPr {Γ Γ' : Env .Pr}
    (w : Weakening Γ Γ') : {τ : Typ .Pr} → Term .Pr Γ τ → Term .Pr Γ' τ
  | _, .var i => .var (weakenVar w i)
  | _, .letE e₁ e₂ => .letE (sinkPr w e₁) (sinkPr (.WCopy w) e₂)
  | _, .prim op e => .prim op (sinkPr w e)
  | _, .unit => .unit
  | _, .pair e₁ e₂ => .pair (sinkPr w e₁) (sinkPr w e₂)
  | _, .fstE e => .fstE (sinkPr w e)
  | _, .sndE e => .sndE (sinkPr w e)
  | _, .inl e => .inl (sinkPr w e)
  | _, .inr e => .inr (sinkPr w e)
  | _, .caseE e₁ e₂ e₃ => .caseE (sinkPr w e₁) (sinkPr (.WCopy w) e₂) (sinkPr (.WCopy w) e₃)
  | _, .arrayBuild n body => .arrayBuild (sinkPr w n) (sinkPr (.WCopy w) body)
  | _, .arrayIndex xs i => .arrayIndex (sinkPr w xs) (sinkPr w i)
  | _, .arrayFold body xs => .arrayFold (sinkPr (.WCopy w) body) (sinkPr w xs)
  | _, .lam inj body => .lam (fun {ρ : Typ .Pr} (i) => weakenVar w (inj i)) body
  | _, .app e₁ e₂ => .app (sinkPr w e₁) (sinkPr w e₂)

def sinkDu {Γ Γ' : Env .Du}
    (w : Weakening Γ Γ') : {τ : Typ .Du} → Term .Du Γ τ → Term .Du Γ' τ
  | _, .var i => .var (weakenVar w i)
  | _, .letE e₁ e₂ => .letE (sinkDu w e₁) (sinkDu (.WCopy w) e₂)
  | _, .prim op e => .prim op (sinkDu w e)
  | _, .unit => .unit
  | _, .pair e₁ e₂ => .pair (sinkDu w e₁) (sinkDu w e₂)
  | _, .fstE e => .fstE (sinkDu w e)
  | _, .sndE e => .sndE (sinkDu w e)
  | _, .inl e => .inl (sinkDu w e)
  | _, .inr e => .inr (sinkDu w e)
  | _, .caseE e₁ e₂ e₃ => .caseE (sinkDu w e₁) (sinkDu (.WCopy w) e₂) (sinkDu (.WCopy w) e₃)
  | _, .arrayBuild n body => .arrayBuild (sinkDu w n) (sinkDu (.WCopy w) body)
  | _, .arrayIndex xs i => .arrayIndex (sinkDu w xs) (sinkDu w i)
  | _, .arrayFold body xs => .arrayFold (sinkDu (.WCopy w) body) (sinkDu w xs)
  | _, .lam inj body => .lam (fun {ρ : Typ .Du} (i) => weakenVar w (inj i)) body
  | _, .app e₁ e₂ => .app (sinkDu w e₁) (sinkDu w e₂)
  | _, .pureevm e => .pureevm (sinkDu w e)
  | _, .bindevm e₁ e₂ => .bindevm (sinkDu w e₁) (sinkDu w e₂)
  | _, .runevm e₁ e₂ => .runevm (sinkDu w e₁) (sinkDu w e₂)
  | _, .addevm i e => .addevm i (sinkDu w e)
  | _, .scopeevm e₁ e₂ => .scopeevm (sinkDu w e₁) (sinkDu w e₂)
  | _, .toDyn e => .toDyn (sinkDu w e)
  | _, .fromDyn e => .fromDyn (sinkDu w e)
  | _, .scatterevm inj e => .scatterevm inj (sinkDu w e)
  | _, .ldyntzero => .ldyntzero
  | _, .larrayzero => .larrayzero
  | _, .larrayone i d => .larrayone (sinkDu w i) (sinkDu w d)
  | _, .larraybag xs => .larraybag (sinkDu w xs)
  | _, .larraycollect d => .larraycollect (sinkDu w d)
  | _, .arrayUnzipD xs => .arrayUnzipD (sinkDu w xs)
  | _, .arrayScatterD base pairs => .arrayScatterD (sinkDu w base) (sinkDu w pairs)
  | _, .arrayZipWithScopeD fs ds => .arrayZipWithScopeD (sinkDu w fs) (sinkDu w ds)
  | _, .arraySequenceUnitD acts => .arraySequenceUnitD (sinkDu w acts)
  | _, .arrayFoldAD xs body => .arrayFoldAD (sinkDu w xs) (sinkDu (.WCopy w) body)
  | _, .lunit => .lunit
  | _, .lpair e₁ e₂ => .lpair (sinkDu w e₁) (sinkDu w e₂)
  | _, .lfstE e => .lfstE (sinkDu w e)
  | _, .lsndE e => .lsndE (sinkDu w e)
  | _, .lpairzero => .lpairzero
  | _, .linl e => .linl (sinkDu w e)
  | _, .linr e => .linr (sinkDu w e)
  | _, .lcastl e => .lcastl (sinkDu w e)
  | _, .lcastr e => .lcastr (sinkDu w e)
  | _, .lsumzero => .lsumzero

def sink : {tag : PDTag} → {Γ Γ' : Env tag} →
    Weakening Γ Γ' → {τ : Typ tag} → Term tag Γ τ → Term tag Γ' τ
  | .Pr, _, _, w, _, tm => sinkPr w tm
  | .Du, _, _, w, _, tm => sinkDu w tm

def sink1 {tag : PDTag} {Γ : Env tag} {σ τ : Typ tag} (e : Term tag Γ τ) : Term tag (σ :: Γ) τ :=
  sink (Weakening.WSkip Weakening.WEnd) e

def listGet {α : Type u} : (xs : List α) → Fin xs.length → α
  | [], i => nomatch i
  | x :: xs, i =>
      match i with
      | ⟨0, _⟩ => x
      | ⟨Nat.succ n, h⟩ => listGet xs ⟨n, Nat.lt_of_succ_lt_succ h⟩

def «_!!_» {α : Type u} (xs : List α) (idx : Fin xs.length) : α :=
  listGet xs idx

def buildIdx {α : Type u} {Γ : List α} (i : Fin Γ.length) : Idx Γ (listGet Γ i) :=
  match Γ with
  | [] => nomatch i
  | _τ :: Γtail =>
      match i with
      | ⟨0, _⟩ => .Z
      | ⟨Nat.succ n, h⟩ => .S (buildIdx (Γ := Γtail) ⟨n, Nat.lt_of_succ_lt_succ h⟩)

def buildInj {tag : PDTag} {Γ : Env tag} (vars : List (Fin Γ.length)) :
    EnvInj (List.map (fun i => listGet Γ i) vars) Γ := by
  induction vars with
  | nil =>
      intro ρ idx
      cases idx
  | cons i rest ih =>
      intro ρ idx
      cases idx with
      | Z => exact buildIdx i
      | S j => exact ih j

def lamwith {α : Typ .Du} {Γ : Env .Du} {τ : Typ .Du}
    (vars : List (Fin Γ.length))
    (body : Term .Du (α :: List.map (fun i => listGet Γ i) vars) τ) :
    Term .Du Γ (.arr α τ) :=
  .lam (buildInj (tag := .Du) vars) body

/-- Source lambda helper using an explicit compact closure list.  The list should
contain exactly the free variables of the body, excluding the bound variable,
for the sharp complexity reading. -/
def prlamwith {α : Typ .Pr} {Γ : Env .Pr} {τ : Typ .Pr}
    (vars : List (Fin Γ.length))
    (body : Term .Pr (α :: List.map (fun i => listGet Γ i) vars) τ) :
    Term .Pr Γ (.arr α τ) :=
  .lam (buildInj (tag := .Pr) vars) body

/-- Source lambda helper for a closed body. -/
def prlamClosed {α : Typ .Pr} {Γ : Env .Pr} {τ : Typ .Pr}
    (body : Term .Pr [α] τ) : Term .Pr Γ (.arr α τ) :=
  .lam (fun {ρ : Typ .Pr} (i : Idx [] ρ) => nomatch i) body

/-- Compatibility helper: close over the whole ambient source context.  This is
correct but may be less efficient than `prlamwith`. -/
def prlamFull {α : Typ .Pr} {Γ : Env .Pr} {τ : Typ .Pr}
    (body : Term .Pr (α :: Γ) τ) : Term .Pr Γ (.arr α τ) :=
  .lam (fun {ρ : Typ .Pr} (i : Idx Γ ρ) => i) body

def finZero {n : Nat} : Fin (Nat.succ n) := ⟨0, Nat.zero_lt_succ n⟩

def finOne {n : Nat} : Fin (Nat.succ (Nat.succ n)) :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩

def finTwo {n : Nat} : Fin (Nat.succ (Nat.succ (Nat.succ n))) :=
  ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ n))⟩

def thenevm {Γl : LEnv} {Γ : Env .Du}
    (a b : Term .Du Γ (.EVM Γl .Un)) : Term .Du Γ (.EVM Γl .Un) :=
  .letE b
    (.bindevm
      (sink1 a)
      (lamwith (α := .Un) (Γ := (.EVM Γl .Un :: Γ)) [finZero] (.var (.S .Z))))

def convIdx {α β : Type u} {Γ : List α} {τ : α} (f : α → β)
    (idx : Idx Γ τ) : Idx (List.map f Γ) (f τ) :=
  match idx with
  | .Z => .Z
  | .S i => .S (convIdx f i)

/-- Map a typed environment injection through a type translation.  This is used
for both `D₁` closure capture and `D₂` closure scatter. -/
def mapIdxInj {α β : Type u} (f : α → β) :
    {Γsrc Γdst : List α} →
    (∀ {ρ : α}, Idx Γsrc ρ → Idx Γdst ρ) →
    ∀ {δ : β}, Idx (List.map f Γsrc) δ → Idx (List.map f Γdst) δ
  | [], _Γdst, _inj, _δ, idx => nomatch idx
  | _a :: Γsrc, Γdst, inj, _δ, idx =>
      match idx with
      | .Z => convIdx f (inj .Z)
      | .S i => mapIdxInj f (fun {ρ} (j : Idx Γsrc ρ) => inj (.S j)) i

@[reducible] def D2τPrimeAll : {tag : PDTag} → Typ tag → LTyp
  | _, .Un => .LUn
  | _, .Inte => .LUn
  | _, .R => .LR
  | _, .prod σ τ => .prod (D2τPrimeAll σ) (D2τPrimeAll τ)
  | _, .sum σ τ => .sum (D2τPrimeAll σ) (D2τPrimeAll τ)
  | _, .array τ => .array (D2τPrimeAll τ)
  | .Pr, .arr _ _ => .Dyn
  | .Du, .arr _ _ => .LUn
  | .Du, .EVM _ _ => .LUn
  | .Du, .Lin τ => τ

abbrev D2τPrime (τ : Typ .Pr) : LTyp :=
  D2τPrimeAll τ

def «D2τ'» : Typ .Pr → LTyp :=
  D2τPrime

abbrev D2τ (τ : Typ .Pr) : Typ .Du := .Lin (D2τPrime τ)

/-- Primal type translation on all type tags.  We define the recursive
worker on *all* `Typ tag`s, rather than only on `Typ .Pr`, so Lean elaborates it
as a structurally recursive function.  The public source translation `D1τ`
below is just its restriction to source types.  Function types are the only
non-trivial source clause:
`D₁(A → B) = D₁ A → (D₁ B × (D₂ B → Dyn × D₂ A))`. -/
@[reducible] def D1τAll : {tag : PDTag} → Typ tag → Typ .Du
  | _, .Un => .Un
  | _, .Inte => .Inte
  | _, .R => .R
  | _, .prod σ τ => .prod (D1τAll σ) (D1τAll τ)
  | _, .sum σ τ => .sum (D1τAll σ) (D1τAll τ)
  | _, .array τ => .array (D1τAll τ)
  | .Pr, .arr σ τ =>
      .arr (D1τAll σ)
        (.prod (D1τAll τ)
          (.arr (.Lin (D2τPrimeAll τ))
            (.prod (.Lin .Dyn) (.Lin (D2τPrimeAll σ)))))
  -- Target functions are already target functions.  The `D₁` worker is defined
  -- on all tags only to make the source recursion structurally transparent; it
  -- must not apply the source Dyn translation to target helper arrows.
  | .Du, .arr σ τ => .arr σ τ
  | .Du, .EVM Γ τ => .EVM Γ τ
  | .Du, .Lin τ => .Lin τ

abbrev D1τ (τ : Typ .Pr) : Typ .Du :=
  D1τAll τ

/-- The local reverse component stored in the translated primal of a function. -/
abbrev D1ArrLocalRev (σ τ : Typ .Pr) : Typ .Du :=
  .arr (D2τ τ) (.prod (.Lin .Dyn) (D2τ σ))

/-- The result of applying a translated function to a translated argument. -/
abbrev D1ArrResult (σ τ : Typ .Pr) : Typ .Du :=
  .prod (D1τ τ) (D1ArrLocalRev σ τ)

/-- Named form of the non-trivial `D₁` translation of source functions. -/
abbrev D1Arr (σ τ : Typ .Pr) : Typ .Du :=
  .arr (D1τ σ) (D1ArrResult σ τ)

/-- Function cotangents are represented by the abstract dynamic carrier. -/
abbrev D2Arr : Typ .Du := .Lin .Dyn

/- Lean sometimes needs these named computation rules when elaborating
terms whose target types mention the recursive translations.  They are theorems,
not extra assumptions: all of them reduce by the structurally recursive workers
above. -/
@[simp] theorem D1τ_Un_eq : D1τ (Typ.Un : Typ .Pr) = Typ.Un := by
  simp [D1τ, D1τAll]
@[simp] theorem D1τ_Inte_eq : D1τ (Typ.Inte : Typ .Pr) = Typ.Inte := by
  simp [D1τ, D1τAll]
@[simp] theorem D1τ_R_eq : D1τ (Typ.R : Typ .Pr) = Typ.R := by
  simp [D1τ, D1τAll]
@[simp] theorem D1τ_prod_eq (σ τ : Typ .Pr) :
    D1τ (.prod σ τ) = .prod (D1τ σ) (D1τ τ) := by
  simp [D1τ, D1τAll]
@[simp] theorem D1τ_sum_eq (σ τ : Typ .Pr) :
    D1τ (.sum σ τ) = .sum (D1τ σ) (D1τ τ) := by
  simp [D1τ, D1τAll]
@[simp] theorem D1τ_array_eq (τ : Typ .Pr) :
    D1τ (.array τ) = .array (D1τ τ) := by
  simp [D1τ, D1τAll]
@[simp] theorem D1τ_arr_eq (σ τ : Typ .Pr) :
    D1τ (.arr σ τ) = D1Arr σ τ := by
  simp [D1τ, D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll]

@[simp] theorem D1τAll_Pr_arr_eq (σ τ : Typ .Pr) :
    D1τAll (.arr σ τ) = D1Arr σ τ := by
  simp [D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll]

@[simp] theorem D1τAll_Du_arr_eq (σ τ : Typ .Du) :
    D1τAll (.arr σ τ) = .arr σ τ := by
  simp [D1τAll]

@[simp] theorem D2τPrime_Un_eq : D2τPrime (Typ.Un : Typ .Pr) = .LUn := by
  simp [D2τPrime, D2τPrimeAll]
@[simp] theorem D2τPrime_Inte_eq : D2τPrime (Typ.Inte : Typ .Pr) = .LUn := by
  simp [D2τPrime, D2τPrimeAll]
@[simp] theorem D2τPrime_R_eq : D2τPrime (Typ.R : Typ .Pr) = .LR := by
  simp [D2τPrime, D2τPrimeAll]
@[simp] theorem D2τPrime_prod_eq (σ τ : Typ .Pr) :
    D2τPrime (.prod σ τ) = .prod (D2τPrime σ) (D2τPrime τ) := by
  simp [D2τPrime, D2τPrimeAll]
@[simp] theorem D2τPrime_sum_eq (σ τ : Typ .Pr) :
    D2τPrime (.sum σ τ) = .sum (D2τPrime σ) (D2τPrime τ) := by
  simp [D2τPrime, D2τPrimeAll]
@[simp] theorem D2τPrime_array_eq (τ : Typ .Pr) :
    D2τPrime (.array τ) = .array (D2τPrime τ) := by
  simp [D2τPrime, D2τPrimeAll]
@[simp] theorem D2τPrime_arr_eq (σ τ : Typ .Pr) :
    D2τPrime (.arr σ τ) = .Dyn := by
  simp [D2τPrime, D2τPrimeAll]

@[simp] theorem D2τPrimeAll_Du_arr_eq (σ τ : Typ .Du) :
    D2τPrimeAll (.arr σ τ) = .LUn := by
  simp [D2τPrimeAll]

@[simp] theorem D2τ_arr_eq (σ τ : Typ .Pr) :
    D2τ (.arr σ τ) = D2Arr := by
  simp [D2τ, D2τPrime, D2τPrimeAll, D2Arr]

/-- `D₁` is the identity on target types.  This theorem is intentionally stated
for all target types because many target helper functions have higher-order
function types; the source-only Dyn translation must never be applied to them. -/
theorem D1τAll_target_id : (τ : Typ .Du) → D1τAll τ = τ
  | .Un => rfl
  | .Inte => rfl
  | .R => rfl
  | .prod σ τ => by
      simp [D1τAll, D1τAll_target_id σ, D1τAll_target_id τ]
  | .sum σ τ => by
      simp [D1τAll, D1τAll_target_id σ, D1τAll_target_id τ]
  | .array τ => by
      simp [D1τAll, D1τAll_target_id τ]
  | .arr σ τ => by
      simp [D1τAll]
  | .EVM Γ τ => rfl
  | .Lin τ => rfl

/-- Ordinary source-to-target translation for non-AD interpretation of function
values.  Unlike `D₁`, this maps source arrows to ordinary target arrows. -/
@[simp] theorem dut_arr_eq (σ τ : Typ .Pr) :
    dut (.arr σ τ) = .arr (dut σ) (dut τ) := by
  simp [dut, dutAll]

abbrev D1Γ (Γ : Env .Pr) : Env .Du := List.map D1τ Γ

/-- Linear cotangent environment associated to a source context. -/
abbrev D2Γl (Γ : Env .Pr) : LEnv := List.map D2τPrime Γ

abbrev D2Γtup (Γ : Env .Pr) : Typ .Du := LEτ (D2Γl Γ)

abbrev D2Γ (Γ : Env .Pr) : Typ .Du := .EVM (D2Γl Γ) .Un

/-- The compact cotangent tuple stored in `Dyn` for a lambda closure. -/
abbrev DClosureTup (Γclo : Env .Pr) : Typ .Du := LEτ (D2Γl Γclo)

/-- Linear environment of a compact closure cotangent. -/
abbrev D2ClosureΓl (Γclo : Env .Pr) : LEnv := D2Γl Γclo

/-- EVM type of a compact closure cotangent update. -/
abbrev D2ClosureΓ (Γclo : Env .Pr) : Typ .Du := .EVM (D2ClosureΓl Γclo) .Un

/-- Map a source closure injection through the primal translation. -/
abbrev D1ClosureInj {Γclo Γ : Env .Pr} (inj : EnvInj Γclo Γ) :
    EnvInj (List.map D1τ Γclo) (List.map D1τ Γ) :=
  mapIdxInj D1τ inj

/-- Map a source closure injection through the cotangent translation. -/
abbrev D2ClosureInj {Γclo Γ : Env .Pr} (inj : EnvInj Γclo Γ) :
    LEnvInj (D2Γl Γclo) (D2Γl Γ) :=
  mapIdxInj D2τPrime inj

/-- Value-level form of a translated higher-order function. -/
abbrev DFunValRep (σ τ : Typ .Pr) : Type := Rep (D1Arr σ τ)

/-- Value-level form of the result returned by a translated function. -/
abbrev DFunResultRep (σ τ : Typ .Pr) : Type := Rep (D1ArrResult σ τ)

/-- Value-level form of the local reverse map packaged in `D₁(A → B)`. -/
abbrev DFunLocalRevRep (σ τ : Typ .Pr) : Type := Rep (D1ArrLocalRev σ τ)

/-- Value-level form of the pair returned by a function local reverse map. -/
abbrev DFunLocalPairRep (σ τ : Typ .Pr) : Type := Rep (.prod (.Lin .Dyn) (D2τ σ))

/-- Apply a translated function value to a translated argument value. -/
@[reducible] def dfunApplyVal {σ τ : Typ .Pr}
    (F : DFunValRep σ τ) (x : Rep (D1τ σ)) : DFunResultRep σ τ × Int :=
  F x

/-- Primal component of a translated function-result value. -/
@[reducible] def dfunResultPrimalVal {σ τ : Typ .Pr}
    (r : DFunResultRep σ τ) : Rep (D1τ τ) :=
  r.1

/-- Local reverse component of a translated function-result value. -/
@[reducible] def dfunResultRevVal {σ τ : Typ .Pr}
    (r : DFunResultRep σ τ) : DFunLocalRevRep σ τ :=
  r.2

/-- Apply the local reverse map of a translated function result. -/
@[reducible] def dfunLocalRevVal {σ τ : Typ .Pr}
    (rev : DFunLocalRevRep σ τ) (db : Rep (D2τ τ)) : DFunLocalPairRep σ τ × Int :=
  rev db

/-- Dynamic function cotangent component returned by a local reverse map. -/
@[reducible] def dfunLocalDynVal {σ τ : Typ .Pr}
    (p : DFunLocalPairRep σ τ) : DynRep :=
  p.1

/-- Argument cotangent component returned by a local reverse map. -/
@[reducible] def dfunLocalArgVal {σ τ : Typ .Pr}
    (p : DFunLocalPairRep σ τ) : Rep (D2τ σ) :=
  p.2

/-- Coerce a value of the named function translation into the recursive `D₁` type. -/
@[reducible] def d1arrRepIn {σ τ : Typ .Pr}
    (f : DFunValRep σ τ) : Rep (D1τ (.arr σ τ)) := by
  simpa [DFunValRep, D1τ, D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev,
    D2τ, D2τPrime, D2τPrimeAll] using f

/-- Coerce a value of the recursive `D₁` function type into the named shape. -/
@[reducible] def d1arrRepOut {σ τ : Typ .Pr}
    (f : Rep (D1τ (.arr σ τ))) : DFunValRep σ τ := by
  simpa [DFunValRep, D1τ, D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev,
    D2τ, D2τPrime, D2τPrimeAll] using f

/-- Coerce the `Dyn` function cotangent into the recursive cotangent type. -/
@[reducible] def d2arrRepIn {σ τ : Typ .Pr}
    (d : DynRep) : Rep (D2τ (.arr σ τ)) := by
  simpa [D2τ, D2τPrime, D2τPrimeAll, D2Arr] using d

/-- Coerce the recursive function cotangent into the concrete `Dyn` carrier. -/
@[reducible] def d2arrRepOut {σ τ : Typ .Pr}
    (d : Rep (D2τ (.arr σ τ))) : DynRep := by
  simpa [D2τ, D2τPrime, D2τPrimeAll, D2Arr] using d

/-- A translated function value always has the explicit Dyn shape. -/
@[simp] theorem Rep_D1_arr_eq (σ τ : Typ .Pr) :
    Rep (D1τ (.arr σ τ)) = DFunValRep σ τ := by
  simp [DFunValRep, D1τ, D1τAll, D1Arr, D1ArrResult,
    D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll, Rep]

/-- A function cotangent is the dynamic carrier. -/
@[simp] theorem Rep_D2_arr_eq (σ τ : Typ .Pr) :
    Rep (D2τ (.arr σ τ)) = DynRep := by
  simp [D2τ, D2τPrime, D2τPrimeAll, Rep, LinRep, D2Arr]

/-- Opaque semantic lifting for higher-order variables.  Syntactic lambdas are
translated by `chad`; this operation accounts for already-supplied function
values in source environments.  Its laws are expressed by `HOFunRel`. -/
axiom primalFun (σ τ : Typ .Pr) : Rep (.arr σ τ) → DFunValRep σ τ

def primal : (τ : Typ .Pr) → Rep τ → Rep (D1τ τ)
  | .Un, x => by simpa [D1τ, D1τAll, Rep] using x
  | .Inte, x => by simpa [D1τ, D1τAll, Rep] using x
  | .R, x => by simpa [D1τ, D1τAll, Rep] using x
  | .prod σ τ, x => by
      simpa [D1τ, D1τAll, Rep] using ((primal σ x.1, primal τ x.2) : Rep (D1τ σ) × Rep (D1τ τ))
  | .sum σ τ, Sum.inl x => by
      simpa [D1τ, D1τAll, Rep] using (Sum.inl (primal σ x) : Sum (Rep (D1τ σ)) (Rep (D1τ τ)))
  | .sum σ τ, Sum.inr y => by
      simpa [D1τ, D1τAll, Rep] using (Sum.inr (primal τ y) : Sum (Rep (D1τ σ)) (Rep (D1τ τ)))
  | .array τ, xs => by
      simpa [D1τ, D1τAll, Rep] using (xs.map (fun x => primal τ x) : List (Rep (D1τ τ)))
  | .arr σ τ, f => d1arrRepIn (σ := σ) (τ := τ) (primalFun σ τ f)

@[simp] theorem primal_arr_eq (σ τ : Typ .Pr) (f : Rep (.arr σ τ)) :
    primal (.arr σ τ) f = d1arrRepIn (σ := σ) (τ := τ) (primalFun σ τ f) := by
  simp [primal]

/-- Logical relation for one application of an ambient source function value.
It exposes both halves of the translated result: the primal result and the local
reverse map.  The latter is the value-level counterpart of the Dyn rule used by
syntactic applications. -/
structure HOFunAppRel (σ τ : Typ .Pr)
    (f : Rep (.arr σ τ)) (F : DFunValRep σ τ) (x : Rep σ) : Prop where
  result_primal :
    let rx := f x
    let rF := dfunApplyVal F (primal σ x)
    dfunResultPrimalVal rF.1 = primal τ rx.1
  local_reverse_cost_nonneg :
    ∀ db : Rep (D2τ τ),
      0 ≤ (dfunLocalRevVal (dfunResultRevVal (dfunApplyVal F (primal σ x)).1) db).2

/-- Higher-order logical relation for ambient source function values.  A source
function value that arrives through the environment is not syntax, so its
translated primal is supplied by `primalFun`; this relation records the semantic
obligation needed for applying such values and for using their local reverse
component.  Syntactic lambdas are handled separately by the structural `lam`
case of the CHAD proof. -/
structure HOFunRel (σ τ : Typ .Pr)
    (f : Rep (.arr σ τ)) (F : DFunValRep σ τ) : Prop where
  app_related : ∀ x : Rep σ, HOFunAppRel σ τ f F x

/-- Assumptions for ambient higher-order values.  This is separated from the
syntax-directed lambda/application cases so that first-order environments do not
need to provide any extra data. -/
class HigherOrderValueLaws : Prop where
  primalFun_related :
    ∀ (σ τ : Typ .Pr) (f : Rep (.arr σ τ)), HOFunRel σ τ f (primalFun σ τ f)

theorem primalFun_result_primal [HigherOrderValueLaws]
    (σ τ : Typ .Pr) (f : Rep (.arr σ τ)) (x : Rep σ) :
    let rx := f x
    let rF := primalFun σ τ f (primal σ x)
    rF.1.1 = primal τ rx.1 := by
  simpa [dfunApplyVal, dfunResultPrimalVal] using
    ((HigherOrderValueLaws.primalFun_related σ τ f).app_related x).result_primal

theorem primalFun_local_reverse_cost_nonneg [HigherOrderValueLaws]
    (σ τ : Typ .Pr) (f : Rep (.arr σ τ)) (x : Rep σ) (db : Rep (D2τ τ)) :
    0 ≤ (dfunLocalRevVal
      (dfunResultRevVal (dfunApplyVal (primalFun σ τ f) (primal σ x)).1) db).2 :=
  ((HigherOrderValueLaws.primalFun_related σ τ f).app_related x).local_reverse_cost_nonneg db

def duPrim {σ τ : Typ .Pr} (op : Primop .Pr σ τ) : Primop .Du (dut σ) (dut τ) :=
  match op with
  | .ADD => .ADD
  | .MUL => .MUL
  | .NEG => .NEG
  | .LIT x => .LIT x
  | .IADD => .IADD
  | .IMUL => .IMUL
  | .INEG => .INEG
  | .SIGN => .SIGN

def d1Prim {σ τ : Typ .Pr} (op : Primop .Pr σ τ) : Primop .Du (D1τ σ) (D1τ τ) :=
  match op with
  | .ADD => by simpa [D1τ, D1τAll] using (Primop.ADD : Primop .Du (.prod .R .R) .R)
  | .MUL => by simpa [D1τ, D1τAll] using (Primop.MUL : Primop .Du (.prod .R .R) .R)
  | .NEG => by simpa [D1τ, D1τAll] using (Primop.NEG : Primop .Du .R .R)
  | .LIT x => by simpa [D1τ, D1τAll] using (Primop.LIT x : Primop .Du .Un .R)
  | .IADD => by simpa [D1τ, D1τAll] using (Primop.IADD : Primop .Du (.prod .Inte .Inte) .Inte)
  | .IMUL => by simpa [D1τ, D1τAll] using (Primop.IMUL : Primop .Du (.prod .Inte .Inte) .Inte)
  | .INEG => by simpa [D1τ, D1τAll] using (Primop.INEG : Primop .Du .Inte .Inte)
  | .SIGN => by simpa [D1τ, D1τAll] using (Primop.SIGN : Primop .Du .R (.sum (.sum .Un .Un) .Un))
theorem niceprim {σ τ : Typ .Pr} (op : Primop .Pr σ τ) :
    D1τ σ = dut σ ∧ D1τ τ = dut τ := by
  cases op <;> simp [D1τ, D1τAll, dut, dutAll]

def dprimPrime {σ τ : Typ .Pr} (op : Primop .Pr σ τ) :
    Term .Du (D2τ τ :: D1τ σ :: []) (D2τ σ) := by
  cases op with
  | ADD =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.lpair (.var .Z) (.var .Z) :
          Term .Du ((.Lin .LR) :: (.prod .R .R) :: []) (.Lin (.prod .LR .LR)))
  | MUL =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.lpair
          (.prim .LSCALE (.pair (.var .Z) (.sndE (.var (.S .Z)))))
          (.prim .LSCALE (.pair (.var .Z) (.fstE (.var (.S .Z))))) :
          Term .Du ((.Lin .LR) :: (.prod .R .R) :: []) (.Lin (.prod .LR .LR)))
  | NEG =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.prim .LNEG (.var .Z) : Term .Du ((.Lin .LR) :: .R :: []) (.Lin .LR))
  | LIT x =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.lunit : Term .Du ((.Lin .LR) :: .Un :: []) (.Lin .LUn))
  | IADD =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.lpair .lunit .lunit :
          Term .Du ((.Lin .LUn) :: (.prod .Inte .Inte) :: []) (.Lin (.prod .LUn .LUn)))
  | IMUL =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.lpair .lunit .lunit :
          Term .Du ((.Lin .LUn) :: (.prod .Inte .Inte) :: []) (.Lin (.prod .LUn .LUn)))
  | INEG =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.lunit : Term .Du ((.Lin .LUn) :: .Inte :: []) (.Lin .LUn))
  | SIGN =>
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll] using
        (.prim .LZERO .lunit :
          Term .Du ((.Lin (.sum (.sum .LUn .LUn) .LUn)) :: .R :: []) (.Lin .LR))
def «dprim'» {σ τ : Typ .Pr} (op : Primop .Pr σ τ) :
    Term .Du (D2τ τ :: D1τ σ :: []) (D2τ σ) :=
  dprimPrime op

def dprim {Γ : Env .Du} {σ τ : Typ .Pr} (op : Primop .Pr σ τ)
    (p : Term .Du Γ (D1τ σ)) (d : Term .Du Γ (D2τ τ)) : Term .Du Γ (D2τ σ) :=
  .letE p (.letE (sink1 d) (sink (.WCopy (.WCopy (Weakening.WCut (Γ' := Γ)))) (dprimPrime op)))

inductive Val : (tag : PDTag) → Env tag → Type where
  | empty {tag : PDTag} : Val tag []
  | push {tag : PDTag} {Γ : Env tag} {τ : Typ tag} :
      Rep τ → Val tag Γ → Val tag (τ :: Γ)

def valprj {tag : PDTag} {Γ : Env tag} {τ : Typ tag} (env : Val tag Γ) (idx : Idx Γ τ) : Rep τ :=
  match env, idx with
  | .empty, i => nomatch i
  | .push x _, .Z => x
  | .push _ env', .S i => valprj env' i

def primalVal {Γ : Env .Pr} (env : Val .Pr Γ) : Val .Du (D1Γ Γ) :=
  match env with
  | .empty => .empty
  | .push (τ := τ) x rest => .push (primal τ x) (primalVal rest)

def buildValFromInj {tag : PDTag} {Γ Γclo : Env tag}
    (inj : EnvInj Γclo Γ)
    (env : Val tag Γ) : Val tag Γclo :=
  match Γclo with
  | [] => .empty
  | _τ :: Γrest =>
      .push (valprj env (inj .Z))
        (buildValFromInj (fun {ρ : Typ tag} (i : Idx Γrest ρ) => inj (.S i)) env)


/-- Total default values used only to make the list-backed array semantics total.
The paper assumes well-formed array programs, so the default branches correspond to
out-of-bounds indexing and empty folds. -/
def defaultRep : {tag : PDTag} → (τ : Typ tag) → Rep τ
  | _, .Un => ()
  | _, .Inte => 0
  | _, .R => 0.0
  | _, .prod σ τ => (defaultRep σ, defaultRep τ)
  | _, .sum σ _ => Sum.inl (defaultRep σ)
  | _, .array _ => []
  | _, .arr _ τ => fun _ => (defaultRep τ, one)
  | .Du, .EVM _ τ => LACM.pure (defaultRep τ)
  | .Du, .Lin τ => (zerov τ).1

def arrayListGetD {α : Type u} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, Nat.succ n, d => arrayListGetD xs n d

def arrayIndexCore {α : Type u} (xs : List α) (i : Int) (default : α) : α :=
  arrayListGetD xs i.toNat default

def arrayBuildCoreFrom {α : Type u} (start : Nat) : Nat → (Int → α) → List α
  | 0, _ => []
  | Nat.succ n, f => f (Int.ofNat start) :: arrayBuildCoreFrom (Nat.succ start) n f

def arrayBuildCoreAux {α : Type u} (n : Nat) (f : Int → α) : List α :=
  arrayBuildCoreFrom 0 n f

def arrayBuildCore {α : Type u} (n : Int) (f : Int → α) : List α :=
  arrayBuildCoreAux n.toNat f

def arrayUpdatePlus {α : Type u} (plus : α → α → α) : List α → Nat → α → List α
  | [], _, _ => []
  | x :: xs, 0, v => plus x v :: xs
  | x :: xs, Nat.succ n, v => x :: arrayUpdatePlus plus xs n v

def arrayScatterCore {α : Type u} (plus : α → α → α)
    (base : List α) (pairs : List (Int × α)) : List α :=
  pairs.foldl (fun acc p => arrayUpdatePlus plus acc p.1.toNat p.2) base

def arrayZipWithCore {α : Type u} {β : Type v} {γ : Type u}
    (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: arrayZipWithCore f xs ys

def arrayUnzipCore {α : Type u} {β : Type v} : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: rest =>
      let r := arrayUnzipCore rest
      (x :: r.1, y :: r.2)

def arrayEnumerateFromCore {α : Type u} : Nat → List α → List (Int × α)
  | _, [] => []
  | n, x :: xs => (Int.ofNat n, x) :: arrayEnumerateFromCore (Nat.succ n) xs

def arrayEnumerateCore {α : Type u} (xs : List α) : List (Int × α) :=
  arrayEnumerateFromCore 0 xs

def lacmSequenceUnit {Γ : LEnv} : List (LACM Γ Unit) → LACM Γ Unit
  | [] => LACM.pure ()
  | m :: ms => LACM.bind m (fun _ => (lacmSequenceUnit ms, one))

def lacmScopeDrop {Γ : LEnv} {τ : LTyp} {α : Type u}
    (zero : LinRep τ) (mcall : LACM (τ :: Γ) α × Int) : LACM Γ Unit :=
  fun env =>
    let r := LACM.scope zero mcall.1 env
    ((), r.2.1, one + mcall.2 + r.2.2)


/-- Abstract Dyn encoder for compact closure cotangent environments. -/
axiom dynEncode (Γl : LEnv) : LEtup Γl → DynRep

/-- Abstract Dyn decoder.  Running this action adds the decoded compact
environment to the current linear environment. -/
axiom dynDecode (Γl : LEnv) : DynRep → LACM Γl Unit

/-- Laws required of the chosen `Dyn` encoder/decoder.  `Dyn` itself is a
universal carrier; correctness and complexity are parameterized by these laws so
the theorem statements expose exactly what the higher-order extension assumes. -/
class DynLaws : Prop where
  decode_encode_add (Γl : LEnv) (dΓ : LEtup Γl) (denv : LEtup Γl) :
    let r := LACM.run (dynDecode Γl (dynEncode Γl dΓ)) denv
    r.2.1 = addLEtup Γl dΓ denv
  encode_cost (Γl : LEnv) (dΓ : LEtup Γl) :
    (1 : Int) ≤ one + intLength Γl
  decode_cost (Γl : LEnv) (d : DynRep) :
    (1 : Int) ≤ one + intLength Γl

/-- Retraction law required by the lambda/application correctness argument. -/
theorem dynDecode_encode_add [DynLaws] (Γl : LEnv)
    (dΓ : LEtup Γl) (denv : LEtup Γl) :
  let r := LACM.run (dynDecode Γl (dynEncode Γl dΓ)) denv
  r.2.1 = addLEtup Γl dΓ denv :=
  DynLaws.decode_encode_add Γl dΓ denv

/-- Cost law for the chosen Dyn representation.  It states the intended
amortised linear bound in the compact environment size. -/
theorem dynEncode_cost [DynLaws] (Γl : LEnv) (dΓ : LEtup Γl) :
    (1 : Int) ≤ one + intLength Γl :=
  DynLaws.encode_cost Γl dΓ

theorem dynDecode_cost [DynLaws] (Γl : LEnv) (d : DynRep) :
    (1 : Int) ≤ one + intLength Γl :=
  DynLaws.decode_cost Γl d

/-- Scatter an `EVM` action on a compact closure environment into an ambient
environment.  It is implemented semantically by running the compact action from
zero and adding the resulting compact tuple into the ambient accumulator. -/
def scatterLACM {Γsrc Γdst : LEnv} (inj : LEnvInj Γsrc Γdst)
    (m : LACM Γsrc Unit) : LACM Γdst Unit :=
  fun denv =>
    let r := LACM.run m (zeroLEtup Γsrc)
    ((), addLEtup Γdst (scatterLEtup inj r.2.1) denv, one + r.2.2)

def linFstD {σ τ : LTyp} (x : LinRep (.prod σ τ)) : LinRep σ :=
  match x with
  | none => (zerov σ).1
  | some xy => xy.1

def linSndD {σ τ : LTyp} (x : LinRep (.prod σ τ)) : LinRep τ :=
  match x with
  | none => (zerov τ).1
  | some xy => xy.2

inductive FoldTree (α : Type u) (β : Type v) : Type (max u v) where
  | leaf : α → FoldTree α β
  | node : FoldTree α β → α → β → FoldTree α β → FoldTree α β
  deriving Repr

namespace FoldTree

def getA {α : Type u} {β : Type v} : FoldTree α β → α
  | .leaf x => x
  | .node _ x _ _ => x

def unTree {Γ : LEnv} {δ : Type u} {α : Type v} {β : Type u}
    (split : δ → β → LACM Γ (δ × δ)) : δ → FoldTree α β → LACM Γ (List δ → List δ)
  | d, .leaf _ => fun env => ((fun xs => d :: xs), env, one)
  | d, .node t₁ _ f t₂ => fun env =>
      let r := split d f env
      let r₁ := unTree split r.1.1 t₁ r.2.1
      let r₂ := unTree split r.1.2 t₂ r₁.2.1
      ((fun xs => r₁.1 (r₂.1 xs)), r₂.2.1, one + r.2.2 + r₁.2.2 + r₂.2.2)

end FoldTree

def eval {tag : PDTag} {Γ : Env tag} {τ : Typ tag}
    (env : Val tag Γ) (tm : Term tag Γ τ) : Rep τ × Int :=
  match tm with
  | .var i => (valprj env i, one)
  | .letE rhs body =>
      let r1 := eval env rhs
      let r2 := eval (.push r1.1 env) body
      (r2.1, one + r1.2 + r2.2)
  | .prim op e =>
      let r := eval env e
      (evalprim op r.1, one + r.2)
  | .unit => ((), one)
  | .pair e1 e2 =>
      let r1 := eval env e1
      let r2 := eval env e2
      ((r1.1, r2.1), one + r1.2 + r2.2)
  | .fstE e =>
      let r := eval env e
      (r.1.1, one + r.2)
  | .sndE e =>
      let r := eval env e
      (r.1.2, one + r.2)
  | .inl e =>
      let r := eval env e
      (Sum.inl r.1, one + r.2)
  | .inr e =>
      let r := eval env e
      (Sum.inr r.1, one + r.2)
  | .caseE e1 e2 e3 =>
      let r := eval env e1
      match r.1 with
      | Sum.inl x =>
          let r2 := eval (.push x env) e2
          (r2.1, one + r.2 + r2.2)
      | Sum.inr y =>
          let r3 := eval (.push y env) e3
          (r3.1, one + r.2 + r3.2)
  | .arrayBuild (τ := τ) n body =>
      let rn := eval env n
      let idxs := List.range rn.1.toNat
      let rs := idxs.map (fun j => eval (.push (Int.ofNat j) env) body)
      let vals := rs.map (fun r => r.1)
      let cbody := rs.foldl (fun c r => one + c + r.2) one
      (vals, one + rn.2 + cbody)
  | .arrayIndex (τ := τ) xs i =>
      let rxs := eval env xs
      let ri := eval env i
      (arrayIndexCore rxs.1 ri.1 (defaultRep τ), one + rxs.2 + ri.2)
  | .arrayFold (τ := τ) body xs =>
      let rxs := eval env xs
      match rxs.1 with
      | [] => (defaultRep τ, one + rxs.2 + one)
      | x :: rest =>
          let step := fun (state : Rep τ × Int) (y : Rep τ) =>
            let r := eval (.push (state.1, y) env) body
            (r.1, one + state.2 + r.2)
          let rf := rest.foldl step (x, one)
          (rf.1, one + rxs.2 + rf.2)
  | .lam (Γclo := Γclo) inj body =>
      ((fun x => eval (.push x (buildValFromInj inj env)) body), one + intLength Γclo)
  | .app e1 e2 =>
      let rf := eval env e1
      let rx := eval env e2
      let ry := rf.1 rx.1
      (ry.1, one + rf.2 + rx.2 + ry.2)
  | .pureevm e =>
      let r := eval env e
      (LACM.pure r.1, one + r.2)
  | .bindevm e1 e2 =>
      let r1 := eval env e1
      let r2 := eval env e2
      (LACM.bind r1.1 r2.1, one + r1.2 + r2.2)
  | .runevm (Γl := Γl) e1 e2 =>
      let r1 := eval env e1
      let r2 := eval env e2
      let rr := LACM.run r1.1 (repLEτToLEtup Γl r2.1)
      ((rr.1, LEtupToRepLEτ Γl rr.2.1), one + r1.2 + r2.2 + rr.2.2)
  | .addevm idx e =>
      let r := eval env e
      (LACM.add idx r.1, one + r.2)
  | .scopeevm e1 e2 =>
      let r1 := eval env e1
      let r2 := eval env e2
      (LACM.scope r1.1 r2.1, one + r1.2 + r2.2)
  | .toDyn (Γl := Γl) e =>
      let r := eval env e
      (dynEncode Γl (repLEτToLEtup Γl r.1), one + r.2 + intLength Γl)
  | .fromDyn (Γl := Γl) e =>
      let r := eval env e
      (dynDecode Γl r.1, one + r.2 + intLength Γl)
  | .scatterevm inj e =>
      let r := eval env e
      (scatterLACM inj r.1, one + r.2)
  | .ldyntzero => (dynZero, one)
  | .larrayzero => (Bag.empty, one)
  | .larrayone i d =>
      let ri := eval env i
      let rd := eval env d
      (Bag.one (ri.1, rd.1), one + ri.2 + rd.2)
  | .larraybag xs =>
      let rxs := eval env xs
      (Bag.array rxs.1, one + rxs.2 + intLength rxs.1)
  | .larraycollect d =>
      let rd := eval env d
      (Bag.collect rd.1, one + rd.2 + Bag.collectCost rd.1)
  | .arrayUnzipD xs =>
      let rxs := eval env xs
      let rz := arrayUnzipCore rxs.1
      (rz, one + rxs.2 + intLength rxs.1)
  | .arrayScatterD (τ := τ) base pairs =>
      let rb := eval env base
      let rp := eval env pairs
      (arrayScatterCore (fun x y => (plusv τ x y).1) rb.1 rp.1, one + rb.2 + rp.2 + intLength rb.1 + intLength rp.1)
  | .arrayZipWithScopeD (Γl := Γl) fs ds =>
      let rfs := eval env fs
      let rds := eval env ds
      let actions := arrayZipWithCore
        (fun f d => lacmScopeDrop (Γ := Γl) (τ := .LUn) (zerov .LUn).1 (f d))
        rfs.1 rds.1
      (actions, one + rfs.2 + rds.2 + intLength rfs.1 + intLength rds.1)
  | .arraySequenceUnitD acts =>
      let racts := eval env acts
      (lacmSequenceUnit racts.1, one + racts.2 + intLength racts.1)
  | .arrayFoldAD (Γl := Γl) (α := α) (δ := δ) xs body =>
      let rxs := eval env xs
      let mkLeaf (x : Rep α) : FoldTree (Rep α) (LinRep δ → LACM (.prod δ δ :: Γl) Unit × Int) :=
        FoldTree.leaf x
      let stepTree := fun
          (state : FoldTree (Rep α) (LinRep δ → LACM (.prod δ δ :: Γl) Unit × Int) × Int)
          (y : Rep α) =>
            let t := state.1
            let rb := eval (.push (FoldTree.getA t, y) env) body
            let t' := FoldTree.node t rb.1.1 rb.1.2 (FoldTree.leaf y)
            (t', one + state.2 + rb.2)
      match rxs.1.1 with
      | [] =>
          let bp := fun _ => (LACM.pure (), one)
          ((defaultRep α, bp), one + rxs.2 + one)
      | x :: rest =>
          let treeRes := rest.foldl stepTree (mkLeaf x, one)
          let tree := treeRes.1
          let split := fun d' f =>
            fun denv =>
              let call := f d'
              let scopedRun := LACM.scope (zerov (.prod δ δ)).1 call.1 denv
              let pairCtg := scopedRun.1.1
              ((linFstD pairCtg, linSndD pairCtg), scopedRun.2.1, one + call.2 + scopedRun.2.2)
          let bp := fun d =>
            (LACM.bind (FoldTree.unTree split d tree)
              (fun lf => rxs.1.2 (Bag.array (arrayEnumerateCore (lf [])))), one)
          ((FoldTree.getA tree, bp), one + rxs.2 + treeRes.2)
  | .lunit => ((), one)
  | .lpair e1 e2 =>
      let r1 := eval env e1
      let r2 := eval env e2
      (some (r1.1, r2.1), one + r1.2 + r2.2)
  | .lfstE (σ := σ) e =>
      let r := eval env e
      match r.1 with
      | none =>
          let z := zerov σ
          (z.1, one + r.2 + z.2)
      | some xy => (xy.1, one + r.2)
  | .lsndE (τ := τ) e =>
      let r := eval env e
      match r.1 with
      | none =>
          let z := zerov τ
          (z.1, one + r.2 + z.2)
      | some xy => (xy.2, one + r.2)
  | .lpairzero => (none, one)
  | .linl e =>
      let r := eval env e
      (some (Sum.inl r.1), one + r.2)
  | .linr e =>
      let r := eval env e
      (some (Sum.inr r.1), one + r.2)
  | .lcastl (σ := σ) e =>
      let r := eval env e
      match r.1 with
      | none =>
          let z := zerov σ
          (z.1, one + r.2 + z.2)
      | some (Sum.inl x) => (x, one + r.2)
      | some (Sum.inr _) =>
          let z := zerov σ
          (z.1, one + r.2 + z.2)
  | .lcastr (τ := τ) e =>
      let r := eval env e
      match r.1 with
      | none =>
          let z := zerov τ
          (z.1, one + r.2 + z.2)
      | some (Sum.inl _) =>
          let z := zerov τ
          (z.1, one + r.2 + z.2)
      | some (Sum.inr y) => (y, one + r.2)
  | .lsumzero => (none, one)

def cost {tag : PDTag} {Γ : Env tag} {τ : Typ tag} (env : Val tag Γ) (e : Term tag Γ τ) : Int :=
  (eval env e).2

def zerot {Γ : Env .Du} : (τ : Typ .Pr) → Term .Du Γ (D2τ τ)
  | .Un => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.lunit : Term .Du Γ (.Lin .LUn))
  | .Inte => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.lunit : Term .Du Γ (.Lin .LUn))
  | .R => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.prim Primop.LZERO Term.lunit : Term .Du Γ (.Lin .LR))
  | .prod σ τ => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.lpairzero : Term .Du Γ (.Lin (.prod (D2τPrime σ) (D2τPrime τ))))
  | .sum σ τ => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.lsumzero : Term .Du Γ (.Lin (.sum (D2τPrime σ) (D2τPrime τ))))
  | .array τ => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.larrayzero : Term .Du Γ (.Lin (.array (D2τPrime τ))))
  | .arr σ τ => by
      simpa [D2τ, D2τPrime, D2τPrimeAll] using (Term.ldyntzero : Term .Du Γ (.Lin .Dyn))

/-- Zero term for an arbitrary linear type. -/
def lzerot {Γ : Env .Du} : (τ : LTyp) → Term .Du Γ (.Lin τ)
  | .LUn => .lunit
  | .LR => .prim Primop.LZERO .lunit
  | .Dyn => .ldyntzero
  | .prod σ τ => .lpairzero
  | .sum σ τ => .lsumzero
  | .array τ => .larrayzero

/-- Zero term for a linear environment tuple. -/
def zeroLETerm {Γ : Env .Du} : (Γl : LEnv) → Term .Du Γ (LEτ Γl)
  | [] => .unit
  | τ :: Γl => .pair (lzerot τ) (zeroLETerm Γl)

/-- Pack the reverse action of a lambda body into the Dyn-shaped local reverse
map.  The action has environment `δ :: Γl`; after running it from zero, the
head `δ` is returned directly and the compact closure environment `Γl` is
encoded in `Dyn`. -/
def packDynScoped {Γ : Env .Du} {Γl : LEnv} {δ : LTyp}
    (bodyReverse : Term .Du Γ (.EVM (δ :: Γl) .Un)) :
    Term .Du Γ (.prod (.Lin .Dyn) (.Lin δ)) :=
  .letE (.runevm bodyReverse (zeroLETerm (δ :: Γl)))
    (.pair
      (.toDyn (Γl := Γl) (.sndE (.sndE (.var .Z))))
      (.fstE (.sndE (.var .Z))))

@[reducible] def d1pairTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (a : Term .Du Γ (D1τ σ)) (b : Term .Du Γ (D1τ τ)) :
    Term .Du Γ (D1τ (.prod σ τ)) :=
  Term.pair a b

@[reducible] def d1inlTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (a : Term .Du Γ (D1τ σ)) : Term .Du Γ (D1τ (.sum σ τ)) :=
  Term.inl (τ := D1τ τ) a

@[reducible] def d1inrTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (b : Term .Du Γ (D1τ τ)) : Term .Du Γ (D1τ (.sum σ τ)) :=
  Term.inr (σ := D1τ σ) b

@[reducible] def d1fstTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (p : Term .Du Γ (D1τ (.prod σ τ))) : Term .Du Γ (D1τ σ) :=
  Term.fstE p

@[reducible] def d1sndTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (p : Term .Du Γ (D1τ (.prod σ τ))) : Term .Du Γ (D1τ τ) :=
  Term.sndE p

@[reducible] def d1caseTerm {Γ : Env .Du} {σ τ : Typ .Pr} {ρ : Typ .Du}
    (scrut : Term .Du Γ (D1τ (.sum σ τ)))
    (left : Term .Du (D1τ σ :: Γ) ρ)
    (right : Term .Du (D1τ τ :: Γ) ρ) : Term .Du Γ ρ :=
  Term.caseE scrut left right

@[reducible] def d2lpairTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (a : Term .Du Γ (D2τ σ)) (b : Term .Du Γ (D2τ τ)) :
    Term .Du Γ (D2τ (.prod σ τ)) :=
  Term.lpair a b

@[reducible] def d2lfstTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (d : Term .Du Γ (D2τ (.prod σ τ))) : Term .Du Γ (D2τ σ) :=
  Term.lfstE d

@[reducible] def d2lsndTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (d : Term .Du Γ (D2τ (.prod σ τ))) : Term .Du Γ (D2τ τ) :=
  Term.lsndE d

@[reducible] def d2linlTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (a : Term .Du Γ (D2τ σ)) : Term .Du Γ (D2τ (.sum σ τ)) :=
  Term.linl (τ := D2τPrime τ) a

@[reducible] def d2linrTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (b : Term .Du Γ (D2τ τ)) : Term .Du Γ (D2τ (.sum σ τ)) :=
  Term.linr (σ := D2τPrime σ) b

@[reducible] def d2lcastlTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (d : Term .Du Γ (D2τ (.sum σ τ))) : Term .Du Γ (D2τ σ) :=
  Term.lcastl d

@[reducible] def d2lcastrTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (d : Term .Du Γ (D2τ (.sum σ τ))) : Term .Du Γ (D2τ τ) :=
  Term.lcastr d

@[reducible] def d1UnitInTerm {Γ : Env .Du}
    (u : Term .Du Γ .Un) : Term .Du Γ (D1τ (.Un : Typ .Pr)) := by
  simpa [D1τ, D1τAll] using u

/-- Coerce the syntactic array-shaped `D₁` into the named translation.
Lean's kernel does not use simp lemmas during ordinary unification, so the
array/function branches use these small wrappers at the points where a
constructor expects the unfolded shape. -/
@[reducible] def d1IntTerm {Γ : Env .Du}
    (n : Term .Du Γ (D1τ (Typ.Inte : Typ .Pr))) : Term .Du Γ Typ.Inte := by
  simpa [D1τ, D1τAll] using n

@[reducible] def d1arrayInTerm {Γ : Env .Du} {τ : Typ .Pr}
    (xs : Term .Du Γ (.array (D1τ τ))) : Term .Du Γ (D1τ (.array τ)) := by
  simpa [D1τ, D1τAll] using xs

@[reducible] def d1arrayOutTerm {Γ : Env .Du} {τ : Typ .Pr}
    (xs : Term .Du Γ (D1τ (.array τ))) : Term .Du Γ (.array (D1τ τ)) := by
  simpa [D1τ, D1τAll] using xs

@[reducible] def d2arrayInTerm {Γ : Env .Du} {τ : Typ .Pr}
    (d : Term .Du Γ (.Lin (.array (D2τPrime τ)))) : Term .Du Γ (D2τ (.array τ)) := by
  simpa [D2τ, D2τPrime, D2τPrimeAll] using d

@[reducible] def d2arrayOutTerm {Γ : Env .Du} {τ : Typ .Pr}
    (d : Term .Du Γ (D2τ (.array τ))) : Term .Du Γ (.Lin (.array (D2τPrime τ))) := by
  simpa [D2τ, D2τPrime, D2τPrimeAll] using d

@[reducible] def d1arrInTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (f : Term .Du Γ (D1Arr σ τ)) : Term .Du Γ (D1τ (.arr σ τ)) := by
  simpa [D1τ, D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll] using f

@[reducible] def d1arrOutTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (f : Term .Du Γ (D1τ (.arr σ τ))) : Term .Du Γ (D1Arr σ τ) := by
  simpa [D1τ, D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll] using f

@[reducible] def d2arrInTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (d : Term .Du Γ (.Lin .Dyn)) : Term .Du Γ (D2τ (.arr σ τ)) := by
  simpa [D2τ, D2τPrime, D2τPrimeAll, D2Arr] using d

@[reducible] def d2arrOutTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (d : Term .Du Γ (D2τ (.arr σ τ))) : Term .Du Γ (.Lin .Dyn) := by
  simpa [D2τ, D2τPrime, D2τPrimeAll, D2Arr] using d

/-- Coerce an explicit local reverse arrow into the named component of
`D₁(A → B)`. -/
@[reducible] def d1arrLocalRevInTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (rev : Term .Du Γ (.arr (D2τ τ) (.prod (.Lin .Dyn) (D2τ σ)))) :
    Term .Du Γ (D1ArrLocalRev σ τ) := by
  simpa [D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll] using rev

/-- Expose the explicit arrow shape of a named local reverse component. -/
@[reducible] def d1arrLocalRevOutTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (rev : Term .Du Γ (D1ArrLocalRev σ τ)) :
    Term .Du Γ (.arr (D2τ τ) (.prod (.Lin .Dyn) (D2τ σ))) := by
  simpa [D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll] using rev

@[reducible] def d1funLocalRevInTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (rev : Term .Du Γ (.arr (D2τ τ) (.prod (.Lin .Dyn) (D2τ σ)))) :
    Term .Du Γ (D1ArrLocalRev σ τ) :=
  d1arrLocalRevInTerm (σ := σ) (τ := τ) rev

/-- Result constructor for translated function application. -/
@[reducible] def d1funMkResult {Γ : Env .Du} {σ τ : Typ .Pr}
    (y : Term .Du Γ (D1τ τ))
    (rev : Term .Du Γ (D1ArrLocalRev σ τ)) :
    Term .Du Γ (D1ArrResult σ τ) :=
  .pair y rev

/-- Primal projection from the result of a translated function application. -/
@[reducible] def d1funResultPrimal {Γ : Env .Du} {σ τ : Typ .Pr}
    (r : Term .Du Γ (D1ArrResult σ τ)) : Term .Du Γ (D1τ τ) :=
  .fstE r

/-- Local reverse projection from the result of a translated function application. -/
@[reducible] def d1funResultRev {Γ : Env .Du} {σ τ : Typ .Pr}
    (r : Term .Du Γ (D1ArrResult σ τ)) : Term .Du Γ (D1ArrLocalRev σ τ) :=
  .sndE r

/-- Apply a translated source function to a translated argument. -/
@[reducible] def d1funApplyTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (f : Term .Du Γ (D1τ (.arr σ τ)))
    (x : Term .Du Γ (D1τ σ)) : Term .Du Γ (D1ArrResult σ τ) := by
  have f' : Term .Du Γ (.arr (D1τ σ) (D1ArrResult σ τ)) := by
    simpa [D1τ, D1τAll, D1Arr, D1ArrResult, D1ArrLocalRev,
      D2τ, D2τPrime, D2τPrimeAll] using
      (d1arrOutTerm (σ := σ) (τ := τ) f)
  exact .app f' x

/-- Run the local reverse map returned by a translated function value. -/
@[reducible] def d1funLocalRevApply {Γ : Env .Du} {σ τ : Typ .Pr}
    (rev : Term .Du Γ (D1ArrLocalRev σ τ))
    (db : Term .Du Γ (D2τ τ)) :
    Term .Du Γ (.prod (.Lin .Dyn) (D2τ σ)) := by
  have rev' : Term .Du Γ (.arr (D2τ τ) (.prod (.Lin .Dyn) (D2τ σ))) := by
    simpa [D1ArrLocalRev, D2τ, D2τPrime, D2τPrimeAll] using rev
  exact .app rev' db

@[reducible] def d1funLocalDyn {Γ : Env .Du} {σ τ : Typ .Pr}
    (p : Term .Du Γ (.prod (.Lin .Dyn) (D2τ σ))) : Term .Du Γ (.Lin .Dyn) :=
  .fstE p

@[reducible] def d1funLocalArg {Γ : Env .Du} {σ τ : Typ .Pr}
    (p : Term .Du Γ (.prod (.Lin .Dyn) (D2τ σ))) : Term .Du Γ (D2τ σ) :=
  .sndE p

/-- Compatibility aliases using the old `arr` naming convention.  The
`fun`-named helpers above are the canonical function-value API; these aliases
keep the CHAD clauses and older proof scripts readable. -/
@[reducible] def d1arrAppTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (f : Term .Du Γ (D1τ (.arr σ τ)))
    (x : Term .Du Γ (D1τ σ)) : Term .Du Γ (D1ArrResult σ τ) :=
  d1funApplyTerm (σ := σ) (τ := τ) f x

@[reducible] def d1arrResultPrimalTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (r : Term .Du Γ (D1ArrResult σ τ)) : Term .Du Γ (D1τ τ) :=
  d1funResultPrimal (σ := σ) (τ := τ) r

@[reducible] def d1arrResultRevTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (r : Term .Du Γ (D1ArrResult σ τ)) : Term .Du Γ (D1ArrLocalRev σ τ) :=
  d1funResultRev (σ := σ) (τ := τ) r

@[reducible] def d1arrLocalRevCallTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (rev : Term .Du Γ (D1ArrLocalRev σ τ))
    (db : Term .Du Γ (D2τ τ)) :
    Term .Du Γ (.prod (.Lin .Dyn) (D2τ σ)) :=
  d1funLocalRevApply (σ := σ) (τ := τ) rev db

@[reducible] def d1arrLocalDynTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (p : Term .Du Γ (.prod (.Lin .Dyn) (D2τ σ))) : Term .Du Γ (.Lin .Dyn) :=
  d1funLocalDyn (σ := σ) (τ := τ) p

@[reducible] def d1arrLocalArgTerm {Γ : Env .Du} {σ τ : Typ .Pr}
    (p : Term .Du Γ (.prod (.Lin .Dyn) (D2τ σ))) : Term .Du Γ (D2τ σ) :=
  d1funLocalArg (σ := σ) (τ := τ) p

/-- Decode a function cotangent into the compact closure cotangent environment. -/
def decodeFunCtgToClosure {Γdu : Env .Du} {Γclo : Env .Pr} {σ τ : Typ .Pr}
    (d : Term .Du Γdu (D2τ (.arr σ τ))) :
    Term .Du Γdu (.EVM (D2Γl Γclo) .Un) :=
  .fromDyn (Γl := D2Γl Γclo) (d2arrOutTerm (σ := σ) (τ := τ) d)

/-- Decode a function cotangent and scatter it from the compact closure
environment into the ambient source cotangent environment. -/
def scatterFunCtgToAmbient {Γdu : Env .Du} {Γ Γclo : Env .Pr} {σ τ : Typ .Pr}
    (inj : EnvInj Γclo Γ)
    (d : Term .Du Γdu (D2τ (.arr σ τ))) :
    Term .Du Γdu (D2Γ Γ) :=
  .scatterevm (D2ClosureInj inj) (decodeFunCtgToClosure (Γclo := Γclo) d)

/-- Pack the body reverse map of a lambda into the local reverse map stored in
the translated function value.  The returned `Dyn` contains only the compact
closure cotangent `D₂[Γclo]`; the argument cotangent is returned separately. -/
def packLambdaLocalReverse {Γdu : Env .Du} {Γclo : Env .Pr} {σ τ : Typ .Pr}
    (bodyReverse : Term .Du Γdu (D2Γ (σ :: Γclo))) :
    Term .Du Γdu (.prod (.Lin .Dyn) (D2τ σ)) :=
  packDynScoped
    (Γl := D2Γl Γclo)
    (δ := D2τPrime σ)
    bodyReverse

def chad {Γ : Env .Pr} {τ : Typ .Pr}
    (tm : Term .Pr Γ τ) : Term .Du (D1Γ Γ) (.prod (D1τ τ) (.arr (D2τ τ) (D2Γ Γ))) :=
  match tm with
  | .var idx =>
      .pair (.var (convIdx D1τ idx))
        (lamwith [] (.addevm (convIdx D2τPrime idx) (.var .Z)))
  | .letE (σ := σ) e1 e2 =>
      .letE (chad e1)
        (.letE (.fstE (.var .Z))
          (.letE (sink (.WCopy (.WSkip .WEnd)) (chad e2))
            (.pair (.fstE (.var .Z))
              (lamwith [finZero, finTwo]
                (.bindevm
                  (.scopeevm (zerot σ) (.app (.sndE (.var (.S .Z))) (.var .Z)))
                  (lamwith [finTwo]
                    (.app (.sndE (.var (.S .Z))) (.fstE (.var .Z)))))))))
  | .prim op e =>
      .letE (chad e)
        (.pair (.prim (d1Prim op) (.fstE (.var .Z)))
          (lamwith [finZero]
            (.app (.sndE (.var (.S .Z)))
              (dprim op (.fstE (.var (.S .Z))) (.var .Z)))))
  | .unit =>
      .pair (d1UnitInTerm .unit) (lamwith [] (.pureevm .unit))
  | .pair (σ := σ) (τ := τ) e1 e2 =>
      .letE (.pair (chad e1) (chad e2))
        (.pair (d1pairTerm (.fstE (.fstE (.var .Z))) (.fstE (.sndE (.var .Z))))
          (lamwith (α := D2τ (.prod σ τ)) [finZero]
            (thenevm
              (.app (.sndE (.fstE (.var (.S .Z)))) (d2lfstTerm (σ := σ) (τ := τ) (.var .Z)))
              (.app (.sndE (.sndE (.var (.S .Z)))) (d2lsndTerm (σ := σ) (τ := τ) (.var .Z))))))
  | .fstE (σ := σ) (τ := τ) e =>
      .letE (chad e)
        (.pair (d1fstTerm (σ := σ) (τ := τ) (.fstE (.var .Z)))
          (lamwith (α := D2τ σ) [finZero]
            (.app (.sndE (.var (.S .Z))) (d2lpairTerm (σ := σ) (τ := τ) (.var .Z) (zerot τ)))))
  | .sndE (σ := σ) (τ := τ) e =>
      .letE (chad e)
        (.pair (d1sndTerm (σ := σ) (τ := τ) (.fstE (.var .Z)))
          (lamwith (α := D2τ τ) [finZero]
            (.app (.sndE (.var (.S .Z))) (d2lpairTerm (σ := σ) (τ := τ) (zerot σ) (.var .Z)))))
  | .inl (σ := σ) (τ := τ) e =>
      .letE (chad e)
        (.pair (d1inlTerm (σ := σ) (τ := τ) (.fstE (.var .Z)))
          (lamwith (α := D2τ (.sum σ τ)) [finZero]
            (.app (.sndE (.var (.S .Z))) (d2lcastlTerm (σ := σ) (τ := τ) (.var .Z)))))
  | .inr (σ := σ) (τ := τ) e =>
      .letE (chad e)
        (.pair (d1inrTerm (σ := σ) (τ := τ) (.fstE (.var .Z)))
          (lamwith (α := D2τ (.sum σ τ)) [finZero]
            (.app (.sndE (.var (.S .Z))) (d2lcastrTerm (σ := σ) (τ := τ) (.var .Z)))))
  | .caseE (σ := σ) (τ := τ) e1 e2 e3 =>
      .letE (chad e1)
        (d1caseTerm (σ := σ) (τ := τ) (.fstE (.var .Z))
          (.letE (sink (.WCopy (.WSkip .WEnd)) (chad e2))
            (.pair (.fstE (.var .Z))
              (lamwith [finZero, finTwo]
                (.bindevm
                  (.scopeevm (zerot σ) (.app (.sndE (.var (.S .Z))) (.var .Z)))
                  (lamwith [finTwo]
                    (.app (.sndE (.var (.S .Z))) (d2linlTerm (σ := σ) (τ := τ) (.fstE (.var .Z)))))))))
          (.letE (sink (.WCopy (.WSkip .WEnd)) (chad e3))
            (.pair (.fstE (.var .Z))
              (lamwith [finZero, finTwo]
                (.bindevm
                  (.scopeevm (zerot τ) (.app (.sndE (.var (.S .Z))) (.var .Z)))
                  (lamwith [finTwo]
                    (.app (.sndE (.var (.S .Z))) (d2linrTerm (σ := σ) (τ := τ) (.fstE (.var .Z))))))))))
  /- Paper array-build rule, expanded rather than hidden behind a monolithic
     AD primitive:
       let (n, _) = D[n]
       let a      = build n (i. D[body])
       let (a₁,a₂)= unzip a
       (a₁, λd. let pairs = collect d;
                let d₂    = scatter (build n (i. zero)) pairs;
                sequence (zipWith (λf d'. scope zero (f d')) a₂ d₂)) -/
  | .arrayBuild (τ := τ) n body =>
      .letE (chad n)
        (.letE
          (.arrayBuild (d1IntTerm (.fstE (.var .Z)))
            (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad body)))
          (.letE (.arrayUnzipD (.var .Z))
            (.pair (d1arrayInTerm (τ := τ) (.fstE (.var .Z)))
              (lamwith (α := D2τ (.array τ)) [finZero, finTwo]
                (.letE (.larraycollect (d2arrayOutTerm (τ := τ) (.var .Z)))
                  (.letE
                    (.arrayScatterD
                      (.arrayBuild (d1IntTerm (.fstE (.var (.S (.S (.S .Z)))))) (zerot τ))
                      (.var .Z))
                    (.letE
                      (.arrayZipWithScopeD
                        (.sndE (.var (.S (.S (.S .Z)))))
                        (.var .Z))
                      (.arraySequenceUnitD (.var .Z)))))))))
  /- Paper indexing rule:
       let (xs₁,xs₂) = D[xs]
       let (i,_)     = D[i]
       (xs₁ ! i, λd. xs₂ (BagOne (i,d))) -/
  | .arrayIndex (τ := τ) xs i =>
      .letE (.pair (chad xs) (chad i))
        (.pair (.arrayIndex (d1arrayOutTerm (τ := τ) (.fstE (.fstE (.var .Z)))) (d1IntTerm (.fstE (.sndE (.var .Z)))))
          (lamwith (α := D2τ τ) [finZero]
            (.app (.sndE (.fstE (.var (.S .Z))))
              (d2arrayInTerm (τ := τ) (.larrayone (.fstE (.sndE (.var (.S .Z)))) (.var .Z))))))
  /- The paper's fold rule records the reduction tree in the primal pass and
     traverses it with `unTree` in reverse.  The evaluator of `arrayFoldAD`
     above implements precisely that target-level recorded fold. -/
  | .arrayFold (τ := τ) body xs => by
      let xs' : Term .Du (D1Γ Γ)
          (.prod (.array (D1τ τ)) (.arr (.Lin (.array (D2τPrime τ))) (D2Γ Γ))) := by
        simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, D2Γ, D2Γl] using (chad xs)
      let body' : Term .Du (.prod (D1τ τ) (D1τ τ) :: D1Γ Γ)
          (.prod (D1τ τ)
            (.arr (.Lin (D2τPrime τ))
              (.EVM (.prod (D2τPrime τ) (D2τPrime τ) :: D2Γl Γ) .Un))) := by
        simpa [D1Γ, D1τ, D1τAll, D2Γ, D2Γl, D2τ, D2τPrime, D2τPrimeAll] using (chad body)
      simpa [D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, D2Γ, D2Γl] using
        (Term.arrayFoldAD (Γl := D2Γl Γ) (α := D1τ τ) (δ := D2τPrime τ) xs' body')
  /- Function introduction.  The source lambda carries a compact closure
     environment `Γclo`; the local reverse map stores only `D₂[Γclo]` in Dyn,
     not the whole ambient `D₂[Γ]`. -/
  | .lam (Γclo := Γclo) (σ := σ) (τ := τ) inj body =>
      let f : Term .Du (D1Γ Γ) (D1Arr σ τ) :=
        .lam (D1ClosureInj inj)
          (.letE (chad body)
            (d1funMkResult (σ := σ) (τ := τ)
              (.fstE (.var .Z))
              (d1arrLocalRevInTerm (σ := σ) (τ := τ)
                (lamwith (α := D2τ τ) [finZero]
                  (packLambdaLocalReverse (Γclo := Γclo) (σ := σ) (τ := τ)
                    (.app (.sndE (.var (.S .Z))) (.var .Z)))))))
      .pair
        (d1arrInTerm (σ := σ) (τ := τ) f)
        (lamwith (α := D2τ (.arr σ τ)) []
          (scatterFunCtgToAmbient (Γclo := Γclo) (σ := σ) (τ := τ)
            inj (.var .Z)))
  /- Function elimination.  This is the Dyn application rule:
       let ⟨a,a'⟩ = D[t]; let ⟨f,f'⟩ = D[s]; let ⟨b,b'⟩ = f a;
       ⟨b, λdb. let ⟨d,da⟩ = b' db in a' da + f' d⟩. -/
  | .app (σ := σ) (τ := τ) s t =>
      .letE (chad t)
        (.letE (sink1 (chad s))
          (.letE (d1funApplyTerm (σ := σ) (τ := τ)
              (.fstE (.var .Z))
              (.fstE (.var (.S .Z))))
            (.pair (d1funResultPrimal (σ := σ) (τ := τ) (.var .Z))
              (lamwith (α := D2τ τ) [finZero, finOne, finTwo]
                (.letE (d1funLocalRevApply (σ := σ) (τ := τ)
                    (d1funResultRev (σ := σ) (τ := τ) (.var (.S .Z)))
                    (.var .Z))
                  (thenevm
                    (.app
                      (.sndE (.var (.S (.S (.S (.S .Z))))))
                      (d1funLocalArg (σ := σ) (τ := τ) (.var .Z)))
                    (.app
                      (.sndE (.var (.S (.S (.S .Z)))))
                      (d2arrInTerm (σ := σ) (τ := τ)
                        (d1funLocalDyn (σ := σ) (τ := τ) (.var .Z))))))))))


/-- Abstract predicate saying that the closure annotation on a source lambda is
exact: `Γclo` is the type-level list of free variables of `body`, excluding the
bound argument, and `inj` embeds that compact list into the ambient context.

This is intentionally kept as a predicate rather than baked into the raw syntax:
front ends may compute it syntactically, while the core transformation remains
correct for any supplied closure and obtains the sharp bound when this predicate
holds. -/
axiom closureExact {Γ Γclo : Env .Pr} {σ τ : Typ .Pr}
    (inj : EnvInj Γclo Γ)
    (body : Term .Pr (σ :: Γclo) τ) : Prop

/-- All source lambdas in a term carry exact compact closures.  This is the
higher-order analogue of the well-formedness assumptions already implicit in the
array cost model: it is not needed to type the program, but it is the condition
under which the closure-sized Dyn payload should be read as optimal. -/
def allLambdaClosuresExact : {Γ : Env .Pr} → {τ : Typ .Pr} → Term .Pr Γ τ → Prop
  | _, _, .var _ => True
  | _, _, .letE rhs body =>
      allLambdaClosuresExact rhs ∧ allLambdaClosuresExact body
  | _, _, .prim _ e => allLambdaClosuresExact e
  | _, _, .unit => True
  | _, _, .pair e₁ e₂ =>
      allLambdaClosuresExact e₁ ∧ allLambdaClosuresExact e₂
  | _, _, .fstE e => allLambdaClosuresExact e
  | _, _, .sndE e => allLambdaClosuresExact e
  | _, _, .inl e => allLambdaClosuresExact e
  | _, _, .inr e => allLambdaClosuresExact e
  | _, _, .caseE e₁ e₂ e₃ =>
      allLambdaClosuresExact e₁ ∧
      allLambdaClosuresExact e₂ ∧
      allLambdaClosuresExact e₃
  | _, _, .arrayBuild n body =>
      allLambdaClosuresExact n ∧ allLambdaClosuresExact body
  | _, _, .arrayIndex xs i =>
      allLambdaClosuresExact xs ∧ allLambdaClosuresExact i
  | _, _, .arrayFold body xs =>
      allLambdaClosuresExact body ∧ allLambdaClosuresExact xs
  | _, _, .lam inj body =>
      closureExact inj body ∧ allLambdaClosuresExact body
  | _, _, .app s t =>
      allLambdaClosuresExact s ∧ allLambdaClosuresExact t

/-- Cost charged by source lambda construction: the compact closure context, not
the ambient context. -/
abbrev lambdaClosureCost {Γ Γclo : Env .Pr} {σ τ : Typ .Pr}
    (_inj : EnvInj Γclo Γ)
    (_body : Term .Pr (σ :: Γclo) τ) : Int :=
  one + intLength Γclo

def phi : (τ : LTyp) → LinRep τ → Int
  | .LUn, _ => one
  | .LR, _ => one
  | .Dyn, _ => one
  | .prod _ _, none => one
  | .prod σ τ, some (x, y) => one + phi σ x + phi τ y
  | .sum _ _, none => one
  | .sum σ _, some (Sum.inl x) => one + phi σ x
  | .sum _ τ, some (Sum.inr y) => one + phi τ y
  | .array _, b => Bag.collectCost b

def «φ» (τ : LTyp) (x : LinRep τ) : Int :=
  phi τ x

def phiPrime : (Γ : LEnv) → LEtup Γ → Int
  | [], _ => 0
  | τ :: Γ, env => phi τ env.1 + phiPrime Γ env.2

def «φ'» (Γ : LEnv) (env : LEtup Γ) : Int :=
  phiPrime Γ env

def size : (τ : LTyp) → LinRep τ → Nat
  | .LUn, _ => 1
  | .LR, _ => 1
  | .Dyn, _ => 1
  | .prod _ _, none => 1
  | .prod σ τ, some (x, y) => 1 + size σ x + size τ y
  | .sum _ _, none => 1
  | .sum σ _, some (Sum.inl x) => 1 + size σ x
  | .sum _ τ, some (Sum.inr y) => 1 + size τ y
  | .array _, b => Bag.size b

def zeroEnvTerm {Γ' : Env .Du} : (Γ : Env .Pr) → Term .Du Γ' (D2Γtup Γ)
  | [] => .unit
  | τ :: Γ => .pair (zerot τ) (zeroEnvTerm Γ)

def «zero-env-term» {Γ' : Env .Du} (Γ : Env .Pr) : Term .Du Γ' (D2Γtup Γ) :=
  zeroEnvTerm Γ

def TH1_STATEMENT : Prop :=
  ∀ {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (List.map D2τPrime Γ))
    (t : Term .Pr Γ τ),
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

abbrev «TH1-STATEMENT» : Prop :=
  TH1_STATEMENT

def TH1_EXACT_CLOSURES_STATEMENT : Prop :=
  ∀ {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ τ))
    (denvin : LEtup (D2Γl Γ))
    (t : Term .Pr Γ τ),
    allLambdaClosuresExact t →
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
      - phiPrime (D2Γl Γ) denvin
      + phiPrime (D2Γl Γ) denvout
      - intLength Γ
      ≤ (34 : Int) * cost env t

abbrev «TH1-EXACT-CLOSURES-STATEMENT» : Prop :=
  TH1_EXACT_CLOSURES_STATEMENT

def TH2_STATEMENT : Prop :=
  ∀ {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ τ))
    (t : Term .Pr Γ τ),
    cost (Val.push ctg (primalVal env))
      (Term.runevm
        (Term.app
          (Term.sndE (sink1 (chad t)))
          (Term.var Idx.Z))
        (zeroEnvTerm Γ))
    ≤ (5 : Int)
      + (34 : Int) * cost env t
      + Int.ofNat (size (D2τPrime τ) ctg)
      + (4 : Int) * intLength Γ

abbrev «TH2-STATEMENT» : Prop :=
  TH2_STATEMENT

def TH2_EXACT_CLOSURES_STATEMENT : Prop :=
  ∀ {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ)
    (ctg : Rep (D2τ τ))
    (t : Term .Pr Γ τ),
    allLambdaClosuresExact t →
    cost (Val.push ctg (primalVal env))
      (Term.runevm
        (Term.app
          (Term.sndE (sink1 (chad t)))
          (Term.var Idx.Z))
        (zeroEnvTerm Γ))
    ≤ (5 : Int)
      + (34 : Int) * cost env t
      + Int.ofNat (size (D2τPrime τ) ctg)
      + (4 : Int) * intLength Γ

abbrev «TH2-EXACT-CLOSURES-STATEMENT» : Prop :=
  TH2_EXACT_CLOSURES_STATEMENT

end

end EfficientChad
