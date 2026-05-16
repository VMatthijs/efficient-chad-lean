import EfficientChad.EvalSinkCommute

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace EfficientChad

theorem valprj_primalVal {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) (idx : Idx Γ τ) :
    valprj (primalVal env) (convIdx D1τ idx) = primal τ (valprj env idx) := by
  induction idx with
  | Z =>
      cases env with
      | push x rest => rfl
  | S i ih =>
      cases env with
      | push x rest =>
          exact ih rest

theorem chad_preserves_primal_var {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) (idx : Idx Γ τ) :
    (eval (primalVal env) (chad (Term.var idx))).1.1 =
      primal τ (eval env (Term.var idx)).1 := by
  simpa [chad, eval] using valprj_primalVal env idx

theorem chad_preserves_primal_unit {Γ : Env .Pr}
    (env : Val .Pr Γ) :
    (eval (primalVal env) (chad (Term.unit : Term .Pr Γ (.Un)))).1.1 =
      primal (.Un) (eval env (Term.unit : Term .Pr Γ (.Un))).1 := by
  simp [chad, eval, primal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll]

/-- Array-specific primal-preservation obligations for the extended core
language.

The obligations are now phrased as genuine array-rule cases: each method receives
exactly the scalar preservation induction hypotheses for its subterms.  This is
much smaller than assuming primal preservation for all array source terms at
once, and it mirrors the way the scalar proof consumes recursive hypotheses. -/
class CorePrimalLaws extends CoreRecursorLaws, DynLaws, HigherOrderValueLaws : Prop where
  chad_preserves_primal_arrayBuild {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (n : Term .Pr Γ .Inte)
      (body : Term .Pr (.Inte :: Γ) τ)
      (hn : (eval (primalVal env) (chad n)).1.1 =
        primal (.Inte : Typ .Pr) (eval env n).1)
      (hbody : ∀ envI : Val .Pr (.Inte :: Γ),
        (eval (primalVal envI) (chad body)).1.1 =
          primal τ (eval envI body).1) :
    (eval (primalVal env) (chad (Term.arrayBuild n body))).1.1 =
      primal (.array τ) (eval env (Term.arrayBuild n body)).1

  chad_preserves_primal_arrayIndex {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (xs : Term .Pr Γ (.array τ))
      (i : Term .Pr Γ .Inte)
      (hxs : (eval (primalVal env) (chad xs)).1.1 =
        primal (.array τ) (eval env xs).1)
      (hi : (eval (primalVal env) (chad i)).1.1 =
        primal (.Inte : Typ .Pr) (eval env i).1) :
    (eval (primalVal env) (chad (Term.arrayIndex xs i))).1.1 =
      primal τ (eval env (Term.arrayIndex xs i)).1

  chad_preserves_primal_arrayFold {Γ : Env .Pr} {τ : Typ .Pr}
      (env : Val .Pr Γ)
      (body : Term .Pr (.prod τ τ :: Γ) τ)
      (xs : Term .Pr Γ (.array τ))
      (hbody : ∀ envP : Val .Pr (.prod τ τ :: Γ),
        (eval (primalVal envP) (chad body)).1.1 =
          primal τ (eval envP body).1)
      (hxs : (eval (primalVal env) (chad xs)).1.1 =
        primal (.array τ) (eval env xs).1) :
    (eval (primalVal env) (chad (Term.arrayFold body xs))).1.1 =
      primal τ (eval env (Term.arrayFold body xs)).1


  /-- Function-introduction primal preservation.  This is the higher-order
  logical-relation assumption linking the ambient function-value lift
  `primalFun`/`HOFunRel` with the syntactic Dyn translation of lambdas.  The compact
  closure environment `Γclo` is the one carried by the term. -/
  chad_preserves_primal_lam {Γ Γclo : Env .Pr} {σ τ : Typ .Pr}
      (env : Val .Pr Γ)
      (inj : EnvInj Γclo Γ)
      (body : Term .Pr (σ :: Γclo) τ)
      (hbody : ∀ envBody : Val .Pr (σ :: Γclo),
        (eval (primalVal envBody) (chad body)).1.1 =
          primal τ (eval envBody body).1) :
    (eval (primalVal env) (chad (Term.lam inj body))).1.1 =
      primal (.arr σ τ) (eval env (Term.lam inj body)).1

  /-- Function-elimination primal preservation, i.e. the beta/use case of the
  higher-order logical relation. -/
  chad_preserves_primal_app {Γ : Env .Pr} {σ τ : Typ .Pr}
      (env : Val .Pr Γ)
      (s : Term .Pr Γ (.arr σ τ))
      (t : Term .Pr Γ σ)
      (hs : (eval (primalVal env) (chad s)).1.1 =
        primal (.arr σ τ) (eval env s).1)
      (ht : (eval (primalVal env) (chad t)).1.1 =
        primal σ (eval env t).1) :
    (eval (primalVal env) (chad (Term.app s t))).1.1 =
      primal τ (eval env (Term.app s t)).1

variable [CorePrimalLaws]

theorem chad_preserves_primal {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) : (e : Term .Pr Γ τ) →
  (eval (primalVal env) (chad e)).1.1 = primal τ (eval env e).1
  | .var idx =>
      chad_preserves_primal_var env idx
  | .letE rhs body => by
      have h_rhs := chad_preserves_primal env rhs
      have h_body := chad_preserves_primal (Val.push (eval env rhs).1 env) body
      have h_sink :
          eval
              (Val.push (primal _ (eval env rhs).1)
                (Val.push (eval (primalVal env) (chad rhs)).1 (primalVal env)))
              (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad body))
            = eval (primalVal (Val.push (eval env rhs).1 env)) (chad body) := by
        simpa [primalVal] using
          (eval_copy_skip_wend (primalVal env)
            (primal _ (eval env rhs).1)
            (eval (primalVal env) (chad rhs)).1
            (chad body))
      exact (by
        simpa [chad, eval, primalVal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_rhs] using
          ((congrArg (fun z => z.1.1) h_sink).trans h_body))
  | .prim op arg => by
      have h_arg := chad_preserves_primal env arg
      have h_prim := eval_d1prim op (eval env arg).1
      simpa [chad, eval, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_arg] using h_prim
  | .unit =>
      chad_preserves_primal_unit env
  | .pair left right => by
      have h_left := chad_preserves_primal env left
      have h_right := chad_preserves_primal env right
      simpa [chad, eval, primal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_left, h_right]
  | .fstE pairTerm => by
      have h_pair := chad_preserves_primal env pairTerm
      simpa [chad, eval, primal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_pair]
  | .sndE pairTerm => by
      have h_pair := chad_preserves_primal env pairTerm
      simpa [chad, eval, primal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_pair]
  | .inl arg => by
      have h_arg := chad_preserves_primal env arg
      simpa [chad, eval, primal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_arg]
  | .inr arg => by
      have h_arg := chad_preserves_primal env arg
      simpa [chad, eval, primal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_arg]
  | .caseE scrut left right => by
      have h_scrut := chad_preserves_primal env scrut
      cases h_scrut_val : (eval env scrut).1 with
      | inl x =>
          have h_left := chad_preserves_primal (Val.push x env) left
          have h_sink :
              eval
                  (Val.push (primal _ x)
                    (Val.push (eval (primalVal env) (chad scrut)).1 (primalVal env)))
                  (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad left))
                = eval (primalVal (Val.push x env)) (chad left) := by
            simpa [primalVal] using
              (eval_copy_skip_wend (primalVal env)
                (primal _ x)
                (eval (primalVal env) (chad scrut)).1
                (chad left))
          exact (by
            simpa [chad, eval, primal, primalVal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_scrut, h_scrut_val] using
              ((congrArg (fun z => z.1.1) h_sink).trans h_left))
      | inr y =>
          have h_right := chad_preserves_primal (Val.push y env) right
          have h_sink :
              eval
                  (Val.push (primal _ y)
                    (Val.push (eval (primalVal env) (chad scrut)).1 (primalVal env)))
                  (sink (Weakening.WCopy (Weakening.WSkip Weakening.WEnd)) (chad right))
                = eval (primalVal (Val.push y env)) (chad right) := by
            simpa [primalVal] using
              (eval_copy_skip_wend (primalVal env)
                (primal _ y)
                (eval (primalVal env) (chad scrut)).1
                (chad right))
          exact (by
            simpa [chad, eval, primal, primalVal, d1pairTerm, d1fstTerm, d1sndTerm, d1inlTerm, d1inrTerm, d1caseTerm, d2lpairTerm, d2lfstTerm, d2lsndTerm, d2linlTerm, d2linrTerm, d2lcastlTerm, d2lcastrTerm, d1UnitInTerm, d1IntTerm, d1arrayInTerm, d1arrayOutTerm, d2arrayInTerm, d2arrayOutTerm, d1arrInTerm, d1arrOutTerm, d2arrInTerm, d2arrOutTerm, d1arrLocalRevInTerm, d1arrLocalRevOutTerm, d1funMkResult, d1funResultPrimal, d1funResultRev, d1funApplyTerm, d1funLocalRevApply, d1funLocalDyn, d1funLocalArg, d1arrAppTerm, d1arrResultPrimalTerm, d1arrResultRevTerm, d1arrLocalRevCallTerm, d1arrLocalDynTerm, d1arrLocalArgTerm, decodeFunCtgToClosure, scatterFunCtgToAmbient, packLambdaLocalReverse, D1ClosureInj, D2ClosureInj, d1arrRepIn, d1arrRepOut, d2arrRepIn, d2arrRepOut, D1τ, D1τAll, D2τ, D2τPrime, D2τPrimeAll, valprj, h_scrut, h_scrut_val] using
              ((congrArg (fun z => z.1.1) h_sink).trans h_right))
  | .arrayBuild n body =>
      CorePrimalLaws.chad_preserves_primal_arrayBuild env n body
        (chad_preserves_primal env n)
        (fun envI => chad_preserves_primal envI body)
  | .arrayIndex xs i =>
      CorePrimalLaws.chad_preserves_primal_arrayIndex env xs i
        (chad_preserves_primal env xs)
        (chad_preserves_primal env i)
  | .arrayFold body xs =>
      CorePrimalLaws.chad_preserves_primal_arrayFold env body xs
        (fun envP => chad_preserves_primal envP body)
        (chad_preserves_primal env xs)
  | .lam inj body =>
      CorePrimalLaws.chad_preserves_primal_lam env inj body
        (fun envBody => chad_preserves_primal envBody body)
  | .app s t =>
      CorePrimalLaws.chad_preserves_primal_app env s t
        (chad_preserves_primal env s)
        (chad_preserves_primal env t)

theorem «chad-preserves-primal» {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) (e : Term .Pr Γ τ) :
  (eval (primalVal env) (chad e)).1.1 = primal τ (eval env e).1 :=
  chad_preserves_primal env e

/-- Exact-closure version of primal preservation.  The hypothesis is carried only
to document the efficient higher-order reading; primal preservation itself holds
under the same higher-order logical-relation assumptions as `chad_preserves_primal`. -/
theorem chad_preserves_primal_exactClosures {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) (e : Term .Pr Γ τ)
    (_hclosures : allLambdaClosuresExact e) :
    (eval (primalVal env) (chad e)).1.1 = primal τ (eval env e).1 :=
  chad_preserves_primal env e

end EfficientChad
