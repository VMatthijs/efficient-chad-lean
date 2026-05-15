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
  simp [chad, eval, primal]

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
        simpa [chad, eval, primalVal, valprj, h_rhs] using
          ((congrArg (fun z => z.1.1) h_sink).trans h_body))
  | .prim op arg => by
      have h_arg := chad_preserves_primal env arg
      have h_prim := eval_d1prim op (eval env arg).1
      simpa [chad, eval, valprj, h_arg] using h_prim
  | .unit =>
      chad_preserves_primal_unit env
  | .pair left right => by
      have h_left := chad_preserves_primal env left
      have h_right := chad_preserves_primal env right
      simpa [chad, eval, primal, valprj, h_left, h_right]
  | .fstE pairTerm => by
      have h_pair := chad_preserves_primal env pairTerm
      simpa [chad, eval, primal, valprj, h_pair]
  | .sndE pairTerm => by
      have h_pair := chad_preserves_primal env pairTerm
      simpa [chad, eval, primal, valprj, h_pair]
  | .inl arg => by
      have h_arg := chad_preserves_primal env arg
      simpa [chad, eval, primal, valprj, h_arg]
  | .inr arg => by
      have h_arg := chad_preserves_primal env arg
      simpa [chad, eval, primal, valprj, h_arg]
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
            simpa [chad, eval, primal, primalVal, valprj, h_scrut, h_scrut_val] using
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
            simpa [chad, eval, primal, primalVal, valprj, h_scrut, h_scrut_val] using
              ((congrArg (fun z => z.1.1) h_sink).trans h_right))

theorem «chad-preserves-primal» {Γ : Env .Pr} {τ : Typ .Pr}
    (env : Val .Pr Γ) (e : Term .Pr Γ τ) :
  (eval (primalVal env) (chad e)).1.1 = primal τ (eval env e).1 :=
  chad_preserves_primal env e

end EfficientChad
