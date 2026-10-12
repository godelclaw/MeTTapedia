import Mettapedia.OSLF.Syntax.DeclaredBindingContextTransport
import Mettapedia.OSLF.Syntax.LambdaIntrinsicPresentation

/-!
# Derived binding reduction and an actual lambda-equation model

The beta equation uses the existing authored intrinsic schema. Its contextual
instances are constructed at arbitrary ambient contexts, including open
arguments. The existing free equational model then supplies an actual
substitution-compatible denotation. Administrative result erasure preserves
raw lowering; consuming a `where` performs beta, preserving equation-class
denotation while advancing the reduction observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation

open BindingCloneFoldSubstitution

theorem lower_inst {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
    (value : Term sig Γ .term) :
    lower (inst body value) = inst (S := Target.sig) (lower body) (lower value) := by
  unfold inst
  rw [lower_bind]
  congr 1
  funext s x
  cases x <;> rfl

/-- Source reduction is authored independently of lowering. Base lambda
payloads have the target beta/congruence rules; wrappers have their own
administrative and local-binding rules. -/
inductive Step : {Γ : Ctx sig} → Term sig Γ .term → Term sig Γ .term → Prop where
  | whereBeta {Γ : Ctx sig} (value : Term sig Γ .term)
      (body : Term sig (.term :: Γ) .term) :
      Step (whereBinding value body) (inst body value)
  | resultErase {Γ : Ctx sig} (payload : Term sig Γ .term) :
      Step (result payload) payload
  | baseBeta {Γ : Ctx sig} (value : Term sig Γ .term)
      (body : Term sig (.term :: Γ) .term) :
      Step (.op .baseApp (.cons (.op .baseLam (.cons body .nil)) (.cons value .nil)))
        (inst body value)
  | lambdaBeta {Γ : Ctx sig} (value : Term sig Γ .term)
      (body : Term sig (.term :: Γ) .term) :
      Step (.op .baseApp (.cons (lambda body) (.cons value .nil))) (inst body value)
  | baseAppLeft {Γ : Ctx sig} {f f' : Term sig Γ .term} (a : Term sig Γ .term) :
      Step f f' →
      Step (.op .baseApp (.cons f (.cons a .nil))) (.op .baseApp (.cons f' (.cons a .nil)))
  | baseAppRight {Γ : Ctx sig} {a a' : Term sig Γ .term} (f : Term sig Γ .term) :
      Step a a' →
      Step (.op .baseApp (.cons f (.cons a .nil))) (.op .baseApp (.cons f (.cons a' .nil)))
  | baseLamCong {Γ : Ctx sig} {body body' : Term sig (.term :: Γ) .term} :
      Step body body' → Step (.op .baseLam (.cons body .nil)) (.op .baseLam (.cons body' .nil))
  | lambdaCong {Γ : Ctx sig} {body body' : Term sig (.term :: Γ) .term} :
      Step body body' → Step (lambda body) (lambda body')
  | whereValue {Γ : Ctx sig} {value value' : Term sig Γ .term}
      (body : Term sig (.term :: Γ) .term) :
      Step value value' → Step (whereBinding value body) (whereBinding value' body)
  | whereBody {Γ : Ctx sig} {body body' : Term sig (.term :: Γ) .term}
      (value : Term sig Γ .term) :
      Step body body' → Step (whereBinding value body) (whereBinding value body')
  | resultCong {Γ : Ctx sig} {payload payload' : Term sig Γ .term} :
      Step payload payload' → Step (result payload) (result payload')

/-- A source `where` advances the independently defined lambda reduction
by one genuine beta step. Its value is still in the outer context. -/
theorem where_lower_step {Γ : Ctx sig} (value : Term sig Γ .term)
    (body : Term sig (.term :: Γ) .term) :
    LambdaContextualRung.Step Γ (lower (whereBinding value body))
      (lower (inst body value)) := by
  rw [lower_where, lower_inst]
  exact .beta (lower body) (lower value)

/-- Administrative erasure need not create a target behavioral step. -/
theorem result_lower_equal {Γ : Ctx sig} (payload : Term sig Γ .term) :
    lower (result payload) = lower payload := lower_result payload

/-- Every source step lowers to either administrative equality or one
authorized target step, including reductions beneath declared binders. -/
theorem Step.lower_observation {Γ : Ctx sig} {first second : Term sig Γ .term}
    (step : Step first second) :
    lower first = lower second ∨
      LambdaContextualRung.Step Γ (lower first) (lower second) := by
  induction step with
  | whereBeta value body => exact Or.inr (where_lower_step value body)
  | resultErase payload => exact Or.inl (lower_result payload)
  | baseBeta value body =>
      right
      change LambdaContextualRung.Step _
        (LambdaContextualRung.appT (LambdaContextualRung.lamT (lower body)) (lower value))
        (lower (inst body value))
      rw [lower_inst]
      exact .beta _ _
  | lambdaBeta value body =>
      right
      change LambdaContextualRung.Step _
        (LambdaContextualRung.appT (LambdaContextualRung.lamT (lower body)) (lower value))
        (lower (inst body value))
      rw [lower_inst]
      exact .beta _ _
  | baseAppLeft value _ ih =>
      rcases ih with same | actual
      · exact Or.inl (congrArg (fun f => LambdaContextualRung.appT f (lower value)) same)
      · exact Or.inr (.appCongL (lower value) actual)
  | baseAppRight function _ ih =>
      rcases ih with same | actual
      · exact Or.inl (congrArg (LambdaContextualRung.appT (lower function)) same)
      · exact Or.inr (.appCongR (lower function) actual)
  | baseLamCong _ ih =>
      rcases ih with same | actual
      · exact Or.inl (congrArg LambdaContextualRung.lamT same)
      · exact Or.inr (.lamCong actual)
  | lambdaCong _ ih =>
      rcases ih with same | actual
      · exact Or.inl (congrArg LambdaContextualRung.lamT same)
      · exact Or.inr (.lamCong actual)
  | whereValue body _ ih =>
      rcases ih with same | actual
      · exact Or.inl (congrArg (LambdaContextualRung.appT (LambdaContextualRung.lamT (lower body))) same)
      · exact Or.inr (.appCongR (LambdaContextualRung.lamT (lower body)) actual)
  | whereBody value _ ih =>
      rcases ih with same | actual
      · exact Or.inl (congrArg (fun b => LambdaContextualRung.appT
          (LambdaContextualRung.lamT b) (lower value)) same)
      · exact Or.inr (.appCongL (lower value) (.lamCong actual))
  | resultCong _ ih => exact ih

/-- The independently authored source relation itself is stable under
ambient substitution, with the same lifted body environment as lowering. -/
theorem Step.substitute {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    {first second : Term sig Γ .term} (step : Step first second) :
    Step (bind sigma first) (bind sigma second) := by
  induction step generalizing Δ with
  | whereBeta value body =>
      change Step (whereBinding (bind sigma value) (bind (liftSub sigma [.term]) body))
        (bind sigma (inst body value))
      rw [ContextualLinearSubstitution.bind_inst]
      exact .whereBeta _ _
  | resultErase payload => exact .resultErase (bind sigma payload)
  | baseBeta value body =>
      simpa only [bind, bindArgs, liftSub, ContextualLinearSubstitution.bind_inst] using
        (Step.baseBeta (bind sigma value) (bind (liftSub sigma [.term]) body))
  | lambdaBeta value body =>
      simpa only [lambda, bind, bindArgs, liftSub, ContextualLinearSubstitution.bind_inst] using
        (Step.lambdaBeta (bind sigma value) (bind (liftSub sigma [.term]) body))
  | baseAppLeft value _ ih => exact .baseAppLeft (bind sigma value) (ih sigma)
  | baseAppRight function _ ih => exact .baseAppRight (bind sigma function) (ih sigma)
  | baseLamCong _ ih => exact .baseLamCong (ih (liftSub sigma [.term]))
  | lambdaCong _ ih => exact .lambdaCong (ih (liftSub sigma [.term]))
  | whereValue body _ ih => exact .whereValue (bind (liftSub sigma [.term]) body) (ih sigma)
  | whereBody value _ ih => exact .whereBody (bind sigma value) (ih (liftSub sigma [.term]))
  | resultCong _ ih => exact .resultCong (ih sigma)

namespace BetaModel

abbrev metas := LambdaIntrinsicPresentation.metas

def equation : EqAxiom Target.sig metas where
  ctx := []
  sort := .term
  lhs := LambdaIntrinsicPresentation.betaLhs
  rhs := LambdaIntrinsicPresentation.betaRhs

def equations : List (EqAxiom Target.sig metas) := [equation]

def valuation {Γ : Ctx Target.sig} (body : Term Target.sig (.term :: Γ) .term)
    (value : Term Target.sig Γ .term) : ContextualAssignment Target.sig metas Γ
  | ⟨0, _⟩ => body
  | ⟨1, _⟩ => value
  | ⟨_ + 2, impossible⟩ => by simp [metas, LambdaIntrinsicPresentation.metas] at impossible

private def emptyEnvironment (Γ : Ctx Target.sig) : Sub Target.sig [] Γ :=
  fun _ x => nomatch x

theorem instantiate_lhs {Γ : Ctx Target.sig}
    (body : Term Target.sig (.term :: Γ) .term) (value : Term Target.sig Γ .term) :
    ContextualAssignment.instantiate (valuation body value) (fun _ x => .var x)
      (emptyEnvironment Γ) equation.lhs =
        LambdaContextualRung.appT (LambdaContextualRung.lamT body) value := by
  change LambdaContextualRung.appT
      (LambdaContextualRung.lamT (bind
        (ContextualAssignment.joinSub (S := Target.sig)
          (argsToSub (S := Target.sig) (bs := [LambdaContextualRung.Srt.term]) (.cons (Term.var .zero) .nil))
          (ContextualAssignment.weakenSub (S := Target.sig) [LambdaContextualRung.Srt.term]
            (fun _ x => Term.var x))) body))
      (bind (fun _ x => Term.var x) value) = _
  have identity :
      ContextualAssignment.joinSub (S := Target.sig)
        (argsToSub (S := Target.sig) (bs := [LambdaContextualRung.Srt.term]) (.cons (Term.var .zero) .nil))
        (ContextualAssignment.weakenSub (S := Target.sig) [LambdaContextualRung.Srt.term]
          (fun _ x => Term.var x)) =
        (fun _ x => Term.var x : Sub Target.sig (.term :: Γ) (.term :: Γ)) := by
    funext s x
    cases x <;> rfl
  rw [identity]
  exact congrArg₂ LambdaContextualRung.appT
    (congrArg LambdaContextualRung.lamT (bind_id body)) (bind_id value)

theorem instantiate_rhs {Γ : Ctx Target.sig}
    (body : Term Target.sig (.term :: Γ) .term) (value : Term Target.sig Γ .term) :
    ContextualAssignment.instantiate (valuation body value) (fun _ x => .var x)
      (emptyEnvironment Γ) equation.rhs = inst body value := by
  change bind (S := Target.sig) (ContextualAssignment.joinSub (S := Target.sig)
      (argsToSub (S := Target.sig) (bs := [LambdaContextualRung.Srt.term]) (.cons (bind (fun _ x => .var x) value) .nil))
      (fun _ x => .var x)) body = _
  rw [bind_id]
  have substitution :
      ContextualAssignment.joinSub (S := Target.sig) (argsToSub (S := Target.sig) (bs := [LambdaContextualRung.Srt.term]) (.cons value .nil))
        (fun _ x => .var x) = extend value := by
    funext s x
    cases x <;> rfl
  rw [substitution]
  rfl

/-- Open beta is an instance of the actual authored equation, not an extra
axiom added to the host logic. -/
theorem beta_equation {Γ : Ctx Target.sig}
    (body : Term Target.sig (.term :: Γ) .term) (value : Term Target.sig Γ .term) :
    EqClosure equations (LambdaContextualRung.appT (LambdaContextualRung.lamT body) value)
      (inst body value) := by
  have actual := EqClosure.ax (E := equations) (⟨0, by simp [equations]⟩ : Fin equations.length)
    (valuation body value) (fun _ x => Term.var x) (emptyEnvironment Γ)
  change EqClosure equations
    (ContextualAssignment.instantiate (valuation body value) (fun _ x => .var x)
      (emptyEnvironment Γ) equation.lhs)
    (ContextualAssignment.instantiate (valuation body value) (fun _ x => .var x)
      (emptyEnvironment Γ) equation.rhs) at actual
  rw [instantiate_lhs, instantiate_rhs] at actual
  exact actual

theorem step_equation {Γ : Ctx Target.sig} {first second : Term Target.sig Γ .term}
    (step : LambdaContextualRung.Step Γ first second) : EqClosure equations first second := by
  induction step with
  | beta body value => exact beta_equation body value
  | appCongL value _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.app
        (.cons ih (.cons (.refl value) .nil))
  | appCongR f _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.app
        (.cons (.refl f) (.cons ih .nil))
  | lamCong _ ih => exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.lam (.cons ih .nil)

/-- Every source rule, including contextual wrapper rules, preserves the
constructed beta-equation denotation. Result erasure is a zero-step case. -/
theorem source_step_equation {Γ : Ctx sig} {first second : Term sig Γ .term}
    (step : Step first second) : EqClosure equations (lower first) (lower second) := by
  induction step with
  | whereBeta value body => exact step_equation (where_lower_step value body)
  | resultErase payload => rw [lower_result]; exact .refl (lower payload)
  | baseBeta value body =>
      change EqClosure equations
        (LambdaContextualRung.appT (LambdaContextualRung.lamT (lower body)) (lower value))
        (lower (inst body value))
      rw [lower_inst]
      exact beta_equation (lower body) (lower value)
  | lambdaBeta value body =>
      change EqClosure equations
        (LambdaContextualRung.appT (LambdaContextualRung.lamT (lower body)) (lower value))
        (lower (inst body value))
      rw [lower_inst]
      exact beta_equation (lower body) (lower value)
  | baseAppLeft value _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.app
        (.cons ih (.cons (.refl (lower value)) .nil))
  | baseAppRight f _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.app
        (.cons (.refl (lower f)) (.cons ih .nil))
  | baseLamCong _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.lam (.cons ih .nil)
  | lambdaCong _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.lam (.cons ih .nil)
  | whereValue body _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.app
        (.cons (.refl (LambdaContextualRung.lamT (lower body))) (.cons ih .nil))
  | whereBody value _ ih =>
      exact EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.app
        (.cons (EqClosure.cong (S := Target.sig) LambdaContextualRung.Op.lam (.cons ih .nil))
          (.cons (.refl (lower value)) .nil))
  | resultCong _ ih => exact ih

/-- The free equational model and its proof of equation satisfaction were
constructed by the existing quotient machinery. -/
noncomputable def target := FreeBindingEquationModel.presented equations

noncomputable def denote {Γ : Ctx sig} {s : sig.Srt} (term : Term sig Γ s) :
    TermQ equations Γ s := interpret (model target.algebra) term

/-- The independently constructed model agrees with lowering followed by
the actual equation quotient projection. -/
theorem denote_lower {Γ : Ctx sig} {s : sig.Srt} (term : Term sig Γ s) :
    denote term = (Quotient.mk _ (lower term) : TermQ equations Γ s) := by
  exact (interpretation_naturality (BindingEquationQuotientModel.projection equations) term).symm

theorem denote_where_beta {Γ : Ctx sig} (value : Term sig Γ .term)
    (body : Term sig (.term :: Γ) .term) :
    denote (whereBinding value body) = denote (inst body value) := by
  rw [denote_lower, denote_lower]
  exact Quotient.sound (step_equation (where_lower_step value body))

theorem denote_result {Γ : Ctx sig} (payload : Term sig Γ .term) :
    denote (result payload) = denote payload := by
  rw [denote_lower, denote_lower, lower_result]

theorem denote_step {Γ : Ctx sig} {first second : Term sig Γ .term}
    (step : Step first second) : denote first = denote second := by
  rw [denote_lower, denote_lower]
  exact Quotient.sound (source_step_equation step)

theorem denote_bind {Γ Δ : Ctx sig} {s : sig.Srt} (env : Sub sig Γ Δ)
    (term : Term sig Γ s) :
    denote (bind env term) = target.algebra.substitution.substitute
      (fun s x => denote (env s x)) (denote term) :=
  interpret_bind (model target.algebra) env term

end BetaModel

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation
