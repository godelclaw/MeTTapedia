import Mettapedia.Logic.HOL.EtaConversion
import Mettapedia.Logic.HOL.Syntax.PartialRenaming
import Mettapedia.Logic.Relation.Normalization

/-!
# Termination of typed eta contraction

The existing capture-avoiding eta relation strictly decreases the number of
term-constructor nodes, at every position and in every typed context.
Renaming preserves this measure. These results concern eta contraction;
termination of an interleaved beta/eta algorithm additionally needs their
interaction laws.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.EtaNormalization

open EtaConversion

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma delta : Ctx Base} {type : Ty Base}

theorem nodeCount_rename (rho : Rename Base gamma delta)
    (term : Term Const gamma type) :
    (rename rho term).nodeCount = term.nodeCount := by
  induction term generalizing delta <;> simp_all [rename, Term.nodeCount]

theorem nodeCount_decreases {source target : Term Const gamma type}
    (step : EtaStep source target) : target.nodeCount < source.nodeCount := by
  induction step <;> simp_all [Term.nodeCount, weaken, nodeCount_rename]
  omega

theorem stronglyNormalizing (term : Term Const gamma type) :
    Acc (fun later earlier => EtaStep earlier later) term :=
  (((measure (fun value : Term Const gamma type => value.nodeCount)).wf).mono
    (fun _ _ step => nodeCount_decreases step)).apply term

theorem rename_step (rho : Rename Base gamma delta) {source target : Term Const gamma type}
    (step : EtaStep source target) : EtaStep (rename rho source) (rename rho target) := by
  induction step generalizing delta with
  | eta function =>
      simpa only [rename, weaken, rename_lift_weaken, Rename.lift] using
        (EtaStep.eta (rename rho function))
  | appFun _ _ ih => exact .appFun _ (ih rho)
  | appArg _ _ ih => exact .appArg _ (ih rho)
  | lam _ ih => exact .lam (ih (Rename.lift rho))
  | andLeft _ _ ih => exact .andLeft _ (ih rho)
  | andRight _ _ ih => exact .andRight _ (ih rho)
  | orLeft _ _ ih => exact .orLeft _ (ih rho)
  | orRight _ _ ih => exact .orRight _ (ih rho)
  | impLeft _ _ ih => exact .impLeft _ (ih rho)
  | impRight _ _ ih => exact .impRight _ (ih rho)
  | not _ ih => exact .not (ih rho)
  | eqLeft _ _ ih => exact .eqLeft _ (ih rho)
  | eqRight _ _ ih => exact .eqRight _ (ih rho)
  | all _ ih => exact .all (ih (Rename.lift rho))
  | ex _ ih => exact .ex (ih (Rename.lift rho))

theorem subst_step (theta : Subst Const gamma delta) {source target : Term Const gamma type}
    (step : EtaStep source target) : EtaStep (subst theta source) (subst theta target) := by
  induction step generalizing delta with
  | eta function =>
      simpa only [subst, Subst.lift, subst_weaken] using
        (EtaStep.eta (subst theta function))
  | appFun _ _ ih => exact .appFun _ (ih theta)
  | appArg _ _ ih => exact .appArg _ (ih theta)
  | lam _ ih => exact .lam (ih (Subst.lift theta))
  | andLeft _ _ ih => exact .andLeft _ (ih theta)
  | andRight _ _ ih => exact .andRight _ (ih theta)
  | orLeft _ _ ih => exact .orLeft _ (ih theta)
  | orRight _ _ ih => exact .orRight _ (ih theta)
  | impLeft _ _ ih => exact .impLeft _ (ih theta)
  | impRight _ _ ih => exact .impRight _ (ih theta)
  | not _ ih => exact .not (ih theta)
  | eqLeft _ _ ih => exact .eqLeft _ (ih theta)
  | eqRight _ _ ih => exact .eqRight _ (ih theta)
  | all _ ih => exact .all (ih (Subst.lift theta))
  | ex _ ih => exact .ex (ih (Subst.lift theta))

/-- Successful partial renaming transports eta contraction and remains
successful at its target. No removed variable can be introduced by the step. -/
theorem partial_rename (rho : PartialRename Base gamma delta)
    {source target : Term Const gamma type} (step : EtaStep source target)
    {renamed : Term Const delta type} (success : rename? rho source = some renamed) :
    ∃ result, rename? rho target = some result ∧ EtaStep renamed result := by
  induction step generalizing delta with
  | eta function =>
      cases computed : rename? rho function with
      | none =>
          simp [rename?, rename?_weaken, computed, PartialRename.lift] at success
      | some result =>
          have mapped : rename? rho (.lam (.app (weaken function) (.var .vz))) =
              some (.lam (.app (weaken result) (.var .vz))) := by
            simp [rename?, rename?_weaken, computed, PartialRename.lift]
          rw [mapped] at success
          cases success
          exact ⟨result, rfl, .eta result⟩
  | @appFun gamma domain result first first' second child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (oneResult)
              exact ⟨Term.app result two, by simp [rename?, computed, twoResult], .appFun two moved⟩
  | @appArg gamma domain result first second second' child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (twoResult)
              exact ⟨Term.app one result, by simp [rename?, computed, oneResult], .appArg one moved⟩
  | @andLeft gamma first first' second child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (oneResult)
              exact ⟨Term.and result two, by simp [rename?, computed, twoResult], .andLeft two moved⟩
  | @andRight gamma first second second' child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (twoResult)
              exact ⟨Term.and one result, by simp [rename?, computed, oneResult], .andRight one moved⟩
  | @orLeft gamma first first' second child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (oneResult)
              exact ⟨Term.or result two, by simp [rename?, computed, twoResult], .orLeft two moved⟩
  | @orRight gamma first second second' child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (twoResult)
              exact ⟨Term.or one result, by simp [rename?, computed, oneResult], .orRight one moved⟩
  | @impLeft gamma first first' second child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (oneResult)
              exact ⟨Term.imp result two, by simp [rename?, computed, twoResult], .impLeft two moved⟩
  | @impRight gamma first second second' child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (twoResult)
              exact ⟨Term.imp one result, by simp [rename?, computed, oneResult], .impRight one moved⟩
  | @eqLeft gamma value first first' second child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (oneResult)
              exact ⟨Term.eq result two, by simp [rename?, computed, twoResult], .eqLeft two moved⟩
  | @eqRight gamma value first second second' child ih =>
      cases oneResult : rename? rho first with
      | none => simp [rename?, oneResult] at success
      | some one =>
          cases twoResult : rename? rho second with
          | none => simp [rename?, oneResult, twoResult] at success
          | some two =>
              simp only [rename?, oneResult, twoResult, Option.pure_def] at success
              cases success
              obtain ⟨result, computed, moved⟩ := ih rho (twoResult)
              exact ⟨Term.eq one result, by simp [rename?, computed, oneResult], .eqRight one moved⟩
  | @lam gamma domain result before after child ih =>
      cases bodyResult : rename? (PartialRename.lift rho) before with
      | none => simp [rename?, bodyResult] at success
      | some body =>
          simp only [rename?, bodyResult, Option.map_some, Option.some.injEq] at success
          cases success
          obtain ⟨result, computed, moved⟩ := ih (PartialRename.lift rho) bodyResult
          exact ⟨.lam result, by simp [rename?, computed], .lam moved⟩
  | @not gamma before after child ih =>
      cases bodyResult : rename? rho before with
      | none => simp [rename?, bodyResult] at success
      | some body =>
          simp only [rename?, bodyResult, Option.map_some, Option.some.injEq] at success
          cases success
          obtain ⟨result, computed, moved⟩ := ih rho bodyResult
          exact ⟨.not result, by simp [rename?, computed], .not moved⟩
  | @all gamma domain before after child ih =>
      cases bodyResult : rename? (PartialRename.lift rho) before with
      | none => simp [rename?, bodyResult] at success
      | some body =>
          simp only [rename?, bodyResult, Option.map_some, Option.some.injEq] at success
          cases success
          obtain ⟨result, computed, moved⟩ := ih (PartialRename.lift rho) bodyResult
          exact ⟨.all result, by simp [rename?, computed], .all moved⟩
  | @ex gamma domain before after child ih =>
      cases bodyResult : rename? (PartialRename.lift rho) before with
      | none => simp [rename?, bodyResult] at success
      | some body =>
          simp only [rename?, bodyResult, Option.map_some, Option.some.injEq] at success
          cases success
          obtain ⟨result, computed, moved⟩ := ih (PartialRename.lift rho) bodyResult
          exact ⟨.ex result, by simp [rename?, computed], .ex moved⟩

theorem weaken_step_inv {domain : Ty Base} {source : Term Const gamma type}
    {target : Term Const (domain :: gamma) type} (step : EtaStep (weaken source) target) :
    ∃ lowered, weaken lowered = target ∧ EtaStep source lowered := by
  obtain ⟨lowered, success, moved⟩ := partial_rename PartialRename.drop step (rename?_drop_weaken source)
  exact ⟨lowered, weaken_of_rename?_drop success, moved⟩

private theorem preserves_unary {other : Ctx Base} {first second : Ty Base}
    (wrap : Term Const gamma first → Term Const other second)
    (move : ∀ {source target}, BetaNormalization.Reduces source target →
      BetaNormalization.Reduces (wrap source) (wrap target))
    (project : ∀ source result, BetaNormalization.Reduces (wrap source) result →
      ∃ target, BetaNormalization.Reduces source target)
    {source target : Term Const gamma first}
    (preserves : BetaNormalization.Normal source → BetaNormalization.Normal target) :
    BetaNormalization.Normal (wrap source) → BetaNormalization.Normal (wrap target) := by
  intro normal result step
  have sourceNormal : BetaNormalization.Normal source :=
    fun next reduced => normal (wrap next) (move reduced)
  obtain ⟨next, reduced⟩ := project target result step
  exact preserves sourceNormal next reduced

private theorem preserves_binary {first second result : Ty Base}
    (wrap : Term Const gamma first → Term Const gamma second → Term Const gamma result)
    (moveFirst : ∀ {source target} right, BetaNormalization.Reduces source target →
      BetaNormalization.Reduces (wrap source right) (wrap target right))
    (moveSecond : ∀ {source target} left, BetaNormalization.Reduces source target →
      BetaNormalization.Reduces (wrap left source) (wrap left target))
    (project : ∀ left right output, BetaNormalization.Reduces (wrap left right) output →
      (∃ next, BetaNormalization.Reduces left next) ∨
        ∃ next, BetaNormalization.Reduces right next)
    {left left' : Term Const gamma first} {right right' : Term Const gamma second}
    (preservesFirst : BetaNormalization.Normal left → BetaNormalization.Normal left')
    (preservesSecond : BetaNormalization.Normal right → BetaNormalization.Normal right') :
    BetaNormalization.Normal (wrap left right) → BetaNormalization.Normal (wrap left' right') := by
  intro normal output step
  have leftNormal : BetaNormalization.Normal left :=
    fun next reduced => normal (wrap next right) (moveFirst right reduced)
  have rightNormal : BetaNormalization.Normal right :=
    fun next reduced => normal (wrap left next) (moveSecond left reduced)
  rcases project left' right' output step with ⟨next, reduced⟩ | ⟨next, reduced⟩
  · exact preservesFirst leftNormal next reduced
  · exact preservesSecond rightNormal next reduced

private theorem normal_app_iff {domain result : Ty Base}
    (function : Term Const gamma (domain ⇒ result)) (argument : Term Const gamma domain) :
    BetaNormalization.Normal (.app function argument) ↔
      BetaNormalization.Neutral function ∧ BetaNormalization.Normal function ∧
        BetaNormalization.Normal argument := by
  constructor
  · intro normal
    refine ⟨?_, ?_, ?_⟩
    · cases function with
      | var | const | app => trivial
      | lam body => exact normal _ ⟨.beta body argument⟩
    · intro next ⟨step⟩
      exact normal _ ⟨.appFun argument step⟩
    · intro next ⟨step⟩
      exact normal _ ⟨.appArg function step⟩
  · rintro ⟨neutral, functionNormal, argumentNormal⟩ output step
    rcases BetaNormalization.app_cases step with
      ⟨body, same, _⟩ | ⟨next, reduced, _⟩ | ⟨next, reduced, _⟩
    · subst function
      exact neutral
    · exact functionNormal next reduced
    · exact argumentNormal next reduced

theorem neutral_preserved {source target : Term Const gamma type}
    (step : EtaStep source target) :
    BetaNormalization.Neutral source → BetaNormalization.Neutral target := by
  cases step <;> simp_all [BetaNormalization.Neutral]

/-- Eta contraction preserves beta-normality throughout the full HOL term grammar. -/
theorem preserves_betaNormal {source target : Term Const gamma type}
    (step : EtaStep source target) :
    BetaNormalization.Normal source → BetaNormalization.Normal target := by
  induction step with
  | eta function =>
      intro normal output reduced
      obtain ⟨moved⟩ := BetaNormalization.reduces_rename (Rename.weaken (σ := _)) reduced
      exact normal _ ⟨.lam (.appFun (.var .vz) moved)⟩
  | appFun argument step ih =>
      intro normal
      obtain ⟨neutral, functionNormal, argumentNormal⟩ := (normal_app_iff _ _).mp normal
      exact (normal_app_iff _ _).mpr ⟨neutral_preserved step neutral, ih functionNormal, argumentNormal⟩
  | appArg function _ ih =>
      intro normal
      obtain ⟨neutral, functionNormal, argumentNormal⟩ := (normal_app_iff _ _).mp normal
      exact (normal_app_iff _ _).mpr ⟨neutral, functionNormal, ih argumentNormal⟩
  | lam _ ih =>
      apply preserves_unary Term.lam (fun ⟨step⟩ => ⟨.lam step⟩) ?_ ih
      intro body output reduced
      obtain ⟨next, step, _⟩ := BetaNormalization.lam_cases reduced
      exact ⟨next, step⟩
  | all _ ih =>
      apply preserves_unary Term.all (fun ⟨step⟩ => ⟨.all step⟩) ?_ ih
      intro body output reduced
      obtain ⟨next, step, _⟩ := BetaNormalization.all_cases reduced
      exact ⟨next, step⟩
  | ex _ ih =>
      apply preserves_unary Term.ex (fun ⟨step⟩ => ⟨.ex step⟩) ?_ ih
      intro body output reduced
      obtain ⟨next, step, _⟩ := BetaNormalization.ex_cases reduced
      exact ⟨next, step⟩
  | not _ ih =>
      apply preserves_unary Term.not (fun ⟨step⟩ => ⟨.not step⟩) ?_ ih
      intro body output reduced
      obtain ⟨next, step, _⟩ := BetaNormalization.not_cases reduced
      exact ⟨next, step⟩
  | andLeft _ _ ih =>
      apply preserves_binary Term.and (fun _ ⟨step⟩ => ⟨.andLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.andRight _ step⟩) ?_ ih id
      intro left right output reduced
      rcases BetaNormalization.and_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | andRight _ _ ih =>
      apply preserves_binary Term.and (fun _ ⟨step⟩ => ⟨.andLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.andRight _ step⟩) ?_ id ih
      intro left right output reduced
      rcases BetaNormalization.and_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | orLeft _ _ ih =>
      apply preserves_binary Term.or (fun _ ⟨step⟩ => ⟨.orLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.orRight _ step⟩) ?_ ih id
      intro left right output reduced
      rcases BetaNormalization.or_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | orRight _ _ ih =>
      apply preserves_binary Term.or (fun _ ⟨step⟩ => ⟨.orLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.orRight _ step⟩) ?_ id ih
      intro left right output reduced
      rcases BetaNormalization.or_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | impLeft _ _ ih =>
      apply preserves_binary Term.imp (fun _ ⟨step⟩ => ⟨.impLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.impRight _ step⟩) ?_ ih id
      intro left right output reduced
      rcases BetaNormalization.imp_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | impRight _ _ ih =>
      apply preserves_binary Term.imp (fun _ ⟨step⟩ => ⟨.impLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.impRight _ step⟩) ?_ id ih
      intro left right output reduced
      rcases BetaNormalization.imp_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | eqLeft _ _ ih =>
      apply preserves_binary Term.eq (fun _ ⟨step⟩ => ⟨.eqLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.eqRight _ step⟩) ?_ ih id
      intro left right output reduced
      rcases BetaNormalization.eq_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩
  | eqRight _ _ ih =>
      apply preserves_binary Term.eq (fun _ ⟨step⟩ => ⟨.eqLeft _ step⟩)
        (fun _ ⟨step⟩ => ⟨.eqRight _ step⟩) ?_ id ih
      intro left right output reduced
      rcases BetaNormalization.eq_cases reduced with ⟨next, step, _⟩ | ⟨next, step, _⟩
      · exact Or.inl ⟨next, step⟩
      · exact Or.inr ⟨next, step⟩

theorem eta_contraction {domain result : Ty Base} (function : Term Const gamma (domain ⇒ result)) :
    EtaStep (.lam (.app (weaken (σ := domain) function) (.var .vz))) function :=
  .eta function

theorem not_reflexive (term : Term Const gamma type) : ¬ EtaStep term term := by
  intro step
  exact Nat.lt_irrefl _ (nodeCount_decreases step)

theorem nodeCount_le {source target : Term Const gamma type}
    (steps : Relation.ReflTransGen EtaStep source target) : target.nodeCount ≤ source.nodeCount := by
  induction steps with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact (Nat.le_of_lt (nodeCount_decreases step)).trans ih

theorem no_cycle {source target : Term Const gamma type} (step : EtaStep source target)
    (back : Relation.ReflTransGen EtaStep target source) : False :=
  Nat.not_lt_of_ge (nodeCount_le back) (nodeCount_decreases step)

theorem preserves_betaNormal_star {source target : Term Const gamma type}
    (steps : Relation.ReflTransGen EtaStep source target)
    (normal : BetaNormalization.Normal source) : BetaNormalization.Normal target := by
  induction steps with
  | refl => exact normal
  | tail _ step ih => exact preserves_betaNormal step ih

theorem exists_normalForm (term : Term Const gamma type) :
    ∃ normal, Relation.ReflTransGen EtaStep term normal ∧ ∀ target, ¬ EtaStep normal target :=
  Mettapedia.Logic.Relation.exists_normalForm_of_acc (stronglyNormalizing term)

/-- Every intrinsically typed HOL term has a beta/eta normal form: beta
normalization followed by eta contraction. This is relational existence,
not completeness of a particular interleaved normalization algorithm. -/
theorem exists_betaEta_normalForm (term : Term Const gamma type) :
    ∃ normal, Relation.ReflTransGen BetaEtaStep term normal ∧
      ∀ target, ¬ BetaEtaStep normal target := by
  obtain ⟨betaNormal, betaSteps, betaFinished⟩ :=
    Mettapedia.Logic.Relation.exists_normalForm_of_acc (BetaNormalization.stronglyNormalizing term)
  obtain ⟨normal, etaSteps, etaFinished⟩ := exists_normalForm betaNormal
  refine ⟨normal, ?_, ?_⟩
  · have beta : Relation.ReflTransGen BetaEtaStep term betaNormal :=
      Relation.ReflTransGen.mono (fun _ _ step => Or.inl step) _ _ betaSteps
    have eta : Relation.ReflTransGen BetaEtaStep betaNormal normal :=
      Relation.ReflTransGen.mono (fun _ _ step => Or.inr step) _ _ etaSteps
    exact beta.trans eta
  · intro target step
    rcases step with beta | eta
    · exact preserves_betaNormal_star etaSteps betaFinished target beta
    · exact etaFinished target eta

/-- Constructor count alone cannot justify an interleaved beta/eta normalizer. -/
theorem beta_can_increase_nodeCount :
    ∃ source target : ClosedFormula Const,
      Nonempty (ContextualTrinity.BetaStep source target) ∧ source.nodeCount < target.nodeCount := by
  let truth : ClosedFormula Const := .all (σ := .prop) (.imp (.var .vz) (.var .vz))
  let argument : ClosedFormula Const := .imp truth truth
  let body : Formula Const [.prop] := .imp (.var .vz) (.var .vz)
  refine ⟨.app (.lam body) argument, instantiate argument body, ⟨.beta body argument⟩, ?_⟩
  change 14 < 19
  omega

#print axioms nodeCount_decreases
#print axioms stronglyNormalizing
#print axioms rename_step
#print axioms subst_step
#print axioms partial_rename
#print axioms weaken_step_inv
#print axioms preserves_betaNormal
#print axioms not_reflexive
#print axioms no_cycle
#print axioms beta_can_increase_nodeCount
#print axioms exists_betaEta_normalForm

end Mettapedia.Logic.HOL.EtaNormalization
