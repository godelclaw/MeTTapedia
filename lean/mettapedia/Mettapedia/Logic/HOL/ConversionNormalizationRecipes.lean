import Mettapedia.Logic.HOL.ConversionRecipes

/-!
# Beta-conversion recipes from the existing normal-order evaluator

The strongly normalizing typed evaluator supplies finite executions. Their
actual redex positions form ordinary checked recipes under the beta-only
policy, with no additional equation declarations. Comparing normal forms
therefore produces explicit equality evidence rather than a trusted cast.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ConversionRecipes
open ContextualTrinity ConversionTiers
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable [DecidableEq Base] [∀ type, DecidableEq (Const type)]
variable {gamma : Ctx Base} {type : Ty Base}

def normalizationExecution (source : Term Const gamma type) :
    Execution source (normalForm source) :=
  match replayed : replay? source (normalOrderPositions (normalSteps source) source) with
  | none => False.elim (by
      have result := replay?_normalOrder (normalSteps source) source
      rw [replayed] at result
      cases result)
  | some ⟨target, execution⟩ =>
      have same : target = normalForm source := by
        have result := replay?_normalOrder (normalSteps source) source
        rw [replayed] at result
        exact Option.some.inj result
      same ▸ execution

def noEquations : EquationProofs ([] : List (DefiningEquation Const)) where
  proof _ member := nomatch member

def normalizationRecipe (source : Term Const gamma type) : Recipe (Const := Const) [] gamma type :=
  executionRecipe [] (normalizationExecution source)

theorem normalizationRecipe_checked (source : Term Const gamma type) :
    (checker (noEquations (Const := Const)) (.betaOnly 0) gamma type).check
      (source, normalForm source) (normalizationRecipe source) = true :=
  executionRecipe_checked noEquations (normalizationExecution source)

def betaRecipe? (source target : Term Const gamma type) : Option (Recipe (Const := Const) [] gamma type) :=
  if normalForm source = normalForm target then
    some (.trans (normalizationRecipe source) (.symm (normalizationRecipe target)))
  else none

theorem betaRecipe?_isSome_iff (source target : Term Const gamma type) :
    (betaRecipe? source target).isSome = true ↔ Joinable source target := by
  rw [joinable_iff_normalForm]
  simp [betaRecipe?]

theorem betaRecipe?_checked (source target : Term Const gamma type) (recipe : Recipe (Const := Const) [] gamma type)
    (produced : betaRecipe? source target = some recipe) :
    (checker noEquations (.betaOnly 0) gamma type).check (source, target) recipe = true := by
  unfold betaRecipe? at produced
  split at produced
  next same =>
    cases Option.some.inj produced
    apply EqualityRecipe.trans_checked (leafChecker noEquations (.betaOnly 0) gamma type)
      (normalizationRecipe source) (.symm (normalizationRecipe target)) source (normalForm source) target
    · exact normalizationRecipe_checked source
    · rw [same]
      exact EqualityRecipe.symm_checked (leafChecker noEquations (.betaOnly 0) gamma type)
        (normalizationRecipe target) target (normalForm target) (normalizationRecipe_checked target)
  next different => cases produced

def betaEquality? (source target : Term Const gamma type) :
    Option (ProofSyntax Const [] (.eq source target)) := do
  let recipe ← betaRecipe? source target
  elaborate? noEquations (.betaOnly 0) source target recipe []

theorem betaEquality?_isSome_iff (source target : Term Const gamma type) :
    (betaEquality? source target).isSome = true ↔ Joinable source target := by
  rw [← betaRecipe?_isSome_iff]
  unfold betaEquality?
  cases produced : betaRecipe? source target with
  | none => rfl
  | some recipe =>
      have checked := betaRecipe?_checked source target recipe produced
      simp [elaborate?, checked]

def betaConvertProof? {assumptions : List (Formula Const gamma)}
    {source : Formula Const gamma} (target : Formula Const gamma)
    (proof : ProofSyntax Const assumptions source) : Option (ProofSyntax Const assumptions target) := do
  let equality ← betaEquality? source target
  pure (.impE (.eqPropEL (ProofSyntax.mono (Δ := [])
    { index := fun occurrence => Fin.elim0 occurrence
      get_eq := fun occurrence => Fin.elim0 occurrence } equality)) proof)

#print axioms normalizationExecution
#print axioms betaEquality?
end Mettapedia.Logic.HOL.ConversionRecipes
