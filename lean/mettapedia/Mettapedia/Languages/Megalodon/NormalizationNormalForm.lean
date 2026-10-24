import Mettapedia.Languages.Megalodon.NormalizationTermination
import Mettapedia.Logic.HOL.BetaEtaConfluence

/-!
# Stable native passes and typed beta/eta normal forms

The pass's stability flag is connected to the existing typed reduction
relation. The native erasure premise restricts the theorem to the grammar the
actual algorithm traverses; unsupported HOL connective nodes are encoded
before this pass is run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NormalizationNormalForm

open Mettapedia.Logic.HOL
open EtaConversion RetainedNormalization HenkinTermInterpretation MathdataKernel

variable {environment : Environment} {gamma : Ctx Base} {type domain result : Ty Base}

theorem betaHead_stable (function : Term (Constant environment) gamma (domain ⇒ result))
    (argument : Term (Constant environment) gamma domain) (stable : Bool)
    (finished : (betaHead function argument stable).stable = true) :
    stable = true ∧ (betaHead function argument stable).target = .app function argument := by
  cases function <;> simp_all [betaHead, unchanged]

theorem etaHead_stable (body : Term (Constant environment) (domain :: gamma) result)
    (stable : Bool) (finished : (etaHead body stable).stable = true) :
    stable = true ∧ (etaHead body stable).target = .lam body := by
  cases body with
  | app function argument =>
      cases argument with
      | var index =>
          cases index with
          | vz =>
              simp only [etaHead] at finished ⊢
              split at finished <;> simp_all [unchanged]
          | vs => simp_all [etaHead, unchanged]
      | const | app | lam | top | bot | and | or | imp | not | eq | all | ex =>
          simp_all [etaHead, unchanged]
  | var | const | lam | top | bot | and | or | imp | not | eq | all | ex =>
      simp_all [etaHead, unchanged]

/-- A stable pass leaves its intrinsic input unchanged. -/
theorem stable_target (source : Term (Constant environment) gamma type)
    (finished : (normalizeOne source).stable = true) : (normalizeOne source).target = source := by
  induction source with
  | var | const | top | bot | and | or | not | eq | ex => rfl
  | app function argument ihf iha =>
      obtain ⟨both, head⟩ := betaHead_stable (normalizeOne function).target
        (normalizeOne argument).target _ finished
      obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp both
      exact head.trans (congrArg₂ Term.app (ihf first) (iha second))
  | lam body ih =>
      obtain ⟨before, head⟩ := etaHead_stable (normalizeOne body).target _ finished
      exact head.trans (congrArg Term.lam (ih before))
  | imp left right ihl ihr =>
      obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp finished
      exact congrArg₂ Term.imp (ihl first) (ihr second)
  | all body ih => exact congrArg Term.all (ih finished)

/-- On the actual native grammar, stability excludes every typed beta/eta
contraction, including contractions below binders. -/
theorem stable_normal (source : Term (Constant environment) gamma type) {raw : Tm}
    (erased : erase source = some raw) (finished : (normalizeOne source).stable = true) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep source := by
  induction source generalizing raw with
  | var | const =>
      intro target step
      rcases step with reduced | step
      · obtain ⟨step⟩ := reduced
        cases step
      · cases step
  | top | bot | and | or | not | eq | ex => simp [erase] at erased
  | app function argument ihf iha =>
      cases erasedFunction : erase function with
      | none => simp [erase, erasedFunction] at erased
      | some rawFunction =>
          cases erasedArgument : erase argument with
          | none => simp [erase, erasedArgument] at erased
          | some rawArgument =>
              obtain ⟨both, _⟩ := betaHead_stable (normalizeOne function).target
                (normalizeOne argument).target _ finished
              obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp both
              have functionFixed := stable_target function first
              have headFinished : (betaHead (normalizeOne function).target
                  (normalizeOne argument).target
                  ((normalizeOne function).stable && (normalizeOne argument).stable)).stable = true :=
                finished
              have functionNormal := ihf erasedFunction first
              have argumentNormal := iha erasedArgument second
              intro target step
              rcases step with reduced | step
              · obtain ⟨step⟩ := reduced
                cases step with
                | beta =>
                    rw [functionFixed] at headFinished
                    simp [betaHead] at headFinished
                | appFun _ inner => exact functionNormal _ (Or.inl ⟨inner⟩)
                | appArg _ inner => exact argumentNormal _ (Or.inl ⟨inner⟩)
              · cases step with
                | appFun _ inner => exact functionNormal _ (Or.inr inner)
                | appArg _ inner => exact argumentNormal _ (Or.inr inner)
  | lam body ih =>
      cases erasedBody : erase body with
      | none => simp [erase, erasedBody] at erased
      | some rawBody =>
          obtain ⟨before, _⟩ := etaHead_stable (normalizeOne body).target _ finished
          have bodyFixed := stable_target body before
          have headFinished : (etaHead (normalizeOne body).target
              (normalizeOne body).stable).stable = true := finished
          have bodyNormal := ih erasedBody before
          intro target step
          rcases step with reduced | step
          · obtain ⟨step⟩ := reduced
            cases step with
            | lam inner => exact bodyNormal _ (Or.inl ⟨inner⟩)
          · cases step with
            | eta =>
                rw [bodyFixed] at headFinished
                simp only [etaHead] at headFinished
                split at headFinished
                next failed =>
                  simp [rename?_drop_weaken] at failed
                next _ _ => cases headFinished
            | lam inner => exact bodyNormal _ (Or.inr inner)
  | imp left right ihl ihr =>
      cases erasedLeft : erase left with
      | none => simp [erase, erasedLeft] at erased
      | some rawLeft =>
          cases erasedRight : erase right with
          | none => simp [erase, erasedRight] at erased
          | some rawRight =>
              obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp finished
              have leftNormal := ihl erasedLeft first
              have rightNormal := ihr erasedRight second
              intro target step
              rcases step with reduced | step
              · obtain ⟨step⟩ := reduced
                cases step with
                | impLeft _ inner => exact leftNormal _ (Or.inl ⟨inner⟩)
                | impRight _ inner => exact rightNormal _ (Or.inl ⟨inner⟩)
              · cases step with
                | impLeft _ inner => exact leftNormal _ (Or.inr inner)
                | impRight _ inner => exact rightNormal _ (Or.inr inner)
  | all body ih =>
      cases erasedBody : erase body with
      | none => simp [erase, erasedBody] at erased
      | some rawBody =>
          have bodyNormal := ih erasedBody finished
          intro target step
          rcases step with reduced | step
          · obtain ⟨step⟩ := reduced
            cases step with
            | all inner => exact bodyNormal _ (Or.inl ⟨inner⟩)
          · cases step with
            | all inner => exact bodyNormal _ (Or.inr inner)

/-- Every successful retained run reaches a genuine normal form through the
existing typed beta/eta relation. -/
theorem normalize_result (fuel : Nat) (source : Term (Constant environment) gamma type)
    {raw : Tm} (erased : erase source = some raw) {pass : Pass source}
    (computed : RetainedNormalization.normalize fuel source = some pass) :
    NormalizationTermination.Many source pass.target ∧
      Mettapedia.Logic.Relation.IsNormal BetaEtaStep pass.target := by
  induction fuel generalizing source raw with
  | zero =>
      simp only [RetainedNormalization.normalize] at computed
      split at computed
      next stable =>
        cases Option.some.inj computed
        refine ⟨(NormalizationTermination.normalizeOne_steps source).1, ?_⟩
        rw [stable_target source stable]
        exact stable_normal source erased stable
      next => cases computed
  | succ fuel ih =>
      simp only [RetainedNormalization.normalize] at computed
      split at computed
      next stable =>
        cases Option.some.inj computed
        refine ⟨(NormalizationTermination.normalizeOne_steps source).1, ?_⟩
        rw [stable_target source stable]
        exact stable_normal source erased stable
      next unstable =>
        cases later : RetainedNormalization.normalize fuel (normalizeOne source).target with
        | none => simp [later] at computed
        | some rest =>
            simp only [later, Option.pure_def] at computed
            cases computed
            have targetErased := (normalizeOne_erases source erased).1
            obtain ⟨steps, normal⟩ := ih (normalizeOne source).target targetErased later
            exact ⟨(NormalizationTermination.normalizeOne_steps source).1.trans steps, normal⟩

/-- Successful native normalization has the same normal intrinsic result as
the retained algorithm, including the reflexivity optimization in readback. -/
theorem native_result (fuel : Nat) (source : Term (Constant environment) gamma type)
    {raw target : Tm} (erased : erase source = some raw)
    (accepted : Tm.normalize fuel raw = some target) :
    NormalizationTermination.Many source
        (RetainedNormalization.readback fuel source erased accepted).val.target ∧
      Mettapedia.Logic.Relation.IsNormal BetaEtaStep
        (RetainedNormalization.readback fuel source erased accepted).val.target := by
  have comparison := normalize_erases fuel source erased
  rw [accepted] at comparison
  cases computed : RetainedNormalization.normalize fuel source with
  | none => simp [computed] at comparison
  | some pass =>
      have targetErased : erase pass.target = some target := by simpa [computed] using comparison
      have same := erase_injective_of_eq_some targetErased
        (RetainedNormalization.readback fuel source erased accepted).property
      rw [← same]
      exact normalize_result fuel source erased computed

/-- Any two successful native budgets agree on beta/eta-convertible intrinsic
inputs. The conclusion compares actual raw outputs, not just denotations. -/
theorem normalize_coherent (left right : Term (Constant environment) gamma type)
    {leftRaw rightRaw leftOutput rightOutput : Tm} {leftFuel rightFuel : Nat}
    (leftErased : erase left = some leftRaw) (rightErased : erase right = some rightRaw)
    (converted : BetaEtaConv left right)
    (leftAccepted : Tm.normalize leftFuel leftRaw = some leftOutput)
    (rightAccepted : Tm.normalize rightFuel rightRaw = some rightOutput) :
    leftOutput = rightOutput := by
  let leftResult := RetainedNormalization.readback leftFuel left leftErased leftAccepted
  let rightResult := RetainedNormalization.readback rightFuel right rightErased rightAccepted
  obtain ⟨leftSteps, leftNormal⟩ := native_result leftFuel left leftErased leftAccepted
  obtain ⟨rightSteps, rightNormal⟩ := native_result rightFuel right rightErased rightAccepted
  have normalConversion : BetaEtaConv leftResult.val.target rightResult.val.target :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.reflTransGen_le_eqvGen BetaEtaStep _ _ leftSteps))
      (Relation.EqvGen.trans _ _ _ converted
        (Relation.EqvGen.reflTransGen_le_eqvGen BetaEtaStep _ _ rightSteps))
  have same := BetaEtaConfluence.normal_eq_of_convertible leftNormal rightNormal normalConversion
  have sameErasure := congrArg erase same
  rw [leftResult.property, rightResult.property] at sameErasure
  exact Option.some.inj sameErasure

/-- The existing native algorithm computes a certified normal form on every
intrinsic input that erases into its grammar. -/
def completedResult (source : Term (Constant environment) gamma type) {raw : Tm}
    (erased : erase source = some raw) :
    Mettapedia.Logic.Relation.NormalizationResult BetaEtaStep source :=
  let run := NormalizationTermination.complete source erased
  let result := RetainedNormalization.readback run.val.1 source erased run.property
  let valid := native_result run.val.1 source erased run.property
  ⟨result.val.target, valid.1, valid.2⟩

theorem completed_erased (source : Term (Constant environment) gamma type) {raw : Tm}
    (erased : erase source = some raw) :
    erase (completedResult source erased).normalForm =
      some (NormalizationTermination.complete source erased).val.2 :=
  (RetainedNormalization.readback _ source erased
    (NormalizationTermination.complete source erased).property).property

theorem completed_eq_iff_convertible (left right : Term (Constant environment) gamma type)
    {leftRaw rightRaw : Tm} (leftErased : erase left = some leftRaw)
    (rightErased : erase right = some rightRaw) :
    (NormalizationTermination.complete left leftErased).val.2 =
        (NormalizationTermination.complete right rightErased).val.2 ↔ BetaEtaConv left right := by
  have comparison := Mettapedia.Logic.Relation.NormalizationResult.eq_iff_eqvGen
    BetaEtaConfluence.confluent (completedResult left leftErased) (completedResult right rightErased)
  constructor
  · intro same
    apply comparison.mp
    exact erase_injective_of_eq_some
      ((completed_erased left leftErased).trans (congrArg some same))
      (completed_erased right rightErased)
  · intro converted
    have same := congrArg erase (comparison.mpr converted)
    rw [completed_erased left leftErased, completed_erased right rightErased] at same
    exact Option.some.inj same

/-- Decide monomorphic beta/eta conversion using computed native budgets.
The type and context are shared by the two intrinsic inputs. -/
def decideConversion (left right : Term (Constant environment) gamma type)
    {leftRaw rightRaw : Tm} (leftErased : erase left = some leftRaw)
    (rightErased : erase right = some rightRaw) : Bool :=
  decide ((NormalizationTermination.complete left leftErased).val.2 =
    (NormalizationTermination.complete right rightErased).val.2)

theorem decideConversion_correct (left right : Term (Constant environment) gamma type)
    {leftRaw rightRaw : Tm} (leftErased : erase left = some leftRaw)
    (rightErased : erase right = some rightRaw) :
    decideConversion left right leftErased rightErased = true ↔ BetaEtaConv left right := by
  rw [decideConversion, decide_eq_true_eq]
  exact completed_eq_iff_convertible left right leftErased rightErased

#print axioms betaHead_stable
#print axioms etaHead_stable
#print axioms stable_target
#print axioms stable_normal
#print axioms normalize_result
#print axioms native_result
#print axioms normalize_coherent
#print axioms completedResult
#print axioms completed_eq_iff_convertible
#print axioms decideConversion_correct

end Mettapedia.Languages.Megalodon.NormalizationNormalForm
