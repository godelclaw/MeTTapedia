import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver
import Mettapedia.OSLF.Framework.GeneralCanonicalAgreementControls

/-!
# The partial-recursive machine, read at the front door

The authored machine's rules fire at the root, are first-order and aligned with the reference relation
(`profile`, `aligned`), and its declarations are represented (`declarations_represented`). Its syntax mask admits every
well-sorted closed configuration at an all-`⋆` sort profile (`maskAdmits`). So both of its runtime drivers are read
faithfully in its reference structure:

- **the local driver** of its generated presentation (`localReading`), which the runtime installs from the authored
  machine through the local profile;
- **the machine's own driver** (`driverReading`), whose constructor tests are those of the configuration category.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecReading

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan FirstOrderProfile ReadsProvider)
open Mettapedia.OSLF.NativeTypes.Generation (Generated structuralDeclaration)
open Mettapedia.Languages.PartrecMachine (partrecMachine)
open LocalReading

/-! ## The machine -/

abbrev provider : GeneralPremise.ProviderSnapshot := {signatures := [], rows := []}

theorem plan_eq : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan = rootPlan partrecMachine provider := rfl

theorem profile : FirstOrderProfile partrecMachine provider :=
  FirstOrderProfile.of_check Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.Controls.partrec_congruence_profile

theorem aligned : ReferenceStep.ReferenceProfile partrecMachine := by
  have checked : partrecMachine.rewrites.all ReferenceStep.ruleAligned = true := by decide +kernel
  exact fun rule member => List.all_eq_true.mp checked rule member

theorem declarations_represented : ∀ rule ∈ partrecMachine.terms, RepresentedDeclaration rule := by
  have checked : partrecMachine.terms.all isRepresentedDeclaration = true := by decide +kernel
  exact fun rule member => representedDeclaration_of_check (List.all_eq_true.mp checked rule member)

theorem represented_of_language {generated : Generated} (same : generated.snapshot.language = partrecMachine)
    (index : Fin generated.snapshot.language.terms.length) :
    RepresentedDeclaration (structuralDeclaration generated index) :=
  declarations_represented _ (same ▸ List.getElem_mem index.isLt)

/-- A well-sorted closed term is no variable, so its syntax sort is `⋆`. -/
theorem syntaxSort_of_typed {language : LanguageDef} {free : FreeTypeContext} (noFree : free = FreeTypeContext.empty)
    {type : TypeExpr} {source : Pattern} (typed : OpenPatternWellSorted language free [] type source) :
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.syntaxSort source = .star := by
  cases source with
  | bvar index =>
    cases typed.1 with
    | bvar found => simp at found
  | fvar name =>
    cases typed.1 with
    | fvar found =>
      rw [noFree] at found
      cases found
  | _ => rfl

/-- **The machine's sort mask admits every well-sorted closed term** at an all-`⋆` sort profile. -/
theorem maskAdmits {generated : Generated} (noFree : generated.snapshot.free = FreeTypeContext.empty)
    (star : ∀ position, generated.vertex.2 position = .star) :
    MaskAdmits generated Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.syntaxMask where
  output index source typed := by
    show decide (generated.vertex.2 _ = _) = true
    rw [star, syntaxSort_of_typed noFree typed]
    rfl
  input index position source typed := by
    show decide (generated.vertex.2 _ = _) = true
    rw [star, syntaxSort_of_typed noFree typed]
    rfl

/-! ## The local driver -/

abbrev generated : Generated := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated

theorem samePlan : generated.plan = rootPlan partrecMachine provider :=
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan

theorem foundation : generated.plan.complete = true := by
  rw [samePlan]
  exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_foundation

theorem equationFree : generated.plan.equations = [] :=
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equations

theorem generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true := by
  rw [samePlan]
  exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_generic

abbrev mask := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.syntaxMask

theorem generated_maskAdmits : MaskAdmits generated mask :=
  maskAdmits (snapshot_free_of_plan samePlan) (fun _ => rfl)

/-- **The local driver of the machine, read faithfully.** -/
def localReading :=
  reading profile aligned RelationEnv.empty (ReadsProvider.empty _) generated samePlan (.base "Cfg") foundation
    equationFree generic mask generated_maskAdmits (by decide)

theorem localReading_covered :
    ∀ name leaf, (Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.driver generated [] (.base "Cfg") foundation
      equationFree generic mask).lookup name = some leaf → localReading.covers leaf :=
  lookup_covered profile aligned RelationEnv.empty (ReadsProvider.empty _) generated samePlan (.base "Cfg") foundation
    equationFree generic mask generated_maskAdmits (by decide)
    (represented_of_language (snapshot_language_of_plan samePlan))

/-! ## The machine's own driver -/

open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver (Configuration driver)

/-- The machine's own driver at a configuration. -/
abbrev configured (configuration : Configuration) : Generated :=
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.generated configuration

theorem configured_plan (configuration : Configuration) :
    (configured configuration).plan = rootPlan partrecMachine provider :=
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.original_plan configuration

/-- **The machine's own driver, read faithfully**, at a configuration with an all-`⋆` sort profile. -/
def driverReading (configuration : Configuration)
    (star : ∀ position, (configured configuration).vertex.2 position = .star) :
    Embeddings.Faithful (driver configuration []) RelationEnv.empty partrecMachine
      (fun leaf => testVariable (configured configuration) leaf.val true)
      (fun leaf => testVariable (configured configuration) leaf.val false) where
  structure_ := referenceStructure RelationEnv.empty partrecMachine
  region := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source []
  steps source inside target :=
    rootStep_iff_reference profile aligned RelationEnv.empty (ReadsProvider.empty _) (.base "Cfg") inside
  closed _ _ _ step := step_target_typed Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_equations step
  rendering := (BoundedMorphism.identity _).toSplit
  renders := rfl
  covers _ := True
  test leaf := constructorFormula (structuralDeclaration (configured configuration) leaf.val)
  testAgrees leaf _ source inside := by
    have sameLanguage : (configured configuration).snapshot.language = partrecMachine :=
      snapshot_language_of_plan (configured_plan configuration)
    have typed : OpenPatternWellSorted (configured configuration).snapshot.language
        (configured configuration).snapshot.free [] (.base (structuralDeclaration (configured configuration)
          leaf.val).category) source := by
      have category : (structuralDeclaration (configured configuration) leaf.val).category = "Cfg" := leaf.property
      rw [category]
      have inside' : OpenPatternWellSorted (configured configuration).plan.snapshot.language
          (configured configuration).plan.snapshot.free [] (.base "Cfg") source := by
        rw [configured_plan]
        exact inside
      exact inside'
    exact (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.native_structural_meaning configuration [] leaf
      source).trans (structural_iff (configured configuration)
        (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.no_equations configuration)
        Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.syntaxMask (congrArg LanguageDef.terms sameLanguage)
        (snapshot_free_of_plan (configured_plan configuration)) profile.equationFree (by decide) leaf.val
        ((maskAdmits (snapshot_free_of_plan (configured_plan configuration)) star).at leaf.val) (fun _ _ => true)
        (fun _ _ => rfl) (represented_of_language sameLanguage leaf.val) typed)
  closing := closing (configured configuration)
  closesPositive leaf := closing_positive (configured configuration) leaf.val
  closesNegative leaf := closing_negative (configured configuration) leaf.val
  closingForward := closing_forward (configured configuration)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecReading
