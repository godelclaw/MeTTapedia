import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusReification
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Indexed contextual classifiers in the canonical GSLT native predicates

The installed equation-free operational presentation supplies the actual
focus GSLT. Its equation classes are proved to be singletons; the complete
rely-family predicate therefore descends to the canonical OSLF type carrier.
This interprets indexed modal heads at semantic arguments. It does not
interpret every dependent expression of the generated native grammar.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusOSLF

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventAction (bound)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open FocusMeaning FiniteFocusChecking

variable (installed : Joined.Installed) (index : installed.Index) (ambient : List String)

def theory := gslt (BindingPipeline.plan installed.indexed.operational.generated)
  ((installed.indexed.schema index).focusBound ++ bound ambient) (installed.indexed.schema index).focusCarrier

theorem rules_enabled :
    (BindingPipeline.plan installed.indexed.operational.generated).permissions.sites.enabled = true := by
  change (StructuralDescent.Plan.refine installed.indexed.operational.generated.plan).permissions.sites.enabled = true
  rw [StructuralDescent.Plan.permissions_preserved]
  change installed.indexed.operational.generated.languageFragment.operational.sites.enabled = true
  rw [installed.indexed.operational.rootRules]
  rfl

theorem equivalent_eq {first second : Pattern}
    (equivalent : (theory installed index ambient).Equiv first second) : first = second := by
  change Relation.EqvGen (Equation (BindingPipeline.plan installed.indexed.operational.generated)
    ((installed.indexed.schema index).focusBound ++ bound ambient)
    (installed.indexed.schema index).focusCarrier) first second at equivalent
  induction equivalent with
  | rel first second edge =>
      obtain ⟨receipt, valid, _⟩ := edge
      have selected := valid.job.1
      rw [installed.indexed.operational.equationFree] at selected
      exact False.elim (List.not_mem_nil selected)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

variable {installed index ambient}

def occurrence {arguments : Arguments installed index ambient} {focus : Pattern}
    {values : RelyValues installed index ambient} (response : Response arguments focus values) :
    GeneralRuleJobs.Receipt where
  job := ⟨(installed.indexed.schema index).ordinal, (installed.indexed.schema index).declaration,
    GeneralTypedSites.SiteData.here (bound ambient) (.base (installed.programSort index)) response.source⟩
  matcherTrace := response.receipt.firing.answer.trace
  captured := response.receipt.firing.answer.captured
  completed := response.receipt.firing.answer.completed
  premiseHistory := response.receipt.firing.answer.history
  localTarget := response.receipt.firing.answer.target
  target := response.receipt.firing.answer.target

theorem occurrence_valid {arguments : Arguments installed index ambient} {focus : Pattern}
    {values : RelyValues installed index ambient} (response : Response arguments focus values) :
    (occurrence response).Valid (BindingPipeline.plan installed.indexed.operational.generated)
      (bound ambient) (.base (installed.programSort index)) response.source := by
  have firing := response.receipt.firing.answer.valid
  have typed :
      Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted installed.indexed.operational.Environment.language
        installed.indexed.operational.Environment.free (bound ambient) (.base (installed.programSort index)) response.source ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted installed.indexed.operational.Environment.language
        installed.indexed.operational.Environment.free (bound ambient) (.base (installed.programSort index))
        response.receipt.firing.answer.target := by
    cases firing with
    | fire _ _ _ sourceTyped _ _ _ _ targetTyped => exact ⟨sourceTyped, targetTyped⟩
  refine ⟨⟨(installed.indexed.schema index).declared,
    .here (rules_enabled installed) typed.1.2.2.1 typed.1.1⟩, ?_, rfl, rfl, typed.2⟩
  change GeneralPremise.RootFiring installed.indexed.operational.Environment (bound ambient)
    (.base (installed.programSort index)) response.source (installed.indexed.schema index).ordinal
    response.receipt.firing.answer.trace response.receipt.firing.answer.captured
    response.receipt.firing.answer.completed response.receipt.firing.answer.history response.receipt.firing.answer.target
  rw [← response.receipt.firing.selected]
  exact response.receipt.firing.answer.valid

/-- Each response is an actual primitive GSLT step at its reconstructed
program source. Focus classification does not turn the hole into that source. -/
theorem response_step {arguments : Arguments installed index ambient} {focus : Pattern}
    {values : RelyValues installed index ambient} (response : Response arguments focus values) :
    (gslt (BindingPipeline.plan installed.indexed.operational.generated) (bound ambient)
      (.base (installed.programSort index))).Step response.source response.receipt.firing.answer.target :=
  ⟨response.source, occurrence response, .refl _, occurrence_valid response, .refl _⟩

def predicate (arguments : Arguments installed index ambient) : EquationPredicate (theory installed index ambient) :=
  ⟨Inhabits arguments, by
    intro first second related
    have same := equivalent_eq installed index ambient related
    cases same
    exact Iff.rfl⟩

def nativeType (arguments : Arguments installed index ambient) : GSLTNativeType (theory installed index ambient) :=
  ⟨(), predicate arguments⟩

/-- Canonical OSLF satisfaction is exactly the independently specified
source family, including every rely request and the chosen RHS instance. -/
theorem satisfaction_source (arguments : Arguments installed index ambient) (focus : Pattern) :
    (gsltOSLF (theory installed index ambient)).satisfies (S := ()) focus (nativeType arguments).pred ↔
      SourceMeaning arguments focus :=
  inhabits_iff_source arguments focus

def onClasses (arguments : Arguments installed index ambient) :
    Quotient (theory installed index ambient).equations → Prop :=
  descendPredicate (theory installed index ambient) (predicate arguments)

theorem quotient_source (arguments : Arguments installed index ambient) (focus : Pattern) :
    onClasses arguments (Quotient.mk (theory installed index ambient).equations focus) ↔
      SourceMeaning arguments focus :=
  inhabits_iff_source arguments focus

theorem checked_native_membership (parameters : Parameters installed index ambient) (focus : Pattern)
    (certificate : List Witness) (checked : check parameters focus certificate = true) :
    (gsltOSLF (theory installed index ambient)).satisfies (S := ()) focus
      (nativeType parameters.meaning).pred :=
  check_sound parameters focus certificate checked

theorem native_membership_iff_certificate (parameters : Parameters installed index ambient) (focus : Pattern) :
    (gsltOSLF (theory installed index ambient)).satisfies (S := ()) focus
      (nativeType parameters.meaning).pred ↔
      ∃ certificate, check parameters focus certificate = true :=
  (certificate_exists_iff parameters focus).symm

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusOSLF
