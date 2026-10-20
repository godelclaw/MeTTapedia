import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoPrimitive
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Profile
import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop
import Mettapedia.OSLF.MeTTaIL.GeneralRuleReceiptSource

/-!
# Native rho execution modulo the quote-drop model

The primitive graph uses the compiled rho plan and its standard parallel
reduction contexts. Equality contains its declared parallel laws and
`@(*n) = n`; empty and singleton parallel wrappers remain observable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoProfile

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling
open DerivedContexts

abbrev plan := GeneralRho.Standard.plan
abbrev proc : TypeExpr := .base "Proc"
abbrev presentation := Complete.RhoQuoteDrop.presentation
abbrev form := Complete.QuoteDropCoherence.commit plan presentation

/-- Every actual rho firing survives committing the quote-drop model form.
The sorting premise of the generic coherence theorem follows from the
complete primitive receipt; callers supply no separate source invariant. -/
theorem primitive_form {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan [] proc source receipt) :
    ∃ next, GeneralOccurrenceSemantics.Primitive plan [] proc (form source) next ∧
      Complete.QuoteDropCoherence.ModelEquiv plan [] proc presentation receipt.target next.target := by
  have sorted := QuoteDrop.openPatternWellSorted_normal Complete.RhoQuoteDrop.typedPresentation
    (GeneralRuleReceiptSource.primitive_source_sorted fired)
  exact Complete.QuoteDropCoherence.firingsNormalize Complete.RhoPresented.canonical
    Complete.RhoPresented.descentAdmissible (fun _ member => absurd member List.not_mem_nil)
    (show CanonicalBags.LawTypeOk _ _ proc from trivial) Complete.RhoQuoteDrop.distinct
    Complete.RhoQuoteDrop.typedPresentation Complete.RhoQuoteDrop.quoteOpaque Complete.RhoQuoteDrop.fires
    source receipt sorted fired

theorem normalizer : Complete.Coherence.Normalizer
    (Complete.QuoteDropCoherence.ModelEquation plan [] proc presentation) form where
  sound source := Relation.EqvGen.mono (fun _ _ move => .inr move) _ _
    ((Complete.QuoteDropCoherence.normalizer Complete.RhoPresented.extrusions_eq
      Complete.RhoQuoteDrop.distinct).sound source)
  canonical left right := by
    rintro (equation | move)
    · exact False.elim (Complete.RhoPresented.noEquations [] proc left right equation)
    · exact (Complete.QuoteDropCoherence.normalizer Complete.RhoPresented.extrusions_eq
        Complete.RhoQuoteDrop.distinct).canonical left right move

theorem certificate : Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate
    RhoPrimitive.raw (Complete.QuoteDropCoherence.ModelEquation plan [] proc presentation) form where
  normalizer := normalizer
  raw_equations := by
    intro first second equal
    change first = second at equal
    subst second
    exact .refl _
  normalize_step := by
    rintro source target ⟨receipt, fired, rfl⟩
    obtain ⟨next, valid, related⟩ := primitive_form fired
    exact ⟨next.target, ⟨next, valid, rfl⟩, related⟩

theorem normal_admitted (source : Pattern) (typed : RhoPrimitive.Source source) :
    RhoPrimitive.Source (form source) := by
  apply (GeneralPlanEnvironment.typing_iff plan [] proc (form source)).mp
  apply Complete.DescentCoherence.lawNormal_sorted Complete.RhoPresented.descentAdmissible
    (fun _ member => absurd member List.not_mem_nil) (show CanonicalBags.LawTypeOk _ _ proc from trivial)
  exact QuoteDrop.openPatternWellSorted_normal Complete.RhoQuoteDrop.typedPresentation
    ((GeneralPlanEnvironment.typing_iff plan [] proc source).mpr typed)

/-- Global typing reflection is false: normalization can erase a malformed
quote/drop pair. Decoding must check the original source. -/
def malformed : Pattern := .apply "NQuote" [.apply "PDrop" [.apply "PZero" []]]

theorem malformed_normalizes : form malformed = .apply "PZero" [] := by
  change CanonicalBags.lawNormal (Complete.Normalized.laws plan)
    (QuoteDrop.normal presentation malformed) = _
  have cancelled : QuoteDrop.normal presentation malformed = .apply "PZero" [] := by decide +kernel
  rw [Complete.RhoPresented.laws_eq, cancelled]
  simp [CanonicalBags.lawNormal, CanonicalBags.canon, CollectionLaws.normalize]

theorem malformed_rejected :
    checkOpenPatternWellSorted GeneralRho.language GeneralRho.snapshot.free [] proc malformed = false := by
  decide +kernel

def fragment : Generation.LanguageFragment := {operational := GeneralRho.Standard.permissions}

def chosen : GeneralExecutionAdmission.Snapshot := Generation.selectedSnapshot GeneralRho.snapshot fragment

def vertex : SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated : Generation.Generated :=
  Generation.generate GeneralRho.snapshot fragment Structural.heytingFragment vertex

theorem generated_snapshot : generated.snapshot = GeneralRho.snapshot := by
  change Generation.selectedSnapshot GeneralRho.snapshot fragment = _
  simp only [Generation.selectedSnapshot, fragment, Generation.unrestricted_signature]

theorem generated_plan : generated.plan = plan := by
  unfold Generation.Generated.plan
  rw [generated_snapshot]
  rfl

def generatedBackend : Backend (Normalized.raw generated [] proc) (Normalized.Source generated [] proc) := by
  unfold Normalized.raw Normalized.Source
  rw [generated_plan, generated_snapshot]
  exact RhoPrimitive.backend

def generatedCursor : Mettapedia.OSLF.NativeTypes.Decision.Machine.CursorBackend
    (Normalized.raw generated [] proc) (Normalized.Source generated [] proc) := by
  unfold Normalized.raw Normalized.Source
  rw [generated_plan, generated_snapshot]
  exact RhoPrimitive.cursor

/-- The observation is the empty parallel process, with wrappers retained. -/
def done : Pattern := .collection .hashBag [] none

def profile : Profile generated [] proc where
  policy := .model fun actual _ _ => Complete.QuoteDropCoherence.LawMove actual.plan presentation
  nf := form
  certificate := by
    change Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate
      (Normalized.raw generated [] proc)
      (Complete.QuoteDropCoherence.ModelEquation generated.plan [] proc presentation) form
    unfold Normalized.raw
    rw [generated_plan]
    exact certificate
  foundation := by rw [generated_plan]; exact GeneralRho.Standard.compilation_complete
  normal_admitted source typed := by
    unfold Normalized.Source at typed ⊢
    rw [generated_snapshot] at typed ⊢
    exact normal_admitted source typed
  base := generatedBackend
  cursor := generatedCursor
  provenance := {
    finiteOrigin _ receipt := receipt
    finite_valid := by
      intro budget source receipt member
      change receipt ∈ RhoPrimitive.frontier budget source at member
      rw [generated_plan]
      exact (RhoPrimitive.receipts_exact source receipt).mp (List.mem_of_mem_take member)
    finite_target _ _ := rfl
    cursorOrigin _ receipt := receipt
    cursor_valid := by
      intro source receipt member
      change GeneralRuleJobs.Receipt at receipt
      change receipt ∈ (Stream.pause fun _ => Stream.ofList (RhoPrimitive.receipts source)).flatten at member
      rw [generated_plan]
      exact (RhoPrimitive.receipts_exact source receipt).mp
        (by simpa only [Stream.flatten, Stream.flatten_ofList] using member)
    cursor_target _ _ := rfl }
  profileChoice := .displayed (SortProfiles.DisplayedGraph.allStar generated.snapshot.language) [] rfl
  observations := [⟨"Done", ⟨3, by decide⟩, fun source => source == done⟩]

/-- The native driver's equations and steps are those of the independently
defined quote-drop model, on the actual compiled rho primitive receipts. -/
theorem system_source : profile.policy.sourceSystem generated [] proc =
    Complete.QuoteDropCoherence.gslt plan [] proc presentation := by
  change Complete.QuoteDropCoherence.gslt generated.plan [] proc presentation = _
  rw [generated_plan]

/-- Every complete physical firing at the committed source is retained,
including matcher choices and completed assignments. No endpoint deduplication
is used to establish this receipt-level coverage. -/
theorem cursor_receipt_exact (source : Pattern) (receipt : GeneralRuleJobs.Receipt) :
    receipt ∈ (profile.engine.cursor.tasks source).flatten ↔
      GeneralOccurrenceSemantics.Primitive plan [] proc (form source) receipt := by
  change receipt ∈ (Stream.ofList (RhoPrimitive.receipts (form source))).flatten ↔ _
  rw [Stream.flatten_ofList]
  exact RhoPrimitive.receipts_exact (form source) receipt

/-- A possibility in the independent quotient model is exactly a completed
primitive receipt at the canonical source with the selected canonical result. -/
theorem possibility_iff_receipt (source selected : Pattern) :
    (∃ target, (Complete.QuoteDropCoherence.gslt plan [] proc presentation).Step source target ∧
      form target = selected) ↔
    ∃ receipt ∈ RhoPrimitive.receipts (form source), form receipt.target = selected := by
  constructor
  · rintro ⟨target, ⟨representative, receipt, before, fired, after⟩, selectedEq⟩
    obtain ⟨next, normalized, related⟩ := primitive_form fired
    have sourceEq := normalizer.eqvGen_eq before
    have targetEq := normalizer.eqvGen_eq after
    have nextEq := normalizer.eqvGen_eq related
    refine ⟨next, (RhoPrimitive.receipts_exact (form source) next).mpr ?_, ?_⟩
    · rw [sourceEq]
      exact normalized
    · exact nextEq.symm.trans (targetEq.trans selectedEq)
  · rintro ⟨receipt, member, selectedEq⟩
    exact ⟨receipt.target, ⟨form source, receipt, normalizer.sound source,
      (RhoPrimitive.receipts_exact (form source) receipt).mp member, .refl _⟩, selectedEq⟩

end Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoProfile
