import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.RootReceipts
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking

/-!
# Generated contextual native observations of general root receipts

The observation calls the existing focus-response checker on the complete
payload. It fixes the generated focus, shared indices, rely tuple and
dependent target. The root occurrence must retain the precise ambient
context and program type. Transport through a declared equation/collection
profile remains an explicit local obligation; no invariance of arbitrary
native continuations is inferred from equality of their result patterns.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.NativeResponses

open Mettapedia.OSLF.MeTTaIL Syntax GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open NativeBindingEventAction (bound)
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open FocusMeaning FiniteFocusChecking

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

abbrev plan (installed : Joined.Installed) := BindingPipeline.plan installed.indexed.operational.generated

abbrev expected (installed : Joined.Installed) (index : installed.Index) : TypeExpr :=
  .base (installed.programSort index)

theorem root_enabled (installed : Joined.Installed) : (plan installed).permissions.sites.enabled = true := by
  simp only [plan, BindingPipeline.plan, StructuralDescent.Plan.permissions_preserved, Generated.plan]
  change installed.indexed.operational.generated.languageFragment.operational.sites.enabled = true
  rw [installed.indexed.operational.rootRules]
  rfl

/-- The test checks the entire root site's context and type, not merely an
empty printed address or the equality of a result. -/
def accepts (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (receipt : GeneralRuleJobs.Receipt) : Bool :=
  decide (receipt.job.site = SiteData.here (bound ambient) (expected installed index) receipt.job.site.focus) &&
    (checkResponse parameters.meaning focus values receipt.job.site.focus (RootReceipts.payload receipt)).isSome

theorem accepts_root_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (root : receipt.job.site = SiteData.here (bound ambient) (expected installed index) source) :
    accepts parameters focus values receipt = true ↔
      SourceResponse parameters.meaning focus values source (RootReceipts.payload receipt) := by
  simp only [accepts, root, SiteData.here, decide_true, Bool.true_and]
  exact checkResponse_exact parameters.meaning focus values source (RootReceipts.payload receipt)

theorem accepts_pack_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern) (value : Payload) :
    accepts parameters focus values
        (RootReceipts.pack (installed.indexed.schema index).declaration
          (bound ambient) (expected installed index) source value) = true ↔
      SourceResponse parameters.meaning focus values source value := by
  simpa only [RootReceipts.payload_pack] using accepts_root_exact parameters focus values
    (receipt := RootReceipts.pack (installed.indexed.schema index).declaration
      (bound ambient) (expected installed index) source value) rfl

/-- A selected native source response constructs a licensed general
occurrence with precisely its original payload and authored declaration. -/
theorem source_response_pack_valid (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) {source : Pattern} {value : Payload}
    (response : SourceResponse parameters.meaning focus values source value) :
    (RootReceipts.pack (installed.indexed.schema index).declaration
      (bound ambient) (expected installed index) source value).Valid
        (plan installed) (bound ambient) (expected installed index) source := by
  apply RootReceipts.pack_valid _ (root_enabled installed) response.1
  have declared := (installed.indexed.schema index).declared
  rw [← response.2.1] at declared
  exact declared

theorem source_response_iff_checked_occurrence (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern) (value : Payload) :
    SourceResponse parameters.meaning focus values source value ↔
      let receipt := RootReceipts.pack (installed.indexed.schema index).declaration
        (bound ambient) (expected installed index) source value
      receipt.Valid (plan installed) (bound ambient) (expected installed index) source ∧
        accepts parameters focus values receipt = true := by
  constructor
  · intro response
    exact ⟨source_response_pack_valid parameters focus values response,
      (accepts_pack_exact parameters focus values source value).mpr response⟩
  · intro checked
    exact (accepts_pack_exact parameters focus values source value).mp checked.2

/-- Local law transport of a generated native observation. This is a
receipt-sensitive obligation: selected origins, focus, indices, rely values
and dependent assignment/target tests must all survive the move. -/
def LocalTransport (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) : Prop :=
  ∀ first second, Relation.SymmGen (CanonicalBags.StandardStep
      (Complete.Normalized.laws (plan installed)) (Complete.Normalized.extrusions (plan installed))) first second →
    ∀ receipt, GeneralOccurrenceSemantics.Primitive
      (plan installed) (bound ambient) (expected installed index) first receipt →
      ∃ transported, GeneralOccurrenceSemantics.Primitive
        (plan installed) (bound ambient) (expected installed index) second transported ∧
        accepts parameters focus values receipt = accepts parameters focus values transported

def request (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  ⟨plan installed, bound ambient, expected installed index, source⟩

def receiptTest (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern)
    (transport : LocalTransport parameters focus values) : ReceiptTest (request (installed := installed)
      (index := index) (ambient := ambient) source) :=
  ⟨accepts parameters focus values, transport⟩

/-- Recover the independent native source response from a valid actual
occurrence; the observation's root-site check recovers the enclosing source. -/
theorem accepted_occurrence_source (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (plan installed) (bound ambient) (expected installed index) source)
    (accepted : accepts parameters focus values receipt = true) :
    SourceResponse parameters.meaning focus values source (RootReceipts.payload receipt) := by
  have root : receipt.job.site = SiteData.here (bound ambient) (expected installed index) receipt.job.site.focus :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).1
  have same := valid.1.2.source_eq
  rw [root] at same
  change receipt.job.site.focus = source at same
  have root' : receipt.job.site = SiteData.here (bound ambient) (expected installed index) source := by
    simpa only [same] using root
  exact (accepts_root_exact parameters focus values root').mp accepted

/-- The compared native classifier is explicitly saturated at its source.
This does not identify the old literal-source membership judgment with its
quotient interpretation without a separate source-class coverage theorem. -/
theorem receipt_meaning_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern)
    (transport : LocalTransport parameters focus values) :
    (receiptTest parameters focus values source transport).Meaning ↔
      ∃ representative value,
        Complete.Presented.ModelEquiv (plan installed) (bound ambient) (expected installed index)
          (request (installed := installed) (index := index) (ambient := ambient) source).root representative ∧
        SourceResponse parameters.meaning focus values representative value := by
  constructor
  · rintro ⟨representative, receipt, converted, fires, accepted⟩
    exact ⟨representative, RootReceipts.payload receipt, converted,
      accepted_occurrence_source parameters focus values fires accepted⟩
  · rintro ⟨representative, value, converted, response⟩
    exact ⟨representative,
      RootReceipts.pack (installed.indexed.schema index).declaration
        (bound ambient) (expected installed index) representative value,
      converted, source_response_pack_valid parameters focus values response,
      (accepts_pack_exact parameters focus values representative value).mpr response⟩

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.NativeResponses
