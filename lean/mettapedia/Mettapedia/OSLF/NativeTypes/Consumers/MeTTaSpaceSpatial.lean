import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace
import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel
import Mettapedia.OSLF.NativeTypes.Instances.SpatialBag

/-!
# Source-derived space contracts as shared spatial formulas

The completed query observation is PeTTa's actual finite answer list. The
occurrence and complete-packet questions are formulas of the shared checker:
they use singleton and empty bag leaves with recursive separating conjunction.
Their meanings are proved equivalent to Zero's existing source-derived
occurrence judgment and the existing exact packet contract.

The observation does not reconstruct provenance from counts, authorize a
rejected article, or identify Zero evaluation with PeTTa's selected-rule table.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial

open Mettapedia.Languages.MeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

open Mettapedia.OSLF.NativeTypes.Decision.Spatial

def answers (space : PeTTa.PeTTaSpace) (pattern template : Pattern) : List Pattern :=
  space.spaceMatch pattern template

/-- Ordinal zero asks for one copy; ordinal one asks for two copies. -/
def occurrenceFormula (result : Pattern) (occurrence : Nat) : Core.Formula BagModel.Leaf :=
  BagModel.atLeast result (occurrence + 1)

def packetFormula (expected : List Pattern) : Core.Formula BagModel.Leaf := BagModel.packet expected

theorem occurrence_meaning (space : PeTTa.PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) :
    BagModel.holds (occurrenceFormula result occurrence) (answers space pattern template) ↔
      MeTTaSpace.QueryMember space pattern template result occurrence := by
  rw [occurrenceFormula, BagModel.atLeast_iff, MeTTaSpace.queryMember_iff]
  exact Nat.succ_le_iff

theorem packet_meaning (space : PeTTa.PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) :
    BagModel.holds (packetFormula expected) (answers space pattern template) ↔
      MeTTaSpace.checkPacket space pattern template expected = true := by
  rw [packetFormula, BagModel.packet_iff]
  simp only [MeTTaSpace.checkPacket, decide_eq_true_eq, answers]
  exact eq_comm

/-- The complete packet formula accounts for every source answer occurrence
in both directions; it is not just an all-submitted-values-valid test. -/
theorem packet_source_coverage (space : PeTTa.PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) :
    BagModel.holds (packetFormula expected) (answers space pattern template) ↔
      ∀ result occurrence, occurrence < expected.count result ↔
        MeTTaSpace.QueryMember space pattern template result occurrence :=
  (packet_meaning space pattern template expected).trans
    (MeTTaSpace.checkPacket_exact space pattern template expected)

def occurrenceNativeType (result : Pattern) (occurrence : Nat) : GSLTNativeType BagModel.system :=
  Core.nativeType BagModel.tests (occurrenceFormula result occurrence) BagModel.spatial

def packetNativeType (expected : List Pattern) : GSLTNativeType BagModel.system :=
  Core.nativeType BagModel.tests (packetFormula expected) BagModel.spatial

theorem occurrence_native_source (space : PeTTa.PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) :
    (gsltOSLF BagModel.system).satisfies (answers space pattern template)
      (occurrenceNativeType result occurrence).pred ↔
      MeTTaSpace.QueryMember space pattern template result occurrence :=
  occurrence_meaning space pattern template result occurrence

theorem packet_native_source (space : PeTTa.PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) :
    (gsltOSLF BagModel.system).satisfies (answers space pattern template)
      (packetNativeType expected).pred ↔
      ∀ result occurrence, occurrence < expected.count result ↔
        MeTTaSpace.QueryMember space pattern template result occurrence :=
  packet_source_coverage space pattern template expected

/-- The existing shared checker decides every finite bag formula at its
proved work bound. This theorem introduces no second decision procedure. -/
theorem shared_check_exact (formula : Core.Formula BagModel.Leaf) (items : List Pattern)
    (budget : Nat) (enough : Core.workBound BagModel.backend BagModel.tests formula items ≤ budget) :
    (Core.check BagModel.backend BagModel.tests formula items budget).answer = some true ↔
      BagModel.holds formula items := by
  have complete := Core.checked_complete BagModel.backend BagModel.tests formula items trivial budget enough
  constructor
  · exact Core.checked_positive BagModel.backend BagModel.tests formula items budget
  · intro holds
    generalize Core.check BagModel.backend BagModel.tests formula items budget = outcome at complete ⊢
    cases outcome with
    | proved proof => rfl
    | refuted falsehood => exact False.elim (falsehood holds)
    | unknown => simp [Core.Outcome.Decided, Core.Outcome.answer] at complete

theorem shared_occurrence_exact (space : PeTTa.PeTTaSpace)
    (pattern template result : Pattern) (occurrence budget : Nat)
    (enough : Core.workBound BagModel.backend BagModel.tests (occurrenceFormula result occurrence)
      (answers space pattern template) ≤ budget) :
    (Core.check BagModel.backend BagModel.tests (occurrenceFormula result occurrence)
      (answers space pattern template) budget).answer = some true ↔
      MeTTaSpace.QueryMember space pattern template result occurrence :=
  (shared_check_exact _ _ _ enough).trans (occurrence_meaning _ _ _ _ _)

theorem shared_packet_exact (space : PeTTa.PeTTaSpace)
    (pattern template : Pattern) (expected : List Pattern) (budget : Nat)
    (enough : Core.workBound BagModel.backend BagModel.tests (packetFormula expected)
      (answers space pattern template) ≤ budget) :
    (Core.check BagModel.backend BagModel.tests (packetFormula expected)
      (answers space pattern template) budget).answer = some true ↔
      MeTTaSpace.checkPacket space pattern template expected = true :=
  (shared_check_exact _ _ _ enough).trans (packet_meaning _ _ _ _)

theorem public_packet_meaning (space : PeTTa.PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning Instances.SpatialBag.driver
      (packetFormula expected) (BagModel.encode (answers space pattern template)) ↔
      ∀ result occurrence, occurrence < expected.count result ↔
        MeTTaSpace.QueryMember space pattern template result occurrence :=
  (Instances.SpatialBag.meaning_at_bag _ _).trans (packet_source_coverage _ _ _ _)

theorem public_occurrence_meaning (space : PeTTa.PeTTaSpace)
    (pattern template result : Pattern) (occurrence : Nat) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning Instances.SpatialBag.driver
      (occurrenceFormula result occurrence) (BagModel.encode (answers space pattern template)) ↔
      MeTTaSpace.QueryMember space pattern template result occurrence :=
  (Instances.SpatialBag.meaning_at_bag _ _).trans (occurrence_meaning _ _ _ _ _)

/-- Any successful public packet search certifies complete source occurrence
coverage; the runtime supplies the same soundness rule used by other profiles. -/
theorem public_packet_positive (space : PeTTa.PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) (budget : Nat)
    (accepted : (Runtime.search Instances.SpatialBag.driver Instances.SpatialBag.engine
      (packetFormula expected) (BagModel.encode (answers space pattern template)) budget).readout =
        .judgment (.decided true)) :
    ∀ result occurrence, occurrence < expected.count result ↔
      MeTTaSpace.QueryMember space pattern template result occurrence :=
  (public_packet_meaning space pattern template expected).mp (Runtime.positive _ accepted)

def decodedAnswers (space : PeTTa.PeTTaSpace) (pattern template : Pattern) :
    Instances.SpatialBag.driver.Decoded (BagModel.encode (answers space pattern template)) :=
  ⟨answers space pattern template, trivial, rfl⟩

theorem public_packet_complete (space : PeTTa.PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) :
    ∃ answer, (Runtime.search Instances.SpatialBag.driver Instances.SpatialBag.engine
      (packetFormula expected) (BagModel.encode (answers space pattern template))
      (Runtime.decisionBound Instances.SpatialBag.driver Instances.SpatialBag.engine
        (packetFormula expected) (decodedAnswers space pattern template))).readout =
        .judgment (.decided answer) := by
  exact Runtime.check_complete Instances.SpatialBag.driver Instances.SpatialBag.engine
    (packetFormula expected) (decodedAnswers space pattern template)
    (Instances.SpatialBag.packet_formed expected) Instances.SpatialBag.admitted_profile _ (Nat.le_refl _)

end Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial
