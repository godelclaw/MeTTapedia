import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialExecution
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial

/-!
# Source meaning of the emitted spatial checker

The target strategy and the public native checker interpret the same shared
formula. For a completed PeTTa space query, its packet formula accounts for
every specified answer occurrence. The source answer list is supplied by the
source semantics; this module does not certify arbitrary runtime matchers or
untrusted serialized cursors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes
open Decision.Spatial

theorem completed_public_positive (before : Effects.State) (session : Execution.Session)
    (completed : ReadCompletes before session (some true)) :
    Runtime.Description.Meaning Instances.SpatialBag.driver session.formula
      (BagModel.encode session.bag) :=
  (Instances.SpatialBag.meaning_at_bag _ _).mpr (completed_positive before session completed)

theorem completed_public_negative (before : Effects.State) (session : Execution.Session)
    (completed : ReadCompletes before session (some false)) :
    ¬ Runtime.Description.Meaning Instances.SpatialBag.driver session.formula
      (BagModel.encode session.bag) := by
  intro holds
  exact completed_negative before session completed
    ((Instances.SpatialBag.meaning_at_bag _ _).mp holds)

theorem eventually_public_positive_iff (before : Effects.State) (session : Execution.Session) :
    (∃ work, ReadCompletes before (session.resume work) (some true)) ↔
      Runtime.Description.Meaning Instances.SpatialBag.driver session.formula
        (BagModel.encode session.bag) :=
  (eventually_positive_iff before session).trans (Instances.SpatialBag.meaning_at_bag _ _).symm

private theorem packet_admitted (expected : List Pattern) :
    Execution.admitted (BagModel.packet expected) = true := by
  induction expected with
  | nil => rfl
  | cons value rest ih => simpa [BagModel.packet, Execution.admitted] using ih

private theorem atLeast_admitted (value : Pattern) (count : Nat) :
    Execution.admitted (BagModel.atLeast value count) = true := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [BagModel.atLeast, Execution.admitted] using ih

def packetSession (space : PeTTaSpace) (pattern template : Pattern)
    (expected : List Pattern) : Execution.Session :=
  .begin (Consumers.MeTTaSpaceSpatial.packetFormula expected)
    (Consumers.MeTTaSpaceSpatial.answers space pattern template) (packet_admitted expected)

def occurrenceSession (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) : Execution.Session :=
  .begin (Consumers.MeTTaSpaceSpatial.occurrenceFormula result occurrence)
    (Consumers.MeTTaSpaceSpatial.answers space pattern template) (atLeast_admitted result _)

/-- Eventual successful target execution is equivalent to complete source
occurrence coverage, including multiplicities of equal answers. -/
theorem emitted_packet_source_iff (before : Effects.State) (space : PeTTaSpace)
    (pattern template : Pattern) (expected : List Pattern) :
    (∃ work, ReadCompletes before ((packetSession space pattern template expected).resume work)
      (some true)) ↔
      ∀ result occurrence, occurrence < expected.count result ↔
        Consumers.MeTTaSpace.QueryMember space pattern template result occurrence :=
  (eventually_positive_iff before (packetSession space pattern template expected)).trans
    (Consumers.MeTTaSpaceSpatial.packet_source_coverage space pattern template expected)

/-- A target refutation concerns the submitted packet's exactness, not the
nonderivability of its individual values. Exhausted work yields no refutation. -/
theorem emitted_packet_refuted_iff (before : Effects.State) (space : PeTTaSpace)
    (pattern template : Pattern) (expected : List Pattern) :
    (∃ work, ReadCompletes before ((packetSession space pattern template expected).resume work)
      (some false)) ↔
      ¬ (∀ result occurrence, occurrence < expected.count result ↔
        Consumers.MeTTaSpace.QueryMember space pattern template result occurrence) :=
  (eventually_negative_iff before (packetSession space pattern template expected)).trans
    (not_congr (Consumers.MeTTaSpaceSpatial.packet_source_coverage space pattern template expected))

theorem emitted_occurrence_source_iff (before : Effects.State) (space : PeTTaSpace)
    (pattern template result : Pattern) (occurrence : Nat) :
    (∃ work, ReadCompletes before ((occurrenceSession space pattern template result occurrence).resume work)
      (some true)) ↔ Consumers.MeTTaSpace.QueryMember space pattern template result occurrence :=
  (eventually_positive_iff before (occurrenceSession space pattern template result occurrence)).trans
    (Consumers.MeTTaSpaceSpatial.occurrence_meaning space pattern template result occurrence)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime
