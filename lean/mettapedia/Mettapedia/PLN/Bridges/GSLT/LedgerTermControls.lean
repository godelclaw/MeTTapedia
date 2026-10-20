import Mettapedia.PLN.Bridges.GSLT.LedgerTermSemantics

/-!
# Checked nested ledger derivations and separating controls

The positive example combines three distinct observations in two checked
revision steps and reads the result. The counterexample supplies a false
external disjointness premise: syntax can check while that premise fails in
the actual observation model. Lower bounds also remain distinct from exact
counts when a later rule requests a strength.
-/

namespace Mettapedia.PLN.Bridges.GSLT.LedgerTermControls

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.Bridges.GSLT.LedgerTermSemantics
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceSpaces

private def world (i : Fin 3) : Bool := decide (i ≠ 1)

def q : Pattern := app "query-input" []
def first : Pattern := app "first-input" []
def second : Pattern := app "second-input" []
def third : Pattern := app "third-input" []
def firstTwo : Pattern := app "revise" [first, second]
def allThree : Pattern := app "revise" [firstTwo, third]

private def atomLedger (p : Pattern) : Finset (Fin 3) :=
  if p = first then {0} else if p = second then {1} else if p = third then {2} else ∅

def model : Model where
  Id := Fin 3
  W := Bool
  world := world
  atomQuery _ := id
  atomLedger := atomLedger
  atomSummary p := ledgerEvidence world id (atomLedger p)
  atomValue _ := (∅, ∅)
  priorStrength := 1
  priorStrength_pos := zero_lt_one

def context : List Pattern :=
  [observationCounts q first, observationCounts q second, observationCounts q third,
    ledgerHolds (app "disjoint" [first, second]),
    ledgerHolds (app "disjoint" [firstTwo, third])]

def firstRevision : RawOpenProof :=
  .node ⟨⟨"revise"⟩, [q, first, second]⟩ [.premise 0, .premise 1, .premise 3]

def secondRevision : RawOpenProof :=
  .node ⟨⟨"revise"⟩, [q, firstTwo, third]⟩ [firstRevision, .premise 2, .premise 4]

def readoutProof : RawOpenProof :=
  .node ⟨⟨"read-strength"⟩, [q, allThree]⟩ [secondRevision]

theorem nested_revision_readout_checks :
    checkOpenRaw ledgerValidated context (countReadout q (app "strength" [allThree]))
      readoutProof = true := by decide +kernel

theorem context_holds : ∀ premise ∈ context, model.holds premise := by
  dsimp only [model]
  norm_num [context, Model.holds, observationCounts, ledgerHolds, app, Model.query,
    Model.summary, Model.ledger, model, q, firstTwo, atomLedger, first, second, third,
    Finset.disjoint_left]
  decide +kernel

/-- The accepted proof establishes a semantic readout from checked true
premises, including the recursively interpreted intermediate ledger. -/
theorem checked_nested_readout : model.holds (countReadout q (app "strength" [allThree])) :=
  checked_proof_sound model context _ readoutProof nested_revision_readout_checks context_holds

theorem nested_count_profile : model.summary allThree = ⟨2, 1⟩ := by
  dsimp only [model]
  apply Evidence.ext <;>
    norm_num [allThree, firstTwo, Model.summary, app, model, atomLedger, first, second, third,
      ledgerEvidence, world, sampleEvidence, Evidence.positive, Evidence.negative] <;> decide +kernel

theorem nested_strength : realStrength (model.summary allThree) = (2 / 3 : ℝ) := by
  rw [nested_count_profile]
  norm_num [realStrength, Evidence.strength, Evidence.total, Evidence.map,
    Evidence.map_apply_pos, Evidence.map_apply_neg]

def falseContractContext : List Pattern :=
  [observationCounts q first, ledgerHolds (app "disjoint" [first, first])]

def duplicateRevision : RawOpenProof :=
  .node ⟨⟨"revise"⟩, [q, first, first]⟩ [.premise 0, .premise 0, .premise 1]

/-- The checker treats an external contract as a premise, not as a fact it
can establish by inspecting the observation source. -/
theorem false_external_contract_checks_structurally :
    checkOpenRaw ledgerValidated falseContractContext
      (observationCounts q (app "revise" [first, first])) duplicateRevision = true := by
  decide +kernel

theorem duplicate_contract_is_false :
    ¬ model.holds (ledgerHolds (app "disjoint" [first, first])) := by
  dsimp only [model]
  norm_num [Model.holds, ledgerHolds, app, Model.ledger, atomLedger, first]

theorem duplicate_count_conclusion_is_false :
    ¬ model.holds (observationCounts q (app "revise" [first, first])) := by
  simp [Model.holds, observationCounts, app, Model.summary, Model.ledger,
    model, q, atomLedger, first, ledgerEvidence, world,
    sampleEvidence, Evidence.positive, Evidence.negative, Evidence.ext_iff]

def lowerBoundRevision : RawOpenProof :=
  .node ⟨⟨"revise-unknown-overlap"⟩, [q, first, third]⟩ [.premise 0, .premise 2]

def readLowerBound : RawOpenProof :=
  .node ⟨⟨"read-strength"⟩, [q, app "lowerMerge" [first, third]]⟩ [lowerBoundRevision]

theorem lower_bound_cannot_feed_exact_readout :
    checkOpenRaw ledgerValidated context
      (countReadout q (app "strength" [app "lowerMerge" [first, third]])) readLowerBound =
        false := by decide +kernel

end Mettapedia.PLN.Bridges.GSLT.LedgerTermControls
