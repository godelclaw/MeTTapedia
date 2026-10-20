import Mettapedia.NARS.Bridges.PLN.FiniteEvidenceChart
import Mettapedia.PLN.Evidence.CountRegimes
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Identified observation counts interpreted through NARS revision

Natural sample counts have an exact finite NARS readout. Interpreting that
readout back recovers both count coordinates, and core revision adds them.
For the existing identified-observation model, this agrees with source union
exactly when the source ledgers are disjoint.

This is an observational interpretation. It does not identify an arbitrary
NARS deduction path with direct observations of its conclusion. Tensor fusion
and paired-sample multiplication retain their distinct meanings.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.PLN.LedgerCountInterpretation

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.Evidence.CountRegimes
open Mettapedia.NARS.Bridges.PLN.InformationAdjunction
open Mettapedia.NARS.Bridges.PLN.RevisionWorldModel
open Mettapedia.NARS.Bridges.PLN.FiniteEvidenceChart

/-- The existing finite-evidence readout. A uniform context is selected but
ignored by `U`; confidence uses its fixed unit evidence scale. -/
noncomputable def fromCounts (counts : Evidence ℕ) : NARSTruthValue :=
  U ⟨sampleEmbedding counts, Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform⟩

theorem fromCounts_exact (counts : Evidence ℕ) :
    toCounts (fromCounts counts) = sampleEmbedding counts :=
  counts_round_trip _ (sampleEmbedding_finite counts)

theorem core_revision_counts (first second : Evidence ℕ) :
    toCounts (coreState (fromCounts first) (fromCounts second)) = sampleEmbedding (first + second) := by
  rw [toCounts_coreState, fromCounts_exact, fromCounts_exact, map_add]

variable {Id W : Type*} [DecidableEq Id]

/-- The NARS count interpretation and the PLN source-ledger interpretation
commute exactly under the established source-disjointness contract. -/
theorem ledger_revision_exact_iff_disjoint (world : Id → W) (query : W → Bool)
    (first second : Finset Id) :
    toCounts (coreState (fromCounts (ledgerEvidence world query first))
      (fromCounts (ledgerEvidence world query second))) =
        sampleEmbedding (ledgerEvidence world query (first ∪ second)) ↔ Disjoint first second := by
  rw [core_revision_counts, sampleEmbedding_injective.eq_iff,
    additive_revision_exact_iff_disjoint]

/-- Inclusion–exclusion remains exact when the ledgers overlap. The
intersection is retained as its own observation body. -/
theorem ledger_revision_counts_overlap (world : Id → W) (query : W → Bool)
    (first second : Finset Id) :
    toCounts (coreState (fromCounts (ledgerEvidence world query first))
      (fromCounts (ledgerEvidence world query second))) =
        sampleEmbedding (ledgerEvidence world query (first ∪ second)) +
          sampleEmbedding (ledgerEvidence world query (first ∩ second)) := by
  rw [core_revision_counts, revision_counts_overlap_twice, map_add]

namespace Controls

private def observations (source : Fin 3) : Bool := source ≠ 2

/-- Two nonempty disjoint bodies give the exact same merged counts through
the NARS core and the identified-observation union model. -/
theorem disjoint_sources_commute :
    toCounts (coreState (fromCounts (ledgerEvidence observations id {0}))
      (fromCounts (ledgerEvidence observations id {1, 2}))) =
        sampleEmbedding (ledgerEvidence observations id ({0} ∪ {1, 2})) := by
  apply (ledger_revision_exact_iff_disjoint observations id {0} {1, 2}).mpr
  decide +kernel

/-- Equal numerical frequencies do not authorize reusing the same source. -/
theorem repeated_source_counts_twice :
    toCounts (coreState (fromCounts (ledgerEvidence observations id {0}))
      (fromCounts (ledgerEvidence observations id {0}))) ≠
        sampleEmbedding (ledgerEvidence observations id ({0} ∪ {0})) := by
  intro exact
  have impossible := (ledger_revision_exact_iff_disjoint observations id {0} {0}).mp exact
  exact (by decide +kernel : ¬ Disjoint ({0} : Finset (Fin 3)) {0}) impossible

end Controls

end Mettapedia.NARS.Bridges.PLN.LedgerCountInterpretation
