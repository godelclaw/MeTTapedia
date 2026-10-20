import Mettapedia.ProbabilityTheory.MassSemantics
import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# Binary mass readouts of a query-mass semantics

The binary carrier stores query mass and complementary mass here. Its total
is a normalization mass, not a calibrated count of observations. The strength
readout agrees exactly with the independent normalized query.
-/

namespace Mettapedia.ProbabilityTheory.MassSemantics

open Mettapedia.PLN.Evidence
open scoped ENNReal

variable {Query : Type*} (source : MassSemantics Query)

noncomputable def binaryMass (query : Query) : BinaryEvidence :=
  ⟨source.queryMass query, source.totalMass - source.queryMass query⟩

theorem binaryMass_total (query : Query) : (source.binaryMass query).total = source.totalMass := by
  unfold binaryMass BinaryEvidence.total
  rw [add_comm]
  exact tsub_add_cancel_of_le (source.queryMass_le_total query)

theorem toStrength_binaryMass (query : Query) :
    BinaryEvidence.toStrength (source.binaryMass query) = source.queryProb query := by
  unfold BinaryEvidence.toStrength queryProb
  rw [source.binaryMass_total query]
  split_ifs <;> simp [binaryMass]

end Mettapedia.ProbabilityTheory.MassSemantics
