import Mettapedia.Logic.WorldModel.PartialObservationStore
import Mettapedia.NARS.Bridges.PLN.InformationAdjunction
import Mettapedia.NARS.Evidence.EvidenceScopeIncoherence

/-!
# Path-scoped NARS and PLN world-model observations

The shared store regime retains a statement together with its evidence path.
Interpreting a valid NARS truth value as a PLN belief preserves chronological
store revision. The established readback preserves confidence and, at positive
confidence, frequency. It does not identify NARS inference rules with PLN rules
or assign every path one global statement probability.
-/

namespace Mettapedia.NARS.Bridges.PLN.ScopedWorldModel

open Mettapedia.Logic.WorldModel
open Mettapedia.Logic.WorldModel.PartialObservationStore
open Mettapedia.NARS.Bridges.PLN.InformationAdjunction
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence

variable {Statement Source : Type} [DecidableEq Source]

abbrev ScopedQuery (Statement Source : Type) [DecidableEq Source] :=
  Statement × EvidencePath Statement Source

abbrev NARSStore (Statement Source : Type) [DecidableEq Source] :=
  Store (ScopedQuery Statement Source) NARSTruthValue

abbrev PLNStore (Statement Source : Type) [DecidableEq Source] :=
  Store (ScopedQuery Statement Source) PLNBelief

/-- The path and its source scope remain in the query key. The value
interpretation uses the existing count/prior construction, not a new formula. -/
noncomputable def interpretation :
    RevisionMap (NARSStore Statement Source) (ScopedQuery Statement Source) (Option NARSTruthValue)
      (PLNStore Statement Source) (ScopedQuery Statement Source) (Option PLNBelief) := map L

theorem interpretations_compose_with_updates
    (updates : List (NARSStore Statement Source)) (initial : NARSStore Statement Source) :
    interpretation.state (updates.foldl revise initial) =
      (updates.map interpretation.state).foldl revise (interpretation.state initial) :=
  interpretation.foldl_revise updates initial

/-- Confidence readback needs no positive-support guard. The guard concerns
the frequency coordinate alone. -/
theorem readback_confidence (store : NARSStore Statement Source)
    (query : ScopedQuery Statement Source) (truth : NARSTruthValue)
    (found : store query = some truth) :
    ((interpretation.state store query).map U).map (fun value => value.c) = some truth.c := by
  change ((store query).map L |>.map U |>.map (fun value => value.c)) = _
  rw [found]
  simp only [Option.map_some, U_L_conf_round_trip]

/-- Readback is coordinate-exact where the existing NARS/evidence
correspondence is faithful. Positive confidence is essential for frequency. -/
theorem readback_coordinates (store : NARSStore Statement Source)
    (query : ScopedQuery Statement Source) (truth : NARSTruthValue)
    (found : store query = some truth) (supported : 0 < truth.c) :
    ((interpretation.state store query).map U).map (fun value => (value.f, value.c)) =
      some (truth.f, truth.c) := by
  change ((store query).map L |>.map U |>.map (fun value => (value.f, value.c))) = _
  rw [found]
  simp only [Option.map_some, U_L_freq_round_trip truth supported, U_L_conf_round_trip]

namespace Controls

noncomputable def zeroConfidenceFirst : NARSTruthValue where
  f := 0
  c := 0
  f_nonneg := le_rfl
  f_le_one := zero_le_one
  c_nonneg := le_rfl
  c_lt_one := zero_lt_one

noncomputable def zeroConfidenceSecond : NARSTruthValue where
  f := 1
  c := 0
  f_nonneg := zero_le_one
  f_le_one := le_rfl
  c_nonneg := le_rfl
  c_lt_one := zero_lt_one

/-- The frequency guard is substantive: different unsupported frequencies
have exactly the same zero-count PLN image. -/
theorem zero_confidence_frequency_not_preserved :
    zeroConfidenceFirst.f ≠ zeroConfidenceSecond.f ∧
      L zeroConfidenceFirst = L zeroConfidenceSecond := by
  constructor
  · norm_num [zeroConfidenceFirst, zeroConfidenceSecond]
  · simp [L, zeroConfidenceFirst, zeroConfidenceSecond, Mettapedia.NARS.TruthFunctions.c2w]

/-- Path-sensitive observations cannot factor through the statement alone
when the existing direct and deductive paths disagree. -/
theorem path_frequencies_do_not_factor_through_statement :
    ¬ ∃ frequency : PathWitness.Statement → ℝ,
      frequency PathWitness.directBelief.statement = PathWitness.directBelief.truth.f ∧
      frequency PathWitness.deductiveBelief.statement = PathWitness.deductiveBelief.truth.f := by
  rintro ⟨frequency, direct, deductive⟩
  apply PathWitness.direct_frequency_ne_deductive_frequency
  rw [← direct, ← deductive, PathWitness.same_statement]

end Controls

end Mettapedia.NARS.Bridges.PLN.ScopedWorldModel
