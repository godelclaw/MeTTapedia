import Mettapedia.NARS.Bridges.PLN.RevisionSemantics
import Mettapedia.NARS.Bridges.PLN.InformationAdjunction
import Mettapedia.Logic.WorldModel.Observation

/-!
# Core NARS revision as a general world model

Full valid NARS values form a general revision model. Interpreting them as
binary counts preserves empty state and every core revision. The count model
is additive, but the full NARS model does not have a left identity: revision
resets unsupported frequencies when both confidences are zero.

This is why the general world-model interface is useful before imposing
monoidal or additive laws. The count interpretation forgets unsupported
frequency distinctions; it does not identify the two complete state spaces.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.PLN.RevisionWorldModel

open Mettapedia.Logic.WorldModel
open Mettapedia.NARS.TruthFunctions
open Mettapedia.NARS.Bridges.PLN.InformationAdjunction
open Mettapedia.NARS.Bridges.PLN.RevisionSemantics
open Mettapedia.PLN.Evidence

noncomputable def emptyState : NARSTruthValue := ⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_lt_one⟩

/-- The actual evidence-additive core, with its validity proof reused. -/
noncomputable def coreState (first second : NARSTruthValue) : NARSTruthValue :=
  let valid := core_valid first.toTV second.toTV first.isProbTV second.isProbTV
  { f := (truthRevisionCore first.toTV second.toTV).f
    c := (truthRevisionCore first.toTV second.toTV).c
    f_nonneg := valid.f_nonneg
    f_le_one := valid.f_le_one
    c_nonneg := valid.c_nonneg
    c_lt_one := valid.c_lt_one }

@[instance_reducible] noncomputable def sourceModel :
    WorldModel NARSTruthValue Unit NARSTruthValue where
  revise := coreState
  empty := emptyState
  extract state _ := state

@[instance_reducible] noncomputable def countModel :
    MonoidalWorldModel BinaryEvidence Unit BinaryEvidence where
  revise := (· + ·)
  empty := 0
  extract state _ := state
  revise_assoc := add_assoc
  revise_empty_left := zero_add
  revise_empty_right := add_zero

/-- The existing unit-prior evidence interpretation. -/
noncomputable def toCounts (state : NARSTruthValue) : BinaryEvidence :=
  EvidenceTranslation.TV.toEvidence state.toTV

theorem toCounts_eq_existing_embedding (state : NARSTruthValue) :
    toCounts state = (L state).evidence := rfl

theorem toCounts_coreState (first second : NARSTruthValue) :
    toCounts (coreState first second) = toCounts first + toCounts second :=
  core_counts first.toTV second.toTV first.isProbTV second.isProbTV

/-- An exact revision map, with a potentially information-losing value map.
The source retains the complete truth value; the target reads binary counts. -/
noncomputable def interpretation :
    @RevisionMap NARSTruthValue Unit NARSTruthValue BinaryEvidence Unit BinaryEvidence
      sourceModel countModel.toWorldModel := by
  letI := sourceModel
  letI := countModel
  exact {
    state := toCounts
    query := id
    value := toCounts
    observe _ _ := rfl
    empty := by
      change toCounts emptyState = (0 : BinaryEvidence)
      apply BinaryEvidence.ext' <;>
        norm_num [toCounts, emptyState, NARSTruthValue.toTV,
          EvidenceTranslation.TV.toEvidence, c2w, BinaryEvidence.zero]
    revise := toCounts_coreState }

/-- Every chronological sequence of actual source revisions is transported
into the corresponding count additions. -/
theorem chronological_revisions (updates : List NARSTruthValue) (initial : NARSTruthValue) :
    toCounts (updates.foldl coreState initial) =
      (updates.map toCounts).foldl (· + ·) (toCounts initial) := by
  let := sourceModel
  let := countModel
  exact interpretation.foldl_revise updates initial

/-- The additive law holds after interpreting values, without being assumed
for the complete source state space. -/
theorem count_observer_associative (first second third : NARSTruthValue) :
    toCounts (coreState (coreState first second) third) =
      toCounts (coreState first (coreState second third)) := by
  simp only [toCounts_coreState, add_assoc]

namespace Controls

noncomputable def unsupported : NARSTruthValue := ⟨1, 0, zero_le_one, le_rfl, le_rfl, zero_lt_one⟩

theorem unsupported_frequency_survives_in_source : unsupported ≠ emptyState := by
  intro same
  have frequency := congrArg NARSTruthValue.f same
  norm_num [unsupported, emptyState] at frequency

theorem count_projection_forgets_unsupported_frequency : toCounts unsupported = toCounts emptyState := by
  apply BinaryEvidence.ext' <;>
    norm_num [toCounts, unsupported, emptyState, NARSTruthValue.toTV,
      EvidenceTranslation.TV.toEvidence, c2w]

/-- A monoidal left-identity law would exclude this actual source model. -/
theorem full_source_has_no_left_identity :
    ¬ ∀ state, coreState emptyState state = state := by
  intro identity
  have frequency := congrArg NARSTruthValue.f (identity unsupported)
  norm_num [coreState, emptyState, unsupported, NARSTruthValue.toTV,
    truthRevisionCore, c2w, w2c] at frequency

end Controls

end Mettapedia.NARS.Bridges.PLN.RevisionWorldModel
