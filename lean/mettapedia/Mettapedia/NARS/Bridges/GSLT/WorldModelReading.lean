import Mettapedia.NARS.Bridges.PLN.FiniteEvidenceChart
import Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

/-!
# NARS core and count readings of the authored WM calculus

The existing sorted WM syntax has two distinct readings: complete valid NARS
truth values and additive binary counts. Their operation-preserving reading
morphism commutes with every nested term and with pulled-back native
observations. Count observers respect the core WM rewrites; full NARS values
need not. The zero-confidence counterexample exposes this distinction.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.GSLT.WorldModelReading

open Mettapedia.NARS.Bridges.PLN
open Mettapedia.NARS.Bridges.PLN.InformationAdjunction
open Mettapedia.NARS.Bridges.PLN.RevisionWorldModel
open Mettapedia.PLN.Evidence
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation

noncomputable def source (world : String → NARSTruthValue) : WMReading NARSTruthValue Unit NARSTruthValue where
  revise := coreState
  extract state _ := state
  combine := coreState
  zero := emptyState
  world := world
  query _ := ()

noncomputable def target (world : String → NARSTruthValue) : WMReading BinaryEvidence Unit BinaryEvidence where
  revise := (· + ·)
  extract state _ := state
  combine := (· + ·)
  zero := 0
  world name := toCounts (world name)
  query _ := ()

noncomputable def interpretation (world : String → NARSTruthValue) :
    ReadingMorphism (source world) (target world) where
  mapState := toCounts
  mapQuery := id
  mapEvidence := toCounts
  revise_comm := toCounts_coreState
  extract_comm _ _ := rfl
  combine_comm := toCounts_coreState
  zero_comm := by
    change toCounts emptyState = 0
    let := sourceModel
    let := countModel
    exact Mettapedia.NARS.Bridges.PLN.RevisionWorldModel.interpretation.empty
  world_comm _ := rfl
  query_comm _ := rfl

/-- The actual existing sorted term fold commutes at every sort and depth. -/
theorem denote_commutes (world : String → NARSTruthValue) {sort : WMSort} (term : WMTerm sort) :
    (interpretation world).mapValue sort ((source world).denote term) = (target world).denote term :=
  (interpretation world).denote_map term

/-- The same equality holds for native observation predicates on authored
programs, with the target observer explicitly pulled back to source values. -/
theorem native_observations_commute (world : String → NARSTruthValue) (sort : WMSort)
    (observe : SortValue BinaryEvidence Unit BinaryEvidence sort → Prop) :
    observationPredicate (source world) sort
        (fun value => observe ((interpretation world).mapValue sort value)) =
      observationPredicate (target world) sort observe :=
  (interpretation world).observationPredicate_map sort observe

theorem target_core_laws (world : String → NARSTruthValue) : (target world).CoreLaws where
  extract_revise _ _ _ := rfl
  combine_comm := add_comm
  combine_assoc := add_assoc
  combine_zero := add_zero

/-- Core WM rewriting is sound for the count observer of NARS values,
without asserting the stronger rewrite law on every full truth value. -/
theorem count_observer_rewrite_sound (world : String → NARSTruthValue)
    {first second : WMTerm .evidence} (steps : WMContextStepStar first second) :
    toCounts ((source world).denote first) = toCounts ((source world).denote second) := by
  have firstMap := (interpretation world).denote_map first
  have secondMap := (interpretation world).denote_map second
  have agree := (target_core_laws world).agree_of_contextStepStar steps
  change toCounts ((source world).denote first) = (target world).denote first at firstMap
  change toCounts ((source world).denote second) = (target world).denote second at secondMap
  exact firstMap.trans (agree.trans secondMap.symm)

/-- For supported source values the count interpretation reflects the
complete result. One positive-confidence guard suffices: equal counts also
preserve confidence. -/
theorem supported_full_value_rewrite_sound (world : String → NARSTruthValue)
    {first second : WMTerm .evidence} (steps : WMContextStepStar first second)
    (supported : 0 < ((source world).denote first).c) :
    (source world).denote first = (source world).denote second := by
  have counts := count_observer_rewrite_sound world steps
  have confidence := FiniteEvidenceChart.toCounts_confidence_congr _ _ counts
  exact FiniteEvidenceChart.toCounts_injective_on_supported _ _ supported
    (by rwa [← confidence]) counts

namespace Controls

def full : WMTerm .evidence := .extract (.state "unsupported") (.query "q")
def reduced : WMTerm .evidence := .combine full .zero

theorem zero_rewrite_exists : WMStep reduced full := .combine_zero full

/-- The actual zero rewrite changes a complete unsupported NARS value,
although its projected count readout is preserved. -/
theorem full_value_rewrite_fails :
    (source (fun _ => RevisionWorldModel.Controls.unsupported)).denote reduced ≠
      (source (fun _ => RevisionWorldModel.Controls.unsupported)).denote full := by
  intro same
  have frequency := congrArg NARSTruthValue.f same
  norm_num [source, reduced, full, WMReading.denote, coreState, emptyState,
    RevisionWorldModel.Controls.unsupported, NARSTruthValue.toTV,
    Mettapedia.NARS.TruthFunctions.truthRevisionCore, Mettapedia.NARS.TruthFunctions.c2w,
    Mettapedia.NARS.TruthFunctions.w2c] at frequency

theorem full_value_core_laws_fail :
    ¬ (source (fun _ => RevisionWorldModel.Controls.unsupported)).CoreLaws := by
  intro laws
  apply full_value_rewrite_fails
  exact laws.combine_zero _

end Controls

end Mettapedia.NARS.Bridges.GSLT.WorldModelReading
