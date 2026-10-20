import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.Framework.GeneratedHypercubeInstances

open Mettapedia.OSLF.Framework

/-!
# The source communication geometry through the executable generator

The source communication rule has no parallel remainder. The existing full
rho grammar and equations are retained; only the base communication rule is
the fixed-arity presentation. The continuation's actual generated context
produces two rely inputs and one output, hence seven non-origin directions.
Fixing the channel slot gives the square of the remaining payload/output
assignments. This is local profile geometry, not a claim that local profiles
alone determine a complete sort-operation algebra.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.Framework.GeneratedHypercubeInstances (rhoCommPaper)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences
open Mettapedia.OSLF.NativeTypes.SortProfiles.Slots

def language : LanguageDef := {rhoCalc with rewrites := [rhoCommPaper]}

def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩

def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment := {}

def chosen := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment

theorem chosen_language : chosen.language = language := by
  exact Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature language {}

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated : Mettapedia.OSLF.NativeTypes.Generation.Generated :=
  Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex

def continuationContext : OneHoleContext :=
  .collection .hashBag [] (.apply "PInput" [.fvar "n"] .hole [])
    [.apply "POutput" [.fvar "n", .fvar "q"]] none

def continuationSite : Site where
  declaration := 0
  rule := rhoCommPaper
  context := continuationContext
  focus := .lambda none (.fvar "p")

theorem authored_continuation_generated : continuationSite ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language := by
  apply (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec _ _).mpr
  refine ⟨List.mk_mem_zipIdx_iff_getElem?.mpr rfl, ?_⟩
  exact Selects.collection (Selects.apply Selects.here)

theorem generated_raw_input :
    generated.rawSites = Mettapedia.OSLF.NativeTypes.Generation.selectedSites language fragment.operational := by
  change Mettapedia.OSLF.NativeTypes.Generation.selectedSites chosen.language fragment.operational = _
  rw [chosen_language]

/-- This is a member of the single generator's actual output, not an
independently tabulated replacement for its site catalogue. -/
theorem generator_contains_continuation : continuationSite ∈ generated.rawSites := by
  rw [generated_raw_input]
  apply (Mettapedia.OSLF.NativeTypes.Generation.selected_sites_iff _ _ _).mpr
  have original := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec _ _).mp authored_continuation_generated
  exact ⟨original.1, original.2, rfl⟩

theorem actual_continuation_position : continuationSite.position = [0, 1] := rfl

theorem actual_rely_inputs : continuationSite.relyNames = ["n", "q"] := by decide +kernel

theorem actual_hidden_body : continuationSite.hiddenNames = ["p"] := by decide +kernel

def family : Family := modalFamily language continuationSite

theorem actual_family_inputs :
    family.inputs = [("n", some TypeExpr.name), ("q", some TypeExpr.proc)] := by decide +kernel

theorem actual_channel_is_first : family.inputs[0]? = some ("n", some TypeExpr.name) := by
  rw [actual_family_inputs]
  rfl

theorem computed_three_slots : family.slotCount = 3 := by
  change (modalFamily language continuationSite).slotCount = 3
  rw [modal_slot_count, actual_rely_inputs]
  rfl

theorem seven_generated_axes : (axes family).card = 7 := by
  rw [axes_card, computed_three_slots]
  decide

theorem actual_family_in_the_generated_language :
    family ∈ families generated.snapshot.language := by
  change family ∈ families chosen.language
  rw [chosen_language]
  exact modal_family_generated authored_continuation_generated

def channelSquare := fixedFirstFace family.inputs.length

theorem channelSquare_four_corners : channelSquare.card = 4 := by
  change (fixedFirstFace family.inputs.length).card = 4
  rw [fixedFirstFace_card, actual_family_inputs]
  decide

def channelIndex : Fin family.slotCount := ⟨0, by rw [computed_three_slots]; omega⟩

/-- The actual channel-fixed corners are exactly the two remaining sort
choices. The equivalence retains every assignment, not just cardinalities. -/
def channelSquareEquiv :
    {assignment : Fin family.slotCount → HSort // assignment channelIndex = .star} ≃ (Fin 2 → HSort) :=
  fixedFirstEquiv 2

theorem rest_is_absent_from_source_rule :
    "rest" ∉ continuationSite.relyNames := by rw [actual_rely_inputs]; decide

def restContext : OneHoleContext :=
  .collection .hashBag [] (.apply "PInput" [.fvar "n"] .hole [])
    [.apply "POutput" [.fvar "n", .fvar "q"]] (some "rest")

def restSite : Site where
  declaration := 0
  rule := rhoCommRewrite
  context := restContext
  focus := .lambda none (.fvar "p")

theorem original_rest_rule_has_an_extra_input :
    restSite.relyNames = ["n", "q", "rest"] ∧
      (modalFamily rhoCalc restSite).slotCount = family.slotCount + 1 := by decide +kernel

end Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry
