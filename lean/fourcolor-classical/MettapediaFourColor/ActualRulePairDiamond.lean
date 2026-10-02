import MettapediaFourColor.RulePairDiamond
import MettapediaFourColor.ActualDualContract
import MettapediaFourColor.LocalPreembedding
import MettapediaFourColor.MixedDiamondFaceReduction
import Mettapedia.GraphTheory.FourColor.PentagonalNeighbourSupply

/-!
# A charge-rule pair supplies the actual mixed-diamond reduction

The rule-pair closure is transported through the actual facial dual, with
degree observations identified with original face lengths. The resulting
mixed diamond has the existing thirteen-to-five vertex replacement and
colouring reconstruction. Hence this aligned pair of charge rules, with
the stated five/six guards, cannot occur in a graph-backed vertex-minimal
counterexample. No cartwheel-classification hypothesis is supplied.
-/

namespace FourColor.ActualRulePairDiamond

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24MinimalFaceIntersections
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceCyclicOrder
open GoertzelV24OrbitFaceTwoSided GoertzelV24RotationSystemPrimalGraphBacking
open PentagonalNeighbourSupply RulePairDiamond

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

abbrev graph := MinimalExceptionalEmbedding.graph original minimal
abbrev rotation := MinimalExceptionalEmbedding.rotation original minimal
abbrev darts := ActualDualRotation.darts original.toRotationSystem minimal.facesTwoSided
  (pairwiseUniqueSharedInteriorEdges original minimal)

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- Actual dual degree is the original facial dart length. -/
theorem degree_dart (d : G.Dart) :
    (graph original minimal).degree (darts original minimal d).fst =
      size original.toRotationSystem d := by
  refine (DualGraphQuery.arity_eq_degree (rotation original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) (darts original minimal d)).symm.trans ?_
  change (DualGraphQuery.map (ActualDualRotation.data original.toRotationSystem
    minimal.facesTwoSided (pairwiseUniqueSharedInteriorEdges original minimal))).arity
      (darts original minimal d) = _
  rw [ActualDualContract.map_eq_source_relabel, Hypermap.arity_relabel]
  let RS := original.toRotationSystem
  change Function.minimalPeriod RS.phi d = (RS.faceOrbit d).card
  have cyclic := phi_isCycleOn_faceOrbit RS d
  have periods (n : ℕ) : Function.minimalPeriod RS.phi d ∣ n ↔ (RS.faceOrbit d).card ∣ n := by
    rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    change RS.phi^[n] d = d ↔ _
    rw [Equiv.Perm.iterate_eq_pow, cyclic.pow_apply_eq (RS.mem_faceOrbit_self d)]
  exact Nat.dvd_antisymm ((periods _).mpr (dvd_refl _))
    ((periods _).mp (dvd_refl _))

theorem flip (d : G.Dart) :
    darts original minimal d.symm = (darts original minimal d).symm :=
  primalDartEquiv_alpha (ActualDualRotation.dual original.toRotationSystem minimal.facesTwoSided)
    (ActualDualRotation.dual_endpoints_injective _ _
      (pairwiseUniqueSharedInteriorEdges original minimal)) d

theorem opposite_degree (d : G.Dart) :
    (graph original minimal).degree (darts original minimal d).snd =
      size original.toRotationSystem d.symm := by
  have h := degree_dart original minimal d.symm
  rw [flip] at h
  exact h

theorem step (d : G.Dart) :
    (rotation original minimal).vertexRotation (darts original minimal d) =
      darts original minimal (original.toRotationSystem.phi d) :=
  ActualDualRotation.data_step original.toRotationSystem minimal.facesTwoSided
    (pairwiseUniqueSharedInteriorEdges original minimal) d

theorem previous (d : G.Dart) :
    (rotation original minimal).vertexRotation.symm (darts original minimal d) =
      darts original minimal (original.toRotationSystem.phi.symm d) := by
  apply (rotation original minimal).vertexRotation.injective
  rw [Equiv.apply_symm_apply, step, Equiv.apply_symm_apply]

/-- The four local dual observations are exactly the existing physical
mixed-diamond face pattern on the same original source. -/
theorem face_pattern (e : (graph original minimal).Dart)
    (pattern : MixedAt (rotation original minimal) e) :
    ∃ d : G.Dart, MixedDiamond.FaceLengths original d := by
  obtain ⟨d, rfl⟩ := (darts original minimal).surjective e
  have h5 : size original.toRotationSystem d = 5 :=
    (degree_dart original minimal d).symm.trans pattern.five
  have h6 : size original.toRotationSystem d.symm = 6 :=
    (opposite_degree original minimal d).symm.trans pattern.six
  have hn := pattern.next
  rw [step, opposite_degree] at hn
  have hp := pattern.previous
  rw [previous, opposite_degree] at hp
  refine ⟨d, h5, h6, ?_⟩
  intro i hi
  rcases hi with rfl | rfl
  · exact hn
  · let RS := original.toRotationSystem
    have period := (phi_isCycleOn_faceOrbit RS d).pow_card_apply (RS.mem_faceOrbit_self d)
    change (RS.phi ^ size RS d) d = d at period
    rw [h5] at period
    have last : (RS.phi ^ 4) d = RS.phi.symm d := by
      apply RS.phi.injective
      rw [Equiv.apply_symm_apply]
      simpa only [pow_succ', Equiv.Perm.mul_apply] using period
    change size RS (RS.alpha ((RS.phi ^ 4) d)) = 5
    rw [last]
    exact hp

/-- The supplied rule pair is excluded by actual strict reduction and
reconstruction, independently of the full Four Colour theorem. -/
theorem not_in_minimal (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 4 d = true)
    (right : RuleMatcher.check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (five : (graph original minimal).degree d.fst = 5)
    (six : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 6) : False := by
  obtain ⟨e, he⟩ := mixed_of_checks (MinimalExceptionalEmbedding.cyclic original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) d left right five six
  obtain ⟨root, hroot⟩ := face_pattern original minimal e he
  exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
    original root hroot minimal

/-- A checked left rule forbids the aligned right rule under the two guards.
This form can prune joint charge profiles without a classification oracle. -/
theorem right_check_false (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 4 d = true)
    (five : (graph original minimal).degree d.fst = 5)
    (six : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 6) :
    RuleMatcher.check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = false := by
  cases hr : RuleMatcher.check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d)
  · rfl
  · exact (not_in_minimal original minimal d left hr five six).elim

end
end FourColor.ActualRulePairDiamond
